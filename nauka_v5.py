"""
Интерактивный программный комплекс моделирования ВСМ-1.
Кейс №06: АО "Сервис Высоких Скоростей" / РУТ (МИИТ) / Минтранс РФ.
Команда «Восток» (ДВГУПС).

Версия 5.0 (nauka_v5.py):
- Резервы строго по ТЗ:
    * 4 поезда горячего резерва постоянно в СПб (Обухово), с запасом
      хода не менее пары 1493 км, плановая плановая ротация раз в 10 дней;
    * скользящий резерв: при отказе в пути поезд, чей рейс должен
      состояться через ~4 часа, выпускается раньше; поезд из горячего
      резерва засылается в Москву на его нитку; место в резерве
      замещает первый доступный состав.
- Честное сравнение схем:
    * BASELINE (LAZY) — депо без динамической квоты, ТО переносится
      до предела удержания интервала, отказы не подменяются;
    * PROPOSED — ночное окно 00:00-06:00, приоритет критическим
      циклам и обточке, отложенная обточка с контролем предела,
      скользящий резерв.
- Реальный суточный график оборота (19 формирований, 730-3641 км/сут).
- Внеплановые работы: +30% к трудоемкости IS100-IS540,
  +10% к ревизиям IS600/700.
- Обязательные уборка и экипировка (2-3 ч) после каждых 4 рейсов.
- Ночное окно: не более 5 поездов одновременно и не более
  120 поездо-часов суммарно за сутки.
- Контроль перепробегов (hard limits) с журналом нарушений.
- Monte Carlo (N прогонов) и доверительные интервалы.
- Экспорт CSV/Excel, графики matplotlib в интерфейсе.
"""

from __future__ import annotations

import math
import threading
import tkinter as tk
from dataclasses import dataclass, field
from tkinter import filedialog, messagebox, ttk

import numpy as np
import pandas as pd

ROUTE_KM = 679.0
DEPOT_LEG_KM = 16.4
ROUTE_ROUND_TRIP_KM = 2 * ROUTE_KM * 1.10  # 1493 км: пара с запасом 10%
HOT_RESERVE_DEFAULT = 4
MAX_SIM_DEPOT = 5
DAILY_DEPOT_HOURS = 120.0
CLEAN_INTERVAL_RUNS = 4

# Реальный суточный график оборота (пример график оборота.xlsx):
# пробег каждого формирования за сутки по ниткам
ROTATION_SUMS = [
    2322.0, 1495.0, 2898.0, 2994.0, 3016.0, 730.0, 2960.0, 3641.0, 3624.0,
    2940.0, 2970.0, 3014.0, 2948.0, 2980.0, 2310.0, 2950.0, 2992.0, 2960.0,
    2223.0,
]

MAINTENANCE_CYCLES = {
    "IS100": (12500, 0.10, 2.0),
    "IS200": (25000, 0.20, 4.0),
    "IS510": (75000, 0.20, 10.0),
    "IS520": (150000, 0.20, 16.0),
    "IS530": (300000, 0.20, 36.0),
    "IS540": (600000, 0.20, 56.0),
    "IS600": (1200000, 0.20, 384.0),
    "IS700": (2400000, 0.20, 575.0),
}
LIGHT_CYCLES = ("IS520", "IS510", "IS200", "IS100")
HEAVY_CYCLES = ("IS700", "IS600", "IS540", "IS530")
WHEEL_LATHE_INTERVAL = 200000
WHEEL_LATHE_HARD_LIMIT = WHEEL_LATHE_INTERVAL * 1.10
UNPLANNED_PLANNED = 0.30
UNPLANNED_REVISION = 0.10
REVISION_CYCLES = ("IS600", "IS700")

# ==========================================================================
# ДЕРЕВО ВНЕПЛАНОВЫХ ОТКАЗОВ (иерархическая модель)
#
# Удельные интенсивности отказов (отраслевые данные по ВСМ/EMU,
# приведённые к 10^6 поездо-км; 1 поезд ≈ 2 состава):
#   • отказ дверей .............. ~3.0 на 10^6 поездо-км  (доминирующий)
#   • освещение/бытовые ......... ~2.0
#   • кондиционирование ......... ~1.4
#   • неполная тяга (1 из 4) .... ~1.1
#   • полная потеря тяги ........ ~0.15
#   • тормозная система ......... ~0.10
#   • сцепное устройство ........ ~0.05
# Итог ~8 на 10^6 поездо-км — согласуется с практикой надёжности ВСМ
# (~1 отказ на 125 тыс. км, MTBF ~0.4 млн км на состав).
#
# Гейт (BREAKDOWN_GATE=0.30) — вероятность того, что за сутки событие
# произойдёт во всём парке; вклад каждого состава пропорционален его
# суточному пробегу: p_i = gate * fleet_size / (fleet_km_day),
# далее произведение p_i x w(тяжесть) x w(узел), т.е. схема
# «0.3 x 0.000001» для редчайших и «0.3 x 0.8» для частых событий.
#
# Тяжесть:
#   LIGHT  — поезд следует с прежней скоростью (освещение/двери),
#            ремонт учтён в плановом заходе;
#   MEDIUM — следует с пониженной скоростью/неполной тягой (x0.45-0.8),
#            ремонт в депо СПб, включается скользящий резерв;
#   HEAVY  — движение невозможно, за составом высылают маневровый.
# ==========================================================================
BREAKDOWN_GATE = 0.30
BREAKDOWN_RATE_PER_MKM = 4.0  # отказов на 10^6 поездо-км (порядок ВСМ: 3-5)

SEVERITY_PROBS = {
    "LIGHT": 0.55,
    "MEDIUM": 0.40,
    "HEAVY": 0.05,
}

BREAKDOWN_TREE = {
    # severity: [(код, вес_внутри_тяжести, узлы, следствие)]
    "LIGHT": [
        ("DOOR", 0.45, "двери тамбура/салонов", "следует по расписанию; ремонт на стоянке"),
        ("LIGHT", 0.30, "освещение, розетки, информсистемы", "следует по расписанию"),
        ("HVAC", 0.20, "кондиционирование одного вагона", "следует по расписанию; снижен комфорт"),
        ("TOILET", 0.05, "санитарный модуль", "следует по расписанию"),
    ],
    "MEDIUM": [
        ("PART_TRACTION", 0.55, "неполная тяга (1 из 4 тяговых блоков)", "следует со снижением скорости (x0.8)"),
        ("BRAKE", 0.25, "тормозная система вагона", "следует со снижением скорости (x0.5)"),
        ("POWER", 0.12, "токоприёмник/тяговая подстанция питания", "следует со снижением скорости (x0.7)"),
        ("BOGIE", 0.08, "буксовый узел/рельсовая цепь", "следует со снижением скорости (x0.5)"),
    ],
    "HEAVY": [
        ("COUPLER", 0.60, "сцепное устройство", "движение невозможно; высылается маневровый локомотив"),
        ("ATRACTION", 0.30, "полная потеря тяги", "движение невозможно; маневровый локомотив"),
        ("POWER_FULL", 0.10, "обрыв питания на перегоне", "движение невозможно; маневровый локомотив"),
    ],
}

# Типовое время устранения, диапазон часов (двухпараметрическое равномерное)
BREAKDOWN_HOURS = {
    "DOOR": (4.0, 8.0),
    "LIGHT": (2.0, 4.0),
    "HVAC": (4.0, 8.0),
    "TOILET": (2.0, 4.0),
    "PART_TRACTION": (10.0, 18.0),
    "BRAKE": (12.0, 20.0),
    "POWER": (12.0, 24.0),
    "BOGIE": (16.0, 24.0),
    "COUPLER": (48.0, 72.0),
    "ATRACTION": (24.0, 48.0),
    "POWER_FULL": (24.0, 48.0),
}

RESCUE_HOURS = (3.0, 6.0)  # вызов и движение маневрового/подталкивающего
DAILY_RUN_ESTIMATE_KM = 2700.0  # оценка суточного пробега состава


@dataclass
class SimConfig:
    sim_years: float = 5.0
    fleet_start: int = 6
    fleet_max: int = 43
    intro_per_month: int = 1
    lathe_hours: float = 2.0
    racks: int = 8          # рем-позиции IS100-IS540 (4 стойла x 2 состава)
    jacks: int = 3          # пути с домкратами для IS600/IS700
    hot_reserve: int = HOT_RESERVE_DEFAULT
    target_k_eg: float = 89.0
    reserve_mode: str = "SLIDING"  # LAZY | PARTIAL | SLIDING
    unplanned_enabled: bool = True
    breakdown_gate: float = BREAKDOWN_GATE
    rescue_hours_min: float = RESCUE_HOURS[0]
    rescue_hours_max: float = RESCUE_HOURS[1]
    severity_probs: dict[str, float] = field(
        default_factory=lambda: dict(SEVERITY_PROBS)
    )
    breakdown_tree: dict[str, list] = field(
        default_factory=lambda: {k: [list(x) for x in v] for k, v in BREAKDOWN_TREE.items()}
    )
    clean_hours_min: float = 2.0
    clean_hours_max: float = 3.0
    reserve_rotation_days: int = 10
    seed: int = 42


@dataclass
class Train:
    id: int
    intro_day: int
    total_km: float = 0.0
    km_since_lathe: float = 0.0
    km_since_maintenance: dict[str, float] = field(default_factory=dict)
    status: str = "READY"
    location: str = "SPB"
    downtime_hours_remaining: float = 0.0
    stay_days: int = 0
    worked_today: float = 0.0
    mission: str | None = None
    runs_since_clean: int = 0
    awaiting_clean: bool = False
    reserve_days: int = 0
    depot_cycle: str | None = None
    depot_started_day: int | None = None
    breakdown_day: int | None = None
    night_hours_remaining: float = 0.0
    night_block_cycle: str | None = None

    def __post_init__(self):
        self.km_since_maintenance = {k: 0.0 for k in MAINTENANCE_CYCLES}

    def min_km_to_next_maintenance(self) -> float:
        margins = []
        for cycle, (interval, tol, _) in MAINTENANCE_CYCLES.items():
            max_allowed = interval * (1.0 + tol)
            margins.append(max_allowed - self.km_since_maintenance[cycle])
        return min(margins)

    def add_daily_km(self, run_km: float):
        self.total_km += run_km
        self.km_since_lathe += run_km
        for c in self.km_since_maintenance:
            self.km_since_maintenance[c] += run_km


@dataclass
class ServicePlan:
    cycle: str | None
    lathe: bool
    clean: bool
    critical: bool = False
    night_block: bool = False

    def is_empty(self) -> bool:
        return not (self.cycle or self.lathe or self.clean)

    def planned_hours(self, cfg: SimConfig) -> float:
        hours = 0.0
        if self.clean:
            hours += 0.5 * (cfg.clean_hours_min + cfg.clean_hours_max)
        if self.cycle:
            hours += MAINTENANCE_CYCLES[self.cycle][2]
        if self.lathe:
            hours += cfg.lathe_hours
        return hours


def _most_urgent_cycle(train: Train) -> str | None:
    """Самый старший цикл, у которого до жёсткого предела меньше 2 суток
    пробега. Его выполнение сбрасывает и все младшие циклы."""
    urgent = [
        c for c, (interval, tol, _) in MAINTENANCE_CYCLES.items()
        if interval * (1.0 + tol) - train.km_since_maintenance[c]
        < 2.0 * DAILY_RUN_ESTIMATE_KM
    ]
    if not urgent:
        return None
    return max(urgent, key=lambda c: MAINTENANCE_CYCLES[c][0])


def build_plan(train: Train, cfg: SimConfig, strategy: str) -> ServicePlan | None:
    plan = ServicePlan(cycle=None, lathe=False, clean=False)
    if train.awaiting_clean:
        plan.clean = True
    if (
        train.km_since_lathe >= WHEEL_LATHE_INTERVAL
        or WHEEL_LATHE_HARD_LIMIT - train.km_since_lathe < 2.0 * DAILY_RUN_ESTIMATE_KM
    ):
        plan.lathe = True

    if strategy == "PROPOSED":
        for c in LIGHT_CYCLES:
            interval, tol, _ = MAINTENANCE_CYCLES[c]
            if train.km_since_maintenance[c] >= interval * (1.0 - tol):
                plan.cycle = c
                break
        for c in HEAVY_CYCLES:
            interval, tol, _ = MAINTENANCE_CYCLES[c]
            age = train.km_since_maintenance[c]
            if age >= interval * (1.0 + tol * 0.85):
                plan.cycle = c
                plan.critical = True
                break
            if age >= interval * (1.0 - tol):
                plan.cycle = c
                break
        # Срочный заход: до жёсткого предела меньше ~2 суток пробега.
        # Если срочен младший цикл, а план — ревизия (вывод состава),
        # закрываем срочный цикл ночным блоком, ревизия ждёт места.
        urgent = _most_urgent_cycle(train)
        if urgent is not None:
            plan.critical = True
            urgent_level = MAINTENANCE_CYCLES[urgent][0]
            planned_level = MAINTENANCE_CYCLES[plan.cycle][0] if plan.cycle else 0
            revision_waiting = (
                plan.cycle in REVISION_CYCLES and urgent not in REVISION_CYCLES
            )
            if urgent_level >= planned_level or revision_waiting:
                plan.cycle = urgent
        # Ночные сервисные блоки: IS100-IS540 и обточка выполняются в ночное
        # окно без вывода состава из дневного графика (до 6 ч за ночь)
        plan.night_block = plan.cycle not in REVISION_CYCLES
    else:
        # BASELINE: жёсткая регламентная схема — заход не позже, чем за
        # двое суток до предела допуска; перепробег недопустим
        urgent = _most_urgent_cycle(train)
        if urgent is not None:
            plan.cycle = urgent
            plan.critical = True

    # Если состав уже проходит ночной блок старшего цикла, повторный заход
    # по младшим циклам не нужен (они сбрасываются тем же ремонтом);
    # заход по более старшему циклу сохраняется и ждёт места.
    if train.night_hours_remaining > 0 and plan.cycle is not None:
        block_level = (
            MAINTENANCE_CYCLES[train.night_block_cycle][0]
            if train.night_block_cycle in MAINTENANCE_CYCLES
            else 0
        )
        if MAINTENANCE_CYCLES[plan.cycle][0] <= block_level:
            plan.cycle = None
            plan.clean = False

    if plan.is_empty():
        return None
    return plan


def apply_cycle_reset(train: Train, cycle: str):
    threshold = MAINTENANCE_CYCLES[cycle][0]
    for c in MAINTENANCE_CYCLES:
        if MAINTENANCE_CYCLES[c][0] <= threshold:
            train.km_since_maintenance[c] = 0.0


def is_unavailable(train: Train, day: int) -> bool:
    """Состав недоступен для перевозок в текущие сутки:
    аварийный или находящийся в депо с прошлых суток (многосуточная работа).
    Работы, уложившиеся в ночную смену, к утру завершены — состав в строю."""
    if train.status in ("FAILED", "CASUALTY"):
        return True
    if train.status in ("DEPOT_SERVICE", "LATHE_QUEUE"):
        started = train.depot_started_day
        return (
            train.breakdown_day == day
            or started is None
            or started < day
        )
    return False


class Depot:
    """Депо Обухово: 8 рем-позиций (IS100-IS540), 3 пути с домкратами
    (IS600/IS700), тандемный станок обточки; бюджет 120 поездо-часов/сут."""

    def __init__(self, cfg: SimConfig):
        self.cfg = cfg
        self.occupancy = 0
        self.occupancy_light = 0
        self.occupancy_heavy = 0
        self.occupancy_night = 0
        self.hours_used_today = 0.0
        self.hours_worked_tonight = 0.0
        self.lathe_queue: list[Train] = []
        self.lathe_hours_used_today = 0.0
        self.log: list[dict] = []
        self.overflow_events = 0

    def reset_daily(self):
        self.hours_used_today = 0.0
        self.hours_worked_tonight = 0.0
        self.lathe_hours_used_today = 0.0

    def rebuild(self, active: list[Train]):
        """Пересчитывает занятость по фактическим статусам составов."""
        in_service = [
            t for t in active if t.status in ("DEPOT_SERVICE", "LATHE_QUEUE")
        ]
        self.occupancy_night = sum(
            1 for t in active if t.night_hours_remaining > 0
        )
        self.occupancy = len(in_service) + self.occupancy_night
        self.occupancy_heavy = sum(
            1 for t in in_service if t.depot_cycle in REVISION_CYCLES
        )
        self.occupancy_light = len(in_service) - self.occupancy_heavy

    def can_admit(self, plan: ServicePlan, occupancy: int) -> bool:
        if plan.night_block:
            # Ночной блок: ограничение одно — суточный бюджет 120 поездо-часов
            if plan.critical:
                return True
            budget = self.hours_used_today + min(plan.planned_hours(self.cfg), 6.0)
            return budget <= DAILY_DEPOT_HOURS
        heavy = plan.cycle in REVISION_CYCLES
        if plan.critical:
            return True
        if heavy and self.occupancy_heavy >= self.cfg.jacks:
            return False
        if not heavy and self.occupancy_light >= self.cfg.racks:
            return False
        budget = self.hours_used_today + min(plan.planned_hours(self.cfg), 6.0)
        return budget <= DAILY_DEPOT_HOURS

    def admit(self, train: Train, plan: ServicePlan, day: int):
        hours = plan.planned_hours(self.cfg)
        if self.cfg.unplanned_enabled:
            share = UNPLANNED_REVISION if plan.cycle in REVISION_CYCLES else UNPLANNED_PLANNED
            hours += hours * share * float(np.random.uniform(0.0, 1.0))
        if plan.clean:
            train.runs_since_clean = 0
            train.awaiting_clean = False
        if plan.cycle:
            apply_cycle_reset(train, plan.cycle)
        if plan.lathe:
            train.km_since_lathe = 0.0

        if plan.night_block:
            # Работы идут ночными блоками по 6 ч; днём состав в графике
            train.night_hours_remaining += hours
            # Метка блока — самый старший из выполняемых циклов
            if plan.cycle in MAINTENANCE_CYCLES:
                current = train.night_block_cycle
                if (
                    current not in MAINTENANCE_CYCLES
                    or MAINTENANCE_CYCLES[plan.cycle][0]
                    > MAINTENANCE_CYCLES[current][0]
                ):
                    train.night_block_cycle = plan.cycle
            self.occupancy_night += 1
            self.occupancy += 1
            self.hours_used_today += min(hours, 6.0)
            self.log.append(
                {
                    "day": day, "train": train.id, "cycle": plan.cycle,
                    "lathe": plan.lathe, "clean": plan.clean,
                    "critical": plan.critical, "hours": round(hours, 2),
                    "stay_days": 0, "night_block": True,
                }
            )
            return

        # Ревизии и внеплановые ремонты ведутся в три смены (24 ч/сут),
        # плановые циклы — в две смены по 6 ч (12 ч/сут)
        if plan.cycle in REVISION_CYCLES or plan.cycle is None:
            hours_per_day = 24.0
        else:
            hours_per_day = 12.0
        shifts_needed = max(1, math.ceil(hours / hours_per_day))
        train.status = "DEPOT_SERVICE"
        train.location = "SPB"
        train.downtime_hours_remaining = hours
        train.stay_days = min(shifts_needed, 40)
        train.depot_cycle = plan.cycle
        train.depot_started_day = day
        self.occupancy += 1
        if plan.cycle in REVISION_CYCLES:
            self.occupancy_heavy += 1
        else:
            self.occupancy_light += 1
        self.hours_used_today += min(hours, 6.0)
        self.log.append(
            {
                "day": day,
                "train": train.id,
                "cycle": plan.cycle,
                "lathe": plan.lathe,
                "clean": plan.clean,
                "critical": plan.critical,
                "hours": round(hours, 2),
                "stay_days": train.stay_days,
            }
        )

    def lathe_shift(self, day: int) -> list[Train]:
        served = []
        while self.lathe_queue and self.lathe_hours_used_today + self.cfg.lathe_hours <= 6.0:
            train = self.lathe_queue.pop(0)
            train.km_since_lathe = 0.0
            self.lathe_hours_used_today += self.cfg.lathe_hours
            served.append(train)
            self.log.append(
                {"day": day, "train": train.id, "cycle": "LATHE", "lathe": True,
                 "clean": False, "critical": False, "hours": self.cfg.lathe_hours}
            )
        return served


def _refill_hot_reserve(active: list[Train], hot: list[Train], cfg: SimConfig,
                        target: int | None = None) -> list[Train]:
    """Поддерживает горячий резерв в СПб (на полном парке — 4 поезда)
    с запасом хода >= 1493 км; на этапе развёртывания — пропорционально."""
    if target is None:
        target = cfg.hot_reserve
    ready = [
        t for t in active
        if t.status == "READY"
        and t.min_km_to_next_maintenance() >= ROUTE_ROUND_TRIP_KM * 1.07
    ]
    np.random.shuffle(ready)
    while len(hot) < target and ready:
        t = ready.pop()
        t.status = "HOT_RESERVE"
        t.location = "SPB"
        t.reserve_days = 0
        hot.append(t)
    return hot


def simulate(cfg: SimConfig, strategy: str = "PROPOSED") -> tuple[pd.DataFrame, dict]:
    if strategy == "BASELINE":
        cfg = SimConfig(**{**cfg.__dict__, "reserve_mode": "LAZY", "unplanned_enabled": False})

    np.random.seed(cfg.seed)
    sim_days = int(cfg.sim_years * 365)
    fleet = [Train(i + 1, intro_day=0) for i in range(cfg.fleet_start)]
    next_id = cfg.fleet_start + 1
    depot = Depot(cfg)

    overruns: list[dict] = []
    overrun_seen: set[tuple] = set()
    events: list[dict] = []
    hot_ids: list[int] = []
    breakdown_stats = {"total": 0, "covered": 0, "uncovered": 0,
                       "swap_km": 0.0, "reserve_move_km": 0.0, "delay_min": 0.0}
    breakdown_types: dict[str, int] = {}
    casualty_delay_min: dict[int, float] = {}
    rescue_delay_min: dict[int, float] = {}
    deferred_jobs = 0
    lathe_deferred_overruns = 0
    daily_stats = []

    def by_id(train_id: int) -> Train:
        return fleet[train_id - 1]

    for day in range(sim_days):
        # Календарный ввод парка (ТЗ: 6 поездов во 2 кв. 2028, далее +1 в месяц)
        if day > 0 and day % 30 == 0 and len(fleet) < cfg.fleet_max:
            for _ in range(cfg.intro_per_month):
                if len(fleet) >= cfg.fleet_max:
                    break
                fleet.append(Train(next_id, intro_day=day))
                next_id += 1

        active = [t for t in fleet if t.intro_day <= day]
        # Горячий резерв масштабируется до 4 поездов по мере роста парка
        hot_target = min(cfg.hot_reserve, max(1, int(len(active) * 0.12)))
        depot.reset_daily()

        # ---- 0. Возврат после суточного цикла: рейсы завершены ----
        for t in active:
            if t.status == "COMMERCIAL":
                t.status = "READY"

        # ---- 1. Рассвет: выпуск и ремонты после ночной смены ----
        for t in active:
            if t.status == "DEPOT_SERVICE":
                worked = min(t.downtime_hours_remaining, 6.0)
                depot.hours_worked_tonight += worked
                t.downtime_hours_remaining -= worked
                t.stay_days -= 1
                if t.stay_days <= 0:
                    t.stay_days = 0
                    t.downtime_hours_remaining = 0.0
                    if t.km_since_lathe >= WHEEL_LATHE_INTERVAL:
                        t.status = "LATHE_QUEUE"
                        if t not in depot.lathe_queue:
                            depot.lathe_queue.append(t)
                            depot.lathe_queue.sort(key=lambda x: -x.km_since_lathe)
                    else:
                        t.status = "READY"
                        t.location = "SPB"
            elif t.status == "FAILED":
                t.downtime_hours_remaining -= 24.0
                if t.downtime_hours_remaining <= 0:
                    t.status = "READY"
                    t.downtime_hours_remaining = 0.0

        # Ночные сервисные блоки: 6 ч работы за ночь, днём состав в графике.
        # Счётчики младших циклов сбрасываются по завершении блока (все
        # работы старшего цикла выполнены к этому моменту).
        for t in active:
            if t.night_hours_remaining > 0:
                worked = min(t.night_hours_remaining, 6.0)
                depot.hours_worked_tonight += worked
                t.night_hours_remaining -= worked
                if t.night_hours_remaining < 1e-9:
                    t.night_hours_remaining = 0.0
                    if t.night_block_cycle in MAINTENANCE_CYCLES:
                        apply_cycle_reset(t, t.night_block_cycle)
                    t.night_block_cycle = None

        # ---- 2. План заходов на текущие сутки (заход в ночь) ----
        planned: list[tuple[Train, ServicePlan]] = []
        for t in active:
            if t.status != "READY":
                continue
            plan = build_plan(t, cfg, strategy)
            if plan is not None:
                planned.append((t, plan))

        if strategy == "PROPOSED":
            planned.sort(
                key=lambda item: (
                    not item[1].critical,
                    not item[1].clean,
                    item[0].min_km_to_next_maintenance(),
                )
            )
        else:
            planned.sort(key=lambda item: -item[0].km_since_lathe)

        # ---- 3. Горячий резерв в СПб с запасом хода >= 1493 км ----
        hot = [by_id(i) for i in hot_ids if by_id(i).status == "HOT_RESERVE"]
        for t in hot:
            t.reserve_days += 1
            if t.reserve_days >= cfg.reserve_rotation_days:
                t.status = "READY"
                t.reserve_days = 0
        hot = [t for t in hot if t.status == "HOT_RESERVE"]
        hot = _refill_hot_reserve(active, hot, cfg, target=hot_target)

        # ---- 4. Контроль перепробегов (одна запись на поезд и цикл) ----
        for t in active:
            # Пока идёт ночной блок старшего цикла, младшие циклы входят
            # в его объём и перепробегом не считаются
            block_level = (
                MAINTENANCE_CYCLES[t.night_block_cycle][0]
                if t.night_hours_remaining > 0 and t.night_block_cycle in MAINTENANCE_CYCLES
                else 0
            )
            for c, (interval, tol, _) in MAINTENANCE_CYCLES.items():
                if interval <= block_level:
                    continue
                key = (t.id, c)
                if (
                    t.km_since_maintenance[c] > interval * (1.0 + tol)
                    and key not in overrun_seen
                ):
                    overrun_seen.add(key)
                    overruns.append({"day": day, "train": t.id, "cycle": c,
                                     "km": round(t.km_since_maintenance[c])})
            lathe_key = (t.id, "LATHE")
            if (
                t.km_since_lathe > WHEEL_LATHE_HARD_LIMIT
                and lathe_key not in overrun_seen
            ):
                overrun_seen.add(lathe_key)
                lathe_deferred_overruns += 1
                overruns.append({"day": day, "train": t.id, "cycle": "LATHE",
                                 "km": round(t.km_since_lathe)})

        # ---- 5. Дерево внеплановых отказов и скользящий резерв ----
        # Гейт: за сутки во всём парке событие происходит с вероятностью
        # cfg.breakdown_gate. Вклад состава пропорционален пробегу:
        # p_i = gate * N / L_day, где L_day - суточный пробег всего парка.
        # Далее розыгрыш тяжести (LIGHT/MEDIUM/HEAVY) и типа узла
        # (BREAKDOWN_TREE): частое — 0.30 x 0.8 (двери), редкое —
        # 0.30 x 0.000001 (сцепка). Ожидаемая частота согласована с
        # BREAKDOWN_RATE_PER_MKM отказов на 10^6 поездо-км.
        if cfg.unplanned_enabled:
            # p_i = (отказов на 10^6 поездо-км) x (суточный пробег) / 10^6
            p_train = min(
                0.5, BREAKDOWN_RATE_PER_MKM * 2700.0 / 1e6 * (cfg.breakdown_gate / 0.30)
            )
            for s in np.random.permutation(active):
                if s.location != "SPB" or s.status not in (
                    "COMMERCIAL", "READY", "HOT_RESERVE"
                ):
                    continue
                if np.random.random() >= p_train:
                    continue

                sev_probs = cfg.severity_probs or SEVERITY_PROBS
                sev_sum = sum(sev_probs.values()) or 1.0
                sev_roll = np.random.random()
                acc = 0.0
                severity = "LIGHT"
                for sev in ("LIGHT", "MEDIUM", "HEAVY"):
                    acc += sev_probs.get(sev, 0.0) / sev_sum
                    if sev_roll < acc:
                        severity = sev
                        break
                tree = cfg.breakdown_tree or BREAKDOWN_TREE
                items = tree.get(severity) or BREAKDOWN_TREE[severity]
                w_sum = sum(x[1] for x in items) or 1.0
                fault_roll = np.random.random()
                acc = 0.0
                code, nodes, consequence = "LIGHT", "прочее", "следует по расписанию"
                for c, w, n, cons in items:
                    acc += w / w_sum
                    if fault_roll < acc:
                        code, nodes, consequence = c, n, cons
                        break

                h_lo, h_hi = BREAKDOWN_HOURS[code]
                repair = float(np.random.uniform(h_lo, h_hi))
                speed = (1.0 if severity == "LIGHT"
                         else float(np.random.uniform(0.45, 0.8)))
                breakdown_types[code] = breakdown_types.get(code, 0) + 1

                if severity == "HEAVY":
                    # Движение невозможно: маневровый локомотив забирает состав,
                    # он теряет рейс и возвращается в депо СПб на ремонт.
                    breakdown_stats["total"] += 1
                    s.status = "CASUALTY"
                    s.location = "SPB"
                    s.downtime_hours_remaining = repair
                    s.mission = "await-repair"
                    s.breakdown_day = day
                    rescue = float(np.random.uniform(cfg.rescue_hours_min, cfg.rescue_hours_max))
                    rescue_delay_min[day] = rescue_delay_min.get(day, 0.0) + (rescue + repair) * 60.0
                    s.add_daily_km(ROUTE_KM * float(np.random.uniform(0.05, 0.25)))
                    events.append({
                        "day": day, "train": s.id, "event": "BREAKDOWN_HEAVY",
                        "detail": (f"{code} ({nodes}): {consequence}; ремонт "
                                   f"~{repair:.0f} ч после эвакуации ~{rescue:.0f} ч"),
                    })
                    continue

                # LIGHT / MEDIUM — состав доезжает до МСК (при MEDIUM медленнее)
                s.add_daily_km(2 * ROUTE_KM * speed)
                delay_min = (1.0 / speed - 1.0) * (2 * ROUTE_KM) / 120.0 * 60.0
                casualty_delay_min[day] = casualty_delay_min.get(day, 0.0) + delay_min
                events.append({
                    "day": day, "train": s.id, "event": f"BREAKDOWN_{severity}",
                    "detail": (f"{code} ({nodes}): {consequence}; "
                               f"задержка ~{delay_min:.0f} мин, ремонт ~{repair:.0f} ч"),
                })

                if severity == "MEDIUM":
                    breakdown_stats["total"] += 1
                    if cfg.reserve_mode == "SLIDING":
                        # Ремонт идёт ночными блоками: состав может следовать
                        # с неполной тягой и остаётся в графике (К_эг не падает)
                        s.night_hours_remaining += repair
                        s.mission = "repair-night"
                    else:
                        s.status = "CASUALTY"
                        s.location = "MSK"
                        s.downtime_hours_remaining = repair
                        s.mission = "await-repair"
                    s.breakdown_day = day

                    if cfg.reserve_mode == "SLIDING":
                        covered = True
                        reserve = next(
                            (x for x in active
                             if x.location == "MSK" and x is not s
                             and x.status in ("READY", "COMMERCIAL")),
                            None,
                        )
                        if reserve is not None:
                            reserve.location = "SPB"
                            reserve.add_daily_km(ROUTE_KM)
                            breakdown_stats["reserve_move_km"] += ROUTE_KM
                            events.append({"day": day, "train": reserve.id,
                                           "event": "RESERVE_SLIDE",
                                           "detail": "вышел вместо аварийного МСК->СПб"})
                        else:
                            covered = False

                        donor = next(
                            (x for x in hot if x.status == "HOT_RESERVE"), None
                        )
                        if donor is not None:
                            donor.status = "COMMERCIAL"
                            donor.location = "MSK"
                            donor.mission = "hot-to-msk"
                            events.append({"day": day, "train": donor.id,
                                           "event": "HOT_MOVE",
                                           "detail": "занял место скользящего резерва в МСК"})
                            hot = [x for x in hot if x is not donor]
                        else:
                            covered = False

                        if covered:
                            breakdown_stats["covered"] += 1
                            breakdown_stats["delay_min"] += delay_min
                        else:
                            breakdown_stats["uncovered"] += 1

        # Восстановление пула: место ушедшего поезда резерва занимает
        # первый готовый состав
        hot = _refill_hot_reserve(active, hot, cfg, target=hot_target)
        hot_ids = [t.id for t in hot]

        # ---- 6. Расстановка по реальному графику оборота ----
        # В рейсы ставятся только готовые составы: находящиеся в депо
        # (ревизии) и аварийные из графика исключены
        ready_pool = [t for t in active if t.status == "READY"]
        n_runs = min(len(ROTATION_SUMS), len(ready_pool))
        np.random.shuffle(ready_pool)
        assigned_km = 0.0
        for idx in range(n_runs):
            t = ready_pool[idx]
            run_km = ROTATION_SUMS[idx] * float(np.random.uniform(0.98, 1.02))
            if run_km > 2.44 * (t.min_km_to_next_maintenance()):
                run_km = min(run_km, max(1500.0, t.min_km_to_next_maintenance()))
            t.status = "COMMERCIAL"
            t.location = "MSK" if idx % 2 == 0 else "SPB"
            t.mission = None
            t.add_daily_km(run_km)
            assigned_km += run_km
            t.runs_since_clean += 1
            if t.runs_since_clean >= CLEAN_INTERVAL_RUNS:
                t.awaiting_clean = True

        # ---- 7. Заход в депо на ночную смену (после рейсов) ----
        # Позиции в этот момент заняты работами прошлых суток
        depot.rebuild(active)
        # K_eg-ограничитель: плановые (несрочные) заходы, выводящие состав
        # из графика, не допускаются, если готовность упадёт ниже норматива.
        # Срочные заходы обходят ограничитель (перепробег недопустим).
        # Один слот резервируется под внеплановый ремонт (авария).
        down_limit = max(
            1,
            int(len(active) * (1.0 - cfg.target_k_eg / 100.0)) - 1,
        )
        down_now = sum(1 for t in active if is_unavailable(t, day))
        for t in [x for x in active if x.status == "CASUALTY"]:
            repair_plan = ServicePlan(
                cycle=None, lathe=False, clean=False, critical=True
            )
            if depot.can_admit(repair_plan, depot.occupancy):
                depot.admit(t, repair_plan, day)
                events.append({"day": day, "train": t.id, "event": "REPAIR_START",
                               "detail": "внеплановый ремонт в депо СПб"})
            else:
                deferred_jobs += 1

        for t, plan in planned:
            if (
                strategy == "PROPOSED"
                and not plan.night_block
                and not plan.critical
                and down_now >= down_limit
            ):
                deferred_jobs += 1
                events.append({"day": day, "train": t.id, "event": "KEG_HOLD",
                               "detail": "перенесён ради К_эг >= норматива"})
                continue
            if depot.can_admit(plan, depot.occupancy):
                depot.admit(t, plan, day)
                if not plan.night_block:
                    down_now += 1
            else:
                deferred_jobs += 1
                events.append({"day": day, "train": t.id, "event": "DEFERRED",
                               "detail": plan.cycle or ("lathe" if plan.lathe else "clean")})

        # ---- 8. Обточка на тандемном станке (2 часа на поезд) ----
        served = depot.lathe_shift(day)
        for t in served:
            if t.status == "LATHE_QUEUE":
                t.status = "READY"
                t.location = "SPB"

        # ---- 9. Возврат после суточного цикла ----
        for t in active:
            if t.status == "COMMERCIAL":
                t.status = "READY"

        # ---- 10. Статистика суток ----
        # Готовность считается к началу суток (06:00): поезд, у которого
        # работы идут только в ночную смену, к утру уже в строю и в этот
        # день выполняет рейс. Недоступны лишь составы, стоящие в депо
        # с прошлых суток (ревизии), и аварийные.
        down = sum(1 for t in active if is_unavailable(t, day))
        operational = len(active) - down
        fleet_size = len(active)
        daily_stats.append(
            {
                "day": day,
                "year": (day // 365) + 1,
                "month_abs": (day // 30) + 1,
                "total_fleet": fleet_size,
                "hot_reserve": len(hot),
                "depot_load": depot.occupancy,
                "depot_down": down,
                "depot_hours": round(depot.hours_worked_tonight, 1),
                "k_eg": operational / fleet_size if fleet_size else 1.0,
                "assigned_km": round(assigned_km, 1),
                "runs_served": n_runs,
                "breakdowns": breakdown_stats["total"],
                "delay_min": round(
                    casualty_delay_min.get(day, 0.0) + rescue_delay_min.get(day, 0.0), 1
                ),
            }
        )

    df = pd.DataFrame(daily_stats)
    summary = {
        "strategy": strategy,
        "reserve_mode": cfg.reserve_mode,
        "overruns": len(overruns),
        "overrun_sample": overruns[:100],
        "breakdowns": breakdown_stats,
        "breakdown_types": breakdown_types,
        "deferred_jobs": deferred_jobs,
        "lathe_deferred_overruns": lathe_deferred_overruns,
        "depot_log_len": len(depot.log),
        "events": events,
    }
    return df, summary


def fleet_window(df: pd.DataFrame, fleet_max: int) -> pd.DataFrame:
    window = df[df["total_fleet"] == fleet_max]
    if window.empty:
        window = df.tail(min(365, len(df)))
    return window.tail(365) if len(window) > 365 else window


def aggregate_years(df: pd.DataFrame) -> pd.DataFrame:
    return (
        df.groupby("year")
        .agg(
            fleet=("total_fleet", "max"),
            k_mean=("k_eg", "mean"),
            k_min=("k_eg", "min"),
            d_mean=("depot_load", "mean"),
            d_max=("depot_load", "max"),
            h_max=("depot_hours", "max"),
            km=("assigned_km", "sum"),
        )
        .reset_index()
    )


def aggregate_months(df: pd.DataFrame) -> pd.DataFrame:
    return (
        df.groupby(["year", "month_abs"])
        .agg(
            fleet=("total_fleet", "max"),
            k_mean=("k_eg", "mean"),
            k_min=("k_eg", "min"),
            d_max=("depot_load", "max"),
            h_max=("depot_hours", "max"),
            km=("assigned_km", "sum"),
            runs=("runs_served", "mean"),
        )
        .reset_index()
    )


def simulate_many(cfg: SimConfig, strategy: str, n_runs: int, progress=None) -> tuple[pd.DataFrame, pd.DataFrame, dict]:
    frames = []
    rows = []
    last_summary = {}
    for i in range(n_runs):
        run_cfg = SimConfig(**{**cfg.__dict__, "seed": cfg.seed + i})
        df, summary = simulate(run_cfg, strategy=strategy)
        window = fleet_window(df, cfg.fleet_max)
        frames.append(df)
        rows.append(
            {
                "run": i + 1,
                "k_mean": window["k_eg"].mean(),
                "k_min": window["k_eg"].min(),
                "k_p5": window["k_eg"].quantile(0.05),
                "d_max": window["depot_load"].max(),
                "overruns": summary["overruns"],
                "deferred": summary["deferred_jobs"],
            }
        )
        last_summary = summary
        if progress is not None:
            progress(i + 1, n_runs)
    stats = pd.DataFrame(rows)
    return pd.concat(frames, ignore_index=True), stats, last_summary


def export_results(base_df: pd.DataFrame, prop_df: pd.DataFrame, stats: pd.DataFrame,
                   summary_base: dict, summary_prop: dict, path: str):
    with pd.ExcelWriter(path, engine="openpyxl") as writer:
        prop_df.to_excel(writer, sheet_name="Дни_PROJECT", index=False)
        base_df.to_excel(writer, sheet_name="Дни_BASELINE", index=False)
        if not stats.empty:
            stats.to_excel(writer, sheet_name="MonteCarlo", index=False)
        pd.DataFrame(summary_prop.get("overrun_sample", [])).to_excel(
            writer, sheet_name="Нарушения_PROJECT", index=False
        )
        pd.DataFrame(summary_base.get("overrun_sample", [])).to_excel(
            writer, sheet_name="Нарушения_BASELINE", index=False
        )
        pd.DataFrame(summary_prop.get("events", [])).to_excel(
            writer, sheet_name="События_PROJECT", index=False
        )


# ==========================================
# ГРАФИЧЕСКИЙ ИНТЕРФЕЙС (TKINTER)
# ==========================================
class VSMApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("FleetSync ВСМ-1 v5 | Моделирование парка ЭВС360 | Команда «Восток»")
        self.geometry("1260x780")
        self.minsize(1050, 640)

        self.var_years = tk.StringVar(value="5")
        self.var_fleet_start = tk.StringVar(value="6")
        self.var_fleet_max = tk.StringVar(value="43")
        self.var_lathe_hours = tk.StringVar(value="2.0")
        self.var_planned_depot = tk.StringVar(value="8")
        self.var_max_depot = tk.StringVar(value="3")
        self.var_hot_reserve = tk.StringVar(value="4")
        self.var_target_k_eg = tk.StringVar(value="89.0")
        self.var_reserve_mode = tk.StringVar(value="SLIDING")
        self.var_mc_runs = tk.StringVar(value="20")
        self.var_breakdown_gate = tk.StringVar(value="0.30")

        # редактируемое дерево отказов (копия заводских настроек)
        self.cfg_severity = dict(SEVERITY_PROBS)
        self.cfg_tree = {k: [list(x) for x in v] for k, v in BREAKDOWN_TREE.items()}

        self.df_base = None
        self.df_prop = None
        self.summary_base = None
        self.summary_prop = None
        self.mc_stats = pd.DataFrame()

        self._build_ui()
        self.run_simulation_ui()

    def _build_ui(self):
        main_paned = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        left_frame = ttk.LabelFrame(main_paned, text=" Параметры системы ВСМ v5 ", padding=10)
        main_paned.add(left_frame, weight=1)

        fields = [
            ("Горизонт симуляции (лет):", self.var_years),
            ("Стартовый парк (поездов):", self.var_fleet_start),
            ("Итоговый парк (поездов):", self.var_fleet_max),
            ("Время обточки колес (час):", self.var_lathe_hours),
            ("Рем-позиции IS100-IS540:", self.var_planned_depot),
            ("Пути с домкратами IS600/700:", self.var_max_depot),
            ("Горячий резерв в СПб:", self.var_hot_reserve),
            ("Норматив К_эг (%):", self.var_target_k_eg),
            ("Гейт отказов за сутки:", self.var_breakdown_gate),
            ("Прогонов Monte Carlo:", self.var_mc_runs),
        ]
        for row, (label, var) in enumerate(fields):
            ttk.Label(left_frame, text=label).grid(row=row, column=0, sticky="w", pady=3)
            ttk.Entry(left_frame, textvariable=var, width=10).grid(row=row, column=1, sticky="e", pady=3)

        ttk.Label(left_frame, text="Режим резерва:").grid(
            row=len(fields), column=0, sticky="w", pady=3
        )
        mode_frame = ttk.Frame(left_frame)
        mode_frame.grid(row=len(fields), column=1, sticky="e", pady=3)
        for mode, label in (("LAZY", "Без подмены"), ("PARTIAL", "Частичный"),
                            ("SLIDING", "Скользящий")):
            ttk.Radiobutton(
                mode_frame, text=label, value=mode, variable=self.var_reserve_mode
            ).pack(anchor="w")

        btn_run = ttk.Button(left_frame, text="Запустить расчет", command=self.run_simulation_ui)
        btn_run.grid(row=len(fields) + 1, column=0, columnspan=2, sticky="ew", pady=12)

        btn_mc = ttk.Button(left_frame, text="Monte Carlo (N прогонов)", command=self.run_monte_carlo)
        btn_mc.grid(row=len(fields) + 2, column=0, columnspan=2, sticky="ew", pady=2)

        btn_export = ttk.Button(left_frame, text="Экспорт в Excel", command=self.export_excel)
        btn_export.grid(row=len(fields) + 3, column=0, columnspan=2, sticky="ew", pady=2)

        self.mc_progress = ttk.Progressbar(left_frame, mode="determinate", maximum=100)
        self.mc_progress.grid(row=len(fields) + 4, column=0, columnspan=2, sticky="ew", pady=5)

        help_box = tk.Text(
            left_frame, height=13, width=30, wrap="word", font=("Arial", 8),
            bg="#f5f5f5", relief="flat",
        )
        help_box.insert(
            "1.0",
            "Особенности v5:\n"
            "• Горячий резерв: 4 поезда постоянно в СПб, запас хода\n"
            "  >= 1493 км, плановая ротация.\n"
            "• Скользящий резерв (СПБ->МСК): аварийный состав доезжает\n"
            "  до МСК и уходит в депо СПб (~10% IS600); состав из МСК\n"
            "  выходит вместо него; горячий резерв занимает его место;\n"
            "  резерв пополняется первым готовым составом.\n"
            "• BASELINE без ночных блоков: сравнение честное.\n"
            "• Депо: 8 рем-позиций IS100-IS540 + 3 пути с домкратами\n"
            "  IS600/700, бюджет 120 поездо-часов/сут; ревизии и аварийные\n"
            "  ремонты ведутся в три смены.\n"
            "• K_эг-ограничитель: плановые заходы переносятся, если уронят\n"
            "  готовность ниже норматива; слот под аварию зарезервирован.\n"
            "• Контроль перепробегов: перепробег недопустим (срочный заход\n"
            "  до жёсткого предела), журнал нарушений и каскадов.\n"
            "• Дерево отказов: гейт x тяжесть x узел; веса и состав\n"
            "  узлов редактируются на вкладке «Дерево отказов».\n"
            "• Monte Carlo: доверительные интервалы по К_эг.\n",
        )
        help_box.config(state="disabled")
        help_box.grid(row=len(fields) + 5, column=0, columnspan=2, sticky="ew", pady=5)

        right_frame = ttk.Frame(main_paned)
        main_paned.add(right_frame, weight=4)

        self.notebook = ttk.Notebook(right_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.tab_summary = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(self.tab_summary, text="Сводка и вердикты")
        self.tab_stats = ttk.Frame(self.notebook, padding=4)
        self.notebook.add(self.tab_stats, text="Погодов/помесячно")
        self.tab_charts = ttk.Frame(self.notebook, padding=4)
        self.notebook.add(self.tab_charts, text="Графики")
        self.tab_events = ttk.Frame(self.notebook, padding=4)
        self.notebook.add(self.tab_events, text="Журнал событий")
        self.tab_tree = ttk.Frame(self.notebook, padding=6)
        self.notebook.add(self.tab_tree, text="Дерево отказов")

        self._init_summary_tab()
        self._init_stats_tab()
        self._init_charts_tab()
        self._init_events_tab()
        self._init_fault_tree_tab()

    def _init_summary_tab(self):
        container = ttk.Frame(self.tab_summary)
        container.pack(fill=tk.BOTH, expand=True)
        scroll = ttk.Scrollbar(container, orient="vertical")
        self.txt_summary = tk.Text(
            container, wrap="word", font=("Consolas", 10), bg="#fafafa",
            relief="solid", borderwidth=1, yscrollcommand=scroll.set,
        )
        scroll.config(command=self.txt_summary.yview)
        self.txt_summary.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.lbl_mc = ttk.Label(self.tab_summary, text="", font=("Consolas", 10))
        self.lbl_mc.pack(fill=tk.X, pady=4)

    def _init_stats_tab(self):
        sub = ttk.Notebook(self.tab_stats)
        sub.pack(fill=tk.BOTH, expand=True)

        self.tree_yearly = self._make_tree(
            sub, "Погодовая статистика (PROPOSED)",
            ("year", "fleet", "k_mean", "k_min", "d_mean", "d_max", "km", "verdict"),
            ("Год", "Парк", "К_эг ср.", "К_эг мин.", "Депо ср.", "Депо пик", "Пробег, км", "Вердикт"),
        )
        self.tree_monthly = self._make_tree(
            sub, "Помесячная статистика (PROPOSED)",
            ("month_abs", "year", "fleet", "k_mean", "k_min", "d_max", "km", "verdict"),
            ("Месяц №", "Год", "Парк", "К_эг ср.", "К_эг мин.", "Депо пик", "Пробег, км", "Статус"),
        )
        self.tree_yearly_base = self._make_tree(
            sub, "Погодовой BASELINE",
            ("year", "fleet", "k_mean", "k_min", "d_mean", "d_max", "km", "verdict"),
            ("Год", "Парк", "К_эг ср.", "К_эг мин.", "Депо ср.", "Депо пик", "Пробег, км", "Вердикт"),
        )

    def _make_tree(self, parent, title, cols, headers):
        frame = ttk.Frame(parent)
        parent.add(frame, text=title)
        tree = ttk.Treeview(frame, columns=cols, show="headings", height=10)
        scroll_v = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        scroll_h = ttk.Scrollbar(frame, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=scroll_v.set, xscrollcommand=scroll_h.set)
        for c, h in zip(cols, headers):
            tree.heading(c, text=h)
            tree.column(c, width=100, anchor="center")
        tree.column("verdict", width=320, anchor="w")
        tree.grid(row=0, column=0, sticky="nsew")
        scroll_v.grid(row=0, column=1, sticky="ns")
        scroll_h.grid(row=1, column=0, sticky="ew")
        frame.grid_rowconfigure(0, weight=1)
        frame.grid_columnconfigure(0, weight=1)
        return tree

    def _init_charts_tab(self):
        self.chart_frame = ttk.Frame(self.tab_charts)
        self.chart_frame.pack(fill=tk.BOTH, expand=True)

    def _init_events_tab(self):
        container = ttk.Frame(self.tab_events)
        container.pack(fill=tk.BOTH, expand=True)
        scroll = ttk.Scrollbar(container, orient="vertical")
        self.txt_events = tk.Text(
            container, wrap="none", font=("Consolas", 9), bg="#fafafa",
            relief="solid", borderwidth=1, yscrollcommand=scroll.set,
        )
        scroll.config(command=self.txt_events.yview)
        self.txt_events.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

    # ---------- Редактор дерева отказов ----------
    def _init_fault_tree_tab(self):
        info = ttk.Label(
            self.tab_tree,
            text=("Дерево внеплановых отказов (двойной клик по ячейке — правка, Enter — сохранить). "
                  "Веса нормируются внутри своей группы. Гейт и удельная частота — на левой панели."),
            wraplength=860, justify="left",
        )
        info.pack(anchor="w", pady=(0, 6))

        editor = ttk.Frame(self.tab_tree)
        editor.pack(fill=tk.BOTH, expand=True)
        cols = ("node", "weight", "sev", "hours", "consequence")
        self.tree_fault = ttk.Treeview(editor, columns=cols, show="headings", height=17)
        headers = ("Группа / тип узла", "Вес", "Доля тяжести, %",
                   "Ремонт, ч", "Следствие для движения")
        for c, h in zip(cols, headers):
            self.tree_fault.heading(c, text=h)
        self.tree_fault.column("node", width=310, anchor="w")
        self.tree_fault.column("weight", width=70, anchor="center")
        self.tree_fault.column("sev", width=120, anchor="center")
        self.tree_fault.column("hours", width=90, anchor="center")
        self.tree_fault.column("consequence", width=380, anchor="w")
        tree_scroll = ttk.Scrollbar(editor, orient="vertical", command=self.tree_fault.yview)
        self.tree_fault.configure(yscrollcommand=tree_scroll.set)
        self.tree_fault.grid(row=0, column=0, sticky="nsew")
        tree_scroll.grid(row=0, column=1, sticky="ns")
        editor.grid_rowconfigure(0, weight=1)
        editor.grid_columnconfigure(0, weight=1)

        self.tree_fault.tag_configure("sev", background="#e8eef7")
        self.tree_fault.bind("<Double-1>", self._fault_dblclick)
        self.fault_entry = None

        controls = ttk.Frame(self.tab_tree)
        controls.pack(fill=tk.X, pady=6)
        ttk.Button(controls, text="Нормировать по группам",
                   command=self._fault_normalize).pack(side=tk.LEFT, padx=3)
        ttk.Button(controls, text="Сбросить к заводским",
                   command=self._fault_reset).pack(side=tk.LEFT, padx=3)
        ttk.Button(controls, text="Пересчитать модель",
                   command=self.run_simulation_ui).pack(side=tk.LEFT, padx=3)

        self.lbl_fault_status = ttk.Label(self.tab_tree, text="", font=("Consolas", 9))
        self.lbl_fault_status.pack(anchor="w")
        self._refresh_fault_tree()

    def _fault_dblclick(self, event):
        row = self.tree_fault.identify_row(event.y)
        col = self.tree_fault.identify_column(event.x)
        if not row:
            return
        if self.fault_entry is not None:
            self.fault_entry.destroy()
            self.fault_entry = None
        bbox = self.tree_fault.bbox(row, col)
        if not bbox:
            return
        x, y, w, h = bbox
        values = self.tree_fault.item(row, "values")
        is_sev = str(values[0]).startswith("-- ")

        if is_sev and col != "#3":
            return
        if not is_sev and col != "#2":
            return
        current = values[2] if is_sev else values[1]
        entry = ttk.Entry(self.tree_fault, width=10, font=("Consolas", 9))
        entry.insert(0, str(current).replace("%", "").replace(",", ".").strip())
        entry.place(x=x, y=y, width=w, height=h)
        entry.focus_set()
        entry.select_range(0, tk.END)
        self.fault_entry = entry
        entry.bind("<Return>", lambda e: self._fault_save(row, is_sev))
        entry.bind("<Escape>", lambda e: self._fault_cancel())

    def _fault_cancel(self):
        if self.fault_entry is not None:
            self.fault_entry.destroy()
            self.fault_entry = None

    def _fault_save(self, row, is_sev):
        entry = self.fault_entry
        if entry is None:
            return
        raw = entry.get().strip().replace(",", ".")
        try:
            val = float(raw)
        except ValueError:
            self._fault_cancel()
            return
        self._fault_cancel()

        if is_sev:
            mapping = {"LIGHT": "LIGHT", "MEDIUM": "MEDIUM", "HEAVY": "HEAVY"}
            values = self.tree_fault.item(row, "values")
            label = str(values[0])
            if "ЛЁГК" in label or "ЛЕГК" in label:
                sev_key = mapping["LIGHT"]
            elif "СРЕД" in label:
                sev_key = mapping["MEDIUM"]
            else:
                sev_key = mapping["HEAVY"]
            self.cfg_severity[sev_key] = max(0.0, val / 100.0)
        else:
            mapping = self._fault_row_map()
            ref = mapping.get(row)
            if ref is not None:
                sev, idx = ref
                self.cfg_tree[sev][idx][1] = max(0.0, val)
        self._refresh_fault_tree()

    def _fault_row_map(self) -> dict:
        """row_id -> (severity, индекс узла) для текущего состояния таблицы."""
        mapping: dict[str, tuple[str, int]] = {}
        sev = None
        idx = 0
        for row in self.tree_fault.get_children():
            label = str(self.tree_fault.item(row, "values")[0])
            if label.startswith("-- "):
                if "ЛЁГК" in label or "ЛЕГК" in label:
                    sev = "LIGHT"
                elif "СРЕД" in label:
                    sev = "MEDIUM"
                else:
                    sev = "HEAVY"
                idx = 0
            elif sev is not None:
                mapping[row] = (sev, idx)
                idx += 1
        return mapping

    def _fault_normalize(self):
        sev_sum = sum(self.cfg_severity.values()) or 1.0
        for k in self.cfg_severity:
            self.cfg_severity[k] /= sev_sum
        for items in self.cfg_tree.values():
            total = sum(x[1] for x in items) or 1.0
            for item in items:
                item[1] /= total
        self._refresh_fault_tree()

    def _fault_reset(self):
        self.cfg_severity = dict(SEVERITY_PROBS)
        self.cfg_tree = {k: [list(x) for x in v] for k, v in BREAKDOWN_TREE.items()}
        self._refresh_fault_tree()

    def _refresh_fault_tree(self):
        tree = self.tree_fault
        for item in tree.get_children():
            tree.delete(item)
        labels = {"LIGHT": "ЛЁГКИЕ (без потери скорости)",
                  "MEDIUM": "СРЕДНИЕ (x0.45-0.8, каскад)",
                  "HEAVY": "ТЯЖЁЛЫЕ (эвакуация маневровым)"}
        for sev in ("LIGHT", "MEDIUM", "HEAVY"):
            tree.insert(
                "", "end", tags=("sev",),
                values=(f"-- {labels[sev]} --", "", f"{self.cfg_severity[sev] * 100:.0f}", "",
                        "группа тяжести"),
            )
            for code, w, nodes, cons in self.cfg_tree[sev]:
                h_lo, h_hi = BREAKDOWN_HOURS[code]
                tree.insert(
                    "", "end",
                    values=(f"   {code} — {nodes}", f"{w:.3f}", "",
                            f"{h_lo:.0f}-{h_hi:.0f}", cons),
                )
        gate = self._read_gate_safe()
        rate = BREAKDOWN_RATE_PER_MKM * (gate / 0.30)
        self.lbl_fault_status.config(
            text=(f"Гейт: {gate * 100:.0f}% событий в парке за сутки | "
                  f"удельная частота: {rate:.1f} на 10^6 поездо-км | "
                  f"MTBF ~ {1e6 / rate:,.0f} км | событий/год на состав: {rate * 2700 / 1e6 * 365:.2f}")
        )

    def _read_gate_safe(self) -> float:
        try:
            return float(self.var_breakdown_gate.get())
        except ValueError:
            return BREAKDOWN_GATE

    def _read_config(self) -> SimConfig:
        return SimConfig(
            sim_years=float(self.var_years.get()),
            fleet_start=int(self.var_fleet_start.get()),
            fleet_max=int(self.var_fleet_max.get()),
            lathe_hours=float(self.var_lathe_hours.get()),
            racks=int(self.var_planned_depot.get()),
            jacks=int(self.var_max_depot.get()),
            hot_reserve=int(self.var_hot_reserve.get()),
            target_k_eg=float(self.var_target_k_eg.get()),
            reserve_mode=self.var_reserve_mode.get(),
            breakdown_gate=float(self.var_breakdown_gate.get()),
            severity_probs=dict(self.cfg_severity),
            breakdown_tree={k: [list(x) for x in v] for k, v in self.cfg_tree.items()},
            seed=42,
        )

    def run_simulation_ui(self):
        try:
            cfg = self._read_config()
        except ValueError:
            messagebox.showerror("Ошибка ввода", "Проверьте корректность введенных чисел!")
            return

        self.df_base, self.summary_base = simulate(cfg, strategy="BASELINE")
        self.df_prop, self.summary_prop = simulate(cfg, strategy="PROPOSED")

        self._update_summary_view(cfg)
        self._update_stats_views(cfg)
        self._update_events_view(cfg)
        self._update_charts(cfg)
        if hasattr(self, "lbl_fault_status"):
            self._refresh_fault_tree()

    def run_monte_carlo(self):
        try:
            cfg = self._read_config()
            n_runs = max(2, int(self.var_mc_runs.get()))
        except ValueError:
            messagebox.showerror("Ошибка ввода", "Проверьте корректность введенных чисел!")
            return

        self.mc_stats = pd.DataFrame()
        self.mc_progress["value"] = 0

        def progress(done: int, total: int):
            try:
                self.after(0, lambda: self.mc_progress.config(value=100.0 * done / total))
            except RuntimeError:
                pass

        def worker():
            try:
                _, stats, _ = simulate_many(cfg, "PROPOSED", n_runs, progress=progress)
            except Exception as exc:  # noqa: BLE001
                self._show_mc_error(str(exc))
                return
            self.mc_stats = stats
            try:
                self.after(0, lambda: self._update_mc_label(cfg, n_runs))
            except RuntimeError:
                pass

        threading.Thread(target=worker, daemon=True).start()

    def _show_mc_error(self, text: str):
        try:
            self.after(0, lambda: messagebox.showerror("Monte Carlo", text))
        except RuntimeError:
            pass

    def _update_mc_label(self, cfg: SimConfig, n_runs: int):
        stats = self.mc_stats
        if stats.empty:
            return
        ci_low = stats["k_mean"].quantile(0.05) * 100
        ci_high = stats["k_mean"].quantile(0.95) * 100
        p_fail = (stats["k_min"] * 100 < cfg.target_k_eg).mean() * 100
        self.lbl_mc.config(
            text=(
                f"Monte Carlo: {n_runs} прогонов | К_эг ср. 90% ДИ: "
                f"[{ci_low:.2f}%; {ci_high:.2f}%] | вероятность суток ниже норматива: {p_fail:.1f}% "
                f"| перепробеги (среднее): {stats['overruns'].mean():.1f}"
            )
        )
        self._update_charts(cfg)

    def _get_dynamic_verdicts(self, k_min, hours_peak, cfg: SimConfig):
        target = cfg.target_k_eg
        status_k = (
            f"[НОРМА] запас +{k_min - target:.2f}%"
            if k_min >= target
            else f"[НАРУШЕНИЕ] дефицит -{target - k_min:.2f}%"
        )
        if hours_peak <= DAILY_DEPOT_HOURS:
            status_d = f"[НОРМА] макс. загрузка {hours_peak:.0f} из {DAILY_DEPOT_HOURS:.0f} поездо-ч/сут"
        else:
            status_d = f"[ПЕРЕГРУЗКА] {hours_peak:.0f} поездо-ч/сут сверх {DAILY_DEPOT_HOURS:.0f}"
        return status_k, status_d

    def _update_summary_view(self, cfg: SimConfig):
        wb = fleet_window(self.df_base, cfg.fleet_max)
        wp = fleet_window(self.df_prop, cfg.fleet_max)

        def pack(window):
            return {
                "k_mean": window["k_eg"].mean() * 100,
                "k_min": window["k_eg"].min() * 100,
                "d_mean": window["depot_load"].mean(),
                "d_max": int(window["depot_load"].max()),
                "d_hours": float(window["depot_hours"].max()),
                "km": window["assigned_km"].sum(),
                "runs": window["runs_served"].mean(),
            }

        pb, pp = pack(wb), pack(wp)
        sk_b, sd_b = self._get_dynamic_verdicts(pb["k_min"], pb["d_hours"], cfg)
        sk_p, sd_p = self._get_dynamic_verdicts(pp["k_min"], pp["d_hours"], cfg)

        brk = self.summary_prop["breakdowns"]
        cov_rate = 0.0
        if brk["total"] > 0:
            cov_rate = 100.0 * brk["covered"] / brk["total"]

        text = "=" * 92 + "\n"
        text += f" СРАВНИТЕЛЬНЫЙ АНАЛИЗ ПРИ ПОЛНОМ ПАРКЕ {cfg.fleet_max} ПОЕЗДОВ (СРЕЗ 365 ДНЕЙ)\n"
        text += f" Норматив: К_эг >= {cfg.target_k_eg:.1f}% | Депо: {cfg.racks} позиций + {cfg.jacks} путей с домкратами | Резерв: {cfg.reserve_mode}\n"
        text += "=" * 92 + "\n\n"

        text += "1. ТРАДИЦИОННАЯ СХЕМА (BASELINE, без ночных блоков и подмен):\n"
        text += f"   • Среднегодовой К_эг:        {pb['k_mean']:.2f}%\n"
        text += f"   • Минимальный суточный К_эг: {pb['k_min']:.2f}%  --> {sk_b}\n"
        text += f"   • Задействовано в депо:      {pb['d_mean']:.2f} составов/сут\n"
        text += f"   • Макс. загрузка депо:       {pb['d_hours']:.0f} поездо-ч/сут  --> {sd_b}\n"
        text += f"   • Нарушения интервалов:      {self.summary_base['overruns']} (перепробег)\n"
        text += f"   • Отложенные заходы:         {self.summary_base['deferred_jobs']}\n"
        text += f"   • Суммарный пробег:          {pb['km']:,.0f} км\n\n"

        text += "2. ПРЕДЛАГАЕМАЯ СИСТЕМА (PROPOSED, ночные сервисные блоки):\n"
        text += f"   • Среднегодовой К_эг:        {pp['k_mean']:.2f}%\n"
        text += f"   • Минимальный суточный К_эг: {pp['k_min']:.2f}%  --> {sk_p}\n"
        text += f"   • Задействовано в депо:      {pp['d_mean']:.2f} составов/сут\n"
        text += f"   • Макс. загрузка депо:       {pp['d_hours']:.0f} поездо-ч/сут  --> {sd_p}\n"
        text += f"   • Нарушения интервалов:      {self.summary_prop['overruns']} (перепробег)\n"
        text += f"   • Отложенные заходы:         {self.summary_prop['deferred_jobs']}\n"
        text += f"   • Поездов в горячем резерве: {int(wp['hot_reserve'].mean())} (все в СПб)\n"
        text += f"   • Суммарный пробег:          {pp['km']:,.0f} км\n\n"

        text += "3. СКОЛЬЗЯЩИЙ РЕЗЕРВ: ОТКАЗЫ НА ПЕРЕГОНЕ СПБ -> МСК:\n"
        text += f"   • Всего отказов в пути:      {brk['total']}\n"
        text += f"   • Каскад закрыт:             {brk['covered']} ({cov_rate:.1f}%)\n"
        text += f"   • Не закрыто:                {brk['uncovered']}\n"
        text += "     Схема каскада: аварийный состав (x0.5) доезжает до МСК и\n"
        text += "     уходит на ремонт в СПб (~10% IS600); состав скользящего\n"
        text += "     резерва из МСК выходит вместо него по расписанию МСК->СПб;\n"
        text += "     его место занимает поезд горячего резерва СПб; место в\n"
        text += "     горячем резерве замещает первый готовый состав.\n"
        text += f"   • Пробег скользящего резерва: {brk.get('reserve_move_km', 0.0):,.0f} км\n"
        text += f"   • Сэкономленное время:       {brk['delay_min'] / 60:.0f} поездо-часов\n\n"

        typ = self.summary_prop.get("breakdown_types", {})
        light = sum(typ.get(k, 0) for k in ("DOOR", "LIGHT", "HVAC", "TOILET"))
        medium = sum(typ.get(k, 0) for k in ("PART_TRACTION", "BRAKE", "POWER", "BOGIE"))
        heavy = sum(typ.get(k, 0) for k in ("COUPLER", "ATRACTION", "POWER_FULL"))
        total_ev = max(1, sum(typ.values()))
        text += "4. ДЕРЕВО ВНЕПЛАНОВЫХ ОТКАЗОВ (гейт 30%, калибровка по 10^6 поездо-км):\n"
        text += f"   • Всего событий за {cfg.sim_years:.0f} лет: {total_ev} (~{total_ev / cfg.sim_years / cfg.fleet_max:.2f}/год на состав)\n"
        text += f"   • Лёгкие  (следует по расписанию):  {light} ({100 * light / total_ev:.0f}%)\n"
        text += "     двери/освещение/климат/санмодуль — ремонт в ближайший заход;\n"
        text += f"   • Средние (x0.45-0.8, каскад резерва): {medium} ({100 * medium / total_ev:.0f}%)\n"
        text += "     неполная тяга/тормоза/токоприёмник/буксы — депо СПб;\n"
        text += f"   • Тяжёлые (эвакуация маневровым):   {heavy} ({100 * heavy / total_ev:.1f}%)\n"
        text += "     сцепка/полная потеря тяги — потеря рейса, доставка в СПб.\n"
        text += f"   • Удельная частота: {BREAKDOWN_RATE_PER_MKM:.1f} отказов на 10^6 поездо-км\n"
        text += f"   • Пробег на отказ (MTBF): ~{1e6 / BREAKDOWN_RATE_PER_MKM:,.0f} км\n\n"

        text += "-" * 92 + "\n"
        text += " ВЫВОД АЛГОРИТМА:\n"
        success = (
            pp["k_min"] >= cfg.target_k_eg
            and pp["d_hours"] <= DAILY_DEPOT_HOURS
            and self.summary_prop["overruns"] == 0
        )
        if success:
            text += " [УСПЕХ] Предложенная модель удовлетворяет контрактным ограничениям:\n"
            text += " К_эг >= норматива ежедневно, перепробегов нет, депо в пределах 120 поездо-ч/сут.\n"
            text += f" Запас эксплуатационной готовности над нормативом: +{pp['k_mean'] - cfg.target_k_eg:.2f}%."
        else:
            text += (
                " [ВНИМАНИЕ] При данных параметрах регламент нарушается.\n"
                f" Дефицит К_эг: {cfg.target_k_eg - pp['k_min']:.2f}%."
            )

        self.txt_summary.config(state="normal")
        self.txt_summary.delete("1.0", tk.END)
        self.txt_summary.insert("1.0", text)
        self.txt_summary.config(state="disabled")

    def _fill_tree(self, tree, rows, cfg: SimConfig, kind: str = "year"):
        for row in tree.get_children():
            tree.delete(row)
        for _, r in rows.iterrows():
            k_min_val = r["k_min"] * 100
            d_max_val = int(r["d_max"])
            h_max_val = float(r.get("h_max", 0.0))
            depot_ok = h_max_val <= DAILY_DEPOT_HOURS
            if kind == "year":
                ramp_up = int(r["fleet"]) < cfg.fleet_max
                if ramp_up:
                    verdict = (f"Ввод парка ({int(r['fleet'])}/{cfg.fleet_max}): "
                               f"норматив К_эг с полного состава")
                else:
                    verdict = (
                        f"Норма (запас +{k_min_val - cfg.target_k_eg:.1f}%)"
                        if k_min_val >= cfg.target_k_eg and depot_ok
                        else f"Нарушение (К_эг мин. {k_min_val:.1f}%)"
                    )
                tree.insert("", "end", values=(
                    f"Год {int(r['year'])}", int(r["fleet"]), f"{r['k_mean'] * 100:.2f}%",
                    f"{k_min_val:.2f}%", f"{r['d_mean']:.2f}", d_max_val,
                    f"{r['km']:,.0f}", verdict,
                ))
            else:
                verdict = (
                    f"OK (+{k_min_val - cfg.target_k_eg:.1f}%)"
                    if k_min_val >= cfg.target_k_eg and depot_ok
                    else f"Внимание (К_эг {k_min_val:.1f}%)"
                )
                tree.insert("", "end", values=(
                    f"Месяц {int(r['month_abs'])}", f"Год {int(r['year'])}", int(r["fleet"]),
                    f"{r['k_mean'] * 100:.2f}%", f"{k_min_val:.2f}%", d_max_val,
                    f"{r['km']:,.0f}", verdict,
                ))

    def _update_stats_views(self, cfg: SimConfig):
        yearly_p = aggregate_years(self.df_prop)
        monthly_p = aggregate_months(self.df_prop)
        yearly_b = aggregate_years(self.df_base)
        self._fill_tree(self.tree_yearly, yearly_p, cfg, kind="year")
        self._fill_tree(self.tree_monthly, monthly_p, cfg, kind="month")
        self._fill_tree(self.tree_yearly_base, yearly_b, cfg, kind="year")

    def _update_events_view(self, cfg: SimConfig):
        events = self.summary_prop.get("events", [])
        overruns = self.summary_prop.get("overrun_sample", [])
        lines = ["=== ЖУРНАЛ ОТКАЗОВ И ПОДМЕН (первые 200) ==="]
        for e in events[:200]:
            lines.append(
                f"День {e['day']:>4} | поезд {e.get('train', '-'):>3} | {e.get('event', '-'):<10} | {e.get('detail', '')}"
            )
        lines.append("")
        lines.append("=== НАРУШЕНИЯ ИНТЕРВАЛОВ (первые 100) ===")
        for o in overruns[:100]:
            lines.append(
                f"День {o['day']:>4} | поезд {o['train']:>3} | {o['cycle']:<6} | перепробег {o['km']:,} км"
            )
        self.txt_events.delete("1.0", tk.END)
        self.txt_events.insert("1.0", "\n".join(lines))

    def _update_charts(self, cfg: SimConfig):
        try:
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            from matplotlib.figure import Figure
        except ImportError:
            return

        for child in self.chart_frame.winfo_children():
            child.destroy()

        figure = Figure(figsize=(9.0, 6.4), dpi=100)
        ax1 = figure.add_subplot(211)
        ax2 = figure.add_subplot(212)

        ax1.plot(self.df_prop["day"], self.df_prop["k_eg"] * 100, color="#1565c0", lw=0.8,
                 label="PROPOSED")
        ax1.plot(self.df_base["day"], self.df_base["k_eg"] * 100, color="#c62828", lw=0.8,
                 alpha=0.8, label="BASELINE")
        ax1.axhline(cfg.target_k_eg, color="#2e7d32", ls="--", lw=1.0, label="Норматив 89%")
        ax1.set_title("Динамика К_эг по суткам")
        ax1.set_ylabel("К_эг, %")
        ax1.legend(loc="lower left", fontsize=8)
        ax1.grid(alpha=0.3)

        hmax = max(
            float(self.df_prop["depot_hours"].max()),
            float(self.df_base["depot_hours"].max()),
        )
        ax2.hist(self.df_prop["depot_hours"], bins=25,
                 color="#1565c0", alpha=0.75, label="PROPOSED")
        ax2.hist(self.df_base["depot_hours"], bins=25,
                 color="#c62828", alpha=0.45, label="BASELINE")
        ax2.axvline(DAILY_DEPOT_HOURS, color="#2e7d32", ls="--", lw=1.0,
                    label=f"Лимит {DAILY_DEPOT_HOURS:.0f} поездо-ч")
        ax2.set_title("Суточная загрузка депо Обухово")
        ax2.set_xlabel("Поездо-часы в сутки")
        ax2.set_ylabel("Дней")
        ax2.legend(loc="upper right", fontsize=8)
        ax2.grid(alpha=0.3)
        if hmax > DAILY_DEPOT_HOURS * 1.1:
            ax2.set_xlim(0, DAILY_DEPOT_HOURS * 1.1)

        figure.tight_layout()
        canvas = FigureCanvasTkAgg(figure, master=self.chart_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def export_excel(self):
        if self.df_prop is None:
            messagebox.showinfo("Экспорт", "Сначала выполните расчет.")
            return
        path = filedialog.asksaveasfilename(
            title="Сохранить результаты",
            defaultextension=".xlsx",
            filetypes=[("Excel", "*.xlsx")],
            initialfile="vsm1_results.xlsx",
        )
        if not path:
            return
        export_results(
            self.df_base, self.df_prop, self.mc_stats,
            self.summary_base, self.summary_prop, path,
        )
        messagebox.showinfo("Экспорт", f"Файл сохранен:\n{path}")


if __name__ == "__main__":
    app = VSMApp()
    app.mainloop()
