@echo off
chcp 866 >nul
title FleetSync VSM-1 - запуск
cd /d "%~dp0"

rem ============================================================
rem  Универсальный запуск FleetSync ВСМ-1 (nauka_v5.py)
rem  Нужен только Python 3.10+. Зависимости ставятся сами.
rem ============================================================

rem --- 1. Поиск Python ---
set "PY="
where py >nul 2>nul
if not errorlevel 1 set "PY=py -3"
if not defined PY (
    where python >nul 2>nul
    if not errorlevel 1 set "PY=python"
)
if not defined PY (
    echo.
    echo [ОШИБКА] Python не найден.
    echo Установите Python 3.10+ : https://www.python.org/downloads/
    echo ВАЖНО: при установке включите галочку "Add python.exe to PATH".
    echo.
    pause
    exit /b 1
)

rem --- 2. Проверка зависимостей ---
echo Проверка зависимостей...
%PY% -c "import numpy, pandas, openpyxl, matplotlib" >nul 2>nul
if errorlevel 1 (
    echo Зависимости не найдены. Устанавливаю, это займет 1-2 минуты...
    %PY% -m pip install --upgrade pip
    %PY% -m pip install -r requirements.txt
    if errorlevel 1 (
        echo.
        echo [ОШИБКА] Не удалось установить зависимости.
        echo Проверьте подключение к интернету и запустите файл заново.
        echo.
        pause
        exit /b 1
    )
)

rem --- 3. Запуск программы ---
echo Запуск программы...
%PY% "nauka_v5.py"
if errorlevel 1 (
    echo.
    echo [ОШИБКА] Программа завершилась с ошибкой. Текст ошибки выше.
    pause
)
exit /b 0
