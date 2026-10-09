#!/usr/bin/env bash
# Keyboard menu for build.sh. Sourced when interactive mode is selected.

menu_dialog() {
  NEWT_COLORS='
root=green,black
roottext=green,black
window=green,black
border=green,black
shadow=black,black
title=green,black
label=green,black
textbox=green,black
acttextbox=green,black
entry=green,black
disentry=green,black
listbox=green,black
actlistbox=black,green
sellistbox=green,black
actsellistbox=black,green
button=green,black
actbutton=black,green
compactbutton=green,black
actcompactbutton=black,green
checkbox=green,black
actcheckbox=black,green
helpline=green,black
emptyscale=green,black
fullscale=black,green
' whiptail --title 'KILT' --backtitle 'KILT | Builds, checked examples and logs' "$@"
}

menu_targets() {
  local selection
  selection=$(menu_dialog --menu 'Choose what to build:' 18 76 6 \
    default 'KILT and all examples' \
    KILT 'Library only' \
    Examples 'All checked examples' \
    Examples.Syntax 'LTL syntax checks' \
    Examples.Words 'LTL word-semantics checks' \
    Examples.Integration 'CSLib compatibility checks' \
    3>&1 1>&2 2>&3) || return 0
  gui_targets=()
  if [[ "$selection" != default ]]; then gui_targets=("$selection"); fi
}

menu_clean() {
  local selection description
  selection=$(menu_dialog --menu 'Choose what to remove:' 14 76 3 \
    clean 'KILT build outputs; keep logs' \
    logs 'Generated build logs only' \
    all 'KILT build outputs and generated logs' \
    3>&1 1>&2 2>&3) || return 0
  case "$selection" in
    clean) selection=--clean; description='Remove KILT build outputs?' ;;
    logs) selection=--clean-logs; description='Remove generated build logs?' ;;
    all) selection=--clean-all; description='Remove KILT build outputs and generated build logs?' ;;
    *) return 0 ;;
  esac
  if menu_dialog --defaultno --yesno \
      "$description Downloaded dependencies and their compiled caches are kept." 10 76; then
    menu_run "$selection"
  fi
}

menu_run() {
  local status=0
  local flags=()
  if [[ "$gui_verbose" == true ]]; then flags+=(--verbose); fi
  clear
  if GUI_LAUNCH=false "$gui_script" "${flags[@]}" "$@"; then
    printf '\nCommand completed successfully.\n'
  else
    status=$?
    printf '\nCommand failed (exit status %s).\n' "$status"
  fi
  read -r -p 'Press Enter to return to the menu...' _ || return 1
}

menu_logs() {
  if [[ -f "$log_dir/latest.log" ]]; then
    menu_dialog --scrolltext --textbox "$log_dir/latest.log" 22 80 || true
  else
    menu_dialog --msgbox 'No build log yet. Run a build first.' 8 64 || true
  fi
}

build_menu() {
  local gui_script=$1 gui_verbose=$2
  shift 2
  local gui_targets=("$@")
  local selection scope

  if [[ ! -t 0 || ! -t 1 || "${TERM:-dumb}" == dumb ]]; then
    printf 'The --gui menu needs an interactive terminal.\n' >&2
    return 1
  fi
  if ! command -v whiptail >/dev/null 2>&1; then
    printf 'Install whiptail for --gui (Ubuntu: sudo apt install whiptail).\n' >&2
    return 1
  fi

  while true; do
    scope='KILT + Examples'
    if ((${#gui_targets[@]})); then scope="${gui_targets[*]}"; fi
    selection=$(menu_dialog --menu \
      "Targets: $scope | Verbose: $gui_verbose
Use arrow keys, Tab and Enter. Esc or Cancel exits." 20 80 8 \
      build 'Build selected targets with logging' \
      rebuild 'Clean KILT outputs, then build selected targets' \
      targets 'Choose library or example targets' \
      clean 'Clean outputs or generated logs' \
      logs 'View the latest build log' \
      verbose 'Toggle verbose build output' \
      help 'Show options and keyboard help' \
      quit 'Exit' \
      3>&1 1>&2 2>&3) || break
    case "$selection" in
      build) menu_run "${gui_targets[@]}" || break ;;
      rebuild) menu_run --rebuild "${gui_targets[@]}" || break ;;
      targets) menu_targets ;;
      clean) menu_clean || break ;;
      logs) menu_logs ;;
      verbose)
        if [[ "$gui_verbose" == true ]]; then gui_verbose=false; else gui_verbose=true; fi
        ;;
      help)
        menu_dialog --scrolltext --msgbox "$(usage)

Keyboard: Up/Down selects, Tab switches buttons, Enter confirms, Esc cancels.
The log viewer also supports Page Up and Page Down." 23 80 || true
        ;;
      quit) break ;;
    esac
  done
}
