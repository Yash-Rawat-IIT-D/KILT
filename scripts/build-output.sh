#!/usr/bin/env bash
# Terminal formatting shared by the build script and its menu.

build_color_enabled=false
if [[ -t 1 && "${TERM:-dumb}" != dumb && -z "${NO_COLOR:-}" ]]; then
  build_color_enabled=true
fi

print_build_line() {
  local line=$1 color=
  local duration_pattern='^(.*)(\([0-9]+([.][0-9]+)?(ms|s|m|h)([[:space:]][0-9]+([.][0-9]+)?(ms|s|m|h))*\))$'

  if [[ "$build_color_enabled" != true ]]; then
    printf '%s\n' "$line"
    return
  fi

  case "$line" in
    ✖*|error:*|fatal:*|Command\ failed*|Failed\ to\ capture*|Build\ exit\ status:\ [1-9]*)
      color=31 ;;
    ⚠*|warning:*|Started:*|Finished:*|Elapsed:*|Total\ time:*)
      color=33 ;;
    ✔*|*' Built '*|Build\ completed\ successfully*|Build\ exit\ status:\ 0|\
    Command\ completed\ successfully*|Cleaned*|Removed\ script\ build\ logs*)
      color=32 ;;
  esac

  if [[ "$color" == 32 && "$line" =~ $duration_pattern ]]; then
    printf '\033[32m%s\033[33m%s\033[0m\n' "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}"
  elif [[ -n "$color" ]]; then
    printf '\033[%sm%s\033[0m\n' "$color" "$line"
  else
    printf '%s\n' "$line"
  fi
}

display_build_output() {
  local line
  while IFS= read -r line || [[ -n "$line" ]]; do
    print_build_line "$line"
  done
}
