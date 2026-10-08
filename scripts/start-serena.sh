#!/usr/bin/env bash
set -euo pipefail

# Let each project's lean-toolchain select Lean, even when launched from `lake env`.
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_SRC_PATH
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  cat <<'EOF'
Usage: scripts/start-serena.sh [SERENA_MCP_OPTIONS...]
       scripts/start-serena.sh --no-project [SERENA_MCP_OPTIONS...]
       scripts/start-serena.sh project-server [PROJECT_SERVER_OPTIONS...]

Starts the MCP server in KILT with cross-project queries enabled.
Use --project references/cslib or --project references/LeanLTL to start elsewhere.
Run project-server in a separate terminal to enable queries of inactive projects.
Use --no-project to defer project activation and language servers until needed.
EOF
  exit 0
fi

if [[ "${1:-}" == "--no-project" ]]; then
  shift
  exec serena start-mcp-server --add-mode query-projects "$@"
fi

cd -- "$project_root"
if [[ "${1:-}" == "project-server" ]]; then
  shift
  exec serena start-project-server "$@"
fi

exec serena start-mcp-server --project "$project_root" --add-mode query-projects "$@"
