#!/usr/bin/env bash
# A gloss command for `checks.py gloss` that runs Claude Code's `claude` with the given model:
#
#     python3 scripts/checks.py gloss SOURCE --command "scripts/checks/gloss-claude.sh MODEL"
#
# The model gets no tools, settings, MCP servers or session history, and runs in an empty directory,
# so it sees only the prompt and the text on standard input.
set -euo pipefail
model=${1:?usage: gloss-claude.sh MODEL}
prompt=$(cat "${GLOSS_PROMPT:?GLOSS_PROMPT is not set}")
cd "$(mktemp -d)"
trap 'rmdir "$PWD"' EXIT
claude -p --model "$model" --tools "" --setting-sources "" --strict-mcp-config \
  --no-session-persistence --system-prompt "$prompt"
