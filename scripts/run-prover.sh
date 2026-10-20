#!/bin/bash
# Runs inside the isolated Docker container. Docker supplies the sandbox.
set -euo pipefail

PROMPT="Prove the theorem requested in README.md. Follow README.md and AGENTS.md. lean-lsp MCP is required — if it is unavailable, write out/mcp-unavailable with a reason and stop immediately (do not continue shell-only). Use lean_diagnostic_messages, lean_goal, lean_hover_info, lean_local_search. Stop when ./check/check_proof.sh exits 0."

if [[ "${TURBO_LEAN:-0}" == "1" || "${TURBO_LEAN:-0}" == "force" ]]; then
  export PATH="/opt/turbo-lean/bin:$PATH"
fi

if [[ "${TURBO_LEAN:-0}" == "1" ]]; then
  PROMPT="$PROMPT turbo-lean is installed for fast Lean checks: to check edits, run \`turbo-lean check <File.lean> --decl <name> --project-dir .\` (one declaration) or \`turbo-lean check <File.lean> --project-dir .\` (whole file) instead of \`lake build\` or \`lake env lean\`. Run \`lake build <Module>\` only when a module that other files import has changed. lean-lsp MCP is still required for goals, diagnostics and search, and ./check/check_proof.sh is still the final judge."
elif [[ "${TURBO_LEAN:-0}" == "force" ]]; then
  PROMPT="$PROMPT In this trial \`lake build\` and \`lake env lean\` are blocked for you. To check edits, run \`turbo-lean check <File.lean> --decl <name> --project-dir .\` (one declaration) or \`turbo-lean check <File.lean> --project-dir .\` (whole file). After changing a module that other files import, run \`turbo-lean build --project-dir .\` before checking files that import it. lean-lsp MCP is still required for goals, diagnostics and search, and ./check/check_proof.sh (allowed) is still the final judge."
fi

case "${AGENT_BACKEND:-cursor}" in
  cursor)
    exec agent -p --force --trust --approve-mcps --sandbox disabled \
      --model "${AGENT_MODEL:?}" --workspace /work "$PROMPT"
    ;;
  codex)
    codex exec --cd /work --skip-git-repo-check \
      --dangerously-bypass-approvals-and-sandbox \
      --model "${AGENT_MODEL:?}" \
      -c "model_reasoning_effort=\"${AGENT_REASONING_EFFORT:-high}\"" \
      --json "$PROMPT" | tee /root/.codex/prover-events.jsonl
    ;;
  claude)
    source /opt/midnight/claude-common.sh
    run_claude --model "${AGENT_MODEL:?}" \
      --effort "${AGENT_REASONING_EFFORT:-high}" \
      --mcp-config /opt/midnight/claude-prover.json \
      --verbose --output-format stream-json "$PROMPT" \
      | tee /root/.claude/prover-events.jsonl
    ;;
  *) echo "Unknown AGENT_BACKEND: $AGENT_BACKEND" >&2; exit 2 ;;
esac
