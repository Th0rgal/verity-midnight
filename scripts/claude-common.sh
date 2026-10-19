# Sourced inside Docker by both Claude entry points.
export CLAUDE_CONFIG_DIR=/root/.claude
export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
export ENABLE_CLAUDEAI_MCP_SERVERS=false
export DISABLE_AUTOUPDATER=1
export MCP_TIMEOUT=60000

run_claude() {
  # Explicit approvals work as root; bypassPermissions requires a non-root user.
  # Docker and the egress proxy supply isolation. Keep hosted web tools absent.
  # Do not use --bare: it ignores subscription OAuth tokens.
  local allowed_tools='Bash,Read,Write,Edit,Glob,Grep,mcp__lean-lsp__*'
  if [[ "${TURBO_LEAN:-0}" == "1" ]]; then
    allowed_tools="$allowed_tools,Bash(turbo-lean *)"
  fi
  claude -p --permission-mode dontAsk \
    --tools 'Bash,Read,Write,Edit,Glob,Grep' \
    --allowedTools "$allowed_tools" \
    --disallowedTools 'WebSearch,WebFetch' \
    --setting-sources '' --strict-mcp-config "$@"
}
