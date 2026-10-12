# Sourced by the host launchers. Credentials are passed by name, never by value.
AGENT_BACKEND="${AGENT_BACKEND:-cursor}"
case "$AGENT_BACKEND" in
  cursor)
    AGENT_KEY_ENV=CURSOR_API_KEY
    AGENT_HOME_MOUNT=/root/.cursor
    AGENT_MODEL="${AGENT_MODEL:-gpt-5.6-sol-high}"
    # Cursor's API hosts are not documented; add hosts with EGRESS_ALLOW_EXTRA if the
    # proxy log (audit-logs/<id>/tinyproxy.log) shows a refused Cursor host.
    EGRESS_ALLOW_DEFAULT='(^|\.)cursor\.sh$ ^(api\.)?cursor\.com$'
    ;;
  codex)
    AGENT_KEY_ENV=CODEX_API_KEY
    AGENT_HOME_MOUNT=/root/.codex
    AGENT_MODEL="${AGENT_MODEL:-gpt-6.1-sol}"
    # API key (api.openai.com) and ChatGPT sign-in (chatgpt.com, auth.openai.com).
    EGRESS_ALLOW_DEFAULT='^api\.openai\.com$ ^chatgpt\.com$ ^auth\.openai\.com$'
    ;;
  *)
    echo "Unknown AGENT_BACKEND: $AGENT_BACKEND (expected cursor or codex)" >&2
    exit 2
    ;;
esac
# Space-separated extended regexes (matched on the host name) for the hosts
# agent containers may reach through the egress proxy.
EGRESS_ALLOW="$EGRESS_ALLOW_DEFAULT ${EGRESS_ALLOW_EXTRA:-}"
AGENT_REASONING_EFFORT="${AGENT_REASONING_EFFORT:-high}"
MONITOR_REASONING_EFFORT="${MONITOR_REASONING_EFFORT:-$AGENT_REASONING_EFFORT}"
if [[ "$AGENT_BACKEND" == codex ]]; then
  for effort in "$AGENT_REASONING_EFFORT" "$MONITOR_REASONING_EFFORT"; do
    case "$effort" in
      none|minimal|low|medium|high|xhigh|max) ;;
      *) echo "Invalid Codex reasoning effort: $effort" >&2; exit 2 ;;
    esac
  done
fi
