#!/usr/bin/env python3
import json
import re
import sys


command = json.load(sys.stdin).get('tool_input', {}).get('command', '')
if (
    re.search(r'\blake(\s+-\S+)*\s+(build|env\s+(lean|repl))\b', command)
    or re.search(r'\blake\s+-d\s+\S+\s+(build|env\s+(lean|repl))\b', command)
):
    print(
        'Blocked in this trial: lake build / lake env lean are disabled. '
        'Check edits with turbo-lean check <File.lean> [--decl <name>] --project-dir . ; '
        './check/check_proof.sh is allowed.',
        file=sys.stderr,
    )
    sys.exit(2)
sys.exit(0)
