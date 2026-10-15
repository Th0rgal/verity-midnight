#!/usr/bin/env python3
"""Validate/copy a Claude subscription login without displaying credentials."""
import json
from pathlib import Path
import sys


def main():
    try:
        auth_bytes = Path(sys.argv[1]).read_bytes()
        auth = json.loads(auth_bytes)
    except (OSError, ValueError):
        sys.exit('Cannot read Claude login cache. Run bash scripts/claude-login.sh first, '
                 'or set CLAUDE_AUTH_FILE.')
    oauth = auth.get('claudeAiOauth') if isinstance(auth, dict) else None
    if not isinstance(oauth, dict) or not oauth.get('accessToken') or not oauth.get('refreshToken'):
        sys.exit('Not a refreshable Claude subscription login. Run bash scripts/claude-login.sh.')
    for destination in sys.argv[2:]:
        directory = Path(destination)
        directory.mkdir(parents=True, exist_ok=True)
        target = directory / '.credentials.json'
        with target.open('wb') as output:
            target.chmod(0o600)
            output.write(auth_bytes)
    print('Claude login cache validated' if len(sys.argv) == 2
          else 'Claude login installed in isolated agent homes')


if __name__ == '__main__':
    main()
