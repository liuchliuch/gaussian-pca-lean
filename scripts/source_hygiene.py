#!/usr/bin/env python3
"""Conservative lexical screen; no substitute for elaboration or axiom auditing."""
import argparse
import hashlib
import json
from pathlib import Path
import re

CHALLENGE = 'StatementContracts/Challenge.lean'


def code_only(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if char == '\n' else ' '); i += 1
        elif string:
            if char == '\\': out.extend('  '); i += 2
            else:
                if char == '"': string = False
                out.append('\n' if char == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: break
            out.extend(' ' * (end - i)); i = end
        elif char == '"': string = True; out.append(' '); i += 1
        else: out.append(char); i += 1
    return ''.join(out)


def inspect(root):
    files = sorted(p for p in root.rglob('*.lean')
                   if not any(n in {'.lake', '.toolchain', '.cache', '.git'} for n in p.relative_to(root).parts))
    inventory, findings = [], []
    for path in files:
        rel, data = path.relative_to(root).as_posix(), path.read_bytes()
        inventory.append({'path': rel, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
        if rel == CHALLENGE:
            continue
        code = code_only(data.decode())
        for match in re.finditer(r'\b(sorry|admit|axiom|sorryAx|unsafe)\b', code):
            findings.append({'path': rel, 'token': match[0], 'line': code.count('\n', 0, match.start()) + 1})
        if re.search(r'^\s*import\s+StatementContracts\.Challenge\b', code, re.M):
            findings.append({'path': rel, 'token': 'forbidden Challenge import'})
    return {'scope': 'Owned source lexical hygiene only', 'files': inventory, 'findings': findings,
            'exclusion': CHALLENGE + ': isolated untrusted statement placeholders only', 'pass': not findings}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = inspect(args.root)
    text = json.dumps(result, indent=2) + '\n'
    if args.output: args.output.write_text(text)
    else: print(text, end='')
    raise SystemExit(not result['pass'])
