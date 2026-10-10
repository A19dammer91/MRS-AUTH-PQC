#!/usr/bin/env python3
"""Swap X > Y to Y < X and X >= Y to Y <= X in EasyCrypt files."""

import sys
from pathlib import Path

SUFFIX_MARKERS = [' by ', ' => ', ' ==>']


def swap_comparison(line):
    stripped = line.lstrip()

    if stripped.startswith('(*') or stripped.startswith('//') or stripped.startswith('*'):
        return line, False

    if stripped.startswith('type ') or stripped.startswith('op '):
        return line, False

    for op, new_op in [(' >= ', ' <= '), (' > ', ' < ')]:
        if op not in line:
            continue

        idx = line.rfind(op)
        left_part = line[:idx].rstrip()
        right_part = line[idx + len(op):].lstrip()

        colon_idx = left_part.rfind(':')
        if colon_idx != -1:
            prefix = left_part[:colon_idx + 1]
            lhs = left_part[colon_idx + 1:].strip()
        else:
            prefix = ''
            lhs = left_part.strip()

        suffix = ''
        for marker in SUFFIX_MARKERS:
            m_idx = right_part.find(marker)
            if m_idx != -1:
                suffix = right_part[m_idx:]
                right_part = right_part[:m_idx].rstrip()
                break
        rhs = right_part.strip()

        if not lhs or not rhs:
            return line, False

        if prefix:
            new_line = f'{prefix} {rhs} {new_op.strip()} {lhs}{suffix}'
        else:
            new_line = f'{rhs} {new_op.strip()} {lhs}{suffix}'
        return new_line, True

    return line, False


def process_file(path):
    original = path.read_text()
    lines = original.split('\n')
    new_lines = []
    changes = 0
    for line in lines:
        new_line, changed = swap_comparison(line)
        if changed:
            changes += 1
        new_lines.append(new_line)
    if changes > 0:
        path.write_text('\n'.join(new_lines))
    return changes


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    total = 0
    for arg in sys.argv[1:]:
        path = Path(arg)
        if not path.exists():
            print(f'Missing: {path}')
            continue
        n = process_file(path)
        print(f'{path}: {n} lines modified')
        total += n
    print(f'Total: {total} lines modified')


if __name__ == '__main__':
    main()
