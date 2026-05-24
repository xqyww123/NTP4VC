#!/usr/bin/env python3
"""
Post-fix script: rename all Isabelle session names under data/why3/
to be globally unique by using the full directory path as the session name.

Rule: take the path from data/why3/ (exclusive) to the directory containing ROOT,
      replace '/' with '_'.

Example:
  data/why3/frama_c/standard_algorithms/push_heap/lib/isabelle/ROOT
  → session name: frama_c_standard_algorithms_push_heap_lib_isabelle
"""

import os
import re
import sys
from collections import defaultdict

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_WHY3 = os.path.join(BASE, 'data', 'why3')

SESSION_RE = re.compile(r'^session\s+"?([^"=\s]+)"?\s*=')


def find_all_roots(*dirs):
    roots = []
    for d in dirs:
        for dirpath, _, filenames in os.walk(d):
            if 'ROOT' in filenames:
                roots.append(os.path.join(dirpath, 'ROOT'))
    return sorted(roots)


def read_session_name(root_path):
    with open(root_path, 'r') as f:
        for line in f:
            m = SESSION_RE.match(line.strip())
            if m:
                return m.group(1)
    return None


STRIP_SUFFIXES = ['_Why3_ide_vcg_isabelle', '_vcg_isabelle', '_isabelle']

def compute_new_name(root_path):
    """Path from data/why3/ to ROOT's directory, '/' → '_', strip known suffixes."""
    root_dir = os.path.dirname(root_path)
    rel = os.path.relpath(root_dir, DATA_WHY3)
    name = rel.replace(os.sep, '_')
    for suffix in STRIP_SUFFIXES:
        if name.endswith(suffix):
            name = name[:-len(suffix)]
            break
    return name


def rewrite_root(root_path, old_name, new_name, dry_run=False):
    with open(root_path, 'r') as f:
        content = f.read()

    pattern = re.compile(
        r'^(session\s+)"?' + re.escape(old_name) + r'"?(\s*=)',
        re.MULTILINE
    )
    new_content = pattern.sub(r'\g<1>"' + new_name + r'"\2', content)

    if new_content == content:
        print(f"  WARNING: no substitution for '{old_name}' in {root_path}", file=sys.stderr)
        return False

    if not dry_run:
        with open(root_path, 'w') as f:
            f.write(new_content)
    return True


def main():
    dry_run = '--dry-run' in sys.argv

    categories = [os.path.join(DATA_WHY3, c) for c in ['frama_c', 'pearl']]
    roots = find_all_roots(*categories)

    print(f"Found {len(roots)} ROOT files\n")

    renames = []
    new_name_map = defaultdict(list)

    for root_path in roots:
        old_name = read_session_name(root_path)
        if old_name is None:
            continue
        new_name = compute_new_name(root_path)
        new_name_map[new_name].append(root_path)
        if old_name != new_name:
            renames.append((root_path, old_name, new_name))

    # Check collisions
    collisions = {k: v for k, v in new_name_map.items() if len(v) > 1}
    if collisions:
        print(f"!!! {len(collisions)} COLLISIONS !!!")
        for name, paths in sorted(collisions.items()):
            print(f"  {name}:")
            for p in paths:
                print(f"    {os.path.relpath(p, BASE)}")
        return 1

    print(f"Renames needed: {len(renames)}")
    if dry_run:
        print("(dry run)\n")

    for root_path, old_name, new_name in renames:
        rel = os.path.relpath(root_path, BASE)
        print(f"  {old_name} -> {new_name}")
        print(f"    {rel}")

    if not renames:
        print("Nothing to do.")
        return 0

    if dry_run:
        return 0

    print(f"\nApplying {len(renames)} renames...")
    ok = fail = 0
    for root_path, old_name, new_name in renames:
        if rewrite_root(root_path, old_name, new_name):
            ok += 1
        else:
            fail += 1

    print(f"Done: {ok} succeeded, {fail} failed")
    return 0 if fail == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
