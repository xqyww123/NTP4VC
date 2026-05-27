#!/usr/bin/env python3
"""
Post-fix script for Isabelle sessions under data/why3/.

Commands:
  rename    — Rename all session names to globally unique path-based names
  fix-roots — Add lib/isabelle entries to ROOTS files
  fix-imports — Convert ../../lib/isabelle/ relative imports to qualified names
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


def cmd_rename(dry_run=False):
    """Rename all session names to globally unique path-based names."""
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


def cmd_fix_roots(dry_run=False):
    """Add lib/isabelle session entries to ROOTS files."""
    for category in ['frama_c', 'pearl']:
        roots_file = os.path.join(DATA_WHY3, category, 'ROOTS')
        cat_dir = os.path.join(DATA_WHY3, category)

        with open(roots_file) as f:
            existing = set(line.strip() for line in f if line.strip())

        all_roots = find_all_roots(cat_dir)
        lib_entries = []
        for root_path in all_roots:
            root_dir = os.path.dirname(root_path)
            rel = os.path.relpath(root_dir, cat_dir)
            if '/lib/isabelle' in rel or rel.endswith('lib/isabelle'):
                if rel not in existing:
                    lib_entries.append(rel)

        if not lib_entries:
            print(f"  {category}/ROOTS: nothing to add")
            continue

        lib_entries.sort()
        print(f"  {category}/ROOTS: adding {len(lib_entries)} lib entries:")
        for e in lib_entries:
            print(f"    {e}")

        if not dry_run:
            with open(roots_file, 'a') as f:
                for entry in lib_entries:
                    f.write(entry + '\n')

    return 0


IMPORT_RE = re.compile(r'"../../lib/isabelle/([^"]+)"')


def build_lib_session_map():
    """Build map: absolute lib dir path -> session name."""
    lib_map = {}
    for category in ['frama_c', 'pearl']:
        cat_dir = os.path.join(DATA_WHY3, category)
        for root_path in find_all_roots(cat_dir):
            root_dir = os.path.dirname(root_path)
            if root_dir.endswith('/lib/isabelle'):
                lib_map[root_dir] = compute_new_name(root_path)
    return lib_map


def cmd_fix_imports(dry_run=False):
    """Convert ../../lib/isabelle/X imports to session-qualified names."""
    lib_map = build_lib_session_map()
    print(f"Found {len(lib_map)} lib sessions\n")

    thy_fixed = 0
    root_fixed = 0
    warnings = []

    for category in ['frama_c', 'pearl']:
        cat_dir = os.path.join(DATA_WHY3, category)

        # Pass 1: fix .thy imports and collect VCG ROOT -> lib session deps
        root_deps = defaultdict(set)  # VCG ROOT path -> set of lib session names

        for dirpath, _, filenames in os.walk(cat_dir):
            for fn in filenames:
                if not fn.endswith('.thy'):
                    continue
                thy_path = os.path.join(dirpath, fn)
                with open(thy_path) as f:
                    content = f.read()
                if '../../lib/isabelle/' not in content:
                    continue

                thy_dir = os.path.dirname(thy_path)
                lib_dir = os.path.normpath(os.path.join(thy_dir, '../../lib/isabelle'))

                if lib_dir not in lib_map:
                    warnings.append(f"no lib session for {os.path.relpath(thy_path, BASE)}")
                    continue

                session_name = lib_map[lib_dir]
                is_self = os.path.normpath(thy_dir) == os.path.normpath(lib_dir)

                def replace_import(m):
                    if is_self:
                        return f'"{m.group(1)}"'
                    return f'"{session_name}.{m.group(1)}"'

                new_content = IMPORT_RE.sub(replace_import, content)
                if new_content != content:
                    if not dry_run:
                        with open(thy_path, 'w') as f:
                            f.write(new_content)
                    thy_fixed += 1

                    if not is_self:
                        vcg_root = os.path.join(thy_dir, 'ROOT')
                        if os.path.exists(vcg_root):
                            root_deps[vcg_root].add(session_name)

        # Pass 2: add sessions clauses to VCG ROOT files
        for vcg_root, dep_sessions in sorted(root_deps.items()):
            with open(vcg_root) as f:
                root_content = f.read()

            # Skip if already has sessions clause with all deps
            existing_sessions = set(re.findall(r'"([^"]+)"',
                (re.search(r'^sessions\n((?:\s+"[^"]+"\n)*)', root_content, re.MULTILINE) or
                 type('', (), {'group': lambda self, x: ''})()).group(1)))

            missing = dep_sessions - existing_sessions
            if not missing:
                continue

            sessions_block = 'sessions\n' + ''.join(f'  "{s}"\n' for s in sorted(dep_sessions))

            if 'sessions\n' in root_content:
                # Replace existing sessions block
                root_content = re.sub(
                    r'^sessions\n(?:\s+"[^"]+"\n)*',
                    sessions_block,
                    root_content,
                    count=1,
                    flags=re.MULTILINE
                )
            else:
                # Insert before "theories"
                root_content = root_content.replace(
                    'theories\n',
                    sessions_block + 'theories\n',
                    1
                )

            if not dry_run:
                with open(vcg_root, 'w') as f:
                    f.write(root_content)
            root_fixed += 1
            print(f"  ROOT: {os.path.relpath(vcg_root, BASE)} += sessions {sorted(dep_sessions)}")

    print(f"\nFixed {thy_fixed} .thy files, {root_fixed} ROOT files")
    for w in warnings:
        print(f"  WARNING: {w}", file=sys.stderr)

    return 0


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    dry_run = '--dry-run' in sys.argv

    cmd = args[0] if args else 'rename'

    if cmd == 'rename':
        return cmd_rename(dry_run)
    elif cmd == 'fix-roots':
        return cmd_fix_roots(dry_run)
    elif cmd == 'fix-imports':
        return cmd_fix_imports(dry_run)
    else:
        print(f"Unknown command: {cmd}")
        print("Commands: rename, fix-roots, fix-imports")
        return 1


if __name__ == '__main__':
    sys.exit(main())
