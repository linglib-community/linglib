#!/usr/bin/env python3
"""Build the dependency map of the library: which declarations each study theorem's statement rests on.

    python3 scripts/gen_tendrils.py [--out DIR] [--lib DIR] [--modules FILE]
    python3 scripts/gen_tendrils.py --extract-only DIR
    python3 scripts/gen_tendrils.py --from-table DIR [--out DIR]

Run it after `lake build`. It reads the compiled modules under `.lake/build/lib/lean` (or `--lib`), so a
module that is not compiled, or whose imports are not, is left out and listed as unmeasured. `--modules`
restricts the run to the modules a file lists. The page and its data land in `--out`
(default `.lake/build/tendrils`): `index.html` and `graph.json`.

`--extract-only` stops after writing the declaration table to a directory, which the nightly build
uploads; `--from-table` builds the page from such a directory without a compiled library.
"""
import argparse, collections, datetime, functools, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r'^(?:public )?(?:meta )?import (?:all )?((?:Linglib|Studies)\.\S+)')


CONFLICT = re.compile(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)")


def extract(args, table_dir):
    """Write `mods.txt`, `missing.txt`, `table.tsv` and `source.txt` to `table_dir`."""
    imports = {}
    for top in ('Linglib', 'Studies'):
        for dp, _, fs in os.walk(top):
            for f in fs:
                if f.endswith('.lean'):
                    p = os.path.join(dp, f)
                    with open(p, encoding='utf-8') as fh:
                        imports[p[:-5].replace('/', '.')] = [m.group(1) for m in map(IMPORT.match, fh) if m]
    allowed = None
    if args.modules:
        allowed = {l.strip() for l in open(args.modules) if l.strip()}
    sys.setrecursionlimit(20000)

    @functools.lru_cache(None)
    def usable(m):
        return (m in imports and (allowed is None or m in allowed)
                and os.path.exists(os.path.join(args.lib, m.replace('.', '/') + '.olean'))
                and all(usable(i) for i in imports[m]))

    keep = sorted(m for m in imports if usable(m))
    miss = sorted(m for m in imports if not usable(m))
    importers = collections.defaultdict(set)
    for m, deps in imports.items():
        for d in deps: importers[d].add(m)
    env = lambda *a: subprocess.run(['lake', 'env', *a], capture_output=True, text=True, check=True).stdout.strip()
    lean_path = env('printenv', 'LEAN_PATH').replace(os.path.join(ROOT, '.lake/build/lib/lean'), os.path.abspath(args.lib))
    lean = env('which', 'lean')
    os.makedirs(table_dir, exist_ok=True)
    mods, missing, table = (os.path.join(table_dir, n) for n in ('mods.txt', 'missing.txt', 'table.tsv'))
    while True:
        # Two compiled modules that disagree on a generated declaration cannot be loaded together:
        # leave out the later one and its importers, and try again.
        open(mods, 'w').write('\n'.join(keep) + '\n')
        r = subprocess.run([lean, '--run', 'scripts/tendrils/Extract.lean', mods, table], capture_output=True,
                           text=True, env={**os.environ, 'LEAN_PATH': lean_path})
        hit = CONFLICT.search(r.stdout + r.stderr)
        if not hit:
            if r.returncode: sys.exit(r.stdout + r.stderr)
            break
        drop, work = {hit.group(1)}, [hit.group(1)]
        while work:
            for y in importers[work.pop()]:
                if y not in drop: drop.add(y); work.append(y)
        print(f'left out {hit.group(1)} and {len(drop) - 1} importers: it disagrees with {hit.group(3)} on {hit.group(2)}')
        keep = [m for m in keep if m not in drop]; miss = sorted(set(miss) | drop)
    open(missing, 'w').write('\n'.join(miss) + ('\n' if miss else ''))
    commit = subprocess.run(['git', 'rev-parse', '--short=10', 'HEAD'], capture_output=True, text=True).stdout.strip()
    open(os.path.join(table_dir, 'source.txt'), 'w').write(f'{commit}\n{datetime.date.today().isoformat()}\n')
    print(f'{len(keep)} modules measured, {len(miss)} unmeasured')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default=os.path.join(ROOT, '.lake/build/tendrils'))
    ap.add_argument('--lib', default=os.path.join(ROOT, '.lake/build/lib/lean'))
    ap.add_argument('--modules')
    ap.add_argument('--extract-only', metavar='DIR')
    ap.add_argument('--from-table', metavar='DIR')
    args = ap.parse_args()
    for k in ('out', 'lib', 'modules', 'extract_only', 'from_table'):
        if getattr(args, k): setattr(args, k, os.path.abspath(getattr(args, k)))
    os.chdir(ROOT)
    if args.extract_only:
        return extract(args, args.extract_only)
    with tempfile.TemporaryDirectory() as tmp:
        d = args.from_table or tmp
        if not args.from_table: extract(args, d)
        subprocess.run([sys.executable, 'scripts/tendrils/analyze.py', os.path.join(d, 'table.tsv'),
                        os.path.join(d, 'mods.txt'), os.path.join(d, 'missing.txt'), args.out], check=True)
    with open('scripts/tendrils/page.html', encoding='utf-8') as src, \
            open(os.path.join(args.out, 'index.html'), 'w', encoding='utf-8') as dst:
        dst.write(src.read())
    print(f'wrote {args.out}')


if __name__ == '__main__':
    main()
