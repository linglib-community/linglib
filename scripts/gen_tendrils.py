#!/usr/bin/env python3
"""Build the dependency map of the library: which declarations each study theorem's statement rests on.

    python3 scripts/gen_tendrils.py [--out DIR] [--lib DIR] [--modules FILE]

Run it after `lake build`. It reads the compiled modules under `.lake/build/lib/lean` (or `--lib`), so a
module that is not compiled, or whose imports are not, is left out and listed as unmeasured. `--modules`
restricts the run to the modules a file lists. The page and its data land in `--out`
(default `.lake/build/tendrils`): `index.html` and `graph.json`.
"""
import argparse, functools, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r'^(?:public )?(?:meta )?import (?:all )?((?:Linglib|Studies)\.\S+)')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default=os.path.join(ROOT, '.lake/build/tendrils'))
    ap.add_argument('--lib', default=os.path.join(ROOT, '.lake/build/lib/lean'))
    ap.add_argument('--modules')
    args = ap.parse_args()
    os.chdir(ROOT)
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
    env = lambda *a: subprocess.run(['lake', 'env', *a], capture_output=True, text=True, check=True).stdout.strip()
    lean_path = env('printenv', 'LEAN_PATH').replace(os.path.join(ROOT, '.lake/build/lib/lean'), os.path.abspath(args.lib))
    lean = env('which', 'lean')
    with tempfile.TemporaryDirectory() as tmp:
        mods, missing, table = (os.path.join(tmp, n) for n in ('mods.txt', 'missing.txt', 'table.tsv'))
        open(mods, 'w').write('\n'.join(keep) + '\n')
        open(missing, 'w').write('\n'.join(miss) + ('\n' if miss else ''))
        subprocess.run([lean, '--run', 'scripts/tendrils/Extract.lean', mods, table], check=True,
                       env={**os.environ, 'LEAN_PATH': lean_path})
        subprocess.run([sys.executable, 'scripts/tendrils/analyze.py', table, mods, missing, args.out], check=True)
    with open('scripts/tendrils/page.html', encoding='utf-8') as src, \
            open(os.path.join(args.out, 'index.html'), 'w', encoding='utf-8') as dst:
        dst.write(src.read())
    print(f'{len(keep)} modules measured, {len(miss)} unmeasured; wrote {args.out}')


if __name__ == '__main__':
    main()
