#!/usr/bin/env python3
"""Ask the declaration table questions.

    query.py users DECL...            files whose declarations mention DECL (or anything under it)
    query.py needs MODULE             what a file imports against what its declarations use
    query.py cut MODULE IMPORT        remove one import line: who loses something they use
    query.py move NEWMODULE DECL...   move declarations to a new file importing their old one

The table is parsed once and cached beside it. Files with no row in the table are unmeasured: the
answers say how many of those sit above a cut, since only a build can check them.
"""
import collections, functools, os, pickle, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TABLE = os.environ.get('TENDRILS_TABLE', os.path.join(ROOT, '.lake/build/declaration-dependencies/table.tsv'))
IMPORT = re.compile(r'^(?:public )?(?:meta )?import (?:all )?((?:Linglib|Studies)\.\S+)')
sys.setrecursionlimit(30000)
short = lambda m: m.replace('Linglib.', '')

def load():
    cache = TABLE + '.idx'
    if os.path.exists(cache) and os.path.getmtime(cache) > os.path.getmtime(TABLE):
        return pickle.load(open(cache, 'rb'))
    names, mods, deps = [], [], []
    for line in open(TABLE, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        names.append(f[0]); mods.append(f[1])
        deps.append(tuple({int(x) for x in (f[4] + ',' + f[5]).split(',') if x}))
    rdeps = collections.defaultdict(list)
    for i, ds in enumerate(deps):
        for d in ds: rdeps[d].append(i)
    by_name = collections.defaultdict(list)
    for i, n in enumerate(names): by_name[n].append(i)
    by_mod = collections.defaultdict(list)
    for i, m in enumerate(mods): by_mod[m].append(i)
    idx = dict(names=names, mods=mods, deps=deps, rdeps=dict(rdeps), by_name=dict(by_name), by_mod=dict(by_mod))
    pickle.dump(idx, open(cache, 'wb'))
    return idx

def imports():
    G = {}
    for top in ('Linglib', 'Studies'):
        for dp, _, fs in os.walk(os.path.join(ROOT, top)):
            for f in fs:
                if f.endswith('.lean'):
                    p = os.path.join(dp, f)
                    m = os.path.relpath(p, ROOT)[:-5].replace('/', '.')
                    with open(p, encoding='utf-8') as fh:
                        G[m] = [x.group(1) for x in map(IMPORT.match, fh) if x]
    return G

def closure(G):
    @functools.lru_cache(None)
    def c(m):
        s = set()
        for i in G.get(m, []): s.add(i); s |= c(i)
        return frozenset(s)
    return c

T = load()

def ids_of(decl):
    """A declaration with everything generated under its name."""
    return [i for n, ids in T['by_name'].items() if n == decl or n.startswith(decl + '.') for i in ids]

@functools.lru_cache(None)
def need(m):
    """The files the declarations of `m` use, proofs included."""
    seen, work = set(), list(T['by_mod'].get(m, []))
    seen.update(work)
    while work:
        for d in T['deps'][work.pop()]:
            if d not in seen: seen.add(d); work.append(d)
    return frozenset(T['mods'][i] for i in seen) - {m}

def users(decls):
    out = collections.Counter()
    for d in decls:
        own = set(ids_of(d))
        if not own: print('not in the table:', d); continue
        home = T['mods'][next(iter(own))]
        for i in own:
            for u in T['rdeps'].get(i, []):
                if u not in own and T['mods'][u] != home: out[T['mods'][u]] += 1
    return out

def simulate(G2, G, label):
    c0, c1 = closure(G), closure(G2)
    lost, unmeasured = {}, []
    for m in G:
        gone = c0(m) - c1(m)
        if not gone: continue
        if m not in T['by_mod']: unmeasured.append(m); continue
        miss = need(m) & gone
        if miss: lost[m] = miss
    a, b = sum(len(c0(m)) for m in G), sum(len(c1(m)) for m in G)
    print(f'{label}: summed import closure {a} -> {b}')
    print(f'{len(lost)} measured files lose a file they use:')
    for m in sorted(lost):
        tops = [x for x in lost[m] if not any(x in c0(y) for y in lost[m] if y != x)]
        print('   ', short(m), '+ import', ', '.join(short(x) for x in sorted(tops)))
    print(f'{len(unmeasured)} unmeasured files sit above the cut; a build has to check them')
    return lost, unmeasured

def main(argv):
    cmd, args = argv[0], argv[1:]
    if cmd == 'users':
        u = users(args)
        for m, n in sorted(u.items()): print(f'{n:4d}  {short(m)}')
        print(len(u), 'files')
    elif cmd == 'needs':
        m = args[0] if args[0].startswith(('Linglib.', 'Studies.')) else 'Linglib.' + args[0]
        G = imports(); c = closure(G); nd = need(m)
        print(f'{short(m)}: imports {len(c(m))} files, uses {len(nd & c(m))}')
        for i in G[m]:
            got = ({i} | c(i)) & nd
            print(f'   {short(i):58} uses {len(got):3d} of {len(c(i)) + 1}')
    elif cmd == 'cut':
        m, i = (a if a.startswith(('Linglib.', 'Studies.')) else 'Linglib.' + a for a in args[:2])
        G = imports(); G2 = dict(G); G2[m] = [x for x in G[m] if x != i]
        only = ({i} | closure(G)(i)) - closure(G2)(m)
        need_it = [T['names'][k] for k in T['by_mod'].get(m, []) if '._' not in T['names'][k] and
                   any(T['mods'][d] in only for d in T['deps'][k])]
        print(f'{len(only)} files reach {short(m)} only through {short(i)}; its declarations that use them:')
        for n in sorted(need_it)[:20]: print('   ', n)
        simulate(G2, G, 'cut')
    elif cmd == 'move':
        new, decls = args[0], args[1:]
        new = new if new.startswith(('Linglib.', 'Studies.')) else 'Linglib.' + new
        G = imports(); G2 = {k: list(v) for k, v in G.items()}
        home = T['mods'][ids_of(decls[0])[0]]
        G2[new] = [home] + G[home]
        u = users(decls)
        print(f'{len(u)} files use the moved declarations and import {short(new)}:')
        for m in sorted(u):
            print('   ', short(m)); G2[m] = G2.get(m, []) + [new]
    else:
        print(__doc__)

if __name__ == '__main__':
    main(sys.argv[1:] or ['help'])
