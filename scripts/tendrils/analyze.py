#!/usr/bin/env python3
"""Turn the extractor's declaration table into the measures the page shows.

Usage: analyze.py <table.tsv> <measured-modules.txt> <unmeasured-modules.txt> <out-dir>

Meaning edges: what a declaration's statement says. A theorem contributes its statement only, a
definition its type and body, an inductive type its constructors. Full edges add proofs.
"""
import os, re, sys, json, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TSV, MODS_FILE, MISSING_FILE, OUT = sys.argv[1:5]
os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------- rows
rows = []
for line in open(TSV, encoding='utf-8'):
    f = line.rstrip('\n').split('\t')
    f += [''] * (11 - len(f))
    ints = lambda s: [int(x) for x in s.split(',') if x]
    rows.append(dict(name=f[0], mod=f[1], kind=f[2], fl=f[3], t=ints(f[4]), v=ints(f[5]),
                     d=ints(f[6]), te=[x for x in f[7].split(',') if x],
                     ve=[x for x in f[8].split(',') if x], nt=int(f[9] or 0), nv=int(f[10] or 0)))
N = len(rows)
mods = sorted({r['mod'] for r in rows})
compiled = [l.strip() for l in open(MODS_FILE) if l.strip()]
mods = sorted(set(mods) | set(compiled))
mid = {m: i for i, m in enumerate(mods)}

def layer(m):
    p = m.split('.')
    if p[0] == 'Studies': return 'study'
    if p[1] == 'Core': return 'core'
    if p[1] in ('Data', 'Languages'): return 'data'
    return 'theory'

def group(m):
    p = m.split('.')
    if p[0] == 'Studies': return 'Studies'
    if len(p) > 3 and p[1] in ('Syntax', 'Semantics', 'Core', 'Morphology', 'Phonology'):
        return p[1] + '/' + p[2]
    return p[1] if len(p) > 2 else p[1]

# ---------------------------------------------------------------- source: written declarations, imports
KW = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|meta|unsafe|partial|'
                r'nonrec|scoped|local)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|'
                r'opaque)\s+([^\s:({\[⦃]+)')
IMP = re.compile(r'^(?:public )?(?:meta )?import (?:all )?((?:Linglib|Studies)\.\S+)')
written = {}   # module -> {token: (kind, hasDoc)}
imports = {}
lines_of = {}
for m in mods:
    p = ROOT + '/' + m.replace('.', '/') + '.lean'
    toks, imps = {}, []
    try:
        src = open(p, encoding='utf-8').read().split('\n')
    except FileNotFoundError:
        src = []
    lines_of[m] = len(src)
    doc_pending = False
    in_doc = False
    for l in src:
        mm = IMP.match(l)
        if mm: imps.append(mm.group(1))
        s = l.strip()
        if in_doc:
            if '-/' in s: in_doc = False; doc_pending = True
            continue
        if s.startswith('/--'):
            if '-/' in s[3:]: doc_pending = True
            else: in_doc = True
            continue
        k = KW.match(l)
        if k:
            if not (k.group(1) == 'instance' and k.group(2) in (':', 'priority')):
                toks[k.group(2)] = (k.group(1), doc_pending)
            doc_pending = False
        elif s and not s.startswith('@[') and not s.startswith('--'):
            doc_pending = False
    written[m] = toks
    imports[m] = [i for i in imps if i in mid]

def suffix_token(name, toks):
    """The longest dotted suffix of `name` that the source declares, and the prefix before it."""
    parts = name.split('.')
    for k in range(len(parts)):          # longest suffix first
        tok = '.'.join(parts[k:])
        if tok in toks: return tok
    return None

# owner: the written declaration a constant belongs to
by_mod = collections.defaultdict(list)
for i, r in enumerate(rows): by_mod[r['mod']].append(i)
owner = list(range(N))
is_written = [False] * N
has_doc = [False] * N
wkind = [None] * N
for m, idxs in by_mod.items():
    toks = written.get(m, {})
    wnames = {}
    for i in idxs:
        r = rows[i]
        if 'i' in r['fl']: continue
        tok = suffix_token(r['name'], toks)
        if tok is not None and r['kind'] in ('thm', 'def', 'ind', 'opaque', 'axiom'):
            is_written[i] = True; wkind[i] = toks[tok][0]; has_doc[i] = toks[tok][1]
            wnames[r['name']] = i
    for i in idxs:
        if is_written[i]: continue
        parts = rows[i]['name'].split('.')
        for k in range(len(parts) - 1, 0, -1):
            j = wnames.get('.'.join(parts[:k]))
            if j is not None: owner[i] = j; break

members = collections.defaultdict(list)
for i in range(N): members[owner[i]].append(i)
nodes = sorted(members)                  # node = owner id
print(f'{N} constants, {len(nodes)} nodes, {sum(is_written)} written', file=sys.stderr)

AREAS = sorted({a for r in rows for a in r['te'] + r['ve']})
aid = {a: i for i, a in enumerate(AREAS)}

mean_e, full_e, dflt_e, mean_a = {}, {}, {}, {}
for x in nodes:
    rx = rows[x]
    me, fe, de, ma = set(), set(), set(), set()
    stmt = set(rx['t'])
    for c in members[x]:
        rc = rows[c]
        fe.update(rc['t']); fe.update(rc['v']); de.update(rc['d'])
        if c == x:
            me.update(rc['t']); ma.update(rc['te'])
            if rc['kind'] != 'thm': me.update(rc['v']); ma.update(rc['ve'])
        elif rc['kind'] != 'thm' and (rx['kind'] != 'thm' or c in stmt):
            me.update(rc['t']); me.update(rc['v']); ma.update(rc['te']); ma.update(rc['ve'])
    mean_e[x] = {owner[y] for y in me} - {x}
    full_e[x] = {owner[y] for y in fe} - {x}
    dflt_e[x] = {owner[y] for y in de} - {x}
    mean_a[x] = ma

# ---------------------------------------------------------------- closures as bitmasks (iterative Tarjan)
def closure_masks(edges, seed):
    index, low, onstack, comp = {}, {}, set(), {}
    stack, out, counter = [], {}, [0]
    for root in nodes:
        if root in index: continue
        work = [(root, iter(edges[root]))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stack.append(root); onstack.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); onstack.add(w)
                    work.append((w, iter(edges[w]))); advanced = True; break
                elif w in onstack:
                    low[v] = min(low[v], index[w])
            if advanced: continue
            work.pop()
            if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                scc = []
                while True:
                    w = stack.pop(); onstack.discard(w); scc.append(w)
                    if w == v: break
                mask = 0
                for w in scc:
                    mask |= seed(w)
                    for u in edges[w]:
                        if u in out: mask |= out[u]
                for w in scc: out[w] = mask
    return out

bit = lambda x: 1 << mid[rows[x]['mod']]
Mm = closure_masks(mean_e, bit)
Mf = closure_masks(full_e, bit)
full_d = {x: full_e[x] | dflt_e[x] for x in nodes}
Mfd = closure_masks(full_d, bit)
Am = closure_masks(mean_e, lambda x: sum(1 << aid[a] for a in mean_a[x]))

LAYER = [layer(m) for m in mods]
lmask = {L: sum(1 << i for i, l in enumerate(LAYER) if l == L) for L in ('core', 'theory', 'data', 'study')}
LEAN_ONLY = sum(1 << aid[a] for a in AREAS if not a.startswith('Mathlib'))
bits = lambda mask: [i for i in range(len(mods)) if mask >> i & 1]

# ---------------------------------------------------------------- modules
import functools
sys.setrecursionlimit(20000)
@functools.lru_cache(None)
def iclo(m):
    s = 0
    for i in imports[m]: s |= (1 << mid[i]) | iclo(i)
    return s

mod_nodes = collections.defaultdict(list)
for x in nodes: mod_nodes[rows[x]['mod']].append(x)
compiled_set = set(compiled)
M = []
for m in mods:
    me = 1 << mid[m]
    xs = mod_nodes.get(m, [])
    needF = 0; needM = 0; needD = 0
    for x in xs:
        needF |= Mf[x]; needD |= Mfd[x]
        if is_written[x]: needM |= Mm[x]
    ic = iclo(m)
    needF &= ~me; needM &= ~me; needD &= ~me
    unused = ic & ~needF
    dead_direct = [i for i in imports[m] if not (((1 << mid[i]) | iclo(i)) & needF)]
    M.append(dict(name=m, layer=layer(m), group=group(m), lines=lines_of[m],
                  compiled=m in compiled_set, nimp=bin(ic).count('1'),
                  nuse=bin(needF & ic).count('1'), nmean=bin(needM & ic).count('1'),
                  ndflt=bin(needD & ~needF).count('1'), dead=[mid[i] for i in dead_direct],
                  imp=[mid[i] for i in imports[m]], need=bits(needF & ic),
                  ndecl=sum(1 for x in xs if is_written[x])))

# ---------------------------------------------------------------- threads worth cutting
# For a file B and a direct import m: X = the files B reaches only through m. If few declarations of B
# need anything in X, moving them out frees every file above B that uses none of them from X.
rev = {x: set() for x in nodes}
for x in nodes:
    for y in full_e[x]: rev[y].add(x)
Ru = closure_masks(rev, bit)             # the modules whose declarations depend on a declaration
importers = [0] * len(mods)
for m in mods:
    ic = iclo(m); i = mid[m]
    for j in bits(ic): importers[j] |= 1 << i
cuts = []
for m in mods:
    if layer(m) == 'study' or m not in mod_nodes: continue
    B = mid[m]; xs = [x for x in mod_nodes[m] if is_written[x]]
    if len(xs) < 4 or not importers[B]: continue
    reach = {i: (1 << mid[i]) | iclo(i) for i in imports[m]}
    for i in imports[m]:
        others = 0
        for k, v in reach.items():
            if k != i: others |= v
        X = reach[i] & ~others
        if not X: continue
        D = [x for x in xs if Mf[x] & X]
        if not D or len(D) * 4 > len(xs): continue
        users = 0
        for x in D: users |= Ru[x]
        free = importers[B] & ~users
        nfree, nx = bin(free).count('1'), bin(X).count('1')
        if nfree and nx:
            cuts.append((nfree * nx, m, i, nx, len(D), len(xs), nfree, bin(importers[B]).count('1'),
                         sorted(rows[x]['name'] for x in D)[:6]))
cuts.sort(reverse=True)

# ---------------------------------------------------------------- claims
CLASS = ['rooted', 'data', 'study', 'local', 'lean']   # how far a statement reaches

def classify(x):
    me = 1 << mid[rows[x]['mod']]
    mk = Mm[x] & ~me
    if mk & (lmask['core'] | lmask['theory']): return 0
    if mk & lmask['data']: return 1
    if mk & lmask['study']: return 2
    if Am[x] & ~LEAN_ONLY: return 3
    return 4

def flags(x):
    r = rows[x]
    fl = ''
    if dflt_e[x]: fl += 'd'
    if 'b' in r['fl'] and wkind[x] in ('def', 'abbrev'): fl += 'b'
    if any('s' in rows[c]['fl'] for c in members[x]): fl += 's'
    return fl

keep = set()
nshared = {}
study_claims = {}
for m in mods:
    if layer(m) != 'study' or m not in mod_nodes: continue
    cl = [x for x in mod_nodes[m] if is_written[x] and rows[x]['kind'] == 'thm' and 'p' not in rows[x]['fl']]
    study_claims[m] = cl
    seen = set(cl); work = list(cl)
    while work:
        v = work.pop()
        for w in mean_e[v]:
            if w not in seen: seen.add(w); work.append(w)
    keep |= seen
    shared = {}
    for x in cl:
        sx = {x}; wk = [x]; n = 0
        while wk:
            v = wk.pop()
            for w in mean_e[v]:
                if w not in sx:
                    sx.add(w); wk.append(w)
                    if is_written[w] and LAYER[mid[rows[w]['mod']]] in ('core', 'theory'): n += 1
        shared[x] = n
    nshared.update(shared)
    M[mid[m]]['cls'] = [sum(1 for x in cl if classify(x) == k) for k in range(5)]
    hd = [x for x in cl if has_doc[x]]
    M[mid[m]]['hcls'] = [sum(1 for x in hd if classify(x) == k) for k in range(5)]
    M[mid[m]]['closure'] = seen
# traffic: studies whose claims rest on a declaration, and on a module
traffic = collections.Counter(); mtraffic = collections.Counter()
for m, cl in study_claims.items():
    seen = M[mid[m]].pop('closure')
    for x in seen:
        if rows[x]['mod'] != m: traffic[x] += 1
    for mm in {rows[x]['mod'] for x in seen} - {m}: mtraffic[mm] += 1
for m in mods: M[mid[m]]['traffic'] = mtraffic.get(m, 0)

# flagged declarations per module, and the hot list
hot = []
for x in nodes:
    if not is_written[x]: continue
    fl = flags(x)
    if fl:
        M[mid[rows[x]['mod']]].setdefault('flags', []).append([rows[x]['name'], fl, traffic.get(x, 0)])
        if layer(rows[x]['mod']) != 'study': hot.append((traffic.get(x, 0), rows[x]['name'], rows[x]['mod'], fl))
hot.sort(reverse=True)

# ---------------------------------------------------------------- page data
knodes = sorted(keep)
kid = {x: i for i, x in enumerate(knodes)}
times_file = os.path.join(os.path.dirname(os.path.abspath(TSV)), 'times.tsv')
secs = {}
if os.path.exists(times_file):
    for line in open(times_file):
        m, _, t = line.strip().partition('\t')
        if t: secs[m] = float(t)
above = [0.0] * len(mods)                # seconds to rebuild a file and every file above it
if secs:
    for m in mods:
        t = secs.get(m, 0.0); above[mid[m]] += t
        for j in bits(iclo(m)): above[j] += t
src_file = os.path.join(os.path.dirname(os.path.abspath(TSV)), 'source.txt')
source = open(src_file).read().split() if os.path.exists(src_file) else []
recs = [["A", AREAS], ["I", source]]
for d in M:
    recs.append(["M", d['name'], d['layer'], d['group'], d['lines'], int(d['compiled']), d['nimp'], d['nuse'],
                 d['nmean'], d['ndflt'], d['traffic'], d['ndecl'], d.get('cls'), d.get('hcls'), d['imp'], d['need'],
                 d['dead'], d.get('flags', []),
                 round(secs[d['name']], 1) if d['name'] in secs else None,
                 round(above[mid[d['name']]]) if secs else None])
for x in knodes:
    recs.append(["N", rows[x]['name'], mid[rows[x]['mod']], rows[x]['kind'] if is_written[x] else 'gen', flags(x),
                 [kid[y] for y in sorted(mean_e[x]) if y in kid], [aid[a] for a in sorted(mean_a[x])],
                 traffic.get(x, 0)])
for m, cl in study_claims.items():
    recs.append(["C", mid[m], [[kid[x], classify(x), int(has_doc[x]), nshared[x]] for x in cl]])
for c in cuts[:60]:
    recs.append(["S", mid[c[1]], mid[c[2]], c[3], c[4], c[5], c[6], c[7], c[8]])
recs.append(["X", sorted({l.strip() for l in open(MISSING_FILE) if l.strip()})])
with open(OUT + '/graph.json', 'w', encoding='utf-8') as fh:
    fh.write('[\n' + ',\n'.join(json.dumps(r, separators=(',', ':'), ensure_ascii=False) for r in recs) + '\n]\n')
print('graph.json', os.path.getsize(OUT + '/graph.json') // 1024, 'KB;', len(knodes), 'nodes kept', file=sys.stderr)

# ---------------------------------------------------------------- terminal summary
st = [d for d in M if d.get('cls')]
tot = [sum(d['cls'][k] for d in st) for k in range(5)]
print('studies measured:', len(st), '| claims by reach', dict(zip(CLASS, tot)))
htot = [sum(d['hcls'][k] for d in st) for k in range(5)]
print('headline claims by reach', dict(zip(CLASS, htot)))
th = [d for d in M if d['layer'] in ('core', 'theory') and d['compiled']]
print('theory+core modules:', len(th), '| imported', sum(d['nimp'] for d in th), 'used', sum(d['nuse'] for d in th))
print('\nstudies by share of theorems that reach no shared declaration:')
for d in sorted(st, key=lambda d: (-(d['cls'][3] + d['cls'][4]) / max(1, sum(d['cls'])), -sum(d['cls'])))[:12]:
    n = sum(d['cls']); print(f"  {d['name'][8:]:34} {n:4d} claims  {d['cls']}")
print('\nmost overstated imports (theory+core): imported / used / lines / studies resting on it')
for d in sorted(th, key=lambda d: -(d['nimp'] - d['nuse']) * (1 + d['traffic']))[:15]:
    print(f"  {d['name'][8:]:52} {d['nimp']:4d} {d['nuse']:4d} {d['lines']:5d} {d['traffic']:4d}")
print('\nflagged declarations by studies resting on them (d default argument, b literal of 1000 or more, s sorry):')
for t, n, m, fl in hot[:25]: print(f'  {t:4d} {fl:3} {n}  [{m[8:]}]')
print('\nthreads worth cutting: file, import, files only that import brings, declarations needing them / all, files freed / files above')
for c in cuts[:22]:
    print(f"  {c[1][8:]:46} -> {c[2][8:]:44} {c[3]:3d}  {c[4]:3d}/{c[5]:<4d} {c[6]:4d}/{c[7]:<4d} {', '.join(c[8][:3])[:70]}")
