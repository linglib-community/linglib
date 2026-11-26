#!/usr/bin/env python3
"""Write the grouping and layout table that the dependency map at linglib.io/taproot/ reads.

The map is drawn by the tooling of linglib-community/taproot, which knows nothing about
linguistics. This table tells it two things about this library:

* the family of each language directory, taken from the WALS language table
  (`Linglib/Data/WALS/raw/languages.csv`) where the directory is named as a WALS language or genus
  is, so that the hundred-odd language directories are drawn by family. A directory with no such
  match is left out and drawn ungrouped; nothing is guessed.
* where the theory areas sit on the top-level map, as `[column, row]`: the levels of grammar in
  their usual order, logic beneath semantics, processing to the side. This is a choice about the
  picture, not a measurement; the arrows on the map show what imports what.

Usage, from the repository root:

    python3 scripts/taproot_groups.py --out FILE.json
"""

import argparse
import collections
import csv
import json
import os
import re

LANGUAGES = 'Linglib/Languages'
WALS = 'Linglib/Data/WALS/raw/languages.csv'
LAYOUT = {'': {'Phonology': [0, 0], 'Morphology': [1, 0], 'Syntax': [2, 0], 'Semantics': [3, 0],
               'Pragmatics': [4, 0], 'Discourse': [5, 0], 'Processing': [1, 1], 'Logic': [3, 1]}}


def norm(s):
    return re.sub(r'[^a-z]', '', s.lower())


def families():
    dirs = sorted(d for d in os.listdir(LANGUAGES) if os.path.isdir(os.path.join(LANGUAGES, d)))
    by_name, by_genus = collections.defaultdict(set), collections.defaultdict(set)
    with open(WALS, encoding='utf-8') as f:
        for r in csv.DictReader(f):
            for k in (norm(r['Name']), norm(re.sub(r'\s*\(.*?\)', '', r['Name']))):
                by_name[k].add(r['Family'])
            by_genus[norm(r['Genus'])].add(r['Family'])
    out = {}
    for d in dirs:
        for table in (by_name, by_genus):
            fams = {f for f in table.get(norm(d), ()) if f and f != 'other'}
            if len(fams) == 1:
                out[d] = fams.pop()
                break
    return out, len(dirs)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    fam, n = families()
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, 'w', encoding='utf-8') as f:
        json.dump({'Languages': fam, '@layout': LAYOUT}, f, indent=0, sort_keys=True)
    print(f'{args.out}: {len(fam)} of {n} language directories have a WALS family')


if __name__ == '__main__':
    main()
