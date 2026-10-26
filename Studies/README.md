# `Studies/` — paper-anchored study files

Flat layout: one file per paper, named by author-year.

```
Studies/{AuthorYear}.lean        -- namespace AuthorYear
```

For rare multi-file papers, a per-paper subdirectory:

```
Studies/{AuthorYear}/Basic.lean      -- namespace AuthorYear
Studies/{AuthorYear}/{Topic}.lean
```

The full set (current): `Beaver2001/`, `Charlow2021/`, `Heim1982/`,
`IppolitoKissWilliams2025/`, `OsborneGross2012/`, `StankovaSimik2024/`.

## Why flat?

Phenomenon taxonomy is editorial — many papers contribute to multiple
phenomena, and rename/merge/split decisions would force path churn. The
`[key]` reverse index in `blog/data/references.bib` already provides
phenomenon-based discovery (and `grep -l "Phenomena.X" Studies/` recovers
ad-hoc groupings). Flat eliminates the placement debate.

## Same author, same year

Distinct works by the same authors in the same year take APA letters in title order, in the file
name and the bib key alike: `Lewis1973a.lean` (*Causation*, `lewis-1973a`) and `Lewis1973b.lean`
(*Counterfactuals*, `lewis-1973b`).

## Cross-phenomenon name collisions

When the same paper appears in multiple phenomena (different chapters /
applications / aspects), suffix the *newer* arrival with a topical
descriptor, minimising churn to consumers of the existing file:

| Pattern | Example |
|---|---|
| Chapter suffix | `Cooper2023.lean` (Anaphora) + `Cooper2023Ch6.lean` (Modality) + `Cooper2023Ch7.lean` (Quantification) + `Cooper2023Ch8.lean` (Anaphora) |
| Phenomenon suffix | `Dryer2013.lean` (Complementation WALS) + `Dryer2013Question.lean` + `Dryer2013Negation.lean` |
| Suffix-on-arrival | `Rouillard2026.lean` (TenseAspect) + `Rouillard2026Gradability.lean` (the newer file gets the suffix) |

Two formalisations of the same paper grow one file rather than a
suffixed sibling (`Heim1992.lean` holds both the belief-projection and
the desire halves): the suffix is for cross-paper collisions only.

## Bridge files don't belong here

Files that synthesise across multiple papers but aren't anchored on a
single paper (e.g., `AspectualConsistency`, `TheoryComparison`,
`SPEDerivations`, `TowerDerivation`) belong in the relevant phenomenon
directory as topical siblings of the data files, or in `Theories/` if
they extend a framework.
Studies/ is paper-anchored content only.

## Examples and generated content

Per-paper example data is generated from `Linglib/Data/Examples/{AuthorYear}.json`
into a standalone auto-generated module `Linglib/Data/Examples/{AuthorYear}.lean`
declaring `namespace {AuthorYear}.Examples`; the study file imports it
(`import Linglib.Data.Examples.{AuthorYear}`) and refers to `Examples.all`,
`Examples.ex29a`, ... inside its own namespace.

Generator: `python3 scripts/gen_examples.py <AuthorYear>`. (The former
in-study marker-block splice is retired; re-running the generator on a
legacy paper migrates it automatically.)

Schema reference and format conventions:
[`Linglib/Data/Examples/README.md`](../Data/Examples/README.md). Leipzig
glossing rules per [Comrie/Haspelmath/Bickel 2008](https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf).
