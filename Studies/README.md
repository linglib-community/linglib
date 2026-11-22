# `Studies/`: one paper per file

Each file formalizes one paper and is named by author and year:

```
Studies/{AuthorYear}.lean        -- namespace AuthorYear
```

The layout is flat, with no subdirectories. The studies are the library's test suite: each one
states a paper's model on the shared theory layer and proves the predictions the paper claims.

## What a study contains

A study is self-contained: the paper's data, its model, and its predictions. It imports the
theory layer (`Linglib/Semantics/`, `Linglib/Syntax/`, ...) and `Linglib/Fragments/`, and works at
the paper's own granularity.

- **Build on what exists.** When the theory layer already defines an operator or type the paper
  uses, state the study's theorems about that definition instead of a local copy.
- **Derive, don't stipulate.** Define the structural property and prove the conclusion from it.
  A table of verdicts checked by `decide` is a transcription, not a derivation.
- **Respect chronology.** A study may build on, and prove consistency with, older papers, never
  newer ones. A comparison between two papers lives in the later paper's file.
- **One paper only.** A file that synthesizes across papers without being anchored to one of them
  does not belong here.

## Why flat?

A taxonomy by phenomenon is editorial: many papers contribute to several phenomena, and every
rename or split would move files. Discovery by topic is served instead by the `[key]` citation
links, which index every file that cites a given entry of `references.bib`.

## Naming

- **Same authors, same year.** Distinct works take APA letters in title order, in the file name
  and the bib key alike: `Lewis1973a.lean` (*Causation*, `lewis-1973a`) and `Lewis1973b.lean`
  (*Counterfactuals*, `lewis-1973b`).
- **Two formalizations of one paper** grow one file instead of a suffixed sibling: `Heim1992.lean`
  holds both the belief-projection and the desire halves.
- **A second file for the same paper**, when one is unavoidable, takes a topical suffix on the
  newer arrival, so existing importers are not disturbed.

## Example data

Per-paper example sentences are generated from `Linglib/Data/Examples/{AuthorYear}.json` into the
module `Linglib/Data/Examples/{AuthorYear}.lean`, which declares `namespace {AuthorYear}.Examples`.
The study imports it (`import Linglib.Data.Examples.{AuthorYear}`) and refers to `Examples.all`,
`Examples.ex29a`, and so on inside its own namespace.

Generate with `python3 scripts/gen_examples.py <AuthorYear>`. The schema and format conventions
are in [`Linglib/Data/Examples/README.md`](../Linglib/Data/Examples/README.md); glosses follow the
[Leipzig glossing rules](https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf).
