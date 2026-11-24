# Contributing to Linglib

Linglib is a community library for formal linguistics in Lean 4. This
guide describes the most common ways to contribute, with the
conventions you'll need to know inlined. The codebase is also
extensively documented in module docstrings — when in doubt, look at
existing files in the same area.

## Getting set up

1. Install [Lean 4 via elan](https://leanprover-community.github.io/get_started.html).
2. Clone the repo and fetch the mathlib cache:
   ```bash
   git clone https://github.com/linglib-community/linglib
   cd linglib
   lake exe cache get
   lake build Studies.Jenks2018   # one module and what it imports
   lake build                     # everything
   ```
3. While working, build the modules you touched; CI runs the full
   build on every PR. `sorry`s in the codebase
   are intentional placeholders for in-progress proofs.

## Three entry points

### Formalize a paper

Most contributions start by picking a paper from a subfield you know
and writing a study file at `Studies/{AuthorYear}.lean` (study
files are flat, named author-year).

A study file typically:
- Imports the relevant theory layer (`Linglib/Semantics/`,
  `Linglib/Syntax/`, `Linglib/Pragmatics/`, …).
- Imports any cross-linguistic data needed from `Linglib/Languages/`.
- Encodes the paper's model — definitions, denotations, constraint
  ranking, whatever the paper specifies — in Lean syntax.
- Proves the predictions the paper claims, using the encoded model.
- Cites the paper in the module docstring with a `[key]` link (add the
  BibTeX entry to `references.bib` first).

Look at any existing file under `Studies/` for a template —
`Studies/Jenks2018.lean` (definiteness) and
`Studies/FrankGoodman2012.lean` (an RSA implicature model) are
reasonable starting points. `Studies/README.md` covers file naming.
Theory-neutral empirical data lives separately under `Linglib/Data/`
(see `Linglib/Data/README.md`).

### Add a language

The files under `Linglib/Languages/{Language}/` hold the lexical
entries and typological metadata for one language. Even a sparse
language — say, a handful of pronouns and a tense paradigm — is
useful, because it lets phenomena studies cite real cross-linguistic
data instead of toy examples.

If you work on a language whose typological profile is poorly
represented (most non-Indo-European languages outside our existing
sample), a small contribution here goes a long way. See an existing
language (e.g. the files under `Linglib/Languages/English/`) for the
schema.

### Report a problem

If a definition seems wrong, a theorem trivializes the empirical
content, or you spot an inconsistency between two theories that
should agree, [open an issue](https://github.com/linglib-community/linglib/issues).
Critical readings are welcome — formalization makes mistakes visible,
and we want them caught.

## Repository layout

The library is layered, from foundational to derived, and imports only
point downstream:

- `Linglib/Core/`: framework-neutral mathematics, organized like
  mathlib.
- `Linglib/Semantics/`, `Syntax/`, `Pragmatics/`, `Morphology/`,
  `Phonology/`, `Processing/`, `Discourse/`, `Logic/`: reusable
  theory, shared by several studies.
- `Linglib/Generalizations/`: statements about data that theories are
  tested against. They mention no framework.
- `Linglib/Data/`: empirical observations, with no theory imports.
- `Linglib/Languages/{Language}/`: lexical data for one language,
  typed by the theory layer.
- `Studies/`: one paper per file, named `AuthorYear.lean`. The studies
  are the library's test suite.

When a study needs something a lower layer already provides, import it
rather than defining a local copy. That sharing is what lets a change
to one theory show its consequences everywhere else.

### Where a file goes

Directories are addresses. What a file assumes is what it imports, so
the layering of the library is read from the import graph and is not
declared anywhere. To place a file under `Linglib/Syntax/`, ask these
questions in order. The first yes decides.

1. **Is it a claim about data that names no construction?**
   `Linglib/Generalizations/<Name>.lean`, named as the field names it.
2. **Is it a type that descriptions are written in**, such as a
   category, a feature or an order? `Syntax/<Object>/`.
3. **Is it a structure any framework could build on**, such as a tree,
   a spine or a graph? `Syntax/<Structure>/`.
4. **Is it theory stated only on those shared types?** It lives with
   the shared object it is about. One account's analysis is named for
   the account, as `Tree/Shell.lean` is.
5. **Does it need a framework's own objects**, such as a probe or a
   sign? That framework's directory. A file that relates the
   framework's objects to a shared type `T` is named for `T`, as
   `Minimalist/Spine.lean` is.
6. **Is it mathematics mathlib would accept?** `Linglib/Core/`.

The directory follows what a file imports. Whose idea it is goes in
the file's name and its references.

Three rules are checked on every push: nothing in `Generalizations/`
imports a framework, no shared file of `Syntax/` imports a framework,
and no framework of syntax imports another. Two frameworks are not
related in one file. Each proves what its own construction amounts to
in a shared form, and the two results have one right-hand side.

### Generalizations, accounts and linking maps

The library keeps three things apart, so that a claim about a theory
can be checked against data and against other theories.

- **A generalization** is a statement about data: a predicate on a
  descriptive type, such as a pairing of two persons or an order of
  words. It mentions no framework. Generalizations live in
  `Linglib/Generalizations/`.
- **An account** is a framework's construction, stated in the
  framework's own vocabulary. It lives in the framework's directory or
  in a study.
- **A linking map** takes the account's objects to a descriptive type.
  It lives in the framework, in a file named for the type it maps
  into.

What an account predicts is the range of its linking map. The usual
terms for comparing theories then have plain meanings:

| Term | Meaning |
|---|---|
| the account derives a generalization | every description in its range satisfies it |
| the account overgenerates | its range contains a description no language attests |
| one account is more restrictive | its range is contained in the other's |
| two accounts are notational variants | their ranges are equal |
| a datum decides between two accounts | it is in one range and not the other |
| a claim is testable on some data | it depends only on what the linking map shows |
| parameters are identifiable | different settings give different descriptions |

These are ordinary statements about functions and sets, written with
mathlib's own vocabulary: `Set.range`, `⊆`, `Function.FactorsThrough`,
`Function.Injective`. There is no interface to implement. Write the
linking map, and state what you can prove about its range.

These are statements about constructions and what they can produce,
not about the papers that propose them. A study records where a
construction comes from; it is not scored against the others.

## Code conventions

A few conventions are worth knowing before your first PR. Look at
existing files in the same area for full context — the codebase is
the canonical reference.

**File structure.** Every `.lean` file should have a `/-! ... -/`
module docstring placed *after* the `import` statements (Lean
requires imports to come first).

**Citations.** Cite papers with a `[key]` link (`[kratzer-1991]`);
never inline `Author (Year)`. Add the BibTeX entry to `references.bib`
first using `lastname-lastname-year` keys, and validate with
`python3 scripts/check_citations.py`. Check every field of a new entry
against the publication itself, and don't cite an equation, section, or
page number from memory: a missing DOI is better than a wrong one. The
rendered bibliography is a build artifact (regenerated in CI) — don't
commit it.

**Proof style.** Prefer structural tactics (`exact`, `simp only`,
`decide`, `omega`, `linarith`) over bare `simp` or `native_decide`.
Bare `simp` is fragile under simp-set changes; `native_decide`
bypasses kernel verification.

**Derive, don't stipulate.** A definition that encodes its own
conclusion (`def canBridge := true`, then a theorem proving it by
`rfl`) shows nothing. Define the structural property and prove that
the conclusion follows from it.

**`sorry` over weakening.** State the full theorem and use `sorry`
to mark it incomplete — a `sorry` warning is explicit, while a
weakened-but-proved theorem can be silently forgotten as not having
captured the intended claim.

**Lean style.** `autoImplicit` is disabled (declare type parameters
explicitly). Write `fun x ↦ e`, not `λ`. Use `Type*` not `Type 0`. Prefer `Prop` with
`[DecidablePred]` over `Bool` for predicate-shape data. Use
`lowerCamelCase` for lemma names.

**Imports.** Only import what's needed — no `import Mathlib`
blanket. Cite the leaf file. Unnecessary imports slow builds and
create false dependency edges.

## Pull requests

- Branch from `main`, push to a fork, open a PR.
- One coherent change per PR. Small is good.
- The repo is **squash-merge only**, so the PR title becomes the commit
  on `main` — write it in mathlib's `type(scope): subject` form
  (lowercase imperative, ≤ 72 chars), e.g.
  `feat(Studies): formalize Jenks 2018 definiteness`.
- Put the longer story in the PR description; declare cross-PR
  dependencies with a `Depends on #NNNN` line.

If you're not sure whether a contribution makes sense, open an issue
first to discuss. Substantive feedback on direction is welcome before
you've written code.

## Scope of welcome

Contributions are welcome from undergraduates working through their
first formal-semantics course, postdocs with strong opinions about
particular frameworks, computational linguists with probabilistic
models to formalize, and Lean enthusiasts looking for a domain. You
do not need to be a working academic linguist to contribute, and you
do not need to know mathlib internals to start.
