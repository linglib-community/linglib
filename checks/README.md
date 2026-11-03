# Faithfulness checks

Lean checks that a proof proves its statement. It cannot check that the statement says what the
paper says. The files here record which statements a person has checked against their source.

There is one file per source, `checks/<bib-key>.toml`, named by the source's key in
`references.bib`. It lists the source's claims, its numbered definitions, propositions, remarks
and examples, with the Lean declarations that state each one:

```toml
source = "george-2014"

[[claim]]
id       = "prop-4"                      # stable, never reused
label    = "Proposition 4"               # the source's own name for the claim
decls    = ["Quantifier.universalEntailment_iff_trueOf"]
relation = "exact"
notes    = "George's bound `n < |U|` is carried by `TrueOf` (see def-23)."

  [[claim.check]]                        # added by `scripts/checks.py sign`
  by     = "patrl"
  date   = 2026-11-04
  commit = "836c3fc25"
  hash   = "a1a64c03eb680068"
```

`relation` says how the Lean statement stands to the source's claim:

* `exact`: it states the claim.
* `generalizes`: it states something stronger, such as the claim without one of its assumptions.
* `specializes`: it states a special case.
* `variant`: it differs in another way.
* `missing`: nothing states the claim yet, and `decls` is empty.

Every relation other than `exact` and `missing` needs `notes` saying how the statement departs from
the source. A reader relies on these notes, so they should be precise.

## Signing

A sign-off says that its author has read the source and the Lean and finds that the declarations,
and the project definitions their statements use, say what the claim says, up to the `relation` and
`notes`. Sign-offs are made by people, never by agents. Proofs need no check, since Lean has
checked them.

```
python3 scripts/checks.py status [SOURCE ...]
python3 scripts/checks.py sign SOURCE --claims prop-4,prop-5 --by HANDLE
python3 scripts/checks.py sign SOURCE --all --by HANDLE
python3 scripts/checks.py diff SOURCE CLAIM
python3 scripts/checks.py core [--json]
```

`sign` records the hash of the claim's statement closure. The closure takes in:

* the types and docstrings of the claim's declarations;
* the types and bodies of the project definitions those types mention, followed transitively
  (Mathlib is trusted).

It leaves out every proof. So a proof can change without affecting a sign-off. A change to a
statement, or to a definition it uses, makes the sign-off stale, and `diff` shows the changes
since the signed commit. An upgrade of Lean's pretty-printer can also make sign-offs stale.

`status` reports each claim as one of the following:

* `checked`: its sign-off is current, and so is the sign-off of every claim covering a definition
  its statement uses.
* `relies`: its own sign-off is current, but such a claim is not checked.
* `stale`, `unchecked`, `missing`.
* `broken`: one of its declarations does not resolve.
* `unproved`: one of its declarations rests on `sorry`, or on an axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, through its proof or a definition it uses. This includes the
  axiom that `native_decide` adds, which trusts the compiler. The status line still shows the
  sign-off, since a statement can be faithful without being proved.

## The reviewed core

`core` lists the declarations of the checked claims, with the project definitions their statements
use, grouped by module; `--json` gives the same as data. A claim is checked only if the claims it
relies on are, so the core is closed: nothing in it depends for its meaning on a declaration
outside it. Its proofs may use declarations outside it, which need no review, and it is relative to
the Mathlib that the project pins.

The docs pages show, under each declaration stating a `checked`, `relies` or `stale` claim, who
checked it and when, which claim it relies on, or that it has changed since; the docs workflow
reads `checks.py status --json`.

Who checks which source is arranged in GitHub issues, not here. The files record only what has been
checked.
