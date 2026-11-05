# Faithfulness checks

Lean checks that a proof proves its statement. It cannot check that the statement says what the
paper says. The files here record which statements a person has checked against their source.

There is one file per source, `checks/<bib-key>.toml`, named by the source's key in
`references.bib`. It lists the source's items, its numbered definitions, results and data, with
the Lean declarations that state each one:

```toml
source = "elliott-2023"

[[item]]
id       = "ex-22"                       # stable, never reused
kind     = "result"
label    = "(22)"                        # the source's own name for the item
decls    = ["DynamicSemantics.BilateralUpdate.negative_exists_pred1"]
relation = "specializes"
notes    = "Assumes `x` novel at `s` and a nonempty domain."

  [[item.check]]                         # added by `scripts/checks.py sign`
  by     = "patrl"
  date   = 2026-11-04
  commit = "836c3fc25"
  hash   = "a1a64c03eb680068"
```

`kind` says what the item is in the source:

* `definition`: it defines something, which the declarations define or characterize.
* `result`: it asserts something, whether a numbered proposition or a claim made in prose.
* `datum`: it reports a judgment, which the declarations predict.

An item the source makes only in prose has a label naming its section, such as `§3.1, cell 1`.

`relation` says how the Lean statement stands to the source's item:

* `exact`: it states the item.
* `generalizes`: it states something stronger, such as the item without one of its assumptions.
* `specializes`: it states a special case.
* `variant`: it differs in another way.
* `refutes`: it proves the item false, usually by a counterexample. Only a `result` can be refuted.
* `missing`: nothing states the item yet, and `decls` is empty.

Every relation other than `exact` and `missing` needs `notes` saying how the statement departs from
the source; for `refutes`, what the source claims and how the Lean refutes it. A reader relies on
these notes, so they should be precise.

## Signing

A sign-off says that its author has read the source and the Lean and finds that the declarations,
and the project definitions their statements use, say what the item says, up to the `relation` and
`notes`. For a `definition` they define what the source defines; for a `result` they state what it
asserts; for a `datum` they predict the judgment it reports, and the signer has also checked the
recorded example against the source. For a `refutes` item they show that the result is false: the
signer has checked both what the source claims and that the declarations contradict it. Sign-offs
are made by people, never by agents. Proofs need no check, since Lean has checked them.

```
python3 scripts/checks.py status [SOURCE ...]
python3 scripts/checks.py sign SOURCE --items ex-22,ex-23 --by HANDLE
python3 scripts/checks.py sign SOURCE --all --by HANDLE
python3 scripts/checks.py diff SOURCE ITEM
python3 scripts/checks.py core [--json]
```

`sign` records the hash of the item's statement closure. The closure takes in:

* the types and docstrings of the item's declarations;
* the types and bodies of the project definitions those types mention, followed transitively
  (Mathlib is trusted).

It leaves out every proof. So a proof can change without affecting a sign-off. A change to a
statement, or to a definition it uses, makes the sign-off stale, and `diff` shows the changes
since the signed commit. An upgrade of Lean's pretty-printer can also make sign-offs stale.

`status` reports each item as one of the following:

* `checked`: its sign-off is current, and so is the sign-off of every item covering a definition
  its statement uses.
* `relies`: its own sign-off is current, but such an item is not checked.
* `stale`, `unchecked`, `missing`.
* `broken`: one of its declarations does not resolve.
* `unproved`: one of its declarations rests on `sorry`, or on an axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, through its proof or a definition it uses. This includes the
  axiom that `native_decide` adds, which trusts the compiler. The status line still shows the
  sign-off, since a statement can be faithful without being proved.

## The reviewed core

`core` lists the declarations of the checked items, with the project definitions their statements
use, grouped by module; `--json` gives the same as data. An item is checked only if the items it
relies on are, so the core is closed: nothing in it depends for its meaning on a declaration
outside it. Its proofs may use declarations outside it, which need no review, and it is relative to
the Mathlib that the project pins.

The docs pages show, under each declaration stating a `checked`, `relies` or `stale` item, who
checked it and when, which item it relies on, or that it has changed since; the docs workflow
reads `checks.py status --json`.

Who checks which source is arranged in GitHub issues, not here. The files record only what has been
checked.
