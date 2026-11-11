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
python3 scripts/checks.py renames
python3 scripts/checks.py selftest
```

`sign` records the hash of the item's statement closure. The closure takes in:

* the types and docstrings of the item's declarations;
* the types and bodies of the project definitions those types mention, followed transitively
  (Mathlib is trusted).

It leaves out every proof, including proofs inside a statement or a definition's body, and the
declarations used only in them. So a proof can change without affecting a sign-off. A change to a
statement, or to a definition it uses, makes the sign-off stale, and `diff` shows the changes
since the signed commit.

The hash is taken over the elaborated terms, not their printed form. A change that printing would
hide, such as to the type of a bound variable, still makes a sign-off stale. Renaming a bound
variable or changing a binder between explicit and implicit does not, since neither changes what
a statement says. A Lean or Mathlib upgrade that changes how a statement elaborates, for instance
by renaming an instance it uses, also makes the sign-off stale, unless the change is a recorded
rename.

### Renames

An upgrade often renames a constant and keeps the old name for a while as a deprecated alias of the
new one, as Mathlib did when `setOf` became `Set.ofPred`. Since the two names mean the same, a
statement that switches from one to the other should keep its sign-off. `renames.toml` records
such renames, and in the hashed terms every name linked by them stands for the one recorded
first. A sign-off made while a statement used `setOf` is then still current once the statement
uses `Set.ofPred`, even after Mathlib removes the alias.

```
python3 scripts/checks.py renames
```

records every rename of a Lean or Mathlib constant that an item's statement closure uses, under
either name. A rename is recorded only if the old name is a definition whose value is the new
one (up to eta), at the same universe levels and with the same type; a deprecation that points to
a constant meaning something else is not a rename. Run it after an upgrade, while the aliases
still exist; `status` says when there is a rename to record, and `sign` refuses to sign until it
is recorded, since recording it later could make the new sign-off stale. Entries are never
removed or reordered. Renames that an upgrade does not mark with a deprecated alias, such as of an
automatically named instance, still make a sign-off stale.

`selftest` checks that the hash behaves this way, on pairs of declarations in
`scripts/checks/ChecksFixture.lean` that differ in one respect each, with a stand-in for Mathlib
in `scripts/checks/ChecksFixtureDeps.lean`. Run it after changing
`scripts/checks/CheckClosure.lean` or upgrading Lean.

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

## Glosses

A reviewer who does not read Lean can ask for a gloss of each item's statement:

```
python3 scripts/checks.py gloss SOURCE --command CMD [--items ex-22,ex-23] > glosses.md
```

A gloss is written by a model, in English, from the item's statement closure alone. It lists
each declaration's parameters, hypotheses and conclusion, says the whole in one sentence,
describes the definitions it uses, and notes anything odd, such as a hypothesis that seems unused
or a statement that is trivially true. The gloss is blind. The model has no tools and no access to
files, docstrings or the source, and the declarations' own names and the study's namespace are
hidden, so it works from the definitions' bodies and says what the Lean says, not what it is meant
to say. A missing hypothesis or a quantifier the wrong way round then shows as a difference between
the gloss and the source.

A gloss is an aid to reading the Lean, not a substitute for it, and never evidence for a sign-off.
It can be wrong, and its observations sometimes go beyond what it has worked out.

`gloss` works with any model. `--command` is a shell command, run from the repository root, that
reads the text to gloss on standard input and the prompt (`scripts/checks/gloss-prompt.md`) from
the file named by `$GLOSS_PROMPT`, and writes the gloss to standard output. For example, with
Claude Code, or with Simon Willison's [`llm`](https://llm.datasette.io), which reaches most hosted
and local models through plugins:

```
--command "scripts/checks/gloss-claude.sh claude-sonnet-5-5"
--command 'llm -m gpt-5 --no-log -s "$(cat "$GLOSS_PROMPT")"'
```

The command must give the model nothing but the prompt and the text: no tools, no files, no memory
of earlier sessions. `gloss-claude.sh` turns these off for Claude Code and runs it in an empty
directory; `llm` offers no tools unless asked to. There is no default command: a gloss of every item
of a paper costs a fair share of a usage limit, and a larger model costs more, so the choice is the
reviewer's. Glosses are cached in `.cache/checks/glosses/` by the command, the prompt and the exact
text glossed, so a gloss is rewritten only when one of these changes.

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
