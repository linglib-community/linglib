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
claim    = """
The negative update of ∃xP(x) picks out the possibilities in s at which there are no Ps.
"""
decls    = ["DynamicSemantics.BilateralUpdate.negative_exists_pred1"]
relation = "specializes"
notes    = "Assumes `x` novel at `s` and a nonempty domain."
```

`claim` says in words what the source says about the item: the item as the source states it,
with its formulas, and what is odd about it, such as a definition that contradicts its own prose.
It is the inventory half of the record, and `decls`, `relation` and `notes` are the mapping to
Lean, which says how the declarations state it. Anyone can write a claim, by hand or not, since a
sign-off covers it: the signer checks the claim and the declarations against the source, and
rewording the claim makes the sign-off stale. It is not the place for how the Lean departs from
the source, which is the `notes`. The source's edition is the bibliography's business, since the
file is named by the key.

Sign-offs are not kept in this file, but in the ledger, `checks/ledger/` (see below).

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
* `counterexample`: it gives a counterexample to the item as stated. Only a `result` can have one. When the item holds under a restriction, state that as a `specializes` item and list the counterexample among its `decls`, to show that the restriction is needed.
* `missing`: nothing states the item yet, and `decls` is empty.

Every relation other than `exact` and `missing` needs `notes` saying how the statement departs from
the source; for `counterexample`, what the source claims and how the Lean contradicts it. A reader relies on
these notes, so they should be precise.

## Signing

A sign-off says that its author has read the source and the Lean and finds that the declarations,
and the project definitions their statements use, say what the item says, up to the `relation` and
`notes`. For a `definition` they define what the source defines; for a `result` they state what it
asserts; for a `datum` they predict the judgment it reports, and the signer has also checked the
recorded example against the source. For a `counterexample` item they show that the result is false: the
signer has checked both what the source claims and that the declarations contradict it. Sign-offs
are made by people, never by agents. Proofs need no check, since Lean has checked them.

```
python3 scripts/checks.py status [--ci] [SOURCE ...]
python3 scripts/checks.py sign SOURCE --items ex-22,ex-23 --by HANDLE
python3 scripts/checks.py sign SOURCE --all --by HANDLE
python3 scripts/checks.py sign SOURCE --all --by "A. Reviewer" --via email
python3 scripts/checks.py diff SOURCE ITEM
python3 scripts/checks.py core [--json]
python3 scripts/checks.py renames
python3 scripts/checks.py verify-ledger --base origin/main --author HANDLE
python3 scripts/checks.py selftest
```

`sign` records the hash of the item: what the check file says about it, and its statement
closure. The record is the item's `claim`, `kind` and `relation`, its `decls` and its `notes`,
so that changing any of them after a sign-off makes it stale; the whitespace of the claim and
notes, and the order of the declarations, do not count. The closure takes in:

* the types of the item's declarations;
* the types and bodies of the project definitions those types mention, followed transitively
  (Mathlib is trusted).

It leaves out every proof, including proofs inside a statement or a definition's body, and the
declarations used only in them, and every docstring. So a proof or a docstring can change without
affecting a sign-off. A change to a statement, or to a definition it uses, makes the sign-off
stale, and `diff` shows what changed since the sign-off.

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

## Walkthrough: reviewing a paper

This is the path from a paper and its study file to signed items. You need the paper (you supply
it; nothing here fetches it), the repository built (`lake build`), Python 3.11 or later, and, for
the model steps, a way to run a model, such as Claude Code. Sign-offs are made by you, at your own
terminal; an agent never signs.

1. **Find the source's key.** It is the paper's key in `references.bib`, such as `elliott-2023`,
   and the study is its file in `Studies/`. If the paper has no entry, add one first. The check file
   will be `checks/<key>.toml`.
2. **Draft the record.** If there is no `checks/<key>.toml` yet, ask an agent to follow
   `scripts/checks/draft-record.md`, giving it the paper, the key and the study file. It writes the
   claims from the paper alone, then maps them onto the study's declarations (see *Drafting a
   record* below). The draft is unsigned. If you would rather write it by hand, copy the example at
   the top of this file: one `[[item]]` per definition, result or datum of the paper.
3. **Read the claims against the paper.** This is the step that matters most, and it is yours. A
   claim must say what the paper says, with its formulas and conditions, including where the
   paper is odd or wrong. Fix a claim by editing it to match the paper, never to match the Lean. Add
   an item the draft missed, and split one that is really two things. Check each `kind` and
   `label`.
4. **Read the mapping.** For each item, check `decls`, `relation` and `notes`: do the declarations
   state the item, and does the relation and the note describe how they depart from it? Change
   them if not. `python3 scripts/checks.py status <key>` reports `broken` for a name that does
   not resolve.
5. **Have the Lean back-translated (optional).** This uses a model, and so a share of your usage
   limit:

   ```
   python3 scripts/checks.py review <key> --command "scripts/checks/gloss-claude.sh claude-sonnet-5-5" > review.md
   ```

   Read `review.md` from the top. *Looks unfaithful* lists items where a model that saw only the
   Lean describes something different from the claim: read that Lean first. *Looks right* is the
   lowest-risk group, not a verified one. Use `gloss` alone (see *Glosses*) if you only want the
   descriptions.
6. **Read the Lean, then sign.** For each item, read the declarations and the project definitions
   their statements use, as you would a proof you have to believe, and decide whether they say what
   the claim says up to the `relation` and `notes`. If not, fix the record (or the Lean, in a
   separate change) and look again. When you are satisfied with some items:

   ```
   python3 scripts/checks.py sign <key> --items ex-22,ex-23 --by <your-github-handle>
   python3 scripts/checks.py sign <key> --all --by <your-github-handle>   # every unsigned or stale item
   ```

   This writes a file to `checks/ledger/`. Sign only what you have read; a sign-off is your
   statement that you did. If you review for someone without a GitHub account, record their
   sign-off with their name in `--by` and `--via` saying how they told you (see *The ledger*).
   Edit claims before you sign: changing a claim, a `relation`, `decls` or `notes` afterwards makes the
   sign-off stale.
7. **Check and open a pull request.** `python3 scripts/checks.py status <key>` should show your
   items as `checked`, or `relies` where an item they depend on is not signed yet. Commit the
   check file and the new `checks/ledger/` files under your own account, and open the pull
   request from it: the CI job `verify-ledger` requires that the signer is the pull request's
   author, unless there is a `via`.

Later, if a statement or a definition it uses changes, `status` shows the item `stale`, and
`python3 scripts/checks.py diff <key> <item>` shows what changed since you signed. Read it, and
sign again if the item still says what the paper says.

## Drafting a record

A reviewer who has a paper and its study file can have a first draft of the record written, and the
Lean checked against it, by models. Nothing in the draft is a sign-off, and the claims still need a
person to read them against the paper. An agent follows `scripts/checks/draft-record.md`
to run it; its stages are:

1. **Claims.** A model reads the paper and nothing else, and writes each item's `id`, `kind`,
   `label` and `claim` (`scripts/checks/draft-claims-prompt.md`). It has not seen the Lean, so the
   claims say what the paper says, whether or not the study formalizes it that way.
2. **Mapping.** A second model, which has not seen the paper, is given those claims and the study
   file, and writes `decls`, `relation` and `notes` (`scripts/checks/draft-mapping-prompt.md`). It
   may not change a claim: where the Lean departs from one, the departure goes in the `relation`
   and `notes`. It also lists the study's declarations that match no item.
3. **Back-translation.** Each item's declarations are described in English by a model that sees
   only their statement closure (the blind `gloss` of the next section).
4. **Comparison.** A third model sees the claim, the `relation` and `notes`, and the back-translation,
   but neither the paper nor the Lean, and says whether the back-translation agrees with the claim
   up to the departures the notes disclose (`scripts/checks/compare-prompt.md`).

Steps 3 and 4 are `checks.py review`:

```
python3 scripts/checks.py review SOURCE --command CMD [--items ID,...] [--jobs N] [--refresh]
```

with the `--command` of `gloss`. It sorts the items into four groups: *looks unfaithful* (the
comparison found a difference the record does not disclose), *needs a look* (unclear, or no
review), *departs as the record says* (agrees, with a relation other than `exact`), and *looks
right* (agrees, with `exact`). It exits non-zero if any item looks unfaithful. A `missing` item is
listed as not formalized. The same blindness rules as for glosses apply, and each model is given the
least it needs: the model that writes the claims does not see the Lean, and the model that compares
sees neither.

The review is a guide to where to read first. A group of items that look right is the lowest-risk
group, not a verified one, since every stage can be wrong, in the same direction too.

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

## The ledger

A sign-off holds what its signer read, since the repository squashes pull requests and a commit
made on a PR branch never reaches `main`. Sign-offs are kept in an append-only ledger,
`checks/ledger/`, with one file per signing event, so that two people signing at once do not
conflict. A file is named by the hash of its contents, and holds the items signed, each with the
hash of its statement closure and a list of the declarations in it:

```toml
# checks/ledger/<hash>.toml
source      = "elliott-2023"
by     = "A. Reviewer"             # who checked; a GitHub login unless there is a `via`
via    = "email"                   # for a sign-off recorded for someone else
date   = 2026-11-12T10:32:05Z

[[item]]
id       = "ex-22"
hash     = "a1a64c03eb680068"
kind     = "result"                # the record as the signer saw it, for `diff`
relation = "specializes"
decls    = ["DynamicSemantics.BilateralUpdate.negative_exists_pred1"]
claim    = "The negative update of ∃xP(x) picks out the possibilities at which there are no Ps."
notes    = "Assumes `x` novel at `s` and a nonempty domain."
nodes = [
  { name = "DynamicSemantics.…", term = "9f2c…", text = "41b7…" },
]
```

`ledger/nodes/<text-hash>.txt` holds the text of each declaration in the closure as the signer
read it, shared by every sign-off that read it. `diff` compares those texts, and the record, with
the current ones, so it needs no commit and still works after a squash. It also names a
declaration whose printed text is the same but whose term differs. The docs pages say that a
statement has changed since the sign-off, and point to `diff`. An item is current if the hash of
its newest ledger entry is its hash now.

**Who checks.** `by` is a GitHub login, that of the pull request's author, and git records who
added the file. A reviewer without an account is named in `by` instead, and someone else records
the sign-off for them, giving `via`: how the reviewer made the check known, such as `email` or
`issue #123`, with no contact details. The admin who merges the pull request vouches for it, as
for any change from outside. Sign-offs are still made by people, never by agents.

`sign` enforces the `via` rule when it writes the file. CI enforces all of them, with
`verify-ledger`, in a job on every pull request. It fails a pull request that:

* changes or deletes a file in `checks/ledger/`, or has one whose name is not the hash of its
  contents or whose node texts are missing;
* is made by a bot account, or one whose login or `by` names a bot or an agent (a name
  containing `bot`, `claude`, `copilot`, `codex`, `gemini` or `gpt`, which stops accidents rather
  than a determined effort);
* has a `by` that is not the PR's author, without a `via`;
* signs an item that the check file does not list.

A step of the build job runs `status --ci` after the build. It reports a `broken` item, so that
a renamed or removed declaration is caught, and a `stale` item as warnings, since a statement
may change and its sign-off then says so. It fails only on an invalid check file.

CI cannot tell a person from an agent working under that person's account. The check in `sign`
that refuses to run under Claude Code is a guard against accidents, and review of the pull request
does the rest.

Not built: a proof that a changed statement still agrees with a signed one (the texts stored
here are what such a proof would be stated against), and the mapping (`decls`, `relation`,
`notes`) kept in the Lean source, as an attribute on the declarations, which would follow them
through renames and moves.
