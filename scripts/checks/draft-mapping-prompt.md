You relate a list of items from a linguistics paper to the Lean declarations of a study file that
formalizes it. You are given the items, each with a `claim` that says what the paper says, and a
study file.

The claims are the standard. They were written from the paper alone. You must not edit, reword or
drop a claim to fit the Lean, add an item because the Lean has one, or treat the Lean's way of
putting things as correct. If the Lean departs from a claim, the departure is what you report: that
is exactly what a human reviewer will assess. The study file's docstrings and names say what the
author intended; they are not evidence of what the declarations say. Read the definitions' bodies.

## Task

For each item, find the declarations that state it (a definition, a theorem, or for a datum the
theorem or `example` that predicts it) and give:

* `decls`: the fully qualified names of those declarations, as Lean resolves them (namespace
  included). Only declarations that state the item, not lemmas used in proving it. For a
  `definition`, the definition and any declaration that characterizes it. Check that each name
  exists; do not guess a name.
* `relation`, one of:
  * `exact`: the declarations state the item, with nothing added and nothing dropped.
  * `generalizes`: they state something stronger, such as the item without one of its assumptions.
  * `specializes`: they state a special case, for instance with an added hypothesis, a fixed
    domain, or only one of several clauses.
  * `variant`: they differ in another way (a different but related definition, a changed
    representation, a different formulation that is not equivalent).
  * `counterexample`: they give a counterexample to the item as stated (only for a `result`).
  * `missing`: nothing states the item, and `decls` is empty.
* `notes`: required unless the relation is `exact` or `missing`. Say precisely how the Lean
  departs from the claim: which hypothesis is added or dropped, which clause is absent, what the
  representation is. A reviewer relies on these notes.

Choose `exact` only when you have compared the statement with the claim clause by clause. When in
doubt between `exact` and anything else, choose the other and say why in `notes`. Choose `missing`
rather than a declaration that only resembles the item. A declaration may state several items and an
item may need several declarations.

A declaration in the study file that no item corresponds to is not an item: list it at the end,
under `unmatched`, so the reviewer can see what the paper does not state.

## Output

Only TOML, with no commentary. First every item, with its `id` and the fields above, in the
claims' order; claims are left out, since they are not yours to change.

```toml
[[item]]
id       = "ex-22"
decls    = ["Namespace.theorem_name"]
relation = "specializes"
notes    = """
Assumes … .
"""
```

Then, once:

```toml
unmatched = ["Namespace.declaration", …]
```
