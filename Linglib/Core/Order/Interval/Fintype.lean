module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Interval.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Finitely many intervals

A nonempty interval is a pair of endpoints `a ≤ b`, so the nonempty intervals of a finite order
with decidable `≤` form a finite type, enumerated as the pairs that satisfy the inequality.

## Implementation notes

Mathlib's instance `SetLike.instFintype` already makes the nonempty intervals of a finite partial
order a `Fintype`, through the injection into `Set α`, but noncomputably, so `decide` cannot
evaluate its `Finset.univ`. The instance here is a computable one of the kind the TODO in
`Mathlib/Data/SetLike/Fintype.lean` asks for. It needs only `LE α`, and since the `SetLike`
instance has priority 100, it is the one found. `deriving Fintype` cannot produce it, since the
field `fst_le_snd` needs `DecidableLE α`, so it is built by `derive_fintype%` under that
hypothesis.

`[UPSTREAM]` candidate for a file of its own beside `Mathlib/Order/Interval/Basic.lean`, which
does not import `Fintype`.
-/

@[expose] public section

instance NonemptyInterval.instFintype {α : Type*} [LE α] [Fintype α] [DecidableLE α] :
    Fintype (NonemptyInterval α) :=
  derive_fintype% _
