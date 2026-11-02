module

public import Mathlib.Order.Antichain

/-!
# Strict-monotone preimage of an antichain

`[UPSTREAM]` candidate for `Mathlib/Order/Antichain.lean`: a `StrictMono`
pullback lemma for `≤`-antichains, complementing mathlib's existing
`IsAntichain.preimage` (injective + relation-preserving) and
`IsAntichain.preimage_embedding` (order embeddings). On a partial order
`StrictMono` is strictly weaker than `Injective ∧ Monotone`, so this
*generalizes* the `≤`-instance of `preimage`.

This file mirrors mathlib's `Order/Antichain.lean` path: on upstreaming, the
lemma moves verbatim into `namespace IsAntichain` there and this file is
deleted.

## Main statements

* `IsAntichain.preimage_strictMono`
-/

public section

namespace IsAntichain

/-- The preimage of a `≤`-antichain under a strictly monotone map is a
`≤`-antichain. Unlike `IsAntichain.preimage` (which needs `f` injective and
relation-preserving) and `IsAntichain.preimage_embedding` (order embeddings),
this needs only `StrictMono f` — strictly weaker on a partial order. -/
theorem preimage_strictMono {α β : Type*} [PartialOrder α] [Preorder β] {s : Set β}
    (hs : IsAntichain (· ≤ ·) s) {f : α → β} (hf : StrictMono f) :
    IsAntichain (· ≤ ·) (f ⁻¹' s) := by
  intro a ha b hb hab hab_le
  have hlt : f a < f b := hf (lt_of_le_of_ne hab_le hab)
  exact hs ha hb hlt.ne hlt.le

end IsAntichain
