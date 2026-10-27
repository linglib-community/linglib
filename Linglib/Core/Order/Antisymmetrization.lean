module

public import Mathlib.Order.Antisymmetrization

/-!
# The asymmetric part of a relation  `[UPSTREAM]`

The asymmetric part of a relation `r` holds of `a` and `b` when `r a b` holds and `r b a` does
not. It is the strict counterpart of mathlib's `AntisymmRel`, the symmetric part, and on a preorder
it is `<`. Social choice reads it as strict preference when `r` is weak preference.

Upstream home: `Mathlib/Order/Antisymmetrization.lean`, beside `AntisymmRel`.

## Main definitions

* `AsymmRel`: the asymmetric part of a relation.
-/

@[expose] public section

/-- The asymmetric part of a relation holds of `a` and `b` when `r a b` and not `r b a`. Mathlib's
`AntisymmRel r` is the symmetric part. -/
def AsymmRel {α : Type*} (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {α : Type*} (r : α → α → Prop) [DecidableRel r] (a b : α) :
    Decidable (AsymmRel r a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem AsymmRel.trans_le {α : Type*} {r : α → α → Prop} [IsTrans α r] {a b c : α}
    (h : AsymmRel r a b) (h' : r b c) : AsymmRel r a c :=
  ⟨IsTrans.trans _ _ _ h.1 h', fun hca ↦ h.2 (IsTrans.trans _ _ _ h' hca)⟩

theorem asymmRel_of_rel_of_asymmRel {α : Type*} {r : α → α → Prop} [IsTrans α r] {a b c : α}
    (h : r a b) (h' : AsymmRel r b c) : AsymmRel r a c :=
  ⟨IsTrans.trans _ _ _ h h'.1, fun hca ↦ h'.2 (IsTrans.trans _ _ _ hca h)⟩
