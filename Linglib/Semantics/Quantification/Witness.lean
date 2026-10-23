module

public import Linglib.Semantics.Quantification.Defs
public import Mathlib.Order.Minimal

/-!
# Witness sets

A witness set for a type ⟨1⟩ quantifier `Q` living on `A` is a subset of `A` that `Q` holds of
(§4.9 of Barwise and Cooper). Such a quantifier holds of `X` exactly when `A ∩ X` is a witness
set. Witness sets characterise the monotone quantifiers: an increasing quantifier holds of `X`
iff `X` contains one of its witness sets, and a decreasing quantifier holds of `X` iff `X ∩ A`
is contained in one (C11). Living on `A` already confines the minimal sets in `Q` to `A`, so the
minimal witness sets are exactly the minimal sets in the quantifier.

## Main definitions

* `Quantifier.NP.Witness Q A w`: `w ⊆ A` and `Q w`.

## Main statements

* `Quantifier.NP.LivesOn.apply_iff_witness`: a quantifier living on `A` holds of `X` iff
  `A ∩ X` is a witness set.
* `Quantifier.NP.LivesOn.monotone_apply_iff`, `Quantifier.NP.LivesOn.antitone_apply_iff`: C11
  for increasing and decreasing quantifiers.
* `Quantifier.NP.LivesOn.minimal_witness_iff`: the minimal witness sets of a quantifier living
  on `A` are its minimal sets.

## Implementation notes

Witness sets are predicates, like the arguments of an `NP`; a study over a finite domain states a
`Finset` witness `X` as `(· ∈ X)`.

## References

* [J. Barwise, R. Cooper, *Generalized Quantifiers and Natural Language*
  (1981)][barwise-cooper-1981]
-/

@[expose] public section

namespace Quantifier.NP

variable {α : Type*} {Q : NP α} {A X w : α → Prop}

/-- A witness set for a quantifier living on `A` is a subset of `A` in the quantifier
([barwise-cooper-1981] §4.9). -/
def Witness (Q : NP α) (A w : α → Prop) : Prop := (∀ x, w x → A x) ∧ Q w

/-- A quantifier living on `A` holds of `X` iff `A ∩ X` is a witness set, whatever its
monotonicity. -/
theorem LivesOn.apply_iff_witness (h : LivesOn Q A) : Q X ↔ Witness Q A fun x ↦ A x ∧ X x :=
  ⟨fun hX ↦ ⟨fun _ ↦ And.left, (h X).1 hX⟩, fun hw ↦ (h X).2 hw.2⟩

/-- C11(i) says that an increasing quantifier living on `A` holds of `X` iff some witness set
is contained in `X`. -/
theorem LivesOn.monotone_apply_iff (h : LivesOn Q A) (hm : Monotone Q) :
    Q X ↔ ∃ w, Witness Q A w ∧ ∀ x, w x → X x :=
  ⟨fun hX ↦ ⟨_, h.apply_iff_witness.1 hX, fun _ ↦ And.right⟩, fun ⟨_, hw, hwX⟩ ↦ hm hwX hw.2⟩

/-- C11(ii) says that a decreasing quantifier living on `A` holds of `X` iff `X ∩ A` is
contained in some witness set. -/
theorem LivesOn.antitone_apply_iff (h : LivesOn Q A) (hm : Antitone Q) :
    Q X ↔ ∃ w, Witness Q A w ∧ ∀ x, X x ∧ A x → w x :=
  ⟨fun hX ↦ ⟨_, h.apply_iff_witness.1 hX, fun _ ↦ And.symm⟩,
    fun ⟨_, hw, hXw⟩ ↦ (h X).2 (hm (fun x hx ↦ hXw x hx.symm) hw.2)⟩

/-- The minimal witness sets of a quantifier living on `A` are its minimal sets, since a
minimal set in `Q` lies inside `A`, `Q` holding also of its intersection with `A`. -/
theorem LivesOn.minimal_witness_iff (h : LivesOn Q A) :
    Minimal (Witness Q A) w ↔ Minimal Q w :=
  ⟨fun hm ↦ ⟨hm.1.2, fun _ hy hyw ↦ hm.2 ⟨fun x hx ↦ hm.1.1 x (hyw x hx), hy⟩ hyw⟩,
    fun hm ↦
      have hle : w ≤ fun x ↦ A x ∧ w x := hm.2 ((h w).1 hm.1) fun _ hx ↦ hx.2
      ⟨⟨fun x hx ↦ (hle x hx).1, hm.1⟩, fun _ hy hyw ↦ hm.2 hy.2 hyw⟩⟩

end Quantifier.NP
