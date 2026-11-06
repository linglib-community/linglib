module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Presupposition.Strawson

/-!
# Superlatives

Heim's absolute superlative holds of `x` when it is in the comparison class and measures above every
other member. Von Fintel makes membership a presupposition: `trivalentSuperlative` is a trivalent
proposition, so that the presupposition rather than the assertion fails when the class shrinks below
`x`, and at a world it is [true exactly of the absolute
superlative](##trivalentSuperlative_eq_true_iff_absoluteSuperlative). The assertion is [the
set-standard comparative over the other members](##trivalentSuperlative_assertion_iff), so [it is
anti-additive in the class](##isAntiAdditive_trivalentSuperlative_assertion), by Hoeksema's
anti-additivity of the set comparative.

## Implementation notes

The comparison class is given at each world, `C : W → Set α`, the transpose of von Fintel's
world-dependent predicate. The degree measure `μ` does not vary with the world; von Fintel's
`ιd P(x)(d)` measures at the world of evaluation.

## References

* [von-fintel-1999]
* [heim-1999]
* [hoeksema-1983]
* [bobaljik-2012]
-/

@[expose] public section

open Set

variable {α D W : Type*}

/-! ### The absolute superlative

*-est* universally quantifies the comparative over a comparison class ([heim-1999]), the
semantic reflex of [bobaljik-2012]'s containment `[[[ADJ] CMPR] SPRL]`. -/

section Absolute
variable [LinearOrder D] {μ : α → D} {C : Set α} {x y : α}

/-- The absolute superlative holds of `x` when `x` is in the comparison class `C` and beats every
other member on the comparative. -/
def AbsoluteSuperlative (μ : α → D) (C : Set α) (x : α) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → μ y < μ x

theorem absoluteSuperlative_unique (hx : AbsoluteSuperlative μ C x)
    (hy : AbsoluteSuperlative μ C y) : x = y :=
  by_contra fun hne ↦ lt_asymm (hx.2 y hy.1 (Ne.symm hne)) (hy.2 x hx.1 hne)

theorem absoluteSuperlative_isGreatest (h : AbsoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) :=
  ⟨mem_image_of_mem μ h.1, forall_mem_image.2 fun y hy ↦
    (eq_or_ne y x).elim (fun e ↦ e ▸ le_rfl) fun hne ↦ (h.2 y hy hne).le⟩

end Absolute

/-! ### The presuppositional superlative -/

section Preorder

variable [Preorder D]

open Classical in
/-- *x is the μ-est of C* presupposes that `x` is in the comparison class and asserts that it
measures above every other member of the class ([von-fintel-1999]'s (79)). -/
noncomputable def trivalentSuperlative (μ : α → D) (C : W → Set α) (x : α) : W → Trivalent :=
  fun w ↦ Trivalent.transplication (Trivalent.ofProp (x ∈ C w))
    (Trivalent.ofProp (∀ y ∈ C w, y ≠ x → μ y < μ x))

variable {μ : α → D} {C : W → Set α} {x : α} {w : W}

@[simp] theorem trivalentSuperlative_eq_undefined_iff :
    trivalentSuperlative μ C x w = .undefined ↔ x ∉ C w := by
  simp [trivalentSuperlative]

@[simp] theorem trivalentSuperlative_eq_true_iff :
    trivalentSuperlative μ C x w = .true ↔ x ∈ C w ∧ ∀ y ∈ C w, y ≠ x → μ y < μ x := by
  simp [trivalentSuperlative]

/-- The assertion is the set-standard comparative of `x` against the degrees of the other
members of the class. -/
theorem trivalentSuperlative_assertion_iff {s : Set α} :
    (∀ y ∈ s, y ≠ x → μ y < μ x) ↔ x ∈ μ ⁻¹' strictUpperBounds (μ '' (s \ {x})) := by
  simp only [mem_gtOverSet_iff_subset_Iio, subset_def, mem_Iio, forall_mem_image, mem_sdiff,
    mem_singleton_iff, and_imp]

/-- The assertion is anti-additive in the comparison class, by the anti-additivity of the
set-standard comparative ([hoeksema-1983]). -/
theorem isAntiAdditive_trivalentSuperlative_assertion (μ : α → D) (x : α) :
    IsAntiAdditive fun (C : W → Set α) (w : W) ↦ ∀ y ∈ C w, y ≠ x → μ y < μ x :=
  fun C C' ↦ funext fun w ↦ propext <| by
    simp only [Pi.inf_apply, inf_Prop_eq, trivalentSuperlative_assertion_iff, Pi.sup_apply,
      sup_eq_union,
      union_sdiff_distrib, image_union]
    have h := gtOverSet_isAntiAdditive μ (μ '' (C w \ {x})) (μ '' (C' w \ {x}))
    beta_reduce at h
    rw [show μ '' (C w \ {x}) ∪ μ '' (C' w \ {x}) = _ ⊔ _ from rfl, h]
    exact Iff.rfl

end Preorder

/-- At a world the superlative is true exactly when `x` is the absolute superlative of the class
there ([heim-1999]). -/
theorem trivalentSuperlative_eq_true_iff_absoluteSuperlative [LinearOrder D] {μ : α → D}
    {C : W → Set α}
    {x : α} {w : W} : trivalentSuperlative μ C x w = .true ↔ AbsoluteSuperlative μ (C w) x :=
  trivalentSuperlative_eq_true_iff

open Presupposition Trivalent

variable [Preorder D] (μ : α → D) (x : α)

/-- The superlative is Strawson anti-additive in its comparison class. -/
theorem isStrawsonAntiAdditive_trivalentSuperlative :
    IsStrawsonAntiAdditive (trivalentSuperlative (W := W) μ · x) :=
  .of_isAntiAdditive (isAntiAdditive_trivalentSuperlative_assertion μ x) fun _ _ h ↦ by simp_all

theorem isStrawsonDE_trivalentSuperlative : IsStrawsonDE (trivalentSuperlative (W := W) μ · x) :=
  (isStrawsonAntiAdditive_trivalentSuperlative μ x).isStrawsonDE

/-- *Emma is the tallest girl in her class* does not classically entail its restriction to girls who
have learned the alphabet ([von-fintel-1999]'s (76)). -/
theorem not_antitone_posExt_trivalentSuperlative :
    ¬ Antitone fun C : Unit → Set Unit ↦
      Trivalent.posExt (trivalentSuperlative (fun _ : Unit ↦ (0 : ℕ)) C ()) :=
  not_antitone_posExt (p := ⊥) (q := fun _ ↦ .univ) (w := ()) bot_le (by simp) (by simp)

/-- *Emma is the tallest girl to have learned the alphabet* does not Strawson-entail *Emma is the
tallest girl*, defined and false when a taller girl has not learned it. -/
theorem not_isStrawsonUE_trivalentSuperlative :
    ¬ IsStrawsonUE (trivalentSuperlative (W := Unit) (fun _ : Bool ↦ (0 : ℕ)) · Bool.true) :=
  not_isStrawsonUE (p := fun _ ↦ {Bool.true}) (q := fun _ ↦ .univ) (w := ())
    (fun _ ↦ Set.subset_univ _) (by simp) (by simp [trivalentSuperlative])
