/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Logic.Trivalent.Propositional
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Pi

/-!
# Strong Kleene logic as supervaluation

A trivalent value is the supervaluation of its two bivalent readings, true where it is `1` and
true where it is not `-1`, its designation at K3 and at LP. Reading each occurrence of an atom at
a standard of its own, independently of its other occurrences, gives the bivalent variants of a
formula, and the Strong Kleene value of the formula is the supervaluation of its bivalent
variants. The same holds of the Strong Kleene quantifiers, each instance read at its own
standard. Spector states the propositional case and uses it to read an occurrence of
presuppositional exhaustification as underspecified between a parse with an exhaustivity operator
and one without.

Uniform supervaluation, which reads every occurrence of an atom at the same standard, is not
Strong Kleene: `p ∨ ¬p` is supertrue where `p` is `0`, and Strong Kleene leaves it undefined.

## Main definitions

* `Trivalent.Formula.bivalentVariants`: the formulas over atoms paired with standards that read
  each occurrence of an atom at a standard.

## Main results

* `SignType.supervaluation_product_and`, `SignType.supervaluation_product_or`: over a product of
  families, supervaluation takes independent conjunctions and disjunctions to `⊓` and `⊔`.
* `Trivalent.Formula.eval_strongKleene_eq_supervaluation`: the Strong Kleene value of a formula
  is the supervaluation of its bivalent variants.
* `Trivalent.forallStrong_eq_supervaluation`, `Trivalent.existsStrong_eq_supervaluation`: the
  Strong Kleene quantifiers are supervaluations over the readings of their instances.

## References

* [spector-2025]
* [kleene-1952]
* [van-fraassen-1966]
-/

@[expose] public section

namespace SignType

variable {α β ι : Type*} {s : Finset α} {t : Finset β} (P : α → Prop) [DecidablePred P]
  (Q : β → Prop) [DecidablePred Q]

/-- Over a product of nonempty families, the supervaluation of independent conditions on the two
coordinates, conjoined, is the Strong Kleene conjunction of their supervaluations. -/
theorem supervaluation_product_and (hs : s.Nonempty) (ht : t.Nonempty) :
    supervaluation (s ×ˢ t) (fun x ↦ P x.1 ∧ Q x.2) = supervaluation s P ⊓ supervaluation t Q := by
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · simp only [supervaluation_eq_one_iff, inf_eq_one_iff, Finset.mem_product, and_imp,
      Prod.forall]
    obtain ⟨a₀, ha₀⟩ := hs
    obtain ⟨b₀, hb₀⟩ := ht
    exact ⟨fun h ↦ ⟨fun a ha ↦ (h a b₀ ha hb₀).1, fun b hb ↦ (h a₀ b ha₀ hb).2⟩,
      fun h a b ha hb ↦ ⟨h.1 a ha, h.2 b hb⟩⟩
  · simp only [supervaluation_eq_neg_one_iff, inf_eq_neg_one_iff, hs, ht, hs.product ht,
      true_and, Finset.mem_product, and_imp, Prod.forall, not_and]
    refine ⟨fun h ↦ ?_, ?_⟩
    · by_contra! hc
      obtain ⟨⟨a, ha, hPa⟩, b, hb, hQb⟩ := hc
      exact h a b ha hb hPa hQb
    · rintro (h | h) a b ha hb hP hQ
      exacts [h a ha hP, h b hb hQ]

/-- Over a product of nonempty families, the supervaluation of independent conditions on the two
coordinates, disjoined, is the Strong Kleene disjunction of their supervaluations. -/
theorem supervaluation_product_or (hs : s.Nonempty) (ht : t.Nonempty) :
    supervaluation (s ×ˢ t) (fun x ↦ P x.1 ∨ Q x.2) = supervaluation s P ⊔ supervaluation t Q := by
  rw [← neg_neg (supervaluation s P ⊔ _), SignType.neg_sup, ← supervaluation_not _ hs,
    ← supervaluation_not _ ht, ← supervaluation_product_and _ _ hs ht,
    ← supervaluation_not _ (hs.product ht)]
  exact supervaluation_congr fun _ _ ↦ by tauto

variable [Fintype ι] [DecidableEq ι] {S : ι → Finset α} (R : ι → α → Prop)
  [∀ i, DecidablePred (R i)]

/-- Over the choice functions of nonempty families, the supervaluation of independent conditions
on the choices, all holding, is the Strong Kleene universal over their supervaluations. -/
theorem supervaluation_piFinset_forall (hS : ∀ i, (S i).Nonempty) :
    supervaluation (Fintype.piFinset S) (fun c ↦ ∀ i, R i (c i)) =
      Trivalent.forallStrong fun i ↦ supervaluation (S i) (R i) := by
  choose c₀ hc₀ using hS
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · simp only [supervaluation_eq_one_iff, Trivalent.forallStrong_eq_one_iff,
      Fintype.mem_piFinset]
    refine ⟨fun h i a ha ↦ ?_, fun h c hc i ↦ h i (c i) (hc i)⟩
    simpa using h (Function.update c₀ i a) (fun j ↦ by
      rcases eq_or_ne j i with rfl | hj <;> simp [*]) i
  · simp only [supervaluation_eq_neg_one_iff, Trivalent.forallStrong_eq_neg_one_iff,
      Fintype.mem_piFinset, Fintype.piFinset_nonempty, not_forall]
    refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨i, hi, h⟩ ↦ ⟨fun j ↦ ⟨c₀ j, hc₀ j⟩, fun c hc ↦ ⟨i, h _ (hc i)⟩⟩⟩
    by_contra! hc
    choose c hcS hcR using fun i ↦ hc i ⟨c₀ i, hc₀ i⟩
    obtain ⟨i, hi⟩ := h c hcS
    exact hi (hcR i)

/-- Over the choice functions of nonempty families, the supervaluation of independent conditions
on the choices, one holding, is the Strong Kleene existential over their supervaluations. -/
theorem supervaluation_piFinset_exists (hS : ∀ i, (S i).Nonempty) :
    supervaluation (Fintype.piFinset S) (fun c ↦ ∃ i, R i (c i)) =
      Trivalent.existsStrong fun i ↦ supervaluation (S i) (R i) := by
  have h : (fun i ↦ supervaluation (S i) (R i)) = fun i ↦ -supervaluation (S i) (¬R i ·) :=
    funext fun i ↦ by rw [supervaluation_not _ (hS i), neg_neg]
  rw [h, ← Trivalent.neg_forallStrong, ← supervaluation_piFinset_forall _ hS,
    ← supervaluation_not _ (Fintype.piFinset_nonempty.2 hS)]
  exact supervaluation_congr fun _ _ ↦ by simp [not_forall_not]

end SignType

namespace Trivalent

open SignType

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Strong Kleene universal is the supervaluation over the readings of its instances, each
at a standard of its own. -/
theorem forallStrong_eq_supervaluation (p : ι → SignType) :
    forallStrong p = supervaluation Finset.univ fun c : ι → Designation ↦
      ∀ i, (c i).threshold ≤ p i := by
  simpa using (supervaluation_piFinset_forall (S := fun _ ↦ Finset.univ)
    (fun i (d : Designation) ↦ d.threshold ≤ p i) fun _ ↦ Finset.univ_nonempty).symm

/-- The Strong Kleene existential is the supervaluation over the readings of its instances, each
at a standard of its own. -/
theorem existsStrong_eq_supervaluation (p : ι → SignType) :
    existsStrong p = supervaluation Finset.univ fun c : ι → Designation ↦
      ∃ i, (c i).threshold ≤ p i := by
  simpa using (supervaluation_piFinset_exists (S := fun _ ↦ Finset.univ)
    (fun i (d : Designation) ↦ d.threshold ≤ p i) fun _ ↦ Finset.univ_nonempty).symm

namespace Formula

variable {Atom : Type*} [DecidableEq Atom]

/-- The bivalent variants of a formula ([spector-2025]) read each occurrence of an atom at a
standard, independently of its other occurrences. -/
def bivalentVariants : Formula Atom → Finset (Formula (Atom × Designation))
  | atom a => Finset.univ.image fun d ↦ atom (a, d)
  | neg φ => φ.bivalentVariants.image neg
  | conj φ ψ => Finset.image₂ conj φ.bivalentVariants ψ.bivalentVariants
  | disj φ ψ => Finset.image₂ disj φ.bivalentVariants ψ.bivalentVariants
  | cond φ ψ => Finset.image₂ cond φ.bivalentVariants ψ.bivalentVariants

theorem bivalentVariants_nonempty (φ : Formula Atom) : φ.bivalentVariants.Nonempty := by
  induction φ with
  | atom => exact Finset.univ_nonempty.image _
  | neg _ ih => exact ih.image _
  | conj _ _ ihφ ihψ | disj _ _ ihφ ihψ | cond _ _ ihφ ihψ => exact ihφ.image₂ ihψ

/-- The Strong Kleene value of a formula is the supervaluation of its bivalent variants, each
occurrence of an atom designated at its standard ([spector-2025], §5). -/
theorem eval_strongKleene_eq_supervaluation (M : Model Atom) (φ : Formula Atom) :
    eval .strongKleene M φ = supervaluation φ.bivalentVariants
      fun ψ ↦ evalBool (fun x ↦ decide (x.2.threshold ≤ M x.1)) ψ = true := by
  induction φ with
  | atom a =>
    simp only [bivalentVariants, supervaluation_image]
    exact (supervaluation_threshold_le (M a)).symm.trans (supervaluation_congr fun _ _ ↦ by simp)
  | neg φ ih =>
    rw [eval_neg, ih, ← supervaluation_not _ φ.bivalentVariants_nonempty]
    simp only [bivalentVariants, supervaluation_image]
    exact supervaluation_congr fun _ _ ↦ by simp
  | conj φ ψ ihφ ihψ =>
    simp only [eval_conj, Connectives.strongKleene_conj, ihφ, ihψ]
    rw [← supervaluation_product_and _ _ φ.bivalentVariants_nonempty ψ.bivalentVariants_nonempty]
    simp only [bivalentVariants, ← Finset.image_uncurry_product, supervaluation_image]
    exact supervaluation_congr fun _ _ ↦ by simp [Function.uncurry_def]
  | disj φ ψ ihφ ihψ =>
    simp only [eval_disj, Connectives.strongKleene_disj, ihφ, ihψ]
    rw [← supervaluation_product_or _ _ φ.bivalentVariants_nonempty ψ.bivalentVariants_nonempty]
    simp only [bivalentVariants, ← Finset.image_uncurry_product, supervaluation_image]
    exact supervaluation_congr fun _ _ ↦ by simp [Function.uncurry_def]
  | cond φ ψ ihφ ihψ =>
    simp only [eval_cond, Connectives.strongKleene_cond, ihφ, ihψ]
    rw [← supervaluation_not _ φ.bivalentVariants_nonempty,
      ← supervaluation_product_or _ _ φ.bivalentVariants_nonempty ψ.bivalentVariants_nonempty]
    simp only [bivalentVariants, ← Finset.image_uncurry_product, supervaluation_image]
    exact supervaluation_congr fun _ _ ↦ by simp [Function.uncurry_def]

end Formula

end Trivalent
