module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Presupposition.Strawson

/-!
# The modal-horizon counterfactual

On von Fintel's dynamic strict analysis, a counterfactual quantifies over a modal horizon, a set
of worlds accessible from each evaluation point that the context widens as needed. *If p, would
q* presupposes that the horizon admits `p` and asserts that every `p`-world of the horizon is a
`q`-world, the strict conditional `Conditional.strictImp` over the horizon. Strengthening the
antecedent is then not classically valid, since the strengthened antecedent may fall outside the
horizon, but it is valid wherever the conclusion's presupposition holds.

## Main definitions

* `Conditional.horizonCounterfactual`: the counterfactual over a modal horizon, a trivalent
  proposition.

## Main results

* `Conditional.exists_mem_of_horizonCounterfactual_eq_one`: a true counterfactual has a
  horizon-world where antecedent and consequent hold together.

## Implementation notes

The admissibility of the horizon with respect to an ordering source, a condition on the context
that does not mention the antecedent, is left to the caller. Von Fintel's page prints the
consequent as evaluated at `w`; it is evaluated at the horizon-world `w'`, as here.

## References

* [von-fintel-1999]
* [von-fintel-2000]
-/

@[expose] public section

namespace Conditional

variable {I W : Type*} (horizon : I → Set W) (p q : Set W)

open Classical in
/-- *If p, would q* over a modal horizon presupposes that the horizon admits `p` and asserts the
strict conditional over the horizon ([von-fintel-1999]'s (82) and (83)). -/
noncomputable def horizonCounterfactual : I → SignType :=
  {i | (horizon i ∩ p).Nonempty}.indicator fun i ↦ SignType.ofProp (i ∈ strictImp horizon p q)

variable {horizon p q} {i : I}

@[simp] theorem horizonCounterfactual_eq_zero_iff :
    horizonCounterfactual horizon p q i = 0 ↔ ¬ (horizon i ∩ p).Nonempty := by
  simp [horizonCounterfactual]

@[simp] theorem horizonCounterfactual_eq_one_iff :
    horizonCounterfactual horizon p q i = 1 ↔ (horizon i ∩ p).Nonempty ∧ horizon i ∩ p ⊆ q := by
  simp [horizonCounterfactual]

@[simp] theorem horizonCounterfactual_eq_neg_one_iff :
    horizonCounterfactual horizon p q i = -1 ↔
      (horizon i ∩ p).Nonempty ∧ ¬ horizon i ∩ p ⊆ q := by
  simp [horizonCounterfactual]

/-- A true counterfactual has a horizon-world where its antecedent and consequent hold together. -/
theorem exists_mem_of_horizonCounterfactual_eq_one (h : horizonCounterfactual horizon p q i = 1) :
    ∃ w ∈ horizon i, w ∈ p ∧ w ∈ q :=
  let ⟨⟨w, hw⟩, hs⟩ := horizonCounterfactual_eq_one_iff.1 h
  ⟨w, hw.1, hw.2, hs hw⟩

end Conditional

/-! ### Conditional antecedents -/

namespace Conditional

open Presupposition Trivalent

variable {I W : Type*} (horizon : I → Set W) (q : Set W)

/-- The modal-horizon counterfactual is Strawson anti-additive in its antecedent ([gajewski-2011],
Appendix 1). -/
theorem isStrawsonAntiAdditive_horizonCounterfactual :
    IsStrawsonAntiAdditive (horizonCounterfactual horizon · q) :=
  .of_isAntiAdditive (a := fun p i ↦ i ∈ strictImp horizon p q)
    (fun p p' ↦ funext fun i ↦ propext <| by
      show i ∈ strictImp horizon (p ∪ p') q ↔ i ∈ strictImp horizon p q ∧ i ∈ strictImp horizon p' q
      rw [strictImp_union_left]
      exact Iff.rfl)
    fun _ _ h ↦ by simp_all [mem_strictImp]

theorem isStrawsonDE_horizonCounterfactual :
    IsStrawsonDE (horizonCounterfactual horizon · q) :=
  (isStrawsonAntiAdditive_horizonCounterfactual horizon q).isStrawsonDE

/-- Strengthening the antecedent is not classically valid, since a strengthened antecedent can
fall outside the horizon ([von-fintel-1999], §4.3). -/
theorem not_antitone_posSupport_horizonCounterfactual :
    ¬ Antitone fun p : Set Unit ↦
      posSupport (horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Unit)) p .univ) :=
  not_antitone_posSupport (p := ∅) (q := .univ) (w := ()) (Set.empty_subset _) (by simp) (by simp)

/-- Weakening the antecedent is not Strawson valid either, since the weaker antecedent can admit
worlds the consequent excludes. -/
theorem not_isStrawsonUE_horizonCounterfactual :
    ¬ IsStrawsonUE fun p : Set Bool ↦
      horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Bool)) p {true} :=
  not_isStrawsonUE (p := {true}) (q := .univ) (w := ()) (Set.subset_univ _) (by simp)
    (by simp [Set.subset_def])

end Conditional
