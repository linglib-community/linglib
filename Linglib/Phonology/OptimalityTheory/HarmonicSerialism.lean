module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Filtration
public import Mathlib.Data.Finset.Union
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Harmonic Serialism

This file defines a [Harmonic Serialism derivation](##HSDerivation), which applies GEN and EVAL
repeatedly under a fixed ranking and [converges](##HSDerivation.Converged) once the current form is
the only winner of its own round. One round is a [total map on `Option C`](##hsStep) that fixes
both convergence and failure, and a derivation is [its iterate](##iterateGen), computable once the
number of rounds is bounded and a choice among tied winners is given. [If every step that changes
the form descends a well-founded relation, the iterate is eventually
constant](##iterateGen_eventually_constant), and the bound does not affect the result.

## Implementation notes

Each round is evaluated by the parallel `Constraint.eval`, and a directional constraint is a
`Constraint.directionalBlock` spliced into the ranking. Counterfeeding opacity, which Pruitt argues
Harmonic Serialism cannot straightforwardly derive, and the combination with Stratal Optimality
Theory, which changes the ranking between strata, are not formalized.

## References

* [mccarthy-2000]
* [mccarthy-2008b]
* [mccarthy-2010]
* [eisner-2000]
* [lamont-2022a]
* [lamont-2022b]
* [pruitt-2009]
* [pruitt-2023]
* [mcpherson-lamont-2026]
-/

@[expose] public section

namespace OptimalityTheory

/-! ### The serial search -/

/-- The extension of a relation to `Option` that places `none` below every `some`, so that failure
counts as a final descent. -/
private def optionRel {C : Type*} (lt : C → C → Prop) : Option C → Option C → Prop
  | _, none => False
  | none, some _ => True
  | some a, some b => lt a b

private theorem optionRel_wf {C : Type*} {lt : C → C → Prop} (wf : WellFounded lt) :
    WellFounded (optionRel lt) := by
  have hnone : Acc (optionRel lt) none := Acc.intro _ fun _ hy => hy.elim
  refine ⟨fun o => ?_⟩
  cases o with
  | none => exact hnone
  | some a =>
    induction a using wf.induction with
    | _ a IH =>
      refine Acc.intro _ fun o' ho' => ?_
      match o', ho' with
      | none, _ => exact hnone
      | some a', h => exact IH a' h

section Iteration

variable {C : Type*} [DecidableEq C]

/-- One round of the serial search. A form that is the only output of its step is returned
unchanged, any other form is replaced by the candidate that `pick` chooses from its step, and an
empty choice or an earlier failure gives `none`. -/
def hsStep (step : C → Finset C) (pick : Finset C → Option C) (oc : Option C) : Option C :=
  oc.bind fun c => if step c = {c} then some c else pick (step c)

/-- The search from `c` run for `n` rounds. Bounding the number of rounds makes the search total,
since a derivation need not converge ([lamont-2022b], p. 55). -/
def iterateGen (step : C → Finset C) (pick : Finset C → Option C) (n : Nat) (c : C) : Option C :=
  (hsStep step pick)^[n] (some c)

variable {step : C → Finset C} {pick : Finset C → Option C} {c c' : C} (n : Nat)

@[simp] theorem hsStep_none : hsStep step pick none = none := rfl

@[simp] theorem hsStep_some :
    hsStep step pick (some c) = if step c = {c} then some c else pick (step c) := rfl

@[simp] theorem iterateGen_zero : iterateGen step pick 0 c = some c := rfl

theorem isFixedPt_hsStep_of_converged (h : step c = {c}) :
    Function.IsFixedPt (hsStep step pick) (some c) := by
  simp [Function.IsFixedPt, h]

theorem isFixedPt_hsStep_none : Function.IsFixedPt (hsStep step pick) none := rfl

theorem iterateGen_const_of_converged (h : step c = {c}) :
    iterateGen step pick n c = some c :=
  Function.IsFixedPt.iterate (isFixedPt_hsStep_of_converged h) n

variable (hcv : step c ≠ {c})

include hcv in
theorem iterateGen_succ_of_step (hpick : pick (step c) = some c') :
    iterateGen step pick (n + 1) c = iterateGen step pick n c' := by
  rw [iterateGen, Function.iterate_succ_apply, hsStep_some, ite_eq_right hcv, hpick]; rfl

include hcv in
theorem iterateGen_of_pickFail (hpick : pick (step c) = none) :
    iterateGen step pick (n + 1) c = none := by
  rw [iterateGen, Function.iterate_succ_apply, hsStep_some, ite_eq_right hcv, hpick]
  exact Function.IsFixedPt.iterate isFixedPt_hsStep_none n

private theorem hsStep_descends {lt : C → C → Prop}
    (sound : ∀ c c', step c ≠ {c} → pick (step c) = some c' → c' ≠ c → lt c' c)
    (oc : Option C) (hne : hsStep step pick oc ≠ oc) :
    optionRel lt (hsStep step pick oc) oc := by
  match oc with
  | none => exact absurd rfl hne
  | some a =>
    rw [hsStep_some] at hne ⊢
    by_cases hcv : step a = {a}
    · rw [ite_eq_left hcv] at hne
      exact absurd rfl hne
    · rw [ite_eq_right hcv] at hne ⊢
      match hp : pick (step a) with
      | none => exact trivial
      | some a' =>
        rw [hp] at hne
        exact sound a a' hcv hp fun he => hne (congrArg some he)

/-- If every step that changes the form descends a well-founded relation, the search is eventually
constant in the number of rounds. -/
theorem iterateGen_eventually_constant {lt : C → C → Prop} (wf : WellFounded lt)
    (sound : ∀ c c', step c ≠ {c} → pick (step c) = some c' → c' ≠ c → lt c' c)
    (c : C) :
    ∃ N, ∀ m, N ≤ m → iterateGen step pick m c = iterateGen step pick N c := by
  obtain ⟨N, hN⟩ := WellFounded.not_rel_apply_succ (h := optionRel_wf wf)
    fun n ↦ iterateGen step pick n c
  have hfix : Function.IsFixedPt (hsStep step pick) (iterateGen step pick N c) := by_contra fun h ↦
    hN <| by rw [iterateGen, Function.iterate_succ_apply']; exact hsStep_descends sound _ h
  refine ⟨N, fun m hm ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [iterateGen, add_comm, Function.iterate_add_apply]
  exact hfix.iterate k

end Iteration

/-! ### HS derivations -/

/-- A Harmonic Serialism derivation consists of a candidate generator for one step, the restricted
GEN of [mccarthy-2008b], and a ranking that is fixed across rounds. -/
structure HSDerivation (C : Type*) [DecidableEq C] where
  /-- The one-step candidate-generation function. -/
  gen : C → Finset C
  /-- The constraint ranking, most dominant first. -/
  ranking : List (OptimalityTheory.Constraint C)

namespace HSDerivation

variable {C : Type*} [DecidableEq C] (D : HSDerivation C) (c : C)

/-- The optimal candidates of one round, the candidates of `gen c` that the ranking selects. -/
def stepOptimum : Finset C := Constraint.eval (D.gen c) D.ranking

@[simp] theorem stepOptimum_of_empty_gen (h : D.gen c = ∅) : D.stepOptimum c = ∅ := by
  exact Finset.subset_empty.1 (h ▸ Constraint.eval_subset)

/-! ### Convergence -/

/-- A form has converged when it is the only optimal candidate of its round ([mccarthy-2010]). -/
def Converged : Prop := D.stepOptimum c = ({c} : Finset C)

instance : Decidable (D.Converged c) := decEq (D.stepOptimum c) ({c} : Finset C)

/-- A form has converged iff its singleton is a fixed point of the round on sets of forms. -/
@[simp] theorem isFixedPt_singleton_iff_converged :
    Function.IsFixedPt (fun s => s.biUnion D.stepOptimum) ({c} : Finset C)
      ↔ D.Converged c := by
  simp [Converged, Function.IsFixedPt, Finset.singleton_biUnion]

/-- A form whose only candidate is itself has converged. -/
theorem converged_of_singleton_gen (h : D.gen c = ({c} : Finset C)) : D.Converged c := by
  rw [Converged, stepOptimum, h, Constraint.eval_singleton]

/-- The derivation from `c` run for `steps` rounds, with `pick` choosing among tied optimal
candidates, including the divergent ties of [pruitt-2009]. -/
def derive (pick : Finset C → Option C) (steps : Nat) : Option C :=
  iterateGen D.stepOptimum pick steps c

end HSDerivation

end OptimalityTheory
