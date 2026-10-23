module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Data.Finset.Union
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Harmonic Serialism
[mccarthy-2000] [mccarthy-2010] [pruitt-2023] [lamont-2022a] [lamont-2022b]

Harmonic Serialism: iterate a one-step `gen` and a durable constraint ranking to a
fixed point. `HSDerivation` bundles the two; the serial search itself is `iterateGen`,
`Function.iterate` of a one-round map `hsStep` on `Option C` whose fixed points are
exactly convergence and failure — durability of both is mathlib's `IsFixedPt.iterate`;
the `Nat` fuel and the `pick` tie-breaker make a possibly-non-terminating,
possibly-tied search total and computable. One-step EVAL
reuses the parallel `Tableau` machinery; directional EVAL ([lamont-2022b];
[eisner-2000]) needs nothing extra — a directional constraint like `*FLOAT^→` is a
position-indexed scalar block (`Tone.starFloatBlock`) spliced into the ranking under
the canonical lex order.

## Main definitions

* `hsStep` / `iterateGen`: one total round of the search (convergence and failure are
  its fixed points), and its `n`-fold `Function.iterate`.
* `HSDerivation`: a one-step `gen` with a durable ranking; `stepOptimum` is one
  GEN/EVAL round, `Converged` the halting condition, `derive` the bundled search.

## Main results

* `iterateGen_eventually_constant`: under a well-founded harmony order that every
  genuine step descends, the search is eventually constant — derivations cannot loop
  while each step makes measurable progress, so the fuel bound is harmless.
* `isFixedPt_singleton_iff_converged`: `Converged` is `Function.IsFixedPt` of the
  powerset step at the singleton.
* `converged_of_singleton_gen`: GEN-restriction to the faithful candidate forces
  convergence.

## Theoretical scope

Per [pruitt-2023] (Table 1), HS does **not** solve counterfeeding underapplication and
only patches counterbleeding with extra GEN assumptions; this file makes no
"serial OT solves opacity" claim. [mcpherson-lamont-2026] is the motivating positive
case for the directional variant. Architecturally distinct alternatives in linglib:
`Phonology/Subregular/LocalRewrite.lean` (extrinsic rule ordering) and
`Phonology/OptimalityTheory/Stratal.lean` (cyclic ranking). HS and Stratal OT are
sister specializations of parallel OT, not nested: HS holds the ranking constant and
iterates the candidate; Stratal OT varies the ranking and chains the candidate
(Stratal HS, combining both axes, is deferred — cf. [pruitt-2023] §2.4).
-/

@[expose] public section

namespace OptimalityTheory

/-! ### The serial search -/

/-- Lift a relation to `Option`, with `none` a bottom below every `some`: the
well-founded carrier for the search orbit, where failure counts as a final descent. -/
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

/-- One total round of the serial search: a converged form (`step c = {c}`) returns
itself, any other advances by `pick`ing from the step's output (a canonical sort +
`head?`, or a directional tie-breaker), and failure — an empty pick, or an already
failed search — is `none`. Convergence and failure are both fixed points, so the
`n`-round search is literally `Function.iterate` of this map. -/
def hsStep (step : C → Finset C) (pick : Finset C → Option C) (oc : Option C) : Option C :=
  oc.bind fun c => if step c = {c} then some c else pick (step c)

/-- The `n`-round search from `c`: iterate `hsStep`. The `Nat` fuel makes the search
total — HS need not converge ([lamont-2022b]). -/
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

/-- **HS terminates under a well-founded harmony order.** If every genuine step
descends a well-founded `lt` (`sound`), the search is eventually constant: some `N`
past which further fuel doesn't change the result. Derivations cannot loop while each
step makes measurable progress, so the explicit `Nat` bound is harmless: the orbit cannot
descend the harmony order lifted to `Option` forever, so some iterate is a fixed point. -/
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

/-- A Harmonic Serialism derivation: a one-step candidate-generation function (per
[mccarthy-2008b]'s restricted GEN) and a durable ranking. The inner `Tableau` width is
`ranking.length`. -/
structure HSDerivation (C : Type*) [DecidableEq C] where
  /-- The one-step candidate-generation function. -/
  gen : C → Finset C
  /-- The constraint ranking, durable across rounds (head = highest). -/
  ranking : List (OptimalityTheory.Constraint C)

namespace HSDerivation

variable {C : Type*} [DecidableEq C] (D : HSDerivation C) (c : C)

/-- The optimal set of one GEN/EVAL round: the winners of the tableau of `gen c` under the
durable ranking. -/
def stepOptimum : Finset C := (Tableau.ofList (D.gen c) D.ranking).optimal

@[simp] theorem stepOptimum_of_empty_gen (h : D.gen c = ∅) : D.stepOptimum c = ∅ := by
  simp [stepOptimum, Tableau.optimal, h]

/-! ### Convergence -/

/-- A form has **converged** iff its one-round optimal set is the singleton of the
faithful candidate — the canonical HS halting condition ([mccarthy-2010]). -/
def Converged : Prop := D.stepOptimum c = ({c} : Finset C)

instance : Decidable (D.Converged c) := decEq (D.stepOptimum c) ({c} : Finset C)

/-- `Converged` is `Function.IsFixedPt` of the powerset step
`s ↦ ⋃ x ∈ s, stepOptimum x` at the singleton `{c}` — by `Finset.singleton_biUnion`,
with no intermediate combinator. Simp-normalized toward `Converged`. -/
@[simp] theorem isFixedPt_singleton_iff_converged :
    Function.IsFixedPt (fun s => s.biUnion D.stepOptimum) ({c} : Finset C)
      ↔ D.Converged c := by
  simp [Converged, Function.IsFixedPt, Finset.singleton_biUnion]

/-- GEN-restriction to the faithful candidate forces convergence. -/
theorem converged_of_singleton_gen (h : D.gen c = ({c} : Finset C)) : D.Converged c :=
  Tableau.optimal_singleton h

/-- An `n`-round HS derivation: `iterateGen` over `stepOptimum` with a caller-supplied
`pick` tie-breaker for non-singleton optima (ties not yet broken by directional eval,
or genuinely divergent ties in the [pruitt-2009] sense). -/
def derive (pick : Finset C → Option C) (steps : Nat) : Option C :=
  iterateGen D.stepOptimum pick steps c

end HSDerivation

end OptimalityTheory
