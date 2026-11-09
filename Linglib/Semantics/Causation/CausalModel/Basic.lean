module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Counterfactuals in a causal model

This file develops the logic of interventions in an acyclic causal model. Read as a
counterfactual, the solution under an intervention is the value a variable would have had, had the
intervened variables been held at their values. Galles and Pearl show that these counterfactuals
satisfy composition, effectiveness and reversibility, and that in a recursive model the first two
are complete; all three hold here. A partial assignment also serves as an observation, which picks
out the contexts whose actual world agrees with it; conditioning a counterfactual on evidence
restricts it to them.

## Main definitions

* `CausalModel.world`: the world an intervention brings about, as a partial assignment
* `CausalModel.contexts`: the contexts in which an observation holds

## Main results

* `CausalModel.dependsOn_solve`: the solution at a variable reads only the intervention at its
  ancestors
* `CausalModel.solve_eq_of_le_of_le_world`, `CausalModel.solve_eq_solve_iff_le_world`: composition
  and its converse
* `CausalModel.le_world`: effectiveness
* `CausalModel.solve_eq_of_solve_update_of_solve_update`: reversibility
* `CausalModel.mem_contexts_iff_solve_eq`: consistency and its converse

## Implementation notes

Galles and Pearl state composition for one added variable and derive consistency from it. Here
composition adds any set of variables at once, so the one-variable form and consistency, its case
at the null intervention, are both corollaries.

## References

* [galles-pearl-1998]
-/

@[expose] public section

namespace CausalModel

open Relation

variable {U V : Type*} {α : V → Type*} {M : CausalModel U V α} [∀ v, Nonempty (α v)]
  [hM : M.IsAcyclic]

section Intervention

/-- The solution at a variable reads the intervention only at the variable and its ancestors. -/
theorem dependsOn_solve (u : U) (v : V) :
    DependsOn (M.solve · u v) {w | ReflTransGen M.graph.Adj w v} := fun I J h ↦
  WellFounded.fixedPoint_congr (dependsOn_step I u) (dependsOn_step J u) fun w hw _ ↦ by
    rw [step_apply, step_apply, h w hw]

variable (M) in
/-- `M.world I u` is the world the intervention `I` brings about in the context `u`, its solution
as a partial assignment that settles every variable. `M.world ⊥ u` is the actual world of `u`. -/
noncomputable def world (I : ∀ v, Flat (α v)) (u : U) : ∀ v, Flat (α v) :=
  fun v ↦ ↑(M.solve I u v)

@[simp] theorem world_apply (I : ∀ v, Flat (α v)) (u : U) (v : V) :
    M.world I u v = ↑(M.solve I u v) := rfl

/-- Effectiveness: an intervention holds in the world it brings about. -/
theorem le_world (I : ∀ v, Flat (α v)) (u : U) : I ≤ M.world I u := fun v ↦ by
  cases h : I v with
  | bot => exact bot_le
  | coe a => rw [world_apply, solve_of_eq_coe h u]

/-- Composition: extending an intervention by holding more variables at the values they take
under it changes nothing. -/
theorem solve_eq_of_le_of_le_world {I J : ∀ v, Flat (α v)} {u : U} (hIJ : I ≤ J)
    (hJ : J ≤ M.world I u) : M.solve J u = M.solve I u := by
  refine (eq_solve_of_isFixedPt (funext fun v ↦ ?_)).symm
  rw [step_apply]
  cases h : J v with
  | bot => exact (solve_of_eq_bot (le_bot_iff.1 (h ▸ hIJ v)) u).symm
  | coe a => exact Flat.coe_le_coe.1 (h ▸ hJ v)

/-- An extension of an intervention leaves its solution unchanged exactly when the extension holds
in the world the intervention brings about. -/
theorem solve_eq_solve_iff_le_world {I J : ∀ v, Flat (α v)} {u : U} (hIJ : I ≤ J) :
    M.solve J u = M.solve I u ↔ J ≤ M.world I u :=
  ⟨fun h v ↦ by rw [world_apply, ← h]; exact le_world J u v, solve_eq_of_le_of_le_world hIJ⟩

variable [DecidableEq V]

@[simp] theorem solve_update_self (I : ∀ v, Flat (α v)) (c : V) (x : α c) (u : U) :
    M.solve (Function.update I c ↑x) u c = x :=
  solve_of_eq_coe (Function.update_self ..) u

/-- Intervening on `c` leaves every variable that `c` is not an ancestor of unchanged, so every
ordering of the variables along the graph is a causal ordering in the sense of Galles and
Pearl. -/
theorem solve_update_of_not_reflTransGen {c v : V} (h : ¬ ReflTransGen M.graph.Adj c v)
    (I : ∀ v, Flat (α v)) (x : Flat (α c)) (u : U) :
    M.solve (Function.update I c x) u v = M.solve I u v :=
  dependsOn_solve u v fun w hw ↦ Function.update_of_ne (fun hwc : w = c ↦ h (hwc ▸ hw)) x I

/-- Intervening on `c` to hold it at the value it takes anyway changes nothing. -/
theorem solve_update_of_solve_eq {I : ∀ v, Flat (α v)} {c : V} {x : α c} {u : U}
    (h : M.solve I u c = x) : M.solve (Function.update I c ↑x) u = M.solve I u := by
  refine solve_eq_of_le_of_le_world (le_update_self_iff.2 ?_) (update_le_iff.2 ⟨?_, ?_⟩)
  · exact h ▸ le_world I u c
  · rw [world_apply, h]
  · exact fun v _ ↦ le_world I u v

/-- Reversibility: if holding `w` at `b` gives `y` the value `a` and holding `y` at `a` gives `w`
the value `b`, then `y` has the value `a` without either intervention. One of the two variables is
not an ancestor of the other, so one intervention leaves the other variable as it was. -/
theorem solve_eq_of_solve_update_of_solve_update {I : ∀ v, Flat (α v)} {u : U} {y w : V}
    (hyw : y ≠ w) {a : α y} {b : α w} (hy : M.solve (Function.update I w ↑b) u y = a)
    (hw : M.solve (Function.update I y ↑a) u w = b) : M.solve I u y = a := by
  by_cases hwy : ReflTransGen M.graph.Adj w y
  · have hyw' : ¬ ReflTransGen M.graph.Adj y w := fun h ↦
      hyw (h.antisymm (fun _ h ↦ _root_.asymm h h) hwy)
    rw [solve_update_of_not_reflTransGen hyw'] at hw
    rwa [solve_update_of_solve_eq hw] at hy
  · rwa [solve_update_of_not_reflTransGen hwy] at hy

end Intervention

section Observation

variable (M) in
/-- `M.contexts s` is the set of contexts in which the observation `s` holds, those whose actual
world settles every variable `s` settles, at the same value. A counterfactual conditioned on `s` is
evaluated over these contexts. -/
def contexts (s : ∀ v, Flat (α v)) : Set U := {u | s ≤ M.world ⊥ u}

@[simp] theorem contexts_bot : M.contexts ⊥ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ bot_le

theorem contexts_anti : Antitone M.contexts := fun _ _ h _ hu ↦ h.trans hu

variable {s : ∀ v, Flat (α v)} {u : U}

/-- Consistency: the observation `s` holds in a context exactly when imposing it there as an
intervention changes nothing. -/
theorem mem_contexts_iff_solve_eq : u ∈ M.contexts s ↔ M.solve s u = M.solve ⊥ u :=
  (solve_eq_solve_iff_le_world bot_le).symm

theorem mem_contexts_update [DecidableEq V] (hu : u ∈ M.contexts s) {c : V} {x : α c}
    (hx : M.solve ⊥ u c = x) : u ∈ M.contexts (Function.update s c ↑x) :=
  update_le_iff.2 ⟨by rw [world_apply, hx], fun v _ ↦ hu v⟩

end Observation

end CausalModel
