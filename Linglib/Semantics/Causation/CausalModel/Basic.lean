module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Counterfactuals in a causal model

This file develops the logic of interventions in an acyclic causal model. The solution of a
submodel is the world an intervention brings about, and read as a counterfactual, the value a
variable would have had, had the intervened variables been held at their values. Galles and Pearl
show that these counterfactuals satisfy composition, effectiveness and reversibility, and that in
a recursive model the first two are complete; all three hold here. A submodel is itself an acyclic
model, so each law is stated once, for an arbitrary model. An observation is a situation, a
partial assignment of values, and picks out the contexts whose actual world agrees with it;
conditioning a counterfactual on evidence restricts it to them.

## Main definitions

* `CausalModel.contexts`: the contexts in which an observation holds

## Main results

* `CausalModel.solve_intervene_of_mem`: effectiveness
* `CausalModel.solve_intervene_eq_iff`: consistency, which in a submodel is composition
* `CausalModel.solve_intervene_of_not_reflTransGen`: an intervention leaves every variable that
  no intervened variable is an ancestor of as it was
* `CausalModel.solve_eq_of_solve_intervene_of_solve_intervene`: reversibility

## Implementation notes

Galles and Pearl state composition as the claim that holding a variable at the value it takes
under an intervention changes nothing. In the submodel of that intervention this is consistency,
and it needs no statement of its own.

An observation is a situation in the sense of Schulz and Nadathur, a function to values or the
undetermined value, `∀ v, Flat (α v)`, and one situation extends another (a supersituation) in the
pointwise flat order, `Flat.pi_le_iff`. The situation of an intervention holding `X` at `x` is the
everywhere undetermined situation updated on `X`, `Function.updateFinset ⊥ X fun v ↦ ↑(x v)`, as
Schulz builds the situation of a set of literals; `[c ← x]` is its case for one variable. The
contexts of an observation are the subteam of Barbero and Sandu: conditioning on it filters
contexts, where an intervention changes the model.

## References

* [galles-pearl-1998]
* [halpern-2000]
* [schulz-2011]
* [nadathur-2023-implicatives]
* [barbero-sandu-2021]
-/

@[expose] public section

namespace CausalModel

open Relation

variable {U V : Type*} {α : V → Type*} {M : CausalModel U V α}

section Intervention

variable [∀ v, Nonempty (α v)] [hM : M.IsAcyclic] [DecidableEq V] {X : Finset V}
  {x : ∀ v : X, α v} {u : U} {v : V}

/-- Effectiveness: an intervention holds in the world it brings about. -/
theorem solve_intervene_of_mem (h : v ∈ X) : (M.intervene X x).solve u v = x ⟨v, h⟩ := by
  rw [solve_apply, intervene_eqn_of_mem h]

theorem solve_intervene_of_notMem (h : v ∉ X) :
    (M.intervene X x).solve u v = M.eqn v u ((M.intervene X x).solve u) := by
  rw [solve_apply, intervene_eqn_of_notMem h]

@[simp] theorem solve_intervene_singleton_self (c : V) (a : α c) : M[c ← a].solve u c = a :=
  solve_intervene_of_mem (Finset.mem_singleton_self c)

/-- Consistency: an intervention changes nothing exactly when the actual world already gives its
variables their values. In the submodel of another intervention this is composition. -/
theorem solve_intervene_eq_iff :
    (M.intervene X x).solve u = M.solve u ↔ X.restrict (M.solve u) = x := by
  refine ⟨fun h ↦ funext fun ⟨v, hv⟩ ↦ h ▸ solve_intervene_of_mem hv,
    fun h ↦ (eq_solve_of_isFixedPt (funext fun v ↦ ?_)).symm⟩
  by_cases hv : v ∈ X
  · rw [step_apply, intervene_eqn_of_mem hv, ← h]; rfl
  · rw [step_apply, intervene_eqn_of_notMem hv, ← solve_apply]

theorem solve_intervene_singleton_eq_iff {c : V} {a : α c} :
    M[c ← a].solve u = M.solve u ↔ M.solve u c = a := by
  rw [solve_intervene_eq_iff]
  refine ⟨fun h ↦ congrFun h ⟨c, Finset.mem_singleton_self c⟩, fun h ↦ funext fun ⟨v, hv⟩ ↦ ?_⟩
  obtain rfl := Finset.mem_singleton.1 hv
  exact h

/-- Intervening only on variables that are not ancestors of `v` leaves `v` as it was, so every
ordering of the variables along the graph is a causal ordering in the sense of Galles and
Pearl. -/
theorem solve_intervene_of_not_reflTransGen (h : ∀ c ∈ X, ¬ ReflTransGen M.graph.Adj c v) :
    (M.intervene X x).solve u v = M.solve u v :=
  WellFounded.fixedPoint_congr (hr := hM) (dependsOn_step (M := M.intervene X x) u)
    (dependsOn_step u) fun w hw _ ↦ intervene_eqn_of_notMem (fun hwX ↦ h w hwX hw) _ _

theorem solve_intervene_singleton_of_not_reflTransGen {c : V}
    (h : ¬ ReflTransGen M.graph.Adj c v) (a : α c) : M[c ← a].solve u v = M.solve u v :=
  solve_intervene_of_not_reflTransGen fun _ hc ↦ Finset.mem_singleton.1 hc ▸ h

/-- Reversibility: if holding `w` at `b` gives `y` the value `a` and holding `y` at `a` gives `w`
the value `b`, then `y` has the value `a` without either intervention. One of the two variables is
not an ancestor of the other, so one intervention leaves the other variable as it was. -/
theorem solve_eq_of_solve_intervene_of_solve_intervene {y w : V} (hyw : y ≠ w) {a : α y}
    {b : α w} (hy : M[w ← b].solve u y = a) (hw : M[y ← a].solve u w = b) :
    M.solve u y = a := by
  by_cases hwy : ReflTransGen M.graph.Adj w y
  · have hyw' : ¬ ReflTransGen M.graph.Adj y w := fun h ↦
      hyw (h.antisymm (fun _ h ↦ _root_.asymm h h) hwy)
    rw [solve_intervene_singleton_of_not_reflTransGen hyw'] at hw
    rwa [solve_intervene_singleton_eq_iff.2 hw] at hy
  · rwa [solve_intervene_singleton_of_not_reflTransGen hwy] at hy

end Intervention

section Observation

variable [∀ v, Nonempty (α v)] [M.IsAcyclic] {s : ∀ v, Flat (α v)} {u : U}

variable (M) in
/-- `M.contexts s` is the set of contexts in which the observation `s` holds, those whose actual
world gives every variable `s` settles the value `s` settles it to. A counterfactual conditioned
on `s` is evaluated over these contexts. -/
def contexts (s : ∀ v, Flat (α v)) : Set U := {u | s ≤ fun v ↦ ↑(M.solve u v)}

@[simp] theorem contexts_bot : M.contexts ⊥ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ bot_le

theorem contexts_anti : Antitone M.contexts := fun _ _ h _ hu ↦ h.trans hu

theorem mem_contexts_update [DecidableEq V] (hu : u ∈ M.contexts s) {c : V} {x : α c}
    (hx : M.solve u c = x) : u ∈ M.contexts (Function.update s c ↑x) :=
  update_le_iff.2 ⟨by rw [hx], fun v _ ↦ hu v⟩

end Observation

end CausalModel
