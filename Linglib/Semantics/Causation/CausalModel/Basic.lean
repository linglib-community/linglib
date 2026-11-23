module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Core.Order.BoundedComplete
public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Counterfactuals in a causal model

This file develops the logic of interventions in an acyclic causal model. The solution of a
submodel is the world an intervention brings about, and read as a counterfactual, the value a
variable would have had, had the intervened variables been held at their values. Galles and Pearl
show that these counterfactuals satisfy composition, effectiveness and reversibility, and that in
a recursive model the first two are complete; all three hold here. Completeness is stated for
potential responses, functions giving the values of the variables under each intervention in each
context: one that satisfies effectiveness and composition, and in which a variable held against
all the others reads only its parents in a well-founded graph, is the solution of the submodels
of exactly one model on that graph (`CausalModel.potentialResponseEquiv`). A submodel is itself
an acyclic model, so each law is stated once, for an arbitrary model. An observation is a situation, a
partial assignment of values, and picks out the contexts whose actual world agrees with it;
conditioning a counterfactual on evidence restricts it to them.

## Main definitions

* `CausalModel.contexts`: the contexts in which an observation holds

## Main results

* `CausalModel.solve_intervene_of_eq_some`: effectiveness
* `CausalModel.solve_intervene_eq_iff`: consistency, which in a submodel is composition
* `CausalModel.mem_contexts_iff_solve_intervene`: an observation holds in a context exactly when
  holding it there changes nothing
* `CausalModel.solve_intervene_of_not_reflTransGen`: an intervention leaves every variable that
  no intervened variable is an ancestor of as it was
* `CausalModel.solve_eq_of_solve_intervene_of_solve_intervene`: reversibility

## Implementation notes

Galles and Pearl state composition as the claim that holding a variable at the value it takes
under an intervention changes nothing. In the submodel of that intervention this is consistency,
and it needs no statement of its own.

An observation is a situation in the sense of Schulz and Nadathur, a function to values or the
undetermined value, mathlib's partial values `∀ v, Part (α v)`, and one situation extends another
(a supersituation) in the pointwise order of `Part`, `Part.pi_le_iff`. An intervention is a
situation too, the facts it holds, and `[c ← x]` is its case for one variable. The contexts of an
observation are the subteam of Barbero and Sandu: conditioning on it filters contexts, where an
intervention changes the model.

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

variable [∀ v, Nonempty (α v)] [hM : M.IsAcyclic] {s : ∀ v, Part (α v)}
  [∀ v, Decidable (s v).Dom] {u : U} {v : V}

/-- Effectiveness: an intervention holds in the world it brings about. -/
theorem solve_intervene_of_eq_some {x : α v} (h : s v = Part.some x) :
    (M.intervene s).solve u v = x := by
  rw [solve_apply, intervene_eqn_of_eq_some h]

theorem solve_intervene_of_eq_bot (h : s v = ⊥) :
    (M.intervene s).solve u v = M.eqn v u ((M.intervene s).solve u) := by
  rw [solve_apply, intervene_eqn_of_eq_bot h]

@[simp] theorem solve_intervene_singleton_self [DecidableEq V] (c : V) (a : α c) :
    M[c ← a].solve u c = a :=
  solve_intervene_of_eq_some (Function.update_self ..)

/-- Consistency: an intervention changes nothing exactly when the actual world already gives its
variables their values. In the submodel of another intervention this is composition. -/
theorem solve_intervene_eq_iff :
    (M.intervene s).solve u = M.solve u ↔ s ≤ fun v ↦ Part.some (M.solve u v) := by
  refine ⟨fun h ↦ Part.pi_le_iff.2 fun v hv ↦ ?_,
    fun h ↦ (eq_solve_of_isFixedPt (funext fun v ↦ ?_)).symm⟩
  · have hs : s v = Part.some ((s v).get hv) := (Part.some_get hv).symm
    rw [hs, ← h, solve_intervene_of_eq_some hs]
  · by_cases hv : (s v).Dom
    · have hs : s v = Part.some (M.solve u v) := Part.pi_le_iff.1 h v hv
      rw [step_apply, intervene_eqn_of_eq_some hs]
    · rw [step_apply, intervene_eqn_of_eq_bot (Part.eq_none_iff'.2 hv), ← solve_apply]

theorem solve_intervene_singleton_eq_iff [DecidableEq V] {c : V} {a : α c} :
    M[c ← a].solve u = M.solve u ↔ M.solve u c = a := by
  rw [solve_intervene_eq_iff, update_le_iff]
  exact ⟨fun h ↦ (Part.some_le_some.1 h.1).symm,
    fun h ↦ ⟨Part.some_le_some.2 h.symm, fun _ _ ↦ bot_le⟩⟩

/-- Intervening only on variables that are not ancestors of `v` leaves `v` as it was, so every
ordering of the variables along the graph is a causal ordering in the sense of Galles and
Pearl. -/
theorem solve_intervene_of_not_reflTransGen
    (h : ∀ c, (s c).Dom → ¬ ReflTransGen M.graph.Adj c v) :
    (M.intervene s).solve u v = M.solve u v :=
  WellFounded.fixedPoint_congr (hr := hM) (dependsOn_step (M := M.intervene s) u)
    (dependsOn_step u) fun w hw _ ↦
      intervene_eqn_of_eq_bot (Part.eq_none_iff'.2 fun hd ↦ h w hd hw) _ _

theorem solve_intervene_singleton_of_not_reflTransGen [DecidableEq V] {c : V}
    (h : ¬ ReflTransGen M.graph.Adj c v) (a : α c) : M[c ← a].solve u v = M.solve u v :=
  solve_intervene_of_not_reflTransGen fun w hw hwv ↦ by
    obtain rfl | hne := eq_or_ne w c
    · exact h hwv
    · simp [Function.update_of_ne hne] at hw

/-- Reversibility: if holding `w` at `b` gives `y` the value `a` and holding `y` at `a` gives `w`
the value `b`, then `y` has the value `a` without either intervention. One of the two variables is
not an ancestor of the other, so one intervention leaves the other variable as it was. -/
theorem solve_eq_of_solve_intervene_of_solve_intervene [DecidableEq V] {y w : V} (hyw : y ≠ w)
    {a : α y} {b : α w} (hy : M[w ← b].solve u y = a) (hw : M[y ← a].solve u w = b) :
    M.solve u y = a := by
  by_cases hwy : ReflTransGen M.graph.Adj w y
  · have hyw' : ¬ ReflTransGen M.graph.Adj y w := fun h ↦
      hyw (h.antisymm (fun _ h ↦ _root_.asymm h h) hwy)
    rw [solve_intervene_singleton_of_not_reflTransGen hyw'] at hw
    rwa [solve_intervene_singleton_eq_iff.2 hw] at hy
  · rwa [solve_intervene_singleton_of_not_reflTransGen hwy] at hy

end Intervention

section Observation

variable [∀ v, Nonempty (α v)] [M.IsAcyclic] {s : ∀ v, Part (α v)} {u : U}

variable (M) in
/-- `M.contexts s` is the set of contexts in which the observation `s` holds, those whose actual
world gives every variable `s` settles the value `s` settles it to. A counterfactual conditioned
on `s` is evaluated over these contexts. -/
def contexts (s : ∀ v, Part (α v)) : Set U := {u | s ≤ fun v ↦ Part.some (M.solve u v)}

@[simp] theorem contexts_bot : M.contexts ⊥ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ bot_le

theorem contexts_anti : Antitone M.contexts := fun _ _ h _ hu ↦ h.trans hu

/-- Holding and observing: an observation holds in a context exactly when holding it there changes
nothing. -/
theorem mem_contexts_iff_solve_intervene [∀ v, Decidable (s v).Dom] :
    u ∈ M.contexts s ↔ (M.intervene s).solve u = M.solve u :=
  solve_intervene_eq_iff.symm

theorem mem_contexts_update [DecidableEq V] (hu : u ∈ M.contexts s) {c : V} {x : α c}
    (hx : M.solve u c = x) : u ∈ M.contexts (Function.update s c (Part.some x)) :=
  update_le_iff.2 ⟨by rw [hx], fun v _ ↦ hu v⟩

/-- Settling a variable the observation leaves open keeps the contexts whose actual world gives it
that value. -/
theorem contexts_update [DecidableEq V] {c : V} (hc : s c = ⊥) (x : α c) :
    M.contexts (Function.update s c (Part.some x)) =
      (fun u ↦ M.solve u c) ⁻¹' {x} ∩ M.contexts s := by
  ext u
  refine ⟨fun h ↦ ?_, fun h ↦ mem_contexts_update h.2 h.1⟩
  obtain ⟨h₁, h₂⟩ := update_le_iff.1 h
  exact ⟨(Part.some_le_some.1 h₁).symm, fun v ↦
    if hv : v = c then by subst hv; exact hc ▸ bot_le else h₂ v hv⟩

end Observation

/-! ### Potential responses -/

section PotentialResponse

variable [DecidableEq V]

/-- A potential response on the graph `G` gives the values of the variables when a partial
assignment is held in a context. What is held obtains (effectiveness), holding in addition
values that obtain anyway changes nothing (composition), and the value of a variable when every
other variable is held depends only on its parents in `G`. -/
structure IsPotentialResponse (G : Digraph V) (f : (∀ v, Part (α v)) → U → ∀ v, α v) :
    Prop where
  effective (s : ∀ v, Part (α v)) (u : U) : s ≤ fun v ↦ Part.some (f s u v)
  composition {s t r : ∀ v, Part (α v)} (u : U) : (t ≤ fun v ↦ Part.some (f s u v)) →
    IsLUB {s, t} r → f r u = f s u
  dependsOn (v : V) (u : U) :
    DependsOn (fun y ↦ f (Function.update (fun w ↦ Part.some (y w)) v ⊥) u v) {w | G.Adj w v}

/-- The model of a potential response: the equation of a variable gives its value when every
other variable is held. -/
def ofPotentialResponse (G : Digraph V) (f : (∀ v, Part (α v)) → U → ∀ v, α v)
    (h : IsPotentialResponse G f) : CausalModel U V α where
  graph := G
  eqn v u y := f (Function.update (fun w ↦ Part.some (y w)) v ⊥) u v
  dependsOn_eqn := h.dependsOn

variable [∀ v, Nonempty (α v)]

/-- Completeness of composition and effectiveness: a potential response on a well-founded graph
is the solution of the submodels of its model. -/
theorem solve_intervene_ofPotentialResponse {G : Digraph V}
    {f : (∀ v, Part (α v)) → U → ∀ v, α v} (h : IsPotentialResponse G f)
    (hG : WellFounded G.Adj) (s : ∀ v, Part (α v)) [∀ v, Decidable (s v).Dom] (u : U) :
    have : (ofPotentialResponse G f h).IsAcyclic := hG
    ((ofPotentialResponse G f h).intervene s).solve u = f s u := by
  have : (ofPotentialResponse G f h).IsAcyclic := hG
  refine (eq_solve_of_isFixedPt (funext fun v ↦ ?_)).symm
  by_cases hv : (s v).Dom
  · rw [step_apply, intervene_eqn_of_dom hv]
    have e := Part.pi_le_iff.mp (h.effective s u) v hv
    exact Part.get_eq_of_mem (by rw [e]; exact Part.mem_some _) hv
  · rw [step_apply, intervene_eqn_of_eq_bot (Part.eq_bot_iff_not_dom.mpr hv)]
    change f (Function.update (fun w ↦ Part.some (f s u w)) v ⊥) u v = f s u v
    have hs : s ≤ Function.update (fun w ↦ Part.some (f s u w)) v ⊥ :=
      le_update_iff.mpr ⟨(Part.eq_bot_iff_not_dom.mpr hv).le, fun w _ ↦ h.effective s u w⟩
    rw [h.composition u (update_le_iff.mpr ⟨bot_le, fun _ _ ↦ le_rfl⟩)
      (isLUB_pair_iff_forall_le.mpr ⟨hs, le_rfl, fun _ _ h ↦ h⟩)]

open Classical in
/-- The potential response of an acyclic model: the solution of the submodel holding `s`. -/
noncomputable def potentialResponse (M : CausalModel U V α) [hM : M.IsAcyclic]
    (s : ∀ v, Part (α v)) (u : U) : ∀ v, α v :=
  (M.intervene s).solve u

omit [DecidableEq V] in
theorem potentialResponse_eq (M : CausalModel U V α) [M.IsAcyclic] (s : ∀ v, Part (α v))
    [inst : ∀ v, Decidable (s v).Dom] (u : U) :
    M.potentialResponse s u = (M.intervene s).solve u := by
  have : (fun v ↦ Classical.propDecidable (s v).Dom) = inst := Subsingleton.elim _ _
  subst this
  rfl

/-- Holding every variable but `v` gives `v` the value of its equation. -/
theorem potentialResponse_update_bot (M : CausalModel U V α) [hM : M.IsAcyclic] (v : V) (u : U)
    (y : ∀ w, α w) :
    M.potentialResponse (Function.update (fun w ↦ Part.some (y w)) v ⊥) u v = M.eqn v u y := by
  rw [potentialResponse_eq, solve_apply, intervene_eqn_of_eq_bot (Function.update_self ..)]
  exact M.dependsOn_eqn v u fun w hw ↦ solve_intervene_of_eq_some (Function.update_of_ne
    (fun e ↦ by subst e; exact WellFounded.asymmetric (h := hM) _ _ hw hw) ..)

open Classical in
/-- Soundness: the solutions of the submodels of an acyclic model are a potential response on
its graph. -/
theorem isPotentialResponse_potentialResponse (M : CausalModel U V α) [hM : M.IsAcyclic] :
    IsPotentialResponse M.graph M.potentialResponse where
  effective s u := Part.pi_le_iff.mpr fun v hv ↦
    have hs : s v = Part.some ((s v).get hv) := (Part.some_get hv).symm
    hs.trans (congrArg Part.some (solve_intervene_of_eq_some hs).symm)
  composition {s t r} u ht hr := by
    rw [potentialResponse_eq, potentialResponse_eq, ← solve_intervene_eq_iff.mpr ht]
    congr 1
    exact (intervene_intervene_of_isLUB hr).symm
  dependsOn v u x y h := by
    simp only [potentialResponse_update_bot]
    exact M.dependsOn_eqn v u h

theorem ofPotentialResponse_potentialResponse (M : CausalModel U V α) [hM : M.IsAcyclic] :
    ofPotentialResponse M.graph M.potentialResponse (isPotentialResponse_potentialResponse M) =
      M := by
  obtain ⟨g, eqn, hdep⟩ := M
  simp only [ofPotentialResponse, mk.injEq, true_and]
  funext v u y
  exact potentialResponse_update_bot _ v u y

/-- The acyclic causal models on a well-founded graph are the potential responses on it. -/
noncomputable def potentialResponseEquiv (G : Digraph V) (hG : WellFounded G.Adj) :
    {M : CausalModel U V α // M.graph = G} ≃
      {f : (∀ v, Part (α v)) → U → ∀ v, α v // IsPotentialResponse G f} where
  toFun M := ⟨potentialResponse (hM := show WellFounded M.1.graph.Adj from M.2.symm ▸ hG) M.1, by
    obtain ⟨M, rfl⟩ := M
    exact isPotentialResponse_potentialResponse (hM := hG) M⟩
  invFun f := ⟨ofPotentialResponse G f.1 f.2, rfl⟩
  left_inv := by
    rintro ⟨M, rfl⟩
    exact Subtype.ext (ofPotentialResponse_potentialResponse (hM := hG) M)
  right_inv f := Subtype.ext (funext fun s ↦ funext fun u ↦ by
    classical exact solve_intervene_ofPotentialResponse f.2 hG s u)

end PotentialResponse

end CausalModel
