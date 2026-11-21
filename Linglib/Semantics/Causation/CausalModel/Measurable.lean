module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Measurability of the solution of a causal model

With a probability measure on the contexts of a causal model, the solution is a random world and
the solution of a submodel a counterfactual one; their laws are the pushforwards of the measure.
A finite model whose equations are measurable has a
[measurable solution](##CausalModel.measurable_solve), and so does
[each of its submodels](##CausalModel.measurable_solve_intervene).

## References

* [pearl-2000]
* [bongers-forre-peters-mooij-2021]
-/

public section

open Function

namespace CausalModel

variable {U V : Type*} {α : V → Type*} [MeasurableSpace U] [∀ v, MeasurableSpace (α v)]
  {M : CausalModel U V α} [M.IsAcyclic] [∀ v, Nonempty (α v)] [Finite V]

theorem measurable_solve (h : ∀ v, Measurable (uncurry (M.eqn v))) : Measurable M.solve := by
  have := Fintype.ofFinite V
  have x₀ : ∀ v, α v := fun v ↦ Classical.arbitrary _
  have hiter (n : ℕ) : Measurable fun u ↦ (M.step u)^[n] x₀ := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp only [iterate_succ_apply']
      exact .of_eval fun v ↦ (h v).comp (measurable_id.prodMk ih)
  convert hiter (Fintype.card V) using 1
  exact funext fun u ↦ solve_eq_iterate_card u x₀

theorem measurable_solve_intervene (h : ∀ v, Measurable (uncurry (M.eqn v)))
    (s : ∀ v, Part (α v)) [∀ v, Decidable (s v).Dom] : Measurable (M.intervene s).solve :=
  measurable_solve fun v ↦ by
    by_cases hv : (s v).Dom
    · exact (funext fun p ↦ intervene_eqn_of_dom hv p.1 p.2 :
        uncurry ((M.intervene s).eqn v) = fun _ ↦ (s v).get hv) ▸ measurable_const
    · exact (funext fun p ↦ intervene_eqn_of_eq_bot (Part.eq_none_iff'.2 hv) p.1 p.2 :
        uncurry ((M.intervene s).eqn v) = uncurry (M.eqn v)) ▸ h v

end CausalModel
