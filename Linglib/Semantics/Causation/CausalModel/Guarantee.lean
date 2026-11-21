module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# What a state of knowledge guarantees

A state of knowledge is a partial assignment, the variables whose values are known. A *background*
for it is an intervention that holds every known variable at its known value and possibly others
at any value. The state `k` guarantees `E = e` when `E` takes the value `e` in every context under
every background for `k` that leaves `E` open: whatever else is the case, known or not, `E = e`.

Knowing more guarantees no less (`CausalModel.Guarantees.mono`). What knowing one fact `C = c`
guarantees is what holds under every intervention that sets `C` to `c`
(`CausalModel.guarantees_single_iff`), the global sufficiency of `C = c` for `E = e`; global
necessity is the global sufficiency of the opposite value for the opposite effect.

This is entailment by intervention. Entailment by observation, the development of a partial
assignment along the equations, is `CausalModel.CausallyEntails`.

## References

* [glass-2023b]
* [sloman-barbey-hotaling-2009]
* [mackie-1965]
* [halpern-pearl-2005]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} [DecidableEq V] {k k' : ∀ v, Part (α v)}

/-- A background for a state of knowledge holds each known variable at its known value. -/
theorem exists_mem_of_le_updateFinset {X : Finset V} {ξ : ∀ v : X, α v}
    (hk : k ≤ Function.updateFinset ⊥ X fun v ↦ Part.some (ξ v)) {v : V} {a : α v}
    (hv : k v = Part.some a) : ∃ h : v ∈ X, ξ ⟨v, h⟩ = a := by
  have := (Part.pi_le_iff.1 hk v (hv ▸ Part.some_dom a)).symm
  rw [hv] at this
  by_cases h : v ∈ X
  · exact ⟨h, by simpa [Function.updateFinset, h] using this⟩
  · simp [Function.updateFinset, h] at this

variable (M : CausalModel U V α) [M.IsAcyclic] [∀ v, Nonempty (α v)] {E : V} {e : α E}

/-- The state of knowledge `k` guarantees `E = e` when `E = e` in every context under every
intervention that holds what `k` settles and leaves `E` open. -/
def Guarantees (k : ∀ v, Part (α v)) (E : V) (e : α E) : Prop :=
  ∀ u (X : Finset V) (ξ : ∀ v : X, α v),
    k ≤ Function.updateFinset ⊥ X (fun v ↦ Part.some (ξ v)) → E ∉ X →
      (M.intervene X ξ).solve u E = e

variable {M}

/-- Knowing more guarantees no less. -/
theorem Guarantees.mono (h : k ≤ k') (hk : M.Guarantees k E e) : M.Guarantees k' E e :=
  fun u X ξ hk' hE ↦ hk u X ξ (h.trans hk') hE

/-- What knowing `C = c` alone guarantees is what holds under every intervention setting `C` to
`c`. -/
theorem guarantees_single_iff {C : V} {c : α C} :
    M.Guarantees (Function.update ⊥ C (Part.some c)) E e ↔
      ∀ u (X : Finset V) (ξ : ∀ v : X, α v), E ∉ X → ∀ hC : C ∈ X, ξ ⟨C, hC⟩ = c →
        (M.intervene X ξ).solve u E = e := by
  refine ⟨fun h u X ξ hE hC hξ ↦ h u X ξ (Part.pi_le_iff.2 fun v hv ↦ ?_) hE,
    fun h u X ξ hk hE ↦ ?_⟩
  · rcases eq_or_ne v C with rfl | hvC
    · simp [Function.updateFinset, hC, hξ]
    · simp [hvC] at hv
  · obtain ⟨hC, hξ⟩ := exists_mem_of_le_updateFinset hk (Function.update_self ..)
    exact h u X ξ hE hC hξ

end CausalModel
