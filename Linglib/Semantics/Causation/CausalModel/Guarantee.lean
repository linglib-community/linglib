module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# What a state of knowledge guarantees

A state of knowledge is a partial assignment, the variables whose values are known. A *background*
for it is an intervention that holds every known variable at its known value and possibly others
at any value. The state `k` guarantees `E = e` when `E` takes the value `e` in every context under
every background for `k` that holds `E` only if `k` settles it: whatever else is the case, known or
not, `E = e`. A state of knowledge guarantees what it settles
(`CausalModel.guarantees_of_eq_some`).

Knowing more about the other variables guarantees no less (`CausalModel.Guarantees.mono`). What
knowing one fact `C = c` guarantees of another variable is what holds under every intervention
that sets `C` to `c` (`CausalModel.guarantees_single_iff`), the global sufficiency of `C = c` for
`E = e`; global necessity is the global sufficiency of the opposite value for the opposite effect.

## Implementation notes

A background holds finitely many variables, so a state of knowledge that settles infinitely many
has no background and guarantees everything.

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
intervention that holds what `k` settles and holds `E` only if `k` settles it. -/
def Guarantees (k : ∀ v, Part (α v)) (E : V) (e : α E) : Prop :=
  ∀ u (X : Finset V) (ξ : ∀ v : X, α v),
    k ≤ Function.updateFinset ⊥ X (fun v ↦ Part.some (ξ v)) → (E ∈ X → (k E).Dom) →
      (M.intervene X ξ).solve u E = e

variable {M}

/-- Knowing more guarantees no less, when what more is known is not about `E`. -/
theorem Guarantees.mono (h : k ≤ k') (hE : k' E = k E) (hk : M.Guarantees k E e) :
    M.Guarantees k' E e :=
  fun u X ξ hk' hX ↦ hk u X ξ (h.trans hk') fun hEX ↦ hE ▸ hX hEX

/-- A state of knowledge guarantees what it settles. -/
theorem guarantees_of_eq_some (hk : k E = Part.some e) : M.Guarantees k E e :=
  fun _ _ _ hkX _ ↦
    let ⟨hEX, hξ⟩ := exists_mem_of_le_updateFinset hkX hk
    (solve_intervene_of_mem hEX).trans hξ

/-- What knowing `C = c` alone guarantees of another variable is what holds under every
intervention setting `C` to `c`. -/
theorem guarantees_single_iff {C : V} {c : α C} (hCE : C ≠ E) :
    M.Guarantees (Function.update ⊥ C (Part.some c)) E e ↔
      ∀ u (X : Finset V) (ξ : ∀ v : X, α v), E ∉ X → ∀ hC : C ∈ X, ξ ⟨C, hC⟩ = c →
        (M.intervene X ξ).solve u E = e := by
  refine ⟨fun h u X ξ hE hC hξ ↦ h u X ξ (Part.pi_le_iff.2 fun v hv ↦ ?_) fun hEX ↦ (hE hEX).elim,
    fun h u X ξ hk hE ↦ ?_⟩
  · rcases eq_or_ne v C with rfl | hvC
    · simp [Function.updateFinset, hC, hξ]
    · simp [hvC] at hv
  · obtain ⟨hC, hξ⟩ := exists_mem_of_le_updateFinset hk (Function.update_self ..)
    refine h u X ξ (fun hEX ↦ ?_) hC hξ
    simpa [Function.update_of_ne hCE.symm] using hE hEX

end CausalModel
