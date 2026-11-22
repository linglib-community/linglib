module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# What a state of knowledge guarantees

A state of knowledge is a partial assignment, the variables whose values are known. A *background*
for it is an intervention that extends it, holding every known variable at its known value and
possibly others at any value. The state `k` guarantees `E = e` when `E` takes the value `e` in
every context under every background for `k` that agrees with `k` at `E`: whatever else is the
case, known or not, `E = e`. A state of knowledge guarantees what it settles
(`CausalModel.guarantees_of_eq_some`).

Knowing more about the other variables guarantees no less (`CausalModel.Guarantees.mono`). What
knowing one fact `C = c` guarantees of another variable is what holds under every intervention
that sets `C` to `c` (`CausalModel.guarantees_single_iff`), the global sufficiency of `C = c` for
`E = e`; global necessity is the global sufficiency of the opposite value for the opposite effect.

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

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α) [M.IsAcyclic]
  [∀ v, Nonempty (α v)] {k k' : ∀ v, Part (α v)} {E : V} {e : α E}

/-- The state of knowledge `k` guarantees `E = e` when `E = e` in every context under every
intervention that extends `k` and agrees with it at `E`. -/
def Guarantees (k : ∀ v, Part (α v)) (E : V) (e : α E) : Prop :=
  ∀ (i : ∀ v, Part (α v)) [∀ v, Decidable (i v).Dom] (u : U), k ≤ i → i E = k E →
    (M.intervene i).solve u E = e

variable {M}

/-- Knowing more guarantees no less, when what more is known is not about `E`. -/
theorem Guarantees.mono (h : k ≤ k') (hE : k' E = k E) (hk : M.Guarantees k E e) :
    M.Guarantees k' E e :=
  fun i _ u hk' hiE ↦ hk i u (h.trans hk') (hiE.trans hE)

/-- A state of knowledge guarantees what it settles. -/
theorem guarantees_of_eq_some (hk : k E = Part.some e) : M.Guarantees k E e :=
  fun _ _ _ _ hiE ↦ solve_intervene_of_eq_some (hiE.trans hk)

/-- What knowing `C = c` alone guarantees of another variable is what holds under every
intervention holding `C` at `c` and leaving that variable open. -/
theorem guarantees_single_iff [DecidableEq V] {C : V} {c : α C} (hCE : C ≠ E) :
    M.Guarantees [C ← c] E e ↔
      ∀ (i : ∀ v, Part (α v)) [∀ v, Decidable (i v).Dom] (u : U), i C = Part.some c → i E = ⊥ →
        (M.intervene i).solve u E = e := by
  have hE : ([C ← c] : ∀ v, Part (α v)) E = ⊥ := Function.update_of_ne hCE.symm ..
  have hle (i : ∀ v, Part (α v)) : [C ← c] ≤ i ↔ i C = Part.some c := by
    rw [update_le_iff, Part.some_le_iff]
    exact and_iff_left fun _ _ ↦ bot_le
  exact ⟨fun h i _ u hC hiE ↦ h i u ((hle i).2 hC) (hiE.trans hE.symm),
    fun h i _ u hk hiE ↦ h i u ((hle i).1 hk) (hiE.trans hE)⟩

end CausalModel
