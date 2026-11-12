module

public import Linglib.Semantics.Exhaustification.MinimalWorlds
public import Mathlib.Order.SupClosed

/-!
# Optimal assertions

Gricean reasoning about what a speaker says takes her information to be a set of worlds and what
she might have said to be a set of alternatives. Asserting a proposition is optimal for her when
she is certain of it, by Quality, and certain of no alternative that asymmetrically entails it, by
Quantity. This is the optimal answer of Spector's Gricean derivation of exhaustivity, at the
question that separates every two worlds, and the states in which an assertion is optimal are
those the hearer of the neo-Gricean accounts infers from it.

Where every world of the assertion lies above a minimal one, as over finitely many alternatives,
the assertion is [optimal in the state of its minimal worlds](##Gricean.isOptimal_exhMW),
`Exhaustification.exhMW`. When the alternatives include the assertion and are closed under
intersection and nonempty unions that state is the most informed one: every consistent state in
which the assertion is optimal [contains a world making the same alternatives true as each minimal
world](##Gricean.IsOptimal.exists_satisfied_eq).

## References

* [grice-1975]
* [spector-2007]
-/

@[expose] public section

namespace Gricean

open Set

variable {W : Type*} {s φ ψ : Set W} {alts : Set (Set W)}

/-- Asserting `φ` is optimal for a speaker in the state `s`, against the alternatives `alts`,
when she is certain of `φ` and of no alternative that asymmetrically entails it
([spector-2007]'s optimal answer, at the question that separates every two worlds). -/
@[mk_iff] structure IsOptimal (alts : Set (Set W)) (φ s : Set W) : Prop where
  /-- Quality: the speaker is certain of what she asserts. -/
  subset : s ⊆ φ
  /-- Quantity: she is certain of no stronger alternative. -/
  not_ssubset : ∀ ψ ∈ alts, s ⊆ ψ → ¬ ψ ⊂ φ

/-! ### Minimal worlds -/

section MinimalWorlds

open Exhaustification

/-- Where every world of the assertion lies above a minimal one, as over finitely many
alternatives, the assertion is optimal in the state of its minimal worlds. -/
theorem isOptimal_exhMW (h : ∀ w ∈ φ, ∃ u ∈ exhMW alts φ,
    Preorder.satisfied (· ∈ ·) alts u ⊆ Preorder.satisfied (· ∈ ·) alts w) :
    IsOptimal alts φ (exhMW alts φ) :=
  ⟨exhMW_subset, fun _ hψ hsub hψφ ↦ hψφ.2 fun w hw ↦
    let ⟨_, hu, huw⟩ := h w hw
    (huw ⟨hψ, hsub hu⟩).2⟩

variable (hinf : InfClosed alts) (hsup : ∀ A ⊆ alts, A.Nonempty → ⋃₀ A ∈ alts) (hφ : φ ∈ alts)
  (hne : s.Nonempty) (hs : IsOptimal alts φ s)
include hinf hsup hφ hne hs

/-- When the alternatives include the assertion and are closed under intersection and nonempty
unions, a consistent state in which the assertion is optimal contains, for each minimal world of
the assertion, a world making the same alternatives true. -/
theorem IsOptimal.exists_satisfied_eq {u : W} (hu : u ∈ exhMW alts φ) :
    ∃ w ∈ s, Preorder.satisfied (· ∈ ·) alts w = Preorder.satisfied (· ∈ ·) alts u := by
  by_contra hcon
  have hA : ∀ w ∈ s, ∃ a ∈ alts, w ∈ a ∧ u ∉ a := fun w hw ↦ by
    by_contra h
    have hle : Preorder.satisfied (· ∈ ·) alts w ⊆ Preorder.satisfied (· ∈ ·) alts u :=
      fun a ha ↦ ⟨ha.1, by_contra fun hua ↦ h ⟨a, ha.1, ha.2, hua⟩⟩
    exact hcon ⟨w, hw, hle.antisymm (hu.2 (hs.subset hw) hle)⟩
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨a₀, ha₀, -, hua₀⟩ := hA w₀ hw₀
  have hmem : ⋃₀ {a ∈ alts | u ∉ a} ∩ φ ∈ alts :=
    hinf (hsup _ (sep_subset _ _) ⟨a₀, ha₀, hua₀⟩) hφ
  refine hs.not_ssubset _ hmem (fun w hw ↦ ?_) ⟨inter_subset_right, fun h ↦ ?_⟩
  · obtain ⟨a, ha, hwa, hua⟩ := hA w hw
    exact ⟨⟨a, ⟨ha, hua⟩, hwa⟩, hs.subset hw⟩
  · obtain ⟨a, ha, hua⟩ := (h hu.1).1
    exact ha.2 hua

/-- Under the same closure conditions the minimal worlds are the most informed state in which the
assertion is optimal: they entail every alternative that a consistent such state entails. -/
theorem IsOptimal.exhMW_subset (hψ : ψ ∈ alts) (hsψ : s ⊆ ψ) : exhMW alts φ ⊆ ψ := fun _ hu ↦
  let ⟨_, hw, h⟩ := hs.exists_satisfied_eq hinf hsup hφ hne hu
  (h.subset ⟨hψ, hsψ hw⟩).2

/-- And they exclude every alternative that such a state excludes. -/
theorem IsOptimal.exhMW_subset_compl (hψ : ψ ∈ alts) (hsψ : s ⊆ ψᶜ) :
    exhMW alts φ ⊆ ψᶜ := fun _ hu huψ ↦
  let ⟨_, hw, h⟩ := hs.exists_satisfied_eq hinf hsup hφ hne hu
  hsψ hw (h.superset ⟨hψ, huψ⟩).2

end MinimalWorlds

end Gricean
