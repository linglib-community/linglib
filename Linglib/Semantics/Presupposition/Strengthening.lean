module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Minimal

/-!
# Presuppositional strengthening

This file defines the strengthening of a presupposition by its alternatives: the worlds where it
holds and no strictly stronger alternative's does, the domain of the operator EXHp. Removing the
stronger presuppositions gives Percus's anti-presuppositions and Sauerland's implicated
presuppositions. Heim's Maximize Presupposition, as Schlenker states it, compares presuppositions
satisfied in a context: an expression must be [a strongest alternative defined
there](##Presupposition.minimalFor_preimage_Ici_iff). [Strengthening is that condition at one-point
contexts](##Presupposition.mem_strengthen_iff_minimalFor_singleton), its form after Chemla's
epistemic step.

## References

* [heim-1991]
* [percus-2006]
* [sauerland-2008a]
* [chemla-2008]
* [schlenker-2012]
-/

@[expose] public section

namespace Presupposition

variable {S W : Type*} {alts : S → Set S} {content : S → Set W} {φ ψ : S} {c : Set W} {w : W}

/-- The strengthening of `φ`'s presupposition by its alternatives: the presupposition less those of
the strictly stronger alternatives. -/
def strengthen (alts : S → Set S) (content : S → Set W) (φ : S) : Set W :=
  content φ \ ⋃₀ (content '' alts φ ∩ Set.Iio (content φ))

theorem mem_strengthen_iff :
    w ∈ strengthen alts content φ ↔
      w ∈ content φ ∧ ∀ ψ ∈ alts φ, w ∈ content ψ → ¬ content ψ ⊂ content φ := by
  refine ⟨fun ⟨hw, hn⟩ ↦ ⟨hw, fun ψ hψ hwψ hss ↦ hn ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, hwψ⟩⟩,
    fun ⟨hw, h⟩ ↦ ⟨hw, ?_⟩⟩
  rintro ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, hwψ⟩
  exact h ψ hψ hwψ hss

theorem strengthen_subset (alts : S → Set S) (content : S → Set W) (φ : S) :
    strengthen alts content φ ⊆ content φ :=
  sdiff_le

/-- Maximize Presupposition in a context: `φ` is a strongest alternative defined throughout `c`. -/
theorem minimalFor_preimage_Ici_iff :
    MinimalFor (· ∈ insert φ (alts φ) ∩ content ⁻¹' Set.Ici c) content φ ↔
      c ⊆ content φ ∧ ∀ ψ ∈ alts φ, content ψ ⊂ content φ → ¬ c ⊆ content ψ := by
  constructor
  · rintro ⟨⟨-, hc⟩, h⟩
    exact ⟨hc, fun ψ hψ hss hcψ ↦ hss.not_subset (h ⟨.inr hψ, hcψ⟩ hss.subset)⟩
  · rintro ⟨hc, h⟩
    refine ⟨⟨.inl rfl, hc⟩, ?_⟩
    rintro ψ ⟨rfl | hψ, hcψ⟩ hle
    · exact le_rfl
    · by_contra hn
      exact h ψ hψ ⟨hle, hn⟩ hcψ

/-- Strengthening is Maximize Presupposition at one-point contexts. -/
theorem mem_strengthen_iff_minimalFor_singleton :
    w ∈ strengthen alts content φ ↔
      MinimalFor (· ∈ insert φ (alts φ) ∩ content ⁻¹' Set.Ici {w}) content φ := by
  rw [minimalFor_preimage_Ici_iff, mem_strengthen_iff, Set.singleton_subset_iff]
  exact and_congr_right fun _ ↦
    ⟨fun h ψ hψ hss hw ↦ h ψ hψ (Set.singleton_subset_iff.1 hw) hss,
      fun h ψ hψ hw hss ↦ h ψ hψ hss (Set.singleton_subset_iff.2 hw)⟩

theorem strengthen_eq_self (h : ∀ ψ ∈ alts φ, ¬ content ψ ⊂ content φ) :
    strengthen alts content φ = content φ :=
  sdiff_eq_left.2 <| Set.disjoint_left.2 fun _ _ ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, _⟩ ↦ h ψ hψ hss

/-- With one strictly stronger alternative containing the others, strengthening removes exactly its
presupposition. -/
theorem strengthen_eq_sdiff (hψ : ψ ∈ alts φ) (hss : content ψ ⊂ content φ)
    (hother : ∀ χ ∈ alts φ, content χ ⊂ content φ → content χ ⊆ content ψ) :
    strengthen alts content φ = content φ \ content ψ := by
  ext w
  rw [mem_strengthen_iff, Set.mem_sdiff]
  exact and_congr_right fun _ ↦
    ⟨fun h hw ↦ h ψ hψ hw hss, fun h χ hχ hw hss' ↦ h (hother χ hχ hss' hw)⟩

/-- A strictly stronger alternative's presupposition is disjoint from the strengthening. -/
theorem disjoint_strengthen_of_ssubset (hψ : ψ ∈ alts φ) (h : content ψ ⊂ content φ) :
    Disjoint (content ψ) (strengthen alts content φ) :=
  disjoint_sdiff_self_right.mono_left
    (le_sSup (s := content '' alts φ ∩ Set.Iio (content φ)) ⟨⟨ψ, hψ, rfl⟩, h⟩)

end Presupposition
