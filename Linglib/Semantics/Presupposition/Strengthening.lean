module

public import Linglib.Semantics.Exhaustification.Basic
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
epistemic step, and the condition is [strengthening through a knowledge
operator](##Presupposition.mem_strengthen_Iic_iff).

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

/-- The strengthening of `φ`'s presupposition by its alternatives: exhaustification against the
strictly stronger ones. -/
def strengthen (alts : S → Set S) (content : S → Set W) (φ : S) : Set W :=
  Exhaustification.exh (content '' alts φ ∩ Set.Iio (content φ)) (content φ)

theorem mem_strengthen_iff :
    w ∈ strengthen alts content φ ↔
      w ∈ content φ ∧ ∀ ψ ∈ alts φ, w ∈ content ψ → ¬ content ψ ⊂ content φ := by
  refine Exhaustification.mem_exh_inter_Iio.trans (and_congr_right fun _ ↦ ?_)
  simp only [Set.forall_mem_image]
  exact forall₂_congr fun _ _ ↦ ⟨fun h hw hss ↦ h hss hw, fun h hss hw ↦ h hw hss⟩

theorem strengthen_subset (alts : S → Set S) (content : S → Set W) (φ : S) :
    strengthen alts content φ ⊆ content φ :=
  Exhaustification.exh_subset _ _

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

/-- Through a knowledge operator, whose presupposition holds of the information states that
support it, strengthening is the condition at a context: the operand is defined there and no
strictly stronger alternative is. -/
theorem mem_strengthen_Iic_iff :
    c ∈ strengthen alts (fun ψ ↦ Set.Iic (content ψ)) φ ↔
      c ⊆ content φ ∧ ∀ ψ ∈ alts φ, content ψ ⊂ content φ → ¬ c ⊆ content ψ := by
  have key {p q : Set W} : Set.Iic p ⊂ Set.Iic q ↔ p ⊂ q :=
    ⟨fun h ↦ ⟨h.subset (le_refl p), fun hqp ↦ h.not_subset fun _ hr ↦ le_trans hr hqp⟩,
      fun h ↦ ⟨fun _ hr ↦ le_trans hr h.subset, fun hqp ↦ h.not_subset (hqp (le_refl q))⟩⟩
  rw [mem_strengthen_iff]
  exact and_congr_right fun _ ↦ ⟨fun h ψ hψ hss hc ↦ h ψ hψ hc (key.2 hss),
    fun h ψ hψ hc hss ↦ h ψ hψ (key.1 hss) hc⟩

theorem strengthen_eq_self (h : ∀ ψ ∈ alts φ, ¬ content ψ ⊂ content φ) :
    strengthen alts content φ = content φ :=
  Set.ext fun _ ↦ mem_strengthen_iff.trans ⟨And.left, fun hw ↦ ⟨hw, fun ψ hψ _ ↦ h ψ hψ⟩⟩

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
  Set.disjoint_left.2 fun _ hw hs ↦ (mem_strengthen_iff.1 hs).2 ψ hψ hw h

end Presupposition
