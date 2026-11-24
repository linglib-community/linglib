module

public import Linglib.Semantics.Exhaustification.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Minimal

/-!
# Presuppositional strengthening

For expressions `φ : S` with alternatives `alts φ` and presuppositions `content φ : Set W`, the
strengthening of `φ` holds at the worlds where its presupposition holds and that of no strictly
stronger alternative does, `w ∈ content φ` with `¬ content ψ ⊂ content φ` for every
`ψ ∈ alts φ` such that `w ∈ content ψ`. It is exhaustification of `content φ` against the
strictly stronger presuppositions of the alternatives, which gives Percus's anti-presuppositions
and Sauerland's implicated presuppositions. Maximize Presupposition, as Schlenker states it,
compares the presuppositions satisfied throughout a context `c`, and requires `φ` to be a
strongest alternative defined there.

## Main definitions

* `Presupposition.strengthen`: the strengthening of a presupposition by its alternatives.

## Main results

* `Presupposition.mem_strengthen_iff`: membership in the strengthening.
* `Presupposition.minimalFor_preimage_Ici_iff`: Maximize Presupposition in a context `c` holds of
  `φ` when `c ⊆ content φ` and `c` lies in the presupposition of no strictly stronger alternative.
* `Presupposition.mem_strengthen_iff_minimalFor_singleton`: strengthening is that condition at
  one-point contexts.
* `Presupposition.mem_strengthen_Iic_iff`: the condition at a context is strengthening of the
  presuppositions `Set.Iic (content ψ)` of a knowledge operator.
* `Presupposition.strengthen_eq_sdiff`: with one strictly stronger alternative above the others,
  strengthening removes its presupposition.
* `Presupposition.strengthen_anti`: more alternatives strengthen more.

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
  rw [mem_strengthen_iff]
  exact and_congr_right fun _ ↦ ⟨fun h ψ hψ hss hc ↦ h ψ hψ hc (Set.Iic_ssubset_Iic.2 hss),
    fun h ψ hψ hc hss ↦ h ψ hψ (Set.Iic_ssubset_Iic.1 hss) hc⟩

theorem strengthen_anti {alts' : S → Set S} (h : alts φ ⊆ alts' φ) :
    strengthen alts' content φ ⊆ strengthen alts content φ := fun _ hw ↦
  let ⟨hφ, hψ⟩ := mem_strengthen_iff.1 hw
  mem_strengthen_iff.2 ⟨hφ, fun ψ h' ↦ hψ ψ (h h')⟩

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
