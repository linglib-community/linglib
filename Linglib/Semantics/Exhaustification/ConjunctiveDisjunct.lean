module

public import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# Exhaustifying a disjunction with a conjunctive disjunct

A disjunction `(a ∧ b) ∨ c` strengthens under innocent exclusion, against its substitution
alternatives — the connective replacements and the subconstituents — to its strongly
exhaustive reading `(a ∧ b ∧ ¬c) ∨ (c ∧ ¬a ∧ ¬b)`, each disjunct exclusive of the material of
the other. With that reading, the second premise `a` of the illusory inference from
disjunction makes its conclusion `b` classically valid: the scalar-implicature route to the
illusion. Against the four-member Sauerland set the strengthening does not arise — innocent
exclusion only denies the conjunction of the disjuncts — so the subconstituent alternatives
are load-bearing.

## References

* [spector-2007]
* [sauerland-2004]
* [sable-meyer-mascarenhas-2022]
* [bade-picat-chung-mascarenhas-2022]
-/

@[expose] public section

namespace Exhaustification

open Set

variable {W : Type*} {a b c : Set W}

/-- The alternatives of `(a ∧ b) ∨ c` by substitution of connectives and of subconstituents. -/
def conjDisjAlternatives (a b c : Set W) : Set (Set W) :=
  {(a ∩ b) ∪ c, (a ∩ b) ∩ c, a ∪ c, b ∪ c, a ∩ c, b ∩ c, a ∩ b, a, b, c}

theorem exhIE_conjDisjAlternatives (hab : ((a ∩ b) \ c).Nonempty)
    (hc : (c \ (a ∪ b)).Nonempty) :
    exhIE (conjDisjAlternatives a b c) ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
  obtain ⟨x, ⟨hxa, hxb⟩, hxc⟩ := hab
  obtain ⟨y, hyc, hyab⟩ := hc
  have hya : y ∉ a := fun h ↦ hyab (Or.inl h)
  have hyb : y ∉ b := fun h ↦ hyab (Or.inr h)
  have hM : IsMinimalCover (conjDisjAlternatives a b c) ((a ∩ b) ∪ c) {x, y} := by
    refine ⟨?_, fun w hw ↦ ?_, ?_⟩
    · rintro v (rfl | rfl)
      exacts [Or.inl ⟨hxa, hxb⟩, Or.inr hyc]
    · rcases hw with ⟨hwa, hwb⟩ | hwc
      · refine ⟨x, Or.inl rfl, fun q hq hxq ↦ ?_⟩
        simp only [conjDisjAlternatives, mem_insert_iff, mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inl ⟨hwa, hwb⟩, (hxc hxq.2).elim, Or.inl hwa, Or.inl hwb, (hxc hxq.2).elim,
          (hxc hxq.2).elim, ⟨hwa, hwb⟩, hwa, hwb, (hxc hxq).elim]
      · refine ⟨y, Or.inr rfl, fun q hq hyq ↦ ?_⟩
        simp only [conjDisjAlternatives, mem_insert_iff, mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inr hwc, (hya hyq.1.1).elim, Or.inr hwc, Or.inr hwc, (hya hyq.1).elim,
          (hyb hyq.1).elim, (hya hyq.1).elim, (hya hyq).elim, (hyb hyq).elim, hwc]
    · rintro v (rfl | rfl) u (rfl | rfl) huv
      · exact leALT_refl _ _
      · exact (hxc (huv c (by simp [conjDisjAlternatives]) hyc)).elim
      · exact (hya (huv a (by simp [conjDisjAlternatives]) hxa)).elim
      · exact leALT_refl _ _
  rw [hM.exhIE_eq]
  ext u
  simp only [conjDisjAlternatives, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    forall_eq, mem_ofPred_eq, mem_union, mem_inter_iff, mem_sdiff]
  constructor
  · rintro ⟨hu, h⟩
    rcases hu with ⟨hua, hub⟩ | huc
    · refine Or.inl ⟨⟨hua, hub⟩, fun huc ↦ ?_⟩
      exact h.2.2.2.2.1 (by simp_all) ⟨hua, huc⟩
    · by_cases hua : u ∈ a
      · exact (h.2.2.2.2.1 (by simp_all) ⟨hua, huc⟩).elim
      · by_cases hub : u ∈ b
        · exact (h.2.2.2.2.2.1 (by simp_all) ⟨hub, huc⟩).elim
        · exact Or.inr ⟨huc, fun h' ↦ h'.elim hua hub⟩
  · rintro (⟨⟨hua, hub⟩, huc⟩ | ⟨huc, huab⟩)
    · refine ⟨Or.inl ⟨hua, hub⟩, ?_⟩
      simp_all
    · refine ⟨Or.inr huc, ?_⟩
      simp_all

theorem stronglyExhaustive_inter_subset : (((a ∩ b) \ c) ∪ (c \ (a ∪ b))) ∩ a ⊆ b := by
  rintro u ⟨⟨⟨-, hub⟩, -⟩ | ⟨-, huab⟩, hua⟩
  · exact hub
  · exact (huab (Or.inl hua)).elim

end Exhaustification
