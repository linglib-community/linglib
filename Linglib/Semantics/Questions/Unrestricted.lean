module

public import Linglib.Semantics.Questions.Basic

/-!
# Unrestricted inquisitive propositions

This file defines the propositions of unrestricted inquisitive semantics and their content. Such a
proposition is a set of possibilities, sets of worlds, that need not be closed downward, so one
possibility may lie inside another. It is informative when its possibilities do not cover every
world, inquisitive when it has two maximal possibilities, and attentive when it has a non-maximal
one, that is, when its possibilities do not form an antichain. The question it generates, a
downward-closed `Question`, has the same informative content and, for finitely many possibilities,
the same inquisitive content.

## Main definitions

* `Inquisitive.Unrestricted.IsInformative`: the possibilities do not cover every world.
* `Inquisitive.Unrestricted.IsInquisitive`: there are two maximal possibilities.
* `Inquisitive.Unrestricted.IsAttentive`: some possibility is not maximal.
* `Inquisitive.Unrestricted.pro`: the propositional closure.
* `Inquisitive.Unrestricted.restrict`: a proposition restricted to an information set.

## Main statements

* `Inquisitive.Unrestricted.nontrivial_iff_isInquisitive_or_isAttentive`: a proposition has two
  possibilities iff it is inquisitive or attentive.
* `Inquisitive.Unrestricted.eq_singleton_univ_iff`: the tautology is the one proposition that is
  neither informative, inquisitive nor attentive.
* `Inquisitive.Unrestricted.isInquisitive_iff_question`: a finite proposition is inquisitive iff
  the question it generates is.
* `Inquisitive.Unrestricted.univ_mem_iff`: a finite proposition contains the trivial possibility
  iff it is neither informative nor inquisitive.

## References

* [ciardelli-groenendijk-roelofsen-2009]
* [coppock-brochhagen-2013]
-/

@[expose] public section

namespace Inquisitive.Unrestricted

open Set

variable {W : Type*} {P : Set (Set W)}

/-- A proposition is a nonempty set of possibilities that omits the empty possibility unless it
is the contradictory proposition `{∅}` ([ciardelli-groenendijk-roelofsen-2009], Definition 12). -/
def IsProposition (P : Set (Set W)) : Prop := P.Nonempty ∧ (∅ ∉ P ∨ P = {∅})

/-- A proposition is informative when its possibilities do not cover every world
([ciardelli-groenendijk-roelofsen-2009], Definition 16). -/
def IsInformative (P : Set (Set W)) : Prop := ⋃₀ P ≠ univ

/-- A proposition is inquisitive when it has at least two maximal possibilities
([ciardelli-groenendijk-roelofsen-2009], Definition 16). -/
def IsInquisitive (P : Set (Set W)) : Prop := {p | Maximal (· ∈ P) p}.Nontrivial

/-- A proposition is attentive when it has a non-maximal possibility
([ciardelli-groenendijk-roelofsen-2009], Definition 16). -/
def IsAttentive (P : Set (Set W)) : Prop := ∃ p ∈ P, ¬ Maximal (· ∈ P) p

/-! ### Informative, inquisitive and attentive content -/

/-- A proposition is not attentive just in case no possibility in it includes another, as the
propositions of restricted inquisitive semantics require ([ciardelli-groenendijk-roelofsen-2009],
Definition 1). -/
theorem not_isAttentive_iff : ¬ IsAttentive P ↔ IsAntichain (· ⊆ ·) P := by
  simp only [IsAttentive, not_exists, not_and, not_not]
  exact ⟨fun h p hp q hq hpq hle ↦ hpq ((h p hp).eq_of_subset hq hle),
    fun h _ ↦ h.maximal_mem_iff.2⟩

theorem isAttentive_of_ssubset {p q : Set W} (hp : p ∈ P) (hq : q ∈ P) (h : p ⊂ q) :
    IsAttentive P :=
  ⟨p, hp, fun hmax ↦ h.ne (hmax.eq_of_subset hq h.subset)⟩

/-- A proposition whose possibilities form an antichain is inquisitive just in case it has more
than one possibility. -/
theorem isInquisitive_iff_nontrivial (h : IsAntichain (· ⊆ ·) P) :
    IsInquisitive P ↔ P.Nontrivial := by
  rw [IsInquisitive, show {p | Maximal (· ∈ P) p} = P from ext fun _ ↦ h.maximal_mem_iff]

/-- A proposition has more than one possibility just in case it is inquisitive or attentive,
which [coppock-brochhagen-2013] call interactive ((51)); the propositions with one possibility
are the assertions of [ciardelli-groenendijk-roelofsen-2009] (Proposition 21). -/
theorem nontrivial_iff_isInquisitive_or_isAttentive :
    P.Nontrivial ↔ IsInquisitive P ∨ IsAttentive P := by
  by_cases h : IsAttentive P
  · obtain ⟨p, hp, hnm⟩ := h
    obtain ⟨q, hpq, hq⟩ := (not_maximal_iff_exists_gt hp).1 hnm
    exact iff_of_true ⟨p, hp, q, hq, hpq.ne⟩ (.inr ⟨p, hp, hnm⟩)
  · rw [or_iff_left h, isInquisitive_iff_nontrivial (not_isAttentive_iff.1 h)]

/-- The tautology `{univ}` is the one proposition that is neither informative, inquisitive nor
attentive ([ciardelli-groenendijk-roelofsen-2009], Proposition 19). -/
theorem eq_singleton_univ_iff :
    P = {univ} ↔ P.Nonempty ∧ ¬ IsInformative P ∧ ¬ IsInquisitive P ∧ ¬ IsAttentive P := by
  rw [← not_or, ← nontrivial_iff_isInquisitive_or_isAttentive, not_nontrivial_iff, IsInformative,
    not_not]
  refine ⟨?_, fun ⟨⟨p, hp⟩, hU, hP⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨singleton_nonempty _, sUnion_singleton _, subsingleton_singleton⟩
  · obtain rfl := hP.eq_singleton_of_mem hp
    simpa using hU

/-! ### The question a proposition generates -/

/-- A proposition and the question it generates have the same informative content
([ciardelli-groenendijk-roelofsen-2009], p. 99). -/
theorem isInformative_iff_question :
    IsInformative P ↔ (⨆ p ∈ P, Question.ofSet p).IsInformative := by
  rw [Question.IsInformative, Question.info_biSup_ofSet]; rfl

/-- The maximal possibilities of a proposition are the alternatives of the question it generates,
so a proposition is inquisitive just in case that question has two alternatives
([ciardelli-groenendijk-roelofsen-2009], p. 99). -/
theorem isInquisitive_iff_nontrivial_alt :
    IsInquisitive P ↔ (Question.alt (⨆ p ∈ P, Question.ofSet p)).Nontrivial := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp [IsInquisitive]
  · rw [Question.alt_biSup_ofSet_eq hP, IsInquisitive]

/-- A finite proposition is inquisitive just in case the question it generates is not resolved by
its own informative content ([ciardelli-groenendijk-roelofsen-2009], footnote 5). -/
theorem isInquisitive_iff_question (hP : P.Finite) :
    IsInquisitive P ↔ (⨆ p ∈ P, Question.ofSet p).IsInquisitive := by
  have hN := Question.isNormal_biSup_ofSet hP
  rw [isInquisitive_iff_nontrivial_alt, Question.IsInquisitive, Question.mem_props,
    ← hN.exists_alt_eq_singleton_iff, exists_eq_singleton_iff_nonempty_subsingleton,
    ← not_nontrivial_iff, and_iff_right hN.alt_nonempty, not_not]

/-- A finite proposition contains the trivial possibility just in case it is neither informative
nor inquisitive, the conjectures of [ciardelli-groenendijk-roelofsen-2009] (Proposition 25). -/
theorem univ_mem_iff (hfin : P.Finite) (hne : P.Nonempty) :
    univ ∈ P ↔ ¬ IsInformative P ∧ ¬ IsInquisitive P := by
  rw [isInquisitive_iff_question hfin, isInformative_iff_question, Question.IsInformative,
    Question.IsInquisitive, not_not, not_not, Question.info_biSup_ofSet, Question.mem_props]
  constructor
  · intro h
    have hU : ⋃₀ P = univ := eq_univ_of_univ_subset (subset_sUnion_of_mem h)
    exact ⟨hU, hU ▸ Question.mem_biSup_ofSet.2 (.inr ⟨univ, h, subset_rfl⟩)⟩
  · rintro ⟨hU, h⟩
    rcases Question.mem_biSup_ofSet.1 h with h0 | ⟨a, ha, hUa⟩
    · obtain ⟨p, hp⟩ := hne
      have hp0 : p = ∅ := subset_empty_iff.1 (h0 ▸ subset_sUnion_of_mem hp)
      rw [hU] at h0
      exact (hp0.trans h0.symm) ▸ hp
    · rw [hU] at hUa
      exact univ_subset_iff.1 hUa ▸ ha

/-! ### Propositional closure and restriction -/

open Classical in
/-- The propositional closure removes the empty possibility from any set of possibilities but
`{∅}` ([ciardelli-groenendijk-roelofsen-2009], Definition 13). -/
noncomputable def pro (P : Set (Set W)) : Set (Set W) := if P = {∅} then P else P \ {∅}

/-- A proposition restricted to an information set `k` keeps the part of each possibility that
lies in `k` ([coppock-brochhagen-2013], (65)). -/
noncomputable def restrict (P : Set (Set W)) (k : Set W) : Set (Set W) := pro ((k ∩ ·) '' P)

/-- The propositional closure of a nonempty set of possibilities is a proposition
([ciardelli-groenendijk-roelofsen-2009], p. 98). -/
theorem isProposition_pro (hP : P.Nonempty) : IsProposition (pro P) := by
  unfold pro
  split_ifs with h
  · exact ⟨hP, .inr h⟩
  · exact ⟨sdiff_nonempty.2 (mt hP.subset_singleton_iff.1 h), .inl fun h ↦ h.2 rfl⟩

/-- The propositional closure leaves a proposition unchanged. -/
theorem IsProposition.pro_eq (hP : IsProposition P) : pro P = P := by
  unfold pro
  split_ifs with h
  · rfl
  · exact sdiff_singleton_eq_self (hP.2.resolve_right h)

theorem isProposition_singleton (p : Set W) : IsProposition {p} := by
  refine ⟨singleton_nonempty p, ?_⟩
  by_cases h : p = ∅
  · exact .inr (by rw [h])
  · exact .inl fun h' ↦ h (mem_singleton_iff.1 h').symm

/-- Removing the empty possibility does not change the question a set of possibilities
generates. -/
theorem iSup_ofSet_pro : ⨆ p ∈ pro P, Question.ofSet p = ⨆ p ∈ P, Question.ofSet p := by
  unfold pro
  split_ifs
  · rfl
  refine le_antisymm (biSup_mono fun _ h ↦ h.1) (Question.biSup_ofSet_le_iff.2 fun p hp ↦ ?_)
  by_cases h0 : p = ∅
  · rw [h0]
    exact (⨆ q ∈ P \ {∅}, Question.ofSet q).contains_empty
  · exact Question.mem_biSup_ofSet.2 (.inr ⟨p, ⟨hp, h0⟩, subset_rfl⟩)

theorem mem_pro {p : Set W} (hp : p.Nonempty) : p ∈ pro P ↔ p ∈ P := by
  unfold pro
  split_ifs
  · rfl
  · exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hp.ne_empty⟩⟩

theorem empty_mem_pro_iff : ∅ ∈ pro P ↔ P = {∅} := by
  unfold pro
  split_ifs with h
  · exact iff_of_true (by rw [h]; exact mem_singleton _) h
  · exact iff_of_false (fun h' ↦ h'.2 rfl) h

theorem pro_subset : pro P ⊆ P := by
  unfold pro
  split_ifs
  · exact subset_rfl
  · exact sdiff_subset

theorem sUnion_pro : ⋃₀ pro P = ⋃₀ P := by
  unfold pro
  split_ifs
  · rfl
  · exact sUnion_sdiff_singleton_empty P

theorem isAttentive_pro_iff : IsAttentive (pro P) ↔ IsAttentive (P \ {∅}) := by
  unfold pro
  split_ifs with h
  · subst h
    simp [IsAttentive]
  · rfl

theorem pro_eq_singleton {k : Set W} (hk : k ≠ ∅) (hkP : k ∈ P) (hP : P ⊆ {k, ∅}) :
    pro P = {k} := by
  have hne : P ≠ {∅} := fun h ↦ hk (mem_singleton_iff.1 (h ▸ hkP))
  simp only [pro, hne, ↓reduceIte]
  ext p
  refine ⟨fun ⟨hp, hp0⟩ ↦ ?_, ?_⟩
  · rcases hP hp with rfl | rfl
    · rfl
    · exact absurd rfl hp0
  · rintro rfl
    exact ⟨hkP, hk⟩

/-- Restricted to a single world, a proposition keeps at most one possibility. -/
theorem subsingleton_restrict_singleton (w : W) : (restrict P {w}).Subsingleton := by
  unfold restrict pro
  split_ifs with h
  · exact h ▸ subsingleton_singleton
  · refine (subsingleton_singleton (a := {w})).anti ?_
    rintro _ ⟨⟨p, -, rfl⟩, hne⟩
    exact singleton_inter_of_mem (not_not.1 (mt singleton_inter_eq_empty.2 hne))

end Inquisitive.Unrestricted
