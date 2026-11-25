/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Head

/-!
# Phases

[marcolli-chomsky-berwick-2025] read the phases of [chomsky-2013] off a head function, here a
parameter `h`. The terms a lexical item heads run from its leaf up to its maximal projection, and
it heads a phase when it heads more than its leaf. Its complement is the sister it projects over.
The phase is what lies within the terms it heads, the interior what lies within the complement,
and the edge the rest: the head and what is merged above it, a phrase raised there included. A
term is `Inaccessible` when it lies in the interior of a phase other than the highest. The Phase
Impenetrability Condition, which seals the interior, is stated on positions in
`Phase/Transfer.lean`, and as a restriction of the coproduct in `Workspace/Merge/Phase.lean`.

## Implementation notes

* Terms are values, not occurrences, so all copies of a head share one phase, and the lower
  copies of a moved phrase are one term; positions tell copies apart in `Copy/Chain.lean`.
* Every head that projects heads a phase, as in the book; the heads a study counts as phase heads
  (C alone, or also v, D, or Voice) are the positions `sealed` takes in `Phase/Transfer.lean`.
* Which phrases lie in the phase of a head depends on the head function. Under the raising head
  a phrase raised to the edge of a head lies in its phase, and a phrase merged there in place
  lies in it only when the head selects it.
* A head function may give a trace a head, and it may head the Merge of a leaf with itself by
  that leaf's item, which then projects over no sister. The statements that find the leaf of a
  head, or the complement of a phase head, assume the case away.

## TODO

* The book's ordering of phases by inclusion, and the stricter variant of `Inaccessible` that also
  freezes the heads of lower phases. The agreement of `Inaccessible` with the positions `sealed`
  gives needs phases to be nested or disjoint, which holds of positions and not of values.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

namespace SyntacticObject

open Relation

variable {L ι : Type} (h : SyntacticObject L ι → Option L) (T : SyntacticObject L ι) (ℓ : L)
  (x z : SyntacticObject L ι)

/-- `ℓ` heads a phase of `T` when it projects, heading a mother of its leaf. -/
def IsPhaseHead : Prop := ∃ m ∈ T.terms, h m = some ℓ ∧ ImmediatelyContains m (leaf ℓ)

instance [DecidableEq L] [DecidableEq ι] : Decidable (IsPhaseHead h T ℓ) :=
  Multiset.decidableExistsMultiset

/-- `z` is the complement of `ℓ` in `T` when `ℓ` projects over its sister `z`. -/
def IsComplementOf : Prop :=
  ∃ m ∈ T.terms, h m = some ℓ ∧ ImmediatelyContains m (leaf ℓ) ∧
    ImmediatelyContains m z ∧ z ≠ leaf ℓ

instance [DecidableEq L] [DecidableEq ι] : Decidable (IsComplementOf h T ℓ z) :=
  Multiset.decidableExistsMultiset

/-- `x` lies within the projection of `ℓ` in `T` when a term of `T` that `ℓ` heads contains it. -/
def WithinProjection : Prop := ∃ p ∈ T.terms, h p = some ℓ ∧ ContainsOrEq p x

instance [DecidableEq L] [DecidableEq ι] : Decidable (WithinProjection h T ℓ x) :=
  Multiset.decidableExistsMultiset

/-- `x` lies within the complement of `ℓ` in `T` when a complement of `ℓ` contains it. -/
def WithinComplement : Prop := ∃ z ∈ T.terms, IsComplementOf h T ℓ z ∧ ContainsOrEq z x

instance [DecidableEq L] [DecidableEq ι] : Decidable (WithinComplement h T ℓ x) :=
  Multiset.decidableExistsMultiset

/-- `x` is inaccessible in `T`, with `Φ` the phase heads: it lies within the complement of a
phase head other than the head of `T`, the interior of a lower phase. -/
def Inaccessible (h : SyntacticObject L ι → Option L) (T : SyntacticObject L ι) (Φ : L → Prop)
    (x : SyntacticObject L ι) : Prop :=
  ∃ m ∈ T.terms, ∃ ℓ ∈ h m, Φ ℓ ∧ h T ≠ some ℓ ∧ WithinComplement h T ℓ x

instance [DecidableEq L] [DecidableEq ι] (Φ : L → Prop) [DecidablePred Φ] :
    Decidable (Inaccessible h T Φ x) :=
  Multiset.decidableExistsMultiset

variable {h T ℓ x z} {y T' : SyntacticObject L ι}

theorem IsComplementOf.mem_terms (hz : IsComplementOf h T ℓ z) : z ∈ T.terms :=
  let ⟨_, hm, _, _, hmz, _⟩ := hz
  SyntacticObject.mem_terms.2 (.tail (SyntacticObject.mem_terms.1 hm) hmz)

theorem WithinProjection.mem_terms (hx : WithinProjection h T ℓ x) : x ∈ T.terms :=
  let ⟨_, hp, _, hpx⟩ := hx
  terms_subset_terms (SyntacticObject.mem_terms.1 hp) (SyntacticObject.mem_terms.2 hpx)

theorem WithinComplement.withinProjection (hx : WithinComplement h T ℓ x) :
    WithinProjection h T ℓ x :=
  let ⟨_, _, ⟨m, hm, hℓ, _, hz, _⟩, hzx⟩ := hx
  ⟨m, hm, hℓ, .head hz hzx⟩

theorem WithinComplement.mem_terms (hx : WithinComplement h T ℓ x) : x ∈ T.terms :=
  hx.withinProjection.mem_terms

theorem WithinProjection.trans (hx : WithinProjection h T ℓ x) (hxy : ContainsOrEq x y) :
    WithinProjection h T ℓ y :=
  let ⟨p, hp, hℓ, hpx⟩ := hx
  ⟨p, hp, hℓ, hpx.trans hxy⟩

/-- Whatever a frozen term contains is frozen. -/
theorem WithinComplement.trans (hx : WithinComplement h T ℓ x) (hxy : ContainsOrEq x y) :
    WithinComplement h T ℓ y :=
  let ⟨z, hz, hc, hzx⟩ := hx
  ⟨z, hz, hc, hzx.trans hxy⟩

theorem WithinComplement.cCommands (hx : WithinComplement h T ℓ x) : T.CCommands (leaf ℓ) x :=
  let ⟨z, hz, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzx⟩ := hx
  ⟨z, hz, ⟨m, hm, hmℓ, hmz, hne.symm⟩, hzx⟩

theorem IsPhaseHead.mono (hp : IsPhaseHead h T ℓ) (hT : T.terms ⊆ T'.terms) :
    IsPhaseHead h T' ℓ :=
  let ⟨m, hm, hℓ, hmℓ⟩ := hp
  ⟨m, hT hm, hℓ, hmℓ⟩

theorem IsComplementOf.mono (hz : IsComplementOf h T ℓ z) (hT : T.terms ⊆ T'.terms) :
    IsComplementOf h T' ℓ z :=
  let ⟨m, hm, hrest⟩ := hz
  ⟨m, hT hm, hrest⟩

/-- A phase keeps its terms as structure is built above it. -/
theorem WithinProjection.mono (hx : WithinProjection h T ℓ x) (hT : T.terms ⊆ T'.terms) :
    WithinProjection h T' ℓ x :=
  let ⟨p, hp, hrest⟩ := hx
  ⟨p, hT hp, hrest⟩

theorem WithinComplement.mono (hx : WithinComplement h T ℓ x) (hT : T.terms ⊆ T'.terms) :
    WithinComplement h T' ℓ x :=
  let ⟨z, hz, hc, hzx⟩ := hx
  ⟨z, hT hz, hc.mono hT, hzx⟩

theorem IsComplementOf.withinComplement (hz : IsComplementOf h T ℓ z) :
    WithinComplement h T ℓ z :=
  ⟨z, hz.mem_terms, hz, .refl⟩

/-- The head of a phase lies in the phase. -/
theorem IsPhaseHead.withinProjection_leaf (hp : IsPhaseHead h T ℓ) :
    WithinProjection h T ℓ (leaf ℓ) :=
  let ⟨m, hm, hℓ, hmℓ⟩ := hp
  ⟨m, hm, hℓ, .single hmℓ⟩

/-- A lexical item that does not head the Merge of its leaf with itself heads a phase exactly when
it projects over a sister. -/
theorem isPhaseHead_iff_exists_isComplementOf (hself : h (merge (leaf ℓ) (leaf ℓ)) ≠ some ℓ) :
    IsPhaseHead h T ℓ ↔ ∃ z, IsComplementOf h T ℓ z := by
  refine ⟨fun ⟨m, hm, hℓ, hmℓ⟩ ↦ ?_, fun ⟨_, m, hm, hℓ, hmℓ, _⟩ ↦ ⟨m, hm, hℓ, hmℓ⟩⟩
  induction m using SyntacticObject.ind with
  | leaf => simp at hmℓ
  | trace => simp at hmℓ
  | traceOf => simp at hmℓ
  | merge l r _ _ =>
    rcases (immediatelyContains_merge _ _ _).1 hmℓ with rfl | rfl
    · exact ⟨r, _, hm, hℓ, by simp, by simp, by rintro rfl; exact hself hℓ⟩
    · exact ⟨l, _, hm, hℓ, by simp, by simp, by rintro rfl; exact hself hℓ⟩

/-- A lexical item that heads no trace of `T` heads a phase exactly when it heads a term other
than its leaf: the terms it heads run down to the mother of the leaf
([marcolli-chomsky-berwick-2025], Lemma 1.14.1 and (1.14.1)). -/
theorem isPhaseHead_iff_exists_head (hh : IsHeadFunction h)
    (htr : ∀ x ∈ T.terms, x.IsTrace → h x ≠ some ℓ) :
    IsPhaseHead h T ℓ ↔ ∃ p ∈ T.terms, h p = some ℓ ∧ p ≠ leaf ℓ := by
  refine ⟨fun ⟨m, hm, hmh, hmℓ⟩ ↦ ⟨m, hm, hmh, by rintro rfl; simp at hmℓ⟩,
    fun ⟨p, hp, hph, hne⟩ ↦ ?_⟩
  induction p using SyntacticObject.ind with
  | leaf a => exact absurd (by rw [hh.eq_of_mem_leaf hph]) hne
  | trace => exact absurd hph (htr _ hp (.inl rfl))
  | traceOf i => exact absurd hph (htr _ hp (.inr ⟨i, rfl⟩))
  | merge l r ihl ihr =>
    obtain ⟨hl, hr⟩ := mem_terms_of_merge_mem_terms hp
    rcases hh.mem_or_mem hph with h' | h'
    · by_cases hl' : l = leaf ℓ
      · exact ⟨_, hp, hph, by simp [hl']⟩
      · exact ihl hl h' hl'
    · by_cases hr' : r = leaf ℓ
      · exact ⟨_, hp, hph, by simp [hr']⟩
      · exact ihr hr h' hr'

/-! ### The phase, its interior and its edge -/

section Multiset

variable [DecidableEq L] [DecidableEq ι]

variable (h T ℓ) in
/-- The phase of `ℓ` in `T` is the multiset of terms within its projection. -/
def phase : Multiset (SyntacticObject L ι) := T.terms.filter (WithinProjection h T ℓ)

variable (h T ℓ) in
/-- The interior of the phase of `ℓ` in `T` is the multiset of terms within its complement. -/
def phaseInterior : Multiset (SyntacticObject L ι) := T.terms.filter (WithinComplement h T ℓ)

variable (h T ℓ) in
/-- The edge of the phase of `ℓ` in `T` is the multiset of terms of the phase outside its
interior. -/
def phaseEdge : Multiset (SyntacticObject L ι) :=
  (T.phase h ℓ).filter (· ∉ T.phaseInterior h ℓ)

@[simp] theorem mem_phase : x ∈ T.phase h ℓ ↔ WithinProjection h T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinProjection.mem_terms)

@[simp] theorem mem_phaseInterior : x ∈ T.phaseInterior h ℓ ↔ WithinComplement h T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinComplement.mem_terms)

@[simp] theorem mem_phaseEdge :
    x ∈ T.phaseEdge h ℓ ↔ WithinProjection h T ℓ x ∧ ¬ WithinComplement h T ℓ x :=
  Multiset.mem_filter.trans (and_congr mem_phase (not_congr mem_phaseInterior))

/-- A head that does not head the Merge of its leaf with itself projects exactly when its phase
has a nonempty interior. -/
theorem isPhaseHead_iff_phaseInterior_ne_zero (hself : h (merge (leaf ℓ) (leaf ℓ)) ≠ some ℓ) :
    IsPhaseHead h T ℓ ↔ T.phaseInterior h ℓ ≠ 0 := by
  rw [isPhaseHead_iff_exists_isComplementOf hself]
  refine ⟨fun ⟨z, hz⟩ h0 ↦ Multiset.filter_eq_nil.1 h0 z hz.mem_terms ⟨z, hz.mem_terms, hz, .refl⟩,
    fun hne ↦ ?_⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨z, -, hz, -⟩ := mem_phaseInterior.1 hx
  exact ⟨z, hz⟩

theorem phaseInterior_le_phase : T.phaseInterior h ℓ ≤ T.phase h ℓ :=
  Multiset.monotone_filter_right _ fun _ hx ↦ hx.withinProjection

/-- The interior and the edge partition the phase. -/
theorem phaseInterior_add_phaseEdge : T.phaseInterior h ℓ + T.phaseEdge h ℓ = T.phase h ℓ := by
  conv_rhs => rw [← Multiset.filter_add_not (· ∈ T.phaseInterior h ℓ) (T.phase h ℓ)]
  congr 1
  rw [phase, Multiset.filter_filter]
  exact Multiset.filter_congr fun _ _ ↦ by
    grind [mem_phaseInterior, WithinComplement.withinProjection]

/-- A phase head that occurs once lies in the edge of its phase, not in its interior
([marcolli-chomsky-berwick-2025], Remark 1.14.4). -/
theorem IsPhaseHead.leaf_mem_phaseEdge (hp : IsPhaseHead h T ℓ)
    (h1 : T.terms.count (leaf ℓ) ≤ 1) : leaf ℓ ∈ T.phaseEdge h ℓ := by
  refine mem_phaseEdge.2 ⟨hp.withinProjection_leaf, fun ⟨z, _, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzℓ⟩ ↦ ?_⟩
  have hz : 1 ≤ z.terms.count (leaf ℓ) :=
    Multiset.one_le_count_iff_mem.2 (SyntacticObject.mem_terms.2 hzℓ)
  have h2 : 2 ≤ m.terms.count (leaf ℓ) := by
    obtain ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨l, r, rfl⟩ := exists_form m
    · simp at hmℓ
    · simp at hmℓ
    · simp at hmℓ
    · rw [immediatelyContains_merge] at hmℓ hmz
      rw [terms_merge, Multiset.count_cons_of_ne (leaf_ne_merge _ _ _), Multiset.count_add]
      rcases hmℓ with rfl | rfl <;> rcases hmz with rfl | rfl
      · exact absurd rfl hne
      · rw [count_self_terms]; omega
      · rw [count_self_terms]; omega
      · exact absurd rfl hne
  exact absurd (h2.trans (Multiset.count_le_of_le _ (terms_le_terms hm))) (by omega)

theorem phaseInterior_le_cCommandDomain : T.phaseInterior h ℓ ≤ T.cCommandDomain (leaf ℓ) :=
  Multiset.monotone_filter_right _ fun _ hx ↦ hx.cCommands

/-- The interior of a head that projects wherever it occurs is its c-command domain. -/
theorem phaseInterior_eq_cCommandDomain
    (hℓ : ∀ m ∈ T.terms, ImmediatelyContains m (leaf ℓ) → h m = some ℓ) :
    T.phaseInterior h ℓ = T.cCommandDomain (leaf ℓ) :=
  Multiset.filter_congr fun _ _ ↦ by
    grind [WithinComplement, IsComplementOf, CCommands, Sisters]

end Multiset

end SyntacticObject

end Minimalist
