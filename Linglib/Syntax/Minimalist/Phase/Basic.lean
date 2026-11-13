/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Phases

[marcolli-chomsky-berwick-2025] read the phases of [chomsky-2013] off a head function, here the
raising head `SyntacticObject.raisingHead`. The terms a lexical item heads run from its leaf up to
its maximal projection, and it heads a phase when it
[heads more than its leaf](##Minimalist.SyntacticObject.isPhaseHead_iff_exists_raisingHead). Its
complement is the sister it projects over. The phase is what lies within the terms it heads, the
interior what lies within the complement, and the edge the rest: the head and what is merged above
it, a phrase raised there included. The Phase Impenetrability Condition seals the interior, under
[chomsky-2000]'s condition against every probe outside the phase, and under [chomsky-2001]'s
[weaker one](##Minimalist.SyntacticObject.Accessible.nextPhase_of_phase) only against a probe
outside the complement of a higher phase head.

## Implementation notes

* Terms are values, not occurrences, so all copies of a head share one phase, and the lower
  copies of a moved phrase are one term; positions tell copies apart in `Copy/Chain.lean`, and
  `Phase/Transfer.lean` states the two conditions there.
* Every head that projects heads a phase, as in the book; the heads a study counts as phase heads
  (C alone, or also v, D, or Voice) are the list `Accessible` takes.
* Under the raising head a phrase raised to the edge of a head lies in its phase; a phrase merged
  there in place lies in it only when the head selects it.
* The bare trace is headed by the dummy token `LexicalItem.Token.bareTrace`, which the statements
  about the leaf of a head exclude.

## TODO

* The book's ordering of phases by inclusion and its inaccessible terms, those in the interiors of
  lower phases, with the stricter variant that also freezes their heads. That a goal is
  inaccessible to a head exactly when `Accessible` fails needs phases to be nested or disjoint,
  which holds of positions and not of values.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-2013]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Minimalist

/-- When the Phase Impenetrability Condition seals the interior of a phase head. -/
inductive Impenetrability
  /-- Once the phase is built, to everything outside it ([chomsky-2000]). -/
  | phase
  /-- Once a phase head whose complement contains the phase is merged, to everything outside
  that complement ([chomsky-2001]). -/
  | nextPhase
  deriving DecidableEq, Repr

namespace SyntacticObject

open Relation

variable (T : SyntacticObject) (ℓ : LexicalItem.Token) (x z : SyntacticObject)

/-- `ℓ` heads a phase of `T` when it projects, heading a mother of its leaf. -/
def IsPhaseHead : Prop := ∃ m ∈ T.terms, m.raisingHead = some ℓ ∧ ImmediatelyContains m (leaf ℓ)

instance : Decidable (IsPhaseHead T ℓ) := Multiset.decidableExistsMultiset

/-- `z` is the complement of `ℓ` in `T` when `ℓ` projects over its sister `z`. -/
def IsComplementOf : Prop :=
  ∃ m ∈ T.terms, m.raisingHead = some ℓ ∧ ImmediatelyContains m (leaf ℓ) ∧
    ImmediatelyContains m z ∧ z ≠ leaf ℓ

instance : Decidable (IsComplementOf T ℓ z) := Multiset.decidableExistsMultiset

/-- `x` lies within the projection of `ℓ` in `T` when a term of `T` that `ℓ` heads contains it. -/
def WithinProjection : Prop := ∃ p ∈ T.terms, p.raisingHead = some ℓ ∧ ContainsOrEq p x

instance : Decidable (WithinProjection T ℓ x) := Multiset.decidableExistsMultiset

/-- `x` lies within the complement of `ℓ` in `T` when a complement of `ℓ` contains it. -/
def WithinComplement : Prop := ∃ z ∈ T.terms, IsComplementOf T ℓ z ∧ ContainsOrEq z x

instance : Decidable (WithinComplement T ℓ x) := Multiset.decidableExistsMultiset

/-- The phase of `ℓ` in `T` is the multiset of terms within its projection. -/
def phase : Multiset SyntacticObject := T.terms.filter (WithinProjection T ℓ)

/-- The interior of the phase of `ℓ` in `T` is the multiset of terms within its complement. -/
def phaseInterior : Multiset SyntacticObject := T.terms.filter (WithinComplement T ℓ)

/-- The edge of the phase of `ℓ` in `T` is the multiset of terms of the phase outside its
interior. -/
def phaseEdge : Multiset SyntacticObject := (T.phase ℓ).filter (· ∉ T.phaseInterior ℓ)

variable {T ℓ x z} {y : SyntacticObject}

theorem IsComplementOf.mem_terms (h : IsComplementOf T ℓ z) : z ∈ T.terms :=
  let ⟨_, hm, _, _, hz, _⟩ := h
  SyntacticObject.mem_terms.2 (.tail (SyntacticObject.mem_terms.1 hm) hz)

theorem WithinProjection.mem_terms (h : WithinProjection T ℓ x) : x ∈ T.terms :=
  let ⟨_, hp, _, hpx⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hp) (SyntacticObject.mem_terms.2 hpx)

theorem WithinComplement.withinProjection (h : WithinComplement T ℓ x) : WithinProjection T ℓ x :=
  let ⟨_, _, ⟨m, hm, hℓ, _, hz, _⟩, hzx⟩ := h
  ⟨m, hm, hℓ, .head hz hzx⟩

theorem WithinComplement.mem_terms (h : WithinComplement T ℓ x) : x ∈ T.terms :=
  h.withinProjection.mem_terms

theorem WithinProjection.trans (hx : WithinProjection T ℓ x) (hxy : ContainsOrEq x y) :
    WithinProjection T ℓ y :=
  let ⟨p, hp, hℓ, hpx⟩ := hx
  ⟨p, hp, hℓ, hpx.trans hxy⟩

/-- Whatever a frozen term contains is frozen. -/
theorem WithinComplement.trans (hx : WithinComplement T ℓ x) (hxy : ContainsOrEq x y) :
    WithinComplement T ℓ y :=
  let ⟨z, hz, hc, hzx⟩ := hx
  ⟨z, hz, hc, hzx.trans hxy⟩

theorem WithinComplement.cCommands (h : WithinComplement T ℓ x) : T.CCommands (leaf ℓ) x :=
  let ⟨z, hz, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzx⟩ := h
  ⟨z, hz, ⟨m, hm, hmℓ, hmz, hne.symm⟩, hzx⟩

theorem IsPhaseHead.mono {T' : SyntacticObject} (h : IsPhaseHead T ℓ)
    (hT : T.terms ⊆ T'.terms) : IsPhaseHead T' ℓ :=
  let ⟨m, hm, hℓ, hmℓ⟩ := h
  ⟨m, hT hm, hℓ, hmℓ⟩

theorem IsComplementOf.mono {T' : SyntacticObject} (h : IsComplementOf T ℓ z)
    (hT : T.terms ⊆ T'.terms) : IsComplementOf T' ℓ z :=
  let ⟨m, hm, hrest⟩ := h
  ⟨m, hT hm, hrest⟩

/-- A phase keeps its terms as structure is built above it. -/
theorem WithinProjection.mono {T' : SyntacticObject} (h : WithinProjection T ℓ x)
    (hT : T.terms ⊆ T'.terms) : WithinProjection T' ℓ x :=
  let ⟨p, hp, hrest⟩ := h
  ⟨p, hT hp, hrest⟩

theorem WithinComplement.mono {T' : SyntacticObject} (h : WithinComplement T ℓ x)
    (hT : T.terms ⊆ T'.terms) : WithinComplement T' ℓ x :=
  let ⟨z, hz, hc, hzx⟩ := h
  ⟨z, hT hz, hc.mono hT, hzx⟩

theorem IsComplementOf.withinComplement (h : IsComplementOf T ℓ z) : WithinComplement T ℓ z :=
  ⟨z, h.mem_terms, h, .refl⟩

/-- A term headed by `ℓ` contains the leaf of `ℓ`. -/
theorem leaf_mem_terms_of_raisingHead {s : SyntacticObject} (hℓ : ℓ ≠ .bareTrace)
    (h : s.raisingHead = some ℓ) : leaf ℓ ∈ s.terms := by
  induction s using SyntacticObject.ind with
  | leaf a => simp_all
  | trace => exact absurd (by simpa using h.symm) hℓ
  | traceOf a => simp at h
  | merge l r ihl ihr =>
    rw [terms_merge]
    exact Multiset.mem_cons_of_mem <| Multiset.mem_add.2 <|
      (raisingHead_merge h).imp ihl ihr

/-- The head of a phase lies in the phase. -/
theorem IsPhaseHead.withinProjection_leaf (h : IsPhaseHead T ℓ) : WithinProjection T ℓ (leaf ℓ) :=
  let ⟨m, hm, hℓ, hmℓ⟩ := h
  ⟨m, hm, hℓ, .single hmℓ⟩

@[simp] theorem mem_phase : x ∈ T.phase ℓ ↔ WithinProjection T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinProjection.mem_terms)

@[simp] theorem mem_phaseInterior : x ∈ T.phaseInterior ℓ ↔ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinComplement.mem_terms)

@[simp] theorem mem_phaseEdge :
    x ∈ T.phaseEdge ℓ ↔ WithinProjection T ℓ x ∧ ¬ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_congr mem_phase (not_congr mem_phaseInterior))

theorem isPhaseHead_iff_exists_isComplementOf : IsPhaseHead T ℓ ↔ ∃ z, IsComplementOf T ℓ z := by
  refine ⟨fun ⟨m, hm, hℓ, hmℓ⟩ ↦ ?_, fun ⟨_, m, hm, hℓ, hmℓ, _⟩ ↦ ⟨m, hm, hℓ, hmℓ⟩⟩
  induction m using SyntacticObject.ind with
  | leaf => simp at hmℓ
  | trace => simp at hmℓ
  | traceOf => simp at hmℓ
  | merge l r _ _ =>
    rcases (immediatelyContains_merge _ _ _).1 hmℓ with rfl | rfl
    · exact ⟨r, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩
    · exact ⟨l, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩

/-- A lexical item heads a phase exactly when it heads a term other than its leaf: the terms it
heads run down to the mother of the leaf ([marcolli-chomsky-berwick-2025], Lemma 1.14.1 and
(1.14.1)). -/
theorem isPhaseHead_iff_exists_raisingHead (hℓ : ℓ ≠ .bareTrace) :
    IsPhaseHead T ℓ ↔ ∃ p ∈ T.terms, p.raisingHead = some ℓ ∧ p ≠ leaf ℓ := by
  refine ⟨fun ⟨m, hm, h, hmℓ⟩ ↦ ⟨m, hm, h, by rintro rfl; simp at hmℓ⟩, fun ⟨p, hp, h, hne⟩ ↦ ?_⟩
  induction p using SyntacticObject.ind with
  | leaf a => simp_all
  | trace => exact absurd (by simpa using h.symm) hℓ
  | traceOf a => simp at h
  | merge l r ihl ihr =>
    obtain ⟨hl, hr⟩ := mem_terms_of_merge_mem_terms hp
    rcases raisingHead_merge h with h' | h'
    · by_cases hl' : l = leaf ℓ
      · exact ⟨_, hp, h, by simp [hl']⟩
      · exact ihl hl h' hl'
    · by_cases hr' : r = leaf ℓ
      · exact ⟨_, hp, h, by simp [hr']⟩
      · exact ihr hr h' hr'

/-- A head projects exactly when its phase has a nonempty interior. -/
theorem isPhaseHead_iff_phaseInterior_ne_zero : IsPhaseHead T ℓ ↔ T.phaseInterior ℓ ≠ 0 := by
  rw [isPhaseHead_iff_exists_isComplementOf]
  refine ⟨fun ⟨z, hz⟩ h0 ↦ Multiset.filter_eq_nil.1 h0 z hz.mem_terms ⟨z, hz.mem_terms, hz, .refl⟩,
    fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨z, -, hz, -⟩ := mem_phaseInterior.1 hx
  exact ⟨z, hz⟩

theorem phaseInterior_le_phase : T.phaseInterior ℓ ≤ T.phase ℓ :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.withinProjection

/-- The interior and the edge partition the phase. -/
theorem phaseInterior_add_phaseEdge : T.phaseInterior ℓ + T.phaseEdge ℓ = T.phase ℓ := by
  conv_rhs => rw [← Multiset.filter_add_not (· ∈ T.phaseInterior ℓ) (T.phase ℓ)]
  congr 1
  rw [phase, Multiset.filter_filter]
  exact Multiset.filter_congr fun _ _ ↦ by
    grind [mem_phaseInterior, WithinComplement.withinProjection]

/-- A phase head that occurs once lies in the edge of its phase, not in its interior
([marcolli-chomsky-berwick-2025], Remark 1.14.4). -/
theorem IsPhaseHead.leaf_mem_phaseEdge (h : IsPhaseHead T ℓ) (h1 : T.terms.count (leaf ℓ) ≤ 1) :
    leaf ℓ ∈ T.phaseEdge ℓ := by
  refine mem_phaseEdge.2 ⟨h.withinProjection_leaf, fun ⟨z, _, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzℓ⟩ ↦ ?_⟩
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

theorem phaseInterior_le_cCommandDomain : T.phaseInterior ℓ ≤ T.cCommandDomain (leaf ℓ) :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.cCommands

/-- The interior of a head that projects wherever it occurs is its c-command domain. -/
theorem phaseInterior_eq_cCommandDomain
    (h : ∀ m ∈ T.terms, ImmediatelyContains m (leaf ℓ) → m.raisingHead = some ℓ) :
    T.phaseInterior ℓ = T.cCommandDomain (leaf ℓ) :=
  Multiset.filter_congr fun _ _ ↦ by
    grind [WithinComplement, IsComplementOf, CCommands, Sisters]

/-! ### The Phase Impenetrability Condition -/

variable (T) in
/-- `goal` is accessible to `probe` in `T` under the condition `s`, the phase heads being `heads`.
A goal within the complement of a phase head `H` is reachable from within the phase of `H`
([chomsky-2001], (7)), and under the weaker condition also by a probe within the complement of
every phase head `Z` whose complement contains `H`, the stages before the operations at ZP
([chomsky-2001], (8), (11)). -/
def Accessible (heads : List LexicalItem.Token) :
    Impenetrability → SyntacticObject → SyntacticObject → Prop
  | .phase, probe, goal => ∀ H ∈ heads, T.WithinComplement H goal → T.WithinProjection H probe
  | .nextPhase, probe, goal => ∀ H ∈ heads, T.WithinComplement H goal →
      T.WithinProjection H probe ∨
        ∀ Z ∈ heads, T.WithinComplement Z (leaf H) → T.WithinComplement Z probe

instance (heads : List LexicalItem.Token) (s : Impenetrability) (probe goal : SyntacticObject) :
    Decidable (T.Accessible heads s probe goal) := by
  cases s <;> dsimp only [Accessible] <;> infer_instance

variable {heads : List LexicalItem.Token} {probe goal : SyntacticObject}

/-- [chomsky-2000]'s condition is the stronger: what it leaves accessible, [chomsky-2001]'s does
too. -/
theorem Accessible.nextPhase_of_phase (h : T.Accessible heads .phase probe goal) :
    T.Accessible heads .nextPhase probe goal :=
  fun H hH hg ↦ .inl (h H hH hg)

/-- A goal outside the interior of every phase head is accessible to every probe. -/
theorem Accessible.of_forall_not_withinComplement {s : Impenetrability}
    (h : ∀ H ∈ heads, ¬ T.WithinComplement H goal) : T.Accessible heads s probe goal := by
  cases s <;> exact fun H hH hg ↦ absurd hg (h H hH)

/-- Fewer phase heads seal less. -/
theorem Accessible.anti {heads' : List LexicalItem.Token} {s : Impenetrability}
    (h : T.Accessible heads s probe goal) (hsub : heads' ⊆ heads) :
    T.Accessible heads' s probe goal := by
  cases s
  · exact fun H hH hg ↦ h H (hsub hH) hg
  · exact fun H hH hg ↦ (h H (hsub hH) hg).imp_right fun hz Z hZ ↦ hz Z (hsub hZ)

end SyntacticObject

end Minimalist
