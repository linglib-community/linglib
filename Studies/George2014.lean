/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott, Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.UniversalInference
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.NumberTree
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# George (2014): Some remarks on certain trivalent accounts of presupposition projection

George relates trivalent accounts of presupposition projection to Heim's dynamic one, and derives
Peters' Middle Kleene connectives, answering Schlenker's explanatory challenge, by deploying
classical truth functions one argument at a time. Deployed on a quantifier, *every student has
stopped smoking* [entails that every student has
smoked](##George2014.Det.every_universalEntailment) without [presupposing
it](##George2014.Det.not_every_universalAntiEntailment). A quantity-invariant quantifier has a
universal entailment when it is [true of no two consecutive
numbers](##George2014.universalEntailment_iff_trueOf), and a conservative determiner when [its tree
holds at no two neighbouring points](##George2014.Det.universalEntailment_iff_ofDet). Few
quantifiers pass: a monotone one with a universal entailment is `∀` or trivially false, and one
with a universal presupposition is [*an even number of things* or *an odd number of
things*](##George2014.UniversalPresupposition.eq_even_or_eq_odd).

## Implementation notes

The update map from trivalent propositions to Heim's updates is in
`Linglib.Semantics.Dynamic.Partial`, deployment and the connectives it derives in
`Linglib.Logic.Trivalent.Deployment`, and the single-step characterization of universal inferences
in `Linglib.Logic.Trivalent.UniversalInference`. George states his results for quantity-invariant
quantifiers and conservative ones on a finite non-empty universe. The monotone remarks here need
neither quantity invariance nor finiteness, and the parity remarks need finiteness but not quantity
invariance. The reading of universal entailments and presuppositions on the Hasse diagram of
`Set α` is not George's, who argues by counting.

## TODO

* Integrate George's isomorphism between Heim's updates and trivalent propositions, already
  formalized as `CCP.Partial.ofTrivalentEquiv` in `Linglib.Semantics.Dynamic.Partial`.
* George's comparison with the experiments of Chemla, importing `Chemla2009a`: deployment derives
  entailments for *exactly three* (note 26), where Chemla finds rates like those of the
  existentials.

## References

* [george-2014]
* [chemla-2009a]
-/

@[expose] public section

namespace George2014

open Quantifier Quantifier.Det SimpleGraph
open Trivalent hiding UniversalEntailment UniversalAntiEntailment UniversalPresupposition

variable {α : Type*} {Q : Quantifier α}

/-! ### Universal inferences of a quantifier: Definitions 20–22 -/

/-- A quantifier has a universal entailment when its deployment on a trivalent predicate is true
only if the predicate is defined everywhere (Definition 20). -/
def UniversalEntailment (Q : Quantifier α) : Prop :=
  Trivalent.UniversalEntailment Set.univ (deployQuantifier Q)

/-- A quantifier has a universal anti-entailment when its deployment on a trivalent predicate is
false only if the predicate is defined everywhere (Definition 21). -/
def UniversalAntiEntailment (Q : Quantifier α) : Prop :=
  Trivalent.UniversalAntiEntailment Set.univ (deployQuantifier Q)

/-- A quantifier has a universal presupposition when it has a universal entailment and a universal
anti-entailment (Definition 22). -/
def UniversalPresupposition (Q : Quantifier α) : Prop :=
  UniversalEntailment Q ∧ UniversalAntiEntailment Q

theorem universalEntailment_iff :
    UniversalEntailment Q ↔ ∀ B a, a ∉ B → ¬ (Q B ∧ Q (insert a B)) :=
  (Trivalent.universalEntailment_deployQuantifier_iff (R := Set.univ)).trans (by simp)

theorem universalAntiEntailment_iff :
    UniversalAntiEntailment Q ↔ ∀ B a, a ∉ B → ¬ (¬ Q B ∧ ¬ Q (insert a B)) :=
  (Trivalent.universalAntiEntailment_deployQuantifier_iff (R := Set.univ)).trans (by simp)

theorem universalAntiEntailment_iff_compl : UniversalAntiEntailment Q ↔ UniversalEntailment Qᶜ :=
  Trivalent.universalAntiEntailment_deployQuantifier_iff_compl

theorem universalPresupposition_iff :
    UniversalPresupposition Q ↔ ∀ B a, a ∉ B → (Q (insert a B) ↔ ¬ Q B) :=
  (Trivalent.universalPresupposition_deployQuantifier_iff (R := Set.univ)).trans (by simp)

/-! ### Counting: Propositions 4 and 6 -/

/-- A quantifier is true of `n` when it holds of some set of `n` elements, and false of `n` when its
complement is true of `n`. Under quantity invariance on a finite universe this is Definition 23
(`trueOf_ncard_iff`). -/
def TrueOf (Q : Quantifier α) (n : ℕ) : Prop := ∃ B : Set α, B.ncard = n ∧ Q B

theorem trueOf_ncard_iff [Finite α] (hQ : Q.QuantityInvariant) (B : Set α) :
    TrueOf Q B.ncard ↔ Q B :=
  ⟨fun ⟨_, hB, h⟩ ↦ (hQ.iff_of_ncard_eq hB).1 h, fun h ↦ ⟨B, rfl, h⟩⟩

/-- A quantity-invariant quantifier on a finite universe has a universal entailment exactly when it
is true of no two consecutive numbers (Proposition 4). -/
theorem universalEntailment_iff_trueOf [Finite α] (hQ : Q.QuantityInvariant) :
    UniversalEntailment Q ↔ ∀ n, ¬ (TrueOf Q n ∧ TrueOf Q (n + 1)) := by
  rw [universalEntailment_iff]
  constructor
  · rintro h n ⟨⟨B₁, hB₁, h₁⟩, B₂, hB₂, h₂⟩
    obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (s := B₂) (by omega)
    refine h (B₂ \ {a}) a (by simp) ⟨(hQ.iff_of_ncard_eq ?_).1 h₁, ?_⟩
    · rw [Set.ncard_sdiff_singleton_of_mem ha]; omega
    · rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem ha]
  · rintro h B a ha ⟨h₁, h₂⟩
    exact h B.ncard ⟨⟨B, rfl, h₁⟩, insert a B, Set.ncard_insert_of_notMem ha, h₂⟩

-- Proposition 6
theorem universalAntiEntailment_iff_trueOf [Finite α] (hQ : Q.QuantityInvariant) :
    UniversalAntiEntailment Q ↔ ∀ n, ¬ (TrueOf Qᶜ n ∧ TrueOf Qᶜ (n + 1)) := by
  rw [universalAntiEntailment_iff_compl, universalEntailment_iff_trueOf hQ.compl]

/-! ### Monotone quantifiers: Remarks 13, 15, 17 and 19 -/

-- Remark 13
theorem UniversalEntailment.eq_bot_or_eq_univ (h : UniversalEntailment Q) (hm : Monotone Q) :
    Q = ⊥ ∨ Q = (· = Set.univ) := by
  have hQ : ∀ B, Q B → B = Set.univ := fun B hB ↦ by
    by_contra hne
    obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem B).1 hne
    exact universalEntailment_iff.1 h B a ha ⟨hB, hm (Set.subset_insert a B) hB⟩
  by_cases hu : Q Set.univ
  · exact .inr (funext fun B ↦ propext ⟨hQ B, fun e ↦ e ▸ hu⟩)
  · exact .inl (funext fun B ↦ propext ⟨fun hB ↦ hu (hQ B hB ▸ hB), False.elim⟩)

-- Remark 15
theorem UniversalEntailment.eq_bot_or_eq_empty (h : UniversalEntailment Q) (hm : Antitone Q) :
    Q = ⊥ ∨ Q = (· = ∅) := by
  have hQ : ∀ B, Q B → B = ∅ := fun B hB ↦ by
    by_contra hne
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hB' : Q (B \ {a}) := hm Set.sdiff_subset hB
    exact universalEntailment_iff.1 h (B \ {a}) a (by simp)
      ⟨hB', by rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem ha]⟩
  by_cases he : Q ∅
  · exact .inr (funext fun B ↦ propext ⟨hQ B, fun e ↦ e ▸ he⟩)
  · exact .inl (funext fun B ↦ propext ⟨fun hB ↦ he (hQ B hB ▸ hB), False.elim⟩)

-- Remark 17
theorem UniversalAntiEntailment.eq_top_or_nonempty (h : UniversalAntiEntailment Q)
    (hm : Monotone Q) : Q = ⊤ ∨ Q = Set.Nonempty := by
  rw [universalAntiEntailment_iff_compl] at h
  rcases h.eq_bot_or_eq_empty fun _ _ hBC hB hC ↦ hB (hm hBC hC) with e | e
  · exact .inl (compl_injective (by rw [e, compl_top]))
  · refine .inr (funext fun B ↦ propext ?_)
    have : (¬ Q B) = (B = ∅) := congrFun e B
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← this, not_not]

-- Remark 19
theorem UniversalAntiEntailment.eq_top_or_ne_univ (h : UniversalAntiEntailment Q)
    (hm : Antitone Q) : Q = ⊤ ∨ Q = (· ≠ Set.univ) := by
  rw [universalAntiEntailment_iff_compl] at h
  rcases h.eq_bot_or_eq_univ fun _ _ hBC hB hC ↦ hB (hm hBC hC) with e | e
  · exact .inl (compl_injective (by rw [e, compl_top]))
  · refine .inr (funext fun B ↦ propext ?_)
    have : (¬ Q B) = (B = Set.univ) := congrFun e B
    rw [ne_eq, ← this, not_not]

/-! ### Parity: Remark 21 -/

/-- A quantifier on a finite universe with a universal presupposition is *an even number of
things* or *an odd number of things* (Remark 21). -/
theorem UniversalPresupposition.eq_even_or_eq_odd [Finite α] (h : UniversalPresupposition Q) :
    Q = (fun B ↦ Even B.ncard) ∨ Q = (fun B ↦ Odd B.ncard) := by
  have hstep := universalPresupposition_iff.1 h
  have key : ∀ B : Set α, Q B ↔ (Q ∅ ↔ Even B.ncard) := fun B ↦ by
    induction B, B.toFinite using Set.Finite.induction_on with
    | empty => simp
    | @insert a B ha hB ih =>
      rw [hstep B a ha, ih, Set.ncard_insert_of_notMem ha hB, Nat.even_add_one]
      tauto
  by_cases he : Q ∅
  · exact .inl (funext fun B ↦ propext (by rw [key B]; tauto))
  · exact .inr (funext fun B ↦ propext (by rw [key B, ← Nat.not_even_iff_odd]; tauto))

/-! ### The Hasse diagram of `Set α` -/

-- Not George's: Definition 20 as independence in the Hasse diagram of `Set α`
theorem universalEntailment_iff_isIndepSet :
    UniversalEntailment Q ↔ (hasse (Set α)).IsIndepSet Q := by
  rw [universalEntailment_iff]
  constructor
  · intro h B hB C hC _ hadj
    rcases hasse_adj.1 hadj with e | e
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e
      exact h B a ha ⟨hB, hC⟩
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e
      exact h C a ha ⟨hC, hB⟩
  · rintro h B a ha ⟨hB, hC⟩
    have e := Set.covBy_insert ha
    exact h hB hC e.ne (hasse_adj.2 (.inl e))

-- Not George's: Definition 22 as a proper 2-colouring of the Hasse diagram of `Set α`
theorem universalPresupposition_iff_exists_coloring :
    UniversalPresupposition Q ↔ ∃ c : (hasse (Set α)).Coloring Prop, ⇑c = Q := by
  rw [universalPresupposition_iff]
  constructor
  · intro h
    refine ⟨Coloring.mk Q fun {B C} hadj e ↦ ?_, rfl⟩
    rcases hasse_adj.1 hadj with e' | e'
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e'
      have := h B a ha
      simp_all
    · obtain ⟨a, ha, rfl⟩ := Set.covBy_iff_exists_insert.1 e'
      have := h C a ha
      simp_all
  · rintro ⟨c, rfl⟩ B a ha
    have h := c.valid (hasse_adj.2 (.inl (Set.covBy_insert ha)))
    by_cases hB : c B <;> by_cases hC : c (insert a B) <;> simp_all

/-! ### Universal inferences of a determiner: Definitions 20–22 -/

namespace Det

variable {d : Det α}

open Classical in
/-- A determiner has a universal entailment when its deployment with a classical restrictor `R` is
true only if the nuclear scope is defined throughout `R` (Definition 20). -/
def UniversalEntailment (d : Det α) : Prop :=
  ∀ R : Set α, Trivalent.UniversalEntailment R (deployDeterminer d fun a ↦ ofProp (a ∈ R))

open Classical in
/-- A determiner has a universal anti-entailment when its deployment with a classical restrictor `R`
is false only if the nuclear scope is defined throughout `R` (Definition 21). -/
def UniversalAntiEntailment (d : Det α) : Prop :=
  ∀ R : Set α, Trivalent.UniversalAntiEntailment R (deployDeterminer d fun a ↦ ofProp (a ∈ R))

/-- A determiner has a universal presupposition when it has a universal entailment and a universal
anti-entailment (Definition 22). -/
def UniversalPresupposition (d : Det α) : Prop :=
  UniversalEntailment d ∧ UniversalAntiEntailment d

open Classical in
private theorem deployDeterminer_ofProp_eq (d : Det α) (R : Set α) :
    (deployDeterminer d fun a ↦ ofProp (a ∈ R)) = deployQuantifier (d R) :=
  funext (deployDeterminer_ofProp_left d R)

theorem universalEntailment_iff :
    UniversalEntailment d ↔ ∀ R B, ∀ a ∈ R, a ∉ B → ¬ (d R B ∧ d R (insert a B)) :=
  forall_congr' fun R ↦ by
    rw [deployDeterminer_ofProp_eq]
    exact Trivalent.universalEntailment_deployQuantifier_iff

theorem universalAntiEntailment_iff :
    UniversalAntiEntailment d ↔ ∀ R B, ∀ a ∈ R, a ∉ B → ¬ (¬ d R B ∧ ¬ d R (insert a B)) :=
  forall_congr' fun R ↦ by
    rw [deployDeterminer_ofProp_eq]
    exact Trivalent.universalAntiEntailment_deployQuantifier_iff

theorem universalAntiEntailment_iff_compl : UniversalAntiEntailment d ↔ UniversalEntailment dᶜ := by
  rw [universalAntiEntailment_iff, universalEntailment_iff]; rfl

theorem universalPresupposition_iff :
    UniversalPresupposition d ↔ ∀ R B, ∀ a ∈ R, a ∉ B → (d R (insert a B) ↔ ¬ d R B) := by
  rw [UniversalPresupposition, universalEntailment_iff, universalAntiEntailment_iff]
  refine ⟨fun h R B a haR ha ↦ ?_, fun h ↦ ⟨fun R B a haR ha ↦ ?_, fun R B a haR ha ↦ ?_⟩⟩
  · have := h.1 R B a haR ha; have := h.2 R B a haR ha; tauto
  · have := h R B a haR ha; tauto
  · have := h R B a haR ha; tauto

/-! ### Counting: Propositions 5 and 7 -/

open NumberTree in
/-- A conservative, quantity-invariant determiner on a finite universe has a universal entailment
exactly when its tree holds at no two points `(m + 1, n)` and `(m, n + 1)` (Proposition 5). -/
theorem universalEntailment_iff_ofDet [Finite α] (hC : d.Conservative)
    (hQ : d.QuantityInvariant) :
    UniversalEntailment d ↔ ∀ m n, ¬ (ofDet d (m + 1) n ∧ ofDet d m (n + 1)) := by
  rw [universalEntailment_iff]
  constructor
  · rintro h m n ⟨⟨R, B, hd, hi, h₁⟩, R₂, B₂, hd₂, hi₂, h₂⟩
    obtain ⟨a, haR, haB⟩ := Set.nonempty_of_ncard_ne_zero (s := R \ B) (by omega)
    have haRB : a ∈ R \ B := ⟨haR, haB⟩
    refine h R B a haR haB ⟨h₁, (Det.iff_of_ncard_eq hC hQ ?_ ?_).1 h₂⟩
    · rw [hd₂, Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff,
        Set.ncard_sdiff_singleton_of_mem haRB, hd]; rfl
    · rw [hi₂, Set.inter_insert_of_mem haR, Set.ncard_insert_of_notMem (fun h ↦ haB h.2), hi]
  · rintro h R B a haR haB ⟨h₁, h₂⟩
    have haRB : a ∈ R \ B := ⟨haR, haB⟩
    refine h (R \ insert a B).ncard (R ∩ B).ncard ⟨⟨R, B, ?_, rfl, h₁⟩, R, insert a B, rfl, ?_, h₂⟩
    · rw [Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff, Set.ncard_sdiff_singleton_of_mem haRB]
      have : 0 < (R \ B).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨a, haR, haB⟩
      omega
    · rw [Set.inter_insert_of_mem haR, Set.ncard_insert_of_notMem (fun h ↦ haB h.2)]

open NumberTree in
-- Proposition 7
theorem universalAntiEntailment_iff_ofDet [Finite α] (hC : d.Conservative)
    (hQ : d.QuantityInvariant) :
    UniversalAntiEntailment d ↔ ∀ m n, ¬ (ofDet dᶜ (m + 1) n ∧ ofDet dᶜ m (n + 1)) := by
  rw [universalAntiEntailment_iff_compl]
  exact universalEntailment_iff_ofDet (fun A B ↦ not_congr (hC A B))
    fun σ A B ↦ not_congr (hQ σ A B)

/-! ### Monotone determiners: Remarks 14, 16, 18 and 20 -/

-- Remark 14
theorem UniversalEntailment.eq_bot_or_every (h : UniversalEntailment d) (hC : d.Conservative)
    (hm : d.ScopeMonotone) (R : Set α) : d R = ⊥ ∨ d R = every R := by
  have hR : ∀ B, d R B → R ⊆ B := fun B hB a haR ↦ by
    by_contra haB
    exact universalEntailment_iff.1 h R B a haR haB ⟨hB, hm R (Set.subset_insert a B) hB⟩
  have key : ∀ B, d R B ↔ d R R ∧ R ⊆ B := fun B ↦
    ⟨fun hB ↦ ⟨by simpa [Set.inter_eq_left.2 (hR B hB)] using (hC R B).1 hB, hR B hB⟩,
      fun ⟨hRR, hRB⟩ ↦ (hC R B).2 (by rwa [Set.inter_eq_left.2 hRB])⟩
  by_cases hRR : d R R
  · exact .inr (funext fun B ↦ propext (by rw [key]; exact and_iff_right hRR))
  · exact .inl (funext fun B ↦ propext (by rw [key]; simp [hRR]))

-- Remark 16
theorem UniversalEntailment.eq_bot_or_no (h : UniversalEntailment d) (hC : d.Conservative)
    (hm : d.ScopeAntitone) (R : Set α) : d R = ⊥ ∨ d R = no R := by
  have hR : ∀ B, d R B → R ∩ B = ∅ := fun B hB ↦ by
    by_contra hne
    obtain ⟨a, haR, haB⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact universalEntailment_iff.1 h R (B \ {a}) a haR (by simp)
      ⟨hm R Set.sdiff_subset hB, by rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem haB]⟩
  have key : ∀ B, d R B ↔ d R ∅ ∧ R ∩ B = ∅ := fun B ↦
    ⟨fun hB ↦ ⟨by simpa [hR B hB] using (hC R B).1 hB, hR B hB⟩,
      fun ⟨h0, hRB⟩ ↦ (hC R B).2 (by rwa [hRB])⟩
  have hno : ∀ B, no R B ↔ R ∩ B = ∅ := fun B ↦ by
    simp [no, Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty]
  by_cases h0 : d R ∅
  · exact .inr (funext fun B ↦ propext (by rw [key, hno]; exact and_iff_right h0))
  · exact .inl (funext fun B ↦ propext (by rw [key]; simp [h0]))

-- Remark 18
theorem UniversalAntiEntailment.eq_top_or_some (h : UniversalAntiEntailment d)
    (hC : d.Conservative) (hm : d.ScopeMonotone) (R : Set α) :
    d R = ⊤ ∨ d R = Det.some R := by
  rw [universalAntiEntailment_iff_compl] at h
  rcases h.eq_bot_or_no (fun A B ↦ not_congr (hC A B))
    (fun A _ _ hBC hB hC' ↦ hB (hm A hBC hC')) R with e | e
  · exact .inl (funext fun B ↦ propext (by simpa using congrFun e B))
  · refine .inr (funext fun B ↦ propext ?_)
    have : (¬ d R B) = no R B := congrFun e B
    refine not_iff_not.1 ?_
    rw [this, no, Det.some, Set.subset_compl_iff_disjoint_right, Set.not_nonempty_iff_eq_empty,
      Set.disjoint_iff_inter_eq_empty]

-- Remark 20
theorem UniversalAntiEntailment.eq_top_or_notEvery (h : UniversalAntiEntailment d)
    (hC : d.Conservative) (hm : d.ScopeAntitone) (R : Set α) :
    d R = ⊤ ∨ d R = everyᶜ R := by
  rw [universalAntiEntailment_iff_compl] at h
  rcases h.eq_bot_or_every (fun A B ↦ not_congr (hC A B))
    (fun A _ _ hBC hB hC' ↦ hB (hm A hBC hC')) R with e | e
  · exact .inl (funext fun B ↦ propext (by simpa using congrFun e B))
  · refine .inr (funext fun B ↦ propext ?_)
    have : (¬ d R B) = every R B := congrFun e B
    change d R B ↔ ¬ every R B
    rw [← this, not_not]

/-! ### Parity: Remark 22 -/

theorem UniversalPresupposition.iff_even [Finite α] (h : UniversalPresupposition d)
    (hC : d.Conservative) (R B : Set α) : d R B ↔ (d R ∅ ↔ Even (R ∩ B).ncard) := by
  have hstep := universalPresupposition_iff.1 h
  have key : ∀ C : Set α, C ⊆ R → (d R C ↔ (d R ∅ ↔ Even C.ncard)) := fun C ↦ by
    induction C, C.toFinite using Set.Finite.induction_on with
    | empty => simp
    | @insert a C ha hC ih =>
      intro hCR
      rw [hstep R C a (hCR (Set.mem_insert a C)) ha, ih ((Set.subset_insert a C).trans hCR),
        Set.ncard_insert_of_notMem ha hC, Nat.even_add_one]
      tauto
  rw [hC, key _ Set.inter_subset_left]

-- Remark 22
theorem UniversalPresupposition.eq_even_or_eq_odd [Finite α] (h : UniversalPresupposition d)
    (hC : d.Conservative) (R : Set α) :
    d R = (fun B ↦ Even (R ∩ B).ncard) ∨ d R = (fun B ↦ Odd (R ∩ B).ncard) := by
  by_cases he : d R ∅
  · exact .inl (funext fun B ↦ propext (by rw [h.iff_even hC]; tauto))
  · exact .inr (funext fun B ↦ propext (by rw [h.iff_even hC, ← Nat.not_even_iff_odd]; tauto))

/-! ### *Every* -/

/-- *Every* has a universal entailment: *every student has stopped smoking* entails that every
student has smoked. -/
theorem every_universalEntailment : UniversalEntailment (every : Det α) :=
  universalEntailment_iff.2 fun _ _ _ haR haB h ↦ haB (h.1 haR)

/-- On a universe of two or more, *every* has no universal anti-entailment, so no universal
presupposition: *every student has stopped smoking* is false when one student smokes and another
never smoked. -/
theorem not_every_universalAntiEntailment [Nontrivial α] :
    ¬ UniversalAntiEntailment (every : Det α) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine fun h ↦ universalAntiEntailment_iff.1 h {a, b} ∅ a (by simp) (by simp) ⟨?_, ?_⟩
  · exact fun hs ↦ hs (Set.mem_insert a {b})
  · intro hs
    have := hs (Set.mem_insert_of_mem a rfl)
    simp only [insert_empty_eq, Set.mem_singleton_iff] at this
    exact hab this.symm

end Det

end George2014
