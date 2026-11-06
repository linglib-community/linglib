/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.QuantifierDeployment
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.NumberTree

/-!
# Universal inferences under Peters-Kleene deployment

Under Peters-Kleene deployment *every student has stopped smoking* entails that every student has
smoked without presupposing it ([george-2014] §4.2; `Quantifier.Det.every_universalEntailment`,
`Quantifier.Det.not_every_universalAntiEntailment`). A quantifier has a universal entailment when
its deployment on a trivalent predicate is true only if the predicate is defined throughout the
domain, a universal anti-entailment when its deployment is false only then, and a universal
presupposition when it has both (Definitions 20–22). A determiner has them when its deployment
with a classical restrictor does, the domain being the restrictor.

Whether a quantifier has a universal entailment turns on single steps. Its deployment on the
predicate that is true on `B`, undefined at one `a ∉ B` and false elsewhere is true exactly when
it holds of `B` and of `insert a B`, and any predicate undefined at `a` has repairs true on its
positive extension `B` and on `insert a B` (`Trivalent.forall_repairs_imp_iff`). So a quantifier
has a universal entailment exactly when it never holds of both a set and the set with one more
element (`Quantifier.universalEntailment_iff`), and a determiner when it never does so with the
added element in the restrictor (`Quantifier.Det.universalEntailment_iff`). For a
quantity-invariant quantifier on a finite universe the condition is that it is true of no two
consecutive numbers (Proposition 4), and for a conservative quantity-invariant determiner that its
tree holds at no two points `(m + 1, n)` and `(m, n + 1)` (Proposition 5); anti-entailments are
entailments of the complement (Propositions 6 and 7).

Few quantifiers pass. A monotone quantifier with a universal entailment is `∀` or trivially false,
and an antitone one is `¬∃` or trivially false; with a universal anti-entailment they are `∃` or
`¬∀`, or trivially true (Remarks 13–20). A quantifier with a universal presupposition alternates
with each added element, so it is *an even number of things* or *an odd number of things*
(Remarks 21 and 22).

The single-step characterization needs neither quantity invariance nor finiteness, so the
monotone remarks hold of every quantifier and every conservative determiner, and the parity
remarks of every such one on a finite universe; [george-2014] states them for quantity-invariant
ones.

## Main definitions

* `Quantifier.toBool`, `Quantifier.Det.toBool`: a quantifier or determiner as a function of
  characteristic functions, as deployment takes it.
* `Quantifier.UniversalEntailment`, `Quantifier.UniversalAntiEntailment`,
  `Quantifier.UniversalPresupposition`: Definitions 20–22 for a quantifier of one argument.
* `Quantifier.Det.UniversalEntailment`, `Quantifier.Det.UniversalAntiEntailment`,
  `Quantifier.Det.UniversalPresupposition`: Definitions 20–22 for a determiner.
* `Quantifier.TrueOf`: a quantifier is true of `n` when it holds of a set of `n` elements
  (Definition 23); `Quantifier.NumberTree.ofDet` is Definition 24.

## Main results

* `Quantifier.universalEntailment_iff`, `Quantifier.Det.universalEntailment_iff`,
  `Quantifier.universalPresupposition_iff`, `Quantifier.Det.universalPresupposition_iff`: a
  universal entailment is the absence of a single step between two sets the quantifier holds of,
  and a universal presupposition is a quantifier that flips at every step.
* `Quantifier.Det.every_universalEntailment`, `Quantifier.Det.not_every_universalAntiEntailment`:
  *every* has a universal entailment but, on a universe of two or more, no universal
  presupposition.
* `Quantifier.universalEntailment_iff_trueOf`, `Quantifier.Det.universalEntailment_iff_ofDet`,
  `Quantifier.universalAntiEntailment_iff_trueOf`,
  `Quantifier.Det.universalAntiEntailment_iff_ofDet`: Propositions 4–7.
* `Quantifier.UniversalEntailment.eq_bot_or_eq_univ`,
  `Quantifier.UniversalEntailment.eq_bot_or_eq_empty`,
  `Quantifier.UniversalAntiEntailment.eq_top_or_nonempty`,
  `Quantifier.UniversalAntiEntailment.eq_top_or_ne_univ`: Remarks 13, 15, 17 and 19.
* `Quantifier.Det.UniversalEntailment.eq_bot_or_every`,
  `Quantifier.Det.UniversalEntailment.eq_bot_or_no`,
  `Quantifier.Det.UniversalAntiEntailment.eq_top_or_some`,
  `Quantifier.Det.UniversalAntiEntailment.eq_top_or_notEvery`: Remarks 14, 16, 18 and 20.
* `Quantifier.UniversalPresupposition.eq_even_or_eq_odd`,
  `Quantifier.Det.UniversalPresupposition.eq_even_or_eq_odd`: Remarks 21 and 22.

## References

* [george-2014]
-/

@[expose] public section

namespace Quantifier

open Trivalent Trivalent

variable {α : Type*}

/-! ### Quantifiers as functions of characteristic functions -/

open Classical in
/-- A quantifier as a function from characteristic functions to truth values, deciding the
quantifier classically. -/
noncomputable def toBool (Q : Quantifier α) : (α → Bool) → Bool :=
  fun g ↦ decide (Q {a | g a})

open Classical in
/-- A determiner as a function of two characteristic functions, deciding it classically. -/
noncomputable def Det.toBool (d : Det α) : (α → Bool) → (α → Bool) → Bool :=
  fun f g ↦ decide (d {a | f a} {a | g a})

/-- Fixing the first argument of a determiner gives the quantifier it makes of that set. -/
@[simp] theorem Det.toBool_apply (d : Det α) (f : α → Bool) :
    d.toBool f = (d {a | f a}).toBool :=
  rfl

/-- A deployed quantifier is true when it holds of every repair. -/
theorem deployQuantifier_toBool_eq_one_iff {Q : Quantifier α} {A : α → Trivalent} :
    deployQuantifier Q.toBool A = 1 ↔ ∀ g ∈ repairs A, Q {a | g a} := by
  simp [deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_true_iff, toBool]

/-- A deployed quantifier is false when it fails of every repair. -/
theorem deployQuantifier_toBool_eq_neg_one_iff {Q : Quantifier α} {A : α → Trivalent} :
    deployQuantifier Q.toBool A = -1 ↔ ∀ g ∈ repairs A, ¬ Q {a | g a} := by
  simp [deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_false_iff, toBool,
    repairs_nonempty A]


/-! ### Universal inferences of a quantifier -/

/-- A quantifier has a universal entailment when its deployment on a trivalent predicate is true
only if the predicate is defined everywhere (Definition 20). -/
def UniversalEntailment (Q : Quantifier α) : Prop :=
  ∀ A : α → Trivalent, deployQuantifier Q.toBool A = 1 → ∀ a, A a ≠ 0

/-- A quantifier has a universal anti-entailment when its deployment on a trivalent predicate is
false only if the predicate is defined everywhere (Definition 21). -/
def UniversalAntiEntailment (Q : Quantifier α) : Prop :=
  ∀ A : α → Trivalent, deployQuantifier Q.toBool A = -1 → ∀ a, A a ≠ 0

/-- A quantifier has a universal presupposition when it has a universal entailment and a
universal anti-entailment (Definition 22). -/
def UniversalPresupposition (Q : Quantifier α) : Prop :=
  Q.UniversalEntailment ∧ Q.UniversalAntiEntailment

variable {Q : Quantifier α}

/-- A quantifier has a universal entailment when it never holds of both a set and the set with
one more element. -/
theorem universalEntailment_iff :
    Q.UniversalEntailment ↔ ∀ B a, a ∉ B → ¬ (Q B ∧ Q (insert a B)) := by
  have := forall_repairs_imp_iff Q Set.univ
  simp only [Set.mem_univ, forall_const] at this
  simpa [UniversalEntailment, deployQuantifier_toBool_eq_one_iff] using this

/-- A quantifier has a universal anti-entailment when it never fails of both a set and the set
with one more element. -/
theorem universalAntiEntailment_iff :
    Q.UniversalAntiEntailment ↔ ∀ B a, a ∉ B → ¬ (¬ Q B ∧ ¬ Q (insert a B)) := by
  have := forall_repairs_imp_iff (fun B ↦ ¬ Q B) Set.univ
  simp only [Set.mem_univ, forall_const] at this
  simpa [UniversalAntiEntailment, deployQuantifier_toBool_eq_neg_one_iff] using this

theorem universalAntiEntailment_iff_compl :
    Q.UniversalAntiEntailment ↔ Qᶜ.UniversalEntailment := by
  rw [universalAntiEntailment_iff, universalEntailment_iff]; rfl

theorem universalPresupposition_iff :
    Q.UniversalPresupposition ↔ ∀ B a, a ∉ B → (Q (insert a B) ↔ ¬ Q B) := by
  rw [UniversalPresupposition, universalEntailment_iff, universalAntiEntailment_iff]
  refine ⟨fun h B a ha ↦ ?_, fun h ↦ ⟨fun B a ha ↦ ?_, fun B a ha ↦ ?_⟩⟩
  · have := h.1 B a ha; have := h.2 B a ha; tauto
  · have := h B a ha; tauto
  · have := h B a ha; tauto

/-! ### Counting: Propositions 4 and 6 -/

/-- A quantifier is true of `n` when it holds of some set of `n` elements, and false of `n` when its
complement is true of `n`. Under quantity invariance on a finite universe this is Definition 23
(`QuantityInvariant.trueOf_ncard_iff`). -/
def TrueOf (Q : Quantifier α) (n : ℕ) : Prop := ∃ B : Set α, B.ncard = n ∧ Q B

theorem QuantityInvariant.trueOf_ncard_iff [Finite α] (hQ : Q.QuantityInvariant) (B : Set α) :
    Q.TrueOf B.ncard ↔ Q B :=
  ⟨fun ⟨_, hB, h⟩ ↦ (hQ.iff_of_ncard_eq hB).1 h, fun h ↦ ⟨B, rfl, h⟩⟩

/-- A quantity-invariant quantifier on a finite universe has a universal entailment exactly when it
is true of no two consecutive numbers (Proposition 4). -/
theorem universalEntailment_iff_trueOf [Finite α] (hQ : Q.QuantityInvariant) :
    Q.UniversalEntailment ↔ ∀ n, ¬ (Q.TrueOf n ∧ Q.TrueOf (n + 1)) := by
  rw [universalEntailment_iff]
  constructor
  · rintro h n ⟨⟨B₁, hB₁, h₁⟩, B₂, hB₂, h₂⟩
    obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (s := B₂) (by omega)
    refine h (B₂ \ {a}) a (by simp) ⟨(hQ.iff_of_ncard_eq ?_).1 h₁, ?_⟩
    · rw [Set.ncard_sdiff_singleton_of_mem ha]; omega
    · rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem ha]
  · rintro h B a ha ⟨h₁, h₂⟩
    exact h B.ncard ⟨⟨B, rfl, h₁⟩, insert a B, Set.ncard_insert_of_notMem ha, h₂⟩

/-- A quantity-invariant quantifier on a finite universe has a universal anti-entailment exactly
when it is false of no two consecutive numbers (Proposition 6). -/
theorem universalAntiEntailment_iff_trueOf [Finite α] (hQ : Q.QuantityInvariant) :
    Q.UniversalAntiEntailment ↔ ∀ n, ¬ (Qᶜ.TrueOf n ∧ Qᶜ.TrueOf (n + 1)) := by
  rw [universalAntiEntailment_iff_compl, universalEntailment_iff_trueOf hQ.compl]

/-! ### Monotone quantifiers: Remarks 13, 15, 17 and 19 -/

/-- A monotone quantifier with a universal entailment is `∀` or trivially false (Remark 13). -/
theorem UniversalEntailment.eq_bot_or_eq_univ (h : Q.UniversalEntailment) (hm : Monotone Q) :
    Q = ⊥ ∨ Q = (· = Set.univ) := by
  have hQ : ∀ B, Q B → B = Set.univ := fun B hB ↦ by
    by_contra hne
    obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem B).1 hne
    exact universalEntailment_iff.1 h B a ha ⟨hB, hm (Set.subset_insert a B) hB⟩
  by_cases hu : Q Set.univ
  · exact .inr (funext fun B ↦ propext ⟨hQ B, fun e ↦ e ▸ hu⟩)
  · exact .inl (funext fun B ↦ propext ⟨fun hB ↦ hu (hQ B hB ▸ hB), False.elim⟩)

/-- An antitone quantifier with a universal entailment is `¬∃` or trivially false (Remark 15). -/
theorem UniversalEntailment.eq_bot_or_eq_empty (h : Q.UniversalEntailment) (hm : Antitone Q) :
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

/-- A monotone quantifier with a universal anti-entailment is `∃` or trivially true
(Remark 17). -/
theorem UniversalAntiEntailment.eq_top_or_nonempty (h : Q.UniversalAntiEntailment)
    (hm : Monotone Q) : Q = ⊤ ∨ Q = Set.Nonempty := by
  rw [universalAntiEntailment_iff_compl] at h
  rcases h.eq_bot_or_eq_empty fun _ _ hBC hB hC ↦ hB (hm hBC hC) with e | e
  · exact .inl (compl_injective (by rw [e, compl_top]))
  · refine .inr (funext fun B ↦ propext ?_)
    have : (¬ Q B) = (B = ∅) := congrFun e B
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← this, not_not]

/-- An antitone quantifier with a universal anti-entailment is `¬∀` or trivially true
(Remark 19). -/
theorem UniversalAntiEntailment.eq_top_or_ne_univ (h : Q.UniversalAntiEntailment)
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
theorem UniversalPresupposition.eq_even_or_eq_odd [Finite α] (h : Q.UniversalPresupposition) :
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

/-! ### Universal inferences of a determiner -/

namespace Det

variable {d : Det α}

/-- A determiner has a universal entailment when its deployment with a classical restrictor `B`
is true only if the nuclear scope is defined throughout `B` (Definition 20). -/
def UniversalEntailment (d : Det α) : Prop :=
  ∀ (B : α → Bool) (A : α → Trivalent),
    deployDeterminer d.toBool (fun a ↦ ofProp (B a)) A = 1 → ∀ a, B a → A a ≠ 0

/-- A determiner has a universal anti-entailment when its deployment with a classical restrictor
`B` is false only if the nuclear scope is defined throughout `B` (Definition 21). -/
def UniversalAntiEntailment (d : Det α) : Prop :=
  ∀ (B : α → Bool) (A : α → Trivalent),
    deployDeterminer d.toBool (fun a ↦ ofProp (B a)) A = -1 → ∀ a, B a → A a ≠ 0

/-- A determiner has a universal presupposition when it has a universal entailment and a
universal anti-entailment (Definition 22). -/
def UniversalPresupposition (d : Det α) : Prop :=
  d.UniversalEntailment ∧ d.UniversalAntiEntailment

/-- The universal inferences of a determiner, quantified over restrictor sets. -/
private theorem forall_restrictor_iff (P : Set α → Set α → Prop) :
    (∀ B : α → Bool, ∀ A : α → Trivalent,
        (∀ g ∈ repairs A, P {a | B a} {a | g a}) → ∀ a, B a → A a ≠ 0) ↔
      ∀ R B, ∀ a ∈ R, a ∉ B → ¬ (P R B ∧ P R (insert a B)) := by
  classical
  constructor
  · intro h R
    have := (forall_repairs_imp_iff (P {a | decide (a ∈ R)}) {a | decide (a ∈ R)}).1
      fun A hA a ha ↦ h (fun a ↦ decide (a ∈ R)) A hA a (by simpa using ha)
    simpa using this
  · intro h B A hA a ha
    exact (forall_repairs_imp_iff (P {a | B a}) {a | B a}).2 (h {a | B a}) A hA a ha

/-- A determiner has a universal entailment when it never holds of both a scope and the scope with
one more element of the restrictor. -/
theorem universalEntailment_iff :
    d.UniversalEntailment ↔ ∀ R B, ∀ a ∈ R, a ∉ B → ¬ (d R B ∧ d R (insert a B)) := by
  rw [← forall_restrictor_iff]
  simp [UniversalEntailment, deployDeterminer_ofProp_left, deployQuantifier_toBool_eq_one_iff]

/-- A determiner has a universal anti-entailment when it never fails of both a scope and the scope
with one more element of the restrictor. -/
theorem universalAntiEntailment_iff :
    d.UniversalAntiEntailment ↔
      ∀ R B, ∀ a ∈ R, a ∉ B → ¬ (¬ d R B ∧ ¬ d R (insert a B)) := by
  rw [← forall_restrictor_iff (fun R B ↦ ¬ d R B)]
  simp [UniversalAntiEntailment, deployDeterminer_ofProp_left,
    deployQuantifier_toBool_eq_neg_one_iff]

theorem universalAntiEntailment_iff_compl :
    d.UniversalAntiEntailment ↔ dᶜ.UniversalEntailment := by
  rw [universalAntiEntailment_iff, universalEntailment_iff]; rfl

theorem universalPresupposition_iff :
    d.UniversalPresupposition ↔ ∀ R B, ∀ a ∈ R, a ∉ B → (d R (insert a B) ↔ ¬ d R B) := by
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
    d.UniversalEntailment ↔ ∀ m n, ¬ (ofDet d (m + 1) n ∧ ofDet d m (n + 1)) := by
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
/-- A conservative, quantity-invariant determiner on a finite universe has a universal
anti-entailment exactly when the tree of its complement holds at no two points `(m + 1, n)` and
`(m, n + 1)` (Proposition 7). -/
theorem universalAntiEntailment_iff_ofDet [Finite α] (hC : d.Conservative)
    (hQ : d.QuantityInvariant) :
    d.UniversalAntiEntailment ↔ ∀ m n, ¬ (ofDet dᶜ (m + 1) n ∧ ofDet dᶜ m (n + 1)) := by
  rw [universalAntiEntailment_iff_compl]
  exact universalEntailment_iff_ofDet (fun A B ↦ not_congr (hC A B))
    fun σ A B ↦ not_congr (hQ σ A B)

/-! ### Monotone determiners: Remarks 14, 16, 18 and 20 -/

/-- A conservative, scope-monotone determiner with a universal entailment is, at each restrictor,
*every* or trivially false (Remark 14). -/
theorem UniversalEntailment.eq_bot_or_every (h : d.UniversalEntailment) (hC : d.Conservative)
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

/-- A conservative, scope-antitone determiner with a universal entailment is, at each restrictor,
*no* or trivially false (Remark 16). -/
theorem UniversalEntailment.eq_bot_or_no (h : d.UniversalEntailment) (hC : d.Conservative)
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

/-- A conservative, scope-monotone determiner with a universal anti-entailment is, at each
restrictor, *some* or trivially true (Remark 18). -/
theorem UniversalAntiEntailment.eq_top_or_some (h : d.UniversalAntiEntailment)
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

/-- A conservative, scope-antitone determiner with a universal anti-entailment is, at each
restrictor, *not every* or trivially true (Remark 20). -/
theorem UniversalAntiEntailment.eq_top_or_notEvery (h : d.UniversalAntiEntailment)
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

/-- At each restrictor, a conservative determiner on a finite universe with a universal
presupposition holds of a scope according to the parity of its intersection with the
restrictor. -/
theorem UniversalPresupposition.iff_even [Finite α] (h : d.UniversalPresupposition)
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

/-- A conservative determiner on a finite universe with a universal presupposition is, at each
restrictor, *an even number of* or *an odd number of* (Remark 22). -/
theorem UniversalPresupposition.eq_even_or_eq_odd [Finite α] (h : d.UniversalPresupposition)
    (hC : d.Conservative) (R : Set α) :
    d R = (fun B ↦ Even (R ∩ B).ncard) ∨ d R = (fun B ↦ Odd (R ∩ B).ncard) := by
  by_cases he : d R ∅
  · exact .inl (funext fun B ↦ propext (by rw [h.iff_even hC]; tauto))
  · exact .inr (funext fun B ↦ propext (by rw [h.iff_even hC, ← Nat.not_even_iff_odd]; tauto))

/-! ### *Every* -/

/-- *Every* has a universal entailment: *every student has stopped smoking* entails that every
student has smoked. -/
theorem every_universalEntailment : (every : Det α).UniversalEntailment :=
  universalEntailment_iff.2 fun _ _ _ haR haB h ↦ haB (h.1 haR)

/-- On a universe of two or more, *every* has no universal anti-entailment, so no universal
presupposition: *every student has stopped smoking* is false when one student smokes and another
never smoked. -/
theorem not_every_universalAntiEntailment [Nontrivial α] :
    ¬ (every : Det α).UniversalAntiEntailment := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine fun h ↦ universalAntiEntailment_iff.1 h {a, b} ∅ a (by simp) (by simp) ⟨?_, ?_⟩
  · exact fun hs ↦ hs (Set.mem_insert a {b})
  · intro hs
    have := hs (Set.mem_insert_of_mem a rfl)
    simp only [insert_empty_eq, Set.mem_singleton_iff] at this
    exact hab this.symm

end Det

end Quantifier
