module

public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Questions.Closure
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Data.Examples.Xiang2022

/-!
# Xiang (2022): Relativized Exhaustivity: Mention-Some and Uniqueness

This file formalizes [xiang-2022]'s Relativized Exhaustivity, the presupposition that replaces
[dayal-1996]'s exhaustivity presupposition in modalized questions. A question is a topical
property `P : α → Set W` from short answers to propositions, answered by [fox-2013]'s
max-informative true short answers, those not asymmetrically entailed by another true answer
(`MaxI`, mathlib's `MinimalFor`), so that a *can*-question may have several complete answers.
Dayal's presupposition that a strongest true answer exists (`DEP`) rules these out;
Relativized Exhaustivity (`RelExh`) requires it instead of the non-modalized question at every
accessible world verifying a true answer.

The main results are the paper's generalization for existential modals, that the mention-some
readings of *Wh-A can P?* satisfy Relativized Exhaustivity exactly when *Wh-A P?* satisfies
Dayal's presupposition at every accessible world where some member of *A* satisfies *P*
(`relExh_poss_iff`), and the scenarios separating the two presuppositions. Local
exhaustification of the nucleus makes the non-modalized question uniquely answered wherever it
has a true answer, so the exhaustified mention-some reading of a *can*-question always
satisfies Relativized Exhaustivity while Dayal's presupposition fails (`relExh_poss_localExh`,
`chair_scenario`). A *have to*-question with a narrow-scope disjunctive answer separates them
the other way: Dayal's presupposition holds while Relativized Exhaustivity fails wherever an
accessible world violates uniqueness, the local-uniqueness inference of
[hirsch-schwarz-2020] (`assign_scenario`).

## Implementation notes

The paper states Relativized Exhaustivity by quantifying over modal bases that send the
evaluation world to a singleton subset of the original base; `RelExh` states the intended
condition directly, for the modalized question `O ∘ P` built from the non-modalized property by
an operator `O` over the accessibility relation. Local exhaustification is
`Exhaustification.exh` over the alternatives of the wh-trace. Modal flavour and the
anti-exhaustification analysis of disjunctive mention-all answers are not modelled.

## References

* [xiang-2022]
* [dayal-1996]
* [fox-2013]
* [hirsch-schwarz-2020]
-/

@[expose] public section

namespace Xiang2022

open Question ModalLogic Exhaustification Set
open scoped SetRel

variable {W α : Type*}

/-! ### Answerhood over topical properties -/

/-- The short answers true at a world. -/
def trueShort (P : α → Set W) (w : W) : Set α := {a | w ∈ P a}

@[simp] theorem mem_trueShort {P : α → Set W} {w : W} {a : α} :
    a ∈ trueShort P w ↔ w ∈ P a := Iff.rfl

/-- Dayal's exhaustivity presupposition for a topical property: its answer space has a
strongest true member. -/
def DEP (P : α → Set W) (w : W) : Prop := IsExhaustivelyResolvable (range P) w

theorem dep_iff (P : α → Set W) (w : W) :
    DEP P w ↔ ∃ a, w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b :=
  isExhaustivelyResolvable_range_iff P w

/-- A max-informative true short answer: true, and minimal under entailment among the true
short answers. -/
abbrev MaxI (P : α → Set W) (w : W) (a : α) : Prop := MinimalFor (· ∈ trueShort P w) P a

theorem maxI_iff {P : α → Set W} {w : W} {a : α} :
    MaxI P w a ↔ w ∈ P a ∧ ∀ b, w ∈ P b → ¬ P b ⊂ P a := by
  simp only [MaxI, MinimalFor, mem_trueShort, not_lt_iff_le_imp_ge]

/-- The short-answer operator: the max-informative true short answers. -/
def ansS (P : α → Set W) (w : W) : Set α := {a | MaxI P w a}

/-- The propositional operator: the image of the short-answer operator. -/
def ansP (P : α → Set W) (w : W) : Set (Set W) := P '' ansS P w

theorem mem_ansP_iff {P : α → Set W} {w : W} {p : Set W} :
    p ∈ ansP P w ↔ Minimal (· ∈ trueAnswers (range P) w) p := by
  constructor
  · rintro ⟨a, ⟨ha, hmin⟩, rfl⟩
    refine ⟨⟨⟨a, rfl⟩, ha⟩, ?_⟩
    rintro _ ⟨⟨b, rfl⟩, hb⟩ hle
    exact hmin hb hle
  · rintro ⟨⟨⟨a, rfl⟩, ha⟩, hmin⟩
    exact ⟨a, ⟨ha, fun b hb hle ↦ hmin (y := P b) ⟨⟨b, rfl⟩, hb⟩ hle⟩, rfl⟩

theorem ansP_eq_singleton {P : α → Set W} {w : W} {p : Set W}
    (h : IsStrongestTrueAnswer (range P) w p) : ansP P w = {p} := by
  ext q
  rw [mem_ansP_iff, h.minimal_iff, mem_singleton_iff]

/-! ### Modalized questions -/

/-- Relativized Exhaustivity for the question `O ∘ P` built from the non-modalized `P` by the
operator `O` over the accessibility `R`: at every accessible world verifying one of the
modalized question's true short answers, `P` satisfies Dayal's presupposition. -/
def RelExh (O : Set W → Set W) (R : SetRel W W) (P : α → Set W) (w : W) : Prop :=
  ∀ v, w ~[R] v → (∃ a, w ∈ O (P a) ∧ v ∈ P a) → DEP P v

theorem relExh_poss_iff (R : SetRel W W) (P : α → Set W) (w : W) :
    RelExh R.preimage R P w ↔ ∀ v, w ~[R] v → (trueShort P v).Nonempty → DEP P v :=
  forall₂_congr fun v hv ↦ imp_congr_left
    ⟨fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, ⟨v, ha, hv⟩, ha⟩⟩

theorem relExh_id_iff (P : α → Set W) (w : W) :
    RelExh id .id P w ↔ ((trueShort P w).Nonempty → DEP P w) := by
  simp [RelExh, Set.Nonempty]

/-! ### Local exhaustification -/

/-- The nucleus exhaustified against the alternatives of the wh-trace: each short answer, and
no other. -/
def localExh (P : α → Set W) : α → Set W := exh (range P) ∘ P

theorem eq_of_mem_localExh {P : α → Set W} {w : W} {a b : α} (ha : w ∈ localExh P a)
    (hb : w ∈ localExh P b) : P a = P b :=
  (ha.2 _ ⟨b, rfl⟩ hb.1).antisymm (hb.2 _ ⟨a, rfl⟩ ha.1)

theorem dep_localExh {P : α → Set W} {w : W} (h : (trueShort (localExh P) w).Nonempty) :
    DEP (localExh P) w :=
  let ⟨a, ha⟩ := h
  (dep_iff _ _).2 ⟨a, ha, fun b hb ↦ by
    simp only [localExh, Function.comp_apply, eq_of_mem_localExh ha hb, subset_rfl]⟩

theorem relExh_poss_localExh (R : SetRel W W) (P : α → Set W) (w : W) :
    RelExh R.preimage R (localExh P) w :=
  (relExh_poss_iff R _ w).2 fun _ _ h ↦ dep_localExh h

/-! ### The committee scenario -/

/-- The worlds of the committee scenario: the evaluation world `0` and the accessible worlds
`1` and `2`. -/
abbrev CW := Fin 3

/-- *x chairs the committee*: Andy (`0`) chairs in world 1, Billy (`1`) in world 2. -/
def chair : Fin 2 → Set CW
  | 0 => {1}
  | 1 => {2}

/-- The modal base: the evaluation world accesses both alternatives, each of which accesses
only itself. -/
def chairR : SetRel CW CW := {p | if p.1 = 0 then p.2 ≠ 0 else p.1 = p.2}

theorem poss_localExh_chair (a : Fin 2) : chairR.preimage (localExh chair a) = {0, a.succ} := by
  ext w; fin_cases a <;> fin_cases w <;> simp [localExh, exh, chair, chairR]

theorem chair_scenario :
    ansS (chairR.preimage ∘ localExh chair) 0 = univ ∧
      RelExh chairR.preimage chairR (localExh chair) 0 ∧
        ¬ DEP (chairR.preimage ∘ localExh chair) 0 := by
  refine ⟨eq_univ_of_forall fun a ↦ ⟨by simp [poss_localExh_chair], fun b _ hle ↦ ?_⟩,
    relExh_poss_localExh _ _ _, ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [poss_localExh_chair, subset_def] at hle ⊢
  · rw [dep_iff]
    rintro ⟨a, -, h⟩
    fin_cases a
    · simpa [poss_localExh_chair, subset_def] using h 1
    · simpa [poss_localExh_chair, subset_def] using h 0

/-! ### The chapter scenario -/

/-- The worlds of the chapter scenario: the evaluation worlds `0` and `4`, and the accessible
worlds `1`, `2`, `3`. -/
abbrev AW := Fin 5

/-- *We assign chapter c*: chapter 1 is assigned in worlds 1 and 3, chapter 2 in worlds 2
and 3. -/
def assigned : Fin 2 → Set AW
  | 0 => {1, 3}
  | 1 => {2, 3}

/-- The narrow-scope higher-order answers: either chapter, or their disjunction. -/
def assign : Fin 3 → Set AW
  | 0 => assigned 0
  | 1 => assigned 1
  | 2 => assigned 0 ∪ assigned 1

theorem range_assign : range assign = supClosure (range assigned) := by
  rw [Set.supClosure_range_eq_image]
  ext q
  simp only [mem_range, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨{0}, by simp, by simp [assign]⟩
    · exact ⟨{1}, by simp, by simp [assign]⟩
    · exact ⟨{0, 1}, by simp, by simp [assign]⟩
  · rintro ⟨S, hS, rfl⟩
    fin_cases S
    · exact absurd hS (by simp)
    · exact ⟨0, by simp [assign]⟩
    · exact ⟨1, by simp [assign]⟩
    · exact ⟨2, by simp [assign]⟩

/-- The modal base: world `0` accesses the uniqueness-violating world `3`, world `4` does
not. -/
def assignR : SetRel AW AW :=
  {p | if p.1 = 0 then p.2 ∈ ({1, 2, 3} : Set AW)
    else if p.1 = 4 then p.2 ∈ ({1, 2} : Set AW) else p.1 = p.2}

theorem dep_assigned_iff (v : AW) : DEP assigned v ↔ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp [dep_iff, assigned, Fin.exists_fin_two, Fin.forall_fin_two, subset_def]

theorem dep_assign_iff (v : AW) : DEP assign v ↔ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp [dep_iff, assign, assigned, Fin.exists_fin_succ, Fin.forall_fin_succ,
    subset_def]

theorem assign_scenario :
    DEP (assignR.core ∘ assign) 0 ∧ ¬ RelExh assignR.core assignR assign 0 ∧
      RelExh assignR.core assignR assign 4 := by
  have h0 : assignR.core (assign 0) = {1, 3} := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  have h1 : assignR.core (assign 1) = {2, 3} := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  have h2 : assignR.core (assign 2) = univ := by
    ext w; fin_cases w <;> simp [assignR, assign, assigned]
  refine ⟨(dep_iff _ _).2 ⟨2, by simp [h2], fun b hb ↦ by
    fin_cases b <;> simp [h0, h1, h2] at hb ⊢⟩, fun h ↦ ?_, fun v hv _ ↦ ?_⟩
  · simpa [dep_assign_iff] using
      h 3 (by simp [assignR]) ⟨2, by simp [h2], by simp [assign, assigned]⟩
  · exact (dep_assign_iff v).2 (by simpa [assignR] using hv)

theorem assign_can_scenario :
    ¬ RelExh assignR.preimage assignR assigned 0 ∧ RelExh assignR.preimage assignR assigned 4 := by
  simp only [relExh_poss_iff, dep_assigned_iff]
  exact ⟨fun h ↦ by simpa using h 3 (by simp [assignR]) ⟨0, by simp [assigned]⟩,
    fun v hv _ ↦ by simpa [assignR] using hv⟩

end Xiang2022
