/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Alignment
public import Linglib.Syntax.Case.Rule

/-!
# Dependent case

Structural case read off the arrangement of NPs in a domain, under a disjunctive hierarchy:
case a lexical head has valued is kept; otherwise an NP that c-commands a distinct caseless NP
in the domain takes the domain's high case and one c-commanded by such an NP its low case, the
two rules reading the same configuration, so a domain with both marks the higher NP and the
lower NP at once; whatever remains takes the domain's elsewhere case. Which of the two
dependent rules a clause has is its alignment: accusative, ergative, tripartite or neutral, and
[the rules of an alignment mark the core roles with
it](##DependentCase.Rules.classifies_marking_ofAlignment).
The rules are generic in what an NP is, so a phase-cyclic grammar can run them domain by domain.

## References

* [marantz-1991]
* [baker-2015]
-/

@[expose] public section

namespace Case

/-! ### Mechanisms -/

/-- What valued a case: a lexical head, a dependent rule, Agree with a functional head, or
    the elsewhere case of its domain. -/
inductive Mechanism
  /-- A lexical head. -/
  | lexical
  /-- A dependent rule. -/
  | dependent
  /-- Agree with a functional head. -/
  | agree
  /-- The elsewhere case of a domain. -/
  | unmarked
  deriving DecidableEq, Repr

end Case

namespace DependentCase

open Case (Mechanism)
open FeatureSlot (Extends caseless)
open CaseRule (pass_of_mem)

variable {ι : Type*}

/-! ### Rules -/

/-- The rules of one domain: the case of an NP c-commanding a distinct caseless NP in it, the
    case of one c-commanded by such an NP, and the elsewhere case. -/
structure Rules where
  /-- The case of an NP c-commanding a distinct caseless NP in the domain. -/
  high : Option Case := none
  /-- The case of an NP c-commanded by such an NP. -/
  low : Option Case := none
  /-- The elsewhere case. -/
  unmarked : Option Case := none
  deriving DecidableEq, Repr

/-- The clausal rules of an alignment: accusative on the lower NP, ergative on the higher,
    both, or neither, with the elsewhere case absolutive where the higher NP is marked and
    nominative otherwise. A split-S system is not a dependent-case setting and gets the
    neutral rules. -/
def Rules.ofAlignment : Alignment.AlignmentType → Rules
  | .accusative => { low := some .acc, unmarked := some .nom }
  | .ergative => { high := some .erg, unmarked := some .abs }
  | .tripartite => { high := some .erg, low := some .acc, unmarked := some .abs }
  | .neutral | .active => { unmarked := some .nom }

/-! ### The passes -/

/-- The dependent rules: the high case for an NP with a caseless NP below it, otherwise the low
    case for one with a caseless NP above it; an NP in both positions takes the high case. -/
def Rules.dependent (r : Rules) : CaseRule (Case × Mechanism) := fun a b ↦
  ((if 0 < b then r.high else none).or (if 0 < a then r.low else none)).map (·, .dependent)

/-- The elsewhere case, whatever surrounds the NP. -/
def Rules.elsewhere (r : Rules) : CaseRule (Case × Mechanism) :=
  fun _ _ ↦ r.unmarked.map (·, .unmarked)

/-- The slots of NPs entering a domain, `case` giving each the slot of its case: valued by a lexical
head, absent for an NP that bears no case, and unvalued otherwise. -/
def lexical (case : ι → FeatureSlot Case) (x : ι) : FeatureSlot (Case × Mechanism) :=
  (case x).map (·, .lexical)

@[simp] theorem value?_lexical (case : ι → FeatureSlot Case) (x : ι) :
    (lexical case x).value? = (case x).value?.map (·, .lexical) :=
  FeatureSlot.value?_map _ _

theorem Rules.of_mem_values_dependent {r : Rules} {v : Case × Mechanism}
    (h : v ∈ r.dependent.values) : v.2 = .dependent ∧ (r.high = some v.1 ∨ r.low = some v.1) := by
  obtain ⟨a, b, hv⟩ := h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
  refine ⟨rfl, ?_⟩
  rcases Option.or_eq_some_iff.1 hc with hh | ⟨-, hl⟩
  · split_ifs at hh
    exact .inl hh
  · split_ifs at hl
    exact .inr hl

theorem Rules.of_mem_values_elsewhere {r : Rules} {v : Case × Mechanism}
    (h : v ∈ r.elsewhere.values) : v.2 = .unmarked ∧ r.unmarked = some v.1 := by
  obtain ⟨_, _, hv⟩ := h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
  exact ⟨rfl, hc⟩

section Pass

variable [DecidableEq ι] (lt : ι → ι → Prop) [DecidableRel lt]

/-- One domain: the dependent rules, then the elsewhere case. -/
def Rules.pass (r : Rules) (D : Finset ι) (s : ι → FeatureSlot (Case × Mechanism)) :
    ι → FeatureSlot (Case × Mechanism) :=
  r.elsewhere.pass lt D (r.dependent.pass lt D s)

variable {lt} {r : Rules} {D : Finset ι} {s : ι → FeatureSlot (Case × Mechanism)} {x y : ι}
  {c : Case}

/-! ### What the passes assign -/

theorem Rules.extends_pass :
    Extends (r.dependent.values ∪ r.elsewhere.values) s (r.pass lt D s) :=
  ((CaseRule.extends_pass _ D s).mono Set.subset_union_left).trans
    ((CaseRule.extends_pass _ D _).mono Set.subset_union_right)

/-- Lexical case is kept, so it bleeds the dependent rules. -/
theorem Rules.pass_of_valued {v : Case × Mechanism} (hs : s x = .valued v) :
    r.pass lt D s x = .valued v :=
  Rules.extends_pass.valued hs

/-! ### What the dependent rules do -/

omit [DecidableEq ι] in
private theorem card_filter_pos (hy : y ∈ caseless D s) {P : ι → Prop} [DecidablePred P]
    (hP : P y) : 0 < ((caseless D s).filter P).card :=
  Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, hP⟩⟩

/-- A caseless NP with a caseless NP below it in the domain takes the high case. -/
theorem Rules.dependent_pass_high (hx : x ∈ D) (hs : s x = .unvalued) (hy : y ∈ caseless D s)
    (hxy : lt x y) (hc : r.high = some c) :
    r.dependent.pass lt D s x = .valued (c, .dependent) := by
  rw [pass_of_mem hx hs]
  simp [Rules.dependent, card_filter_pos hy hxy, hc]

/-- A caseless NP with a caseless NP above it in the domain, and none below it that the high
    rule could mark it for, takes the low case. -/
theorem Rules.dependent_pass_low (hx : x ∈ D) (hs : s x = .unvalued) (hy : y ∈ caseless D s)
    (hyx : lt y x) (hhigh : r.high = none ∨ ∀ z ∈ caseless D s, ¬ lt x z) (hc : r.low = some c) :
    r.dependent.pass lt D s x = .valued (c, .dependent) := by
  have hn : (if 0 < ((caseless D s).filter (lt x ·)).card then r.high else none) = none := by
    rcases hhigh with h | h
    · simp [h]
    · have : (caseless D s).filter (lt x ·) = ∅ := Finset.filter_eq_empty_iff.2 fun z hz ↦ h z hz
      simp [this]
  have ha := card_filter_pos (P := (lt · x)) hy hyx
  rw [pass_of_mem hx hs, Rules.dependent]
  simp only [hn, Option.none_or, ite_eq_left ha, hc]
  rfl

/-- A caseless NP alone in its domain is untouched by the dependent rules. -/
theorem Rules.dependent_pass_alone (hx : x ∈ D) (hs : s x = .unvalued)
    (halone : ∀ z ∈ caseless D s, ¬ lt x z ∧ ¬ lt z x) : r.dependent.pass lt D s x = .unvalued := by
  have ha : (caseless D s).filter (lt · x) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun z hz ↦ (halone z hz).2
  have hb : (caseless D s).filter (lt x ·) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun z hz ↦ (halone z hz).1
  rw [pass_of_mem hx hs, ha, hb]
  simp [Rules.dependent]

/-! ### Domains of any size without a high case -/

/-- A caseless NP below another caseless NP, with none below it that the high rule could mark it
for, takes the low case. -/
theorem Rules.pass_low (hx : x ∈ D) (hs : s x = .unvalued) (hy : y ∈ caseless D s) (hyx : lt y x)
    (hhigh : r.high = none ∨ ∀ z ∈ caseless D s, ¬ lt x z) (hc : r.low = some c) :
    r.pass lt D s x = .valued (c, .dependent) :=
  (CaseRule.extends_pass _ D _).valued (Rules.dependent_pass_low hx hs hy hyx hhigh hc)

/-- The highest caseless NP, with none below it that the high rule could mark it for, takes the
elsewhere case. -/
theorem Rules.pass_unmarked (hx : x ∈ D) (hs : s x = .unvalued)
    (hi : ∀ z ∈ caseless D s, ¬ lt z x) (hhigh : r.high = none ∨ ∀ z ∈ caseless D s, ¬ lt x z)
    (hc : r.unmarked = some c) : r.pass lt D s x = .valued (c, .unmarked) := by
  have ha : (caseless D s).filter (lt · x) = ∅ := Finset.filter_eq_empty_iff.2 hi
  have hn : (if 0 < ((caseless D s).filter (lt x ·)).card then r.high else none) = none := by
    rcases hhigh with h | h
    · simp [h]
    · have : (caseless D s).filter (lt x ·) = ∅ := Finset.filter_eq_empty_iff.2 fun z hz ↦ h z hz
      simp [this]
  have hd : r.dependent.pass lt D s x = .unvalued := by
    rw [pass_of_mem hx hs, ha]
    simp only [Rules.dependent, hn, Option.none_or]
    simp
  rw [Rules.pass, pass_of_mem hx hd, Rules.elsewhere, hc]
  rfl

/-- Rules with no dependent case leave the state as it is. -/
theorem Rules.dependent_pass_of_eq_none (hh : r.high = none) (hl : r.low = none)
    (s : ι → FeatureSlot (Case × Mechanism)) : r.dependent.pass lt D s = s :=
  CaseRule.pass_of_forall_eq_none fun _ _ ↦ by simp [Rules.dependent, hh, hl]

/-- Rules with no elsewhere case leave the state as it is. -/
theorem Rules.elsewhere_pass_of_eq_none (hu : r.unmarked = none)
    (s : ι → FeatureSlot (Case × Mechanism)) : r.elsewhere.pass lt D s = s :=
  CaseRule.pass_of_forall_eq_none fun _ _ ↦ by simp [Rules.elsewhere, hu]

end Pass

/-! ### The one-domain algorithm -/

section Assign

variable [DecidableEq ι]

/-- Case for the distinct NPs `xs`, listed from the highest down, `lex` giving the case a lexical
    head has valued: the dependent rules, then the elsewhere case. -/
def Rules.assign (r : Rules) (lex : ι → Option Case) (xs : List ι) :
    ι → FeatureSlot (Case × Mechanism) :=
  r.pass (xs.idxOf ⁻¹'o (· < ·)) xs.toFinset (lexical fun x ↦ .offer (lex x))

/-- The valuation of an NP no dependent rule reaches: its lexical case, or the elsewhere case. -/
def Rules.alone (r : Rules) (l : Option Case) : Option (Case × Mechanism) :=
  (l.map (·, Mechanism.lexical)).or (r.unmarked.map (·, .unmarked))

/-- A sole NP is never reached by a dependent rule. -/
theorem Rules.assign_singleton (r : Rules) (lex : ι → Option Case) (x : ι) :
    r.assign lex [x] x = .offer (r.alone (lex x)) := by
  obtain ⟨hi, lo, un⟩ := r
  cases hx : lex x <;> cases hi <;> cases lo <;> cases un <;>
    simp [Rules.assign, Rules.pass, CaseRule.pass, Rules.dependent, Rules.elsewhere, Rules.alone,
      lexical, hx, caseless, Finset.filter_singleton, Order.Preimage]

/-- Of two NPs the dependent rules reach both or neither: when neither has lexical case, the
    higher takes the high case and the lower the low case, where the rules have one. -/
theorem Rules.assign_pair (r : Rules) (lex : ι → Option Case) {x y : ι} (hxy : x ≠ y) :
    r.assign lex [x, y] x =
        .offer (if lex x = none ∧ lex y = none
          then (r.high.map (·, .dependent)).or (r.alone (lex x)) else r.alone (lex x)) ∧
      r.assign lex [x, y] y =
        .offer (if lex x = none ∧ lex y = none
          then (r.low.map (·, .dependent)).or (r.alone (lex y)) else r.alone (lex y)) := by
  obtain ⟨hi, lo, un⟩ := r
  have hyx : y ≠ x := hxy.symm
  cases hx : lex x <;> cases hy : lex y <;> cases hi <;> cases lo <;> cases un <;>
    simp [Rules.assign, Rules.pass, CaseRule.pass, Rules.dependent, Rules.elsewhere, Rules.alone,
      lexical, hx, hy, hxy, hyx, caseless, Finset.filter_insert, Finset.filter_singleton,
      List.idxOf_cons, Finset.filter_true_of_mem, Order.Preimage]

end Assign

/-! ### Alignment -/

/-- The marking the rules give the core roles: S alone in its domain, and A above P in theirs. -/
def Rules.marking (r : Rules) (x : ArgumentRole) : Option Case :=
  (r.assign (fun _ ↦ none) (if x = .S then [ArgumentRole.S] else [.A, .P]) x).value?.map (·.1)

/-- An intransitive subject takes the elsewhere case. -/
theorem Rules.marking_S (r : Rules) : r.marking .S = r.unmarked := by
  obtain ⟨hi, lo, un⟩ := r
  cases hi <;> cases lo <;> cases un <;> rfl

/-- A transitive subject takes the high case, if the rules have one, and else the elsewhere
    case. -/
theorem Rules.marking_A (r : Rules) : r.marking .A = r.high.or r.unmarked := by
  obtain ⟨hi, lo, un⟩ := r
  cases hi <;> cases lo <;> cases un <;> rfl

/-- A transitive object takes the low case, if the rules have one, and else the elsewhere
    case. -/
theorem Rules.marking_P (r : Rules) : r.marking .P = r.low.or r.unmarked := by
  obtain ⟨hi, lo, un⟩ := r
  cases hi <;> cases lo <;> cases un <;> rfl

/-- The rules mark a transitive subject as they mark an intransitive one unless they have a high
    case distinct from the elsewhere case: the two subjects differ only in the NP the transitive
    one c-commands, which only the high rule reads. -/
theorem Rules.marking_S_eq_marking_A_iff (r : Rules) :
    r.marking .S = r.marking .A ↔ r.high = none ∨ r.high = r.unmarked := by
  rw [r.marking_S, r.marking_A]
  cases r.high with
  | none => simp
  | some c =>
    simp only [Option.some_or, reduceCtorEq, false_or]
    exact eq_comm

/-- Rules without a high case are not ergative. -/
theorem Rules.not_isErgative_marking_of_high_eq_none {r : Rules} (h : r.high = none) :
    ¬ Alignment.IsErgative r.marking :=
  fun he ↦ he.2 (r.marking_S_eq_marking_A_iff.2 (.inl h))

/-- The rules of an alignment mark the core roles with that alignment. -/
theorem Rules.classifies_marking_ofAlignment {a : Alignment.AlignmentType} (ha : a ≠ .active) :
    a.Classifies (Rules.ofAlignment a).marking := by
  cases a <;> first | exact absurd rfl ha | decide

end DependentCase
