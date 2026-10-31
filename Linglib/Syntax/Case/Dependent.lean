/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Alignment
public import Linglib.Syntax.Case.Valuation

/-!
# Dependent case

Structural case read off the arrangement of NPs in a domain, under a disjunctive hierarchy:
case a lexical head has valued is kept; otherwise an NP that c-commands a distinct caseless NP
in the domain takes the domain's high case and one c-commanded by such an NP its low case, the
two rules reading the same configuration, so a domain with both marks the higher NP and the
lower NP at once; whatever remains takes the domain's elsewhere case. Which of the two
dependent rules a clause has is its alignment: accusative, ergative, tripartite or neutral.
The passes are generic in what an NP is, so a phase-cyclic grammar can run them domain by
domain.

## Main definitions

* `Case.Mechanism`: what valued a case, a lexical head, a dependent rule, Agree, or the
  elsewhere case, shared by every account of case assignment.
* `Case.lexicalValuation`: the valuation of NPs by lexical case.
* `DependentCase.Rules`: the high, low and elsewhere cases of one domain, and
  `Rules.ofAlignment`, the rules of an alignment.
* `Rules.dependentPassBy`, `Rules.dependentPass`, `Rules.unmarkedPass`: the passes over the NPs a
  predicate selects, the dependent one under an order on them, by default the order listed.
* `Rules.valuations`: the valuations the rules can assign.
* `Rules.assign`, `assignCases`: the one-domain algorithm, and its form for an alignment.

## Main results

* `Rules.dependentPass_high`, `Rules.dependentPass_low`, `Rules.dependentPass_alone`: what the
  dependent rules do to an NP with a caseless NP below it, above it, or neither.
* `Rules.extends_dependentPass`, `Rules.extends_unmarkedPass`, `Rules.extends_assign`: each pass
  extends the valuation by what the rules assign.
* `Rules.dependentPassBy_congr`: the dependent pass reads its order only among the NPs it selects.
* `Rules.length_assign`: the algorithm is total.
* `Rules.assign_getElem?_of_some`: lexical case is kept, so it bleeds the dependent rules.
* `Rules.case_mem_cases`: a caseless NP is valued only with a case the rules mention.
* `Rules.assign_singleton`, `Rules.assign_pair`: the algorithm in closed form on domains of one
  and two NPs.
* `Rules.classifies_marking_ofAlignment`: the rules of an alignment mark S, A and P with that
  alignment.
* `Rules.marking_S_eq_marking_A_iff`, `Rules.not_isErgative_marking_of_high_eq_none`: only a
  high case distinct from the elsewhere case marks a transitive subject apart from an
  intransitive one, so rules without one are not ergative.

## Implementation notes

List position encodes structural height: earlier is higher, and c-commands everything later.
`Rules.dependentPassBy` takes c-command as a relation on the listed NPs instead, for NPs that list
order misplaces, such as one inside a PP, c-commanded but c-commanding nothing outside it.
The NPs are of any type, identified by that type rather than by a label; a study's NPs are
its own positions, and `Valuation.valueOf` reads off the case of one. The passes are
`Valuation.fill`, so what they share (totality, persistence of values) comes from
`Case.Valuation.Extends`.

## References

* [marantz-1991]
* [baker-2015]
-/

@[expose] public section

namespace Case

variable {α : Type*}

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

/-! ### The lexical valuation -/

/-- Every NP with the case slot it enters with: valued by a lexical head, absent for an NP that
bears no case, and unvalued otherwise. -/
def slotValuation (case : α → FeatureSlot Case) (xs : List α) : Valuation α (Case × Mechanism) :=
  Valuation.initial (fun x ↦ (case x).map (·, .lexical)) xs

/-- Every NP with its lexical case valued and nothing else. -/
def lexicalValuation (lexicalCase : α → Option Case) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  slotValuation (fun x ↦ Valuation.offer (lexicalCase x)) xs

theorem slotValuation_getElem?_of_valued (case : α → FeatureSlot Case) {xs : List α} {i : ℕ}
    {x : α} {c : Case} (hx : xs[i]? = some x) (hc : case x = .valued c) :
    (slotValuation case xs)[i]? = some (x, .valued (c, .lexical)) := by
  simp [slotValuation, Valuation.initial_getElem?, hx, hc]

theorem slotValuation_getElem? {case : α → FeatureSlot Case} {xs : List α} {i : ℕ} {x : α}
    {v : Case × Mechanism} (h : (slotValuation case xs)[i]? = some (x, .valued v)) :
    case x = .valued v.1 ∧ v.2 = .lexical := by
  simp only [slotValuation, Valuation.initial_getElem?] at h
  obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hv⟩ := Prod.mk.injEq .. ▸ hy
  cases hc : case y <;> simp_all [eq_comm]

theorem lexicalValuation_getElem?_of_some (lexicalCase : α → Option Case) {xs : List α} {i : ℕ}
    {x : α} {c : Case} (hx : xs[i]? = some x) (hc : lexicalCase x = some c) :
    (lexicalValuation lexicalCase xs)[i]? = some (x, .valued (c, .lexical)) :=
  slotValuation_getElem?_of_valued _ hx (by simp [hc])

theorem lexicalValuation_getElem? {lexicalCase : α → Option Case} {xs : List α} {i : ℕ} {x : α}
    {v : Case × Mechanism} (h : (lexicalValuation lexicalCase xs)[i]? = some (x, .valued v)) :
    lexicalCase x = some v.1 ∧ v.2 = .lexical := by
  obtain ⟨hc, hm⟩ := slotValuation_getElem? h
  exact ⟨Valuation.offer_eq_valued_iff.1 hc, hm⟩

end Case

namespace DependentCase

open Case (Mechanism Valuation lexicalValuation slotValuation lexicalValuation_getElem?_of_some
  lexicalValuation_getElem?)

variable {α : Type*}

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

/-- The cases the rules can value a caseless NP with. -/
def Rules.cases (r : Rules) : List Case := [r.high, r.low, r.unmarked].filterMap id

theorem Rules.high_mem_cases {r : Rules} {c : Case} (h : r.high = some c) : c ∈ r.cases := by
  simp [Rules.cases, h]

theorem Rules.low_mem_cases {r : Rules} {c : Case} (h : r.low = some c) : c ∈ r.cases := by
  simp [Rules.cases, h]

theorem Rules.unmarked_mem_cases {r : Rules} {c : Case} (h : r.unmarked = some c) :
    c ∈ r.cases := by
  simp [Rules.cases, h]

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

/-- The dependent rules over the NPs `P` selects, `lt p q` saying that the NP listed at `p`
    c-commands the one listed at `q`: the high case goes to an unvalued NP c-commanding a caseless
    one and the low case to one c-commanded by a caseless one, both read off the same
    configuration; an NP in both positions takes the high case. An NP that bears no case, such as
    PRO, is caseless and competes, but receives no case. -/
def Rules.dependentPassBy (r : Rules) (lt : ℕ × α → ℕ × α → Prop) [DecidableRel lt]
    (P : α → Prop) [DecidablePred P] (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  let E := s.caselessEntries P
  s.fill fun i x ↦
    if P x then
      if r.high.isSome && E.any (fun q ↦ decide (lt (i, x) q)) then r.high.map (·, .dependent)
      else if E.any (fun q ↦ decide (lt q (i, x))) then r.low.map (·, .dependent)
      else none
    else none

/-- The dependent rules over the NPs `P` selects as listed, the earlier c-commanding the later. -/
def Rules.dependentPass (r : Rules) (P : α → Prop) [DecidablePred P]
    (s : Valuation α (Case × Mechanism)) : Valuation α (Case × Mechanism) :=
  r.dependentPassBy (fun p q ↦ p.1 < q.1) P s

/-- The elsewhere case to the unvalued NPs `P` selects. -/
def Rules.unmarkedPass (r : Rules) (P : α → Prop) [DecidablePred P]
    (s : Valuation α (Case × Mechanism)) : Valuation α (Case × Mechanism) :=
  s.fill fun _ x ↦ if P x then r.unmarked.map (·, .unmarked) else none

/-- Case for every NP of one domain, `lex` giving the case a lexical head has valued: the
    dependent rules, then the elsewhere case. -/
def Rules.assign (r : Rules) (lex : α → Option Case) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  r.unmarkedPass (fun _ ↦ True) <| r.dependentPass (fun _ ↦ True) (lexicalValuation lex xs)

/-- The one-domain algorithm of an alignment. -/
def assignCases (a : Alignment.AlignmentType) (lex : α → Option Case) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  (Rules.ofAlignment a).assign lex xs

/-! ### What the passes assign -/

/-- The valuations the rules can assign: a dependent case, or the elsewhere case. -/
def Rules.valuations (r : Rules) : Set (Case × Mechanism) :=
  {v | v.2 = .dependent ∧ (r.high = some v.1 ∨ r.low = some v.1) ∨
    v.2 = .unmarked ∧ r.unmarked = some v.1}

theorem Rules.fst_mem_cases {r : Rules} {v : Case × Mechanism} (h : v ∈ r.valuations) :
    v.1 ∈ r.cases := by
  rcases h with ⟨-, h | h⟩ | ⟨-, h⟩
  · exact Rules.high_mem_cases h
  · exact Rules.low_mem_cases h
  · exact Rules.unmarked_mem_cases h

theorem Rules.extends_dependentPassBy (r : Rules) (lt : ℕ × α → ℕ × α → Prop) [DecidableRel lt]
    (P : α → Prop) [DecidablePred P] (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ r.valuations) (r.dependentPassBy lt P s) :=
  Valuation.extends_fill (fun _ _ v hv ↦ by
    split_ifs at hv <;>
      first
      | cases hv
      | (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
         first | exact .inl ⟨rfl, .inl hc⟩ | exact .inl ⟨rfl, .inr hc⟩)) s

theorem Rules.extends_dependentPass (r : Rules) (P : α → Prop) [DecidablePred P]
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ r.valuations) (r.dependentPass P s) :=
  r.extends_dependentPassBy _ P s

/-- The pass reads its order only among the caseless NPs it selects. -/
theorem Rules.dependentPassBy_congr (r : Rules) {lt lt' : ℕ × α → ℕ × α → Prop} [DecidableRel lt]
    [DecidableRel lt'] {P : α → Prop} [DecidablePred P] {s : Valuation α (Case × Mechanism)}
    (h : ∀ p ∈ s.caselessEntries P, ∀ q ∈ s.caselessEntries P, (lt p q ↔ lt' p q)) :
    r.dependentPassBy lt P s = r.dependentPassBy lt' P s := by
  refine List.ext_getElem? fun i ↦ ?_
  rw [Rules.dependentPassBy, Rules.dependentPassBy, Valuation.fill_getElem?,
    Valuation.fill_getElem?]
  rcases hi : s[i]? with _ | ⟨x, k⟩
  · rfl
  cases k with
  | absent => rfl
  | valued v => rfl
  | unvalued =>
    by_cases hP : P x
    · have hx : (i, x) ∈ s.caselessEntries P := Valuation.mem_caselessEntries.2 ⟨_, hi, rfl, hP⟩
      have hany (f g : ℕ × α → Prop) [DecidablePred f] [DecidablePred g]
          (hfg : ∀ q ∈ s.caselessEntries P, (f q ↔ g q)) :
          (s.caselessEntries P).any (fun q ↦ decide (f q)) =
            (s.caselessEntries P).any (fun q ↦ decide (g q)) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        exact exists_congr fun q ↦ and_congr_right fun hq ↦ by simp [hfg q hq]
      simp only [Option.map_some, ↓reduceIte, hP,
        hany (lt (i, x)) (lt' (i, x)) fun q hq ↦ h _ hx q hq,
        hany (lt · (i, x)) (lt' · (i, x)) fun q hq ↦ h q hq _ hx]
    · simp only [Option.map_some, ↓reduceIte, hP]

theorem Rules.extends_unmarkedPass (r : Rules) (P : α → Prop) [DecidablePred P]
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ r.valuations) (r.unmarkedPass P s) :=
  Valuation.extends_fill (fun _ _ v hv ↦ by
    split_ifs at hv
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
    exact .inr ⟨rfl, hc⟩) s

/-- Assignment extends the lexical valuation by what the rules assign. -/
theorem Rules.extends_assign (r : Rules) (lex : α → Option Case) (xs : List α) :
    (lexicalValuation lex xs).Extends (· ∈ r.valuations) (r.assign lex xs) :=
  (r.extends_dependentPass _ _).trans (r.extends_unmarkedPass _ _)

/-- The algorithm is total: one valuation per NP. -/
@[simp] theorem Rules.length_assign (r : Rules) (lex : α → Option Case) (xs : List α) :
    (r.assign lex xs).length = xs.length := by
  rw [← (r.extends_assign lex xs).length_eq, lexicalValuation, slotValuation,
    Valuation.length_initial]

/-- Lexical case is kept, so it bleeds the dependent rules. -/
theorem Rules.assign_getElem?_of_some (r : Rules) {lex : α → Option Case} {xs : List α} {i : ℕ}
    {x : α} {c : Case} (hx : xs[i]? = some x) (hc : lex x = some c) :
    (r.assign lex xs)[i]? = some (x, .valued (c, .lexical)) :=
  (r.extends_assign lex xs).getElem?_of_some (lexicalValuation_getElem?_of_some _ hx hc)

/-- A caseless NP is valued only with a case the rules mention. -/
theorem Rules.case_mem_cases (r : Rules) {lex : α → Option Case} {xs : List α} {i : ℕ} {x : α}
    {c : Case} {m : Mechanism} (hlex : lex x = none)
    (h : (r.assign lex xs)[i]? = some (x, .valued (c, m))) : c ∈ r.cases := by
  rcases (r.extends_assign lex xs).of_getElem? h with h | h
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · exact Rules.fst_mem_cases h

/-! ### What the dependent rules do -/

theorem Rules.dependentPass_eq (r : Rules) (P : α → Prop) [DecidablePred P]
    (s : Valuation α (Case × Mechanism)) :
    r.dependentPass P s = s.fill fun i x ↦
      if P x then
        if r.high.isSome && (s.caseless P).any (i < ·) then r.high.map (·, .dependent)
        else if (s.caseless P).any (· < i) then r.low.map (·, .dependent)
        else none
      else none := by
  simp only [Rules.dependentPass, Rules.dependentPassBy, Valuation.caseless, List.any_map,
    Function.comp_def]

/-- A caseless NP with a caseless NP below it in the domain takes the high case. -/
theorem Rules.dependentPass_high (r : Rules) (P : α → Prop) [DecidablePred P]
    {s : Valuation α (Case × Mechanism)}
    {i j : ℕ} {x : α} {c : Case} (hx : s[i]? = some (x, .unvalued)) (hP : P x)
    (hj : j ∈ s.caseless P) (hij : i < j) (hc : r.high = some c) :
    (r.dependentPass P s)[i]? = some (x, .valued (c, .dependent)) := by
  have hany : ∃ k ∈ s.caseless P, i < k := ⟨j, hj, hij⟩
  simp [Rules.dependentPass_eq, Valuation.fill_getElem?_of_unvalued hx, hP, hany, hc]

/-- A caseless NP with a caseless NP above it in the domain, and none below it that the high
    rule could mark it for, takes the low case. -/
theorem Rules.dependentPass_low (r : Rules) (P : α → Prop) [DecidablePred P]
    {s : Valuation α (Case × Mechanism)}
    {i j : ℕ} {x : α} {c : Case} (hx : s[i]? = some (x, .unvalued)) (hP : P x)
    (hj : j ∈ s.caseless P) (hji : j < i)
    (hhigh : r.high = none ∨ ∀ k ∈ s.caseless P, k ≤ i) (hc : r.low = some c) :
    (r.dependentPass P s)[i]? = some (x, .valued (c, .dependent)) := by
  have hany : ∃ k ∈ s.caseless P, k < i := ⟨j, hj, hji⟩
  rcases hhigh with h | h
  · simp [Rules.dependentPass_eq, Valuation.fill_getElem?_of_unvalued hx, hP, hany, h, hc]
  · have hno : ¬ ∃ k ∈ s.caseless P, i < k := fun ⟨k, hk, hik⟩ ↦ absurd (h k hk) (by omega)
    simp [Rules.dependentPass_eq, Valuation.fill_getElem?_of_unvalued hx, hP, hany, hno, hc]

/-- A caseless NP alone in its domain is untouched by the dependent rules. -/
theorem Rules.dependentPass_alone (r : Rules) (P : α → Prop) [DecidablePred P]
    {s : Valuation α (Case × Mechanism)}
    {i : ℕ} {x : α} (hx : s[i]? = some (x, .unvalued)) (halone : ∀ j ∈ s.caseless P, j = i) :
    (r.dependentPass P s)[i]? = some (x, .unvalued) := by
  have h1 : ¬ ∃ k ∈ s.caseless P, i < k :=
    fun ⟨k, hk, hik⟩ ↦ lt_irrefl i (halone k hk ▸ hik)
  have h2 : ¬ ∃ k ∈ s.caseless P, k < i :=
    fun ⟨k, hk, hki⟩ ↦ lt_irrefl i (halone k hk ▸ hki)
  simp [Rules.dependentPass_eq, Valuation.fill_getElem?_of_unvalued hx, h1, h2]

theorem Rules.unmarkedPass_of_none (r : Rules) (P : α → Prop) [DecidablePred P]
    (h : r.unmarked = none)
    (s : Valuation α (Case × Mechanism)) : r.unmarkedPass P s = s := by
  simp [Rules.unmarkedPass, h]

theorem Rules.dependentPassBy_of_none (r : Rules) (lt : ℕ × α → ℕ × α → Prop) [DecidableRel lt]
    (P : α → Prop) [DecidablePred P] (hh : r.high = none) (hl : r.low = none)
    (s : Valuation α (Case × Mechanism)) : r.dependentPassBy lt P s = s := by
  simp [Rules.dependentPassBy, hh, hl]

theorem Rules.dependentPass_of_none (r : Rules) (P : α → Prop) [DecidablePred P]
    (hh : r.high = none)
    (hl : r.low = none) (s : Valuation α (Case × Mechanism)) : r.dependentPass P s = s :=
  r.dependentPassBy_of_none _ P hh hl s

/-! ### Domains of one and two NPs -/

/-- The valuation of an NP no dependent rule reaches: its lexical case, or the elsewhere case. -/
def Rules.elsewhere (r : Rules) (lexical : Option Case) : Option (Case × Mechanism) :=
  (lexical.map (·, Mechanism.lexical)).or (r.unmarked.map (·, .unmarked))

/-- A sole NP is never reached by a dependent rule. -/
theorem Rules.assign_singleton (r : Rules) (lex : α → Option Case) (x : α) :
    r.assign lex [x] = [(x, Valuation.offer (r.elsewhere (lex x)))] := by
  obtain ⟨hi, lo, un⟩ := r
  simp only [Rules.assign, lexicalValuation, slotValuation, Valuation.initial, List.map_cons,
    List.map_nil]
  cases lex x <;> cases hi <;> cases lo <;> cases un <;> rfl

/-- Of two NPs the dependent rules reach both or neither: when neither has lexical case, the
    higher takes the high case and the lower the low case, where the rules have one. -/
theorem Rules.assign_pair (r : Rules) (lex : α → Option Case) (x y : α) :
    r.assign lex [x, y] =
      [(x, Valuation.offer (if lex x = none ∧ lex y = none ∧ r.high.isSome
            then r.high.map (·, .dependent) else r.elsewhere (lex x))),
       (y, Valuation.offer (if lex x = none ∧ lex y = none ∧ r.low.isSome
            then r.low.map (·, .dependent) else r.elsewhere (lex y)))] := by
  obtain ⟨hi, lo, un⟩ := r
  simp only [Rules.assign, lexicalValuation, slotValuation, Valuation.initial, List.map_cons,
    List.map_nil]
  cases lex x <;> cases lex y <;> cases hi <;> cases lo <;> cases un <;> rfl

/-! ### Alignment -/

/-- The marking the rules give the core roles: S alone in its domain, and A above P in theirs. -/
def Rules.marking (r : Rules) (x : ArgumentRole) : Option Case :=
  ((r.assign (fun _ ↦ none) (if x = .S then [ArgumentRole.S] else [.A, .P])).valueOf x).map
    (·.1)

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

/-! ### Alignments on a transitive and an intransitive clause -/

theorem assignCases_transitive :
    assignCases .accusative (fun _ ↦ none) [(0 : Fin 2), 1] =
        [(0, .valued (.nom, .unmarked)), (1, .valued (.acc, .dependent))] ∧
    assignCases .ergative (fun _ ↦ none) [(0 : Fin 2), 1] =
        [(0, .valued (.erg, .dependent)), (1, .valued (.abs, .unmarked))] ∧
    assignCases .tripartite (fun _ ↦ none) [(0 : Fin 2), 1] =
        [(0, .valued (.erg, .dependent)), (1, .valued (.acc, .dependent))] := by
  decide

theorem assignCases_intransitive (a : Alignment.AlignmentType) :
    ((assignCases a (fun _ : Unit ↦ none) [()]).valueOf ()).map (·.2) = some .unmarked := by
  cases a <;> decide

end DependentCase
