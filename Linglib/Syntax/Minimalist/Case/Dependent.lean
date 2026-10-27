/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Dependent case by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain, innermost first,
each phase head's domain with its own high, low and elsewhere cases, and functional heads value
case under Agree on the closest caseless NP they reach; a value once assigned is kept, so a dative
valued in the verb phrase survives the clause. A language's case assigners are the rules of each
phase head's domain and the case each head values under Agree, so configurational, Agree-based
and hybrid systems are points in one space. Assignment over domains
(`assignBy`) takes the rules of each domain, what it sees, c-command among its NPs, closeness to its
probes and its probes as parameters; `CaseAssigners.assign` is its instance on NPs placed by hand
and listed from the highest down, and `Case/SyntacticObject.lean` reads them off an object.

## Main definitions

* `agreeValue`, `agreeValueOn`: Agree on the highest caseless NP of a domain, or the closest.
* `PhasedNP`: an NP placed by hand: its lexical case, whether it bears case, its phase, and the
  phase it shifts into.
* `CaseAssigners`: the rules of each phase head's domain and the case each head values.
* `assignBy`, `CaseAssigners.assign`: assignment over domains, and over NPs placed by hand.

## Main results

* `agreeValue_eq_self_iff`, `agreeValue_eq_map`: Agree values the goal a probe finds, if any.
* `extends_assignBy`: assignment extends the valuation by what the rules and the probes value.
* `case_mem_of_assignBy`, `mechanism_ne_unmarked_of_assignBy`, `exists_probe_of_assignBy`,
  `mechanism_eq_agree_of_assignBy`: what values a case.

## Implementation notes

* A probe's reach is a `Bool` predicate, the one boolean among the parameters, so that the probes
  of a domain form a list.
* A value once assigned is never replaced. Baker and Vinokurova let a later domain re-mark an NP
  and spell out its innermost case (their (15)), which agrees with this wherever the outer case
  is not overt.

## References

* [baker-vinokurova-2010]
* [baker-2015]
* [chomsky-2000], [chomsky-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

open Case (Mechanism Valuation lexicalValuation lexicalValuation_getElem?_of_some
  lexicalValuation_getElem?)
open DependentCase

/-! ### Agree -/

section Agree

variable {α β : Type*} {P : α → Prop} [DecidablePred P] {v : β} {s t : Valuation α β}

/-- Agree into the domain `P` values `v` on the highest NP that `P` selects whose case is still
    unvalued, the activity condition of [chomsky-2000]. -/
def agreeValue (P : α → Prop) [DecidablePred P] (v : β) : Valuation α β → Valuation α β
  | [] => []
  | p :: s => if p.2.isNone ∧ P p.1 then (p.1, some v) :: s else p :: agreeValue P v s

@[simp] theorem agreeValue_nil : agreeValue P v [] = [] := rfl

@[simp] theorem agreeValue_cons (p : α × Option β) (s : Valuation α β) :
    agreeValue P v (p :: s) =
      if p.2.isNone ∧ P p.1 then (p.1, some v) :: s else p :: agreeValue P v s := rfl

/-- Agree values nothing iff the probe seeking an unvalued NP in its domain finds no goal, the
    failed Agree of [preminger-2014]. -/
theorem agreeValue_eq_self_iff : agreeValue P v s = s ↔
    (Probe.relativized fun p : α × Option β ↦ p.2.isNone ∧ P p.1).search s = none := by
  induction s with
  | nil => simp [Probe.search]
  | cons p s ih =>
    obtain ⟨x, _ | a⟩ := p <;> by_cases hx : P x <;> simp_all [Probe.search]

/-- Agree values the NP that the probe seeking an unvalued NP in its domain finds, its goal
(`Probe.search_eq_some_iff_finds`), and leaves the others as they are. -/
theorem agreeValue_eq_map [DecidableEq α] [DecidableEq β] (hs : s.Nodup) :
    agreeValue P v s = s.map fun p ↦
      if (Probe.relativized fun q : α × Option β ↦ q.2.isNone ∧ P q.1).search s = some p then
        (p.1, some v) else p := by
  induction s with
  | nil => rfl
  | cons q s ih =>
    obtain ⟨hq, hs⟩ := List.nodup_cons.mp hs
    by_cases h : q.2.isNone ∧ P q.1
    · rw [agreeValue_cons, ite_eq_left h, Probe.search, List.find?_cons_of_pos (by simpa using h),
        List.map_cons, ite_eq_left rfl]
      congr 1
      refine ((List.map_congr_left fun r hr ↦ ?_).trans (List.map_id' s)).symm
      rw [ite_eq_right (by rintro ⟨⟩; exact hq hr)]
    · rw [agreeValue_cons, ite_eq_right h, Probe.search,
        List.find?_cons_of_neg (by simpa using h), List.map_cons, ← Probe.search, ih hs,
        ite_eq_right fun he ↦ hq (Probe.mem_of_search_eq_some he)]

/-- Agree extends the valuation by its value. -/
theorem extends_agreeValue {p : β → Prop} (hv : p v) :
    ∀ s : Valuation α β, s.Extends p (agreeValue P v s)
  | [] => .nil
  | (x, none) :: s => by
    by_cases hx : P x <;> simp only [agreeValue_cons, Option.isNone_none, hx, and_true,
      and_false, ↓reduceIte]
    · exact .cons ⟨rfl, .inr ⟨rfl, by simpa using hv⟩⟩ (Case.Valuation.Extends.refl s)
    · exact .cons ⟨rfl, .inl rfl⟩ (extends_agreeValue hv s)
  | (x, some w) :: s => by
    simp only [agreeValue_cons, Option.isNone_some, Bool.false_eq_true, false_and, ↓reduceIte]
    exact .cons ⟨rfl, .inl rfl⟩ (extends_agreeValue hv s)

@[simp] theorem map_fst_agreeValue : (agreeValue P v s).map Prod.fst = s.map Prod.fst := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rw [agreeValue_cons]
    split_ifs <;> simp [ih]

/-- Agree reads its domain only on the NPs listed. -/
theorem agreeValue_congr_of_mem {Q : α → Prop} [DecidablePred Q] (h : ∀ p ∈ s, P p.1 ↔ Q p.1) :
    agreeValue P v s = agreeValue Q v s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    simp only [agreeValue_cons, h p List.mem_cons_self,
      ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)]

@[simp] theorem length_agreeValue : (agreeValue P v s).length = s.length :=
  ((extends_agreeValue (p := fun _ ↦ True) trivial s).length_eq).symm

theorem valuedLE_agreeValue (s : Valuation α β) : s.ValuedLE (agreeValue P v s) :=
  (extends_agreeValue (p := fun _ ↦ True) trivial s).valuedLE

/-- Agree preserves which of two derivations values more nominals. -/
theorem _root_.Case.Valuation.ValuedLE.agreeValue (h : s.ValuedLE t) :
    (agreeValue P v s).ValuedLE (agreeValue P v t) := by
  induction h with
  | nil => exact .nil
  | @cons p q s t hpq hst ih =>
    obtain ⟨x, a⟩ := p
    obtain ⟨y, b⟩ := q
    obtain ⟨rfl, hab⟩ := hpq
    rcases a with _ | a <;> rcases b with _ | b <;> by_cases hx : P x <;>
      simp only [agreeValue_cons, Option.isNone_none, Option.isNone_some, hx, and_true,
        and_false, Bool.false_eq_true, ↓reduceIte]
    · exact .cons ⟨rfl, by simp⟩ hst
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ (Case.Valuation.ValuedLE.trans hst (valuedLE_agreeValue t))
    · exact .cons ⟨rfl, by simp⟩ ih
    · simp at hab
    · simp at hab
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ ih

theorem agreeValue_map {α' β' : Type*} {P' : α' → Prop} [DecidablePred P'] {v' : β'}
    (f : α → α') (g : β → β') (hP : ∀ x, P' (f x) ↔ P x) (hv : g v = v')
    (s : List (α × Option β)) :
    agreeValue P' v' (s.map (Prod.map f (Option.map g))) =
      (agreeValue P v s).map (Prod.map f (Option.map g)) := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    rcases a with _ | a
    · by_cases hx : P x <;> simp [hx, hP, hv, ih]
    · simp [ih]

/-- Agree with closeness `lt`, `lt y x` saying `y` is closer to the probe than `x`: the unvalued
    NP of the domain that no other is closer than, the first of them if several are. -/
def agreeValueOn (lt : α → α → Prop) [DecidableRel lt] (P : α → Prop) [DecidablePred P] (v : β)
    (s : Valuation α β) : Valuation α β :=
  agreeValue (fun x ↦ P x ∧ ¬ ∃ q ∈ s, q.2.isNone ∧ P q.1 ∧ lt q.1 x) v s

/-- With no NP closer than another, Agree with closeness values the first, as the list does. -/
@[simp] theorem agreeValueOn_false : agreeValueOn (fun _ _ ↦ False) P v s = agreeValue P v s :=
  agreeValue_congr_of_mem fun _ _ ↦ by simp

end Agree

/-! ### Positions set by hand -/

/-- An NP placed by hand: any case a lexical head has valued, the phase whose domain merges it,
    and the phase it shifts into, if any. -/
structure PhasedNP where
  /-- The case a lexical head has valued, if any. -/
  lexicalCase : Option Case := none
  /-- Whether the NP bears case, which a covert PRO competes for without bearing. -/
  bearsCase : Bool := true
  /-- The phase whose domain merges the NP. -/
  phase : Cat := .C
  /-- The phase whose domain the NP shifts into, if any. -/
  shiftsTo : Option Cat := none
  deriving DecidableEq, Repr

/-- The NP is seen by the domain of `c` when it merges or shifts there. -/
def PhasedNP.visible (np : PhasedNP) (c : Cat) : Prop := np.phase = c ∨ np.shiftsTo = some c

instance (np : PhasedNP) (c : Cat) : Decidable (np.visible c) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The phase whose elsewhere case the NP falls back on: where it shifts to, or where it merges. -/
def PhasedNP.spellOut (np : PhasedNP) : Cat := np.shiftsTo.getD np.phase

/-! ### Case assigners -/

/-- The case assigners of a language, in both modalities of [baker-vinokurova-2010]: the
    dependent-case rules of the domain of each phase head, and the case each head values under
    Agree. -/
structure CaseAssigners where
  /-- The dependent-case rules of the domain of each phase head. -/
  rules : Cat → Rules := fun _ ↦ {}
  /-- The case each head values under Agree, if any. -/
  agreeCase : Cat → Option Case := fun _ ↦ none

/-! ### Assignment over domains -/

section AssignBy

variable {α ι : Type*} (rules : ι → Rules) (visible : ι → α → Prop)
  [∀ i, DecidablePred (visible i)] (above : ι → ℕ × α → ℕ × α → Prop)
  [∀ i, DecidableRel (above i)] (closer : ι → α → α → Prop) [∀ i, DecidableRel (closer i)]
  (probes : ι → List (Case × (α → Bool))) (spellOut : ι → α → Prop)
  [∀ i, DecidablePred (spellOut i)] (bearsCase : α → Prop) [DecidablePred bearsCase]

/-- One domain: its dependent rules over the NPs it sees, `above i` ordering them by c-command,
    then each of its probes valuing the closest NP it reaches, then its elsewhere case, only the
    NPs that bear case taking any. -/
def domainPassBy (i : ι) (s : Valuation α (Case × Mechanism)) : Valuation α (Case × Mechanism) :=
  (rules i).unmarkedPass (fun x ↦ spellOut i x ∧ bearsCase x) <|
    (probes i).foldl (fun st p ↦ agreeValueOn (closer i) (fun x ↦ p.2 x ∧ bearsCase x)
        (p.1, .agree) st)
      ((rules i).dependentPassBy (above i) (visible i) bearsCase s)

/-- The domains in the order `order`, innermost first. -/
def assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  order.foldl (fun st i ↦ domainPassBy rules visible above closer probes spellOut bearsCase i st) s

/-- The valuations assignment over the domains `order` can make: those of the rules of a domain,
    and the case of one of its probes under Agree. -/
def valuationsBy (order : List ι) : Set (Case × Mechanism) :=
  {v | (∃ i ∈ order, v ∈ (rules i).valuations) ∨
    v.2 = .agree ∧ ∃ i ∈ order, ∃ p ∈ probes i, p.1 = v.1}

/-- Assignment over domains extends the valuation by what the rules and the probes value. -/
theorem extends_assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ valuationsBy rules probes order)
      (assignBy rules visible above closer probes spellOut bearsCase order s) := by
  refine Valuation.Extends.foldl _ (fun i hi st ↦ ?_) s
  have hrules : ∀ v ∈ (rules i).valuations, v ∈ valuationsBy rules probes order :=
    fun v hv ↦ .inl ⟨i, hi, hv⟩
  refine (((rules i).extends_dependentPassBy _ _ _ st).mono hrules).trans <|
    (Valuation.Extends.foldl (F := fun p st ↦ agreeValueOn (closer i) (fun x ↦ p.2 x ∧ bearsCase x)
        (p.1, .agree) st)
      _ (fun p hp st ↦ extends_agreeValue (.inr ⟨rfl, i, hi, p, hp, rfl⟩) st) _).trans <|
    ((rules i).extends_unmarkedPass _ _).mono hrules

variable {rules visible above closer probes spellOut bearsCase} {order : List ι}
  {lex : α → Option Case} {xs : List α} {n : ℕ} {x : α} {c : Case} {m : Mechanism}

/-- Assignment is total: one valuation per NP. -/
@[simp] theorem length_assignBy :
    (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs)).length =
      xs.length := by
  simp [← (extends_assignBy rules visible above closer probes spellOut bearsCase order _).length_eq,
    lexicalValuation]

/-- Lexical case is kept through every domain. -/
theorem assignBy_getElem?_of_some (hx : xs[n]? = some x) (hc : lex x = some c) :
    (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs))[n]? =
      some (x, some (c, .lexical)) :=
  (extends_assignBy rules visible above closer probes spellOut bearsCase order _).getElem?_of_some
    (lexicalValuation_getElem?_of_some _ hx hc)

/-- A caseless NP is valued only with a case a domain's rules or one of its probes gives. -/
theorem case_mem_of_assignBy (hlex : lex x = none)
    (h : (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs))[n]? = some (x, some (c, m))) :
    (∃ i ∈ order, c ∈ (rules i).cases) ∨ ∃ i ∈ order, ∃ p ∈ probes i, p.1 = c := by
  rcases (extends_assignBy rules visible above closer probes spellOut bearsCase order
    _).of_getElem? h with
    h | h | ⟨-, h⟩
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · obtain ⟨i, hi, hv⟩ := h
    exact .inl ⟨i, hi, Rules.fst_mem_cases hv⟩
  · exact .inr h

/-- With no elsewhere case in any domain, nothing is valued as unmarked: an NP that no rule and
    no head reaches stays caseless. -/
theorem mechanism_ne_unmarked_of_assignBy (hr : ∀ i ∈ order, (rules i).unmarked = none)
    (h : (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs))[n]? = some (x, some (c, m))) : m ≠ .unmarked := by
  rintro rfl
  rcases (extends_assignBy rules visible above closer probes spellOut bearsCase order
    _).of_getElem? h with
    h | ⟨i, hi, ⟨hm, -⟩ | ⟨-, hu⟩⟩ | ⟨hm, -⟩
  · simpa using (lexicalValuation_getElem? h).2
  · cases hm
  · simp [hr i hi] at hu
  · cases hm

/-- A case valued under Agree is the case of a probe of some domain. -/
theorem exists_probe_of_assignBy
    (h : (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs))[n]? = some (x, some (c, .agree))) :
    ∃ i ∈ order, ∃ p ∈ probes i, p.1 = c := by
  rcases (extends_assignBy rules visible above closer probes spellOut bearsCase order
    _).of_getElem? h with
    h | ⟨-, -, ⟨hm, -⟩ | ⟨hm, -⟩⟩ | ⟨-, h⟩
  · simpa using (lexicalValuation_getElem? h).2
  · cases hm
  · cases hm
  · exact h

/-- With no dependent and no elsewhere case in any domain, a caseless NP is valued under Agree
    alone. -/
theorem mechanism_eq_agree_of_assignBy (hr : ∀ i ∈ order, rules i = {}) (hlex : lex x = none)
    (h : (assignBy rules visible above closer probes spellOut bearsCase order
      (lexicalValuation lex xs))[n]? = some (x, some (c, m))) : m = .agree := by
  rcases (extends_assignBy rules visible above closer probes spellOut bearsCase order
    _).of_getElem? h with
    h | ⟨i, hi, hv⟩ | ⟨hm, -⟩
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · simp [hr i hi, Rules.valuations] at hv
  · exact hm

end AssignBy

/-! ### Assignment over NPs placed by hand -/

section Assign

variable {α : Type*} (g : CaseAssigners) (np : α → PhasedNP)

/-- The probes of the domain of `c` among `probes`, the heads with the domain each agrees into:
    those with an Agree case, reaching what the domain sees. -/
def CaseAssigners.probesIn (probes : List (Cat × Cat)) (c : Cat) : List (Case × (α → Bool)) :=
  (probes.filter (·.2 == c)).filterMap fun pr ↦
    (g.agreeCase pr.1).map (·, fun x ↦ decide ((np x).visible c))

theorem CaseAssigners.mem_probesIn {probes : List (Cat × Cat)} {c : Cat}
    {p : Case × (α → Bool)} (hp : p ∈ g.probesIn np probes c) :
    ∃ pr ∈ probes, pr.2 = c ∧ g.agreeCase pr.1 = some p.1 := by
  obtain ⟨pr, hmem, hk⟩ := List.mem_filterMap.1 hp
  obtain ⟨k, hk', rfl⟩ := Option.map_eq_some_iff.1 hk
  obtain ⟨hmem, hc⟩ := List.mem_filter.1 hmem
  exact ⟨pr, hmem, by simpa using hc, hk'⟩

/-- Case for NPs placed by hand and listed from the highest down, the domains spelling out in
    `order`: assignment over domains with c-command as list order. -/
def CaseAssigners.assign (probes : List (Cat × Cat)) (order : List Cat) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  assignBy g.rules (fun c x ↦ (np x).visible c) (fun _ p q ↦ p.1 < q.1) (fun _ _ _ ↦ False)
    (g.probesIn np probes) (fun c x ↦ (np x).spellOut = c) (fun x ↦ (np x).bearsCase) order
    (lexicalValuation (fun x ↦ (np x).lexicalCase) xs)

end Assign

end Minimalist
