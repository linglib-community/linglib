/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Minimalist.Probe.Agree

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

* `PhasedNP`: an NP placed by hand: the case slot it enters with, absent for PRO, its phase, and
  the phase it shifts into.
* `CaseAssigners`: the rules of each phase head's domain and the case each head values.
* `assignBy`, `CaseAssigners.assign`: assignment over domains, and over NPs placed by hand.

## Main results

* `agreeList_relativized_eq_fillFirst`: Agree on a valuation is `Case.Valuation.fillFirst`.
* `fillFirst_eq_self_iff`, `fillFirst_eq_map`: it values the goal a probe finds, if any.
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

open Case (Mechanism Valuation slotValuation slotValuation_getElem?_of_valued
  slotValuation_getElem?)
open DependentCase

/-! ### Agree -/

section Agree

variable {α β : Type*} [DecidableEq β] {P : α → Prop} [DecidablePred P] {v : β}
  {s : Valuation α β}

/-- Agree into the domain `P` is `Valuation.fillFirst`: the probe relativized to the NPs that `P`
selects whose case is still unvalued, the activity condition of [chomsky-2000], over the valuation
as its own list of goals, copying by valuation of the goal's case slot. -/
theorem agreeList_relativized_eq_fillFirst (s : Valuation α β) :
    (Probe.relativized fun q : α × FeatureSlot β ↦ q.2 = .unvalued ∧ P q.1).agreeList
      (fun q ↦ (q.1, (q.2.valueWith v).untopD q.2)) s = s.fillFirst P v := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rw [Probe.agreeList_cons, Valuation.fillFirst_cons]
    by_cases h : p.2 = .unvalued ∧ P p.1
    · simp only [Probe.relativized_int, Probe.relativized_sat, h, and_self, ↓reduceIte,
        FeatureSlot.valueWith_unvalued, WithTop.untopD_coe]
    · simp only [Probe.relativized_int, Probe.relativized_sat, h, ↓reduceIte, ih]

/-- `fillFirst` values nothing iff the probe seeking an unvalued NP in its domain finds no goal, the
failed Agree of [preminger-2014]. -/
theorem fillFirst_eq_self_iff : s.fillFirst P v = s ↔
    (Probe.relativized fun p : α × FeatureSlot β ↦ p.2 = .unvalued ∧ P p.1).search s = none := by
  induction s with
  | nil => simp [Probe.search]
  | cons p s ih =>
    obtain ⟨x, k⟩ := p
    cases k <;> by_cases hx : P x <;> simp_all [Probe.search]

/-- `fillFirst` values the NP that the probe seeking an unvalued NP in its domain finds, its goal
(`Probe.search_eq_some_iff_finds`), and leaves the others as they are. -/
theorem fillFirst_eq_map [DecidableEq α] (hs : s.Nodup) :
    s.fillFirst P v = s.map fun p ↦
      if (Probe.relativized fun q : α × FeatureSlot β ↦ q.2 = .unvalued ∧ P q.1).search s =
          some p then (p.1, .valued v) else p := by
  induction s with
  | nil => rfl
  | cons q s ih =>
    obtain ⟨hq, hs⟩ := List.nodup_cons.mp hs
    by_cases h : q.2 = .unvalued ∧ P q.1
    · rw [Valuation.fillFirst_cons, ite_eq_left h, Probe.search,
        List.find?_cons_of_pos (by simpa using h), List.map_cons, ite_eq_left rfl]
      congr 1
      refine ((List.map_congr_left fun r hr ↦ ?_).trans (List.map_id' s)).symm
      rw [ite_eq_right (by rintro ⟨⟩; exact hq hr)]
    · rw [Valuation.fillFirst_cons, ite_eq_right h, Probe.search,
        List.find?_cons_of_neg (by simpa using h), List.map_cons, ← Probe.search, ih hs,
        ite_eq_right fun he ↦ hq (Probe.mem_of_search_eq_some he)]

end Agree

/-! ### Positions set by hand -/

/-- An NP placed by hand: the case slot it enters with, the phase whose domain merges it, and the
    phase it shifts into, if any. -/
structure PhasedNP where
  /-- The case slot the NP enters with: valued by a lexical head, absent for an NP that bears no
  case, such as PRO, which competes for dependent case without bearing it, and unvalued
  otherwise. -/
  case : FeatureSlot Case := .unvalued
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
  [∀ i, DecidablePred (spellOut i)]

/-- One domain: its dependent rules over the NPs it sees, `above i` ordering them by c-command,
    then each of its probes valuing the closest NP it reaches, then its elsewhere case. An NP that
    bears no case is passed over by all three. -/
def domainPassBy (i : ι) (s : Valuation α (Case × Mechanism)) : Valuation α (Case × Mechanism) :=
  (rules i).unmarkedPass (spellOut i) <|
    (probes i).foldl (fun st p ↦ Valuation.fillClosest (closer i) (p.2 ·) (p.1, .agree) st)
      ((rules i).dependentPassBy (above i) (visible i) s)

/-- The domains in the order `order`, innermost first. -/
def assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  order.foldl (fun st i ↦ domainPassBy rules visible above closer probes spellOut i st) s

/-- The valuations assignment over the domains `order` can make: those of the rules of a domain,
    and the case of one of its probes under Agree. -/
def valuationsBy (order : List ι) : Set (Case × Mechanism) :=
  {v | (∃ i ∈ order, v ∈ (rules i).valuations) ∨
    v.2 = .agree ∧ ∃ i ∈ order, ∃ p ∈ probes i, p.1 = v.1}

/-- Assignment over domains extends the valuation by what the rules and the probes value. -/
theorem extends_assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ valuationsBy rules probes order)
      (assignBy rules visible above closer probes spellOut order s) := by
  refine Valuation.Extends.foldl _ (fun i hi st ↦ ?_) s
  have hrules : ∀ v ∈ (rules i).valuations, v ∈ valuationsBy rules probes order :=
    fun v hv ↦ .inl ⟨i, hi, hv⟩
  refine (((rules i).extends_dependentPassBy _ _ st).mono hrules).trans <|
    (Valuation.Extends.foldl (F := fun p st ↦ Valuation.fillClosest (closer i) (p.2 ·) (p.1, .agree) st)
      _ (fun p hp st ↦ Valuation.extends_fillFirst (.inr ⟨rfl, i, hi, p, hp, rfl⟩) st) _).trans <|
    ((rules i).extends_unmarkedPass _ _).mono hrules

variable {rules visible above closer probes spellOut} {order : List ι}
  {case : α → FeatureSlot Case} {xs : List α} {n : ℕ} {x : α} {c : Case} {m : Mechanism}

/-- Assignment is total: one valuation per NP. -/
@[simp] theorem length_assignBy :
    (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs)).length =
      xs.length := by
  simp [← (extends_assignBy rules visible above closer probes spellOut order _).length_eq,
    slotValuation]

/-- Lexical case is kept through every domain. -/
theorem assignBy_getElem?_of_valued (hx : xs[n]? = some x) (hc : case x = .valued c) :
    (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs))[n]? =
      some (x, .valued (c, .lexical)) :=
  (extends_assignBy rules visible above closer probes spellOut order _).getElem?_of_some
    (slotValuation_getElem?_of_valued _ hx hc)

/-- A caseless NP is valued only with a case a domain's rules or one of its probes gives. -/
theorem case_mem_of_assignBy (hlex : (case x).value? = none)
    (h : (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs))[n]? = some (x, .valued (c, m))) :
    (∃ i ∈ order, c ∈ (rules i).cases) ∨ ∃ i ∈ order, ∃ p ∈ probes i, p.1 = c := by
  rcases (extends_assignBy rules visible above closer probes spellOut order
    _).of_getElem? h with
    h | h | ⟨-, h⟩
  · simp [(slotValuation_getElem? h).1] at hlex
  · obtain ⟨i, hi, hv⟩ := h
    exact .inl ⟨i, hi, Rules.fst_mem_cases hv⟩
  · exact .inr h

/-- With no elsewhere case in any domain, nothing is valued as unmarked: an NP that no rule and
    no head reaches stays caseless. -/
theorem mechanism_ne_unmarked_of_assignBy (hr : ∀ i ∈ order, (rules i).unmarked = none)
    (h : (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs))[n]? = some (x, .valued (c, m))) : m ≠ .unmarked := by
  rintro rfl
  rcases (extends_assignBy rules visible above closer probes spellOut order
    _).of_getElem? h with
    h | ⟨i, hi, ⟨hm, -⟩ | ⟨-, hu⟩⟩ | ⟨hm, -⟩
  · simpa using (slotValuation_getElem? h).2
  · cases hm
  · simp [hr i hi] at hu
  · cases hm

/-- A case valued under Agree is the case of a probe of some domain. -/
theorem exists_probe_of_assignBy
    (h : (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs))[n]? = some (x, .valued (c, .agree))) :
    ∃ i ∈ order, ∃ p ∈ probes i, p.1 = c := by
  rcases (extends_assignBy rules visible above closer probes spellOut order
    _).of_getElem? h with
    h | ⟨-, -, ⟨hm, -⟩ | ⟨hm, -⟩⟩ | ⟨-, h⟩
  · simpa using (slotValuation_getElem? h).2
  · cases hm
  · cases hm
  · exact h

/-- With no dependent and no elsewhere case in any domain, a caseless NP is valued under Agree
    alone. -/
theorem mechanism_eq_agree_of_assignBy (hr : ∀ i ∈ order, rules i = {})
    (hlex : (case x).value? = none)
    (h : (assignBy rules visible above closer probes spellOut order
      (slotValuation case xs))[n]? = some (x, .valued (c, m))) : m = .agree := by
  rcases (extends_assignBy rules visible above closer probes spellOut order
    _).of_getElem? h with
    h | ⟨i, hi, hv⟩ | ⟨hm, -⟩
  · simp [(slotValuation_getElem? h).1] at hlex
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
    (g.probesIn np probes) (fun c x ↦ (np x).spellOut = c) order
    (slotValuation (fun x ↦ (np x).case) xs)

end Assign

end Minimalist
