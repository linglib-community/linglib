module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Category.Basic
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.List.Lookmap

/-!
# Dependent case by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain: each phase
head's spell-out domain has its own high, low and elsewhere cases, the domains spell out
innermost first, and a case valued in an inner domain — or by a lexical head — is never
overwritten, so a dative valued in the verb phrase survives the clause. Functional heads may
also value case under Agree, each probing the highest caseless NP of the domain it agrees
into. A language's case assigners are the table of domain rules together with the Agree cases,
so a purely configurational system, a purely Agree-based one, and the hybrids are points in one
space.
Which functional heads a derivation contains is a fact about it, so assignment takes the
probes present with the domain each agrees into.

## Main definitions

* `agreeValue`: Agree into a domain, valuing the highest NP there whose case is unvalued.
* `PhasedNP`: an NP's position for case, its lexical case, the phase head whose domain merges
  it, and whether it has shifted to the clause edge.
* `CaseAssigners`: the phase heads in spell-out order with their rules, and the Agree cases.
* `CaseAssigners.assign`: case for every NP of a derivation, the NPs of any type, each with its
  position.

## Main results

* `agreeValue_getElem?`: Agree values at most one NP, an unvalued one in its domain.
* `agreeValue_eq_self_iff`, `agreeValue_eq_map`: Agree values nothing iff the probe seeking an
  unvalued NP in its domain finds no goal, and otherwise values the goal it finds.
* `extends_agreeValue`, `Case.Valuation.ValuedLE.agreeValue`: Agree extends the valuation by its
  value, and preserves which of two derivations values more nominals.
* `CaseAssigners.extends_assign`: assignment extends the lexical valuation by what the assigners
  value.
* `CaseAssigners.assign_length`: assignment is total.
* `CaseAssigners.assign_getElem?_of_some`: lexical case is kept.
* `CaseAssigners.case_mem_cases`: a caseless NP is valued only with a case the assigners
  mention.
* `CaseAssigners.mechanism_ne_unmarked`: assigners with no elsewhere case never value an NP as
  unmarked.
* `CaseAssigners.exists_probe_of_agree`, `CaseAssigners.mechanism_eq_agree`: a case valued under
  Agree is the case of a head that probes, and assigners with no configurational rule value under
  Agree alone.

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

variable {α β : Type*} {P : α → Bool} {v : β} {s t : Valuation α β}

/-- Agree into the domain `P` values `v` on the highest NP that `P` selects whose case is still
    unvalued, the activity condition of [chomsky-2000]. -/
def agreeValue (P : α → Bool) (v : β) : Valuation α β → Valuation α β
  | [] => []
  | p :: s => if p.2.isNone && P p.1 then (p.1, some v) :: s else p :: agreeValue P v s

@[simp] theorem agreeValue_nil : agreeValue P v [] = [] := rfl

@[simp] theorem agreeValue_cons (p : α × Option β) (s : Valuation α β) :
    agreeValue P v (p :: s) =
      if p.2.isNone && P p.1 then (p.1, some v) :: s else p :: agreeValue P v s := rfl

/-- Agree is `List.lookmap` of the update that values an unvalued NP in the domain. -/
theorem agreeValue_eq_lookmap (s : Valuation α β) :
    agreeValue P v s =
      s.lookmap fun p ↦ if p.2.isNone && P p.1 then some (p.1, some v) else none := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    by_cases h : p.2.isNone && P p.1
    · rw [List.lookmap_cons_some (b := (p.1, some v)) _ _ (by simp [h])]; simp [h]
    · rw [List.lookmap_cons_none _ _ (by simp [h])]; simp [h, ih]

/-- Agree values nothing iff the probe seeking an unvalued NP in its domain finds no goal, the
    failed Agree of [preminger-2014]. -/
theorem agreeValue_eq_self_iff : agreeValue P v s = s ↔
    (Probe.relativized fun p : α × Option β ↦ p.2.isNone && P p.1).search s = none := by
  induction s with
  | nil => simp [Probe.search]
  | cons p s ih =>
    obtain ⟨x, _ | a⟩ := p <;> cases hx : P x <;> simp_all [Probe.search]

/-- Agree values the NP that the probe seeking an unvalued NP in its domain finds, its goal
(`Probe.search_eq_some_iff_finds`), and leaves the others as they are. -/
theorem agreeValue_eq_map [DecidableEq α] [DecidableEq β] (hs : s.Nodup) :
    agreeValue P v s = s.map fun p ↦
      if (Probe.relativized fun q : α × Option β ↦ q.2.isNone && P q.1).search s = some p then
        (p.1, some v) else p := by
  induction s with
  | nil => rfl
  | cons q s ih =>
    obtain ⟨hq, hs⟩ := List.nodup_cons.mp hs
    by_cases h : q.2.isNone && P q.1
    · rw [agreeValue_cons, ite_eq_left h, Probe.search, List.find?_cons_of_pos (by simpa using h),
        List.map_cons, ite_eq_left rfl]
      congr 1
      refine ((List.map_congr_left fun r hr ↦ ?_).trans (List.map_id' s)).symm
      rw [ite_eq_right (by rintro ⟨⟩; exact hq hr)]
    · rw [agreeValue_cons, ite_eq_right h, Probe.search,
        List.find?_cons_of_neg (by simpa using h), List.map_cons, ← Probe.search, ih hs,
        ite_eq_right fun he ↦ hq (Probe.mem_of_search_eq_some he)]

/-- Agree leaves every NP as it was except at most one, an unvalued NP in its domain, which it
    values. -/
theorem agreeValue_getElem? (s : Valuation α β) (i : ℕ) :
    (agreeValue P v s)[i]? = s[i]? ∨
      ∃ x, s[i]? = some (x, none) ∧ P x ∧ (agreeValue P v s)[i]? = some (x, some v) := by
  induction s generalizing i with
  | nil => simp
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    by_cases h : a.isNone && P x
    · rcases i with _ | i
      · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨rfl, hx⟩ := h
        simp [hx]
      · simp [h]
    · rcases i with _ | i
      · simp [h]
      · simpa [h] using ih i

/-- Agree extends the valuation by its value. -/
theorem extends_agreeValue {p : β → Prop} (hv : p v) :
    ∀ s : Valuation α β, s.Extends p (agreeValue P v s)
  | [] => .nil
  | (x, none) :: s => by
    cases hx : P x <;>
      simp only [agreeValue_cons, Option.isNone_none, hx, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte]
    · exact .cons ⟨rfl, .inl rfl⟩ (extends_agreeValue hv s)
    · exact .cons ⟨rfl, .inr ⟨rfl, by simpa using hv⟩⟩ (Case.Valuation.Extends.refl s)
  | (x, some w) :: s => by
    simp only [agreeValue_cons, Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact .cons ⟨rfl, .inl rfl⟩ (extends_agreeValue hv s)

@[simp] theorem length_agreeValue : (agreeValue P v s).length = s.length :=
  ((extends_agreeValue (p := fun _ ↦ True) trivial s).length_eq).symm

/-- Agree only adds values. -/
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
    rcases a with _ | a <;> rcases b with _ | b <;> cases hx : P x <;>
      simp only [agreeValue_cons, Option.isNone_none, Option.isNone_some, hx, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ hst
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ (Case.Valuation.ValuedLE.trans hst (valuedLE_agreeValue t))
    · simp at hab
    · simp at hab
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ ih

/-- Agree commutes with relabelling the NPs and the values, provided the relabelling keeps what
    is in the domain and what is valued. -/
theorem agreeValue_map {α' β' : Type*} {P' : α' → Bool} {v' : β'} (f : α → α') (g : β → β')
    (hP : ∀ x, P' (f x) = P x) (hv : g v = v') (s : List (α × Option β)) :
    agreeValue P' v' (s.map (Prod.map f (Option.map g))) =
      (agreeValue P v s).map (Prod.map f (Option.map g)) := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    rcases a with _ | a
    · by_cases hx : P x <;> simp [hx, hP, hv, ih]
    · simp [ih]

end Agree

/-- An NP's position for case is any case a lexical head has valued, the phase head whose
    spell-out domain merges it, and whether it has shifted to the clause edge, where C's domain
    spells it out. -/
structure PhasedNP where
  lexicalCase : Option Case := none
  phase : Cat := .C
  shifted : Bool := false
  deriving DecidableEq, Repr

/-- Whether the NP is in the domain of `c` when it spells out. -/
def PhasedNP.visible (np : PhasedNP) (c : Cat) : Bool := np.phase == c || (np.shifted && c == .C)

/-- The phase head whose elsewhere case the NP falls back on. -/
def PhasedNP.spellOut (np : PhasedNP) : Cat := if np.shifted then .C else np.phase

/-- The case assigners of a language, in both modalities of [baker-vinokurova-2010]: the phase
    heads in spell-out order with the dependent-case rules of their domains, and the case each
    functional head values under Agree. -/
structure CaseAssigners where
  domains : List (Cat × Rules)
  agree : List (Cat × Case) := []
  deriving DecidableEq, Repr

/-- The rules of the domain of `c`. -/
def CaseAssigners.rules (g : CaseAssigners) (c : Cat) : Rules :=
  ((g.domains.find? (·.1 == c)).map (·.2)).getD {}

/-- The case `h` values under Agree, if any. -/
def CaseAssigners.agreeCase (g : CaseAssigners) (h : Cat) : Option Case :=
  (g.agree.find? (·.1 == h)).map (·.2)

/-- The cases the assigners can value a caseless NP with. -/
def CaseAssigners.cases (g : CaseAssigners) : List Case :=
  g.domains.flatMap (·.2.cases) ++ g.agree.map (·.2)

section Assign

variable {α : Type*} (g : CaseAssigners) (np : α → PhasedNP)

/-- The head `h` probing the domain of `c` values what the assigners let it. The NPs are of
    any type, `np` giving each its position. -/
def probePass (c h : Cat) (s : Valuation α (Case × Mechanism)) : Valuation α (Case × Mechanism) :=
  match g.agreeCase h with
  | some k => agreeValue (fun x ↦ (np x).visible c) (k, .agree) s
  | none => s

/-- One spell-out domain: its dependent rules, then its probes in order, then its elsewhere
    case. -/
def domainPass (probes : List (Cat × Cat)) (c : Cat) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  (g.rules c).unmarkedPass (fun x ↦ (np x).spellOut == c) <|
    (probes.filter (·.2 == c)).foldl (fun st hp ↦ probePass g np c hp.1 st)
      ((g.rules c).dependentPass (fun x ↦ (np x).visible c) s)

/-- The domains spelling out in the assigners' order. -/
def CaseAssigners.derive (probes : List (Cat × Cat)) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  (g.domains.map (·.1)).foldl (fun st c ↦ domainPass g np probes c st) s

/-- Case for every NP, the domains spelling out in the assigners' order. `probes` lists the
    functional heads present with the phase head whose domain each agrees into. -/
def CaseAssigners.assign (probes : List (Cat × Cat)) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  g.derive np probes (lexicalValuation (fun x ↦ (np x).lexicalCase) xs)

end Assign

/-! ### What the assigners value -/

/-- The valuations the assigners can make in a derivation whose functional heads are `probes`:
    those of the rules of a domain, and the case one of the heads values under Agree. -/
def CaseAssigners.valuations (g : CaseAssigners) (probes : List (Cat × Cat)) :
    Set (Case × Mechanism) :=
  {v | (∃ d ∈ g.domains, v ∈ d.2.valuations) ∨
    v.2 = .agree ∧ ∃ hp ∈ probes, g.agreeCase hp.1 = some v.1}

theorem CaseAssigners.rules_valuations_subset (g : CaseAssigners) (probes : List (Cat × Cat))
    (c : Cat) : (g.rules c).valuations ⊆ g.valuations probes := by
  intro v hv
  unfold CaseAssigners.rules at hv
  rcases hf : g.domains.find? (·.1 == c) with _ | d
  · simp [hf, Rules.valuations] at hv
  · rw [hf] at hv
    exact .inl ⟨d, List.mem_of_find?_eq_some hf, hv⟩

theorem CaseAssigners.agreeCase_mem_cases {g : CaseAssigners} {h : Cat} {c : Case}
    (hc : g.agreeCase h = some c) : c ∈ g.cases := by
  unfold CaseAssigners.agreeCase at hc
  obtain ⟨⟨d, k⟩, hf, hk⟩ := Option.map_eq_some_iff.1 hc
  subst hk
  exact List.mem_append_right _ (List.mem_map.2 ⟨(d, k), List.mem_of_find?_eq_some hf, rfl⟩)

theorem CaseAssigners.fst_mem_cases {g : CaseAssigners} {probes : List (Cat × Cat)}
    {v : Case × Mechanism} (hv : v ∈ g.valuations probes) : v.1 ∈ g.cases := by
  rcases hv with ⟨d, hd, hv⟩ | ⟨-, hp, -, hh⟩
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨d, hd, Rules.fst_mem_cases hv⟩)
  · exact g.agreeCase_mem_cases hh

section Assign

variable {α : Type*} (g : CaseAssigners) (np : α → PhasedNP)

theorem extends_probePass {probes : List (Cat × Cat)} {hp : Cat × Cat} (hmem : hp ∈ probes)
    (c : Cat) (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (probePass g np c hp.1 s) := by
  unfold probePass
  split
  · exact extends_agreeValue (.inr ⟨rfl, hp, hmem, ‹_›⟩) s
  · exact .refl s

theorem extends_domainPass (probes : List (Cat × Cat)) (c : Cat)
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (domainPass g np probes c s) :=
  (((g.rules c).extends_dependentPass _ s).mono fun _ h ↦
      g.rules_valuations_subset probes c h).trans <|
    (Valuation.Extends.foldl _ (fun _ hmem ↦
      extends_probePass g np (List.mem_of_mem_filter hmem) c) _).trans <|
      ((g.rules c).extends_unmarkedPass _ _).mono fun _ h ↦ g.rules_valuations_subset probes c h

/-- A derivation extends the valuation by what the assigners value. -/
theorem CaseAssigners.extends_derive (probes : List (Cat × Cat))
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (g.derive np probes s) :=
  Valuation.Extends.foldl _ (fun c _ st ↦ extends_domainPass g np probes c st) s

/-- Assignment extends the lexical valuation by what the assigners value. -/
theorem CaseAssigners.extends_assign (probes : List (Cat × Cat)) (xs : List α) :
    (lexicalValuation (fun x ↦ (np x).lexicalCase) xs).Extends (· ∈ g.valuations probes)
      (g.assign np probes xs) :=
  g.extends_derive np probes _

/-- Assignment is total: one valuation per NP. -/
@[simp] theorem CaseAssigners.assign_length (probes : List (Cat × Cat)) (xs : List α) :
    (g.assign np probes xs).length = xs.length := by
  simp [← (g.extends_assign np probes xs).length_eq, lexicalValuation]

variable {g np} {probes : List (Cat × Cat)} {xs : List α} {i : ℕ} {x : α}

/-- Lexical case is kept through every domain. -/
theorem CaseAssigners.assign_getElem?_of_some {c : Case} (hx : xs[i]? = some x)
    (hc : (np x).lexicalCase = some c) :
    (g.assign np probes xs)[i]? = some (x, some (c, .lexical)) :=
  (g.extends_assign np probes xs).getElem?_of_some (lexicalValuation_getElem?_of_some _ hx hc)

/-- A caseless NP is valued only with a case the assigners mention. -/
theorem CaseAssigners.case_mem_cases {c : Case} {m : Mechanism}
    (hlex : (np x).lexicalCase = none) (h : (g.assign np probes xs)[i]? = some (x, some (c, m))) :
    c ∈ g.cases := by
  rcases (g.extends_assign np probes xs).of_getElem? h with h | h
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · exact CaseAssigners.fst_mem_cases h

/-- Assigners with no elsewhere case in any domain never value an NP as unmarked: an NP that
    no rule and no head reaches stays caseless. -/
theorem CaseAssigners.mechanism_ne_unmarked (hg : ∀ d ∈ g.domains, d.2.unmarked = none)
    {c : Case} {m : Mechanism} (h : (g.assign np probes xs)[i]? = some (x, some (c, m))) :
    m ≠ .unmarked := by
  rintro rfl
  rcases (g.extends_assign np probes xs).of_getElem? h with h | h
  · simpa using (lexicalValuation_getElem? h).2
  · rcases h with ⟨d, hd, ⟨hm, -⟩ | ⟨-, hu⟩⟩ | ⟨hm, -⟩
    · cases hm
    · simp [hg d hd] at hu
    · cases hm

/-- A case valued under Agree is the case of a head that probes in the derivation. -/
theorem CaseAssigners.exists_probe_of_agree {c : Case}
    (h : (g.assign np probes xs)[i]? = some (x, some (c, .agree))) :
    ∃ hp ∈ probes, g.agreeCase hp.1 = some c := by
  rcases (g.extends_assign np probes xs).of_getElem? h with h | h
  · simpa using (lexicalValuation_getElem? h).2
  · rcases h with ⟨d, -, ⟨hm, -⟩ | ⟨hm, -⟩⟩ | ⟨-, h⟩
    · cases hm
    · cases hm
    · exact h

/-- Assigners with no dependent and no elsewhere case in any domain value a caseless NP under
    Agree alone. -/
theorem CaseAssigners.mechanism_eq_agree (hg : ∀ d ∈ g.domains, d.2 = {}) {c : Case}
    {m : Mechanism} (hlex : (np x).lexicalCase = none)
    (h : (g.assign np probes xs)[i]? = some (x, some (c, m))) : m = .agree := by
  rcases (g.extends_assign np probes xs).of_getElem? h with h | h
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · rcases h with ⟨d, hd, hv⟩ | ⟨hm, -⟩
    · simp [hg d hd, Rules.valuations] at hv
    · exact hm

end Assign

end Minimalist
