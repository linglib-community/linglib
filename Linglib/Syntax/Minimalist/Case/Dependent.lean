module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Category.Basic
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.List.Lookmap

/-!
# Dependent case by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain, innermost first,
each phase head's domain with its own high, low and elsewhere cases, and functional heads value
case under Agree on the closest caseless NP they reach; a value is never overwritten, so a dative
valued in the verb phrase survives the clause. A language's case assigners are the table of
domain rules with the Agree cases, so configurational, Agree-based and hybrid systems are points
in one space. Assignment over domains (`CaseAssigners.assignBy`) takes what each domain sees,
c-command among its NPs and its probes as parameters; here the NPs are listed by height with
their domains set by hand (`PhasedNP`, `CaseAssigners.assign`), which is that assignment with
c-command as list order (`CaseAssigners.assign_eq_assignBy`), and `Case/SyntacticObject.lean`
reads them off an object.

## Main definitions

* `agreeValue`, `agreeValueOn`: Agree on the highest caseless NP of a domain, or the closest.
* `PhasedNP`: an NP's lexical case, the phase whose domain merges it, and whether it shifted.
* `CaseAssigners`: the phase heads in spell-out order with their rules, and the Agree cases.
* `CaseAssigners.assignBy`, `CaseAssigners.assign`: assignment over domains, and by the list.

## Main results

* `agreeValue_eq_self_iff`, `agreeValue_eq_map`: Agree values the goal a probe finds, if any.
* `CaseAssigners.assign_eq_assignBy`: the list is assignment over domains in list order.
* `CaseAssigners.extends_assign`, `CaseAssigners.extends_assignBy`: assignment extends the
  lexical valuation by what the assigners value.
* `CaseAssigners.mechanism_ne_unmarked`, `CaseAssigners.exists_probe_of_agree`,
  `CaseAssigners.mechanism_eq_agree`: what values a case, given the assigners.

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

/-- Agree reaches the same NP under a narrower domain that still holds the first unvalued NP of
    the wider one. -/
theorem agreeValue_congr {Q : α → Bool} (hQ : ∀ x, Q x → P x)
    (hfirst : ∀ (i : ℕ) (x : α), s[i]? = some (x, none) → P x →
      (∀ j < i, ∀ y, s[j]? = some (y, none) → ¬ P y) → Q x) :
    agreeValue Q v s = agreeValue P v s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    by_cases hp : a.isNone && P x
    · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨rfl, hPx⟩ := hp
      have hQx : Q x := hfirst 0 x rfl hPx fun j hj ↦ absurd hj (Nat.not_lt_zero j)
      simp [hQx, hPx]
    · have hq : ¬ (a.isNone && Q x) := fun h ↦ hp (by
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, hQ x h.2⟩)
      rw [agreeValue_cons, agreeValue_cons, ite_eq_right hq, ite_eq_right hp]
      refine congrArg _ (ih fun i y hy hPy hpre ↦ hfirst (i + 1) y hy hPy fun j hj z hz ↦ ?_)
      rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hz
        obtain ⟨rfl, rfl⟩ := hz
        simpa using hp
      · exact hpre j (by omega) z hz

/-- Agree with closeness `lt`, `lt y x` saying `y` is closer to the probe than `x`: the unvalued
    NP of the domain that no other is closer than, the first of them if several are. -/
def agreeValueOn (lt : α → α → Prop) [DecidableRel lt] (P : α → Bool) (v : β)
    (s : Valuation α β) : Valuation α β :=
  agreeValue (fun x ↦ P x && !s.any fun q ↦ q.2.isNone && P q.1 && decide (lt q.1 x)) v s

/-- On NPs listed closest first, Agree with closeness is Agree over the list. -/
theorem agreeValueOn_eq_agreeValue {lt : α → α → Prop} [DecidableRel lt]
    (h : ∀ (i j : ℕ) (x y : α), s[i]? = some (x, none) → P x → s[j]? = some (y, none) →
      P y → (lt x y ↔ i < j)) :
    agreeValueOn lt P v s = agreeValue P v s := by
  refine agreeValue_congr (fun x hx ↦ by simp_all) fun i x hx hPx hpre ↦ ?_
  simp only [hPx, Bool.true_and, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true,
    Option.isNone_iff_eq_none, decide_eq_true_eq, not_and]
  intro ⟨y, w⟩ hq ⟨hw, hPy⟩ hyx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
  simp only at hw hPy hyx
  subst hw
  exact hpre j ((h j i y x hj hPy hx hPx).1 hyx) y hj hPy

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
def CaseAssigners.probePass (c h : Cat) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  match g.agreeCase h with
  | some k => agreeValue (fun x ↦ (np x).visible c) (k, .agree) s
  | none => s

/-- One spell-out domain: its dependent rules, then its probes in order, then its elsewhere
    case. -/
def CaseAssigners.domainPass (probes : List (Cat × Cat)) (c : Cat)
    (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  (g.rules c).unmarkedPass (fun x ↦ (np x).spellOut == c) <|
    (probes.filter (·.2 == c)).foldl (fun st hp ↦ g.probePass np c hp.1 st)
      ((g.rules c).dependentPass (fun x ↦ (np x).visible c) s)

/-- The domains spelling out in the assigners' order. -/
def CaseAssigners.derive (probes : List (Cat × Cat)) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  (g.domains.map (·.1)).foldl (fun st c ↦ g.domainPass np probes c st) s

/-- Case for every NP, the domains spelling out in the assigners' order. `probes` lists the
    functional heads present with the phase head whose domain each agrees into. -/
def CaseAssigners.assign (probes : List (Cat × Cat)) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  g.derive np probes (lexicalValuation (fun x ↦ (np x).lexicalCase) xs)

end Assign

/-! ### Assignment over domains -/

section AssignBy

variable {α ι : Type*} (g : CaseAssigners) (cat : ι → Cat) (visible : ι → α → Bool)
  (above : ι → α → α → Prop) [∀ i, DecidableRel (above i)]
  (probes : ι → List (Case × (α → Bool))) (spellOut : ι → α → Bool)

/-- One domain: its dependent rules over the NPs it sees, `above i` ordering them by c-command,
    then each of its probes valuing the closest NP it reaches, then its elsewhere case. -/
def CaseAssigners.domainPassBy (i : ι) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  (g.rules (cat i)).unmarkedPass (spellOut i) <|
    (probes i).foldl (fun st p ↦ agreeValueOn (above i) p.2 (p.1, .agree) st)
      ((g.rules (cat i)).dependentPassOn (above i) (visible i) s)

/-- The domains in the order `order`, innermost first. -/
def CaseAssigners.assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  order.foldl (fun st i ↦ g.domainPassBy cat visible above probes spellOut i st) s

/-- The valuations assignment over the domains `order` can make: those of the rules of a domain,
    and the case of one of its probes under Agree. -/
def CaseAssigners.valuationsBy (order : List ι) : Set (Case × Mechanism) :=
  {v | (∃ i ∈ order, v ∈ (g.rules (cat i)).valuations) ∨
    v.2 = .agree ∧ ∃ i ∈ order, ∃ p ∈ probes i, p.1 = v.1}

/-- Assignment over domains extends the valuation by what the rules and the probes value. -/
theorem CaseAssigners.extends_assignBy (order : List ι) (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuationsBy cat probes order)
      (g.assignBy cat visible above probes spellOut order s) := by
  refine Valuation.Extends.foldl _ (fun i hi st ↦ ?_) s
  have hrules : ∀ v ∈ (g.rules (cat i)).valuations, v ∈ g.valuationsBy cat probes order :=
    fun v hv ↦ .inl ⟨i, hi, hv⟩
  refine (((g.rules (cat i)).extends_dependentPassOn _ _ st).mono hrules).trans <|
    (Valuation.Extends.foldl (F := fun p st ↦ agreeValueOn (above i) p.2 (p.1, .agree) st)
      _ (fun p hp st ↦ extends_agreeValue (.inr ⟨rfl, i, hi, p, hp, rfl⟩) st) _).trans <|
    ((g.rules (cat i)).extends_unmarkedPass _ _).mono hrules

end AssignBy

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

theorem CaseAssigners.extends_probePass {probes : List (Cat × Cat)} {hp : Cat × Cat}
    (hmem : hp ∈ probes)
    (c : Cat) (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (g.probePass np c hp.1 s) := by
  unfold CaseAssigners.probePass
  split
  · exact extends_agreeValue (.inr ⟨rfl, hp, hmem, ‹_›⟩) s
  · exact .refl s

theorem CaseAssigners.extends_domainPass (probes : List (Cat × Cat)) (c : Cat)
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (g.domainPass np probes c s) :=
  (((g.rules c).extends_dependentPass _ s).mono fun _ h ↦
      g.rules_valuations_subset probes c h).trans <|
    (Valuation.Extends.foldl _ (fun _ hmem ↦
      g.extends_probePass np (List.mem_of_mem_filter hmem) c) _).trans <|
      ((g.rules c).extends_unmarkedPass _ _).mono fun _ h ↦ g.rules_valuations_subset probes c h

theorem CaseAssigners.extends_derive (probes : List (Cat × Cat))
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ g.valuations probes) (g.derive np probes s) :=
  Valuation.Extends.foldl _ (fun c _ st ↦ g.extends_domainPass np probes c st) s

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

/-! ### The list as an assignment over domains -/

private theorem map_fst_of_extends {α β : Type*} {p : β → Prop} {s t : Valuation α β}
    (h : s.Extends p t) : t.map Prod.fst = s.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, hab.1, ih]

/-- Assignment by the list is assignment by domains, the NPs ordered by c-command as they are
    listed and each probe reaching what its domain sees. -/
theorem CaseAssigners.assign_eq_assignBy {α : Type*} [DecidableEq α] (g : CaseAssigners)
    (np : α → PhasedNP) (probes : List (Cat × Cat)) {xs : List α} (hxs : xs.Nodup) :
    g.assign np probes xs = g.assignBy id (fun c x ↦ (np x).visible c)
      (fun _ x y ↦ xs.idxOf x < xs.idxOf y)
      (fun c ↦ (probes.filter (·.2 == c)).filterMap fun hp ↦
        (g.agreeCase hp.1).map (·, fun x ↦ (np x).visible c))
      (fun c x ↦ (np x).spellOut == c) (g.domains.map (·.1))
      (lexicalValuation (fun x ↦ (np x).lexicalCase) xs) := by
  have hord : ∀ st : Valuation α (Case × Mechanism), st.map Prod.fst = xs →
      ∀ (i j : ℕ) (x y : α) (a b : Option (Case × Mechanism)), st[i]? = some (x, a) →
        st[j]? = some (y, b) → (xs.idxOf x < xs.idxOf y ↔ i < j) := by
    intro st hst i j x y a b hi hj
    have hxi : xs[i]? = some x := by rw [← hst, List.getElem?_map, hi]; rfl
    have hyj : xs[j]? = some y := by rw [← hst, List.getElem?_map, hj]; rfl
    obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hxi
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hyj
    simp [hxs]
  have hstep : ∀ c (st : Valuation α (Case × Mechanism)), st.map Prod.fst = xs →
      g.domainPass np probes c st = g.domainPassBy id (fun c x ↦ (np x).visible c)
        (fun _ x y ↦ xs.idxOf x < xs.idxOf y)
        (fun c ↦ (probes.filter (·.2 == c)).filterMap fun hp ↦
          (g.agreeCase hp.1).map (·, fun x ↦ (np x).visible c))
        (fun c x ↦ (np x).spellOut == c) c st := by
    intro c st hst
    rw [CaseAssigners.domainPass, CaseAssigners.domainPassBy, id,
      Rules.dependentPassOn_eq_dependentPass _ fun i j x y hi _ hj _ ↦
        hord st hst i j x y _ _ hi hj]
    congr 1
    have hst' := (map_fst_of_extends ((g.rules c).extends_dependentPass
      (fun x ↦ (np x).visible c) st)).trans hst
    generalize (g.rules c).dependentPass (fun x ↦ (np x).visible c) st = st' at hst'
    induction probes.filter (·.2 == c) generalizing st' with
    | nil => rfl
    | cons hp L ih =>
      rw [List.foldl_cons, List.filterMap_cons]
      unfold CaseAssigners.probePass
      rcases hk : g.agreeCase hp.1 with _ | k
      · exact ih st' hst'
      · rw [Option.map_some, List.foldl_cons, agreeValueOn_eq_agreeValue fun i j x y hi _ hj _ ↦
          hord st' hst' i j x y _ _ hi hj]
        exact ih _ ((map_fst_of_extends (extends_agreeValue (p := fun _ ↦ True) trivial st')).trans
          hst')
  rw [CaseAssigners.assign, CaseAssigners.derive, CaseAssigners.assignBy]
  have h0 : (lexicalValuation (fun x ↦ (np x).lexicalCase) xs).map Prod.fst = xs := by
    simp [lexicalValuation, Valuation.initial, Function.comp_def]
  generalize lexicalValuation (fun x ↦ (np x).lexicalCase) xs = st at h0
  induction g.domains.map (·.1) generalizing st with
  | nil => rfl
  | cons c L ih =>
    rw [List.foldl_cons, List.foldl_cons, hstep c st h0]
    refine ih _ ?_
    rw [← hstep c st h0]
    exact (map_fst_of_extends (g.extends_domainPass np probes c st)).trans h0

end Minimalist
