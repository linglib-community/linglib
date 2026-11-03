/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.ClemDeal2026
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Kawapanan.Shawi.Basic
public import Linglib.Morphology.DistributedMorphology.Fission
public import Studies.Baker2015
public import Studies.BejarRezac2009
public import Studies.Deal2024

/-!
# Clem and Deal (2026): Dependent case by Agree

A probe flags each goal with all the features its head holds, so [a second goal receives the first
goal's φ-features](##flagged_pair), and a dependent case is the vocabulary item spelling out that φ
on a nominal. The Shawi subject surfaces with [*-ri* and the verb's object
agreement](##forms_of_licit) when the strictly descending probe on v reaches it after a high object,
and the same machinery [predicts the rows of four languages](##rows_predicted). Since a hierarchy is
a probe's run over a feature geometry, [no probe puts third person above
second](##not_forall_iff_rule37), and [a third-person first goal never bleeds a probe that can reach
a second goal](##directionality), whence ergative with forward hierarchies and accusative with
reverse.

## Implementation notes

* Items (36a) and (36c) tie in size on a first person, who bears both [SPKR] and [PART]; the order
  of `objectItems` resolves the tie, and the inclusive items, absent from (36), are not encoded.
* `objectAgreement` states v after Kinyalolo's Constraint (35) has removed the subject's features;
  the impoverishment itself is not encoded.
* The rows of (42), (45), (46) and (49) are read with the object positions of Shawi, as note 38
  assumes for Shiwilu.

## Errata

* Generalizations (5) and (10) and table 7 give dependent case when the subject is at least as high
  as the object, but (15) rules out every first-person object, so [the mechanism gives no ergative
  at 1→1 and does give it at 2→2](##diagonal). The tables have no reflexive rows.
* (6b) prints the subject's object agreement as *-nke(ma)*, but (36d) spells out [PART, AUG, v] as a
  whole and none of the routes to its absence in §3.3 deletes [AUG] alone, so bare *-nke* on the
  subject of a 2PL object is not derived.

## References

* [clem-deal-2026]
* [deal-2024]
* [deal-2010]
* [clem-2019]
* [bejar-rezac-2009]
* [baker-2015]
* [baker-vinokurova-2010]
* [barany-sheehan-2024]
* [valenzuela-2011]
* [maslova-2003]
* [van-urk-2015]
* [bourdeau-2015]
* [barraza-de-garcia-2005]
* [harley-ritter-2002]
-/

@[expose] public section

namespace ClemDeal2026

open Deal2024 Phi.PersonSegment DistributedMorphology Morphology.Exponence
open Clause (Scenario)
open Baker2015 (Arg)
open scoped DistributedMorphology.VocabularyItem

/-! ### Goal flagging -/

/-- The head a probe sits on, v between object and subject ((40)) or T above both ((41)). -/
inductive Locus
  | v
  | T
  deriving DecidableEq, Repr

/-- The features of a nominal and of a flag: a person segment, [AUG], the category feature of a
head, and [D]. -/
inductive Feature
  | person (s : Phi.PersonSegment)
  | aug
  | head (l : Locus)
  | d
  deriving DecidableEq, Repr

/-- A nominal is a person with a number. -/
abbrev Nominal := Person × Number

/-- The φ-features of a nominal. -/
def phi (a : Nominal) : Finset Feature :=
  (spec a.1).image .person ∪ if a.2 = .augmented then {.aug} else ∅

/-- The goals a probe of grammar `g` Agrees with, in search order. -/
def agreed (g : Grammar) (goals : List (Nominal)) : List (Nominal) :=
  (run g Prod.fst goals).interacted

/-- Agree is bidirectional ((31)): a head holding `fs` flags its next goal with all of `fs` and
takes on the goal's φ-features. -/
def flagsFrom : Finset Feature → List (Nominal) → List ((Nominal) × Finset Feature)
  | _, [] => []
  | fs, a :: as => (a, fs) :: flagsFrom (fs ∪ phi a) as

/-- The goals of a probe on `l` with their flags, the head starting with its category feature. -/
def flagged (g : Grammar) (l : Locus) (goals : List (Nominal)) :
    List ((Nominal) × Finset Feature) :=
  flagsFrom {.head l} (agreed g goals)

theorem agreed_pair (g : Grammar) (a b : Nominal) :
    agreed g [a, b] = a :: if Licit g ⟨b.1, a.1⟩ then [b] else [] :=
  interacted_run_pair g Prod.fst a b

/-- Feature transfer under Agree is transitive ((31)): a probe flags its first goal with its
category feature alone and, if it goes on to a second, flags that with the first goal's φ-features
as well. -/
theorem flagged_pair (g : Grammar) (l : Locus) (a b : Nominal) :
    flagged g l [a, b] =
      (a, {.head l}) :: if Licit g ⟨b.1, a.1⟩ then [(b, {.head l} ∪ phi a)] else [] := by
  rw [flagged, agreed_pair]
  split_ifs <;> rfl

theorem flagged_singleton (g : Grammar) (l : Locus) (a : Nominal) :
    flagged g l [a] = [(a, {.head l})] := by
  have h : agreed g [a] = [a] := by
    obtain ⟨_ | x, dyn⟩ := g
    · simp [agreed, run, Minimalist.Probe.Dynamic.agree_cons]
    · by_cases hx : x ∈ spec a.1 <;> simp [agreed, run, Minimalist.Probe.Dynamic.agree_cons, hx]
  rw [flagged, h]
  rfl

/-- A probe assigns dependent case when one of its goals bears a flag with φ in it, the structure
that a dependent-case vocabulary item realizes ((31), (34), (43)). -/
def DependentCase (g : Grammar) (l : Locus) (goals : List (Nominal)) : Prop :=
  ∃ x ∈ flagged g l goals, Feature.person .pi ∈ x.2

instance (g : Grammar) (l : Locus) (goals : List (Nominal)) :
    Decidable (DependentCase g l goals) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

theorem pi_mem_phi (a : Nominal) : Feature.person .pi ∈ phi a := by
  simp [phi]

-- (53)
theorem dependentCase_pair_iff (g : Grammar) (l : Locus) (a b : Nominal) :
    DependentCase g l [a, b] ↔ Licit g ⟨b.1, a.1⟩ := by
  simp only [DependentCase, flagged_pair]
  split_ifs with h <;> simp [h, pi_mem_phi]

theorem not_dependentCase_singleton (g : Grammar) (l : Locus) (a : Nominal) :
    ¬ DependentCase g l [a] := by
  simp [DependentCase, flagged_singleton]

/-! ### The position of the object -/

/-- An object sits above the phase boundary of the categorizing v, visible to the v probe, or in
its base position inside that phase, invisible to it ((30)). -/
inductive ObjectPosition
  | high
  | low
  deriving DecidableEq, Repr

/-- On the surface an object follows the subject, precedes a landmark of the clause (the subject in
(26b), a VP adverb in (42a)), is dropped, follows a VP adverb ((42b)), or does not exist. -/
inductive ObjectSyntax
  | inSitu
  | fronted
  | dropped
  | belowAdverb
  | absent
  deriving DecidableEq, Repr

/-- An object of person `p` with surface syntax `x` may occupy these positions (§3.2). Local
persons move to the high position obligatorily and third persons optionally; fronting and pro-drop
((21a), as in Dinka [van-urk-2015]) require it; and a clause with no object runs as one with a low
object ((24)). -/
def positions (p : Person) : ObjectSyntax → List ObjectPosition
  | .inSitu => if p.IsSAP then [.high] else [.high, .low]
  | .fronted | .dropped => [.high]
  | .belowAdverb | .absent => [.low]

/-- The goals a probe at `l` meets: the object and then the subject on v ((22)), by the cyclic
expansion of [bejar-rezac-2009] ((13)); the subject and then the object on T ((41)); and the
subject alone when the object is low ((24)). -/
def goals (l : Locus) (pos : ObjectPosition) (subj obj : Nominal) : List (Nominal) :=
  match l, pos with
  | .v, .high => [obj, subj]
  | .T, .high => [subj, obj]
  | _, .low => [subj]

/-- The argument bearing a probe's dependent case, its second goal. -/
def Locus.dependentArg : Locus → Arg
  | .v => .subject
  | .T => .object

/-! ### Spell-out -/

/-- A dependent-case vocabulary item spells out φ in a flag on a nominal, `e ↔ φ / __ [φ, D]`:
the Shawi ergative (34), the Sakha accusative (43) and the Kolyma Yukaghir *-gele* (52b), identical
but for the form. -/
def caseItem (e : String) : VocabularyItem Feature String :=
  ⟨{(0, .person .pi), (-1, .person .pi), (-1, .d)}, e⟩

/-- The Shawi ergative (34). -/
def ri : VocabularyItem Feature String := caseItem Kawapanan.Shawi.ergativeMarker

/-- The Shawi object agreement items (36), each with [v], in scansion order. -/
def objectItems : List (VocabularyItem Feature String) :=
  [{.person .speaker, .aug, .head .v} ⟷ "-kui", {.person .speaker, .head .v} ⟷ "-ku",
    {.person .participant, .aug, .head .v} ⟷ "-((n)ke)ma'",
    {.person .participant, .head .v} ⟷ "-(n)ken"]

/-- The dependent-case system of a language: its probe, the head of the probe, and the vocabulary
that spells out flags (table 6). -/
structure CaseSystem where
  grammar : Grammar
  locus : Locus
  items : List (VocabularyItem Feature String)

/-- Shawi has the strictly descending probe on v, §3.1, and the vocabulary (34), (36). -/
def shawi : CaseSystem := ⟨strictlyDescending, .v, ri :: objectItems⟩

/-- Shiwilu has the strong probe on v ((47)) and the ergative *=ler* ([valenzuela-2011]). -/
def shiwilu : CaseSystem := ⟨strong, .v, [caseItem "=ler"]⟩

/-- Sakha has the insatiable probe on T and the accusative (43). -/
def sakha : CaseSystem := ⟨noPCC, .T, [caseItem "-y"]⟩

/-- Kolyma Yukaghir has the weak probe on T and the accusatives (52) ([maslova-2003]), where *-ul*
also spells out the [PART] of a local subject. -/
def kolymaYukaghir : CaseSystem :=
  ⟨weak, .T, [⟨{(0, .person .pi), (0, .person .participant), (-1, .person .pi), (-1, .d)}, "-ul"⟩,
    caseItem "-gele"]⟩

/-- The items each goal's flag receives, the goal's own features one terminal to its left. -/
def CaseSystem.inserted (sys : CaseSystem) (s o : Nominal) (pos : ObjectPosition) :
    List (VocabularyItem Feature String) :=
  (flagged sys.grammar sys.locus (goals sys.locus pos s o)).flatMap fun x ↦
    insertions sys.items { focus := ∅, leftCtx := [insert .d (phi x.1)] } [x.2]

/-- The exponents the flags of a clause receive. -/
def CaseSystem.forms (sys : CaseSystem) (s o : Nominal) (pos : ObjectPosition) :
    List String :=
  (sys.inserted s o pos).map (·.exponent)

/-- The Shawi subject is ergative when its flag receives *-ri*. -/
def Ergative (s o : Nominal) (pos : ObjectPosition) : Prop := ri ∈ shawi.inserted s o pos

instance (s o : Nominal) (pos : ObjectPosition) : Decidable (Ergative s o pos) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Object agreement on the verb realizes v after (35) has removed the subject's features, and so
the object's alone. -/
def objectAgreement (o : Nominal) : List String :=
  scansion objectItems ∅ [{.head .v} ∪ phi o]

theorem applies_caseItem {e : String} {m : Finset Feature} {a : Nominal} :
    Applies (caseItem e)
      ({ focus := m, leftCtx := [insert .d (phi a)] } : Neighborhood (Finset Feature)) ↔
      Feature.person .pi ∈ m := by
  simp [VocabularyItem.applies_iff, caseItem, Neighborhood.mem_def, pi_mem_phi]

theorem insertions_objectItems (env : Neighborhood (Finset Feature)) (ms : List (Finset Feature)) :
    insertions objectItems env ms = insertions objectItems ∅ ms :=
  congrArg Prod.fst (scan_congr env ∅ _ (by simp [objectItems]; grind) ms)

private theorem phi_of_ne {p : Person} {n : Number} (h : n ≠ .augmented) :
    phi (p, n) = phi (p, .minimal) := by
  simp [phi, h]

private theorem insertions_ri_second (a o : Nominal) :
    insertions (ri :: objectItems) { focus := ∅, leftCtx := [insert .d (phi a)] }
        [{.head .v} ∪ phi o] =
      ri :: insertions objectItems ∅ [{.head .v} ∪ phi o] := by
  have hpi : Feature.person .pi ∈ ({.head .v} ∪ phi o : Finset Feature) :=
    Finset.mem_union_right _ (pi_mem_phi o)
  have hd : discharge ri { focus := ∅, leftCtx := [insert .d (phi a)] } [{.head .v} ∪ phi o] =
      some [({.head .v} ∪ phi o) \ {.person .pi}] := by
    rw [discharge_singleton, ite_eq_left (show Applies ri _ from applies_caseItem.2 hpi)]
    rfl
  rw [insertions, scan_cons_of_discharge_eq_some hd]
  refine congrArg (ri :: ·) ((insertions_objectItems _ _).trans ?_)
  obtain ⟨p, n⟩ := o
  by_cases hn : n = .augmented
  · subst hn; cases p <;> decide
  · rw [phi_of_ne hn]; cases p <;> decide

private theorem insertions_ri_first (a : Nominal) :
    insertions (ri :: objectItems) { focus := ∅, leftCtx := [insert .d (phi a)] }
      [{Feature.head .v}] = [] := by
  have hd : discharge ri { focus := ∅, leftCtx := [insert .d (phi a)] } [{.head .v}] = none := by
    rw [discharge_singleton, ite_eq_right fun h : Applies ri _ ↦ by
      simpa using applies_caseItem.1 h]
  rw [insertions, scan_cons_of_discharge_eq_none hd]
  exact (insertions_objectItems _ _).trans (by decide)

variable {s o : Nominal} {pos : ObjectPosition}

theorem shawi_inserted_low : shawi.inserted s o .low = [] := by
  simp only [CaseSystem.inserted, shawi, goals, flagged_singleton, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  exact insertions_ri_first s

theorem shawi_inserted_high :
    shawi.inserted s o .high =
      if Licit strictlyDescending ⟨s.1, o.1⟩ then
        ri :: insertions objectItems ∅ [{.head .v} ∪ phi o]
      else [] := by
  simp only [CaseSystem.inserted, shawi, goals, flagged_pair]
  split_ifs with h
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [insertions_ri_first, insertions_ri_second]
    rfl
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact insertions_ri_first o

theorem ergative_iff :
    Ergative s o pos ↔ pos = .high ∧ Licit strictlyDescending ⟨s.1, o.1⟩ := by
  cases pos with
  | low => simp [Ergative, shawi_inserted_low]
  | high =>
    simp only [Ergative, shawi_inserted_high, true_and]
    split_ifs with h <;> simp [h]

/-- The Shawi subject, as the probe's second goal, is spelled out as *-ri* followed by the object
agreement of the verb ((33), (34), (36)), which is the sense in which ergative case and object
agreement on the subject are both features of the object realized on the subject. -/
theorem forms_of_licit (h : Licit strictlyDescending ⟨s.1, o.1⟩) :
    shawi.forms s o .high = Kawapanan.Shawi.ergativeMarker :: objectAgreement o := by
  simp only [CaseSystem.forms, shawi_inserted_high, ite_eq_left h]
  rfl

-- (12)
example :
    shawi.forms (.firstExclusive, .augmented) (.second, .augmented) .high =
      ["-ri", "-((n)ke)ma'"] := by
  decide +kernel

-- (36) [clem-deal-2026]
theorem objectAgreement_eq_objectMarker :
    ∀ p ∈ [Person.firstExclusive, .second, .third], ∀ n ∈ [Number.minimal, .augmented],
      objectAgreement (p, n) = (Kawapanan.Shawi.objectMarker p n).toList := by
  decide +kernel

-- §2, fn. 7, §3.3
theorem objectItem_inserted {i : VocabularyItem Feature String} (hi : i ∈ objectItems)
    (h : i ∈ shawi.inserted s o pos) (hne : s.1.prominence ≠ o.1.prominence) :
    Ergative s o pos ∧ .speaker ∈ spec s.1 ∧ o.1 = .second := by
  have key : ∀ q p : Person, Licit strictlyDescending ⟨q, p⟩ → q.prominence ≠ p.prominence →
      p ≠ .third → .speaker ∈ spec q ∧ p = .second := by
    decide +kernel
  have hthird : ∀ n : Number, insertions objectItems ∅ [{.head .v} ∪ phi (.third, n)] = [] := by
    intro n
    by_cases hn : n = .augmented
    · subst hn; decide
    · rw [phi_of_ne hn]; decide
  have hri : i ≠ ri := by
    rintro rfl
    exact absurd hi (by decide +kernel)
  cases pos with
  | low => simp [shawi_inserted_low] at h
  | high =>
    rw [shawi_inserted_high] at h
    split_ifs at h with hl
    · refine ⟨ergative_iff.2 ⟨rfl, hl⟩, key _ _ hl hne fun ho ↦ ?_⟩
      obtain ⟨p, n⟩ := o
      dsimp only at ho
      subst ho
      rw [hthird] at h
      simp [hri] at h
    · simp at h

/-! ### Table 4 -/

/-- The three values of a Table 4 cell. -/
inductive Marking
  | obligatory
  | optional
  | impossible
  deriving DecidableEq, Repr

/-- Table 4's cell for a subject and an in-situ object records whether the subject is ergative in
every position open to the object, in some, or in none; number plays no part. -/
def marking (s o : Person) : Marking :=
  if ∀ pos ∈ positions o .inSitu, Ergative (s, .minimal) (o, .minimal) pos then .obligatory
  else if ∃ pos ∈ positions o .inSitu, Ergative (s, .minimal) (o, .minimal) pos then .optional
  else .impossible

-- Table 4
theorem table4 :
    marking .first .second = .obligatory ∧ marking .first .third = .optional ∧
    marking .second .first = .impossible ∧ marking .second .third = .optional ∧
    marking .third .first = .impossible ∧ marking .third .second = .impossible ∧
    marking .third .third = .optional := by
  decide +kernel

-- (23), (24)
theorem marking_optional_iff (s o : Person) : marking s o = .optional ↔ ¬ o.IsSAP := by
  revert s o; decide +kernel

-- (5), (10), (15)
theorem diagonal :
    ¬ Ergative (.first, .minimal) (.first, .minimal) .high ∧
      Ergative (.second, .minimal) (.second, .minimal) .high ∧
      Ergative (.third, .minimal) (.third, .minimal) .high := by
  decide +kernel

-- (49), §5.2: *-gele* with a third-person subject, *-ul* between local persons, nothing at 1→3
example :
    kolymaYukaghir.forms (.third, .singular) (.first, .singular) .high = ["-gele"] ∧
      kolymaYukaghir.forms (.first, .singular) (.second, .singular) .high = ["-ul"] ∧
      kolymaYukaghir.forms (.first, .singular) (.third, .singular) .high = [] ∧
      kolymaYukaghir.forms (.first, .singular) (.third, .singular) .low = [] := by
  decide +kernel

/-! ### The rows -/

/-- The persons a row names. -/
def personTable : List (String × Person) :=
  [("1", .first), ("1excl", .firstExclusive), ("2", .second), ("3", .third)]

/-- The numbers a row names, the Shawi glosses read as minimal and augmented by note 4. -/
def numberTable : List (String × Number) :=
  [("min", .minimal), ("aug", .augmented), ("sg", .singular), ("pl", .plural)]

/-- The surface syntax a row names. -/
def syntaxTable : List (String × ObjectSyntax) :=
  [("inSitu", .inSitu), ("fronted", .fronted), ("dropped", .dropped),
    ("belowAdverb", .belowAdverb), ("absent", .absent)]

/-- A nominal of a row. -/
def nominal? (e : Datum) (person number : String) : Option Nominal := do
  pure (← e.parse? person personTable, ← e.parse? number numberTable)

/-- What a row presents: the language's system, the arguments, the object's syntax, the case marker
it prints and the argument bearing it, and whether it prints object agreement on the subject. -/
structure Stimulus where
  sys : CaseSystem
  subj : Nominal
  obj : Nominal
  objectSyntax : ObjectSyntax
  case? : Option String
  caseOn : Option Arg
  oagrOnS : Bool

/-- A row's stimulus. -/
def stimulus? (e : Datum) : Option Stimulus := do
  let sys ← e.byLanguage
    [(.shawi, shawi), (.jebero, shiwilu), (.sakha, sakha), (.southernYukaghir, kolymaYukaghir)]
  let s ← nominal? e "subject" "subjectNumber"
  let x ← e.parse? "objectSyntax" syntaxTable
  pure ⟨sys, s, (nominal? e "object" "objectNumber").getD (.third, .minimal), x, e.feature? "case",
    e.parse? "caseOn" [("subject", .subject), ("object", .object)],
    e.feature? "oagrOnS" = some "yes"⟩

/-- A stimulus is grammatical when a position open to its object spells out the printed case on the
probe's second goal, the first item of the spell-out, and object agreement on the subject only where
the vocabulary has some to spell out (optional, fn. 7). -/
def predicted (c : Stimulus) : Judgment.Band :=
  .ofProp (∃ pos ∈ positions c.obj.1 c.objectSyntax,
    let f := c.sys.forms c.subj c.obj pos
    f.head? = c.case? ∧ (∀ a ∈ c.caseOn, a = c.sys.locus.dependentArg) ∧
      (c.oagrOnS = true → 1 < f.length))

/-- Every row of Shawi, Shiwilu, Sakha and Kolyma Yukaghir is judged as the run of the language's
probe and its vocabulary predict: a sentence is accepted exactly when some position open to its
object spells out what it prints. -/
theorem rows_predicted : Datum.Checks stimulus? predicted Examples.all 43 := by
  decide +kernel

/-! ### Configurational rules (§1, §4.1) -/

/-- The NPs of the subject's spell-out domain, highest first: a low object is in another. -/
def domain : ObjectPosition → List Arg
  | .high => [.subject, .object]
  | .low => [.subject]

-- (1), (7a–c) [baker-2015]
theorem rule1_overgenerates :
    ((DependentCase.assignCases .ergative (fun _ ↦ none) (domain .high)).valueOf .subject).map
      (·.1) = some .erg ∧
    ¬ Ergative (.second, .minimal) (.first, .minimal) .high ∧
    ¬ Ergative (.third, .minimal) (.first, .minimal) .high ∧
    ¬ Ergative (.third, .minimal) (.second, .minimal) .high := by
  decide +kernel

/-- Rule (37), [barany-sheehan-2024]'s writing a hierarchy into (1): over the ranking `rank`, an NP
takes the ergative when it c-commands a caseless NP no higher on `rank`. -/
def rule37 (rank : Person → ℕ) (s o : Person) (pos : ObjectPosition) :
    Case.Valuation Arg (Case × Case.Mechanism) :=
  let person : Arg → Person
    | .subject => s
    | .object => o
  (DependentCase.Rules.ofAlignment .ergative).dependentPassBy
    (fun p q ↦ p.1 < q.1 ∧ rank (person q.2) ≤ rank (person p.2)) (fun _ ↦ True)
    (Case.lexicalValuation (fun _ ↦ none) (domain pos))

-- (37), §4.1
theorem rule37_valueOf_iff (rank : Person → ℕ) (s o : Person) :
    ((rule37 rank s o .high).valueOf .subject).map (·.1) = some .erg ↔ rank o ≤ rank s := by
  by_cases h : rank o ≤ rank s <;>
    simp [rule37, domain, h, DependentCase.Rules.dependentPassBy, DependentCase.Rules.ofAlignment,
      Case.lexicalValuation, Case.slotValuation, Case.Valuation.initial,
      Case.Valuation.caselessEntries, Case.Valuation.fill, Case.Valuation.fillFrom,
      Case.Valuation.valueOf, Case.Valuation.offer]

/-- Agree cannot do what (37) can: no probe yields the rule over a ranking with third person above
second, since a probe that gets past a second person gets past a third (§4.1). -/
theorem not_forall_iff_rule37 (g : Grammar) {rank : Person → ℕ} (h : rank .second < rank .third)
    (n : Number) : ¬ ∀ s o : Person, s.prominence ≠ o.prominence →
      (DependentCase g .v (goals .v .high (s, n) (o, n)) ↔
        ((rule37 rank s o .high).valueOf .subject).map (·.1) = some .erg) := by
  intro hg
  have h₁ : Licit g ⟨.third, .second⟩ := (dependentCase_pair_iff g .v (.second, n) (.third, n)).1
    ((hg .third .second (by decide)).2 ((rule37_valueOf_iff ..).2 h.le))
  have hsub : spec Person.third ⊆ spec Person.second := by decide
  have h₂ : Licit g ⟨.second, .third⟩ :=
    Licit.mono (s := ⟨.third, .second⟩) (t := ⟨.second, .third⟩) hsub hsub h₁
  exact absurd ((rule37_valueOf_iff ..).1 ((hg .second .third (by decide)).1
    ((dependentCase_pair_iff g .v (.third, n) (.second, n)).2 h₂))) (not_le.2 h)

/-! ### The typology of global case splits (§5) -/

/-- The alignment of a probe's dependent case, ergative on v and accusative on T. -/
def Locus.alignment : Locus → Alignment.AlignmentType
  | .v => .ergative
  | .T => .accusative

-- §5.1 [deal-2010] [clem-2019] [baker-vinokurova-2010]
theorem noPCC_iff_assignCases (l : Locus) (pos : ObjectPosition) (s o : Nominal) :
    DependentCase noPCC l (goals l pos s o) ↔
      ((DependentCase.assignCases l.alignment (fun _ ↦ none) (domain pos)).valueOf
        l.dependentArg).map (·.2) = some .dependent := by
  have h : ∀ p q : Person, Licit noPCC ⟨p, q⟩ := by decide +kernel
  cases l <;> cases pos <;> simp [goals, dependentCase_pair_iff, not_dependentCase_singleton, h] <;>
    decide

-- table 7, strong
theorem dependentCase_strong_iff (l : Locus) (a b : Nominal) :
    DependentCase strong l [a, b] ↔ .participant ∉ spec a.1 := by
  simp [dependentCase_pair_iff, licit_iff, strong]

-- table 7, weak
theorem dependentCase_weak_iff (l : Locus) (a b : Nominal) :
    DependentCase weak l [a, b] ↔ (.participant ∈ spec a.1 → .participant ∈ spec b.1) := by
  by_cases h : .participant ∈ spec a.1 <;> simp [dependentCase_pair_iff, licit_iff, weak, h]

-- (15), (17), (19), (22), table 7
theorem dependentCase_sd_iff (l : Locus) (a b : Nominal) :
    DependentCase strictlyDescending l [a, b] ↔
      .speaker ∉ spec a.1 ∧ (.participant ∈ spec a.1 → .participant ∈ spec b.1) := by
  by_cases h : .participant ∈ spec a.1 <;>
    simp [dependentCase_pair_iff, licit_iff, strictlyDescending, h]

-- table 7, Shawi; Kashmiri, fn. 42
theorem dependentCase_sd_off_diagonal_iff (l : Locus) (a b : Nominal)
    (h : a.1.prominence ≠ b.1.prominence) :
    DependentCase strictlyDescending l [a, b] ↔ a.1.prominence < b.1.prominence :=
  (dependentCase_pair_iff ..).trans (sd_off_diagonal_iff_outranks ⟨b.1, a.1⟩ h.symm)

/-- The Directionality Correlation (54). Once a grammar assigns dependent case at all, a
third-person first goal never bleeds it: on v a third-person object lets the probe reach any
subject, and on T a third-person subject lets it reach any object. So only the object's person can
bleed ergative, a forward hierarchy, and only the subject's person accusative, a reverse one. -/
theorem directionality {g : Grammar} {l : Locus} {a b : Nominal}
    (h : DependentCase g l [a, b]) (n : Number) (c : Nominal) :
    DependentCase g .v (goals .v .high c (.third, n)) ∧
      DependentCase g .T (goals .T .high (.third, n) c) :=
  have hl := ((dependentCase_pair_iff ..).1 h).third c.1
  ⟨(dependentCase_pair_iff ..).2 hl, (dependentCase_pair_iff ..).2 hl⟩

-- fn. 29, fn. 44
theorem not_forall_ergative_iff_object_outranks (g : Grammar) (n : Number) :
    ¬ ∀ s o : Person, s.prominence ≠ o.prominence →
      (DependentCase g .v (goals .v .high (s, n) (o, n)) ↔ s.prominence < o.prominence) := by
  intro hg
  have h₁ := (hg .second .first (by decide)).2 (by decide)
  have h₂ := (directionality h₁ n (.first, n)).1
  exact absurd ((hg .first .third (by decide)).1 h₂) (by decide)

/-! ### Cyclic Agree (§3.1) -/

-- §3.1
theorem kashmiri_isDirect_iff (s : Scenario Person) (hs : s ∈ PCC.distinctPairs) :
    BejarRezac2009.kashmiri.IsDirect s ↔ Licit strictlyDescending s := by
  revert s; decide +kernel

-- §3.1
theorem not_isDirect_of_isChain (sys : Minimalist.CyclicAgree.AgreementSystem)
    (h : sys.geometry.IsChain) :
    ¬ (sys.IsDirect ⟨.first, .second⟩ ∧ sys.IsDirect ⟨.second, .first⟩) :=
  fun ⟨h₁, h₂⟩ ↦ lt_asymm
    ((Minimalist.CyclicAgree.AgreementSystem.isDirect_iff_rank_lt sys ⟨.first, .second⟩ h).1 h₁)
    ((Minimalist.CyclicAgree.AgreementSystem.isDirect_iff_rank_lt sys ⟨.second, .first⟩ h).1 h₂)

-- §3.1 [harley-ritter-2002]
theorem branching_isDirect_iff (s : Scenario Person) (hs : s ∈ PCC.distinctPairs) :
    (⟨.branching, Minimalist.CyclicAgree.fullProbe .branching⟩ :
      Minimalist.CyclicAgree.AgreementSystem).IsDirect s ↔ Licit weak s := by
  revert s; decide +kernel

end ClemDeal2026
