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
public import Studies.Deal2025a

/-!
# Clem and Deal (2026): Dependent case by Agree

A probe flags each goal with all the features its head holds, so [a second goal receives the first
goal's φ-features](##flagged_pair), and a dependent case is the vocabulary item spelling out that φ
on a nominal. The Shawi subject surfaces with [*-ri* and the verb's object
agreement](##forms_of_licit) when the strictly descending probe on v reaches it after a high object,
and the same machinery [predicts the rows of four languages](##rows_predicted). Since a hierarchy is
a probe's run over a feature geometry, [no probe puts third person above
second](##not_forall_iff_rule37), and [no probe on v yields a reverse hierarchy, nor one on T a
forward hierarchy](##directionality).

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
  whole and none of the routes to its absence in §3.3 deletes [AUG] alone, so [bare *-nke* on the
  subject of a 2PL object is not derived](##not_predicted_bare_nke).

## References

* [clem-deal-2026]
* [deal-2024]
* [deal-2025a]
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

/-- The nominals of a clause by argument. -/
def nominals (s o : Nominal) : Arg → Nominal
  | .subject => s
  | .object => o

section Flags

variable (g : Grammar) (l : Locus) (nom : Arg → Nominal)

/-- The arguments a probe of grammar `g` Agrees with, in search order. -/
def agreed (goals : List Arg) : List Arg :=
  (run g (fun a ↦ (nom a).1) goals).interacted

/-- Agree is bidirectional ((31)): a head holding `fs` flags its next goal with all of `fs`, beyond
the mark of agreement that is [deal-2025a]'s goal flag, and takes on the goal's φ-features. -/
def flagsFrom : Finset Feature → List Arg → List (Arg × Finset Feature)
  | _, [] => []
  | fs, a :: as => (a, fs) :: flagsFrom (fs ∪ phi (nom a)) as

/-- The goals of a probe on `l` with their flags, the head starting with its category feature. -/
def flagged (goals : List Arg) : List (Arg × Finset Feature) :=
  flagsFrom nom {.head l} (agreed g nom goals)

theorem agreed_pair (a b : Arg) :
    agreed g nom [a, b] = a :: if Licit g ⟨(nom b).1, (nom a).1⟩ then [b] else [] :=
  interacted_run_pair g _ a b

/-- Feature transfer under Agree is transitive ((31)): a probe flags its first goal with its
category feature alone and, if it goes on to a second, flags that with the first goal's φ-features
as well. -/
theorem flagged_pair (a b : Arg) :
    flagged g l nom [a, b] =
      (a, {.head l}) ::
        if Licit g ⟨(nom b).1, (nom a).1⟩ then [(b, {.head l} ∪ phi (nom a))] else [] := by
  rw [flagged, agreed_pair]
  split_ifs <;> rfl

theorem flagged_singleton (a : Arg) : flagged g l nom [a] = [(a, {.head l})] := by
  have h : agreed g nom [a] = [a] := by
    obtain ⟨_ | x, dyn⟩ := g
    · simp [agreed, run, Minimalist.Probe.Dynamic.agree_cons]
    · by_cases hx : x ∈ spec (nom a).1 <;>
        simp [agreed, run, Minimalist.Probe.Dynamic.agree_cons, hx]
  rw [flagged, h]
  rfl

/-- A probe assigns dependent case when one of its goals bears a flag with φ in it, the structure
that a dependent-case vocabulary item realizes ((31), (34), (43)). -/
def DependentCase (goals : List Arg) : Prop :=
  ∃ x ∈ flagged g l nom goals, Feature.person .pi ∈ x.2

instance (goals : List Arg) : Decidable (DependentCase g l nom goals) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

theorem pi_mem_phi (a : Nominal) : Feature.person .pi ∈ phi a := by
  simp [phi]

-- (53)
theorem dependentCase_pair_iff (a b : Arg) :
    DependentCase g l nom [a, b] ↔ Licit g ⟨(nom b).1, (nom a).1⟩ := by
  simp only [DependentCase, flagged_pair]
  split_ifs with h <;> simp [h, pi_mem_phi]

-- (15), (17), (19), (22), table 7
theorem dependentCase_sd_iff (a b : Arg) :
    DependentCase strictlyDescending l nom [a, b] ↔
      .speaker ∉ spec (nom a).1 ∧
        (.participant ∈ spec (nom a).1 → .participant ∈ spec (nom b).1) := by
  by_cases h : .participant ∈ spec (nom a).1 <;>
    simp [dependentCase_pair_iff, licit_iff, strictlyDescending, h]

end Flags

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
def goals : Locus → ObjectPosition → List Arg
  | .v, .high => [.object, .subject]
  | .T, .high => [.subject, .object]
  | _, .low => [.subject]

theorem dependentCase_v_iff (g : Grammar) (s o : Nominal) :
    DependentCase g .v (nominals s o) (goals .v .high) ↔ Licit g ⟨s.1, o.1⟩ :=
  dependentCase_pair_iff g .v (nominals s o) .object .subject

theorem dependentCase_T_iff (g : Grammar) (s o : Nominal) :
    DependentCase g .T (nominals s o) (goals .T .high) ↔ Licit g ⟨o.1, s.1⟩ :=
  dependentCase_pair_iff g .T (nominals s o) .subject .object

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
that spells out flags, in scansion order (table 6). -/
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

/-- The items the flag of an argument receives, its own features one terminal to the left, and
nothing if the probe never reaches it. -/
def CaseSystem.inserted (sys : CaseSystem) (s o : Nominal) (pos : ObjectPosition) (x : Arg) :
    List (VocabularyItem Feature String) :=
  ((flagged sys.grammar sys.locus (nominals s o) (goals sys.locus pos)).lookup x).elim [] fun fs ↦
    insertions sys.items { focus := ∅, leftCtx := [insert .d (phi (nominals s o x))] } [fs]

/-- The exponents the flag of an argument receives. -/
def CaseSystem.forms (sys : CaseSystem) (s o : Nominal) (pos : ObjectPosition) (x : Arg) :
    List String :=
  (sys.inserted s o pos x).map (·.exponent)

/-- The Shawi subject is ergative when its flag receives *-ri*. -/
def Ergative (s o : Nominal) (pos : ObjectPosition) : Prop := ri ∈ shawi.inserted s o pos .subject

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

private theorem objectItems_site :
    ∀ i ∈ objectItems, ∀ y ∈ i.site, y.1 = 0 ∧ y.2 ≠ Feature.person .pi := by
  simp [objectItems]
  grind

theorem insertions_objectItems (env : Neighborhood (Finset Feature)) (ms : List (Finset Feature)) :
    insertions objectItems env ms = insertions objectItems ∅ ms :=
  congrArg Prod.fst (scan_congr env ∅ _ (fun i hi y hy ↦ (objectItems_site i hi y hy).1) ms)

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
  rw [insertions_cons_of_discharge_eq_some hd, insertions_objectItems,
    insertions_sdiff_singleton ∅ _ _ objectItems_site]

private theorem insertions_ri_first (a : Nominal) :
    insertions (ri :: objectItems) { focus := ∅, leftCtx := [insert .d (phi a)] }
      [{Feature.head .v}] = [] := by
  have hd : discharge ri { focus := ∅, leftCtx := [insert .d (phi a)] } [{.head .v}] = none := by
    rw [discharge_singleton, ite_eq_right fun h : Applies ri _ ↦ by
      simpa using applies_caseItem.1 h]
  rw [insertions_cons_of_discharge_eq_none hd, insertions_objectItems]
  decide

variable {s o : Nominal} {pos : ObjectPosition}

theorem shawi_inserted_object : shawi.inserted s o pos .object = [] := by
  cases pos <;> simp only [CaseSystem.inserted, shawi, goals, flagged_pair, flagged_singleton,
    nominals]
  · split_ifs <;> exact insertions_ri_first o
  · rfl

theorem shawi_inserted_low : shawi.inserted s o .low .subject = [] := by
  simp only [CaseSystem.inserted, shawi, goals, flagged_singleton]
  exact insertions_ri_first s

theorem shawi_inserted_high :
    shawi.inserted s o .high .subject =
      if Licit strictlyDescending ⟨s.1, o.1⟩ then
        ri :: insertions objectItems ∅ [{.head .v} ∪ phi o]
      else [] := by
  simp only [CaseSystem.inserted, shawi, goals, flagged_pair, nominals]
  by_cases h : Licit strictlyDescending ⟨s.1, o.1⟩
  · simp only [h, ↓reduceIte]
    exact insertions_ri_second s o
  · simp only [h, ↓reduceIte]
    rfl

theorem ergative_iff : Ergative s o pos ↔ pos = .high ∧ Licit strictlyDescending ⟨s.1, o.1⟩ := by
  cases pos with
  | low => simp [Ergative, shawi_inserted_low]
  | high =>
    simp only [Ergative, shawi_inserted_high, true_and]
    split_ifs with h <;> simp [h]

/-- The Shawi subject, as the probe's second goal, is spelled out as *-ri* followed by the object
agreement of the verb ((33), (34), (36)), which is the sense in which ergative case and object
agreement on the subject are both features of the object realized on the subject. -/
theorem forms_of_licit (h : Licit strictlyDescending ⟨s.1, o.1⟩) :
    shawi.forms s o .high .subject = Kawapanan.Shawi.ergativeMarker :: objectAgreement o := by
  simp only [CaseSystem.forms, shawi_inserted_high, ite_eq_left h]
  rfl

-- (12)
example :
    shawi.forms (.firstExclusive, .augmented) (.second, .augmented) .high .subject =
      ["-ri", "-((n)ke)ma'"] := by
  decide +kernel

-- (36) [clem-deal-2026]
theorem objectAgreement_eq_objectMarker :
    ∀ p ∈ [Person.firstExclusive, .second, .third], ∀ n ∈ [Number.minimal, .augmented],
      objectAgreement (p, n) = (Kawapanan.Shawi.objectMarker p n).toList := by
  decide +kernel

-- §2, fn. 7, §3.3
theorem objectItem_inserted {i : VocabularyItem Feature String} (hi : i ∈ objectItems)
    (h : i ∈ shawi.inserted s o pos .subject) (hne : s.1.prominence ≠ o.1.prominence) :
    Ergative s o pos ∧ .speaker ∈ spec s.1 ∧ o.1 = .second := by
  have key : ∀ q p : Person, Licit strictlyDescending ⟨q, p⟩ → q.prominence ≠ p.prominence →
      p ≠ .third → .speaker ∈ spec q ∧ p = .second := by
    decide +kernel
  have hthird : ∀ n : Number, insertions objectItems ∅ [{.head .v} ∪ phi (.third, n)] = [] := by
    intro n
    by_cases hn : n = .augmented
    · subst hn; decide
    · simp only [phi, hn, ite_false]; decide
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
  simp only [marking, ergative_iff]
  decide

-- (23), (24)
theorem marking_optional_iff (s o : Person) : marking s o = .optional ↔ ¬ o.IsSAP := by
  simp only [marking, ergative_iff]
  revert s o
  decide

-- (5), (10), (15)
theorem diagonal :
    ¬ Ergative (.first, .minimal) (.first, .minimal) .high ∧
      Ergative (.second, .minimal) (.second, .minimal) .high ∧
      Ergative (.third, .minimal) (.third, .minimal) .high := by
  simp only [ergative_iff]
  decide

-- (49), §5.2: *-gele* with a third-person subject, *-ul* between local persons, nothing at 1→3
example :
    kolymaYukaghir.forms (.third, .singular) (.first, .singular) .high .object = ["-gele"] ∧
      kolymaYukaghir.forms (.first, .singular) (.second, .singular) .high .object = ["-ul"] ∧
      kolymaYukaghir.forms (.first, .singular) (.third, .singular) .high .object = [] ∧
      kolymaYukaghir.forms (.first, .singular) (.third, .singular) .low .object = [] := by
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
it prints and the argument bearing it, and the object agreement it prints on the subject. -/
structure Stimulus where
  sys : CaseSystem
  subj : Nominal
  obj : Nominal
  objectSyntax : ObjectSyntax
  case? : Option String
  caseOn : Option Arg
  oagrOnS : Option String

/-- A row's stimulus. -/
def stimulus? (e : Datum) : Option Stimulus := do
  let sys ← e.byLanguage
    [(.shawi, shawi), (.jebero, shiwilu), (.sakha, sakha), (.southernYukaghir, kolymaYukaghir)]
  let s ← nominal? e "subject" "subjectNumber"
  let x ← e.parse? "objectSyntax" syntaxTable
  pure ⟨sys, s, (nominal? e "object" "objectNumber").getD (.third, .minimal), x, e.feature? "case",
    e.parse? "caseOn" [("subject", .subject), ("object", .object)], e.feature? "oagrOnS"⟩

/-- A stimulus is grammatical when, in a position open to its object, each argument's flag begins
with exactly the case the row prints on it, and any object agreement printed on the subject is
what the subject's flag spells out after that (it is optional, fn. 7). -/
def predicted (c : Stimulus) : Judgment.Band :=
  .ofProp (∃ pos ∈ positions c.obj.1 c.objectSyntax,
    (∀ x ∈ [Arg.subject, .object], (c.sys.forms c.subj c.obj pos x).head? =
      if c.caseOn = some x then c.case? else none) ∧
    ∀ f ∈ c.oagrOnS, f ∈ (c.sys.forms c.subj c.obj pos .subject).tail)

/-- Every row of Shawi, Shiwilu, Sakha and Kolyma Yukaghir but the bare *-nke* of (6b) is judged as
the run of the language's probe and its vocabulary predict: a sentence is accepted exactly when some
position open to its object spells out what it prints, on the argument it prints it on. -/
theorem rows_predicted :
    Datum.Checks stimulus? predicted (Examples.all.erase Examples.ex_6b_nke) 42 := by
  decide +kernel

-- (6b), (36d)
theorem not_predicted_bare_nke :
    Examples.ex_6b_nke.judgment.band = .accepted ∧
      (stimulus? Examples.ex_6b_nke).map predicted = some .rejected := by
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
  simp only [ergative_iff]
  decide

/-- Rule (37), [barany-sheehan-2024]'s writing a hierarchy into (1): over the ranking `rank`, an NP
takes the ergative when it c-commands a caseless NP no higher on `rank`. -/
def rule37 (rank : Person → ℕ) (s o : Nominal) (pos : ObjectPosition) :
    Case.Valuation Arg (Case × Case.Mechanism) :=
  (DependentCase.Rules.ofAlignment .ergative).dependentPassBy
    (fun p q ↦ p.1 < q.1 ∧ rank (nominals s o q.2).1 ≤ rank (nominals s o p.2).1) (fun _ ↦ True)
    (Case.lexicalValuation (fun _ ↦ none) (domain pos))

-- (37), §4.1
theorem rule37_valueOf_iff (rank : Person → ℕ) (s o : Nominal) :
    ((rule37 rank s o .high).valueOf .subject).map (·.1) = some .erg ↔ rank o.1 ≤ rank s.1 := by
  by_cases h : rank o.1 ≤ rank s.1 <;>
    simp [rule37, domain, nominals, h, DependentCase.Rules.dependentPassBy,
      DependentCase.Rules.ofAlignment, Case.lexicalValuation, Case.slotValuation,
      Case.Valuation.initial, Case.Valuation.caselessEntries, Case.Valuation.fill,
      Case.Valuation.fillFrom, Case.Valuation.valueOf, Case.Valuation.offer]

/-- Agree cannot do what (37) can: no probe yields the rule over a ranking with third person above
second, since a probe that gets past a second person gets past a third (§4.1). -/
theorem not_forall_iff_rule37 (g : Grammar) {rank : Person → ℕ} (h : rank .second < rank .third)
    (n : Number) : ¬ ∀ s o : Person, s.prominence ≠ o.prominence →
      (DependentCase g .v (nominals (s, n) (o, n)) (goals .v .high) ↔
        ((rule37 rank (s, n) (o, n) .high).valueOf .subject).map (·.1) = some .erg) := by
  intro hg
  have h₁ : Licit g ⟨.third, .second⟩ := (dependentCase_v_iff g (.third, n) (.second, n)).1
    ((hg .third .second (by decide)).2 ((rule37_valueOf_iff rank (.third, n) (.second, n)).2 h.le))
  have hsub : spec Person.third ⊆ spec Person.second := by decide
  have h₂ : Licit g ⟨.second, .third⟩ :=
    Licit.mono (s := ⟨.third, .second⟩) (t := ⟨.second, .third⟩) hsub hsub h₁
  exact absurd ((rule37_valueOf_iff rank (.second, n) (.third, n)).1
    ((hg .second .third (by decide)).1 ((dependentCase_v_iff g (.second, n) (.third, n)).2 h₂)))
    (not_le.2 h)

/-! ### The typology of global case splits (§5) -/

/-- The alignment of a probe's dependent case, ergative on v and accusative on T. -/
def Locus.alignment : Locus → Alignment.AlignmentType
  | .v => .ergative
  | .T => .accusative

-- §5.1 [deal-2010] [clem-2019] [baker-vinokurova-2010]
theorem noPCC_iff_assignCases (l : Locus) (pos : ObjectPosition) (s o : Nominal) (x : Arg) :
    (∃ fs, (x, fs) ∈ flagged noPCC l (nominals s o) (goals l pos) ∧ Feature.person .pi ∈ fs) ↔
      ((DependentCase.assignCases l.alignment (fun _ ↦ none) (domain pos)).valueOf x).map (·.2) =
        some .dependent := by
  have h : ∀ p q : Person, Licit noPCC ⟨p, q⟩ := by decide +kernel
  cases l <;> cases pos <;> cases x <;>
    simp [goals, flagged_pair, flagged_singleton, h, pi_mem_phi] <;> decide

-- table 7
theorem table7 (p : Grammar × PCCType)
    (hp : p ∈ [(strong, .strong), (weak, .weak), (strictlyDescending, .strictlyDescending)])
    (s o : Nominal) (h : s.1.prominence ≠ o.1.prominence) :
    (DependentCase p.1 .v (nominals s o) (goals .v .high) ↔ p.2.Licit ⟨s.1, o.1⟩) ∧
      (DependentCase p.1 .T (nominals s o) (goals .T .high) ↔ p.2.Licit ⟨o.1, s.1⟩) := by
  have key : ∀ p ∈ [((strong, .strong) : Grammar × PCCType), (weak, .weak),
      (strictlyDescending, .strictlyDescending)], ∀ a b : Person, a.prominence ≠ b.prominence →
        (Licit p.1 ⟨a, b⟩ ↔ p.2.Licit ⟨a, b⟩) := by
    decide +kernel
  exact ⟨(dependentCase_v_iff p.1 s o).trans (key p hp _ _ h),
    (dependentCase_T_iff p.1 s o).trans (key p hp _ _ h.symm)⟩

private theorem not_forall_iff_swap {L : Scenario Person → Prop}
    (hL : ∀ s, L s → ∀ p, L ⟨p, .third⟩) {t : PCCType} (ht : ¬ t.Licit ⟨.third, .first⟩) :
    ¬ ∀ p q : Person, p.prominence ≠ q.prominence → (L ⟨p, q⟩ ↔ t.Licit ⟨q, p⟩) := fun h ↦
  ht ((h .first .third (by decide)).1 (hL _ ((h .third .first (by decide)).2
    (participant_third_licit t .first (by decide))) .first))

/-- The Directionality Correlation (54). Whatever a hierarchy effect `t` that bans a first-person
direct object under a third-person indirect object, no probe on v yields its reverse and no probe on
T its forward form, since a first goal's person is what bleeds a probe: only the object's can bleed
ergative and only the subject's accusative. This excludes ergative where the object outranks the
subject, as reported for Fore and Dalabon (fns. 29, 44). -/
theorem directionality (g : Grammar) {t : PCCType} (ht : ¬ t.Licit ⟨.third, .first⟩) (n : Number) :
    (¬ ∀ s o : Person, s.prominence ≠ o.prominence →
      (DependentCase g .v (nominals (s, n) (o, n)) (goals .v .high) ↔ t.Licit ⟨o, s⟩)) ∧
    ¬ ∀ s o : Person, s.prominence ≠ o.prominence →
      (DependentCase g .T (nominals (s, n) (o, n)) (goals .T .high) ↔ t.Licit ⟨s, o⟩) :=
  ⟨fun h ↦ not_forall_iff_swap (L := Deal2024.Licit g) (fun _ hs p ↦ Deal2024.Licit.third hs p) ht
      fun p q hpq ↦ (dependentCase_v_iff g (p, n) (q, n)).symm.trans (h p q hpq),
    fun h ↦ not_forall_iff_swap (L := Deal2024.Licit g) (fun _ hs p ↦ Deal2024.Licit.third hs p) ht
      fun p q hpq ↦ (dependentCase_T_iff g (q, n) (p, n)).symm.trans (h q p hpq.symm)⟩

-- (54), under (30) of [deal-2025a]
theorem not_forall_agree_iff_swap (g : Grammar) {t : PCCType} (ht : ¬ t.Licit ⟨.third, .first⟩) :
    ¬ ∀ p q : Person, p.prominence ≠ q.prominence → (Deal2025a.Licit g ⟨p, q⟩ ↔ t.Licit ⟨q, p⟩) :=
  not_forall_iff_swap (L := Deal2025a.Licit g) (fun _ hs p ↦ Deal2025a.Licit.third hs p) ht

/-! ### Cyclic Agree (§3.1) -/

/-- The cyclic probes of [bejar-rezac-2009] compared with Deal's, on the six cells only: every
reflexive cell is inverse (`AgreementSystem.isInverse_self`), where a third-person first goal lets
Deal's probes go on, as Table 4's row g and the Kolyma Yukaghir 3→3 require. -/
example : (BejarRezac2009.kashmiri).IsInverse ⟨.third, .third⟩ ∧
    Licit strictlyDescending ⟨.third, .third⟩ ∧ Licit weak ⟨.third, .third⟩ :=
  ⟨Minimalist.CyclicAgree.AgreementSystem.isInverse_self _ _, by decide, by decide⟩

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
