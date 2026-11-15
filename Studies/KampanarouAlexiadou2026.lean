module

public import Linglib.Morphology.DistributedMorphology.Allosemy
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Nominality
public import Linglib.Data.Examples.KampanarouAlexiadou2026
public import Linglib.Data.Examples.Readers

/-!
# Kampanarou and Alexiadou (2026): Genitive Alternation in Possessives and Beyond

This file formalizes [kampanarou-alexiadou-2026], on the Standard Modern Greek alternation
between an inflectional genitive and a prepositional *apo*-phrase. The paper argues that the
*apo*-PP is not a second spell-out of the genitive but a complement with a partitive meaning,
through which a possessive reading is coerced. With possessors, the *apo*-PP is accepted for
parts and sources and resisted by pronouns and proper names; plural marking, modification and a
paradigm gap of the genitive [only raise its acceptability](##facilitation_mono), and a gap is
[not sufficient](##gap_not_sufficient) for it. With derived nominals, a theme realized as an
*apo*-PP excludes the complex-event reading of [grimshaw-1990], so a nominal with two arguments
[has a genitive theme and a by-phrase](##Nominal.WellFormed.genitive_and_apo): the single
genitive restriction of [horrocks-stavrou-1987], extended to PPs, which the Grevena Greek of
[michelioudakis-chatzikyriakidis-spathas-2024] does not obey; the Grevena *apo*-PP also
[fronts and extracts](##displacement_rows_agree) as the standard genitive does. A possessor
[takes surface scope exactly when it is a complement](##scope_rows_agree), as the inalienable
genitive of [alexiadou-2003] and every *apo*-PP are.

## Implementation notes

* The paper marks variation among speakers with `?`, so a row is `Acceptable` unless its mark is
  in the rejected band.
* The readings of a derived nominal are the library's `NominalizationReading`; the paper
  contrasts the complex-event reading with the rest, and `Nominal.Licenses` treats the rest
  alike. The paper pluralizes only nominals with an *apo* theme and no modifier, so its rows do
  not separate `Nominal.Licenses.plural` from the other conditions.
* The three analyses of the *apo*-PP (selection by the possessee, a predicative small clause, a
  light *p*) agree that it is a complement, which is all `Marking.site` records.
* The recursive possessives are recorded as the paper reports them, with only the innermost
  possessor alternating; the paper derives the pattern from none of its analyses.

## TODO

* Of the paper's table of properties of the three expressions, the range of relations each
  expresses and its unmarked position are not encoded.

## References

* [kampanarou-alexiadou-2026]
* [alexiadou-2003], [grimshaw-1990], [horrocks-stavrou-1987]
* [michelioudakis-chatzikyriakidis-spathas-2024]
-/

@[expose] public section

namespace KampanarouAlexiadou2026

open DistributedMorphology.Allosemy

/-- A mark the paper accepts: none, or `?`, its mark for variation among speakers. -/
def Acceptable (j : Judgment) : Prop := j.band ≠ .rejected

instance : DecidablePred Acceptable := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The realization of a possessor or of an argument. -/
inductive Marking
  | genitive | apo
  deriving DecidableEq, Repr

def markingOf : List (String × Marking) := [("genitive", .genitive), ("apo", .apo)]

def nominalityOf : List (String × Nominality) :=
  [("common", .commonNoun), ("pronoun", .pronoun), ("properName", .properName)]

def animacyOf : List (String × Animacy) :=
  [("inanimate", .inanimate), ("animate", .animate), ("human", .human)]

/-- The rows of the group `g` of the paper's examples, as `f` reads them. -/
def groupRows {α : Type} (g : String) (f : Datum → Option α) : List α :=
  Examples.all.filterMap fun e ↦ if e.feature? "group" = some g then f e else none

/-! ### Possessive apo-PPs -/

/-- The paper's classification of the relation between possessee and possessor: part-whole (5a),
source (5b), kinship (6a), ownership (6b), and the mere association of a mat with its door (11). -/
inductive Relation
  | partWhole | source | kinship | ownership | association
  deriving DecidableEq, Repr

/-- The relations the paper reads as partitive: the possessee is a part of, or comes from, the
possessor. -/
def Relation.IsPartitive (r : Relation) : Prop := r = .partWhole ∨ r = .source

instance : DecidablePred Relation.IsPartitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Inalienable relations in the sense of [alexiadou-2003]: parts, body parts, and kin. -/
def Relation.IsInalienable (r : Relation) : Prop := r = .partWhole ∨ r = .kinship

instance : DecidablePred Relation.IsInalienable := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The conditions the paper reports to raise the acceptability of the apo-PP: plural marking and
modification of the possessor, and a paradigm gap of its genitive. -/
inductive Facilitator
  | plural | modified | gap
  deriving DecidableEq, Repr

/-- The possessor nominal: its nominality, its animacy, and the facilitating conditions it
meets. -/
structure Possessor where
  nominality : Nominality
  animacy : Animacy
  facilitators : Finset Facilitator

/-- The facilitation order: `p ≤ q` when `q` is the same kind of nominal as `p` and meets every
facilitating condition `p` does. -/
instance : Preorder Possessor where
  le p q := p.nominality = q.nominality ∧ p.animacy = q.animacy ∧
    p.facilitators ⊆ q.facilitators
  le_refl _ := ⟨rfl, rfl, subset_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

instance : DecidableRel (α := Possessor) (· ≤ ·) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A possessive row: the relation, the possessor, and the judgment on the apo-PP. -/
structure Row where
  relation : Relation
  possessor : Possessor
  judgment : Judgment

def relationOf : List (String × Relation) :=
  [("partWhole", .partWhole), ("source", .source), ("kinship", .kinship),
    ("ownership", .ownership), ("association", .association)]

/-- The feature value under which a row meets each facilitating condition. -/
def facilitatorOf : List (String × String × Facilitator) :=
  [("number", "pl", .plural), ("modified", "yes", .modified), ("gap", "yes", .gap)]

/-- The possessive rows. -/
def rows : List Row := groupRows "possessive" fun e ↦ do
  let fs := facilitatorOf.filterMap fun (k, v, f) ↦ if e.feature? k = some v then some f else none
  some ⟨← e.parse? "relation" relationOf, ⟨← e.parse? "possessor" nominalityOf,
    ← e.parse? "animacy" animacyOf, fs.toFinset⟩, e.judgment⟩

-- (5), (14)
theorem partitive_alternates :
    ∀ r ∈ rows, r.relation.IsPartitive → r.possessor.nominality = .commonNoun →
      Acceptable r.judgment := by
  decide

-- (9a), (10a)
theorem individual_resists :
    ∀ r ∈ rows, r.possessor.nominality ≠ .commonNoun → ¬ Acceptable r.judgment := by
  decide

-- (6), (11a), (15)
theorem nonpartitive_resists :
    ∀ r ∈ rows, ¬ r.relation.IsPartitive → .plural ∉ r.possessor.facilitators →
      .modified ∉ r.possessor.facilitators → ¬ Acceptable r.judgment := by
  decide

/-- Within a relation, acceptability is monotone in the facilitation order: plural marking (11),
modification (fn. 5, (28)) and a paradigm gap (14) only raise the judgment. -/
theorem facilitation_mono :
    ∀ r ∈ rows, ∀ s ∈ rows, r.relation = s.relation → r.possessor ≤ s.possessor →
      r.judgment ≤ s.judgment := by
  decide

-- (5a), (11a): the order does not carry across relations.
theorem relation_matters :
    ∃ r ∈ rows, ∃ s ∈ rows, r.possessor ≤ s.possessor ∧ ¬ r.judgment ≤ s.judgment := by
  decide

/-- A paradigm gap of the genitive does not suffice for the apo-PP: the owner and the kin of
(15) have no genitive and still resist it. -/
theorem gap_not_sufficient :
    ∃ r ∈ rows, .gap ∈ r.possessor.facilitators ∧ ¬ Acceptable r.judgment := by
  decide

-- (5)
theorem gap_not_necessary :
    ∃ r ∈ rows, .gap ∉ r.possessor.facilitators ∧ Acceptable r.judgment := by
  decide

-- (5c), (14b): animacy does not block the apo-PP.
theorem animate_alternates :
    ∃ r ∈ rows, r.possessor.animacy ≠ .inanimate ∧ Acceptable r.judgment := by
  decide

/-! ### Recursive possessives -/

/-- A recursive possessive, (25) to (27): the inner possessor, closest to the head, and the outer
one it embeds. -/
structure Stacked where
  inner : Marking
  outer : Marking
  judgment : Judgment

/-- The recursive possessives. -/
def stacked : List Stacked := groupRows "stacking" fun e ↦ do
  some ⟨← e.parse? "inner" markingOf, ← e.parse? "outer" markingOf, e.judgment⟩

-- (25), (27)
theorem innermost_alternates : ∀ s ∈ stacked, Acceptable s.judgment ↔ s.outer = .genitive := by
  decide

/-! ### Derived nominals and the single argument restriction -/

/-- An argument of a derived nominal: its realization and its nominality. -/
structure Argument where
  marking : Marking
  nominality : Nominality
  deriving DecidableEq, Repr

/-- A derived nominal: its theme and its agent, if realized, whether an aspectual modifier
(*for x time*) is present, and whether the nominal is plural. -/
structure Nominal where
  theme : Option Argument
  agent : Option Argument
  aspectual : Bool
  plural : Bool
  deriving DecidableEq, Repr

namespace Nominal

variable {n : Nominal} {r : NominalizationReading} {t a : Argument}

/-- The arguments of `n` inside the DP under the reading `r`: the theme, and the agent unless it
is a by-phrase, an apo-PP adjoined to the verbal structure of the complex-event reading (31). -/
def arguments (n : Nominal) (r : NominalizationReading) : List Argument :=
  n.theme.toList ++ n.agent.toList.filter fun a ↦ ¬ (r = .complexEvent ∧ a.marking = .apo)

/-- The reading `r` is available to the nominal `n`. -/
@[mk_iff]
structure Licenses (n : Nominal) (r : NominalizationReading) : Prop where
  /-- An aspectual modifier diagnoses the complex-event reading. -/
  aspectual : n.aspectual → r = .complexEvent
  /-- A complex-event nominal does not pluralize. -/
  plural : n.plural → r ≠ .complexEvent
  /-- The paper's claim: a theme realized as an apo-PP is not an argument of verbal structure,
  so the nominal patterns with result nominals. -/
  theme : ∀ t ∈ n.theme, t.marking = .apo → r ≠ .complexEvent
  /-- The single argument restriction: the DP has one position for an argument. -/
  single : (n.arguments r).length ≤ 1
  /-- An apo-PP inside the DP is the possessive one, which resists pronouns and proper names. -/
  common : ∀ a ∈ n.arguments r, a.marking = .apo → a.nominality = .commonNoun

instance : Decidable (n.Licenses r) := decidable_of_iff _ (licenses_iff n r).symm

/-- Some reading is available to the nominal. -/
def WellFormed (n : Nominal) : Prop := ∃ r, n.Licenses r

instance : DecidablePred WellFormed := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

-- (34)
theorem Licenses.not_aspectual (h : n.Licenses r) (ht : n.theme = some t)
    (hm : t.marking = .apo) : ¬ n.aspectual :=
  fun hasp ↦ h.theme t ht hm (h.aspectual hasp)

-- (30): beside a theme, the agent is a by-phrase.
theorem Licenses.byPhrase (h : n.Licenses r) (ht : n.theme = some t) (ha : n.agent = some a) :
    r = .complexEvent ∧ a.marking = .apo := by
  by_contra hr
  have := h.single
  simp [arguments, ht, ha, hr] at this

/-- A nominal with both arguments has a genitive theme and an apo agent, the by-phrase of the
complex-event reading. Two genitives, two apo-PPs, and an apo theme beside a genitive agent are
all excluded: an apo theme leaves no verbal structure for a by-phrase to adjoin to, and the DP
holds one argument. -/
theorem WellFormed.genitive_and_apo (h : n.WellFormed) (ht : n.theme = some t)
    (ha : n.agent = some a) : t.marking = .genitive ∧ a.marking = .apo := by
  obtain ⟨r, h⟩ := h
  have hr := h.byPhrase ht ha
  refine ⟨?_, hr.2⟩
  cases hm : t.marking
  · rfl
  · exact absurd hr.1 (h.theme t ht hm)

end Nominal

/-- Standard Modern Greek, or Grevena Greek with no inflectional genitive. -/
inductive Variety
  | smg | grevena
  deriving DecidableEq, Repr

/-- A derived-nominal row: the variety, the nominal, and the judgment. -/
structure DerivedRow where
  variety : Variety
  nominal : Nominal
  judgment : Judgment

def varietyOf : List (String × Variety) := [("smg", .smg), ("grevena", .grevena)]

/-- The argument a row records under the keys `role` and `form`, if it has one. -/
def argument? (e : Datum) (role form : String) : Option Argument := do
  some ⟨← e.parse? role markingOf, ← e.parse? form nominalityOf⟩

/-- The derived-nominal rows. -/
def derivedRows : List DerivedRow := groupRows "derived" fun e ↦ do
  some ⟨← e.parse? "variety" varietyOf,
    ⟨argument? e "theme" "themeForm", argument? e "agent" "agentForm",
      e.feature? "aspectual" == some "yes", e.feature? "head" == some "pl"⟩, e.judgment⟩

/-- In Standard Modern Greek a derived nominal is accepted exactly when some reading is
available to it. -/
theorem derived_rows_agree :
    ∀ r ∈ derivedRows, r.variety = .smg → (Acceptable r.judgment ↔ r.nominal.WellFormed) := by
  decide

-- (12)
theorem grevena_stacks :
    ∃ r ∈ derivedRows, r.variety = .grevena ∧ ¬ r.nominal.WellFormed ∧ Acceptable r.judgment := by
  decide

/-! ### Fronting and sub-extraction -/

/-- A possessor fronted with its head noun or extracted out of its DP, (22) to (24): the variety,
the realization of the possessor, and the judgment. -/
structure Displaced where
  variety : Variety
  marking : Marking
  judgment : Judgment

/-- The fronting and sub-extraction rows. -/
def displaced : List Displaced := groupRows "displacement" fun e ↦ do
  some ⟨← e.parse? "variety" varietyOf, ← e.parse? "marking" markingOf, e.judgment⟩

-- (22) to (24): the Grevena apo-PP moves as the standard genitive does; the standard apo-PP
-- does not.
theorem displacement_rows_agree :
    ∀ r ∈ displaced, ¬ Acceptable r.judgment ↔ r.variety = .smg ∧ r.marking = .apo := by
  decide

/-! ### Scope and the merge site of the possessor -/

/-- The merge site of a possessor: the complement of the possessee, or external to it. -/
inductive Site
  | complement | external
  deriving DecidableEq, Repr

/-- [alexiadou-2003]: a genitive inalienable possessor is a complement, an alienable one is
external. -/
def Relation.genitiveSite (r : Relation) : Site :=
  if r.IsInalienable then .complement else .external

/-- The site of a possessor realized as `m`: every apo-PP is a complement, the structural claim
shared by the paper's three analyses. -/
def Marking.site : Marking → Relation → Site
  | .genitive, r => r.genitiveSite
  | .apo, _ => .complement

/-- A scope row, (38) and (39): an indefinite possessee under a universal possessor, and the
judgment on its surface-scope reading, one leg for all the tables; the inverse reading is always
available. -/
structure ScopeRow where
  marking : Marking
  relation : Relation
  surface : Judgment

/-- The scope rows. -/
def scopeRows : List ScopeRow := groupRows "scope" fun e ↦ do
  some ⟨← e.parse? "marking" markingOf, ← e.parse? "relation" relationOf,
    ← e.readings.lookup "surface"⟩

/-- Surface scope is available exactly for a complement possessor: the inalienable genitive (38a)
and both apo-PPs (39), not the alienable genitive (38b). -/
theorem scope_rows_agree :
    ∀ r ∈ scopeRows, Acceptable r.surface ↔ r.marking.site r.relation = .complement := by
  decide

end KampanarouAlexiadou2026
