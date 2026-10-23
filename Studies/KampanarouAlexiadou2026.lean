module

public import Linglib.Data.Examples.KampanarouAlexiadou2026

/-!
# Kampanarou and Alexiadou (2026): Genitive Alternation in Possessives and Beyond

This file formalizes [kampanarou-alexiadou-2026], on the Standard Modern Greek alternation
between an inflectional genitive and a prepositional *apo*-phrase, with adnominal possessors and
with the arguments of derived nominals. The paper argues that the alternation is structural rather
than morphological: the *apo*-PP is not an alternative spell-out of the genitive but a complement
with a partitive semantics, through which a possessive reading is coerced.

The possessive data of Sections 2, 3 and 5 are rows carrying the paper's classification of the
relation and of the possessor nominal (`Possessor`). Part-whole and source relations alternate
with a common-noun possessor, pronouns and proper names never do, and acceptability is monotone in
the facilitation order on possessors, which adds plural marking, modification, or a paradigm gap
of the genitive (`facilitation_mono`); a gap is neither sufficient nor necessary for the
alternation.

For derived nominals (Sections 2 and 6), the complex-event reading of [grimshaw-1990] survives
only under a genitive theme, an *apo* agent is a by-phrase only under that reading, and the
nominal otherwise admits at most one argument (`Nominal.WellFormed`): the single argument
restriction of Section 8, extending the single genitive restriction of [horrocks-stavrou-1987] to
PPs. Grevena Greek, which has lost the inflectional genitive
([michelioudakis-chatzikyriakidis-spathas-2024]), stacks two *apo*-PPs. The scope data of
Section 7 follow from the merge site of the possessor (`Site`): the genitive of an inalienable
possessor and every *apo*-PP are complements ([alexiadou-2003]), and only a complement possessor
admits surface scope (`scope_rows_agree`).

## Implementation notes

The paper's markers are read on the `Judgment` scale, `?` as `marginal`, `??` and `???` as
`questionable`, `#` as `unacceptable` and `*` as `ungrammatical`; a row is `Acceptable` from
`marginal` up, since `?` marks speaker variation. The three syntactic analyses of Section 7
(selection by the possessee, a predicative small clause, a light *p*) share the consequence
formalized here, that the *apo*-PP is a complement, and are not distinguished. The recursive
possessives (25) to (27) record, as the paper does, that only the innermost possessor alternates;
its footnote 14 offers no account.

## References

* [kampanarou-alexiadou-2026]
* [alexiadou-2003], [grimshaw-1990], [horrocks-stavrou-1987]
* [michelioudakis-chatzikyriakidis-spathas-2024]
-/

@[expose] public section

namespace KampanarouAlexiadou2026


/-- Acceptable from `marginal`, the paper's `?`, up. -/
def Acceptable (j : Judgment) : Prop := .marginal ≤ j

instance : DecidablePred Acceptable := λ _ => inferInstanceAs (Decidable (_ ≤ _))

/-! ### Possessive apo-PPs (Sections 2, 3 and 5) -/

/-- The paper's classification of the relation between possessee and possessor: part-whole (5a),
source (5b), kinship (6a), ownership (6b), and the mere association of a mat with its door (11). -/
inductive Relation
  | partWhole | source | kinship | ownership | association
  deriving DecidableEq, Repr

/-- The relations the paper reads as partitive: the possessee is a part of, or comes from, the
possessor. -/
def Relation.IsPartitive (r : Relation) : Prop := r = .partWhole ∨ r = .source

instance : DecidablePred Relation.IsPartitive := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Inalienable relations in the sense of [alexiadou-2003]: parts, body parts, and kin. -/
def Relation.IsInalienable (r : Relation) : Prop := r = .partWhole ∨ r = .kinship

instance : DecidablePred Relation.IsInalienable := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- How the possessor is presented. -/
inductive Form
  | common | pronoun | properName
  deriving DecidableEq, Repr

/-- The possessor nominal: its form, animacy, plural marking and modification, and whether its
genitive is a paradigm gap (Section 3). -/
structure Possessor where
  form : Form
  animate : Bool
  plural : Bool
  modified : Bool
  gap : Bool
  deriving DecidableEq, Repr

/-- The facilitation order: `p ≤ q` when `q` is the same kind of nominal as `p` with plural
marking, modification, or a paradigm gap only added, each of which the paper reports to raise the
acceptability of the apo-PP. -/
instance : PartialOrder Possessor where
  le p q := p.form = q.form ∧ p.animate = q.animate ∧ p.plural ≤ q.plural ∧
    p.modified ≤ q.modified ∧ p.gap ≤ q.gap
  le_refl _ := ⟨rfl, rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩
  le_antisymm p q h h' := by
    obtain ⟨hf, ha, hp, hm, hg⟩ := h
    obtain ⟨-, -, hp', hm', hg'⟩ := h'
    cases p; cases q
    dsimp only at hf ha hp hm hg hp' hm' hg'
    subst hf ha
    rw [le_antisymm hp hp', le_antisymm hm hm', le_antisymm hg hg']

instance : DecidableRel (α := Possessor) (· ≤ ·) :=
  λ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A possessive row: the relation, the possessor, and the judgment on the apo-PP. -/
structure Row where
  relation : Relation
  possessor : Possessor
  judgment : Judgment

def relationOf : List (String × Relation) :=
  [("partWhole", .partWhole), ("source", .source), ("kinship", .kinship),
    ("ownership", .ownership), ("association", .association)]

def formOf : List (String × Form) :=
  [("common", .common), ("pronoun", .pronoun), ("properName", .properName)]

/-- A row of the `possessive` group, from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  guard (e.feature? "group" = some "possessive")
  let rel ← e.parse? "relation" relationOf
  let form ← e.parse? "possessor" formOf
  let yes k := e.feature? k == some "yes"
  some ⟨rel, ⟨form, yes "animate", e.feature? "number" == some "pl", yes "modified", yes "gap"⟩,
    e.judgment⟩

/-- The possessive data of Sections 2, 3 and 5. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Part-whole and source relations alternate whenever the possessor is a common noun, (5), (14). -/
theorem partitive_alternates :
    ∀ r ∈ rows, r.relation.IsPartitive → r.possessor.form = .common → Acceptable r.judgment := by
  decide

/-- Pronouns and proper names resist the apo-PP whatever the relation, (9), (10). -/
theorem individual_resists :
    ∀ r ∈ rows, r.possessor.form ≠ .common → r.judgment = .unacceptable := by
  decide

/-- Kinship, ownership and mere association resist the apo-PP unless the possessor is plural or
modified, (6), (11a), (15). -/
theorem nonpartitive_resists :
    ∀ r ∈ rows, ¬ r.relation.IsPartitive → ¬ r.possessor.plural → ¬ r.possessor.modified →
      ¬ Acceptable r.judgment := by
  decide

/-- Acceptability is monotone in the facilitation order: plural marking (11), modification
(fn. 5, (28)) and a paradigm gap (14) only raise the judgment. -/
theorem facilitation_mono :
    ∀ r ∈ rows, ∀ s ∈ rows, r.relation = s.relation → r.possessor ≤ s.possessor →
      r.judgment ≤ s.judgment := by
  decide

/-- A paradigm gap is not sufficient for the alternation, (15). -/
theorem gap_not_sufficient : ∃ r ∈ rows, r.possessor.gap ∧ r.judgment = .unacceptable := by
  decide

/-- Nor is it necessary, (5). -/
theorem gap_not_necessary : ∃ r ∈ rows, ¬ r.possessor.gap ∧ Acceptable r.judgment := by
  decide

/-- The same possessor yields an acceptable apo-PP for the door's handle (5a) and a questionable one
for its mat (11a). -/
theorem relation_matters :
    ∃ r ∈ rows, ∃ s ∈ rows, r.possessor = s.possessor ∧ r.judgment ≠ s.judgment := by
  decide

/-! ### Recursive possessives (Section 5) -/

/-- The realization of a possessor or of an argument. -/
inductive Marking
  | genitive | apo
  deriving DecidableEq, Repr

def markingOf : List (String × Marking) := [("genitive", .genitive), ("apo", .apo)]

/-- A recursive possessive, (25) to (27): the inner possessor, closest to the head, and the outer
one it embeds. -/
structure Stacked where
  inner : Marking
  outer : Marking
  judgment : Judgment

/-- A row of the `stacking` group. -/
def Stacked.ofDatum (e : Datum) : Option Stacked := do
  guard (e.feature? "group" = some "stacking")
  let i ← e.parse? "inner" markingOf
  let o ← e.parse? "outer" markingOf
  some ⟨i, o, e.judgment⟩

/-- The recursive possessives of Section 5. -/
def stacked : List Stacked := Examples.all.filterMap Stacked.ofDatum

theorem innermost_alternates : ∀ s ∈ stacked, Acceptable s.judgment ↔ s.outer = .genitive := by
  decide

/-! ### Derived nominals (Sections 2 and 6) and the single argument restriction (Section 8) -/

/-- A derived nominal with its theme and its agent, each genitive, apo-PP, or absent, and whether
an aspectual modifier (*for x time*) is present. -/
structure Nominal where
  theme : Option Marking
  agent : Option Marking
  aspectual : Bool
  deriving DecidableEq, Repr

namespace Nominal

/-- The complex-event reading of [grimshaw-1990], with verbal argument structure, is available
only under a genitive theme; an apo theme forces the result reading, diagnosed by the aspectual
modifier (34), (35) and by pluralization (36). -/
def IsComplexEvent (n : Nominal) : Prop := n.theme = some .genitive

instance : DecidablePred IsComplexEvent := λ _ => inferInstanceAs (Decidable (_ = _))

/-- An apo agent is a by-phrase, adjoined to the verbal structure, only under the complex-event
reading, (30). -/
def IsByPhrase (n : Nominal) : Prop := n.agent = some .apo ∧ n.IsComplexEvent

instance : DecidablePred IsByPhrase := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The DP-internal arguments: the theme, and the agent unless it is a by-phrase. -/
def arguments (n : Nominal) : List Marking :=
  n.theme.toList ++ if n.IsByPhrase then [] else n.agent.toList

/-- The single argument restriction: at most one argument inside the DP. -/
def SingleArgument (n : Nominal) : Prop := n.arguments.length ≤ 1

instance : DecidablePred SingleArgument := λ _ => inferInstanceAs (Decidable (_ ≤ _))

/-- A single argument, and an aspectual modifier only under the complex-event reading. -/
def WellFormed (n : Nominal) : Prop := n.SingleArgument ∧ (n.aspectual → n.IsComplexEvent)

instance : DecidablePred WellFormed := λ _ => inferInstanceAs (Decidable (_ ∧ (_ → _)))

theorem not_isComplexEvent_of_theme_apo {n : Nominal} (h : n.theme = some .apo) :
    ¬ n.IsComplexEvent := by
  simp [IsComplexEvent, h]

/-- Two apo-PPs never satisfy the restriction: the theme forces the result reading, so the agent is
a second argument rather than a by-phrase, (8d). -/
theorem not_singleArgument_of_apo_apo {n : Nominal} (ht : n.theme = some .apo)
    (ha : n.agent = some .apo) : ¬ n.SingleArgument := by
  simp [SingleArgument, arguments, IsByPhrase, IsComplexEvent, ht, ha]

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

/-- A row of the `derived` group. -/
def DerivedRow.ofDatum (e : Datum) : Option DerivedRow := do
  guard (e.feature? "group" = some "derived")
  let v ← e.parse? "variety" varietyOf
  some ⟨v, ⟨e.parse? "theme" markingOf, e.parse? "agent" markingOf,
    e.feature? "aspectual" == some "yes"⟩, e.judgment⟩

/-- The derived nominals of Sections 2, 4 and 6. -/
def derivedRows : List DerivedRow := Examples.all.filterMap DerivedRow.ofDatum

/-- The Standard Modern Greek rows are acceptable exactly when well-formed: (7), (8), (30) and
(33) to (36). -/
theorem derived_rows_agree :
    ∀ r ∈ derivedRows, r.variety = .smg → (Acceptable r.judgment ↔ r.nominal.WellFormed) := by
  decide

/-- Grevena Greek stacks two apo-PPs on one nominal, (12). -/
theorem grevena_stacks :
    ∃ r ∈ derivedRows, r.variety = .grevena ∧ ¬ r.nominal.SingleArgument ∧
      Acceptable r.judgment := by
  decide

/-! ### Scope and the merge site of the possessor (Section 7) -/

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

/-- A scope row, (38) and (39): an indefinite possessee under a universal possessor, and whether the
surface-scope reading, one leg for all the tables, is available; the inverse reading always is. -/
structure ScopeRow where
  marking : Marking
  relation : Relation
  surface : Bool

/-- A row of the `scope` group. -/
def ScopeRow.ofDatum (e : Datum) : Option ScopeRow := do
  guard (e.feature? "group" = some "scope")
  let m ← e.parse? "marking" markingOf
  let r ← e.parse? "relation" relationOf
  some ⟨m, r, decide (e.readings.lookup "surface" = some .acceptable)⟩

/-- The scope data of Section 7. -/
def scopeRows : List ScopeRow := Examples.all.filterMap ScopeRow.ofDatum

/-- Surface scope is available exactly for a complement possessor: the inalienable genitive (38a)
and both apo-PPs (39), not the alienable genitive (38b). -/
theorem scope_rows_agree :
    ∀ r ∈ scopeRows, r.surface = true ↔ r.marking.site r.relation = .complement := by
  decide

end KampanarouAlexiadou2026
