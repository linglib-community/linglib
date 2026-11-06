module

public import Mathlib.Data.Finset.Card
public import Linglib.Data.Examples.Comrie1989
public import Linglib.Syntax.Clause.Alignment
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Syntax.Person.Class
public import Linglib.Semantics.Causation.Morphological
public import Linglib.Syntax.Clause.Relative
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Comrie (1989): Language Universals and Linguistic Typology

Case marking serves to keep apart the agent A and the patient P of a transitive clause, so
[accusative and ergative alignment do this with the fewest cases](##discriminates_two_cases_iff)
and differential marking is spent where the information flow departs from the natural one,
[on a P high and an A low in prominence](##marking_rows). A causee takes [the highest free
position on the hierarchy subject > direct object > indirect object > oblique](##causee_rows),
and of two positions [the lower encodes more control](##control_rows). Subject is a prototype,
the intersection of agent and topic, so constructions tied to agents group S with A and those
tied to affected participants S with P, [each as a tendency](##bias_rows).

## Implementation notes

* S, A and P are `ArgumentRole.S`, `.A` and `.P`, and a case system is a marking of the roles, so
  the five logically possible systems are the five alignments of `Alignment.marking_cases`.
* A marking row records, for each argument the book discusses, the scales the book invokes for
  that language and the marking its position takes, obligatory, optional or none. A row covers
  every value of a scale it does not cite, so two rows of a language and role are compared when
  some value of the first lies below some value of the second in the product of the person,
  animacy and definiteness scales. A row whose marking the book attributes to a parameter beside
  the hierarchies, Polish's male-human cut, carries a `parameter` feature and has no marking.
* The departures from the paradigm causee are per-language parameters: which positions a
  language doubles, whether it demotes further than required, and whether it has a passive
  expressing its agent in the causee's oblique case, the last consulted only by the rival
  analysis. Sanskrit's and Kannada's passives are textbook facts.
* Imperative addressee deletion and indirect commands are tied to agents, the resultative to
  affected participants, and coordination to neither; the book gives the Chukchi infinitive
  construction no bias.

## TODO

* The book's four-grade definiteness continuum, complete identifiability > definite superset >
  relevance of identification > neither, is coarsened onto the substrate's scale, which merges
  the middle two grades into the specific indefinite.
* The book says Sanskrit has no dative causee at all, a position the hierarchy skips; the
  parameters record only doubling and further demotion, and no row tests the gap.
* The argument that Hungarian has an oblique causee and no passive to supply it is recorded in
  the parameters but tested by no row, since the book gives no Hungarian causative of a
  transitive verb.
* The doubling universal, that the possibilities for doubling increase down the hierarchy, needs
  more languages than the book's rows give.
* Each language's marking rows should extend to a conditioned marking that fits the prominence
  order in the sense of `Alignment.Fits`, A marked on a lower set and P on an upper set; the book
  states the cut-off form of the prediction, and `marking_rows` checks only pairs of rows.
* The animacy hierarchy of chapter 9 (the Navajo *yi-* ~ *bi-* alternation, Chukchi number,
  Tangut and Southern Tiwa agreement), the Russian numeral continuum, and Greenberg's Universal
  38 on the unmarkedness of the case of S are not stated.

## References

* [B. Comrie, *Language Universals and Linguistic Typology* (1989)][comrie-1989]
* [E. L. Keenan and B. Comrie, *Noun Phrase Accessibility and Universal Grammar*
  (1977)][keenan-comrie-1977]
* [B. Comrie, *Ergativity* (1978)][comrie-1978]
* [M. Silverstein, *Hierarchy of Features and Ergativity* (1976)][silverstein-1976]
* [R. M. W. Dixon, *The Dyirbal Language of North Queensland* (1972)][dixon-1972]
-/

@[expose] public section

namespace Comrie1989

open Alignment Causation.Morphological

/-! ### The discriminatory function of case -/

section Discrimination

variable {κ : Type*} {m : ArgumentRole → κ}

-- §6.1
theorem ne_iff_not_isNeutral_and_not_isHorizontal :
    m .A ≠ m .P ↔ ¬ IsNeutral m ∧ ¬ IsHorizontal m := by
  unfold IsNeutral IsHorizontal
  by_cases h₁ : m .S = m .A <;> by_cases h₂ : m .S = m .P <;> by_cases h₃ : m .A = m .P <;>
    simp_all

/-- A marking keeps A and P apart with only two cases on S, A and P exactly when it is accusative
or ergative: since S never occurs with A or P, its case can serve one of them, and the tripartite
system spends a third case on a distinction never needed (§6.1). -/
theorem discriminates_two_cases_iff [DecidableEq κ] :
    m .A ≠ m .P ∧ (ArgumentRole.core.image m).card = 2 ↔ IsAccusative m ∨ IsErgative m := by
  simp only [ArgumentRole.core, Finset.image_insert, Finset.image_singleton, IsAccusative,
    IsErgative]
  by_cases h₁ : m .S = m .A <;> by_cases h₂ : m .S = m .P <;> by_cases h₃ : m .A = m .P <;>
    simp_all [Finset.card_insert_of_notMem]

end Discrimination

/-! ### The rows -/

/-- The rows the book accepts. -/
def acceptable : List Datum := Examples.all.filter (·.judgment = .acceptable)

/-! ### Differential marking and the natural information flow (§6.2) -/

/-- The marking an argument's position takes is none, optional, or obligatory. -/
inductive Marked
  | unmarked | optional | marked
  deriving DecidableEq, Repr, Fintype

/-- Optional marking sits between unmarked and marked. -/
instance : LinearOrder Marked := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- One argument's marking in a row records its role, the parameters the book invokes for the
language, and the marking its position takes. -/
structure Marking where
  /-- A or P; S, taking the unmarked case, has no row. -/
  role : ArgumentRole
  /-- Whether the argument is a speech-act participant, where the marking consults it. -/
  person : Option Person.Class
  /-- The argument's animacy, where the marking consults it. -/
  animacy : Option Animacy
  /-- The argument's degree of definiteness, where the marking consults it. -/
  definiteness : Option DefinitenessDegree
  /-- The marking the position takes. -/
  marked : Marked

/-- The animacy labels of the rows, read as person and animacy apart, the speech-act
participants being human and the nouns third person. -/
def animacyNames : List (String × (Person.Class × Animacy)) :=
  [("speaker", (.participant, .human)), ("addressee", (.participant, .human)),
    ("human", (.nonParticipant, .human)), ("animal", (.nonParticipant, .animate)),
    ("inanimate", (.nonParticipant, .inanimate))]

/-- The markings a row records, one per argument whose marking it gives, under the key
prefixes `A.` and `P.`; a row whose marking the book attributes to a parameter beside the
hierarchies has none. -/
def Marking.ofRow (row : Datum) : List Marking :=
  if row.feature? "construction" = some "marking" ∧ row.feature? "parameter" = none then
    [(ArgumentRole.A, "A."), (.P, "P.")].filterMap fun (role, p) ↦ do
      let a := row.parse? (p ++ "animacy") animacyNames
      return ⟨role, a.map Prod.fst, a.map Prod.snd,
        row.parse? (p ++ "definiteness") [("definite", DefinitenessDegree.definite),
          ("indefiniteSpecific", .specific), ("nonSpecific", .nonSpecific)],
        ← row.parse? (p ++ "marked")
          [("marked", Marked.marked), ("optional", .optional), ("unmarked", .unmarked)]⟩
  else []

/-- `m₁` marks the same role as `m₂` and is at most as prominent on every parameter both
cite. -/
def Marking.AtMost (m₁ m₂ : Marking) : Prop :=
  m₁.role = m₂.role ∧ (∀ p₁ ∈ m₁.person, ∀ p₂ ∈ m₂.person, p₁ ≤ p₂) ∧
    (∀ a₁ ∈ m₁.animacy, ∀ a₂ ∈ m₂.animacy, a₁ ≤ a₂) ∧
    ∀ d₁ ∈ m₁.definiteness, ∀ d₂ ∈ m₂.definiteness, d₁ ≤ d₂

instance (m₁ m₂ : Marking) : Decidable (m₁.AtMost m₂) := inferInstanceAs (Decidable (_ ∧ _))

/-- The pair follows the information flow: where `m₁` is at most as prominent as `m₂`, a P is
marked no more and an A no less. -/
def Marking.FollowsFlow (m₁ m₂ : Marking) : Prop :=
  m₁.AtMost m₂ → (m₁.role = .P → m₁.marked ≤ m₂.marked) ∧ (m₁.role = .A → m₂.marked ≤ m₁.marked)

instance (m₁ m₂ : Marking) : Decidable (m₁.FollowsFlow m₂) := inferInstanceAs (Decidable (_ → _))

/-- A marking row is acceptable exactly when its marking agrees with the information flow against
every acceptable row of its language, special P-marking rising up the prominence scales and
special A-marking falling down them; the one row the book doubts, the Hindi human P without *ko*
of (18), is the one that departs ((7)–(27) of chapter 6). -/
theorem marking_rows : ∀ r ∈ Examples.all, r.feature? "construction" = some "marking" →
    (r.judgment = .acceptable ↔ ∀ r' ∈ acceptable.filter (·.language = r.language),
      ∀ m ∈ Marking.ofRow r, ∀ m' ∈ Marking.ofRow r', m.FollowsFlow m' ∧ m'.FollowsFlow m) := by
  decide

theorem marking_contrast : ∀ role : ArgumentRole, role = .A ∨ role = .P →
    ∃ r₁ ∈ acceptable, ∃ r₂ ∈ acceptable, r₁.language = r₂.language ∧
      ∃ m₁ ∈ Marking.ofRow r₁, ∃ m₂ ∈ Marking.ofRow r₂, m₁.role = role ∧ m₁.AtMost m₂ ∧
        (role = .P → m₁.marked < m₂.marked) ∧ (role = .A → m₂.marked < m₁.marked) := by
  decide

/-! ### The causee hierarchy (§8.2) -/

/-- `causeePosition s` is the position of the same name in [keenan-comrie-1977]'s accessibility
hierarchy. -/
def causeePosition : CauseeSlot → Relativization.Position
  | .directObject => .directObject
  | .indirectObject => .indirectObject
  | .oblique => .oblique

/-- The causee hierarchy embedded in the accessibility hierarchy, which the book finds very similar
to it once the indirect object is included, without the two being necessarily identical
(p. 177). -/
def causeeEmbedding : CauseeSlot ↪o Relativization.Position :=
  OrderEmbedding.ofStrictMono causeePosition fun a b ↦ by revert a b; decide

theorem range_causeeEmbedding :
    Set.range causeeEmbedding = Set.Icc .oblique .directObject := by
  ext p
  simp only [causeeEmbedding, OrderEmbedding.coe_ofStrictMono, Set.mem_range, Set.mem_Icc]
  revert p; decide

/-- A language's departures from the paradigm case. -/
structure Parameters where
  /-- The positions the language lets a causee double. -/
  doubles : Finset CauseeSlot
  /-- Whether the causee may take a position below the paradigm one. -/
  extended : Bool
  /-- Whether the language has a passive expressing its agent in the oblique case of the
  causee, which the rival analysis consults. -/
  passive : Bool

/-- Among the languages with causative rows, Turkish doubles indirect objects and
never demotes further, Sanskrit doubles direct objects and demotes to the instrumental,
French, Hungarian, Japanese and Kannada demote further, and Hungarian has no passive. -/
def parameters : List (Glottocode × Parameters) :=
  [(.turkish, { doubles := {.indirectObject}, extended := false, passive := true }),
    (.sanskrit, { doubles := {.directObject}, extended := true, passive := true }),
    (.french, { doubles := ∅, extended := true, passive := true }),
    (.hungarian, { doubles := ∅, extended := true, passive := false }),
    (.japanese, { doubles := ∅, extended := true, passive := true }),
    (.kannada, { doubles := ∅, extended := true, passive := true })]

/-- The causee positions the rows name. -/
def causeeNames : List (String × CauseeSlot) :=
  [("directObject", .directObject), ("indirectObject", .indirectObject), ("oblique", .oblique)]

/-- A causative row's configuration is the base verb's valency, the causee's position, and the
language's parameters. -/
structure Causative where
  /-- The base verb's valency. -/
  valency : ℕ
  /-- The position the causee takes. -/
  causee : CauseeSlot
  /-- The language's parameters. -/
  params : Parameters

/-- The configuration a causative or control row records. -/
def Causative.ofRow (row : Datum) : Option Causative := do
  guard (row.feature? "construction" ∈ [some "causative", some "control"])
  return ⟨← row.nat? "valency", ← row.parse? "causee" causeeNames, ← row.byLanguage parameters⟩

/-- The paradigm position is the highest the base verb's arguments leave free. -/
def Causative.paradigm (c : Causative) : CauseeSlot := causeeDemotion c.valency

/-- The causee doubles a filled position the language permits. -/
def Causative.Doubles (c : Causative) : Prop := c.causee ∈ c.params.doubles ∧ c.paradigm < c.causee

instance (c : Causative) : Decidable c.Doubles := inferInstanceAs (Decidable (_ ∧ _))

/-- The hierarchy analysis admits the causee's position in the paradigm case, in a doubled
position, or in a lower one where the language demotes further. -/
def Causative.HierarchyAdmits (c : Causative) : Prop :=
  c.causee = c.paradigm ∨ c.Doubles ∨ (c.params.extended ∧ c.causee < c.paradigm)

instance (c : Causative) : Decidable c.HierarchyAdmits := inferInstanceAs (Decidable (_ ∨ _))

/-- The rival analysis takes the oblique causee as a passive agent, admitting the paradigm case,
a doubled position, or the oblique of a transitive base wherever the language has a passive. -/
def Causative.PassiveAdmits (c : Causative) : Prop :=
  c.causee = c.paradigm ∨ c.Doubles ∨ (c.params.passive ∧ 2 ≤ c.valency ∧ c.causee = .oblique)

instance (c : Causative) : Decidable c.PassiveAdmits := inferInstanceAs (Decidable (_ ∨ _))

/-- The causee hierarchy with each language's parameters admits exactly the accepted positions of
(12)–(16), (17)–(18), (20) and (22). -/
theorem causee_rows : ∀ row ∈ Examples.all, ∀ c ∈ Causative.ofRow row,
    (row.judgment = .acceptable ↔ c.HierarchyAdmits) := by
  decide

-- (22) and (9): Turkish passivizes every transitive verb yet bars the oblique causee of one, and
-- the oblique causee of the intransitive (9) is one no passive can supply.
theorem passive_analysis_fails :
    (∃ row ∈ Examples.all, ∃ c ∈ Causative.ofRow row,
      c.PassiveAdmits ∧ row.judgment = .ungrammatical) ∧
      ∃ row ∈ Examples.all, ∃ c ∈ Causative.ofRow row,
        ¬ c.PassiveAdmits ∧ row.judgment = .acceptable := by
  decide

/-- Whether a causee retains less or more control. -/
inductive Control
  | less | more
  deriving DecidableEq, Repr

/-- A control row's configuration is the control the causee retains and its position. -/
structure Controlled where
  /-- The control the causee retains. -/
  control : Control
  /-- The position the causee takes. -/
  causee : CauseeSlot

/-- The configuration a control row records. -/
def Controlled.ofRow (row : Datum) : Option Controlled := do
  guard (row.feature? "construction" = some "control")
  return ⟨← row.parse? "control" [("less", Control.less), ("more", .more)],
    ← row.parse? "causee" causeeNames⟩

/-- Within a language the causee retaining more control takes the lower hierarchy position, and some
language offers the pair ((8)–(9), (23)–(28)). -/
theorem control_rows :
    (∀ r₁ ∈ Examples.all, ∀ c₁ ∈ Controlled.ofRow r₁,
      ∀ r₂ ∈ Examples.all.filter (·.language = r₁.language), ∀ c₂ ∈ Controlled.ofRow r₂,
        c₁.control = .less → c₂.control = .more → c₂.causee < c₁.causee) ∧
      ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all, r₁.language = r₂.language ∧
        ∃ c₁ ∈ Controlled.ofRow r₁, ∃ c₂ ∈ Controlled.ofRow r₂,
          c₁.control = .less ∧ c₂.control = .more := by
  decide

/-! ### Compactness and directness (§8.1) -/

/-- The causative construction a row records, its formal complexity and its mediation. -/
def CausativeConstruction.ofRow (row : Datum) : Option CausativeConstruction := do
  guard (row.feature? "construction" = some "compactness")
  return ⟨← row.parse? "complexity"
      [("lexical", CausativeComplexity.lexical), ("morphological", .morphological),
      ("analytic", .periphrastic)],
    ← row.parse? "mediation" [("direct", Mediation.direct), ("indirect", .indirect)]⟩

-- Nivkh (6)–(7) and English *Anton broke the stick* against *Anton brought it about that the
-- stick broke*.
theorem compactness_rows :
    (∀ r₁ ∈ Examples.all, ∀ c₁ ∈ CausativeConstruction.ofRow r₁,
      ∀ r₂ ∈ Examples.all.filter (·.language = r₁.language),
        ∀ c₂ ∈ CausativeConstruction.ofRow r₂, c₁.ComrieMonotone c₂) ∧
      ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all, r₁.language = r₂.language ∧
        ∃ c₁ ∈ CausativeConstruction.ofRow r₁, ∃ c₂ ∈ CausativeConstruction.ofRow r₂,
          c₁.complexity < c₂.complexity ∧ c₁.mediation < c₂.mediation := by
  decide

/-! ### Subject as a prototype (chapter 5) -/

/-- The argument of a transitive clause a construction groups with S is A, P, or neither,
where either may be omitted. -/
inductive Grouping
  | withA | withP | neither
  deriving DecidableEq, Repr, Fintype

/-- The constructions tested. -/
inductive Test
  | coordination | imperative | indirectCommand | resultative | infinitive
  deriving DecidableEq, Repr, Fintype

/-- The prototype predicts that a construction tied to agents, the deletion of an imperative's
addressee or of the recipient of an indirect command, favours S with A, and one tied to affected
participants, the resultative, S with P; coordination, tied to neither, is free to vary (§5.4).
The Chukchi infinitive construction, nominative-accusative in a language whose coordination is
neutral, is given no bias (§5.3). -/
def Test.bias : Test → Option Grouping
  | .imperative | .indirectCommand => some .withA
  | .resultative => some .withP
  | .coordination | .infinitive => none

/-- A grouping row's configuration. -/
structure Grouped where
  /-- The construction. -/
  test : Test
  /-- The grouping it shows. -/
  grouping : Grouping

/-- The configuration a grouping row records. -/
def Grouped.ofRow (row : Datum) : Option Grouped := do
  guard (row.feature? "construction" = some "grouping")
  return ⟨← row.parse? "test" [("coordination", Test.coordination), ("imperative", .imperative),
      ("indirectCommand", .indirectCommand), ("resultative", .resultative),
      ("infinitive", .infinitive)],
    ← row.parse? "grouping" [("withA", Grouping.withA), ("withP", .withP), ("neither", .neither)]⟩

/-- Imperative addressee deletion groups S with A in every language, even Dyirbal, and the
resultative groups S with P somewhere; but each bias is a tendency, crossed by the Dyirbal
indirect command and the English resultative (§5.4). -/
theorem bias_rows :
    (∀ row ∈ Examples.all, ∀ g ∈ Grouped.ofRow row, g.test = .imperative →
      g.grouping = .withA) ∧
      (∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
        g.test = .resultative ∧ g.grouping = .withP) ∧
      ∀ b : Grouping, b ≠ .neither → ∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
        g.test.bias = some b ∧ g.grouping ≠ b := by
  decide

theorem coordination_rows : ∀ gr : Grouping, ∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
    g.test = .coordination ∧ g.grouping = gr := by
  decide

theorem mixed_rows : ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all, r₁.language = r₂.language ∧
    ∃ g₁ ∈ Grouped.ofRow r₁, ∃ g₂ ∈ Grouped.ofRow r₂, g₁.grouping ≠ g₂.grouping := by
  decide

end Comrie1989
