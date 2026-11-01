module

public import Mathlib.Data.Finset.Card
public import Linglib.Data.Examples.Comrie1989
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Syntax.Person.Class
public import Linglib.Semantics.Causation.Morphological
public import Linglib.Syntax.Clause.Relative
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Comrie (1989): Language Universals and Linguistic Typology

Three of the book's chapters make claims sharp enough to state. Case marking (chapter 6) serves
first to discriminate the two arguments of a transitive clause: of the five ways the primitives
S, A and P can share cases, only the nominative–accusative and ergative–absolutive systems keep
A and P apart with two cases, which is why those two are the widespread ones, the tripartite
system spending a case on a distinction it does not need and the neutral and the A/P-against-S
systems failing to make the one that matters. The same function explains differential marking:
the agent of a transitive clause is typically more animate and more definite than its patient,
so marking is spent on the departures, a P high on the hierarchies or an A low on them, and
each language's marking is monotone in prominence, Russian and Polish by animacy, Turkish and
Persian by definiteness, Hindi and Spanish by both, Dyirbal marking its As downward and its Ps
upward from the same cut between first and second person pronouns and the rest of the animacy
hierarchy.

In causatives (chapter 8) the causee takes the highest position on the hierarchy subject >
direct object > indirect object > oblique that the base verb's arguments leave free, as Turkish
shows for intransitive, transitive and ditransitive bases; languages may in addition double a
filled position, Sanskrit a direct object and Turkish an indirect object, or demote further
than required, French by *par*, and the analysis of the oblique causee as a passive fails for
Turkish, where passive applies to every transitive verb but the oblique causee only to
ditransitive bases, and for Hungarian, which has an oblique causee and no passive expressing
its agent in that case. Where a language offers two cases for the causee, the one lower on
the hierarchy encodes the causee that retains more control, Hungarian instrumental over
accusative, Japanese dative over accusative, Kannada instrumental over dative; and within a
language the more compact a causative's form, the more direct the causation it expresses.
Subject (chapter 5) is a prototype, the intersection of agent and topic, so that constructions
tied to agents, such as imperative addressee deletion, group S with A even in Dyirbal,
constructions tied to affected participants, such as the Nivkh resultative, group S with P,
both as tendencies, and constructions tied to neither, such as coordination, vary: S with A in
English, S with P in Dyirbal, neither in Chukchi.

The case systems are the equivalence relations on the three primitives, `caseSystem_of_equivalence`
that the five are all of them and `discriminates_two_case_iff` that two of them are the
economical discriminating ones; the book's examples are the rows, over which `marking_monotone`
is the information-flow prediction, `causee_rows` and `passive_analysis_fails` the hierarchy
against its rival, `range_causeeEmbedding` its place in the accessibility hierarchy of relative
clauses, `control_rows` the control hierarchy, `compactness_rows` the directness
correlation through the substrate's monotonicity, and `bias_rows`, `coordination_rows` and
`mixed_rows` the prototype's predictions.

## Implementation notes

* A marking row records, for each argument the book discusses, the scales the book invokes for that
  language and the marking its position takes, obligatory, optional or none; monotonicity is read
  over pairs of acceptable rows of one language and role in the product order of the parameters §9.4
  separates, person, animacy proper and the degree of definiteness, a parameter the row does not
  cite constraining nothing. A row whose marking the book attributes to a parameter beside the
  hierarchies, Polish's male-human cut, carries a `parameter` feature and has no marking.
* The departures from the paradigm case are per-language parameters: which positions a
  language doubles, whether it demotes further than required, and whether it has a passive,
  the last consulted only by the rival analysis and stated by the book for Turkish, French and
  Hungarian; Sanskrit's and Kannada's passives are textbook facts.
* The prototype's predictions are stated through the bias of a construction type, agent-linked
  or patient-linked, which the book gives as the explanation; a control complement, the
  Chukchi infinitive construction, favours S with A on the book's account, and coordination
  has no bias.

## TODO

* The book's four-grade definiteness continuum, complete identifiability > definite superset >
  discourse relevance > neither, is coarsened onto the substrate's scale, which merges the
  middle two grades; Persian (23) and Turkish (25) are therefore indefinite specific.
* The book says Sanskrit has no dative causee at all, a position the hierarchy skips; the
  parameters record only doubling and further demotion, and no row tests the gap.
* The doubling universal of §8.2, that the possibilities for doubling increase down the
  hierarchy, needs more languages than the book's rows give.
* Chapter 9's animacy hierarchy is prose here: the Navajo *yi-* ~ *bi-* alternation, Chukchi
  number and the Tangut and Southern Tiwa agreement data would need agreement substrate.
* The Russian numeral continuum of §5.2 and Greenberg's Universal 38 on the unmarkedness of the
  S case (§6.1) are not stated.

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

open Causation.Morphological

/-! ### The discriminatory function of case (§6.1) -/

/-- The three primitives of case marking are the intransitive subject and the agent and patient
of the transitive clause. -/
inductive Primitive
  | S | A | P
  deriving DecidableEq, Repr, Fintype

/-- The five logically possible case systems, by which primitives share a case. -/
inductive CaseSystem
  | neutral | nominativeAccusative | ergativeAbsolutive | tripartite | apAgainstS
  deriving DecidableEq, Repr, Fintype

/-- The cases of a system, as the sets of primitives each marks. -/
def CaseSystem.blocks : CaseSystem → Finset (Finset Primitive)
  | .neutral => {{.S, .A, .P}}
  | .nominativeAccusative => {{.S, .A}, {.P}}
  | .ergativeAbsolutive => {{.S, .P}, {.A}}
  | .tripartite => {{.S}, {.A}, {.P}}
  | .apAgainstS => {{.A, .P}, {.S}}

/-- Two primitives take the same case. -/
def CaseSystem.Same (c : CaseSystem) (x y : Primitive) : Prop := ∃ b ∈ c.blocks, x ∈ b ∧ y ∈ b

instance (c : CaseSystem) (x y : Primitive) : Decidable (c.Same x y) :=
  inferInstanceAs (Decidable (∃ b ∈ c.blocks, x ∈ b ∧ y ∈ b))

/-- The number of cases. -/
def CaseSystem.caseCount (c : CaseSystem) : ℕ := c.blocks.card

/-- The system discriminates the two arguments of a transitive clause. -/
def CaseSystem.Discriminates (c : CaseSystem) : Prop := ¬ c.Same .A .P

instance (c : CaseSystem) : Decidable c.Discriminates := inferInstanceAs (Decidable (¬ _))

/-- The reflexive symmetric relation with the given values on the three pairs. -/
private def rel (sa sp ap : Bool) : Primitive → Primitive → Bool
  | .S, .A | .A, .S => sa
  | .S, .P | .P, .S => sp
  | .A, .P | .P, .A => ap
  | _, _ => true

private theorem exhaustive_bool : ∀ sa sp ap : Bool, (sa → sp → ap) → (sa → ap → sp) →
    (sp → ap → sa) → ∃ c : CaseSystem, ∀ x y, rel sa sp ap x y ↔ c.Same x y := by
  decide

theorem caseSystem_of_equivalence (r : Primitive → Primitive → Prop) (h : Equivalence r) :
    ∃ c : CaseSystem, ∀ x y, r x y ↔ c.Same x y := by
  classical
  have hs : ∀ x y, r x y ↔ r y x := fun _ _ ↦ ⟨h.symm, h.symm⟩
  obtain ⟨c, hc⟩ := exhaustive_bool (decide (r .S .A)) (decide (r .S .P)) (decide (r .A .P))
    (by simpa using fun h₁ h₂ ↦ h.trans (h.symm h₁) h₂) (by simpa using fun h₁ ↦ h.trans h₁)
    (by simpa using fun h₁ h₂ ↦ h.trans h₁ (h.symm h₂))
  refine ⟨c, fun x y ↦ (?_ : r x y ↔ _).trans (hc x y)⟩
  cases x <;> cases y <;> simp [rel, h.refl _, hs .A .S, hs .P .S, hs .P .A]

theorem CaseSystem.discriminates_iff (c : CaseSystem) :
    c.Discriminates ↔ c ≠ .neutral ∧ c ≠ .apAgainstS := by
  cases c <;> decide

theorem CaseSystem.discriminates_two_case_iff (c : CaseSystem) :
    c.Discriminates ∧ c.caseCount = 2 ↔ c = .nominativeAccusative ∨ c = .ergativeAbsolutive := by
  cases c <;> decide

/-! ### The rows -/

/-- The rows the book accepts. -/
def acceptable : List Datum := Examples.all.filter (·.judgment = .acceptable)

/-! ### Differential marking and the natural information flow (§6.2) -/

/-- The marking an argument's position takes is none, optional, or obligatory. -/
inductive Marked
  | unmarked | optional | marked
  deriving DecidableEq, Repr

/-- Optional marking sits between unmarked and marked. -/
def Marked.toNat : Marked → ℕ
  | .unmarked => 0
  | .optional => 1
  | .marked => 2

instance : LinearOrder Marked :=
  LinearOrder.lift' Marked.toNat (fun a b h ↦ by cases a <;> cases b <;> simp_all [Marked.toNat])

/-- One argument's marking in a row records its role, the parameters the book invokes for the
language, and the marking its position takes. -/
structure Marking where
  /-- A or P; S, taking the unmarked case, has no row. -/
  role : Primitive
  /-- Whether the argument is a speech-act participant, where the marking consults it. -/
  person : Option Person.Class
  /-- The argument's animacy, where the marking consults it. -/
  animacy : Option Animacy
  /-- The argument's degree of definiteness, where the marking consults it. -/
  definiteness : Option DefinitenessDegree
  /-- The marking the position takes. -/
  marked : Marked

/-- The animacy labels of the rows, read as person and animacy apart, the parameters §9.4
separates: the speech-act participants are human, and the nouns are third person. -/
def animacyNames : List (String × (Person.Class × Animacy)) :=
  [("speaker", (.participant, .human)), ("addressee", (.participant, .human)),
    ("human", (.nonParticipant, .human)), ("animal", (.nonParticipant, .animate)),
    ("inanimate", (.nonParticipant, .inanimate))]

/-- The markings a row records, one per argument whose marking it gives, under the key
prefixes `A.` and `P.`; a row whose marking the book attributes to a parameter beside the
hierarchies has none. -/
def Marking.ofRow (row : Datum) : List Marking :=
  if row.feature? "construction" = some "marking" ∧ row.feature? "parameter" = none then
    [(Primitive.A, "A."), (.P, "P.")].filterMap fun (role, p) ↦ do
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

/-- Within a language, special P-marking is monotone up the prominence scales and special A-marking
down them ((7)–(27) of chapter 6). -/
theorem marking_monotone : ∀ r₁ ∈ acceptable, ∀ m₁ ∈ Marking.ofRow r₁,
    ∀ r₂ ∈ acceptable.filter (·.language = r₁.language), ∀ m₂ ∈ Marking.ofRow r₂,
      m₁.AtMost m₂ →
        (m₁.role = .P → m₁.marked ≤ m₂.marked) ∧ (m₁.role = .A → m₂.marked ≤ m₁.marked) := by
  decide

theorem marking_contrast : ∀ role : Primitive, role ≠ .S →
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
  doubles : List CauseeSlot
  /-- Whether the causee may take a position below the paradigm one. -/
  extended : Bool
  /-- Whether the language has a passive expressing its agent in the oblique case of the
  causee, which the rival analysis consults. -/
  passive : Bool

/-- Among the languages with causative rows, Turkish doubles indirect objects and
never demotes further, Sanskrit doubles direct objects and demotes to the instrumental,
French, Hungarian, Japanese and Kannada demote further, and Hungarian has no passive. -/
def parameters : List (Glottocode × Parameters) :=
  [(.turkish, { doubles := [.indirectObject], extended := false, passive := true }),
    (.sanskrit, { doubles := [.directObject], extended := true, passive := true }),
    (.french, { doubles := [], extended := true, passive := true }),
    (.hungarian, { doubles := [], extended := true, passive := false }),
    (.japanese, { doubles := [], extended := true, passive := true }),
    (.kannada, { doubles := [], extended := true, passive := true })]

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
  return ⟨← row.parse? "valency" [("1", 1), ("2", 2), ("3", 3)],
    ← row.parse? "causee" [("directObject", .directObject), ("indirectObject", .indirectObject),
      ("oblique", .oblique)],
    ← row.byLanguage parameters⟩

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

/-- The passive analysis wrongly admits the Turkish oblique causee (22) and excludes the Hungarian
instrumental causee (9). -/
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
    ← row.parse? "causee" [("directObject", .directObject), ("indirectObject", .indirectObject),
      ("oblique", .oblique)]⟩

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

/-- Within a language the more compact causative is the more appropriate to direct causation, as in
Nivkh (6)–(7). -/
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
addressee or of the recipient of an indirect command, and a control complement such as the
Chukchi infinitive construction, favour S with A; one tied to affected participants, the
resultative, favours S with P; coordination, tied to neither, is free to vary (§5.3–§5.4). -/
def Test.bias : Test → Option Grouping
  | .imperative | .indirectCommand | .infinitive => some .withA
  | .resultative => some .withP
  | .coordination => none

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
