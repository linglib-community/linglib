module

public import Mathlib.Data.Finset.Card
public import Linglib.Core.Order.Monotone.Extension
public import Linglib.Data.Examples.Comrie1989
public import Linglib.Syntax.Clause.Alignment
public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Fragments.Turkish.ObjectMarking
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
and of two, [the one keeping more control the lower](##control_rows). Subject is the intersection
of agent and topic, so a construction's alignment [leans to S with A or with P by what it asks of
its pivot](##bias_rows) and [need not match case marking](##dyirbal_marking_syntax).

## Implementation notes

* S, A and P are `ArgumentRole.S`, `.A` and `.P`, and a case system is a marking of the roles, so
  the five logically possible systems are the five alignments of `Alignment.marking_cases`.
* A marking row records, for each argument the book discusses, the scales the book invokes for
  that language and whether its position takes the special marking always, sometimes or never
  (`Alignment.Overtness`), and covers every value of a scale it does not cite. A language's rows
  follow the information flow when a graded marking fitting the componentwise order of person,
  animacy and definiteness (`Alignment.FitsGraded`), A's overtness falling and P's rising, takes
  each row's value on what it covers. By `exists_monotone_forall_eq_iff` such a marking exists
  exactly when the rows agree pair by pair, which `decide` checks. A row whose marking the book
  attributes to a parameter beside the hierarchies, Polish's male-human cut, carries a
  `parameter` feature and has no marking.
* The departures from the paradigm causee are per-language parameters: which positions a
  language doubles, whether it demotes further than required, and whether it has a passive
  expressing its agent in the causee's oblique case, the last consulted only by the rival
  analysis. Sanskrit's and Kannada's passives are textbook facts.
* A construction's grouping of S is the alignment, in the sense of `Alignment`, of its pivot: the
  core roles that may bear its shared or omitted argument. Its bias comes from the property it asks
  of the pivot, control (`ProtoRoleFeature.volition`) for imperatives and indirect commands and a
  change of state for resultatives, and from which of the two proto-role clusters contains it; the
  book gives coordination and the Chukchi infinitive construction no such property.
* A causee's control is its proto-agent entailments, sentience where it keeps less control and
  volition beside it where it keeps more. A case's control is that of the role it typically
  marks, through the substrate's `ThetaRole.canonicalProfile`, which orders the accusative, the
  dative and the instrumental as the book's control hierarchy does.
* The Turkish marking rows are checked against `Turkish.ObjectMarking.accusative` rather than
  restated.

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

open Alignment ArgumentStructure Causation.Morphological

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

/-- An argument's prominence is its person, animacy and degree of definiteness, ordered
componentwise. -/
abbrev Prominence := Person.Class × Animacy × Definiteness

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
  definiteness : Option Definiteness
  /-- Whether the position takes the special marking always, sometimes or never. -/
  overtness : Overtness
  deriving DecidableEq

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
        row.parse? (p ++ "definiteness") [("definite", Definiteness.definite),
          ("indefiniteSpecific", .specific), ("nonSpecific", .nonSpecific)],
        ← row.parse? (p ++ "marked")
          [("marked", Overtness.obligatory), ("optional", .optional), ("unmarked", .excluded)]⟩
  else []

/-- The prominences a marking covers: every value of a scale it does not cite. -/
def Marking.cell (m : Marking) : Set Prominence :=
  {c | (∀ p ∈ m.person, c.1 = p) ∧ (∀ a ∈ m.animacy, c.2.1 = a) ∧ ∀ d ∈ m.definiteness, c.2.2 = d}

/-- Some prominence `m₁` covers lies below some prominence `m₂` covers. -/
def Marking.AtMost (m₁ m₂ : Marking) : Prop := ∃ x ∈ m₁.cell, ∃ y ∈ m₂.cell, x ≤ y

private theorem exists_le_of_option {γ : Type*} [Preorder γ] (g : γ) {o₁ o₂ : Option γ}
    (h : ∀ a ∈ o₁, ∀ b ∈ o₂, a ≤ b) :
    ∃ x y : γ, (∀ a ∈ o₁, x = a) ∧ (∀ b ∈ o₂, y = b) ∧ x ≤ y := by
  rcases o₁ with _ | a <;> rcases o₂ with _ | b
  exacts [⟨g, g, by simp⟩, ⟨b, b, by simp⟩, ⟨a, a, by simp⟩,
    ⟨a, b, by simp, by simp, h a rfl b rfl⟩]

theorem Marking.atMost_iff {m₁ m₂ : Marking} : m₁.AtMost m₂ ↔
    (∀ p₁ ∈ m₁.person, ∀ p₂ ∈ m₂.person, p₁ ≤ p₂) ∧
      (∀ a₁ ∈ m₁.animacy, ∀ a₂ ∈ m₂.animacy, a₁ ≤ a₂) ∧
        ∀ d₁ ∈ m₁.definiteness, ∀ d₂ ∈ m₂.definiteness, d₁ ≤ d₂ := by
  refine ⟨fun ⟨x, ⟨hp, ha, hd⟩, y, ⟨hp', ha', hd'⟩, h₁, h₂, h₃⟩ ↦
    ⟨fun p h q h' ↦ hp p h ▸ hp' q h' ▸ h₁, fun a h b h' ↦ ha a h ▸ ha' b h' ▸ h₂,
      fun d h e h' ↦ hd d h ▸ hd' e h' ▸ h₃⟩, fun ⟨hp, ha, hd⟩ ↦ ?_⟩
  obtain ⟨x₁, y₁, hx₁, hy₁, h₁⟩ := exists_le_of_option ⊥ hp
  obtain ⟨x₂, y₂, hx₂, hy₂, h₂⟩ := exists_le_of_option .inanimate ha
  obtain ⟨x₃, y₃, hx₃, hy₃, h₃⟩ := exists_le_of_option .nonSpecific hd
  exact ⟨(x₁, x₂, x₃), ⟨hx₁, hx₂, hx₃⟩, (y₁, y₂, y₃), ⟨hy₁, hy₂, hy₃⟩, h₁, h₂, h₃⟩

instance (m₁ m₂ : Marking) : Decidable (m₁.AtMost m₂) := decidable_of_iff' _ Marking.atMost_iff

/-- The markings of `rows` follow the natural information flow: a graded marking that fits the
prominence order, A's overtness falling and P's rising, each with its own cut-offs, takes every
row's value throughout the prominences the row covers. -/
def FollowsFlow (rows : List Datum) : Prop :=
  ∃ μ : ArgumentRole → Prominence → Overtness, FitsGraded μ ∧ ∀ ρ ∈ [ArgumentRole.A, .P],
    ∀ m ∈ rows.flatMap Marking.ofRow, m.role = ρ → ∀ c ∈ m.cell, μ ρ c = m.overtness

section FollowsFlow

variable {L : List Marking} {ρ : ArgumentRole}

theorem followsFlow_iff {rows : List Datum} : FollowsFlow rows ↔
    (∃ f : Prominence → Overtness, Antitone f ∧
      ∀ m ∈ rows.flatMap Marking.ofRow, m.role = .A → ∀ c ∈ m.cell, f c = m.overtness) ∧
    ∃ f : Prominence → Overtness, Monotone f ∧
      ∀ m ∈ rows.flatMap Marking.ofRow, m.role = .P → ∀ c ∈ m.cell, f c = m.overtness := by
  refine ⟨fun ⟨μ, ⟨hA, hP⟩, h⟩ ↦ ⟨⟨μ .A, hA, h .A (by simp)⟩, ⟨μ .P, hP, h .P (by simp)⟩⟩,
    fun ⟨⟨f, hf, hf'⟩, g, hg, hg'⟩ ↦ ⟨fun r ↦ if r = .A then f else g, ⟨hf, hg⟩, ?_⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hf', hg'⟩

theorem exists_monotone_iff :
    (∃ f : Prominence → Overtness, Monotone f ∧
      ∀ m ∈ L, m.role = ρ → ∀ c ∈ m.cell, f c = m.overtness) ↔
      ∀ m ∈ L, m.role = ρ → ∀ m' ∈ L, m'.role = ρ → m.AtMost m' → m.overtness ≤ m'.overtness := by
  have h := exists_monotone_forall_eq_iff (t := (L.filter (·.role = ρ)).toFinset)
    (s := Marking.cell) (k := Marking.overtness)
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_imp] at h
  exact h

theorem exists_antitone_iff :
    (∃ f : Prominence → Overtness, Antitone f ∧
      ∀ m ∈ L, m.role = ρ → ∀ c ∈ m.cell, f c = m.overtness) ↔
      ∀ m ∈ L, m.role = ρ → ∀ m' ∈ L, m'.role = ρ → m'.AtMost m → m.overtness ≤ m'.overtness := by
  have h := exists_antitone_forall_eq_iff (t := (L.filter (·.role = ρ)).toFinset)
    (s := Marking.cell) (k := Marking.overtness)
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_imp] at h
  exact h

end FollowsFlow

/-- A marking row is acceptable exactly when it and the acceptable rows of its language follow
the natural information flow, special P-marking rising with prominence and special A-marking
falling with it; the one row the book doubts, the Hindi human P without *ko* of (18), is the one
that departs ((7)–(27) of chapter 6). -/
theorem marking_rows : ∀ r ∈ Examples.all, r.feature? "construction" = some "marking" →
    (r.judgment = .acceptable ↔
      FollowsFlow (r :: acceptable.filter (·.language = r.language))) := by
  simp only [followsFlow_iff, exists_monotone_iff, exists_antitone_iff]
  decide

theorem marking_contrast : ∀ role : ArgumentRole, role = .A ∨ role = .P →
    ∃ r₁ ∈ acceptable, ∃ r₂ ∈ acceptable, r₁.language = r₂.language ∧
      ∃ m₁ ∈ Marking.ofRow r₁, ∃ m₂ ∈ Marking.ofRow r₂, m₁.role = role ∧ m₂.role = role ∧
        m₁.AtMost m₂ ∧ (role = .P → m₁.overtness < m₂.overtness) ∧
          (role = .A → m₂.overtness < m₁.overtness) := by
  decide

-- (13), (14) and (25): the Turkish rows mark P exactly on the degrees of definiteness the
-- fragment's accusative covers, the continuum cut at the specific indefinites.
theorem turkish_rows : ∀ r ∈ Examples.all, r.language = .turkish → ∀ m ∈ Marking.ofRow r,
    ∀ d ∈ m.definiteness, (m.overtness = .obligatory ↔ d ∈ Turkish.ObjectMarking.accusative) := by
  decide

/-! ### The causee hierarchy (§8.2) -/

/-- `causeePosition s` is the position of the same name in [keenan-comrie-1977]'s accessibility
hierarchy. -/
def causeePosition : CauseeSlot → Relativization.Position
  | .subject => .subject
  | .directObject => .directObject
  | .indirectObject => .indirectObject
  | .oblique => .oblique

/-- The causee hierarchy embedded in the accessibility hierarchy, which the book finds very similar
to it once the indirect object is included, without the two being necessarily identical
(p. 177). -/
def causeeEmbedding : CauseeSlot ↪o Relativization.Position :=
  OrderEmbedding.ofStrictMono causeePosition fun a b ↦ by revert a b; decide

theorem range_causeeEmbedding :
    Set.range causeeEmbedding = Set.Icc .oblique .subject := by
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

/-- The role a case typically marks, on the book's account of the control hierarchy: the
accusative a patient, the dative an experiencer, and the instrumental, as the case of passive
agents, an agent (p. 181). -/
def typicalRole : Case → Option ThetaRole
  | .acc => some .patient
  | .dat => some .experiencer
  | .inst => some .agent
  | _ => none

/-- The control a case typically marks, the proto-agent entailments of its typical role. -/
def caseControl (c : Case) : Finset ProtoRoleFeature :=
  EntailmentProfile.protoAgent ((typicalRole c).elim ∅ ThetaRole.canonicalProfile)

/-- The basic case of each position: the nominative of the subject, the accusative of the direct
object, the dative of the indirect object, and the instrumental of the oblique. -/
def basicCase : CauseeSlot → Case
  | .subject => .nom
  | .directObject => .acc
  | .indirectObject => .dat
  | .oblique => .inst

-- p. 181: the control hierarchy instrumental > dative > accusative is the causee hierarchy below
-- the subject "presented in reverse order".
theorem caseControl_basicCase_strictAntiOn :
    StrictAntiOn (caseControl ∘ basicCase) {s | s ≠ .subject} := by
  intro a ha b hb h; revert a b; decide

/-- A control row's configuration: the causee's entailments, sentience where it retains less
control and volition beside it where it retains more, and the case it takes. -/
structure Controlled where
  /-- The proto-role entailments of the causee. -/
  profile : EntailmentProfile
  /-- The causee's case. -/
  causeeCase : Case

/-- The configuration a control row records. -/
def Controlled.ofRow (row : Datum) : Option Controlled := do
  guard (row.feature? "construction" = some "control")
  return ⟨← row.parse? "control"
      [("less", ({.sentience} : EntailmentProfile)), ("more", {.volition, .sentience})],
    ← row.parse? "case" [("acc", Case.acc), ("dat", .dat), ("inst", .inst)]⟩

/-- Within a language the causee with more proto-agent entailments takes the case higher on the
control hierarchy, the one whose typical role has more, and some language offers the pair
((8)–(9), (23)–(28)). -/
theorem control_rows :
    (∀ r₁ ∈ Examples.all, ∀ c₁ ∈ Controlled.ofRow r₁,
      ∀ r₂ ∈ Examples.all.filter (·.language = r₁.language), ∀ c₂ ∈ Controlled.ofRow r₂,
        c₁.profile.protoAgent ⊂ c₂.profile.protoAgent →
          caseControl c₁.causeeCase ⊂ caseControl c₂.causeeCase) ∧
      ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all, r₁.language = r₂.language ∧
        ∃ c₁ ∈ Controlled.ofRow r₁, ∃ c₂ ∈ Controlled.ofRow r₂,
          c₁.profile.protoAgent ⊂ c₂.profile.protoAgent := by
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

/-- The constructions tested. -/
inductive Test
  | coordination | imperative | indirectCommand | resultative | infinitive
  deriving DecidableEq, Repr, Fintype

/-- The property a construction asks of its pivot, on the book's explanation: the addressee of an
imperative and the recipient of an indirect command must control the resulting situation, and a
resultative attributes a change of state; coordination and the Chukchi infinitive ask for
neither (§5.3, §5.4). -/
def Test.property : Test → Option ProtoRoleFeature
  | .imperative | .indirectCommand => some .volition
  | .resultative => some .changeOfState
  | .coordination | .infinitive => none

/-- A construction is biased toward the alignment identifying S with the transitive argument whose
prototype has its property: A, the agent of the prototypical transitive situation, for a
proto-agent property, and P, the patient, for a proto-patient one. -/
def Test.bias (t : Test) : Option AlignmentType :=
  t.property.map fun f ↦ if f ∈ ProtoRoleFeature.agentCluster then .accusative else .ergative

/-- A grouping row's configuration: the construction and the core roles that may bear its shared
or omitted argument. -/
structure Grouped where
  /-- The construction. -/
  test : Test
  /-- The core roles that may bear the shared or omitted argument. -/
  pivot : List ArgumentRole

/-- The construction's marking of the roles, whether each may be its pivot; its alignment is the
grouping the construction shows. -/
def Grouped.marking (g : Grouped) (r : ArgumentRole) : Bool := decide (r ∈ g.pivot)

/-- The configuration a grouping row records. -/
def Grouped.ofRow (row : Datum) : Option Grouped := do
  guard (row.feature? "construction" = some "grouping")
  return ⟨← row.parse? "test" [("coordination", Test.coordination), ("imperative", .imperative),
      ("indirectCommand", .indirectCommand), ("resultative", .resultative),
      ("infinitive", .infinitive)],
    ← row.parseAll? "pivot" [("S", ArgumentRole.S), ("A", .A), ("P", .P)]⟩

/-- Imperative addressee deletion follows its bias in every language, accusative even in Dyirbal,
and the resultative is ergative somewhere; but each bias is a tendency, crossed by the Dyirbal
indirect command and the English resultative (§5.4). -/
theorem bias_rows :
    (∀ row ∈ Examples.all, ∀ g ∈ Grouped.ofRow row, g.test = .imperative →
      ∃ a ∈ g.test.bias, a = .accusative ∧ a.Classifies g.marking) ∧
      (∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
        g.test = .resultative ∧ IsErgative g.marking) ∧
      ∀ t : Test, ∀ a ∈ t.bias, ∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
        g.test.bias = some a ∧ ¬ a.Classifies g.marking := by
  decide

-- §5.4: coordination is accusative in English, ergative in Dyirbal and neutral in Chukchi.
theorem coordination_rows : ∀ a ∈ [AlignmentType.accusative, .ergative, .neutral],
    ∃ row ∈ Examples.all, ∃ g ∈ Grouped.ofRow row,
      g.test = .coordination ∧ a.Classifies g.marking := by
  decide

-- §5.3: Chukchi coordination is neutral and its infinitive construction accusative.
theorem mixed_rows : ∃ r₁ ∈ Examples.all, ∃ r₂ ∈ Examples.all, r₁.language = r₂.language ∧
    ∃ g₁ ∈ Grouped.ofRow r₁, ∃ g₂ ∈ Grouped.ofRow r₂, ∃ a : AlignmentType,
      a.Classifies g₁.marking ∧ ¬ a.Classifies g₂.marking := by
  decide

/-- The cases a marking row gives the core roles of its clause: a role whose position takes the
special marking has a case of its own, the ergative of A or the accusative of P, and the rest
share the unmarked case of S (§6.1, §6.2). -/
def Marking.clause (row : Datum) (r : ArgumentRole) : Option ArgumentRole :=
  if ∃ m ∈ Marking.ofRow row, m.role = r ∧ m.overtness ≠ .excluded then some r else none

-- Chapter 6, (7)–(10): the split marking of Dyirbal gives its clauses four alignments, ergative
-- A with accusative P and nominative A with absolutive P beside the two familiar ones.
theorem dyirbal_clauses :
    IsErgative (Marking.clause Examples.ch6_ex7) ∧ IsAccusative (Marking.clause Examples.ch6_ex8) ∧
      IsTripartite (Marking.clause Examples.ch6_ex9) ∧
        IsNeutral (Marking.clause Examples.ch6_ex10) := by
  decide

-- Chapter 5, (16)–(19), and chapter 6, (7)–(8): syntax does not follow morphology. Dyirbal marks
-- the pronouns of *Ŋadʸa ŋinuna balgan* 'I hit you' accusatively and the nouns of (7)
-- ergatively, yet coordinates the same pronominal clause ergatively, S with P.
theorem dyirbal_marking_syntax :
    IsAccusative (Marking.clause Examples.ch6_ex8) ∧ IsErgative (Marking.clause Examples.ch6_ex7) ∧
      ∀ g ∈ Grouped.ofRow Examples.ch5_ex19, IsErgative g.marking := by
  decide

end Comrie1989
