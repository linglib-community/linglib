module

public import Linglib.Data.Examples.Everdell2023
public import Studies.Krejci2012
public import Linglib.Data.Examples.Readers

/-!
# Everdell (2023): Arguments and Adjuncts in O'dam, Chapter 5

This file formalizes the account of applicativization in O'dam (Southeastern Tepehuan) in
Chapter 5 of [everdell-2023]. The applicative suffixes *-dha* and *-tuda* add exactly one
syntactic argument, and the thematic role of that argument is predictable from the argument
structure of the base verb through the hierarchy (273): an agent is added to a base with a
single distinct argument; failing that, an entailed participant that is not a syntactic object
and is compatible with an animate referent is promoted to object; failing that, a beneficiary
is added, which makes benefaction the elsewhere function of the applicatives rather than
their core. A base with three arguments takes no applicative, since a verb of O'dam has at
most three: hypertransitivity is banned, so the ditransitives 'give' and 'ask' have no
applied form.

`Base.arguments` counts the base's arguments as the applicative counts them: the subject and
the objects co-referenced on the verb, plus the incorporated nominal of a denominal *-ta* verb
of creation, minus an object not maximally distinct from the subject in the sense of
[naess-2007], which is what unites the exceptional transitives of Table 5.2 (lexical middles,
verbs of ingestion, verbs of perception). Entailed participants that are not objects, whether
implicit objects or entailed locations, do not count. That is the chapter's argument that
locative expressions and instruments are adjuncts: a motion verb co-referencing only its
subject gains an agent like any intransitive, and an entailed location is promoted the way an
implicit object is.

`rows` are the chapter's verbs (Tables 5.1, 5.2, 5.6 and 5.7, the promotion cases of §5.2 and
§5.3, the ditransitives, the denominal verbs of creation and the suppletive paradigms of
§5.4), and `rows_role` derives each one's attested function, an applicative attaching only to
the alternant of a suppletive paradigm with the most arguments. `role_eq_beneficiary_iff` is
the chapter's two-part elsewhere condition and `role_eq_none_iff` the hypertransitivity ban.
`causativizability` places O'dam on the causativizability hierarchy of [krejci-2012], which
the chapter invokes to explain why ingestives and middles pattern with intransitives: the
applicatives reach unergatives but not simple transitives.

## Implementation notes

* Promotion is modelled by its precondition. The applied form entails that the promoted
  participant is animate, so only a participant compatible with an animate referent is
  promotable: implicit objects (buyers, hearers, the person something is hidden from) always
  are, entailed locations are or are not by the speakers' judgments (§5.3 against §5.4.1),
  and instruments never are, since a *-k1'n* 'with' phrase rejects an animate referent. The
  chapter's case that promotion adds animacy rather than the change of possession of the
  dative alternation ([beavers-nishida-2010]) or of Kinyarwanda applicatives stays in prose:
  the possession implicature runs from the promoted source to the subject with *baabu'*
  'take out from under' and is absent with *nui'ña'* 'push'.
* The agent-adding use is the causative-applicative syncretism of [shibatani-pardeshi-2002],
  which the chapter declines to read as two morphemes: one suffix adds an agent or an object
  depending on the base. Unlike the Kinyarwanda *-ish* of [jerro-2017], an O'dam applicative
  has one function with a given base; the two senses of *m11ya'* ('burn', 'ignite') are two
  bases.
* Verb classes are only those the chapter names; the Table 5.1 verbs it does not classify are
  `Class.plain`. The subtype of a beneficiary (deputative, recipient, basic) and the role of
  an entailed participant are recorded in the rows and play no part in the model.

## TODO

* *torkia'* 'bark' is the one base with two functions (agent as a verb of sound emission,
  promotion of the addressee as a verb of speaking), and *aga'* 'talk' and *jiiñkia'* 'yell'
  promote a hearer they do not entail, by analogy with the speaking class; the rows record
  only the sound-emission use of *torkia'*.
* The denominal *mar-ta'* 'have children' and *ak-cha'* 'make a river' take an applicative
  whose applied object is a co-agent or the diverted theme rather than a beneficiary; the
  model predicts of them only that no agent is added.

## References

* [everdell-2023]
* [naess-2007]
* [krejci-2012]
* [beavers-nishida-2010]
* [jerro-2017]
* [shibatani-pardeshi-2002]
-/

@[expose] public section

namespace Everdell2023


/-- The verb classes the chapter names; `plain` is any other verb. -/
inductive Class
  | unaccusative | unergative | motion | ingestion | perception | middle | denominal | plain
  deriving DecidableEq, Repr

/-- A lexical middle, verb of ingestion or verb of perception: the subject is not maximally
distinct from the object ([naess-2007]), so the applicative counts the two as one argument. -/
def Class.Nondistinct : Class → Prop
  | .ingestion | .perception | .middle => True
  | _ => False

instance : DecidablePred Class.Nondistinct := λ c => by
  cases c <;> unfold Class.Nondistinct <;> infer_instance

/-- A participant entailed by the base verb that is not one of its syntactic objects: an
implicit object that cannot be expressed in the base clause, an entailed location that must be
expressed as a locative phrase, or an entailed instrument. -/
inductive Participant
  | implicitObject
  | locative (animate : Bool)
  | instrument
  deriving DecidableEq, Repr

/-- Compatibility with an animate referent, the precondition of promotion. -/
def Participant.Animate : Participant → Prop
  | .implicitObject => True
  | .locative a => a = true
  | .instrument => False

instance : DecidablePred Participant.Animate := λ p => by
  cases p <;> unfold Participant.Animate <;> infer_instance

/-- The argument structure of a base verb as the applicative reads it. -/
structure Base where
  /-- The semantic class. -/
  verbClass : Class
  /-- The objects co-referenced on the verb. -/
  objects : ℕ
  /-- An entailed participant that is not a syntactic object. -/
  entailed : Option Participant
  deriving DecidableEq, Repr

/-- The thematic roles an applied argument can bear. -/
inductive Role
  | agent | promoted | beneficiary
  deriving DecidableEq, Repr

/-- (273): the roles in the order the applicative tries them, benefaction last. -/
def hierarchy : List Role := [.agent, .promoted, .beneficiary]

/-- A verb of O'dam has at most three syntactic arguments. -/
def maxArguments : ℕ := 3

namespace Base

variable (b : Base)

/-- Distinct syntactic arguments: the subject and the objects, an incorporated nominal counted
in, an object not distinct from the subject counted out. -/
def arguments : ℕ :=
  1 + (b.objects + (if b.verbClass = .denominal then 1 else 0)
    - if b.verbClass.Nondistinct then 1 else 0)

/-- The base entails a participant that promotion can make an animate object. -/
def Promotable : Prop := ∃ p ∈ b.entailed, p.Animate

instance : Decidable b.Promotable := by unfold Promotable; infer_instance

/-- A role is available when the applied form stays within `maxArguments` and the base has
what the role needs: a single distinct argument for a new agent, an agent already (two
arguments) and a promotable participant for promotion, an agent already for a beneficiary. -/
def Available : Role → Prop
  | .agent => b.arguments + 1 ≤ maxArguments ∧ b.arguments = 1
  | .promoted => b.arguments + 1 ≤ maxArguments ∧ 2 ≤ b.arguments ∧ b.Promotable
  | .beneficiary => b.arguments + 1 ≤ maxArguments ∧ 2 ≤ b.arguments

instance (r : Role) : Decidable (b.Available r) := by
  cases r <;> unfold Available <;> infer_instance

/-- The role of the applied argument: the first available role of the hierarchy, `none` when
the base takes no applicative. -/
def role : Option Role := hierarchy.find? (λ r => decide (b.Available r))

theorem one_le_arguments : 1 ≤ b.arguments := Nat.le_add_right 1 _

theorem role_eq :
    b.role = if b.arguments = 1 then some .agent else if b.arguments = 2 then
      if b.Promotable then some .promoted else some .beneficiary else none := by
  have h1 := b.one_le_arguments
  obtain h | h | h : b.arguments = 1 ∨ b.arguments = 2 ∨ 3 ≤ b.arguments := by omega
  · simp [role, hierarchy, Available, maxArguments, h]
  · by_cases hp : b.Promotable <;> simp [role, hierarchy, Available, maxArguments, h, hp]
  · simp [role, hierarchy, List.find?, Available, maxArguments, show ¬ b.arguments ≤ 2 by omega,
      show b.arguments ≠ 1 by omega, show b.arguments ≠ 2 by omega]

theorem role_eq_agent_iff : b.role = some .agent ↔ b.arguments = 1 := by
  rw [role_eq]; split_ifs <;> simp_all

theorem role_eq_promoted_iff : b.role = some .promoted ↔ b.arguments = 2 ∧ b.Promotable := by
  rw [role_eq]; split_ifs <;> simp_all

/-- A beneficiary is added only to a basic transitive base that is not promotable, the elsewhere
condition of §5.5. -/
theorem role_eq_beneficiary_iff :
    b.role = some .beneficiary ↔ b.arguments = 2 ∧ ¬ b.Promotable := by
  rw [role_eq]; split_ifs <;> simp_all

theorem role_eq_none_iff : b.role = none ↔ maxArguments ≤ b.arguments := by
  have h1 := b.one_le_arguments
  rw [role_eq]; split_ifs <;> simp_all [maxArguments]
  omega

-- Table 5.2
theorem role_eq_agent_of_nondistinct (h : b.verbClass.Nondistinct) (ho : b.objects = 1) :
    b.role = some .agent := by
  rw [role_eq_agent_iff]
  cases hc : b.verbClass <;> simp_all [arguments, Class.Nondistinct]

theorem role_eq_beneficiary_of_denominal (h : b.verbClass = .denominal) (ho : b.objects = 0)
    (he : b.entailed = none) : b.role = some .beneficiary := by
  rw [role_eq_beneficiary_iff]
  simp [arguments, Promotable, h, ho, he, Class.Nondistinct]

-- §5.4.1
theorem role_ne_promoted_of_instrument (h : b.entailed = some .instrument) :
    b.role ≠ some .promoted := by
  rw [Ne, role_eq_promoted_iff]
  simp [Promotable, h, Participant.Animate]

end Base

/-! ### The chapter's verbs -/

/-- A verb of the chapter with its attested applicative function; `paradigm` numbers the
suppletive paradigms of §5.4. -/
structure Row where
  base : Base
  observed : Option Role
  paradigm : Option ℕ
  deriving DecidableEq, Repr

def classTable : List (String × Class) :=
  [("unaccusative", .unaccusative), ("unergative", .unergative), ("motion", .motion),
    ("ingestion", .ingestion), ("perception", .perception), ("middle", .middle),
    ("denominal", .denominal), ("plain", .plain)]

def entailedTable : List (String × Option Participant) :=
  [("none", none), ("implicit", some .implicitObject), ("animateLocative", some (.locative true)),
    ("inanimateLocative", some (.locative false)), ("instrument", some .instrument)]

def roleTable : List (String × Option Role) :=
  [("agent", some .agent), ("promotion", some .promoted), ("beneficiary", some .beneficiary),
    ("blocked", none)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let verbClass ← ex.parse? "class" classTable
  let objects ← ex.nat? "objects"
  let entailed ← ex.parse? "entailed" entailedTable
  let observed ← ex.parse? "function" roleTable
  pure ⟨⟨verbClass, objects, entailed⟩, observed, ex.nat? "paradigm"⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by
  decide +kernel

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The most arguments any alternant of suppletive paradigm `p` has. -/
def paradigmMax (p : ℕ) : ℕ :=
  (rows.filterMap λ r => if r.paradigm = some p then some r.base.arguments else none).foldl max 0

/-- Within a suppletive paradigm the applicative attaches only to the alternant with the most
arguments (§5.4); a verb outside any paradigm hosts it freely. -/
def Row.Host (r : Row) : Prop := ∀ p ∈ r.paradigm, paradigmMax p ≤ r.base.arguments

instance : DecidablePred Row.Host := λ r => by unfold Row.Host; infer_instance

theorem rows_role : ∀ r ∈ rows, r.observed = if r.Host then r.base.role else none := by
  decide +kernel

/-! ### O'dam on the causativizability hierarchy -/

/-- The tier of the causativizability hierarchy of [krejci-2012] a base verb belongs to. -/
def Base.tier (b : Base) : Option Krejci2012.Tier :=
  match b.verbClass with
  | .unaccusative => some .unaccusative
  | .middle | .ingestion => some .middleIngestive
  | .unergative => some .unergative
  | .plain => if 1 ≤ b.objects then some .simpleTransitive else none
  | _ => none

/-- O'dam's row for Table 2.8 of [krejci-2012], read off the rows: the tiers whose verbs gain
an agent from the applicative. -/
def causativizability : Krejci2012.Causative where
  language := "O'dam"
  morpheme := "-dha, -tuda"
  reach := (rows.filterMap λ r => if r.observed = some .agent then r.base.tier else none).toFinset

theorem causativizability_type : causativizability.type = some .unergative := by
  decide +kernel

theorem causativizability_respectsHierarchy : causativizability.RespectsHierarchy := by
  decide +kernel

end Everdell2023
