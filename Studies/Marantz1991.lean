module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Fragments.HindiUrdu.Case
public import Linglib.Data.Examples.Marantz1991
public import Linglib.Data.Examples.Readers

/-!
# Marantz (1991): Case and Licensing

Marantz develops a theory of morphological case. Noun phrases are
licensed by projection and the requirement that clauses have subjects, and case is read off the
finished structure afterwards. A case affix takes the first case it is eligible for in a
disjunctive hierarchy: a case determined by a lexical head, then a dependent case, then the
unmarked case of its environment, then a default. The dependent cases are accusative and
ergative. The verb with its inflection assigns one to a position it governs when another
position it governs holds a distinct chain that no lexical head has marked, the accusative
downward to the object and the ergative upward to the subject.

Case goes to chains, not to positions. A subject that has moved from the object position is one
chain with its trace, so there is no second chain for a dependent case to be assigned against.
This one fact covers both what Burzio's generalization says about the accusative and what the
paper calls the ergative generalization, that a derived subject is never ergative. Whether the
subject position is thematic plays no part: a raised subject over a distinct object, as with
*strike*, leaves the object accusative. An unergative clause has an unfilled object position,
and languages differ in whether it counts as a position to assign the ergative against:
Georgian and Basque always count it, Hindi may, Inuktitut never does.

The split ergativity of Georgian follows. The inflection of the first series assigns
dependent case downward and that of the second upward, while the agreement on the inflection
finds its controller in the same way in both, taking the subject unless a lexical head has
marked it and the object otherwise.

## Main declarations

* `Clause`: a clause as the case rules see it, by what its subject and object positions hold;
  `Clause.chains` lists its chains.
* `Clause.subject`, `Clause.object`: the case of the two chains under given rules.
* `Setting`: the rules of an inflection, the visibility of unfilled positions and the names the
  language gives the cases; `georgian`, `hindi`, `basque`, `inuktitut`.
* `Clause.agr`: the position the agreement of the paper's (31) takes its features from.

## Implementation notes

The argument that **It arrived the man* fails for want of a subject and not for want of Case,
and the residue of Case theory that governs PRO, are not formalized. Default case is not
modelled apart from unmarked case. The rules of `Syntax/Case/Dependent.lean` count a noun
phrase as a competitor while it is caseless, where the paper asks only that no lexical head
has marked it; the two agree when the domains of a sentence are run from the lowest up, as
they are in `ecm`. The third series of Georgian is outside the paper.

## References

* [marantz-1991]
-/

@[expose] public section

namespace Marantz1991

open Case DependentCase

/-! ### Clauses and their chains -/

/-- What the object position governed by the verb and its inflection holds. -/
inductive ObjectPosition where
  /-- A chain distinct from the subject's, with any case a lexical head determines on it. -/
  | chain (lexicalCase : Option Case)
  /-- A link of the subject's chain, the subject having moved from here. -/
  | trace
  /-- Nothing, as in an unergative clause. -/
  | unfilled
  deriving DecidableEq, Repr

/-- A clause as the case rules see it. -/
structure Clause where
  /-- The subject position is thematic, so that an argument is projected into it. -/
  thematicSubject : Bool
  /-- The case a lexical head determines on the chain in subject position. -/
  subjectCase : Option Case
  /-- What the object position holds. -/
  object : ObjectPosition
  deriving DecidableEq, Repr

namespace Clause

/-- A transitive clause. -/
def transitive : Clause := ⟨true, none, .chain none⟩

/-- An unergative clause. -/
def unergative : Clause := ⟨true, none, .unfilled⟩

/-- An unaccusative or passive clause, whose subject has moved from the object position. -/
def unaccusative : Clause := ⟨false, none, .trace⟩

/-- A clause whose subject is derived from inside the verb phrase and bears a lexical case,
over an object, as with the dative-subject psychological verbs of Georgian. -/
def psych (c : Case) : Clause := ⟨false, some c, .chain none⟩

/-- A clause whose non-thematic subject position is filled by a chain distinct from the
object's, as in *Elmer struck her as being too stubborn*. -/
def raising : Clause := ⟨false, none, .chain none⟩

variable (c : Clause) (r : Rules) (v : Bool)

/-- The chains with a link in a position the verb and its inflection govern, highest first, each
given by the case a lexical head has valued on it, if any.
An unfilled object position is listed when the language sees it. -/
def chains : List (Option Case) :=
  c.subjectCase ::
    match c.object with
    | .chain l => [l]
    | .trace => []
    | .unfilled => if v then [none] else []

/-- The case of the subject's chain, with what valued it. -/
def subject : Option (Case × Mechanism) := ((r.assign id (c.chains v)).map (·.2.value?)).headD none

/-- The case of the object's chain, with what valued it, where there is one. -/
def object? : Option (Case × Mechanism) :=
  match c.object with
  | .chain _ => ((r.assign id (c.chains v)).map (·.2.value?)).getD 1 none
  | .trace | .unfilled => none

theorem subject_of_lexical {l : Case} (h : c.subjectCase = some l) :
    c.subject r v = some (l, .lexical) := by
  obtain ⟨t, s, o⟩ := c
  subst h
  rcases o with l' | _ | _
  · simp [subject, chains, Rules.assign_pair, Rules.elsewhere]
  · simp [subject, chains, Rules.assign_singleton, Rules.elsewhere]
  · cases v <;> simp [subject, chains, Rules.assign_pair, Rules.assign_singleton, Rules.elsewhere]

/-- The subject has dependent case exactly when no lexical head has marked it, the rules assign
a dependent case upward, and the object position holds a distinct unmarked chain or is unfilled
and seen. -/
theorem subject_dependent_iff :
    (c.subject r v).map (·.2) = some .dependent ↔
      c.subjectCase = none ∧ r.high.isSome ∧
        (c.object = .chain none ∨ c.object = .unfilled ∧ v = true) := by
  obtain ⟨t, _ | s, (_ | l') | _ | _⟩ := c <;> obtain ⟨_ | hi, lo, _ | un⟩ := r <;>
    cases v <;>
    simp [subject, chains, Rules.assign_pair, Rules.assign_singleton, Rules.elsewhere]

/-- The object has dependent case exactly when it is a distinct chain no lexical head has
marked, the subject's chain is unmarked too, and the rules assign a dependent case downward. -/
theorem object_dependent_iff :
    (c.object? r v).map (·.2) = some .dependent ↔
      c.subjectCase = none ∧ c.object = .chain none ∧ r.low.isSome := by
  obtain ⟨t, _ | s, (_ | l') | _ | _⟩ := c <;> obtain ⟨hi, _ | lo, _ | un⟩ := r <;>
    simp [object?, chains, Rules.assign_pair, Rules.elsewhere]

/-- The ergative generalization holds under any rules, since a subject moved from the object
position has no dependent case. -/
theorem ergative_generalization (h : c.object = .trace) :
    (c.subject r v).map (·.2) ≠ some .dependent := fun hd ↦ by
  simpa [h] using ((c.subject_dependent_iff r v).1 hd).2.2

/-- Burzio's generalization does not hold of case, since the object of a clause with a
non-thematic subject position is accusative when the subject's chain is distinct from it. -/
theorem not_burzio :
    raising.thematicSubject = false ∧
      raising.object? (.ofAlignment .accusative) v = some (.acc, .dependent) := by
  cases v <;> decide

end Clause

/-! ### Settings of a language -/

/-- Whether a language sees an unfilled object position as a position to assign dependent case
against. -/
inductive Visibility where
  | always
  | optionally
  | never
  deriving DecidableEq, Repr

/-- The ways a language may treat the unfilled position of a given clause. -/
def Visibility.settings : Visibility → Finset Bool
  | .always => {true}
  | .optionally => {true, false}
  | .never => {false}

/-- A setting is what decides the case of the chains of a clause, namely the rules of its
inflection, the visibility of unfilled positions, and the names the language gives the cases. -/
structure Setting where
  rules : Rules
  unfilled : Visibility
  spellOut : Case → Case := id

namespace Setting

variable (g : Setting) (c : Clause)

/-- The cases the subject may have. -/
def subjectCases : Finset (Option Case) :=
  g.unfilled.settings.image fun v ↦ (c.subject g.rules v).map (g.spellOut ·.1)

/-- The cases the object may have. -/
def objectCases : Finset (Option Case) :=
  g.unfilled.settings.image fun v ↦ (c.object? g.rules v).map (g.spellOut ·.1)

end Setting

/-- The direction in which the inflection of a Georgian series assigns dependent case, downward
in the first series and upward in the second. The paper does not treat the third series, which
is given the value of the first. -/
def alignment : Georgian.Series → Alignment.AlignmentType
  | .aorist => .ergative
  | .present | .perfect => .accusative

/-- Georgian always sees an unfilled position. Its dative is what the accusative has fallen
together with, and its nominative is the unmarked case under either direction. -/
def georgian (s : Georgian.Series) : Setting where
  rules := .ofAlignment (alignment s)
  unfilled := .always
  spellOut
    | .acc => .dat
    | .abs => .nom
    | c => c

/-- Hindi sees an unfilled position optionally, and its unmarked case is the nominative. -/
def hindi (a : Aspect.Perfectivity) : Setting where
  rules := .ofAlignment (HindiUrdu.alignment a)
  unfilled := .optionally
  spellOut
    | .abs => .nom
    | c => c

/-- Basque assigns the ergative in every tense and always sees an unfilled position. -/
def basque : Setting := ⟨.ofAlignment .ergative, .always, id⟩

/-- Inuktitut assigns the ergative and never sees an unfilled position. -/
def inuktitut : Setting := ⟨.ofAlignment .ergative, .never, id⟩

theorem unergative_subjectCases :
    basque.subjectCases .unergative = {some .erg} ∧
    (hindi .perfective).subjectCases .unergative = {some .erg, some .nom} ∧
    inuktitut.subjectCases .unergative = {some .abs} := by
  decide

/-! ### The examples -/

/-- The setting of an example, by its language and the inflection the paper notes. -/
def setting? (e : Datum) : Option Setting :=
  [(("nucl1302", some "I"), georgian .present), (("nucl1302", some "II"), georgian .aorist),
    (("hind1269", some "perfect"), hindi .perfective), (("basq1248", none), basque)].lookup
    (e.language, e.feature? "inflection")

/-- The clause of an example. -/
def clause? (e : Datum) : Option Clause :=
  e.parse? "clause" [("transitive", .transitive), ("unergative", .unergative),
    ("unaccusative", .unaccusative), ("psych", .psych .dat)]

/-- The case an example shows on its subject or object. -/
def case? (e : Datum) (key : String) : Option Case :=
  e.parse? key [("NOM", .nom), ("ERG", .erg), ("DAT", .dat), ("ABS", .abs)]

/-- An example is acceptable exactly when the case of its subject is one the setting of its
language gives the subject of its clause. This covers the ergative on Georgian and Basque
unergatives, its optionality in Hindi, and its absence from unaccusatives in all three. -/
theorem subject_rows : ∀ e ∈ Examples.all,
    ∃ g ∈ setting? e, ∃ c ∈ clause? e, ∃ s ∈ case? e "subject",
      (e.judgment = .acceptable ↔ some s ∈ g.subjectCases c) := by
  decide +kernel

/-- The case of the object of an example is the one its setting gives. -/
theorem object_rows : ∀ e ∈ Examples.all, ∀ o ∈ case? e "object",
    ∃ g ∈ setting? e, ∃ c ∈ clause? e, g.objectCases c = {some o} := by
  decide +kernel

/-! ### Georgian -/

/-- The clause of each Georgian verb class. The intransitives have derived subjects, the
medials are unergative, and the indirect verbs have a derived dative subject over an object. -/
def clause : Georgian.VerbClass → Clause
  | .transitive => .transitive
  | .intransitive => .unaccusative
  | .medial => .unergative
  | .indirect => .psych .dat

/-- The two series the paper treats. -/
def series : List Georgian.Series := [.present, .aorist]

/-- The rules derive the subject case of the Fragment for every class in both series. -/
theorem georgian_subject_eq_pattern : ∀ v : Georgian.VerbClass, ∀ s ∈ series,
    (georgian s).subjectCases (clause v) = {some (Georgian.pattern v s).subject.case.label} := by
  decide +kernel

/-- The rules derive the object case of the Fragment for the two classes with an object. -/
theorem georgian_object_eq_pattern : ∀ v ∈ [Georgian.VerbClass.transitive, .indirect],
    ∀ s ∈ series,
      (georgian s).objectCases (clause v) =
        {some (Georgian.pattern v s).directObject.case.label} := by
  decide +kernel

/-! ### Agreement across the split -/

/-- The positions the verb and its inflection govern. -/
inductive Position where
  | subject
  | object
  deriving DecidableEq, Repr

/-- The position the agreement of the paper's (31) takes its features from, or `none` for the
default third person singular. Dependent agreement upward and unmarked agreement both pass over
a chain a lexical head has marked, so the agreement goes to the subject unless it is so marked,
and then to the object. The direction of dependent case plays no part. -/
def Clause.agr (c : Clause) : Option Position :=
  if c.subjectCase = none then some .subject
  else if c.object = .chain none then some .object
  else none

/-- Set A agreement marks the argument the agreement of (31) picks in both series. -/
theorem georgian_agr : ∀ v : Georgian.VerbClass, ∀ s ∈ series,
    ((Georgian.pattern v s).subject.affixes = some .A ↔ (clause v).agr = some .subject) ∧
    ((Georgian.pattern v s).directObject.affixes = some .A ↔
      (clause v).agr = some .object) := by
  decide

/-! ### Exceptional case marking -/

/-- The noun phrases of *I consider him to have discovered her*. -/
inductive ECMArgument where
  | matrixSubject
  | embeddedSubject
  | embeddedObject
  deriving DecidableEq, Repr

/-- The embedded subject is accusative against the matrix subject and the embedded object
against the embedded subject, so an accusative does not depend on a nominative having been
assigned in its clause. -/
theorem ecm :
    let r := Rules.ofAlignment .accusative
    ((r.unmarkedPass (fun _ ↦ true) <|
      r.dependentPass (fun x ↦ x ≠ .embeddedObject) <|
      r.dependentPass (fun x ↦ x ≠ .matrixSubject) <|
      lexicalValuation (fun _ ↦ none)
        [ECMArgument.matrixSubject, .embeddedSubject, .embeddedObject]).map
          (·.2.value?.map (·.1))) =
      [some .nom, some .acc, some .acc] := by
  decide

end Marantz1991
