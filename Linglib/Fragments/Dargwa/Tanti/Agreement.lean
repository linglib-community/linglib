module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Person.Class

/-!
# Tanti Dargwa agreement

This file defines the gender and person agreement of Tanti Dargwa as Sumbatova describes it.
Dargwa is among the few Nakh-Dagestanian languages with both. There are three genders,
masculine for men, feminine for women and neuter for animals and things, and the gender marker
a target shows distinguishes them only in the singular. In the plural it distinguishes humans
from non-humans, and humans again by whether they include the speaker or the addressee, which
is why Sumbatova counts three different plural genders. Gender agreement is controlled by the
absolutive argument, by the predicate in a copular clause with two absolutives, and in Tanti
a copula or essive in a transitive clause may agree with the ergative or dative instead.

Person agreement has three sets of markers and leaves the third person unmarked. In the clitic
and optative sets the second person singular stands against the first person and the second
person plural, the configuration Sumbatova calls the Dargic type after the literary Dargi
paradigm in Cysouw's typology. A transitive verb agrees in person with the speech-act
participant when only one of its arguments is one, and otherwise with the absolutive P. The
thematic suffix of a transitive verb is *-i* when A outranks P on the person hierarchy 1, 2 > 3
and *-u* otherwise, so it marks exactly the clauses in which the verb agrees with A.

## Main declarations

* `Dargwa.Tanti.Gender.Value`: the three controller genders, with the singular and plural markers
  `Value.sgMarker` and `Value.plMarker`.
* `Dargwa.Tanti.PersonSet`: the clitic, irrealis and optative sets of person markers.
* `Dargwa.Tanti.personController`, `Dargwa.Tanti.thematic`: the person agreement controller and the
  thematic suffix of a transitive clause.

## Main results

* `Dargwa.Tanti.Gender.Value.sgMarker_injective`, `Dargwa.Tanti.Gender.Value.plMarker_masc_eq_fem`:
  the singular markers distinguish the three genders; the plural ones do not.
* `Dargwa.Tanti.PersonSet.realize_eq_nil_iff`: in every set, a cell is unmarked exactly when it is
  not a speech-act participant's.
* `Dargwa.Tanti.isDargic_clitic`, `Dargwa.Tanti.isDargic_optative`,
  `Dargwa.Tanti.not_isDargic_irrealis`: the clitic and optative sets have the Dargic configuration,
  the irrealis set does not.
* `Dargwa.Tanti.thematic_eq_i_iff`: the thematic suffix is *-i* exactly when A controls person
  agreement.

## Implementation notes

* A transitive clause is a `Clause.Scenario` of the persons of A and P. The thematic suffix is
  read off its kind on the binary scale `Person.Class`, as Sumbatova states it; the
  controller is the two-hierarchy rule as she states it.
* The masculine marker ‹w› is dropped or realized *-j* in some positions. Some nouns for liquids
  and granular substances take plural agreement, and a few nouns contain a gender marker of
  their own, which follows the referent's or the possessor's gender.
* Tanti has no clusivity, so the paradigms range over `Agreement.Bundle.personNumberCells`.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

@[expose] public section

namespace Dargwa.Tanti

open Agreement Clause Morphology

/-! ### Gender -/

namespace Gender

/-- A controller gender is one of the three classes into which the nouns fall. -/
inductive Value where
  /-- Men. -/
  | masc
  /-- Women. -/
  | fem
  /-- Animals and inanimates. -/
  | neut
  deriving DecidableEq, Repr, Fintype

/-- Each gender bears the comparative label of the referents it is assigned to. -/
def Value.toLabel : Value → _root_.Gender
  | .masc => .masculine
  | .fem => .feminine
  | .neut => .neuter

/-- A gender marker is cited without its position, since a target takes it as a prefix, a suffix
or an infix. -/
inductive Marker where
  | w
  | r
  | b
  | d
  deriving DecidableEq, Repr, Fintype

/-- The segment of a marker. -/
def Marker.form : Marker → String
  | .w => "w"
  | .r => "r"
  | .b => "b"
  | .d => "d"

/-- A singular controller of each gender takes its own marker. -/
def Value.sgMarker : Value → Marker
  | .masc => .w
  | .fem => .r
  | .neut => .b

/-- A plural controller takes ‹d› when it is non-human or includes the speaker or the addressee,
and ‹b› when it is human and does not. -/
def Value.plMarker : Value → Person.Class → Marker
  | .neut, _ => .d
  | _, .participant => .d
  | _, .nonParticipant => .b

/-- The singular markers distinguish the three genders. -/
theorem Value.sgMarker_injective : Function.Injective Value.sgMarker := by decide

/-- The plural markers do not distinguish men from women. -/
theorem Value.plMarker_masc_eq_fem : Value.masc.plMarker = Value.fem.plMarker := by
  funext c; cases c <;> rfl

theorem Value.plMarker_eq_d_iff {g : Value} {c : Person.Class} :
    g.plMarker c = .d ↔ g = .neut ∨ c = .participant := by
  cases g <;> cases c <;> decide

end Gender

/-! ### Person markers -/

/-- The person markers fall into three sets. The clitic set appears in the present, preterite,
perfect, present resultative and propositive, the irrealis set in the past habitual, future and
conditional, and the optative set in the optative. -/
inductive PersonSet where
  | clitic
  | irrealis
  | optative
  deriving DecidableEq, Repr, Fintype

/-- Each set is a paradigm over the person–number cells. The irrealis first person plural
*-ʜaˁ* reduces to *-ʜe*, the second person *-t:* to *-t*, and the optative second person plural
*-a* also appears as *-a-ja*. -/
def PersonSet.paradigm : PersonSet → Paradigm (List Morph)
  | .clitic =>
    [(.personNumber .first .singular, [.encl "da"]),
     (.personNumber .second .singular, [.encl "de"]),
     (.personNumber .third .singular, []), (.personNumber .first .plural, [.encl "da"]),
     (.personNumber .second .plural, [.encl "da"]), (.personNumber .third .plural, [])]
  | .irrealis =>
    [(.personNumber .first .singular, [.suff "d"]), (.personNumber .second .singular, [.suff "t:"]),
     (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "ʜaˁ"]),
     (.personNumber .second .plural, [.suff "t:", .suff "a"]), (.personNumber .third .plural, [])]
  | .optative =>
    [(.personNumber .first .singular, [.suff "a"]), (.personNumber .second .singular, [.suff "e"]),
     (.personNumber .third .singular, []), (.personNumber .first .plural, [.suff "a"]),
     (.personNumber .second .plural, [.suff "a"]), (.personNumber .third .plural, [])]

/-- In every set, a cell is unmarked exactly when it is not a speech-act participant's. -/
theorem PersonSet.realize_eq_nil_iff :
    ∀ s : PersonSet, ∀ c ∈ Bundle.personNumberCells,
      s.paradigm.realize c = some [] ↔ ¬ c.IsSAP := by
  decide

/-- The past tense clitic bears no person. -/
def pastClitic : Morph := .encl "de"

/-- The second person singular clitic is the past tense clitic. -/
theorem clitic_second_singular :
    PersonSet.clitic.paradigm.realize (.personNumber .second .singular) = some [pastClitic] := rfl

/-- A paradigm has the Dargic configuration when two speech-act participant cells share a
marker exactly when both or neither is the second person singular. -/
def IsDargic (p : Paradigm (List Morph)) : Prop :=
  ∀ c ∈ Bundle.personNumberCells, ∀ c' ∈ Bundle.personNumberCells, c.IsSAP → c'.IsSAP →
    (p.realize c = p.realize c' ↔
      (c = .personNumber .second .singular ↔ c' = .personNumber .second .singular))

instance (p : Paradigm (List Morph)) : Decidable (IsDargic p) := by
  unfold IsDargic; infer_instance

theorem isDargic_clitic : IsDargic PersonSet.clitic.paradigm := by decide

theorem isDargic_optative : IsDargic PersonSet.optative.paradigm := by decide

/-- The irrealis set has a first person plural marker of its own. -/
theorem not_isDargic_irrealis : ¬ IsDargic PersonSet.irrealis.paradigm := by decide

/-! ### Transitive clauses -/

/-- The argument a transitive verb agrees with in person, by the hierarchies 1, 2 > 3 and
absolutive > ergative. It is A when A alone is a speech-act participant and the absolutive P
otherwise. -/
def personController (s : Scenario Person) : ArgumentRole :=
  if s.high.IsSAP ∧ ¬ s.low.IsSAP then .A else .P

/-- The thematic suffix of a transitive verb is *-i* when A is higher than P on the person
hierarchy 1, 2 > 3, and *-u* when the two are equal or P is higher. -/
def thematic (s : Scenario Person) : Morph :=
  if (s.map Person.toClass).kind = .downstream then .suff "i" else .suff "u"

/-- An intransitive verb takes the thematic suffix *-u* with a speech-act participant, and *-ar*
or *-an* otherwise. -/
def intransitiveThematic (p : Person) : List Morph :=
  if p.IsSAP then [.suff "u"] else [.suff "ar", .suff "an"]

/-- The thematic suffix is *-i* exactly when A controls person agreement. -/
theorem thematic_eq_i_iff (s : Scenario Person) :
    thematic s = .suff "i" ↔ personController s = .A := by
  simp only [thematic, personController, Person.kind_map_toClass_eq_downstream_iff]
  split_ifs <;> decide

/-- A transitive verb whose A and P are the given person–number cells takes the clitic of the
cell that controls it. -/
def transitiveClitic (a p : Person × Number) : Option (List Morph) :=
  let c := if personController ⟨a.1, p.1⟩ = .A then a else p
  PersonSet.clitic.paradigm.realize (.personNumber c.1 c.2)

/-- 'I caught you' takes *=de*, 'you caught me' *=da*, 'I caught him' *=da*, 'you caught him'
*=de* and 'Rasul caught you' *=de*, since the verb agrees with the absolutive when both
arguments are speech-act participants and with the participant when one is. -/
theorem transitiveClitic_caught :
    transitiveClitic (.first, .singular) (.second, .singular) = some [.encl "de"] ∧
    transitiveClitic (.second, .singular) (.first, .singular) = some [.encl "da"] ∧
    transitiveClitic (.first, .singular) (.third, .singular) = some [.encl "da"] ∧
    transitiveClitic (.second, .singular) (.third, .singular) = some [.encl "de"] ∧
    transitiveClitic (.third, .singular) (.second, .singular) = some [.encl "de"] := by
  decide

end Dargwa.Tanti
