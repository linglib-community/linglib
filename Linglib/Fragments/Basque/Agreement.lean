module

public import Linglib.Fragments.Basque.Pronouns
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Category.Verb.Tense

/-!
# Basque verbal agreement

The finite verb of Basque, in most clauses an auxiliary, agrees with the absolutive, the dative
and the ergative phrase of its clause. Each case has its own marker and its own place: the
absolutive marker stands before the root, the dative marker after it, and the ergative marker
after that, as in *d-i-da-zu* 'you have (sold) it to me'. The dative and ergative markers are
the same for the first and second persons and differ in the third, where the dative has *-o* and
*-e* and the ergative has nothing in the singular and *-te* in the plural. The familiar second
person *hi* is the one place where the verb marks gender, *-k* for a man and *-n* for a woman.

The absolutive slot treats the third person differently from the others. The first and second
persons have the prefixes *n-*, *h-*, *g-* and *z-* in every tense. A third person absolutive
has no prefix of its own: the slot holds *d-* in the present and *z-* in the past, whatever the
number, and the number of the absolutive phrase shows only in a separate plural marker. In a
past-tense transitive verb with a third person absolutive the slot is taken over by the ergative
phrase, which then has no suffix, so that *n-u-en* 'I had it' begins like *n-ind-u-zu-n* 'you
had me'. This is the pattern known as ergative displacement.

The pronoun *zu*, once a plural and now the ordinary way of addressing one person, still agrees
as a plural, and the newer plural *zuek* adds a further plural marker to the forms of *zu*.

## Main declarations

* `Basque.absolutive`, `Basque.dative`, `Basque.ergative`: the marker of each slot for each
  person and number, in the present tense.
* `Basque.thirdAbsolutive`: what fills the absolutive slot by tense when the absolutive phrase
  is third person.
* `Basque.displacedErgative`: the ergative markers of a past-tense verb with a third person
  absolutive.
* `Basque.HasPersonPrefix`: the absolutive slot has a prefix for the person and number.

## Main results

* `Basque.hasPersonPrefix_iff_isSAP`: the absolutive prefixes are those of the first and second
  persons.
* `Basque.dative_eq_ergative`: the dative and ergative markers of the first and second persons
  coincide.
* `Basque.displacedErgative_head`: a displaced ergative begins with what would fill the
  absolutive slot for its own person and number in the past.
* `Basque.allocutive_eq_ergative`: the familiar allocutive suffixes are the ergative suffixes of
  *hi*.

## Implementation notes

The cells are the bundles of `Syntax/Agreement/Bundle.lean`, so that a pronoun's features index
a table directly. The second person plural cell is that of *zu*, following the forms rather than
the meaning, and *zuek* has no cell of its own. The two cells of *hi* with a gender occur only in
the dative and ergative tables. The first and second person singular suffixes are given as they
stand at the end of the word; before another suffix they are *-da-*, *-a-* and *-na-*. Forms
with modal markers, where the third person filler is *l-*, are not covered.

## References

* [laka-1996]
-/

@[expose] public section

namespace Basque

open Agreement Morphology

/-- The cell of the familiar second person *hi* addressed to a person of the given gender. -/
def familiar (g : Gender) : Bundle := (Bundle.personNumber .second .singular).set .gender g

/-! ### The three slots -/

/-- The absolutive prefixes. Only the first and second persons have one. -/
def absolutive : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.pref "n"]), (.personNumber .second .singular, [.pref "h"]),
   (.personNumber .first .plural, [.pref "g"]), (.personNumber .second .plural, [.pref "z"])]

/-- The suffixes of the first and second persons, which the dative and ergative slots share. -/
def participantSuffixes : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.suff "t"]), (familiar .masculine, [.suff "k"]),
   (familiar .feminine, [.suff "n"]), (.personNumber .first .plural, [.suff "gu"]),
   (.personNumber .second .plural, [.suff "zu"])]

/-- The dative suffixes. -/
def dative : Paradigm (List Morph) :=
  participantSuffixes ++ [(.personNumber .third .singular, [.suff "o"]),
                          (.personNumber .third .plural, [.suff "e"])]

/-- The ergative suffixes. The third person singular has none. -/
def ergative : Paradigm (List Morph) :=
  participantSuffixes ++ [(.personNumber .third .singular, []),
                          (.personNumber .third .plural, [.suff "te"])]

/-- The element in the absolutive slot when the absolutive phrase is third person, *d-* in the
present and *z-* in the past. Basque has no future inflection. -/
def thirdAbsolutive : Tense → Option Morph
  | .present => some (.pref "d")
  | .past => some (.pref "z")
  | .future => none

/-- The ergative markers of a past-tense verb whose absolutive phrase is third person. They
stand in the absolutive slot, and the third person plural keeps its suffix. -/
def displacedErgative : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.pref "n"]), (.personNumber .second .singular, [.pref "h"]),
   (.personNumber .third .singular, [.pref "z"]),
   (.personNumber .first .plural, [.pref "g", .pref "en"]),
   (.personNumber .second .plural, [.pref "z", .pref "en"]),
   (.personNumber .third .plural, [.pref "z", .suff "te"])]

/-! ### Person in the absolutive slot -/

/-- The absolutive slot has a prefix for the cell. -/
def HasPersonPrefix (c : Bundle) : Prop := (absolutive.realize c).isSome

instance : DecidablePred HasPersonPrefix := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem hasPersonPrefix_iff_isSAP :
    ∀ c ∈ Bundle.personNumberCells, HasPersonPrefix c ↔ c.IsSAP := by
  decide

theorem hasPersonPrefix_phi_iff : ∀ p ∈ Pronouns.pronouns,
    HasPersonPrefix (HasPhi.phi p) ↔ p.person ≠ some .third := by
  decide

theorem dative_eq_ergative {c : Bundle} (h : c.IsSAP) : dative.realize c = ergative.realize c := by
  have h3 (n : Number) : (c == Bundle.personNumber .third n) = false := by
    rw [beq_eq_false_iff_ne]
    rintro rfl
    exact absurd h (by simp only [Bundle.IsSAP, Bundle.person_personNumber]; decide)
  simp [dative, ergative, Paradigm.realize, List.lookup_append, List.lookup_cons, h3]

theorem displacedErgative_head : ∀ c ∈ Bundle.personNumberCells,
    (displacedErgative.realize c).bind (·.head?) =
      ((absolutive.realize c).bind (·.head?)).or (thirdAbsolutive .past) := by
  decide

theorem allocutive_eq_ergative (g : Gender) :
    (Pronouns.allocutive .familiar g).map ([·]) = ergative.realize (familiar g) := by
  cases g <;> decide +kernel

end Basque
