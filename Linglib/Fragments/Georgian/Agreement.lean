module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Fragments.Georgian.Case

/-!
# Georgian case marking and verbal agreement

The Georgian verb agrees with its subject and its objects by means of two sets of affixes. Set A
has *v-* for the first person, nothing for the second and a suffix for the third, and adds *-t*
for a first or second person plural. Set B has *m-* for the first person singular, *gv-* for
the first person plural and *g-* for the second person, with *-t* for its plural. A third person
direct object has no Set B affix, while a third person indirect object has *h-* or *s-* before
certain consonants.

Which set marks which argument, and in which case the arguments stand, depends on the class of
the verb and on the series of its tense. The tenses fall into three series: the first contains
the present and the future, the second the aorist, the third the perfect. Transitive verbs, and
the medial verbs that pattern with them, such as *tamaš* 'play', have three patterns. In the
first series the subject is nominative with Set A and the direct object dative with Set B. In
the second the subject is ergative and the direct object nominative, with the same sets. In the
third the subject is dative with Set B and the direct object nominative with Set A, and an
indirect object loses its agreement and becomes the object of the postposition *-tvis* 'for'.
Intransitive verbs have the first of these patterns in every series, and indirect verbs, such
as *c'on* 'like', have the third in every series.

## Main declarations

* `Georgian.setA`, `Georgian.setB`: the two sets of agreement affixes.
* `Georgian.Series`, `Georgian.VerbClass`: the series of the tenses and the classes of verbs.
* `Georgian.Pattern`: the case and the agreement set of the subject and the objects, with the
  three patterns `Pattern.nominative`, `Pattern.ergative` and `Pattern.inverse`.
* `Georgian.pattern`: the pattern of each class in each series.

## Main results

* `Georgian.hasObjectPrefix_iff_isSAP`: the direct objects with a Set B prefix are the first and
  second persons.
* `Georgian.subject_affixes_present_eq_aorist`: the subject keeps its set of affixes from the
  first series to the second, whatever becomes of its case.
* `Georgian.subject_case_ne_iff`: the subject changes case from the first series to the second
  exactly in the transitive and medial classes.
* `Georgian.subject_affixes_eq_A_iff`, `Georgian.directObject_affixes_eq_A_iff`: Set A marks the
  subject unless it is dative, and the direct object exactly when the subject is dative.

## Implementation notes

The third person suffixes of Set A are those of the present; other tenses have *-a* or *-o* in
the singular and *-es* or *-nen* in the plural. The classes are the four of Harris, who numbers
them 1 (transitive), 2 (intransitive), 3 (medial) and 4 (indirect); Hewitt adds a small class of
stative verbs, which pattern with the intransitives.

## References

* [hewitt-1995]
* [harris-1981]
-/

@[expose] public section

namespace Georgian

open Agreement Morphology

/-! ### The agreement affixes -/

/-- The affixes of Set A, as they stand in the present. -/
def setA : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.pref "v"]), (.personNumber .second .singular, []),
   (.personNumber .third .singular, [.suff "s"]),
   (.personNumber .first .plural, [.pref "v", .suff "t"]),
   (.personNumber .second .plural, [.suff "t"]), (.personNumber .third .plural, [.suff "en"])]

/-- The affixes of Set B, as they mark a direct object. -/
def setB : Paradigm (List Morph) :=
  [(.personNumber .first .singular, [.pref "m"]), (.personNumber .second .singular, [.pref "g"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.pref "gv"]),
   (.personNumber .second .plural, [.pref "g", .suff "t"]), (.personNumber .third .plural, [])]

/-- The Set B prefix of a third person indirect object. It stands before *k*, *k'*, *g*, *q'*
and *p'*, becomes *s-* before *c*, *c'*, *j*, *č*, *č'*, *ǰ*, *t*, *t'* and *d*, and is dropped
before other consonants and before vowels. -/
def thirdIndirect : Morph := .pref "h"

/-- A direct object of the cell has a Set B prefix. -/
def HasObjectPrefix (c : Bundle) : Prop := ∃ ms ∈ setB.realize c, ms ≠ []

instance : DecidablePred HasObjectPrefix := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The direct objects with a Set B prefix are the first and second persons. -/
theorem hasObjectPrefix_iff_isSAP :
    ∀ c ∈ Bundle.personNumberCells, HasObjectPrefix c ↔ c.IsSAP := by
  decide

/-! ### Series and verb classes -/

/-- The three series of tenses. The first contains the present, the imperfect, the future and
the conditional, the second the aorist and the optative, the third the perfect and the
pluperfect. -/
inductive Series where
  | present
  | aorist
  | perfect
  deriving DecidableEq, Repr, Fintype

/-- The classes of verbs, by their case marking and agreement. -/
inductive VerbClass where
  /-- Transitive verbs, as *k'l* 'kill'. -/
  | transitive
  /-- Intransitive verbs, among them the passives, as *i-k'vl-eb* 'be killed'. -/
  | intransitive
  /-- Medial verbs, which usually have a subject alone and pattern with the transitives, as
  *tamaš* 'play'. -/
  | medial
  /-- Indirect verbs, whose experiencer is dative in every series, as *c'on* 'like'. -/
  | indirect
  deriving DecidableEq, Repr, Fintype

/-- The two sets of agreement affixes. -/
inductive AffixSet where
  | A
  | B
  deriving DecidableEq, Repr, Fintype

/-- The affixes of a set. -/
def AffixSet.paradigm : AffixSet → Paradigm (List Morph)
  | .A => setA
  | .B => setB

/-- The marking of an argument, its case and the set of affixes it agrees by, if any. -/
structure Marking where
  case : Case
  affixes : Option AffixSet
  deriving DecidableEq, Repr

/-- A pattern of case marking and agreement for the subject and the two objects. -/
structure Pattern where
  subject : Marking
  directObject : Marking
  indirectObject : Marking
  deriving DecidableEq, Repr

namespace Pattern

/-- The subject is nominative with Set A, and both objects are dative with Set B. -/
def nominative : Pattern := ⟨⟨.nom, some .A⟩, ⟨.dat, some .B⟩, ⟨.dat, some .B⟩⟩

/-- The subject is ergative with Set A, the direct object nominative and the indirect object
dative, both with Set B. -/
def ergative : Pattern := ⟨⟨.erg, some .A⟩, ⟨.nom, some .B⟩, ⟨.dat, some .B⟩⟩

/-- The subject is dative with Set B and the direct object nominative with Set A. The indirect
object is a genitive governed by the postposition *-tvis* 'for', without agreement. -/
def inverse : Pattern := ⟨⟨.dat, some .B⟩, ⟨.nom, some .A⟩, ⟨.gen, none⟩⟩

end Pattern

/-- The pattern of each class of verbs in each series. -/
def pattern : VerbClass → Series → Pattern
  | .transitive, .present | .medial, .present => .nominative
  | .transitive, .aorist | .medial, .aorist => .ergative
  | .transitive, .perfect | .medial, .perfect => .inverse
  | .intransitive, _ => .nominative
  | .indirect, _ => .inverse

/-- The subject keeps its set of affixes from the first series to the second, whatever becomes
of its case. -/
theorem subject_affixes_present_eq_aorist (v : VerbClass) :
    (pattern v .present).subject.affixes = (pattern v .aorist).subject.affixes := by
  cases v <;> rfl

/-- The subject changes case from the first series to the second exactly in the transitive and
medial classes. -/
theorem subject_case_ne_iff (v : VerbClass) :
    (pattern v .present).subject.case ≠ (pattern v .aorist).subject.case ↔
      v = .transitive ∨ v = .medial := by
  cases v <;> decide

theorem subject_affixes_eq_A_iff (v : VerbClass) (s : Series) :
    (pattern v s).subject.affixes = some .A ↔ (pattern v s).subject.case ≠ .dat := by
  cases v <;> cases s <;> decide

theorem directObject_affixes_eq_A_iff (v : VerbClass) (s : Series) :
    (pattern v s).directObject.affixes = some .A ↔ (pattern v s).subject.case = .dat := by
  cases v <;> cases s <;> decide

end Georgian
