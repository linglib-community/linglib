module

public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic

/-!
# German conjugation

This file defines the stem of a German verb, the forms its conjugation is built from, and the
rules that build them. A verb is weak or strong. A weak verb forms its past with *-te* and its past
participle with *-t* on its root, so that all its forms follow from the infinitive; a strong verb
changes the vowel of its root, and its forms have to be learnt. A root in *-d* or *-t*, or in *-m*
or *-n* after a consonant other than *l* or *r*, puts a linking *-e-* before these endings, as in
*arbeitet* and *zeichnete*. The past participle has the prefix *ge-* when the verb is stressed on
its first syllable, and so lacks it in the verbs in *-ieren* and in the verbs with an inseparable
prefix such as *be-*, *ver-* or *ent-*: *gratuliert*, *bezahlt*.

A separable verb conjugates like the simple verb it is formed from. Its particle stands at the end
of a main clause, *ruft … an*, and is joined to the non-finite forms, with the *ge-* of the simple
verb and the *zu* of the infinitive after it: *angerufen*, *anzurufen*. The present participle is
the infinitive with *-d*, *kaufend* and *ankommend*, in all but the irregular verbs. The present
tense has the
endings *-e*, *-st*, *-t*, *-en*, *-t* and *-en* in weak and strong verbs alike. The rules and the
examples are Durrell's.

## Main definitions

* `German.Conjugation.Stem`: the infinitive, third person singular present and past, and past
  and present participles of a verb.
* `German.Conjugation.weak`, `German.Conjugation.strong`: the stem of a weak verb from its
  infinitive, and of a strong verb from its principal parts.
* `German.Conjugation.Stem.inseparable`, `German.Conjugation.Stem.separable`: the stem of a verb
  with an inseparable prefix or a separable particle.
* `German.Conjugation.weakPresent`: the present tense of a weak verb.

## Implementation notes

The rules read the spelling. A root in *-ier* is taken to be the suffix of the verbs in *-ieren*,
and an *h* after a vowel, as in *lohnen*, marks vowel length and is not a consonant. Irregular
weak verbs, the vowel changes of strong verbs in the present and the verbs stressed off their first
syllable for other reasons are not covered: their forms are given as those of a strong verb.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German.Conjugation

/-- The vowel letters. -/
def IsVowel (c : Char) : Prop := c ∈ ['a', 'e', 'i', 'o', 'u', 'ä', 'ö', 'ü', 'y']

instance : DecidablePred IsVowel := fun c ↦ inferInstanceAs (Decidable (c ∈ _))

/-- `root inf` is the root of the infinitive `inf`: less *-n* after *-el* and *-er*, less *-en*
otherwise. -/
def root (inf : String) : String :=
  match inf.toList.reverse with
  | 'n' :: 'l' :: 'e' :: r => String.ofList ('l' :: 'e' :: r).reverse
  | 'n' :: 'r' :: 'e' :: r => String.ofList ('r' :: 'e' :: r).reverse
  | 'n' :: 'e' :: r => String.ofList r.reverse
  | _ => inf

/-- `linking r` is the *-e-* a root in *-d* or *-t*, or in *-m* or *-n* after a consonant other
than *l* or *r*, puts before the endings *-st*, *-t* and *-te*, and is empty otherwise. -/
def linking (r : String) : String :=
  match r.toList.reverse with
  | 'd' :: _ | 't' :: _ => "e"
  | 'm' :: 'h' :: v :: _ | 'n' :: 'h' :: v :: _ => if IsVowel v then "" else "e"
  | 'm' :: c :: _ | 'n' :: c :: _ => if IsVowel c ∨ c = 'l' ∨ c = 'r' then "" else "e"
  | _ => ""

/-- `IsIer r` holds of a root in *-ier*, the suffix of the verbs in *-ieren*. -/
def IsIer (r : String) : Prop := ['i', 'e', 'r'] <:+ r.toList

instance (r : String) : Decidable (IsIer r) := inferInstanceAs (Decidable (_ <:+ _))

/-- The stem of a verb is its infinitive, its third person singular present and past, its past
participle without a leading *ge-*, with whether the participle takes one, and its present
participle. -/
structure Stem where
  /-- The infinitive. -/
  infinitive : String
  /-- The third person singular present. -/
  present : String
  /-- The first and third person singular past. -/
  past : String
  /-- The past participle without a leading *ge-*. -/
  participle : String
  /-- The past participle takes a leading *ge-*, as that of a simple verb stressed on its first
  syllable does. -/
  prefixGe : Bool := true
  /-- The present participle, the infinitive with *-d* unless the verb is irregular there, as
  *kaufend*, *wandernd* and *singend*. -/
  presentParticiple : String := infinitive ++ "d"
  deriving DecidableEq, Repr

/-- `s.pastParticiple` is the past participle. -/
def Stem.pastParticiple (s : Stem) : String :=
  if s.prefixGe then "ge" ++ s.participle else s.participle

/-- `s.zuInfinitive` is the infinitive with *zu*. -/
def Stem.zuInfinitive (s : Stem) : String := "zu " ++ s.infinitive

/-- `weak inf` is the stem of the weak verb with the infinitive `inf`: the root with the endings
*-t*, *-te* and *-t*, after the linking *-e-* where the root takes one, and stressed on its first
syllable unless it is a verb in *-ieren*. -/
def weak (inf : String) : Stem :=
  let r := root inf ++ linking (root inf)
  { infinitive := inf, present := r ++ "t", past := r ++ "te", participle := r ++ "t",
    prefixGe := !decide (IsIer (root inf)) }

/-- `strong inf present past pp` is the stem of the strong verb with those principal parts, the
past participle `pp` given with its *ge-*. -/
def strong (inf present past pp : String) : Stem :=
  { infinitive := inf, present, past,
    participle := match pp.toList with
      | 'g' :: 'e' :: r => String.ofList r
      | _ => pp }

/-- `s.inseparable pfx` is the stem of the verb formed from `s` with the inseparable prefix `pfx`,
which is joined to every form and, taking the stress off the first syllable, leaves the past
participle without *ge-*. -/
def Stem.inseparable (s : Stem) (pfx : String) : Stem :=
  { infinitive := pfx ++ s.infinitive, present := pfx ++ s.present, past := pfx ++ s.past,
    participle := pfx ++ s.participle, prefixGe := false }

/-- `s.separable prt` is the stem of the verb formed from `s` with the separable particle `prt`.
The particle follows the finite forms, as at the end of a main clause, and precedes the
non-finite ones, where the *ge-* of `s` stays after it. -/
def Stem.separable (s : Stem) (prt : String) : Stem :=
  { infinitive := prt ++ s.infinitive, present := s.present ++ " " ++ prt,
    past := s.past ++ " " ++ prt, participle := prt ++ s.pastParticiple, prefixGe := false }

/-- `s.separableZuInfinitive prt` is the infinitive with *zu* of the verb formed from `s` with the
separable particle `prt`, *zu* standing between the two. -/
def Stem.separableZuInfinitive (s : Stem) (prt : String) : String := prt ++ "zu" ++ s.infinitive

/-- `weakPresent inf` gives the present tense of the weak verb with the infinitive `inf`: the root
with *-e*, *-st*, *-t*, *-t* in the singular and the second person plural, after the linking *-e-*
before *-st* and *-t*, and the infinitive in the first and third person plural. -/
def weakPresent (inf : String) : Person × Number → Option String
  | (.first, .singular) => some (root inf ++ "e")
  | (.second, .singular) => some (root inf ++ linking (root inf) ++ "st")
  | (.third, .singular) | (.second, .plural) => some (root inf ++ linking (root inf) ++ "t")
  | (.first, .plural) | (.third, .plural) => some inf
  | _ => none

/-! ### Examples -/

/-- *kaufen* 'buy' and *arbeiten* 'work' are weak, the latter with the linking *-e-*, and
*gratulieren* 'congratulate' has no *ge-*. -/
example :
    (weak "kaufen").past = "kaufte" ∧ (weak "kaufen").pastParticiple = "gekauft" ∧
      (weak "arbeiten").present = "arbeitet" ∧ (weak "arbeiten").past = "arbeitete" ∧
      (weak "atmen").pastParticiple = "geatmet" ∧ (weak "lernen").present = "lernt" ∧
      (weak "gratulieren").pastParticiple = "gratuliert" ∧
      (weak "kaufen").presentParticiple = "kaufend" ∧
      (weak "wandern").presentParticiple = "wandernd" := by
  decide

/-- The separable *ankommen* 'arrive' conjugates like *kommen*: *kommt an*, *ankommend*,
*angekommen*, *anzukommen*; *einstudieren* 'rehearse' keeps the missing *ge-* of *studieren*; the
inseparable *verstehen* 'understand' has no *ge-*. -/
example :
    let kommen := strong "kommen" "kommt" "kam" "gekommen"
    (kommen.separable "an").present = "kommt an" ∧
      (kommen.separable "an").presentParticiple = "ankommend" ∧
      (kommen.separable "an").pastParticiple = "angekommen" ∧
      kommen.separableZuInfinitive "an" = "anzukommen" ∧
      ((weak "studieren").separable "ein").pastParticiple = "einstudiert" ∧
      ((strong "stehen" "steht" "stand" "gestanden").inseparable "ver").pastParticiple =
        "verstanden" := by
  decide

end German.Conjugation
