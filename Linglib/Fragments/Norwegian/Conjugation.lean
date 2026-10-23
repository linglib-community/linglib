module

public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Norwegian conjugation

This file defines the stem of a Norwegian verb and builds it from the infinitive by the weak
classes of Faarlund, Lie and Vannebo's reference grammar, in either written standard. A stem is
the infinitive, the present, the preterite and the past participle. The classes differ in the
preterite and the participle, and the grammar draws the line between them there. A weak verb of
the first class, the largest and the productive one, has one form for both: in Bokmål *-et* on
the root, *kaste*, *kaster*, *kastet*, *kastet*, with *-a* as a rarer written variant, and in
Nynorsk *-a*, with the present in *-ar*, *kaste*, *kastar*, *kasta*, *kasta*. A weak verb of the
second class has a dental in both, and the dental of the participle is that of the preterite,
in both standards alike: *-te* and *-t* after most stems, *reiste*, *reist*, *-de* and *-d*
after a stem in a voiced *-d*, *-g* or *-v* or in the diphthongs *-ei* and *-øy*, *levde*,
*levd*, and *-dde* and *-dd* after a stem in a single stressed vowel, *rodde*, *rodd*. The
present of a second-class verb, and of a Bokmål first-class verb, is the infinitive with *-r*:
*-er* on the root of an infinitive in *-e*, *-r* on a stem in a stressed vowel. A double
consonant at the end of the stem is written single before the dental endings, *kjenne*,
*kjente*, *bygge*, *bygde*. A strong verb, or a weak verb with a vowel change such as *sette*,
*satte*, *satt*, is given by its four forms.

## Main definitions

* `Norwegian.Standard`: the written standards, Bokmål and Nynorsk.
* `Norwegian.Conjugation.Stem`: the infinitive, present, preterite and past participle.
* `Norwegian.Conjugation.weak1`, `dental`, `weak2a`, `weak2b`, `weak2c`: the stem of a weak
  verb of each class, from its infinitive, the first class by standard.

## Main results

* `Norwegian.Conjugation.weak1_preterite_eq_participle`, `dental_preterite`,
  `weak2c_preterite`: the first class has one form for the preterite and the participle, and the
  second class the participle with *-e*.
* `Norwegian.Conjugation.weak1_present`, `dental_present`: the present is *-er* on the root.

## Implementation notes

The rules read the spelling. The *-a* variant of the Bokmål first class, the Nynorsk side forms
of the second class with *-t* in the participle, the Nynorsk fourth subclass with a bare
present and a vowel change, *telje*, *tel*, *talde*, *talt*, and the agreement of a Nynorsk
participle after *vere* and *verte* are not covered. A verb whose stressed vowel is *e*, as
*kle*, is a second-class verb in *-dde* by `weak2c`, which does not take the final *-e* for an
infinitive ending.

## References

* [faarlund-lie-vannebo-1997]
-/

@[expose] public section

namespace Norwegian

/-- The written standards of Norwegian. -/
inductive Standard where
  | bokmaal
  | nynorsk
  deriving DecidableEq, Repr, Fintype

namespace Conjugation

/-- The stem of a verb is its infinitive, its present, its preterite and its past participle. -/
structure Stem where
  /-- The infinitive. -/
  infinitive : String
  /-- The present. -/
  present : String
  /-- The preterite. -/
  preterite : String
  /-- The past participle. -/
  participle : String
  deriving DecidableEq, Repr

/-- `root inf` is the root of the infinitive `inf`, the infinitive less a final *-e*. -/
def root (inf : String) : String :=
  match inf.toList.reverse with
  | 'e' :: r => String.ofList r.reverse
  | _ => inf

@[simp] theorem root_append_e (s : String) : root (s ++ "e") = s := by simp [root]

/-- `dentalStem inf` is the root of `inf` with a final double consonant written single, the
stem the dental endings of the second class attach to, *kjenn* to *kjen*. -/
def dentalStem (inf : String) : String :=
  match (root inf).toList.reverse with
  | c :: c' :: r => if c = c' then String.ofList (c :: r).reverse else root inf
  | _ => root inf

/-- `weak1 s inf` is the stem of a weak verb of the first class in the standard `s`, with one
form for the preterite and the participle: in Bokmål *-et* on the root, *kaste*, *kaster*,
*kastet*, *kastet*, in Nynorsk *-a*, with the present in *-ar*, *kaste*, *kastar*, *kasta*,
*kasta*. -/
def weak1 : Standard → String → Stem
  | .bokmaal, inf =>
    { infinitive := inf, present := inf ++ "r", preterite := root inf ++ "et",
      participle := root inf ++ "et" }
  | .nynorsk, inf =>
    { infinitive := inf, present := root inf ++ "ar", preterite := root inf ++ "a",
      participle := root inf ++ "a" }

/-- `dental d inf` is the stem of a weak verb of the second class with the dental `d`, the
preterite in `d` with *-e* and the participle in `d`, on the stem written with a single final
consonant. -/
def dental (d inf : String) : Stem :=
  { infinitive := inf, present := inf ++ "r", preterite := dentalStem inf ++ d ++ "e",
    participle := dentalStem inf ++ d }

/-- `weak2a inf` is the stem of a weak verb of the second class with the preterite in *-te*
and the participle in *-t*, as *reise*, *reiser*, *reiste*, *reist*. -/
abbrev weak2a : String → Stem := dental "t"

/-- `weak2b inf` is the stem of a weak verb of the second class with the preterite in *-de*
and the participle in *-d*, as *leve*, *lever*, *levde*, *levd*. -/
abbrev weak2b : String → Stem := dental "d"

/-- `weak2c inf` is the stem of a weak verb of the second class whose stem is the infinitive,
ending in a single stressed vowel, with *-dde* and *-dd*, as *ro*, *ror*, *rodde*, *rodd*. -/
def weak2c (inf : String) : Stem :=
  { infinitive := inf, present := inf ++ "r", preterite := inf ++ "dde",
    participle := inf ++ "dd" }

/-! ### The forms across the classes -/

/-- The verbs of the first class have the same form in the preterite and the participle, in
both standards. -/
theorem weak1_preterite_eq_participle (s : Standard) (inf : String) :
    (weak1 s inf).preterite = (weak1 s inf).participle := by
  cases s <;> rfl

/-- In the second class the dental of the participle is that of the preterite. -/
theorem dental_preterite (d inf : String) :
    (dental d inf).preterite = (dental d inf).participle ++ "e" := rfl

theorem weak2c_preterite (inf : String) :
    (weak2c inf).preterite = (weak2c inf).participle ++ "e" := by
  rw [weak2c, String.append_assoc]; rfl

/-- The present of a Bokmål first-class verb is *-er* on its root. -/
theorem weak1_present (s : String) : (weak1 .bokmaal (s ++ "e")).present = s ++ "er" := by
  rw [weak1, String.append_assoc]; rfl

/-- The present of a second-class verb with an infinitive in *-e* is *-er* on its root. -/
theorem dental_present (d s : String) : (dental d (s ++ "e")).present = s ++ "er" := by
  rw [dental, String.append_assoc]; rfl

/-- The double consonant is written single before the dental endings, *kjenne*, *kjente*,
*kjent* and *bygge*, *bygde*, *bygd*. -/
example :
    (weak2a "kjenne").preterite = "kjente" ∧ (weak2a "kjenne").participle = "kjent" ∧
      (weak2b "bygge").preterite = "bygde" ∧ (weak2b "bygge").participle = "bygd" := by
  decide

end Conjugation

end Norwegian
