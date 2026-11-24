module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Jarawara possessed nouns

This file records the genders of Jarawara (Arawan, Brazil), its possessors, and its possessed
nouns, after Dixon.

Jarawara has two genders, masculine and feminine, the feminine being unmarked. About 175 nouns,
among them body parts, parts of wholes and places, are possessed by placing the possessor directly
before them. Many of them have two forms, which Dixon calls the f form and the m form: the m form
goes with a first or second person possessor and with a masculine singular one, and the f form
with a feminine singular possessor and with a third person nonsingular one. The first and second
person singular possessors are prefixes, the other pronouns separate words, and a third person
singular pronoun is unpronounced. A possessed noun used without a possessor is feminine, with the
one exception of *atiwa* 'thorn'.

## Implementation notes

* A possessed noun with a single form has the same f and m form.
* A few possessed nouns, *isi/iso* 'leg' among them, take the first and second person singular
  prefixes on the f form; `PossessedNoun.form` gives the general rule.

## References

* [dixon-2004]
-/

@[expose] public section

namespace Jarawara

/-- The two genders. -/
inductive Gender where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The possessors that a possessed noun's form distinguishes. -/
inductive Possessor where
  | sg1
  | sg2
  /-- The first person nonsingular inclusive. -/
  | incl
  /-- The first person nonsingular exclusive. -/
  | excl
  | nsg2
  /-- The third person singular, with its gender. -/
  | sg3 (g : Gender)
  /-- The third person nonsingular, with the gender of the noun it accompanies. -/
  | nsg3 (g : Gender)
  deriving DecidableEq, Repr, Fintype

/-- The pronoun of a possessor, none for the third person singular. -/
def Possessor.pronoun : Possessor → Option String
  | .sg1 => some "o-"
  | .sg2 => some "ti-"
  | .incl => some "ee"
  | .excl => some "otaa"
  | .nsg2 => some "tee"
  | .nsg3 _ => some "mee"
  | .sg3 _ => none

/-- The first and second person singular pronouns are prefixes on the possessed noun. -/
def Possessor.IsPrefix : Possessor → Prop
  | .sg1 | .sg2 => True
  | _ => False

instance : DecidablePred Possessor.IsPrefix := fun p ↦ by
  cases p <;> unfold Possessor.IsPrefix <;> infer_instance

/-- The gender of the form a possessor takes, masculine for first and second person and masculine
singular possessors and feminine for feminine singular and third person nonsingular ones. -/
def Possessor.formGender : Possessor → Gender
  | .sg3 g => g
  | .nsg3 _ => .fem
  | _ => .masc

/-- A possessed noun with its f and m forms, and the free noun it is used as, if any. -/
structure PossessedNoun where
  /-- The f form. -/
  fForm : String
  /-- The m form. -/
  mForm : String
  /-- The gloss. -/
  gloss : String
  /-- The noun used without a possessor. -/
  free : Option (GenderedNoun Gender) := none
  deriving DecidableEq, Repr

/-- The form of a possessed noun with a possessor. -/
def PossessedNoun.form (n : PossessedNoun) (p : Possessor) : String :=
  match p.formGender with
  | .masc => n.mForm
  | .fem => n.fForm

/-! ### Possessed nouns -/

/-- *mani/mano* 'arm'. -/
def mano : PossessedNoun := ⟨"mani", "mano", "arm", none⟩

/-- *baki/bako* 'underside, inside surface'. -/
def bako : PossessedNoun := ⟨"baki", "bako", "underside, inside surface", none⟩

/-- *mahi/maho* 'smell'. -/
def maho : PossessedNoun := ⟨"mahi", "maho", "smell", none⟩

/-- *tati* 'head', which has one form. -/
def tati : PossessedNoun := ⟨"tati", "tati", "head", none⟩

/-- *hawi/hawine* 'path', used freely as *hawi* 'path'. -/
def hawi : PossessedNoun := ⟨"hawi", "hawine", "path", some ⟨⟨"hawi", "path", none⟩, .fem⟩⟩

/-- *ame/emene* 'blood', used freely as *ama* 'blood'. -/
def ame : PossessedNoun := ⟨"ame", "emene", "blood", some ⟨⟨"ama", "blood", none⟩, .fem⟩⟩

/-- *fehe/fehene* 'liquid, juice, sap, water', used freely as *faha* 'water'. -/
def fehe : PossessedNoun :=
  ⟨"fehe", "fehene", "liquid, juice, sap, water", some ⟨⟨"faha", "water", none⟩, .fem⟩⟩

/-- *atine* 'thorn', used freely as the masculine *atiwa* 'thorn'. -/
def atine : PossessedNoun := ⟨"atine", "atine", "thorn", some ⟨⟨"atiwa", "thorn", none⟩, .masc⟩⟩

/-- The possessed nouns. -/
def possessedNouns : List PossessedNoun := [mano, bako, maho, tati, hawi, ame, fehe, atine]

end Jarawara
