module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Syntax.Gender.Assignment
public import Linglib.Syntax.Number.Basic

/-!
# Spanish noun gender

Spanish nouns are masculine or feminine, and Butt and Benjamin's grammar sorts them by what they
denote. A
noun for human beings or a few well-known animals takes the gender of its referent's sex: in a
special form for each sex, *el hombre* 'man' and *la mujer* 'woman', with feminine *-a* for
masculine *-o*, *el niño* and *la niña*, or in one form for either sex, *el estudiante* and *la
estudiante*. A few such nouns keep one gender whatever the referent's sex, *la persona* 'person'
and *el ángel* 'angel'. Every other noun, for things, plants and the remaining animals, has a
gender that must be learned, *la mesa* 'table' and *el libro* 'book'. The definite article shows
the gender: *el* and *los* go with a masculine, *la* and *las* with a feminine.

## Main definitions

* `Spanish.Gender.Value`: the two genders.
* `Spanish.Gender.Noun`: a noun with its grammatical gender, the gender it restricts its referents
  to where it does, and their animacy.
* `Spanish.Gender.Noun.ofReferentGender`: the entry of a noun whose grammatical gender is the one
  its referents' gender is assigned.
* `Spanish.Gender.Value.definiteArticle`: the definite article of each gender in each number.

## Main results

* `Spanish.Gender.faithful_definiteArticle`: the definite article distinguishes the genders.

## Implementation notes

A noun of one form for either sex is a function from the gender of its referent to the entry for
that referent, so that *estudiante .fem* is *la estudiante*. Before a feminine singular beginning
with stressed *a-*, the article is *el*, as in *el agua* 'water', and the noun stays feminine;
`Value.definiteArticle` gives the form before every other noun.

## References

* [butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.Gender

/-- The two genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- Male humans are masculine and female humans feminine. -/
def Value.ofReferentGender : ReferentGender → Value
  | .male => .masc
  | .female => .fem

/-- A noun with its grammatical gender, the gender it restricts its referents to where it does,
and their animacy. -/
structure Noun extends GenderedNoun Value where
  /-- The animacy of the noun's referents. -/
  animacy : Animacy
  deriving DecidableEq, Repr

/-- A noun's gender is natural when it is the one its referents' gender is assigned. -/
abbrev Noun.IsNatural (n : Noun) : Prop :=
  _root_.Gender.IsNatural (Option.map Value.ofReferentGender) (·.referentGender) (·.gender) n

/-- `Noun.ofReferentGender form gloss a x` is the noun `form` 'gloss' for referents of gender `x`
and animacy `a`, whose grammatical gender is the one `x` is assigned. -/
def Noun.ofReferentGender (form gloss : String) (animacy : Animacy) (x : ReferentGender) : Noun :=
  ⟨⟨⟨form, gloss⟩, Value.ofReferentGender x, some x⟩, animacy⟩

@[simp]
theorem Noun.isNatural_ofReferentGender (form gloss : String) (a : Animacy) (x : ReferentGender) :
    (Noun.ofReferentGender form gloss a x).IsNatural :=
  rfl

/-! ### Nouns taking the referent's gender -/

/-- *hombre* 'man'. -/
def hombre : Noun := .ofReferentGender "hombre" "man" .human .male

/-- *mujer* 'woman'. -/
def mujer : Noun := .ofReferentGender "mujer" "woman" .human .female

/-- *niño* 'boy'. -/
def niño : Noun := .ofReferentGender "niño" "boy" .human .male

/-- *niña* 'girl'. -/
def niña : Noun := .ofReferentGender "niña" "girl" .human .female

/-- *rey* 'king'. -/
def rey : Noun := .ofReferentGender "rey" "king" .human .male

/-- *reina* 'queen'. -/
def reina : Noun := .ofReferentGender "reina" "queen" .human .female

/-- *gato* 'cat', whose plural *los gatos* also covers cats of either sex. -/
def gato : Noun := .ofReferentGender "gato" "cat" .animate .male

/-- *gata* 'she-cat'. -/
def gata : Noun := .ofReferentGender "gata" "she-cat" .animate .female

/-- *soldado* 'soldier', *un soldado* of a man and *una soldado* of a woman. -/
def soldado : ReferentGender → Noun := .ofReferentGender "soldado" "soldier" .human

/-- *estudiante* 'student', *el estudiante* of a man and *la estudiante* of a woman. -/
def estudiante : ReferentGender → Noun := .ofReferentGender "estudiante" "student" .human

/-- *artista* 'artist', *el artista* of a man and *la artista* of a woman. -/
def artista : ReferentGender → Noun := .ofReferentGender "artista" "artist" .human

/-! ### Nouns of one gender for either sex -/

/-- *persona* 'person', feminine whatever the referent's sex. -/
def persona : Noun := { form := "persona", gloss := "person", gender := .fem, animacy := .human }

/-- *ángel* 'angel', masculine whatever the referent's sex. -/
def ángel : Noun := { form := "ángel", gloss := "angel", gender := .masc, animacy := .human }

/-! ### Nouns of arbitrary gender -/

/-- *mesa* 'table'. -/
def mesa : Noun := { form := "mesa", gloss := "table", gender := .fem, animacy := .inanimate }

/-- *silla* 'chair'. -/
def silla : Noun := { form := "silla", gloss := "chair", gender := .fem, animacy := .inanimate }

/-- *casa* 'house'. -/
def casa : Noun := { form := "casa", gloss := "house", gender := .fem, animacy := .inanimate }

/-- *puerta* 'door'. -/
def puerta : Noun := { form := "puerta", gloss := "door", gender := .fem, animacy := .inanimate }

/-- *ventana* 'window'. -/
def ventana : Noun :=
  { form := "ventana", gloss := "window", gender := .fem, animacy := .inanimate }

/-- *cama* 'bed'. -/
def cama : Noun := { form := "cama", gloss := "bed", gender := .fem, animacy := .inanimate }

/-- *libro* 'book'. -/
def libro : Noun := { form := "libro", gloss := "book", gender := .masc, animacy := .inanimate }

/-- *zapato* 'shoe'. -/
def zapato : Noun := { form := "zapato", gloss := "shoe", gender := .masc, animacy := .inanimate }

/-- *coche* 'car'. -/
def coche : Noun := { form := "coche", gloss := "car", gender := .masc, animacy := .inanimate }

/-- *árbol* 'tree'. -/
def árbol : Noun := { form := "árbol", gloss := "tree", gender := .masc, animacy := .inanimate }

/-- *cielo* 'sky'. -/
def cielo : Noun := { form := "cielo", gloss := "sky", gender := .masc, animacy := .inanimate }

/-- *vaso* 'glass'. -/
def vaso : Noun := { form := "vaso", gloss := "glass", gender := .masc, animacy := .inanimate }

/-- The nouns, with both entries of each noun of one form for either sex. -/
def allNouns : List Noun :=
  [hombre, mujer, niño, niña, rey, reina, gato, gata] ++
    ([soldado, estudiante, artista].flatMap fun n ↦ [n .male, n .female]) ++
    [persona, ángel, mesa, silla, casa, puerta, ventana, cama, libro, zapato, coche, árbol,
      cielo, vaso]

/-! ### The definite article -/

/-- Spanish distinguishes the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- The definite article a gender takes in each number. -/
def Value.definiteArticle (g : Value) : numberSystem.values → String :=
  numberSystem.elim (match g with | .masc => "el" | .fem => "la")
    (match g with | .masc => "los" | .fem => "las")

/-- The definite article distinguishes the two genders. -/
theorem faithful_definiteArticle : Gender.Faithful Value.definiteArticle := by decide

end Spanish.Gender
