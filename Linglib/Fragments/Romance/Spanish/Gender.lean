module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Syntax.Category.Noun.Basic
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

* `Spanish.Gender.Value`: the two genders, with their comparative labels.
* `Spanish.Gender.Noun`: a noun with its gender, the gender of its referents where they have
  one, and their animacy.
* `Spanish.Gender.Noun.ofNaturalGender`: the entry of a noun whose gender is its referent's sex.
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

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine

/-- A noun with its gender, the gender of its referents where they have one, and their
animacy. -/
structure Noun extends GenderedNoun Value where
  /-- The animacy of the noun's referents. -/
  animacy : Reference.Animacy
  deriving DecidableEq, Repr

/-- `Noun.ofNaturalGender form gloss a g` is the noun `form` 'gloss' for a referent of gender
`g` and animacy `a`, whose gender is `g`. -/
def Noun.ofNaturalGender (form gloss : String) (animacy : Reference.Animacy) (g : Value) :
    Noun :=
  ⟨⟨⟨form, gloss⟩, g, some g.toLabel⟩, animacy⟩

@[simp]
theorem Noun.isNaturalGender_ofNaturalGender (form gloss : String) (a : Reference.Animacy)
    (g : Value) : (Noun.ofNaturalGender form gloss a g).IsNaturalGender Value.toLabel :=
  rfl

/-! ### Nouns taking the referent's gender -/

/-- *hombre* 'man'. -/
def hombre : Noun := .ofNaturalGender "hombre" "man" .human .masc

/-- *mujer* 'woman'. -/
def mujer : Noun := .ofNaturalGender "mujer" "woman" .human .fem

/-- *niño* 'boy'. -/
def niño : Noun := .ofNaturalGender "niño" "boy" .human .masc

/-- *niña* 'girl'. -/
def niña : Noun := .ofNaturalGender "niña" "girl" .human .fem

/-- *rey* 'king'. -/
def rey : Noun := .ofNaturalGender "rey" "king" .human .masc

/-- *reina* 'queen'. -/
def reina : Noun := .ofNaturalGender "reina" "queen" .human .fem

/-- *gato* 'cat', whose plural *los gatos* also covers cats of either sex. -/
def gato : Noun := .ofNaturalGender "gato" "cat" .animate .masc

/-- *gata* 'she-cat'. -/
def gata : Noun := .ofNaturalGender "gata" "she-cat" .animate .fem

/-- *soldado* 'soldier', *un soldado* of a man and *una soldado* of a woman. -/
def soldado : Value → Noun := .ofNaturalGender "soldado" "soldier" .human

/-- *estudiante* 'student', *el estudiante* of a man and *la estudiante* of a woman. -/
def estudiante : Value → Noun := .ofNaturalGender "estudiante" "student" .human

/-- *artista* 'artist', *el artista* of a man and *la artista* of a woman. -/
def artista : Value → Noun := .ofNaturalGender "artista" "artist" .human

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
    ([soldado, estudiante, artista].flatMap fun n ↦ [n .masc, n .fem]) ++
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
