module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Semantics.Reference.Animacy

/-!
# Latin noun gender

Latin has three genders, masculine, feminine and neuter, and its adjectives differ in how
many of them they distinguish: in the nominative singular *acer* 'sharp' has a form for each,
*facilis* 'easy' sets the neuter against the other two, and *felix* 'happy' has one form for
all three ([corbett-1998]). The nouns are those of Corbett's examples of resolved agreement,
*pater* 'father' and *mater* 'mother', and *murus* 'wall' and *porta* 'gate' ([corbett-1991]).

## References

* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

@[expose] public section

namespace Latin.Gender

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A Latin noun with its controller gender, the gender it restricts its referents to where it
does, and their animacy. -/
structure Noun extends GenderedNoun Value where
  /-- The animacy of the noun's referents. -/
  animacy : Animacy
  deriving DecidableEq, Repr

/-- *pater* 'father'. -/
def pater : Noun := ⟨⟨⟨"pater", "father"⟩, .masc, some .male⟩, .human⟩
/-- *mater* 'mother'. -/
def mater : Noun := ⟨⟨⟨"mater", "mother"⟩, .fem, some .female⟩, .human⟩
/-- *murus* 'wall'. -/
def murus : Noun := ⟨⟨⟨"murus", "wall"⟩, .masc, none⟩, .inanimate⟩
/-- *porta* 'gate'. -/
def porta : Noun := ⟨⟨⟨"porta", "gate"⟩, .fem, none⟩, .inanimate⟩

/-- The nouns of the file. -/
def allNouns : List Noun := [pater, mater, murus, porta]

/-- An adjective by its nominative singular forms. -/
structure Adjective where
  /-- The gloss. -/
  gloss : String
  /-- The nominative singular form in each gender. -/
  nomSg : Value → String

/-- *acer*, *acris*, *acre* 'sharp'. -/
def acer : Adjective := ⟨"sharp", fun | .masc => "acer" | .fem => "acris" | .neut => "acre"⟩
/-- *facilis*, *facile* 'easy'. -/
def facilis : Adjective := ⟨"easy", fun | .neut => "facile" | _ => "facilis"⟩
/-- *felix* 'happy'. -/
def felix : Adjective := ⟨"happy", fun _ ↦ "felix"⟩

/-- The adjectives of Corbett's table. -/
def allAdjectives : List Adjective := [acer, facilis, felix]

theorem faithful_acer : Function.Injective acer.nomSg := by decide

end Latin.Gender
