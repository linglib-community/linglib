module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Gender.Basic

/-!
# Latin noun gender

Latin has three genders, masculine, feminine and neuter, and its adjectives differ in how
many of them they distinguish: in the nominative singular *acer* 'sharp' has a form for each,
*facilis* 'easy' sets the neuter against the other two, and *felix* 'happy' has one form for
all three ([corbett-1998]).

## References

* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
-/

@[expose] public section

namespace Latin.Gender

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

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
