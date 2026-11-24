module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Semantics.Reference.Animacy

/-!
# Romanian noun gender

Agreeing adjectives such as *bun* 'good' show two forms in the singular, *-Ø* and *-ă*, and
two in the plural, *-i* and *-e*, but nouns fall into three sets by the forms they take
across the two numbers: *bărbat* 'man' (*-Ø*, *-i*), *fată* 'girl' (*-ă*, *-e*) and *scaun*
'chair' (*-Ø*, *-e*), the last the disputed neuter or ambigeneric gender
(Mallinson; Corbett).

## References

* [G. Mallinson, *Rumanian* (1984)][mallinson-1984]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

@[expose] public section

namespace Romanian.Gender

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A Romanian noun with its controller gender, the gender it restricts its referents to where it
does, and their animacy. -/
structure Noun extends GenderedNoun Value where
  /-- The animacy of the noun's referents. -/
  animacy : Animacy
  deriving DecidableEq, Repr

def barbat : Noun := ⟨⟨⟨"bărbat", "man", some .male⟩, .masc⟩, .human⟩
def fata : Noun := ⟨⟨⟨"fată", "girl", some .female⟩, .fem⟩, .human⟩
def scaun : Noun := ⟨⟨⟨"scaun", "chair", none⟩, .neut⟩, .inanimate⟩
def femeie : Noun := ⟨⟨⟨"femeie", "woman", some .female⟩, .fem⟩, .human⟩
def baiat : Noun := ⟨⟨⟨"băiat", "boy", some .male⟩, .masc⟩, .human⟩
def usa : Noun := ⟨⟨⟨"uşă", "door", none⟩, .fem⟩, .inanimate⟩
def perete : Noun := ⟨⟨⟨"perete", "wall", none⟩, .masc⟩, .inanimate⟩
def masa : Noun := ⟨⟨⟨"masă", "table", none⟩, .fem⟩, .inanimate⟩
def nuc : Noun := ⟨⟨⟨"nuc", "walnut tree", none⟩, .masc⟩, .inanimate⟩
def prun : Noun := ⟨⟨⟨"prun", "plum tree", none⟩, .masc⟩, .inanimate⟩
def frigider : Noun := ⟨⟨⟨"frigider", "refrigerator", none⟩, .neut⟩, .inanimate⟩
def televizor : Noun := ⟨⟨⟨"televizor", "television", none⟩, .neut⟩, .inanimate⟩

def allNouns : List Noun :=
  [barbat, fata, scaun, femeie, baiat, usa, perete, masa, nuc, prun, frigider, televizor]

/-- The endings of *bun* 'good'. -/
inductive AdjForm where
  | zero
  | ă
  | i
  | e
  deriving DecidableEq, Repr, Fintype

/-- Romanian distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The ending an agreeing adjective takes with each gender, in each number. -/
def Value.adjForm (g : Value) : numberSystem → AdjForm :=
  Number.elim numberSystem (match g with | .masc => .zero | .fem => .ă | .neut => .zero)
    (match g with | .masc => .i | .fem => .e | .neut => .e)

theorem faithful_adjForm : Gender.Faithful Value.adjForm := by decide

end Romanian.Gender
