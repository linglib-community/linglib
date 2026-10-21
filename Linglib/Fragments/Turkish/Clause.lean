module

public import Mathlib.Data.Finset.Union
public import Linglib.Data.UD.Features
public import Linglib.Morphology.Morph
public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Fragments.Turkish.Negation
public import Linglib.Syntax.Clause.Chaining

/-!
# Turkish converbs

Turkish chains clauses with converbial suffixes on the verb of each medial clause before a
single final verb, without switch-reference. *-(y)Ip* conjoins clauses of equal status in place
of the tense, aspect and modality suffixes, *-(y)ArAk* gives the manner or means, *-(y)IncA*
'when' sequences two events, *-(y)AlI* 'since' marks a starting point, *-mAdAn* 'without doing'
contains the negative, *-DIkçA* marks proportionality, and *-(y)ken* 'while' and *-cAsInA* 'as
if' attach not to the stem but to a tensed one, *-(y)ken* being the copula on a position-3
marker or a nominal. The converbs take no person marker, except the third-person plural on
*-(y)ken* and a person marker on *-mIşçAsInA*. Two more converbial subordinators go on a
doubled verb: *-(A/I)r … -mAz* 'as soon as' and *-(y)A … -(y)A*, continuous manner.

## Implementation notes

* Whether a converb takes a tense marker or the negative is read off the finite verb's
  template `Turkish.Verb.template` from the slot the converb follows.
* The clause-chaining typology over the converbs is in `Studies/SarvasyAikhenvald2025.lean`.

## References

* [goksel-kerslake-2005]
-/

@[expose] public section

namespace Turkish

open Clause.Chaining (InterclauseRelation)
open Morphology (Morph)

/-- The converbial suffixes on a single verb, with vowel harmony shown by a capital
archiphoneme and a buffer consonant in parentheses. -/
inductive Converb where
  /-- *-(y)Ip*, conjunctive 'and, and then'. -/
  | ip
  /-- *-(y)ArAk* 'by doing, doing', manner and means, also conjunctive. -/
  | arak
  /-- *-(y)IncA* 'when'. -/
  | inca
  /-- *-(y)ken* 'while, as, when', the copula on a tensed stem or a nominal. -/
  | ken
  /-- *-(y)AlI* 'since', colloquial. -/
  | ali
  /-- *-mAdAn* 'without doing, before doing', containing the negative. -/
  | madan
  /-- *-cAsInA* 'as if', on the aorist or *-mIş*. -/
  | casina
  /-- *-DIkçA* 'the more, as', proportional. -/
  | dikca
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | ip => [.suff "(y)Ip"]
  | arak => [.suff "(y)ArAk"]
  | inca => [.suff "(y)IncA"]
  | ken => [.suff "(y)ken"]
  | ali => [.suff "(y)AlI"]
  | madan => Negation.mA.morphs ++ [.suff "DAn"]
  | casina => [.suff "cAsInA"]
  | dikca => [.suff "DIkçA"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | ip => "and, and then"
  | arak => "by doing, doing"
  | inca => "when"
  | ken => "while, as, when"
  | ali => "since"
  | madan => "without doing, before doing"
  | casina => "as if"
  | dikca => "the more, as"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | ip => {.sequential, .additive}
  | arak => {.manner, .simultaneous, .additive}
  | inca | ali => {.sequential}
  | ken => {.simultaneous}
  | madan | casina => {.manner}
  | dikca => ∅

/-- The last slot of the finite verb whose exponent may precede the converb, which is the
negative for the converbs on the stem, a position-3 marker for *-(y)ken* and *-cAsInA*, and
the possibility suffix for *-mAdAn*, which contains the negative itself. -/
def follows : Converb → Verb.Slot
  | ip | arak | inca | ali | dikca => .negation
  | ken | casina => .tam
  | madan => .possibility

/-- An exponent of the slot may precede the converb, since the slot is the one the converb
follows or the finite verb's template admits it before that one. -/
def Admits (c : Converb) (s : Verb.Slot) : Prop :=
  c.follows = s ∨ [s, c.follows] ∈ Verb.template.language

instance (c : Converb) (s : Verb.Slot) : Decidable (c.Admits s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The converb is inherently negative. -/
def InherentlyNegative (c : Converb) : Prop := c = madan

instance : DecidablePred InherentlyNegative := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The converb can be negated, being negative itself or admitting the negative before it. -/
def Negatable (c : Converb) : Prop := c.InherentlyNegative ∨ c.Admits .negation

instance : DecidablePred Negatable := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A tense, aspect or modality marker may precede the converb. -/
def Tensed (c : Converb) : Prop := c.Admits .tam

instance : DecidablePred Tensed := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The converb may carry a person marker, the third-person plural on *-(y)ken* and a person
marker on *-mIşçAsInA*. -/
def PersonMarked (c : Converb) : Prop := c = ken ∨ c = casina

instance : DecidablePred PersonMarked := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference, encoding their relations, and
indexing the subject where they may carry a person marker. -/
instance : Clause.Chaining.MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject := PersonMarked

end Converb

/-- *-(A/I)r … -mAz* 'as soon as', the positive and negative aorist on a doubled verb. -/
def arMaz : List (List Morph) := [[.suff "(A/I)r"], Negation.mA.morphs ++ [.suff "z"]]

/-- *-(y)A … -(y)A*, emphatic continuous manner on a doubled verb. -/
def aA : List (List Morph) := [[.suff "(y)A"], [.suff "(y)A"]]

end Turkish
