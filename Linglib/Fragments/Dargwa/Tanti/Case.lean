module

public import Linglib.Syntax.Case.Alignment
public import Linglib.Morphology.Morph

/-!
# Tanti Dargwa case

This file defines the grammatical cases of Tanti Dargwa as Sumbatova describes them. A noun has
a direct stem, its absolutive singular, and an oblique stem, the direct stem with *-li*, which
is its ergative singular and the base of most other forms. The dative and the comitative add
their suffix to the oblique stem, as do the locative forms of `Locatives.lean`, while the
absolutive and the adverbial are built on the direct stem. Tanti has the absolutive, ergative,
genitive, dative and comitative of most Dargwa varieties and an adverbial case of nominal and
secondary predicates besides, which goes under the comparative label of the essive. The
alignment is ergative without a split, A ergative and S and P absolutive.

## Main definitions

* `Dargwa.Tanti.Case`, `Dargwa.Tanti.Case.label`: the six cases, and the comparative value each is named for
* `Dargwa.Tanti.obliqueStem`: the oblique stem suffix *-li*
* `Dargwa.Tanti.Case.exponent`: the suffixes of a case after the direct stem
* `Dargwa.Tanti.marking`: the ergative marking of the core arguments

## Main results

* `Dargwa.Tanti.Case.builtOnOblique_iff`: the ergative, dative and comitative are the cases built
  on the oblique stem
* `Dargwa.Tanti.label_comp_marking`: the marking is the ergative alignment

## Implementation notes

* The genitive is *-la*, or *-lla* for some nouns, and for some nouns is built on the oblique
  stem; the exponent records the *-la* of *dubur-la* 'mountain's'. The plural builds its
  oblique forms on an oblique plural stem, the absolutive plural with *-a*, which is not
  treated.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.Tanti

open Morphology

/-- The oblique stem suffix *-li*. The oblique singular stem is the direct stem with it, and
is the ergative singular. -/
def obliqueStem : Morph := .suff "li"

/-- The six grammatical cases. -/
inductive Case where
  /-- The absolutive, the direct stem. -/
  | abs
  /-- The ergative, the oblique stem. -/
  | erg
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The comitative. -/
  | com
  /-- The adverbial, of nominal and secondary predicates. -/
  | adv
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the essive for the adverbial. -/
def label : Case → _root_.Case
  | abs => .abs
  | erg => .erg
  | gen => .gen
  | dat => .dat
  | com => .com
  | adv => .ess

/-- The suffixes of a case after the direct singular stem. The absolutive is unmarked, the
ergative is the oblique stem, the genitive takes *-la*, the dative *-ž* and the comitative
*-cːele* on the oblique stem, and the adverbial *-le*. -/
def exponent : Case → List Morph
  | abs => []
  | erg => [obliqueStem]
  | gen => [.suff "la"]
  | dat => [obliqueStem, .suff "ž"]
  | com => [obliqueStem, .suff "cːele"]
  | adv => [.suff "le"]

/-- A case is built on the oblique stem when its exponent begins with the stem suffix. -/
def BuiltOnOblique (c : Case) : Prop := c.exponent.head? = some obliqueStem

instance : DecidablePred BuiltOnOblique := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The ergative, dative and comitative are the cases built on the oblique stem. -/
theorem builtOnOblique_iff (c : Case) :
    BuiltOnOblique c ↔ c = .erg ∨ c = .dat ∨ c = .com := by
  cases c <;> decide

end Case

/-- The marking of the core arguments is ergative, A ergative and S and P absolutive, with no
split by tense or aspect. -/
def marking : ArgumentRole → Case
  | .A => .erg
  | .S | .P | .R | .T => .abs

/-- The marking is the ergative alignment. -/
theorem label_comp_marking : Case.label ∘ marking = Alignment.ergative := by
  funext r; cases r <;> rfl

end Dargwa.Tanti
