module

public import Linglib.Semantics.Modality.Typology
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# English adverbs

The closed-class adverbs of English are typed by their semantic owners. The modal adverbs
*certainly*, *definitely*, *necessarily*, *possibly*, *perhaps*, *maybe*, *probably* and
*potentially* are `Modality.ModalItem`s, with their force–flavor meanings and register. The
adverbs of quantification *always*, *usually*, *sometimes* and *never*, which Lewis analyzes as
quantifiers over cases, are the carrier `AdverbOfQuantification`, whose words denote their
readings as generalized quantifiers. The modal-concord readings of *must certainly* and *may
possibly* and the situation-pronoun analysis of adverbs of quantification live in the studies
that treat them.

## References

* [kratzer-1981]
* [lewis-1975]
* [percus-2000]
* [liu-rotter-2025]
-/

@[expose] public section

namespace English.Adverbs

/-! ### Modal adverbs -/

section ModalAdverbs

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def certainly : ModalItem := { form := "certainly", meaning := {ne}, register := .formal }
def definitely : ModalItem := { form := "definitely", meaning := {ne, nd} }
def necessarily : ModalItem := { form := "necessarily", meaning := {ne, nc}, register := .formal }
def possibly : ModalItem := { form := "possibly", meaning := {pe} }
def perhaps : ModalItem := { form := "perhaps", meaning := {pe}, register := .formal }
def maybe : ModalItem := { form := "maybe", meaning := {pe}, register := .informal }
def probably : ModalItem := { form := "probably", meaning := {ne} }
def potentially : ModalItem := { form := "potentially", meaning := {pc} }

def modalAdverbs : List ModalItem :=
  [certainly, definitely, necessarily, possibly, perhaps, maybe, probably, potentially]

end ModalAdverbs

/-! ### Adverbs of quantification -/

/-- The adverbs of quantification *always*, *usually*, *sometimes* and *never* quantify over the
cases their restrictor supplies ([lewis-1975]). -/
inductive AdverbOfQuantification where
  | always | usually | sometimes | never
  deriving DecidableEq, Repr

namespace AdverbOfQuantification

/-- The form of an adverb is its spelling. -/
def form : AdverbOfQuantification → String
  | .always => "always"
  | .usually => "usually"
  | .sometimes => "sometimes"
  | .never => "never"

universe u

/-- An adverb denotes its reading over cases, *always* `every`, *usually* `most`, *sometimes*
`Quantifier.GQ.some` and *never* `no`. -/
noncomputable instance : Denotes AdverbOfQuantification (Set Quantifier.GQ.Family.{u})
    where
  denote
    | .always => {Quantifier.GQ.Family.every}
    | .usually => {Quantifier.GQ.Family.most}
    | .sometimes => {Quantifier.GQ.Family.some}
    | .never => {Quantifier.GQ.Family.no}

end AdverbOfQuantification

end English.Adverbs
