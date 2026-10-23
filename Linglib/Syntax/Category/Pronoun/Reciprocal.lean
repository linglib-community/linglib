module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Reciprocal

/-!
# Reciprocal pronouns

A reciprocal pronoun is a pronoun that is the nominal exponent of reciprocity: it carries the
marker data of `Syntax/Reciprocal.lean` and the nominal strategy it realizes, and its kind fixes
the reciprocal binding class. A fragment writes the pronoun once and
derives its `Reciprocal.Marker` with `toMarker`; Hungarian *egymás*, Japanese *otagai* and Wan
*ɔ̄ŋ̄* are such objects. Verbal and clitic reciprocal strategies are not pronouns and stay bare
markers.

## Main definitions

* `ReciprocalPronoun`: a pronoun with its reciprocal strategy.
* `ReciprocalPronoun.toMarker`: its entry in a marker inventory.

## Main statements

* `ReciprocalPronoun.bindingClassOf_toWord`: its token classifies as a reciprocal anaphor.

## References

* [nordlinger-2023]
-/

@[expose] public section

/-- A reciprocal pronoun is a `Pronoun` that is the nominal exponent of reciprocity, with the
strategy it realizes. -/
@[ext]
structure ReciprocalPronoun extends Pronoun where
  /-- The nominal strategy, a dedicated pronoun (*egymás*, *otagai*) or a two-part quantifier
  noun phrase (*each other*). -/
  strategy : Reciprocal.Strategy := .recipPronoun

instance : DecidableEq ReciprocalPronoun :=
  fun _ _ ↦ decidable_of_iff _ ReciprocalPronoun.ext_iff.symm

/-- The marker entry of a reciprocal pronoun. -/
def ReciprocalPronoun.toMarker (p : ReciprocalPronoun) : Reciprocal.Marker :=
  { morphs := [.free p.form], script := p.script, strategy := p.strategy }

/-- A reciprocal's word is of UD pronoun type `Rcp`. -/
def ReciprocalPronoun.toWord (p : ReciprocalPronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Rcp)

@[simp]
theorem ReciprocalPronoun.bindingClassOf_toWord (p : ReciprocalPronoun) :
    Binding.bindingClassOf p.toWord = some .reciprocal :=
  Pronoun.bindingClassOf_toWord_rcp _

