module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Japanese postpositions

The postpositions of Japanese as `Adposition` entries. Tsujimura lists *de* 'at', *e* 'to', *to*
'with', *made* 'until' and *kara* 'from' (§1.5, p. 133). Unlike the case particles, the cases of
`Japanese.Case`, they carry an inherent meaning and cannot be dropped (pp. 136–137), and they
cannot stand independently, which places them outside the word class (p. 133), so each is an
enclitic. *De* marks location (p. 136) and the instrument (p. 218), *kara* the source (p. 218),
and *made* 'until, as far as' an endpoint (p. 137).

## Main definitions

* `Japanese.Adpositions.inventory`: the postpositions.

## Implementation notes

* *Yori* 'than' is the standard marker of the comparative (`Japanese.Comparison.yori`), recorded
  here as an ablative postposition after Stassen; Tsujimura does not classify it.
* The postposition *ni* that Sadakane and Koizumi separate from the dative case marker is the
  matter of `Studies/SadakaneKoizumi1995.lean`; the language file keeps the single dative *ni*.

## References

* [tsujimura-2014]
* [stassen-1985]
* [sadakane-koizumi-1995]
-/

@[expose] public section

namespace Japanese.Adpositions

/-- *de* で 'at', marking the place of an action and its instrument. -/
def de : Adposition :=
  { morphs := [.encl "de"], linearization := {.post},
    functions := {.spatial none .place, .instrumental},
    complements := {some .np} }

/-- *e* へ 'to', marking a goal. -/
def e : Adposition :=
  { morphs := [.encl "e"], linearization := {.post}, functions := {.spatial none .goal},
    complements := {some .np} }

/-- *to* と 'with', marking a companion. -/
def «to» : Adposition :=
  { morphs := [.encl "to"], linearization := {.post}, functions := {.comitative},
    complements := {some .np} }

/-- *kara* から 'from', marking a source. -/
def kara : Adposition :=
  { morphs := [.encl "kara"], linearization := {.post}, functions := {.spatial none .source},
    complements := {some .np} }

/-- *made* まで 'until, as far as', marking an endpoint. -/
def made : Adposition :=
  { morphs := [.encl "made"], linearization := {.post}, functions := {.terminative},
    complements := {some .np} }

/-- *yori* より 'than', marking the standard of a comparison as an ablative. -/
def yori : Adposition :=
  { morphs := [.encl "yori"], linearization := {.post}, functions := {.spatial none .source},
    complements := {some .np} }

/-- The postpositions. -/
def inventory : List Adposition := [de, e, «to», kara, made, yori]

end Japanese.Adpositions
