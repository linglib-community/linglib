module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Hindi-Urdu postpositions

The simple postpositions of Hindi-Urdu, *ne*, *ko*, *se*, *kaa*, *mẽ*, *par* and *tak*, as
`Adposition` entries. They follow the oblique form of the noun and have one shape in both numbers
(Masica p. 233), and they are clitics rather than affixes: a pause may separate them from the
noun, and one may scope over coordinated nouns, *madraas aur haiderabaad-se* 'from Madras and
Hyderabad' (Mohanan pp. 61–62; Masica p. 234). Each is an enclitic. The values marked are
Mohanan's labels, *ko* both accusative and dative (p. 61), with *se* the instrumental, sociative
and ablative at once (Masica p. 238); *tak* is the clitic Mohanan adds to the six (p. 61). *Kaa*
alone agrees, with the possessed noun, as Spencer notes.

## Main definitions

* `HindiUrdu.Adpositions.inventory`: the simple postpositions.

## Implementation notes

* The sources agree that these are clitics and disagree on whether they realize case: Mohanan
  takes them to mark case features, Masica treats them as formal cases, and Spencer as
  postpositions that select the oblique, the only cases being the inflected forms of
  `HindiUrdu.Case`.
* *Kaa* is recorded in its masculine singular direct form.

## References

* [masica-1991]
* [mohanan-1994]
* [spencer-2005]
-/

@[expose] public section

namespace HindiUrdu.Adpositions

/-- *ne*, marking the agent of a perfective verb. -/
def ne : Adposition :=
  { morphs := [.encl "ne"], linearization := {.post}, functions := {.argument .A},
    complements := {some .np} }

/-- *ko*, marking the goal and the object. -/
def ko : Adposition :=
  { morphs := [.encl "ko"], linearization := {.post}, functions := {.argument .R, .argument .P},
    complements := {some .np} }

/-- *se*, marking the instrument, the source and the companion. -/
def se : Adposition :=
  { morphs := [.encl "se"], linearization := {.post},
    functions := {.instrumental, .spatial none .source, .comitative},
    complements := {some .np} }

/-- *kaa*, marking the possessor. -/
def kaa : Adposition :=
  { morphs := [.encl "kaa"], linearization := {.post}, functions := {.possessor},
    complements := {some .np} }

/-- *mẽ* 'in'. -/
def me : Adposition :=
  { morphs := [.encl "mẽ"], linearization := {.post}, functions := {.spatial none .place},
    complements := {some .np} }

/-- *par* 'on, at'. -/
def par : Adposition :=
  { morphs := [.encl "par"], linearization := {.post}, functions := {.spatial none .place},
    complements := {some .np} }

/-- *tak* 'until', as in *kal-tak* 'until yesterday'. -/
def tak : Adposition :=
  { morphs := [.encl "tak"], linearization := {.post}, functions := {.terminative},
    complements := {some .np} }

/-- The simple postpositions. -/
def inventory : List Adposition := [ne, ko, se, kaa, me, par, tak]

end HindiUrdu.Adpositions
