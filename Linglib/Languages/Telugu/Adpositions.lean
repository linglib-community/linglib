module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Telugu postpositions

The postpositions *lō* 'in' and *nunci* 'from' as `Adposition` entries. Both follow the oblique
stem of the noun (Krishnamurti and Gwynn §9.14). They differ in boundness: *nunci* is a
postposition of the first type, which only occurs bound to an oblique stem and never as a
separate word, while *lō* is of the second type, a separate word that can also stand as an
adverbial noun (§§9.14–9.15). Aitha places the postpositions outside the noun's prosodic word,
so *nunci* is an enclitic and *lō* a free word.

## Main definitions

* `Telugu.Adpositions.inventory`: the postpositions.

## Implementation notes

* Krishnamurti and Gwynn spell *lō* as *loo* and give *nunci* the variant *ninci*.
* The inventory has the two postpositions of Aitha's paradigms; the grammar lists more of
  both types, *koosam* 'for', *too* 'with' and *kaNTe* 'than' among the first and *miida* 'on'
  and *kinda* 'under' among the second.

## References

* [krishnamurti-gwynn-1985]
* [aitha-2026]
-/

@[expose] public section

namespace Telugu.Adpositions

/-- *lō* 'in'. -/
def lō : Adposition :=
  { morphs := [.free "lō"], linearization := {.post}, functions := {.spatial none .place},
    complements := {some .np} }

/-- *nunci* 'from'. -/
def nunci : Adposition :=
  { morphs := [.encl "nunci"], linearization := {.post}, functions := {.spatial none .source},
    complements := {some .np} }

/-- The postpositions. -/
def inventory : List Adposition := [lō, nunci]

end Telugu.Adpositions
