module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# English adpositions

The central prepositions of English as `Adposition` entries, after the Cambridge Grammar. *At*,
*on* and *in* have distinct counterparts for the goal and the source of a change of location,
*to* and *from*, *onto* and *off*, *into* and *out*, and the only other source preposition is
*away*. The grammaticised *by*, *for*, *of* and *with* and the postposed *ago* complete the list.

## Main definitions

* `English.Adpositions.inventory`: the entries.

## Main results

* `English.Adpositions.cells_biUnion_functions`: the location, goal and source prepositions fill
  every localization.
* `English.Adpositions.exists_dirOf_eq_source_iff`: the source prepositions are *from*, *away*,
  *off* and *out*.

## Implementation notes

* An entry marks the values of the uses its docstring lists. Left out are the temporal uses,
  which extend the spatial ones, the static uses of *off*, *out* and *away*, and the uses with no
  comparative value, such as the passive agent of *by* and the *at* of *laugh at*.
* *Out of* is *out* with an *of* phrase as its complement, since *out* alone occurs without one.
* Which interval the measure phrase of *for*, *in* and *ago* measures (Dowty's tests,
  `Aspect.forXPrediction`) is left to the studies; *in years* is
  `English.PolarityItems.inYears`, and *before*, *since*, *until* and deadline *by* are
  `English.TemporalConnectives`.

## Errata

The Cambridge Grammar's second table is said to add *away* and the static uses of *off* and *on*
(p. 649); it adds those of *off* and *out*.

## References

* [huddleston-pullum-2002]
* [dowty-1979]
-/

@[expose] public section

namespace English

namespace Adpositions

/-! ### Location, goal and source -/

/-- *at* marks a point location, *I'm at Heathrow* ([huddleston-pullum-2002] pp. 648, 650), and
takes an obligatory complement (p. 635). -/
def at_ : Adposition :=
  { morphs := [.free "at"], linearization := {.pre}, functions := {.ade},
    complements := {some .np} }

/-- *to* marks the goal, *I went to Heathrow*, the recipient, *Give it to me*, and the endpoint of
a change of state, *The snow turned to water* ([huddleston-pullum-2002] pp. 648, 660); it takes an
adjective in *from bad to worse* (p. 638) and occurs without a complement only in secondary
senses, *He came to* (p. 613). -/
def to_ : Adposition :=
  { morphs := [.free "to"], linearization := {.pre}, functions := {.all, .dat, .transl},
    complements := {some .np, some .ap, none} }

/-- *from* marks the source, *I departed from Heathrow* ([huddleston-pullum-2002] p. 648), and
takes an adpositional phrase, *from behind the curtain* (p. 599), and an adjective, *from bad to
worse* (p. 638). -/
def from_ : Adposition :=
  { morphs := [.free "from"], linearization := {.pre}, functions := {.abl},
    complements := {some .np, some .pp, some .ap} }

/-- *on* marks location and goal on a surface, *It is on the floor*, *It fell on the floor*, and
occurs without a complement, *The roof is still on*, *She jumped on* ([huddleston-pullum-2002]
p. 648); it takes an interrogative clause, *We can't agree on whether we should call in the
police* (p. 599). -/
def on : Adposition :=
  { morphs := [.free "on"], linearization := {.pre}, functions := {.sup, .sub},
    complements := {some .np, some .clause, none} }

/-- *onto* marks the goal on a surface, *It fell onto the floor* ([huddleston-pullum-2002]
p. 648), and takes an obligatory complement (p. 635). -/
def onto : Adposition :=
  { morphs := [.free "onto"], linearization := {.pre}, functions := {.sub},
    complements := {some .np} }

/-- *off* marks the source on a surface, *I lifted it off the floor*, and occurs without a
complement, *I fell off* ([huddleston-pullum-2002] p. 648); it takes an *of* phrase in American
English only (p. 639). -/
def off : Adposition :=
  { morphs := [.free "off"], linearization := {.pre}, functions := {.del},
    complements := {some .np, some .pp, none} }

/-- *in* marks location and goal in an interior, *It is in the box*, *It fell in the box*, and
occurs without a complement, *The doctor is in* ([huddleston-pullum-2002] p. 648); it takes a
measure phrase, *I'll be ready in a few minutes* (p. 657). -/
def in_ : Adposition :=
  { morphs := [.free "in"], linearization := {.pre}, functions := {.ine, .ill},
    complements := {some .np, some .measure, none} }

/-- *into* marks the goal in an interior, *It fell into the box* ([huddleston-pullum-2002]
p. 648), and the result of a change of state, *the witch turned him into a frog*, which is an
object and not an adjective, *This turned your answer into correct* being ungrammatical
(p. 637). -/
def into : Adposition :=
  { morphs := [.free "into"], linearization := {.pre}, functions := {.ill, .transl},
    complements := {some .np} }

/-- *out* marks the source in an interior, *I took it out of the box*, and occurs without a
complement, *They won't come out* ([huddleston-pullum-2002] p. 648); its complement is an *of*
phrase, or a noun phrase mainly in American English, *He jumped out the window* (p. 639). -/
def out : Adposition :=
  { morphs := [.free "out"], linearization := {.pre}, functions := {.ela},
    complements := {some .pp, some .np, none} }

/-- *away* marks the source, *I walked away (from them)*, with a *from* phrase or no complement
([huddleston-pullum-2002] p. 648), and never a noun phrase (p. 614). -/
def away : Adposition :=
  { morphs := [.free "away"], linearization := {.pre}, functions := {.abl},
    complements := {some .pp, none} }

/-! ### Grammaticised prepositions -/

/-- *by* marks proximity, *by the wall*, motion past, *Many people passed by*, and the instrument
or means, *by hand*, *by unscrewing it*, and occurs without a complement, *They stood by*
([huddleston-pullum-2002] p. 655). -/
def by_ : Adposition :=
  { morphs := [.free "by"], linearization := {.pre}, functions := {.ade, .perl, .inst},
    complements := {some .np, some .clause, none} }

/-- *with* marks accompaniment, *Christopher Robin went down with Alice*, and the instrument,
*undo it with a pin* ([huddleston-pullum-2002] p. 661). -/
def with_ : Adposition :=
  { morphs := [.free "with"], linearization := {.pre}, functions := {.com, .inst},
    complements := {some .np} }

/-- *for* marks the beneficiary, *Say a prayer for me*, and the reason, *He wouldn't help for
some reason*, and takes a measure phrase, *We stayed for a week* ([huddleston-pullum-2002]
pp. 655–656). -/
def for_ : Adposition :=
  { morphs := [.free "for"], linearization := {.pre}, functions := {.ben, .caus},
    complements := {some .np, some .measure} }

/-- *of* relates a noun phrase to the noun heading a larger one, as the genitive does, *the death
of the emperor* beside *the emperor's death* ([huddleston-pullum-2002] p. 658), and heads the
complement of *out*, *because* and *instead* (p. 659). -/
def of_ : Adposition :=
  { morphs := [.free "of"], linearization := {.pre}, functions := {.gen},
    complements := {some .np} }

/-- *ago* follows its complement, a period of time, *She died ten years ago*
([huddleston-pullum-2002] p. 632). -/
def ago : Adposition :=
  { morphs := [.free "ago"], linearization := {.post}, functions := {.tem},
    complements := {some .measure} }

/-- The entries. -/
def inventory : List Adposition :=
  [at_, to_, from_, on, onto, off, in_, into, out, away, by_, with_, for_, of_, ago]

open Case (cells) in
/-- The location, goal and source prepositions fill every localization
([huddleston-pullum-2002] p. 648). -/
theorem cells_biUnion_functions :
    cells (inventory.toFinset.biUnion Adposition.functions) =
      .univ ×ˢ ({.place, .goal, .source} : Finset Spatial.Path.Direction) := by
  decide

/-- There are no source prepositions beside *from*, *away*, *off* and *out*
([huddleston-pullum-2002] p. 649). -/
theorem exists_dirOf_eq_source_iff : ∀ a ∈ inventory,
    (∃ c ∈ a.functions, c.dirOf = some .source) ↔ a ∈ [from_, away, off, out] := by
  decide

end Adpositions

end English
