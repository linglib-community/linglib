module

public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Semantics.Events.Path

/-!
# Dutch adpositions

A Dutch adposition is the root `Adposition`, as Broekhuis and Corver's grammar describes it,
with the direction of the path a spatial use denotes in each position it takes, and with whether
its complement can be replaced by an R-word such as *er*. A spatial use is locational or
directional, and every postpositional use is directional, so *op* is locational in *op de berg*
'on the mountain' and denotes a goal path in *de berg op* 'up the mountain'. Every postposition
but *af* 'off' is also a preposition, and the complement of a non-spatial preposition such as
*tijdens* 'during' cannot be R-pronominalized.

## Main definitions

* `Dutch.Adposition`: the entry.
* `Dutch.Adpositions.inventory`: the entries.

## Main results

* `Dutch.Adpositions.direction_post_ne_place`: every postpositional use denotes a path.
* `Dutch.Adpositions.pre_of_post`: every postposition but *af* is also a preposition.
* `Dutch.Adpositions.not_isSpatial_of_not_rPronoun`: the adpositions that resist
  R-pronominalization are non-spatial.

## Implementation notes

* The values an entry marks are those of the uses its docstring lists: *voor* marks a place,
  'in front of', a time, 'before', and a beneficiary, 'for'. The spatial values are computed
  from the directions, by the case that expresses a direction with no localization
  (`Case.ofDir`), since the grammar does not record the localization; *door* marks a cause
  and a means besides its spatial uses, and its agent use has no comparative value. The
  grammar's complement types are the root's, a *te*-infinitive counting as a clause.
* The direction of a position records the grammar's classification of the use as locational or
  directional and, for a directional use, whether the complement is the endpoint, the starting
  point or a point on the path. The directional prepositions are the eight the grammar tests
  against verbs of location; *door* 'through', which the grammar marks as both, is recorded as
  locational, and *over* is two entries as in the grammar. The direction of a postpositional
  use is read off the grammar's gloss.
* A circumposition is an entry with a complex form and the circumpositional position, recorded
  with the direction of its directional use, since the grammar suspects that the locational
  uses of the circumpositions that have one are prepositional phrases with a particle.
* An entry used with its complement omitted records `none` among its complements, and one
  with no other complement is a particle; the grammar says that a particle has lost some of
  the spatial meaning of the adposition it is related to, and this file does not draw that
  line, recording only that the entry occurs without a complement.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VII: Adpositions and Adpositional
  Phrases* (2026)][broekhuis-corver-2026c]
-/

@[expose] public section

namespace Dutch

/-- A Dutch adposition is the root entry with, for each position relative to its complement,
the direction of the path a spatial use there denotes, and with whether its complement can be
R-pronominalized. -/
structure Adposition extends _root_.Adposition where
  /-- `direction l` is `.place` when a use in position `l` is locational and `.goal`, `.source`
  or `.route` when it denotes a path whose endpoint, starting point or interior is the
  reference object; a position the entry does not take is `.place`. -/
  direction : _root_.Adposition.Linearization → Spatial.Path.Direction := fun _ ↦ .place
  /-- The complement can be replaced by an R-word, as *met de pop* 'with the doll' beside *er
  ... mee* 'with it'. -/
  rPronoun : Bool := true

/-- `a.bare` is `a` used also with its complement omitted. -/
def Adposition.bare (a : Adposition) : Adposition :=
  { a with complements := insert none a.complements }

/-- `a.marks c` is `a` marking `c` as well. -/
def Adposition.marks (a : Adposition) (c : Case) : Adposition :=
  { a with functions := insert c a.functions }

namespace Adpositions

/-- `preposition form functions` is the preposition over a noun phrase marking `functions`,
by default a locational one. -/
def preposition (form : String) (functions : Finset Case := {.loc}) : Adposition :=
  { morphs := [.free form], linearization := {.pre}, functions, complements := {some .np} }

/-- `directional form d` is the preposition over a noun phrase denoting a path in direction
`d`. -/
def directional (form : String) (d : Spatial.Path.Direction) : Adposition :=
  { preposition form {Case.ofDir d} with direction := fun _ ↦ d }

/-- `ambipositional form d` is the spatial adposition over a noun phrase that is locational
before its complement and denotes a path in direction `d` after it. -/
def ambipositional (form : String) (d : Spatial.Path.Direction) : Adposition :=
  { preposition form {.loc, Case.ofDir d} with
    linearization := {.pre, .post}, direction := fun | .post => d | _ => .place }

/-- `circumposition first second d` is the circumposition *first … second* over a noun phrase,
denoting a path in direction `d`, or locational when `d` is `.place`. -/
def circumposition (first second : String) (d : Spatial.Path.Direction) : Adposition :=
  { morphs := [.free first, .free second], linearization := {.circum},
    functions := {Case.ofDir d}, complements := {some .np},
    direction := fun | .circum => d | _ => .place }


/-! ### Spatial adpositions

The locational prepositions are the deictic *achter*, *naast* and *voor*, the absolute *boven*,
*om*, *onder*, *rond* and *tussen*, and the inherent *aan*, *bij*, *binnen*, *buiten*, *door*,
*in*, *langs*, *op*, *over*, *tegen*, *tegenover* and *uit*, with *beneden* 'below', the
counterpart of *boven*, listed beside them; the directional prepositions are
*naar* and *tot*, whose complement is the endpoint, *van*, *vanaf* and *vanuit*, whose
complement is the starting point, and *over*, *via* and *voorbij*, whose complement lies on
the path. -/

/-- *aan* 'on' is a locational preposition, also used without its complement, *Jan doet een jas
aan* 'Jan puts on a coat', and the second part of *achter … aan* and *tegen … aan*. -/
def aan : Adposition := (preposition "aan").bare

/-- *achter* 'behind' is a deictic locational preposition, *Jan staat achter de auto* 'Jan
stands behind the car', and the particle of *achter blijven* 'lag behind'. -/
def achter : Adposition := (preposition "achter").bare

/-- *beneden* 'below' is a locational preposition, *Jan bevindt zich beneden de grote rivieren*
'Jan is south of the big rivers', and is used without its complement, *de kamer beneden* 'the
room downstairs'. -/
def beneden : Adposition := (preposition "beneden").bare

/-- *bij* 'near' is a locational preposition, also used without its complement, *het
postkantoor is dicht bij* 'the post office is close by'. -/
def bij : Adposition := (preposition "bij").bare

/-- *binnen* 'inside' is locational before its complement and denotes a goal path after it,
*het huis binnen* 'into the house', and is the particle of *binnen komen* 'come in'. -/
def binnen : Adposition := (ambipositional "binnen" .goal).bare

/-- *boven* 'above' is a locational preposition, *de lamp hangt boven de kast* 'the lamp hangs
above the cupboard', and the particle of *boven komen* 'come to the surface'. -/
def boven : Adposition := (preposition "boven").bare

/-- *buiten* 'outside' is a locational preposition and the particle of *buiten komen* 'get
outside'. -/
def buiten : Adposition := (preposition "buiten").bare

/-- *door* 'through' is locational before its complement, where the grammar marks it directional
as well, and denotes a route after it, *het hek door* 'through the gate' and the temporal *het
hele jaar door* 'throughout the year'. It takes a finite clause in *doordat* 'because' and a
*te*-infinitive, *door hard te werken* 'by working hard', is the particle of *door lopen* 'keep
walking', and is the second part of *onder … door* and *tussen … door*. -/
def door : Adposition :=
  ({ ((ambipositional "door" .route).marks .caus).marks .inst with
    complements := {some .np, some .clause} } : Adposition).bare

/-- *in* 'in' is locational before its complement and denotes a goal path after it, *de sloot
in* 'into the ditch' and the temporal *het nieuwe jaar in* 'into the new year', and is the
particle of *iets in brengen* 'introduce something'. -/
def in_ : Adposition := ((ambipositional "in" .goal).marks .tem).bare

/-- *langs* 'along' is locational before its complement, *de ladder ligt langs de muur* 'the
ladder lies along the wall', denotes a route after it, *het huis langs* 'along the house', and
is the particle of *bij iemand langs gaan* 'check on someone'. -/
def langs : Adposition := (ambipositional "langs" .route).bare

/-- *naar* 'to' denotes a path whose endpoint is its complement, *Jan rijdt naar Groningen* 'Jan
is driving to Groningen', and is the first part of *naar … toe*. -/
def naar : Adposition := directional "naar" .goal

/-- *naast* 'next to' is a deictic locational preposition. -/
def naast : Adposition := preposition "naast"

/-- *om* 'around' is locational before its complement, *de mannen zitten om de tafel* 'the men
sit around the table', denotes a route after it, *de hoek om* 'around the corner', and is used
without its complement, *Jan doet een das om* 'Jan puts on a scarf'. It is also temporal, 'at',
and marks a purpose. -/
def om : Adposition := ((ambipositional "om" .route).marks .tem).bare

/-- *onder* 'under' is a locational preposition, *de bal ligt onder de kast* 'the ball lies
under the cupboard', and the first part of *onder … door*. -/
def onder : Adposition := preposition "onder"

/-- *op* 'on' is locational before its complement and denotes a goal path after it, *op de berg*
'on the mountain' against *de berg op* 'up the mountain', and is used without its complement,
*Jan zet een hoed op* 'Jan puts a hat on'. It is also temporal. -/
def op : Adposition := ((ambipositional "op" .goal).marks .tem).bare

/-- *over* 'across', the grammar's first *over*, denotes a route before its complement and
after it, *het grasveld over* 'across the lawn', and is the first part of *over … heen*. -/
def over₁ : Adposition := { directional "over" .route with linearization := {.pre, .post} }

/-- *over* 'over', the grammar's second *over*, is a locational preposition. -/
def over₂ : Adposition := preposition "over"

/-- *rond* 'around' is locational before its complement, *de kaarsen staan rond de kerststal*
'the candles stand around the crib', and denotes a route after it, *het plein rond* 'around
the square'. -/
def rond : Adposition := ambipositional "rond" .route

/-- *tegen* 'against' is a locational preposition, *de ladder ligt tegen de muur* 'the ladder
lies against the wall', also temporal, 'towards', and the first part of *tegen … aan*, *tegen
… in* and *tegen … op*. -/
def tegen : Adposition := (preposition "tegen").marks .tem

/-- *tegenover* 'opposite' is a locational preposition. -/
def tegenover : Adposition := preposition "tegenover"

/-- *tot* 'until, as far as' denotes a path on which its complement is a point, the endpoint of
a part of the path, also temporally, and takes an adpositional phrase as well as a noun
phrase, as *van* does. -/
def tot : Adposition :=
  { (directional "tot" .goal).marks .tem with complements := {some .np, some .pp} }

/-- *tussen* 'between' is a locational preposition, *de lamp staat tussen twee vazen* 'the
lamp stands between two vases', also temporal, and the first part of *tussen … in* and
*tussen … door*. -/
def tussen : Adposition := (preposition "tussen").marks .tem

/-- *uit* 'out of' is locational before its complement in the grammar's classification and
denotes a source path after it, *de auto uit* 'out of the car' and the temporal *dag in dag
uit* 'day in day out', and is used without its complement, which it then cannot take. -/
def uit : Adposition := ((ambipositional "uit" .source).marks .tem).bare

/-- *van* 'from' denotes a path whose starting point is its complement, *Jan reed van Utrecht
naar Groningen* 'Jan drove from Utrecht to Groningen', and takes an adpositional phrase, *van
boven de kast* 'from above the cupboard'. It also marks a possessor, 'of', and is the first
part of *van … af*. -/
def van : Adposition :=
  { (directional "van" .source).marks .gen with complements := {some .np, some .pp} }

/-- *vanaf* 'from' denotes a path whose starting point is its complement, also temporally. -/
def vanaf : Adposition := (directional "vanaf" .source).marks .tem

/-- *vanuit* 'from out of' denotes a path whose starting point is its complement. -/
def vanuit : Adposition := directional "vanuit" .source

/-- *via* 'via' denotes a path on which its complement lies. -/
def via : Adposition := directional "via" .route

/-- *voor* 'in front of' is a deictic locational preposition, *Jan staat voor de auto* 'Jan
stands in front of the car', and also temporal, 'before'. Marking an intended goal, 'for', *de
koekjes zijn voor jou* 'the biscuits are for you', it takes an adpositional phrase, *voor na
het eten* 'for after dinner', and an adjective phrase, *voor hoe lang* 'for how long', and it
takes a finite clause in *voordat* 'before'. -/
def voor : Adposition :=
  { preposition "voor" {.loc, .tem, .ben} with
    complements := {some .np, some .pp, some .ap, some .clause} }

/-- *voorbij* 'past' denotes a path on which its complement lies, before its complement and
after it, *het huis voorbij* 'past the house'. -/
def voorbij : Adposition :=
  { directional "voorbij" .route with linearization := {.pre, .post} }

/-- *af* 'off' is the one postposition that is not also a preposition, denoting a source path,
*de berg af* 'down the mountain'; it is used without its complement, *Jan zet zijn hoed af*
'Jan takes his hat off', and is the second part of *van … af* and *op … af*. -/
def af : Adposition :=
  ({ preposition "af" {.abl} with
    linearization := {.post}, direction := fun | .post => .source | _ => .place } :
    Adposition).bare

/-- *heen* is a particle and the second part of *over … heen* and its kin, and is not an
adposition on its own. -/
def heen : Adposition :=
  { morphs := [.free "heen"], linearization := ∅, functions := ∅, complements := {none} }

/-- *toe* is a particle, the second part of *naar … toe* and the closing element of *tot (aan)
het einde (aan) toe* 'to the very end', and is not an adposition on its own. -/
def toe : Adposition :=
  { morphs := [.free "toe"], linearization := ∅, functions := ∅, complements := {none} }

/-! ### Circumpositions -/

/-- *van … af* 'from, off', *van het dak af springen* 'jump off the roof'. -/
def vanAf : Adposition := circumposition "van" "af" .source

/-- *onder … door* 'under and past', *onder de brug door lopen* 'walk under the bridge'. -/
def onderDoor : Adposition := circumposition "onder" "door" .route

/-- *tussen … door* 'through, between', *tussen de bomen door lopen* 'walk between the trees',
and the temporal *tussen twee lessen door* 'in between two lessons'. -/
def tussenDoor : Adposition := (circumposition "tussen" "door" .route).marks .tem

/-- *over … heen* 'over, across', *over het hek heen springen* 'jump over the fence'. -/
def overHeen : Adposition := circumposition "over" "heen" .route

/-- *door … heen* 'through', *door het stof heen lopen* 'walk through the dust'. -/
def doorHeen : Adposition := circumposition "door" "heen" .route

/-- *om … heen* 'around', *om het huis heen lopen* 'walk around the house'. -/
def omHeen : Adposition := circumposition "om" "heen" .route

/-- *naar … toe* 'towards', *naar Peter toe lopen* 'walk towards Peter'. -/
def naarToe : Adposition := circumposition "naar" "toe" .goal

/-- *tussen … in* 'in between' is locational, *tussen twee meisjes in zitten* 'sit between two
girls'. -/
def tussenIn : Adposition := circumposition "tussen" "in" .place

/-! ### Temporal and other adpositions -/

/-- *na* 'after' is temporal and takes a finite clause in *nadat* 'after' and a *te*-infinitive,
*na zijn vader gekust te hebben* 'after having kissed his father'. -/
def na : Adposition := { preposition "na" {.tem} with complements := {some .np, some .clause} }

/-- *tijdens* 'during' is temporal and resists R-pronominalization, *tijdens de oorlog* 'during
the war' but not *er tijdens*. -/
def tijdens : Adposition := { preposition "tijdens" {.tem} with rPronoun := false }

/-- *met* 'with' marks an instrument or a companion, *Jan speelt met de pop* 'Jan plays with
the doll', and heads the absolute construction over a subject and its predicate, *met Jan
ziek* 'with Jan ill'. -/
def met : Adposition :=
  { preposition "met" {.inst, .com} with complements := {some .np, some .smallClause} }

/-- *zonder* 'without' takes a *te*-infinitive, *zonder iets te vragen* 'without asking
anything', heads an absolute construction like *met*, and resists R-pronominalization. -/
def zonder : Adposition :=
  { preposition "zonder" {.abess} with
    complements := {some .np, some .clause, some .smallClause}, rPronoun := false }

/-- *dankzij* 'thanks to' resists R-pronominalization. -/
def dankzij : Adposition := { preposition "dankzij" {.caus} with rPronoun := false }

/-- *namens* 'on behalf of' resists R-pronominalization. -/
def namens : Adposition := { preposition "namens" {.ben} with rPronoun := false }

/-- *ondanks* 'despite' resists R-pronominalization. -/
def ondanks : Adposition := { preposition "ondanks" ∅ with rPronoun := false }

/-- *ongeacht* 'regardless of' resists R-pronominalization. -/
def ongeacht : Adposition := { preposition "ongeacht" ∅ with rPronoun := false }

/-- *vanwege* 'because of' resists R-pronominalization. -/
def vanwege : Adposition := { preposition "vanwege" {.caus} with rPronoun := false }

/-- *volgens* 'according to' resists R-pronominalization. -/
def volgens : Adposition := { preposition "volgens" ∅ with rPronoun := false }

/-- *wegens* 'because of' resists R-pronominalization. -/
def wegens : Adposition := { preposition "wegens" {.caus} with rPronoun := false }

/-! ### The inventory -/

/-- `inventory` lists the entries. -/
def inventory : List Adposition :=
  [aan, achter, beneden, bij, binnen, boven, buiten, door, in_, langs, naar, naast, om, onder, op,
   over₁, over₂, rond, tegen, tegenover, tot, tussen, uit, van, vanaf, vanuit, via, voor,
   voorbij, af, heen, toe,
   vanAf, onderDoor, tussenDoor, overHeen, doorHeen, omHeen, naarToe, tussenIn,
   na, tijdens, met, zonder, dankzij, namens, ondanks, ongeacht, vanwege, volgens, wegens]

theorem direction_post_ne_place :
    ∀ a ∈ inventory, a.IsPostposition → a.direction .post ≠ .place := by
  decide

theorem pre_of_post :
    ∀ a ∈ inventory, a.IsPostposition → a.IsPreposition ∨ a.toAdposition = af.toAdposition := by
  decide

theorem circum_iff_isComplex :
    ∀ a ∈ inventory, a.IsCircumposition ↔ a.IsComplex := by
  decide

theorem complements_of_circum :
    ∀ a ∈ inventory, a.IsCircumposition → a.complements = {some .np} := by
  decide

theorem not_isSpatial_of_not_rPronoun :
    ∀ a ∈ inventory, a.rPronoun = false → ¬ a.IsSpatial := by
  decide

end Adpositions

end Dutch
