module

public import Linglib.Core.Combinatorics.SimpleGraph.Induce
public import Linglib.Core.Order.OrdConnected
public import Linglib.Syntax.Feature.Case.Function
public import Studies.Blake1994
public import Linglib.Languages.Japanese.Case
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Haspelmath (2003): semantic maps of dative and instrumental functions

A semantic map arranges the functions of grammatical morphemes as a graph on which each gram of
each language covers a contiguous area, a set of functions that induces a connected graph.
Haspelmath draws one for the functions datives typically have and one for the instrumental and its
neighbours, and [the datives](##connected_dativeGrams) and [the instrumentals and
comitatives](##connected_instrumentalGrams) he places on them are such areas. A map predicts by
the lines it lacks: with no line from purpose to anything but direction, [a gram with purpose and
another function has direction](##direction_mem_of_purpose_mem), the arrangement that [French *à*
and German *zu* select among the three orders of purpose, direction and recipient](##arrangement),
while on the map with all three lines [any two of them are a contiguous area](##vacuous).
Of the cases of the language files, [the Latin dative covers a contiguous area of the first map
but for its infrequent use for purpose](##latin_dative), and [Japanese *ni* does not of the
second](##japanese_ni).

## Implementation notes

A map has its own functions, at the grain at which some language tells them apart, so each map is
a graph on its own type of nodes, and `toFunction` gives the function of a case or adposition
each node stands for. Direction is motion to a goal in any configuration, and the source of the
instrumental map covers the giver of *a pension from the government* with the place of *aus
Paris*.

The chapter's universal for a chain of three functions, that a gram with the outer two has the
middle one, is formalized where the map has no other way round: for purpose behind direction and
for direction behind recipient. Both maps have a circle, and on each a gram of the chapter has
two functions without one between them: [the French dative clitics and *ek*](##around).

The areas are the closed curves of the figures. An implicational hierarchy is the stronger
statement that a pattern reaches back to the start of a chain, the lower sets among the areas of
a linear map, as [in the case hierarchy](##conforms_iff_connected).

## TODO

The grams of the figures are stated here as drawn. Of the language files' own cases and adpositions
only the Latin dative and Japanese *ni* list the functions of these maps from a grammar; the
English prepositions of the figures do not yet.

## References

* [haspelmath-2003]
* [blake-1994]
* [greenough-kittredge-howard-dooge-1903]
* [pinkster-2015]
* [pinkster-2021]
* [tsujimura-2014]
-/

@[expose] public section

namespace Haspelmath2003

open SimpleGraph

/-! ### The map of typical dative functions -/

/-- The functions of the map of typical dative functions (Fig. 8.1). -/
inductive DativeFunction where
  | direction
  | purpose
  | recipient
  | experiencer
  | predicativePossessor
  | externalPossessor
  | beneficiary
  | judicantis
  deriving DecidableEq, Fintype, Repr

namespace DativeFunction

/-- The function of a case or adposition a node stands for, direction as the goal with no
configuration. -/
def toFunction : DativeFunction → Case.Function
  | direction => .spatial none .goal
  | purpose => .purpose
  | recipient => .argument .R
  | experiencer => .experiencer
  | predicativePossessor => .predicativePossessor
  | externalPossessor => .externalPossessor
  | beneficiary => .beneficiary
  | judicantis => .judicantis

/-- The node a function belongs to, a goal in any configuration to direction. -/
def ofFunction : Case.Function → Option DativeFunction
  | .spatial _ .goal => some direction
  | .purpose => some purpose
  | .argument .R => some recipient
  | .experiencer => some experiencer
  | .predicativePossessor => some predicativePossessor
  | .externalPossessor => some externalPossessor
  | .beneficiary => some beneficiary
  | .judicantis => some judicantis
  | _ => none

theorem ofFunction_toFunction (n : DativeFunction) : ofFunction n.toFunction = some n := by
  cases n <;> rfl

/-- The functions of the map among the functions of a case or adposition. -/
def area (fs : Finset Case.Function) : Finset DativeFunction :=
  Finset.univ.filter fun n ↦ ∃ f ∈ fs, ofFunction f = some n

end DativeFunction

open DativeFunction in
/-- The eight lines of the map of typical dative functions (Fig. 8.1). -/
def dativeEdges : Finset (Sym2 DativeFunction) :=
  {s(direction, recipient), s(direction, purpose), s(recipient, experiencer),
    s(recipient, predicativePossessor), s(predicativePossessor, externalPossessor),
    s(externalPossessor, beneficiary), s(recipient, beneficiary), s(beneficiary, judicantis)}

/-- The map of typical dative functions (Fig. 8.1).

```
            predicative possessor —— external possessor
                     |                     |
direction ——— recipient ——————————— beneficiary ——— judicantis
    |                |
 purpose        experiencer
```
-/
def dativeMap : SimpleGraph DativeFunction := .fromEdgeSet ↑dativeEdges

instance : DecidableRel dativeMap.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (↑dativeEdges : Set (Sym2 DativeFunction))).Adj)

section
open DativeFunction

/-- English *to* (Fig. 8.1). -/
def englishTo : Finset DativeFunction := {experiencer, recipient, direction, purpose}

/-- French *à* (Figs. 8.2, 8.5), which is not used for purpose but may be used for predicative
possession. -/
def frenchÀ : Finset DativeFunction := {predicativePossessor, experiencer, recipient, direction}

/-- The French dative clitics (Fig. 8.5), which do not express direction or predicative
possession but have the benefactive and external-possessor senses. -/
def frenchDative : Finset DativeFunction :=
  {externalPossessor, experiencer, beneficiary, recipient}

/-- German *zu*, which expresses purpose and direction but not recipient (p. 217). -/
def germanZu : Finset DativeFunction := {purpose, direction}

end

/-- English *to*, French *à*, the French dative clitics and German *zu* each cover a contiguous
area of the map of dative functions. -/
theorem connected_dativeGrams :
    ∀ g ∈ [englishTo, frenchÀ, frenchDative, germanZu], (dativeMap.induce ↑g).Connected := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    repeat' first
      | exact induce_coe_singleton_connected _
      | refine induce_coe_insert_connected ?_ (by decide)

/-! ### The map of instrumental and related functions -/

/-- The functions of the map of instrumental and related functions (Fig. 8.12). -/
inductive InstrumentalFunction where
  | recipient
  | beneficiary
  | cause
  | coAgent
  | conjunctive
  | comitative
  | instrumental
  | passiveAgent
  | source
  deriving DecidableEq, Fintype, Repr

namespace InstrumentalFunction

/-- The function of a case or adposition a node stands for, source as the source with no
configuration. -/
def toFunction : InstrumentalFunction → Case.Function
  | recipient => .argument .R
  | beneficiary => .beneficiary
  | cause => .cause
  | coAgent => .coAgent
  | conjunctive => .conjunctive
  | comitative => .comitative
  | instrumental => .instrumental
  | passiveAgent => .passiveAgent
  | source => .spatial none .source

/-- The node a function belongs to, a source in any configuration to source. -/
def ofFunction : Case.Function → Option InstrumentalFunction
  | .argument .R => some recipient
  | .beneficiary => some beneficiary
  | .cause => some cause
  | .coAgent => some coAgent
  | .conjunctive => some conjunctive
  | .comitative => some comitative
  | .instrumental => some instrumental
  | .passiveAgent => some passiveAgent
  | .spatial _ .source => some source
  | _ => none

theorem ofFunction_toFunction (n : InstrumentalFunction) : ofFunction n.toFunction = some n := by
  cases n <;> rfl

/-- The functions of the map among the functions of a case or adposition. -/
def area (fs : Finset Case.Function) : Finset InstrumentalFunction :=
  Finset.univ.filter fun n ↦ ∃ f ∈ fs, ofFunction f = some n

end InstrumentalFunction

open InstrumentalFunction in
/-- The ten lines of the map of instrumental and related functions (Fig. 8.12). -/
def instrumentalEdges : Finset (Sym2 InstrumentalFunction) :=
  {s(recipient, beneficiary), s(beneficiary, cause), s(recipient, coAgent),
    s(coAgent, comitative), s(conjunctive, comitative), s(comitative, instrumental),
    s(instrumental, passiveAgent), s(passiveAgent, cause), s(passiveAgent, source),
    s(cause, source)}

/-- The map of instrumental and related functions (Fig. 8.12).

```
               recipient ——— beneficiary ——————————— cause
                   |                                /     \
               co-agent                            /       \
                   |                              /         \
conjunctive —— comitative —— instrumental —— passive agent —— source
```
-/
def instrumentalMap : SimpleGraph InstrumentalFunction := .fromEdgeSet ↑instrumentalEdges

instance : DecidableRel instrumentalMap.Adj :=
  inferInstanceAs
    (DecidableRel (fromEdgeSet (↑instrumentalEdges : Set (Sym2 InstrumentalFunction))).Adj)

section
open InstrumentalFunction

/-- English *with* (Fig. 8.13). -/
def englishWith : Finset InstrumentalFunction := {coAgent, comitative, instrumental}

/-- French *par* (Fig. 8.13). -/
def frenchPar : Finset InstrumentalFunction := {passiveAgent, cause}

/-- German *aus* (Fig. 8.13). -/
def germanAus : Finset InstrumentalFunction := {cause, source}

/-- German *von* (Fig. 8.13). -/
def germanVon : Finset InstrumentalFunction := {passiveAgent, source}

/-- Seychelles Creole *ek* (Fig. 8.14), every function of the map but beneficiary. -/
def seychellesEk : Finset InstrumentalFunction :=
  {recipient, coAgent, conjunctive, comitative, instrumental, passiveAgent, cause, source}

/-- Russian *s* 'with' (Fig. 8.15). -/
def russianS : Finset InstrumentalFunction := {conjunctive, coAgent, comitative}

/-- The Russian instrumental case (Fig. 8.15). -/
def russianInstrumental : Finset InstrumentalFunction := {instrumental, passiveAgent}

end

/-- English *with*, French *par*, German *aus* and *von*, Seychelles Creole *ek*, Russian *s* and
the Russian instrumental each cover a contiguous area of the map of instrumental functions. -/
theorem connected_instrumentalGrams :
    ∀ g ∈ [englishWith, frenchPar, germanAus, germanVon, seychellesEk, russianS,
        russianInstrumental],
      (instrumentalMap.induce ↑g).Connected := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat' first
      | exact induce_coe_singleton_connected _
      | refine induce_coe_insert_connected ?_ (by decide)

/-! ### What the maps predict -/

section Predictions

open DativeFunction

variable {t : Set DativeFunction} {f : DativeFunction}

/-- A gram with purpose and another function has direction: with no line from purpose to
recipient, no gram expresses the two without direction (p. 218). -/
theorem direction_mem_of_purpose_mem (h : (dativeMap.induce t).Connected) (hp : purpose ∈ t)
    (hf : f ∈ t) (hne : f ≠ purpose) : direction ∈ t := by
  obtain ⟨a, -, b, hb, rfl, -, hab⟩ :=
    exists_adj_of_induce_preconnected h.preconnected (t := {purpose}) hp rfl hf hne
  have key : ∀ b, dativeMap.Adj purpose b → b = direction := by decide
  exact key b hab ▸ hb

-- p. 233, the chain of direction, recipient and predicative possessor
theorem recipient_mem_of_direction_mem (h : (dativeMap.induce t).Connected) (hd : direction ∈ t)
    (hf : f ∈ t) (hne : f ≠ direction) (hne' : f ≠ purpose) : recipient ∈ t := by
  obtain ⟨a, -, b, hb, ha, hb', hab⟩ :=
    exists_adj_of_induce_preconnected h.preconnected (t := {direction, purpose}) hd (by simp) hf
      (by simp [hne, hne'])
  have key : ∀ a b, a = direction ∨ a = purpose → ¬ (b = direction ∨ b = purpose) →
      dativeMap.Adj a b → b = recipient := by decide
  exact key a b ha hb' hab ▸ hb

/-- The chain of three functions with `b` in the middle. -/
def chain (a b c : DativeFunction) : SimpleGraph DativeFunction :=
  .fromEdgeSet ↑({s(a, b), s(b, c)} : Finset (Sym2 DativeFunction))

instance (a b c : DativeFunction) : DecidableRel (chain a b c).Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet
    (↑({s(a, b), s(b, c)} : Finset (Sym2 DativeFunction)) : Set (Sym2 DativeFunction))).Adj)

/-- Of the three orders of purpose, direction and recipient, *à*, with direction and recipient
but not purpose, is not a contiguous area on the one with purpose in the middle, nor *zu*, with
purpose and direction but not recipient, on the one with recipient in the middle; the map has
the third ((4), p. 217). -/
theorem arrangement :
    ¬ ((chain direction purpose recipient).induce {direction, recipient}).Connected ∧
      ¬ ((chain direction recipient purpose).induce {purpose, direction}).Connected ∧
      chain purpose direction recipient ≤ dativeMap ∧
      direction ∈ frenchÀ ∧ recipient ∈ frenchÀ ∧ purpose ∉ frenchÀ ∧
      germanZu = {purpose, direction} := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, rfl⟩
  · rw [induce_pair_connected_iff (by decide)]; decide
  · rw [induce_pair_connected_iff (by decide)]; decide
  · intro a b; revert a b; decide

-- With a line added from recipient to purpose, any two of purpose, direction and recipient are
-- a contiguous area, so the map excludes no gram (Fig. 8.4).
theorem vacuous : ∀ a ∈ [purpose, direction, recipient], ∀ b ∈ [purpose, direction, recipient],
    a ≠ b → ((chain purpose direction recipient ⊔ fromEdgeSet {s(recipient, purpose)}).induce
      {a, b}).Connected := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> intro h <;>
    first
      | exact absurd rfl h
      | exact induce_pair_connected_of_adj (by simp [chain])

end Predictions

/-! ### Circles

Each map has a circle, recipient, predicative possessor, external possessor and beneficiary on
the first and recipient, beneficiary, cause, passive agent, instrumental, comitative and co-agent
on the second, and a gram can cover two functions of a circle the other way round: the French
dative clitics have recipient and external possessor without predicative possessor, and *ek* has
recipient and cause without beneficiary. -/

theorem around :
    (.recipient ∈ frenchDative ∧ .externalPossessor ∈ frenchDative ∧
        .predicativePossessor ∉ frenchDative) ∧
      .recipient ∈ seychellesEk ∧ .cause ∈ seychellesEk ∧ .beneficiary ∉ seychellesEk := by
  decide

/-! ### Two cases of the language files

The chapter places no Latin or Japanese gram on its maps. In the prose of the grammar the Latin
dative has every function of the first map but direction, which is left to the poets. Its use
for purpose is confined to gerund and gerundive clauses and is not frequent; with it the dative
has purpose without the one function purpose is linked to, and without it the dative has the
recipient with the five functions linked to it or to beneficiary. The Japanese dative particle
*ni* has recipient and passive agent, which the second map joins only through functions *ni*
does not have. -/

/-- The Latin dative marks every function of the map of dative functions but direction. With
its infrequent use for purpose it does not cover a contiguous area of the map; its other
functions are one. -/
theorem latin_dative :
    DativeFunction.area (Latin.Case.functions .dat) = Finset.univ.erase .direction ∧
      ¬ (dativeMap.induce ↑(DativeFunction.area (Latin.Case.functions .dat))).Connected ∧
      (dativeMap.induce
        ↑((DativeFunction.area (Latin.Case.functions .dat)).erase .purpose)).Connected := by
  have h : DativeFunction.area (Latin.Case.functions .dat) = Finset.univ.erase .direction := by
    decide
  have h' : (Finset.univ.erase DativeFunction.direction).erase .purpose =
      {.judicantis, .externalPossessor, .predicativePossessor, .experiencer, .beneficiary,
        .recipient} := by decide
  refine ⟨h, fun hc ↦ ?_, ?_⟩
  · have := direction_mem_of_purpose_mem (f := .recipient) hc (by rw [h]; decide)
      (by rw [h]; decide) (by decide)
    rw [h] at this
    exact absurd this (by decide)
  · rw [h, h']
    repeat' first
      | exact induce_coe_singleton_connected _
      | refine induce_coe_insert_connected ?_ (by decide)

theorem japanese_ni :
    InstrumentalFunction.area (Japanese.Case.functions .dat) = {.recipient, .passiveAgent} ∧
      ¬ (instrumentalMap.induce
        ↑(InstrumentalFunction.area (Japanese.Case.functions .dat))).Connected := by
  have h : InstrumentalFunction.area (Japanese.Case.functions .dat) =
      {.recipient, .passiveAgent} := by decide
  refine ⟨h, ?_⟩
  rw [h, Finset.coe_insert, Finset.coe_singleton, induce_pair_connected_iff (by decide)]
  decide

/-! ### Hierarchies

An implicational hierarchy differs from a map in that one item predicts all items up to the
beginning of the hierarchy, not just a contiguous part of it (p. 238). [blake-1994]'s case
hierarchy is one: a case system conforms to it exactly when the positions it fills are none or a
contiguous area of the chain of positions that contains the first, the nominative. -/

open Blake1994 in
theorem conforms_iff_connected {inv : Finset Case} :
    Conforms inv ↔ positions inv = ∅ ∨
      ((hasse Position).induce ↑(positions inv)).Connected ∧ Position.nom ∈ positions inv := by
  rcases (positions inv).eq_empty_or_nonempty with h | h
  · simp [Conforms, h, isLowerSet_empty]
  · rw [Conforms, isLowerSet_iff_ordConnected_and_bot_mem (Finset.coe_nonempty.2 h),
      induce_hasse_connected_iff]
    simp [h, h.ne_empty]

end Haspelmath2003
