module

public import Linglib.Core.Combinatorics.SimpleGraph.Induce
public import Linglib.Syntax.Case.Function
public import Studies.Blake1994
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Haspelmath (2003): semantic maps of dative and instrumental functions

A semantic map arranges the functions of grammatical morphemes as a graph on which each gram of
each language covers a contiguous area, a set of functions that induces a connected graph.
Haspelmath draws one for the functions datives typically have and one for the instrumental and its
neighbours, and [the datives](##connected_dativeGrams) and [the instrumentals and
comitatives](##connected_instrumentalGrams) he places on them are such areas. A map predicts by
the lines it lacks: with no line from purpose to anything but direction, [a gram with purpose and
another function has direction](##direction_mem_of_purpose_mem), the arrangement that [the French
and German prepositions select among the three orders of purpose, direction and
recipient](##arrangement), while the map with all three lines [excludes nothing](##vacuous).

## Implementation notes

The chapter's universal for a chain of three functions, that a gram with the outer two has the
middle one, is formalized where the middle function lies on every path between the outer two. On
the circular map of instrumental functions [*ek* covers recipient and cause without
beneficiary](##ek_recipient_cause), joined the other way round.

The areas are the closed curves of the figures. An implicational hierarchy is the stronger
statement that a pattern reaches back to the start of a chain, the lower sets among the areas of
a linear map, as [in the case hierarchy](##conforms_iff_connected).

## TODO

The grams are stated here as the figures draw them; the adpositions and cases of the fragments
do not yet list the functions of these maps.

## References

* [haspelmath-2003]
* [blake-1994]
-/

@[expose] public section

namespace Haspelmath2003

open Case (Function)
open Case.Function

/-! ### The functions and the maps -/

/-- The chapter's direction, motion to a goal. -/
abbrev direction : Function := .spatial none .goal

/-- The chapter's recipient, the recipient of a transfer. -/
abbrev recipient : Function := .argument .R

/-- The chapter's source. -/
abbrev source : Function := .spatial none .source

/-- The eight lines of the map of typical dative functions (Fig. 8.1). -/
def dativeEdges : Finset (Sym2 Function) :=
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
def dativeMap : SimpleGraph Function := .fromEdgeSet ↑dativeEdges

/-- The ten lines of the map of instrumental and related functions (Fig. 8.12). -/
def instrumentalEdges : Finset (Sym2 Function) :=
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
def instrumentalMap : SimpleGraph Function := .fromEdgeSet ↑instrumentalEdges

instance : DecidableRel dativeMap.Adj := fun f g ↦
  inferInstanceAs (Decidable (s(f, g) ∈ (↑dativeEdges : Set (Sym2 Function)) ∧ f ≠ g))

instance : DecidableRel instrumentalMap.Adj := fun f g ↦
  inferInstanceAs (Decidable (s(f, g) ∈ (↑instrumentalEdges : Set (Sym2 Function)) ∧ f ≠ g))

/-! ### The grams -/

/-- English *to* (Fig. 8.1). -/
def «to» : Finset Function := {experiencer, recipient, direction, purpose}

/-- French *à* (Fig. 8.2), which is not used for purpose but may be used for predicative
possession. -/
def à : Finset Function := {predicativePossessor, experiencer, recipient, direction}

/-- The French dative clitics (Fig. 8.5), which do not express direction or predicative
possession but have the benefactive and external-possessor senses. -/
def dativeClitic : Finset Function := {externalPossessor, experiencer, beneficiary, recipient}

/-- German *zu*, which expresses purpose and direction but not recipient (p. 217). -/
def zu : Finset Function := {purpose, direction}

/-- English *with* (Fig. 8.13). -/
def «with» : Finset Function := {coAgent, comitative, instrumental}

/-- French *par* (Fig. 8.13). -/
def par : Finset Function := {passiveAgent, cause}

/-- German *aus* (Fig. 8.13). -/
def aus : Finset Function := {cause, source}

/-- German *von* (Fig. 8.13). -/
def von : Finset Function := {passiveAgent, source}

/-- Seychelles Creole *ek* (Fig. 8.14), every function of the map but beneficiary. -/
def ek : Finset Function :=
  {recipient, coAgent, conjunctive, comitative, instrumental, passiveAgent, cause, source}

/-- Russian *s* 'with' (Fig. 8.15). -/
def s : Finset Function := {conjunctive, coAgent, comitative}

/-- The Russian instrumental case (Fig. 8.15). -/
def russianInstrumental : Finset Function := {instrumental, passiveAgent}

/-- English *to*, French *à*, the French dative clitics and German *zu* each cover a contiguous
area of the map of dative functions. -/
theorem connected_dativeGrams :
    ∀ g ∈ [«to», à, dativeClitic, zu], (dativeMap.induce ↑g).Connected := by
  have h₀ (f : Function) := SimpleGraph.induce_singleton_connected (G := dativeMap) f
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    «to», à, dativeClitic, zu]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (repeat rw [Finset.coe_insert]) <;> rw [Finset.coe_singleton]
  · refine .induce_insert (u := recipient) ?_ (by simp) (by decide)
    refine .induce_insert (u := direction) ?_ (by simp) (by decide)
    refine .induce_insert (u := purpose) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := recipient) ?_ (by simp) (by decide)
    refine .induce_insert (u := recipient) ?_ (by simp) (by decide)
    refine .induce_insert (u := direction) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := beneficiary) ?_ (by simp) (by decide)
    refine .induce_insert (u := recipient) ?_ (by simp) (by decide)
    refine .induce_insert (u := recipient) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := direction) (h₀ _) rfl (by decide)

/-- English *with*, French *par*, German *aus* and *von*, Seychelles Creole *ek*, Russian *s* and
the Russian instrumental each cover a contiguous area of the map of instrumental functions. -/
theorem connected_instrumentalGrams :
    ∀ g ∈ [«with», par, aus, von, ek, s, russianInstrumental],
      (instrumentalMap.induce ↑g).Connected := by
  have h₀ (f : Function) := SimpleGraph.induce_singleton_connected (G := instrumentalMap) f
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    «with», par, aus, von, ek, s, russianInstrumental]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (repeat rw [Finset.coe_insert]) <;>
    rw [Finset.coe_singleton]
  · refine .induce_insert (u := comitative) ?_ (by simp) (by decide)
    refine .induce_insert (u := instrumental) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := cause) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := source) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := source) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := coAgent) ?_ (by simp) (by decide)
    refine .induce_insert (u := comitative) ?_ (by simp) (by decide)
    refine .induce_insert (u := comitative) ?_ (by simp) (by decide)
    refine .induce_insert (u := instrumental) ?_ (by simp) (by decide)
    refine .induce_insert (u := passiveAgent) ?_ (by simp) (by decide)
    refine .induce_insert (u := source) ?_ (by simp) (by decide)
    refine .induce_insert (u := source) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := comitative) ?_ (by simp) (by decide)
    refine .induce_insert (u := comitative) (h₀ _) rfl (by decide)
  · refine .induce_insert (u := passiveAgent) (h₀ _) rfl (by decide)

/-! ### What the maps predict -/

theorem dativeMap_adj {f g : Function} :
    dativeMap.Adj f g ↔ s(f, g) ∈ dativeEdges ∧ f ≠ g := by
  rw [dativeMap, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]

theorem dativeMap_adj_purpose {g : Function} : dativeMap.Adj purpose g ↔ g = direction := by
  simp only [dativeMap_adj, dativeEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨h, -⟩
    simpa [direction, recipient] using h
  · rintro rfl
    simp [direction]

variable {t : Set Function}

/-- A gram with purpose and another function has direction: with no line from purpose to
recipient, no gram expresses the two without direction (p. 218). -/
theorem direction_mem_of_purpose_mem (h : (dativeMap.induce t).Connected) (hp : purpose ∈ t)
    {f : Function} (hf : f ∈ t) (hne : f ≠ purpose) : direction ∈ t := by
  obtain ⟨a, -, b, hb, rfl, -, hab⟩ :=
    SimpleGraph.exists_adj_of_induce_connected h (t := {purpose}) hp rfl hf hne
  exact dativeMap_adj_purpose.1 hab ▸ hb

/-- Of the three orders of purpose, direction and recipient, *à*, with direction and recipient
but not purpose, excludes the one with purpose in the middle, and *zu*, with purpose and
direction but not recipient, the one with recipient in the middle; the map has the third
((4), p. 217). -/
theorem arrangement :
    ¬ (SimpleGraph.fromEdgeSet {s(direction, purpose), s(purpose, recipient)}).Adj
        direction recipient ∧
      ¬ (SimpleGraph.fromEdgeSet {s(direction, recipient), s(recipient, purpose)}).Adj
        direction purpose ∧
      dativeMap.Adj direction recipient ∧ dativeMap.Adj direction purpose := by
  refine ⟨?_, ?_, by decide, by decide⟩ <;> simp [direction, recipient]

/-- With a line added from recipient to purpose every nonempty set of functions is a contiguous
area, so the map excludes no gram (Fig. 8.4). -/
theorem vacuous {t : Set Function} (ht : t.Nonempty) :
    ((⊤ : SimpleGraph Function).induce t).Connected :=
  SimpleGraph.induce_top_connected_iff.2 ht

theorem ek_recipient_cause : recipient ∈ ek ∧ cause ∈ ek ∧ beneficiary ∉ ek := by decide

/-! ### Hierarchies

An implicational hierarchy differs from a map in that one item predicts all items up to the
beginning of the hierarchy, not just a contiguous part of it (p. 238). [blake-1994]'s case
hierarchy is one: a case system conforms to it exactly when the positions it fills are none or a
contiguous area of the chain of positions that contains the first, the nominative. -/

open Blake1994 in
theorem conforms_iff_connected {inv : Finset Case} :
    Conforms inv ↔ positions inv = ∅ ∨
      ((SimpleGraph.hasse Position).induce ↑(positions inv)).Connected ∧
        Position.nom ∈ positions inv := by
  rcases (positions inv).eq_empty_or_nonempty with h | h
  · simp [Conforms, h, isLowerSet_empty]
  · rw [← Finset.mem_coe, show Position.nom = ⊥ from rfl,
      SimpleGraph.induce_hasse_connected_and_bot_mem_iff]
    simp [Conforms, h, h.ne_empty]

end Haspelmath2003
