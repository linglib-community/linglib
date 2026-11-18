module

public import Studies.Haspelmath2003

/-!
# Malchukov & Narrog (2009): case polysemy

Malchukov and Narrog survey the semantic maps proposed for case functions and join them in a
general map of the major roles, on which [the cases of West Greenlandic and of Imbabura Quechua
each cover a contiguous area](##connected_systems). Its upper part, around the agent, and its
lower part, around the objects, [are joined by two routes only](##routes), through the material
and through the beneficiary. Of [haspelmath-2003]'s map of dative functions they take [the chain
of goal, recipient and beneficiary](##goal_recipient_beneficiary), which English *to* and the
Russian dative divide differently, and they note that the map may want a line from beneficiary
to purpose. With that line [the Latin dative covers a contiguous
area](##latin_dative_connected), which on the map as [haspelmath-2003] draws it it does not.

## Implementation notes

The chapter takes a map to state what is probable, since a gram may come to violate it when
another gram replaces it in some of its functions; the theorems here state contiguity on the maps
as drawn. The Latin dative's use for purpose is infrequent and confined to gerund and gerundive
clauses, and the dative of an abstract noun that the tradition calls a dative of purpose is for
[pinkster-2015] a use of the dative of the beneficiary. The general map
has no S, which the chapter does not take for a single role, and leaves out the experiencer and
the spatial functions but goal and source. The material or means of *load the cart with bricks*
has no function of a case or adposition in `Case.Function`.

## TODO

The chapter also notes a probable line from experiencer to beneficiary, which nothing here uses.

## References

* [malchukov-narrog-2009]
* [haspelmath-2003]
* [greenough-kittredge-howard-dooge-1903]
* [pinkster-2015]
-/

@[expose] public section

namespace MalchukovNarrog2009

open SimpleGraph

/-! ### The general map -/

/-- The roles of the general map (Fig. 34.8): the agent, the comitative, the instrument, the
possessor, the source, the material or means, the beneficiary, the theme, the recipient, the goal
and the patient. -/
inductive Role where
  | A
  | COM
  | INS
  | POS
  | SO
  | MAT
  | BEN
  | T
  | R
  | G
  | P
  deriving DecidableEq, Fintype, Repr

/-- The function of a case or adposition a role stands for, none for the material. -/
def Role.toFunction : Role → Option Case.Function
  | .A => some (.argument .A)
  | .COM => some .comitative
  | .INS => some .instrumental
  | .POS => some .possessor
  | .SO => some (.spatial none .source)
  | .MAT => none
  | .BEN => some .beneficiary
  | .T => some (.argument .T)
  | .R => some (.argument .R)
  | .G => some (.spatial none .goal)
  | .P => some (.argument .P)

open Role in
/-- The twelve lines of the general map (Fig. 34.8). -/
def generalEdges : Finset (Sym2 Role) :=
  {s(COM, INS), s(INS, A), s(A, POS), s(INS, SO), s(SO, POS), s(INS, MAT), s(MAT, T), s(T, P),
    s(P, R), s(R, G), s(POS, BEN), s(BEN, R)}

/-- The general map for the major roles (Fig. 34.8).

```
              A
            /   \
COM —— INS       POS
        |  \   /  |
        |   SO    |
       MAT       BEN
        |         |
        T         R —— G
          \     /
             P
```
-/
def generalMap : SimpleGraph Role := .fromEdgeSet ↑generalEdges

instance : DecidableRel generalMap.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet (↑generalEdges : Set (Sym2 Role))).Adj)

section
open Role

/-- The cases of West Greenlandic (Fig. 34.9): *-up* for the agent and the possessor, *-mit* for
the source, *-mik* for the instrument, the material and the theme, *-mut* for the beneficiary,
the recipient and the goal, and the unmarked case for the patient and the recipient. -/
def westGreenlandic : List (Finset Role) :=
  [{A, POS}, {SO}, {INS, MAT, T}, {BEN, R, G}, {P, R}]

/-- The cases of Imbabura Quechua (Fig. 34.10): the unmarked case for the agent, *-wan* for the
comitative, the instrument and the material, *manda* for the source, *-paj* for the possessor and
the beneficiary, *-ta* for the theme and the patient, and *-man* for the recipient and the
goal. -/
def imbaburaQuechua : List (Finset Role) :=
  [{A}, {COM, INS, MAT}, {SO}, {POS, BEN}, {T, P}, {R, G}]

end

/-- Each case of West Greenlandic and of Imbabura Quechua covers a contiguous area of the general
map. -/
theorem connected_systems :
    ∀ g ∈ westGreenlandic ++ imbaburaQuechua, (generalMap.induce ↑g).Connected := by
  simp only [westGreenlandic, imbaburaQuechua, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat' first
      | exact induce_coe_singleton_connected _
      | refine induce_coe_insert_connected ?_ (by decide)

/-- The upper part of the map, the agent with the comitative, the instrument, the possessor and
the source, has no line to the lower part, the theme, the patient, the recipient and the goal:
the two are joined through the material and through the beneficiary (p. 531). -/
theorem routes :
    (∀ a ∈ [Role.A, .COM, .INS, .POS, .SO], ∀ b ∈ [Role.T, .P, .R, .G], ¬ generalMap.Adj a b) ∧
      generalMap.Adj .INS .MAT ∧ generalMap.Adj .MAT .T ∧
      generalMap.Adj .POS .BEN ∧ generalMap.Adj .BEN .R := by
  decide

/-! ### The dative functions -/

section Dative

open Haspelmath2003 Haspelmath2003.DativeFunction

/-- The Russian dative (Fig. 34.7). -/
def russianDative : Finset DativeFunction :=
  {externalPossessor, experiencer, beneficiary, recipient}

/-- Goal, recipient and beneficiary form a chain with recipient in the middle, a part of the map
of dative functions: English *to* has goal and recipient without beneficiary, and the Russian
dative recipient and beneficiary without goal (p. 520). -/
theorem goal_recipient_beneficiary :
    chain direction recipient beneficiary ≤ dativeMap ∧
      (direction ∈ englishTo ∧ recipient ∈ englishTo ∧ beneficiary ∉ englishTo) ∧
      recipient ∈ russianDative ∧ beneficiary ∈ russianDative ∧ direction ∉ russianDative := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro a b; revert a b; decide

/-- The map of dative functions with the line from beneficiary to purpose that the chapter
suggests might be posited (p. 528, n. 14). -/
def dativeMapWithPurpose : SimpleGraph DativeFunction :=
  .fromEdgeSet ↑(insert s(beneficiary, purpose) dativeEdges)

instance : DecidableRel dativeMapWithPurpose.Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet
    (↑(insert s(beneficiary, purpose) dativeEdges) : Set (Sym2 DativeFunction))).Adj)

/-- With a line from beneficiary to purpose the Latin dative, which has purpose without
direction, covers a contiguous area of the map of dative functions. -/
theorem latin_dative_connected :
    (dativeMapWithPurpose.induce ↑(DativeFunction.area (Latin.Case.functions .dat))).Connected := by
  have h : Finset.univ.erase DativeFunction.direction =
      {purpose, judicantis, externalPossessor, predicativePossessor, experiencer, beneficiary,
        recipient} := by decide
  rw [latin_dative.1, h]
  repeat' first
    | exact induce_coe_singleton_connected _
    | refine induce_coe_insert_connected ?_ (by decide)

end Dative

end MalchukovNarrog2009
