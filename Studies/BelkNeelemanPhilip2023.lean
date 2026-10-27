/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Belk, Neeleman and Philip (2023): What Divides, and What Unites, Right-Node Raising

Right-node raising (*John likes, and Mary dislikes, opera*) shows properties of ellipsis, such as
morphological mismatches and vehicle change, and properties of multidominance, such as cumulative
agreement and internal readings of *same*. Belk, Neeleman and Philip argue that it comes from
either source, and that one pruning rule at PF unites the two. The rule removes a branch of the
first conjunct when a corresponding branch of the second can stand in for it without disturbing
the first conjunct's word order. Applied to a branch pointing to multidominated material, pruning
is forced, since the structure could not otherwise be linearized without crossing branches;
applied to a branch with a counterpart of its own, it leaves an orphan that goes unrealized, which
is ellipsis. Forced pruning comes first, so a constituent elided in the first conjunct can contain
a multidominated pivot only at its right edge, and a finite pivot, which ellipsis cannot create,
contains no further pivot.

## Implementation notes

* A derivation is a linearized syntactic object, multidominated material shared, with its forced and
  its free prunings, each pairing a pruned branch of the first conjunct with its proxy in the
  second. That the conjuncts are parallel, a condition the paper states in focus semantics, is
  assumed of the pairing.
* The coordinator and the matrix clauses of the paper's examples are left out, so a string is the
  conjuncts' words.
* A multidominated pivot requires a prosodic break at its onset, before its first word.

## References

* [Z. Belk, A. Neeleman and J. Philip, *What divides, and what unites, right-node raising*
  (2023)][belk-neeleman-philip-2023]
* [C. Wilder, *Right node raising and the LCA* (1999)][wilder-1999]
-/

@[expose] public section

namespace BelkNeelemanPhilip2023

open Minimalist Minimalist.LinearizedSyntacticObject Core.Order RoseTree

/-! ### Pruning -/

/-- A derivation of right-node raising is a coordination, the first conjunct at `[0]` and the
second at `[1]`, with the branches it prunes, each paired with its proxy in the second conjunct:
first the branches to multidominated material, then the free ones. -/
structure Derivation where
  /-- The coordination, multidominated material shared. -/
  input : LinearizedSyntacticObject
  /-- The branches to multidominated material, with their proxies. -/
  forced : List (TreePath × TreePath)
  /-- The branches whose material goes unrealized, with their proxies. -/
  free : List (TreePath × TreePath)

/-- `x` precedes `y` in the linear order of a tree, lexicographically by address. -/
def Precedes (x y : TreePath) : Prop := x.toList < y.toList

instance (x y : TreePath) : Decidable (Precedes x y) := inferInstanceAs (Decidable (_ < _))

/-- Where material of the first conjunct at `x` is realized once the branches `P` are pruned:
inside a pruned branch, at the corresponding position under its proxy. -/
def realizedAt (P : List (TreePath × TreePath)) (x : TreePath) : TreePath :=
  match P.find? (decide <| ·.1 ≤ x) with
  | some (p, q) => ⟨q.toList ++ x.toList.drop p.toList.length⟩
  | none => x

/-- The pruning rule (86). After the prunings `P`, the branch at `p` may be pruned with proxy `q`
when `p` lies inside the first conjunct and `q` inside the second, and the proxy's yield satisfies
the ordering statements of `p`'s yield in the first conjunct: pronounced material of the first
conjunct that precedes `p` is realized before `q`, and material that follows `p` after it. -/
def MayPrune (t : LinearizedSyntacticObject) (P : List (TreePath × TreePath)) (p q : TreePath) :
    Prop :=
  p.toList.head? = some 0 ∧ 1 < p.toList.length ∧ q.toList.head? = some 1 ∧
    (subtreeAt t.val q.toList).isSome ∧
    ∀ x ∈ tokenList t.val, x.1.toList.head? = some 0 → ¬ p ≤ x.1 → x.2.item.phonForm?.isSome →
      (Precedes x.1 p → Precedes (realizedAt P x.1) q) ∧
        (Precedes p x.1 → Precedes q (realizedAt P x.1))

instance (t : LinearizedSyntacticObject) (P : List (TreePath × TreePath)) (p q : TreePath) :
    Decidable (MayPrune t P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace Derivation

variable (d : Derivation)

/-- All prunings, the forced ones first. -/
def prunings : List (TreePath × TreePath) := d.forced ++ d.free

/-- A derivation is licensed when each pruning obeys (86) given the ones before it; when forced
pruning removes branches to multidominated material, the same constituent as their proxies, and
free pruning branches with a counterpart of their own and no finite head, since a finite pivot
cannot be created through ellipsis (26); and when, as the No-Tangling Condition requires, no
multidominated token keeps a branch in the first conjunct. -/
def Licensed : Prop :=
  (∀ x ∈ d.prunings.zipIdx, MayPrune d.input (d.prunings.take x.2) x.1.1 x.1.2) ∧
    (∀ pq ∈ d.forced, subtreeAt d.input.val pq.1.toList = subtreeAt d.input.val pq.2.toList) ∧
    (∀ pq ∈ d.free, subtreeAt d.input.val pq.1.toList ≠ subtreeAt d.input.val pq.2.toList ∧
      ∀ x ∈ tokenList d.input.val, pq.1 ≤ x.1 → x.2.item.cat ≠ .T) ∧
    ∀ x ∈ tokenList d.input.val, x.1.toList.head? = some 0 → IsShared d.input x.2 →
      ∃ pq ∈ d.forced, pq.1 ≤ x.1

instance : Decidable d.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- The realized tokens, left to right, are those outside every pruned branch. -/
def yield : List LexicalItem.Token :=
  (tokenList d.input.val).filterMap fun x ↦
    if ∀ pq ∈ d.prunings, ¬ pq.1 ≤ x.1 then some x.2 else none

/-- The realized words, left to right. -/
def phon : List String := d.yield.filterMap (·.item.phonForm?)

/-- The first word of the first multidominated pivot, where a prosodic break falls. -/
def pivotOnset : Option String :=
  d.forced.head?.bind fun pq ↦ (subtreeAt d.input.val pq.2.toList).bind fun s ↦
    ((tokenList s).filterMap (·.2.item.phonForm?)).head?

end Derivation

/-! ### Multidominance and ellipsis (§§1, 7) -/

def john : LexicalItem.Token := ⟨.of .D [] "John", 1⟩
def likes : LexicalItem.Token := ⟨.of .V [.D] "likes", 2⟩
def mary : LexicalItem.Token := ⟨.of .D [] "Mary", 3⟩
def dislikes : LexicalItem.Token := ⟨.of .V [.D] "dislikes", 4⟩
/-- *Opera*, and a second token of it. -/
def opera : LexicalItem.Token := ⟨.of .D [] "opera", 5⟩
def opera' : LexicalItem.Token := ⟨.of .D [] "opera", 6⟩

/-- `[John likes x] and [Mary dislikes y]`. -/
def likesDislikes (x y : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  (john * (likes * x)) * (mary * (dislikes * y))

/-- Multidominance (84) puts one *opera* under both verbs and prunes the first branch (85). -/
def rnrMD : Derivation := ⟨likesDislikes opera opera, [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)], []⟩
/-- Ellipsis (88) has an *opera* in each conjunct and prunes the first, leaving it unrealized. -/
def rnrE : Derivation := ⟨likesDislikes opera opera', [], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩
/-- The gap in the second conjunct (89), by multidominance and by ellipsis. -/
def leftNodeMD : Derivation := ⟨likesDislikes opera opera, [(⟨[1, 1, 1]⟩, ⟨[0, 1, 1]⟩)], []⟩
def leftNodeE : Derivation := ⟨likesDislikes opera opera', [], [(⟨[1, 1, 1]⟩, ⟨[0, 1, 1]⟩)]⟩

theorem phon_rnrMD : rnrMD.phon = ["John", "likes", "Mary", "dislikes", "opera"] := by decide
theorem phon_rnrE : rnrE.phon = rnrMD.phon := by decide

/-- Both derivations of right-node raising are licensed. -/
theorem licensed_rnrMD : rnrMD.Licensed := by decide
theorem licensed_rnrE : rnrE.Licensed := by decide

-- (89)
theorem not_licensed_leftNode :
    ¬ leftNodeMD.Licensed ∧ ¬ leftNodeE.Licensed ∧
      ¬ (⟨rnrMD.input, [], []⟩ : Derivation).Licensed := by
  decide

def bought : LexicalItem.Token := ⟨.of .V [.D] "bought", 7⟩
def forMary : LexicalItem.Token := ⟨.of .P [] "for Mary", 8⟩
def bill : LexicalItem.Token := ⟨.of .D [] "Bill", 9⟩
def wrapped : LexicalItem.Token := ⟨.of .V [.D] "wrapped", 10⟩
/-- *A book about opera*, and a second token of it. -/
def aBook : LexicalItem.Token := ⟨.of .D [] "a book about opera", 11⟩
def aBook' : LexicalItem.Token := ⟨.of .D [] "a book about opera", 12⟩

/-- `[John [[bought x] for Mary]] and [Bill [wrapped y]]` (91). -/
def boughtWrapped (x y : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  (john * ((bought * x) * forMary)) * (bill * (wrapped * y))

/-- Material of the first conjunct follows the gap (90), so neither (91a) nor (91b) is licensed. -/
theorem not_licensed_gapBeforePP :
    ¬ (⟨boughtWrapped aBook aBook', [], [(⟨[0, 1, 0, 1]⟩, ⟨[1, 1, 1]⟩)]⟩ : Derivation).Licensed ∧
      ¬ (⟨boughtWrapped aBook aBook, [(⟨[0, 1, 0, 1]⟩, ⟨[1, 1, 1]⟩)], []⟩ :
        Derivation).Licensed := by
  decide

def flattered : LexicalItem.Token := ⟨.of .V [.D] "flattered", 13⟩
def disparaged : LexicalItem.Token := ⟨.of .V [.D] "disparaged", 14⟩
/-- *Excessively*, and a second token of it, and a second *John*. -/
def excessively : LexicalItem.Token := ⟨.of .A [] "excessively", 15⟩
def excessively' : LexicalItem.Token := ⟨.of .A [] "excessively", 16⟩
def john' : LexicalItem.Token := ⟨.of .D [] "John", 17⟩

/-- `[Mary [[flattered x] y]] and [Bill [[disparaged x'] y']]` (92). -/
def flatteredDisparaged (x y x' y' : LexicalItem.Token) : LinearizedSyntacticObject :=
  (mary * ((flattered * x) * y)) * (bill * ((disparaged * x') * y'))

/-- Two pivots, by ellipsis (92a) or multidominance (92b), pruning the adverb's branch before the
object's (93). -/
def twoPivotsE : Derivation :=
  ⟨flatteredDisparaged john excessively john' excessively', [],
    [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩), (⟨[0, 1, 0, 1]⟩, ⟨[1, 1, 0, 1]⟩)]⟩
def twoPivotsMD : Derivation :=
  ⟨flatteredDisparaged john excessively john excessively,
    [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩), (⟨[0, 1, 0, 1]⟩, ⟨[1, 1, 0, 1]⟩)], []⟩

theorem licensed_twoPivots :
    twoPivotsE.phon = ["Mary", "flattered", "Bill", "disparaged", "John", "excessively"] ∧
      twoPivotsMD.phon = twoPivotsE.phon ∧ twoPivotsE.Licensed ∧ twoPivotsMD.Licensed ∧
      ¬ (⟨twoPivotsE.input, [], twoPivotsE.free.reverse⟩ : Derivation).Licensed := by
  decide

/-! ### Ellipsis before multidominance (§5) -/

def she : LexicalItem.Token := ⟨.of .D [] "she", 18⟩
def isGoingTo : LexicalItem.Token := ⟨.of .T [.V] "is going to", 19⟩
def ryo : LexicalItem.Token := ⟨.of .D [] "Ryo", 20⟩
def willSoon : LexicalItem.Token := ⟨.of .T [.V] "will soon", 21⟩
/-- *Show*, and a second token of it. -/
def showV : LexicalItem.Token := ⟨.of .V [.D, .D] "show", 22⟩
def showV' : LexicalItem.Token := ⟨.of .V [.D, .D] "show", 23⟩
/-- The objects of (58), *Ava's supervisor* and *the same paper*, and of (61), *the same person*
and *Ava's paper*, each with a second token. -/
def supervisor : LexicalItem.Token := ⟨.of .D [] "Ava's supervisor", 24⟩
def supervisor' : LexicalItem.Token := ⟨.of .D [] "Ava's supervisor", 25⟩
def samePaper : LexicalItem.Token := ⟨.of .D [] "the same paper", 26⟩
def samePerson : LexicalItem.Token := ⟨.of .D [] "the same person", 42⟩
def avasPaper : LexicalItem.Token := ⟨.of .D [] "Ava's paper", 43⟩
def avasPaper' : LexicalItem.Token := ⟨.of .D [] "Ava's paper", 44⟩

/-- `[she [is going to [show [x y]]]] and [Ryo [will soon [show [x' y']]]]` (58), (61). -/
def showVP (x y x' y' : LexicalItem.Token) : LinearizedSyntacticObject :=
  (she * (isGoingTo * (showV * (x * y)))) * (ryo * (willSoon * (showV' * (x' * y'))))

/-- In (58) the verb phrase is an elided pivot, the indirect object showing vehicle change, and
the direct object at its right edge a multidominated pivot. -/
def pieBeforePim : Derivation :=
  ⟨showVP supervisor samePaper supervisor' samePaper,
    [(⟨[0, 1, 1, 1, 1]⟩, ⟨[1, 1, 1, 1, 1]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩
/-- In (61) the multidominated pivot, the indirect object, precedes the elided direct object. -/
def pimBeforePie : Derivation :=
  ⟨showVP samePerson avasPaper samePerson avasPaper',
    [(⟨[0, 1, 1, 1, 0]⟩, ⟨[1, 1, 1, 1, 0]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩

theorem phon_pieBeforePim : pieBeforePim.phon =
    ["she", "is going to", "Ryo", "will soon", "show", "Ava's supervisor", "the same paper"] := by
  decide

/-- A multidominated pivot may stand at the right edge of an elided pivot (49), with the
prosodic break before it. -/
theorem licensed_pieBeforePim :
    pieBeforePim.Licensed ∧ pieBeforePim.pivotOnset = some "the same paper" := by decide

/-- But not before material of the elided pivot, since forced pruning comes first, while the direct
object still follows the indirect one in the first conjunct. -/
theorem not_licensed_pimBeforePie :
    ¬ pimBeforePie.Licensed ∧
      ¬ MayPrune pimBeforePie.input [] ⟨[0, 1, 1, 1, 0]⟩ ⟨[1, 1, 1, 1, 0]⟩ := by
  decide

/-! ### Finite and nonfinite pivots (§5) -/

def she' : LexicalItem.Token := ⟨.of .D [] "she", 28⟩
def will : LexicalItem.Token := ⟨.of .T [.V] "will", 29⟩
def will' : LexicalItem.Token := ⟨.of .T [.V] "will", 30⟩
def could : LexicalItem.Token := ⟨.of .T [.V] "could", 31⟩
/-- The perfect auxiliary *have*, and a second one. -/
def haveAux : LexicalItem.Token := ⟨.of .V [.V] "have", 32⟩
def haveAux' : LexicalItem.Token := ⟨.of .V [.V] "have", 33⟩
def traveled : LexicalItem.Token := ⟨.of .V [.P] "traveled", 34⟩
def traveled' : LexicalItem.Token := ⟨.of .V [.P] "traveled", 35⟩
def travel : LexicalItem.Token := ⟨.of .V [.P] "travel", 36⟩
def travel' : LexicalItem.Token := ⟨.of .V [.P] "travel", 37⟩
def toP : LexicalItem.Token := ⟨.of .P [.D] "to", 38⟩
def the : LexicalItem.Token := ⟨.of .D [.N] "the", 39⟩
def same : LexicalItem.Token := ⟨.of .A [] "same", 40⟩
def country : LexicalItem.Token := ⟨.of .N [] "country", 41⟩

/-- The pivot *to the same country*, whose internal reading requires it to be multidominated. -/
def samePivot : LinearizedSyntacticObject := toP * (the * (same * country))

/-- Example (51) with the auxiliary phrase multidominated, and no ellipsis. -/
def shareAuxP : Derivation :=
  let a := haveAux * (traveled * samePivot)
  ⟨(she * (will * a)) * (she' * (could * a)), [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)], []⟩
/-- Example (51) with the verb phrase multidominated and the first auxiliary phrase elided. -/
def shareVP : Derivation :=
  let v := traveled * samePivot
  ⟨(she * (will * (haveAux * v))) * (she' * (could * (haveAux' * v))),
    [(⟨[0, 1, 1, 1]⟩, ⟨[1, 1, 1, 1]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩
/-- Example (51) with only the prepositional phrase multidominated. -/
def sharePP : Derivation :=
  ⟨(she * (will * (haveAux * (traveled * samePivot)))) *
      (she' * (could * (haveAux' * (traveled' * samePivot)))),
    [(⟨[0, 1, 1, 1, 1]⟩, ⟨[1, 1, 1, 1, 1]⟩)], [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)]⟩

/-- The three derivations of (51). -/
def derivations51 : List Derivation := [shareAuxP, shareVP, sharePP]

theorem phon_derivations51 : ∀ d ∈ derivations51, d.phon =
    ["she", "will", "she", "could", "have", "traveled", "to", "the", "same", "country"] := by
  decide

/-- The nonfinite pivot of (51) has three licensed derivations, which put the prosodic break
before *have*, *traveled* or *to*. -/
theorem pivotOnset_nonfinite : (∀ d ∈ derivations51, d.Licensed) ∧
    derivations51.map (·.pivotOnset) = [some "have", some "traveled", some "to"] := by
  decide

/-- Example (52), its finite pivot multidominated. -/
def finiteShareT : Derivation :=
  let t := will * (travel * samePivot)
  ⟨(john * t) * (ryo * t), [(⟨[0, 1]⟩, ⟨[1, 1]⟩)], []⟩
/-- Its rivals with the verb phrase or the prepositional phrase multidominated and the rest of the
finite pivot elided. -/
def finiteShareVP : Derivation :=
  let v := travel * samePivot
  ⟨(john * (will * v)) * (ryo * (will' * v)), [(⟨[0, 1, 1]⟩, ⟨[1, 1, 1]⟩)],
    [(⟨[0, 1]⟩, ⟨[1, 1]⟩)]⟩
def finiteSharePP : Derivation :=
  ⟨(john * (will * (travel * samePivot))) * (ryo * (will' * (travel' * samePivot))),
    [(⟨[0, 1, 1, 1]⟩, ⟨[1, 1, 1, 1]⟩)], [(⟨[0, 1]⟩, ⟨[1, 1]⟩)]⟩

/-- The finite pivot of (52) is multidominated as a whole, so its prosodic break cannot shift
rightward (26). -/
theorem pivotOnset_finite :
    finiteShareT.Licensed ∧ finiteShareT.pivotOnset = some "will" ∧
      ¬ finiteShareVP.Licensed ∧ ¬ finiteSharePP.Licensed := by
  decide

-- (26)
theorem mayPrune_finiteRivals : ∀ d ∈ [finiteShareVP, finiteSharePP],
    ∀ x ∈ d.prunings.zipIdx, MayPrune d.input (d.prunings.take x.2) x.1.1 x.1.2 := by
  decide

end BelkNeelemanPhilip2023
