module

public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Cinque 2005: Deriving Greenberg's Universal 20 and its exceptions

Of the 24 orders of demonstrative, numeral, adjective and noun, 14 are attested, in very
unequal numbers of languages, and Greenberg's Universal 20 in Hawkins's revision (1)
misdescribes the postnominal ones. The paper derives exactly the attested orders from one
order of Merge, `[Dem [Num [A [N]]]]` (7a), and leftward movement of the NP alone or of a phrase
containing it past each modifier in turn (7b): no movement and pied-piping of the whose-picture
type, `[NP [XP]]`, are unmarked; movement without pied-piping, pied-piping of the picture-of-who
type, `[XP [NP]]`, and partial rather than total raising are marked; head movement and movement
of a phrase without the overt NP are excluded, the asymmetry Kayne's antisymmetry imposes. Each
attested order has such a derivation and each unattested one would need a wrong order of Merge
(6a–x), and the number of marked options a derivation uses tracks frequency: none for the two
orders of very many languages, two for orders of few or very few.

`table` is (6) with each order's frequency and the count of marked options the paper's analysis
of it states; `stagesOf` enumerates the derivations of (7) on the substrate's `Derivation`, an
optional raise of any subtree containing the overt noun after each Merge, with the orders read
by the substrate's externalization, and `u20_reachable_iff_attested` is the paper's result. The
marked options are derived from the derivations rather than transcribed: raising the modifier's
whole complement pied-pipes, of the whose-picture type when the noun is its specifier, raising
a proper part strands, and a derivation is partial when the noun moves but not to the left
edge; `markedOptions` takes the least count over an order's derivations. The derived counts are
the paper's for every order with a stated count except (6w), which (7b-v) classes as partial
while the count omits it (`markedOptions_eq_stated`, `markedOptions_w`); with two marked
options rather than one, its very few languages fit the frequency claim `markedness_extremes`.
The paper's own derivations of (6a), (6o) and (6n) are `mergeOrder`, `derivation6o` and
`derivation6n`, the two pied-piping types each keeping the moved phrase's internal order. The
demonstrative is `Cat.Dem`.

## References

* [G. Cinque, *Deriving Greenberg's Universal 20 and its exceptions* (2005)][cinque-2005]
* [J. H. Greenberg, *Some Universals of Grammar with Particular Reference to the Order of
  Meaningful Elements* (1963)][greenberg-1963]
* [J. A. Hawkins, *Word Order Universals* (1983)][hawkins-1983]
* [R. S. Kayne, *The Antisymmetry of Syntax* (1994)][kayne-1994]
-/

@[expose] public section

namespace Cinque2005

open Minimalist SyntacticObject RoseTree UnorderedTree

/-! ### The orders and their frequencies (6) -/

/-- The paper's frequency labels. -/
inductive Freq
  | veryMany | many | few | veryFew | unattested
  deriving DecidableEq, Repr

/-- A row of (6) records an order of Dem, Num, A and N, its frequency, and the number of marked
options the paper's derivation of it counts, none for the unattested orders and for (6p). -/
structure OrderRow where
  order : List Cat
  freq : Freq
  stated : Option ℕ
  deriving DecidableEq, Repr

/-- The order is attested. -/
def OrderRow.Attested (r : OrderRow) : Prop := r.freq ≠ .unattested

instance (r : OrderRow) : Decidable r.Attested := inferInstanceAs (Decidable (_ ≠ _))

/-- (6a)–(6x). -/
def table : List OrderRow :=
  [ ⟨[.Dem, .Num, .A, .N], .veryMany, some 0⟩   -- a
  , ⟨[.Dem, .Num, .N, .A], .many, some 1⟩       -- b
  , ⟨[.Dem, .N, .Num, .A], .veryFew, some 2⟩    -- c
  , ⟨[.N, .Dem, .Num, .A], .few, some 1⟩        -- d
  , ⟨[.Num, .Dem, .A, .N], .unattested, none⟩   -- e
  , ⟨[.Num, .Dem, .N, .A], .unattested, none⟩   -- f
  , ⟨[.Num, .N, .Dem, .A], .unattested, none⟩   -- g
  , ⟨[.N, .Num, .Dem, .A], .unattested, none⟩   -- h
  , ⟨[.A, .Dem, .Num, .N], .unattested, none⟩   -- i
  , ⟨[.A, .Dem, .N, .Num], .unattested, none⟩   -- j
  , ⟨[.A, .N, .Dem, .Num], .veryFew, some 2⟩    -- k
  , ⟨[.N, .A, .Dem, .Num], .few, some 1⟩        -- l
  , ⟨[.Dem, .A, .Num, .N], .unattested, none⟩   -- m
  , ⟨[.Dem, .A, .N, .Num], .veryFew, some 2⟩    -- n
  , ⟨[.Dem, .N, .A, .Num], .many, some 1⟩       -- o
  , ⟨[.N, .Dem, .A, .Num], .veryFew, none⟩      -- p
  , ⟨[.Num, .A, .Dem, .N], .unattested, none⟩   -- q
  , ⟨[.Num, .A, .N, .Dem], .veryFew, some 2⟩    -- r
  , ⟨[.Num, .N, .A, .Dem], .few, some 2⟩        -- s
  , ⟨[.N, .Num, .A, .Dem], .few, some 1⟩        -- t
  , ⟨[.A, .Num, .Dem, .N], .unattested, none⟩   -- u
  , ⟨[.A, .Num, .N, .Dem], .unattested, none⟩   -- v
  , ⟨[.A, .N, .Num, .Dem], .veryFew, some 1⟩    -- w
  , ⟨[.N, .A, .Num, .Dem], .veryMany, some 0⟩ ] -- x

/-! ### The derivation space (7) -/

/-- The marked options of (7b) are raising without pied-piping (iii), pied-piping of the
picture-of-who type (iv), and partial rather than total raising (v). -/
inductive Marked
  | withoutPiedPiping | pictureOfWho | partialMovement
  deriving DecidableEq, Repr

def tokN : LexicalItem.Token := ⟨.of .N [], 1⟩
def tokA : LexicalItem.Token := ⟨.of .A [], 2⟩
def tokNum : LexicalItem.Token := ⟨.of .Num [], 3⟩
def tokDem : LexicalItem.Token := ⟨.of .Dem [], 4⟩

/-- The tree contains the overt noun; a trace does not count (7b-vi). -/
def hasN : RoseTree SyntacticObject.Vertex → Bool
  | .node (.inl (some t)) _ => t == tokN
  | .node (.inl none) [l, r] => hasN l || hasN r
  | .node _ _ => false

/-- The noun is the tree's specifier, `[NP [XP]]` (fn. 21). -/
def specHasN : RoseTree SyntacticObject.Vertex → Bool
  | .node (.inl (some t)) _ => t == tokN
  | .node (.inl none) [l, _] => hasN l
  | .node _ _ => false

/-- The marked option used by raising `s` past a modifier whose complement is `c`. The whole
complement pied-pipes, of the whose-picture type when the noun is its specifier and of the
picture-of-who type otherwise, and a proper part strands the rest. -/
def markOf (c s : RoseTree SyntacticObject.Vertex) : Option Marked :=
  if s == c then (if specHasN s then none else some .pictureOfWho) else some .withoutPiedPiping

/-- A stage of the enumeration records the derivation, the marked options of its raises and
their number. -/
structure Stage where
  derivation : Derivation
  marks : List Marked
  raises : ℕ

/-- Merge the modifier `m` above the current object, then optionally raise a subtree of it
containing the overt noun to the left edge, the subtrees read off the derivation's ordered
object. -/
def step (m : LexicalItem.Token) (st : Stage) : List Stage :=
  let d := st.derivation.append [.em .left (leaf m)]
  ⟨d, st.marks, st.raises⟩ :: match st.derivation.externalize? with
    | none => []
    | some p => (p.val.subtrees.filter hasN).filterMap fun s ↦
        if h : IsSyntacticObject (UnorderedTree.mk s) then
          some ⟨d.append [.im (LinearizedSyntacticObject.toSyntacticObject ⟨s, h⟩)],
            (markOf p.val s).toList ++ st.marks, st.raises + 1⟩
        else none

/-- The derivations (7) allows from the noun and the modifiers `ms`, merged in turn, with an
optional raise after each Merge. -/
def stagesOf (ms : List LexicalItem.Token) : List Stage :=
  ms.foldl (fun sts m ↦ sts.flatMap (step m)) [⟨⟨leaf tokN, []⟩, [], 0⟩]

/-- The derivations of A, Num and Dem. -/
def stages : List Stage := stagesOf [tokA, tokNum, tokDem]

/-- The surface order of a stage, read by the substrate's externalization. -/
def Stage.order (st : Stage) : List Cat := st.derivation.surfaceCats

/-- The orders some derivation reaches. -/
def reachableOrders : List (List Cat) := (stages.map Stage.order).eraseDups

/-- Universal 20 is derived, an order being reachable iff it is attested, so the 14 attested
orders have derivations and the 10 unattested do not. -/
theorem u20_reachable_iff_attested :
    table.all fun r => decide (r.order ∈ reachableOrders) = decide r.Attested := by decide +kernel

/-! ### The pied-piping types (7b-ii, iv)

A pied-piped phrase keeps its internal order. In the derivation of (6o) the NP raises past A
with vacuous pied-piping of the whose-picture type, `[NP [XP]]`, and then pied-pipes `[N A]` past
Num; in that of (6n) `[A N]` pied-pipes past Num, of the picture-of-who type, `[XP [NP]]`. -/

/-- The Merge order (7a) with nothing moved. -/
def mergeOrder : Derivation :=
  ⟨leaf tokN, [.em .left (leaf tokA), .em .left (leaf tokNum), .em .left (leaf tokDem)]⟩

/-- The derivation of (6o): NP raises past A, and `[N [A t]]` past Num. -/
def derivation6o : Derivation :=
  ⟨leaf tokN, [.em .left (leaf tokA), .im (leaf tokN), .em .left (leaf tokNum),
    .im (tokN * (tokA * .traceOf tokN) : LinearizedSyntacticObject), .em .left (leaf tokDem)]⟩

/-- The derivation of (6n): `[A N]` raises past Num. -/
def derivation6n : Derivation :=
  ⟨leaf tokN, [.em .left (leaf tokA), .em .left (leaf tokNum),
    .im (tokA * tokN : LinearizedSyntacticObject), .em .left (leaf tokDem)]⟩

/-- With nothing moved the order is (6a), Dem Num A N. -/
theorem surfaceCats_mergeOrder : mergeOrder.surfaceCats = [.Dem, .Num, .A, .N] := by decide

/-- Pied-piping of the whose-picture type gives (6o), Dem N A Num. -/
theorem surfaceCats_derivation6o : derivation6o.surfaceCats = [.Dem, .N, .A, .Num] := by decide

/-- Pied-piping of the picture-of-who type gives (6n), Dem A N Num. -/
theorem surfaceCats_derivation6n : derivation6n.surfaceCats = [.Dem, .A, .N, .Num] := by decide

/-! ### Markedness and frequency (7b) -/

/-- The marked options of a stage, partial movement (7b-v) among them when the noun has moved but
not to the left edge. -/
def Stage.marked (st : Stage) : List Marked :=
  (if 0 < st.raises ∧ st.order.head? ≠ some .N then [.partialMovement] else []) ++ st.marks

/-- The number of distinct marked options in the least marked derivation of an order. -/
def markedOptions (ord : List Cat) : Option ℕ :=
  ((stages.filter fun st => decide (st.order = ord)).map fun st =>
    st.marked.eraseDups.length).min?

/-- The derived count is the paper's for every order with a stated count except (6w). -/
theorem markedOptions_eq_stated :
    (table.filter fun r => r.stated.isSome && r.order != [.A, .N, .Num, .Dem]).all fun r =>
      decide (markedOptions r.order = r.stated) := by decide +kernel

/-- For (6w), A N Num Dem, the paper counts one marked option, the picture-of-who pied-piping of
`[A N]` past Num, but (7b-v) lists the order as partial, and no derivation avoids it, since the
noun never passes A. -/
theorem markedOptions_w : markedOptions [.A, .N, .Num, .Dem] = some 2 := by decide +kernel

/-- (6p), N Dem A Num, for which the paper states no count, has one marked option, the
extraction of the noun past Dem. -/
theorem markedOptions_p : markedOptions [.N, .Dem, .A, .Num] = some 1 := by decide +kernel

/-- Marked options predict the extremes of frequency. An attested order has no marked option iff
it is found in very many languages, and an order with two is found in few or very few. -/
theorem markedness_extremes :
    (table.filter fun r => decide r.Attested).all fun r =>
      decide ((markedOptions r.order = some 0 ↔ r.freq = .veryMany) ∧
        (markedOptions r.order = some 2 → r.freq = .few ∨ r.freq = .veryFew)) := by decide +kernel

end Cinque2005
