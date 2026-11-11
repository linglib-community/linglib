module

public import Mathlib.Order.Basic
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Data.Statistics.Cinque2005

/-!
# Cinque (2005): Deriving Greenberg's Universal 20 and its exceptions

Of the 24 orders of demonstrative, numeral, adjective and noun, 14 are attested, in very unequal
numbers of languages, and neither Greenberg's Universal 20 nor Hawkins's revision of it [carves
out the attested ones](##greenberg_hawkins_mispredict). One order of Merge, `[Dem [Num [A N]]]`,
and leftward movement of the noun phrase alone or of a phrase containing it [derive exactly the
attested orders](##u20_reachable_iff_attested). The marked options a derivation needs, ordered
by their number and then by their severity, [rank the orders as their frequencies
do](##frequency_antitone), but for the two orders the paper itself sets aside.

## Implementation notes

* The derivations of the Merge order with an optional raise after each Merge are enumerated on
  the substrate's `Derivation`, and an order's surface is read by its externalization. A raise of
  a modifier's whole complement pied-pipes, of the whose-picture type when the noun is its
  specifier, a raise of a proper part strands, and a derivation is partial when the noun moves
  but not to the left edge.
* An order's markedness is that of its least marked derivation. The paper's own derivations of
  (6a), (6o) and (6n) are `mergeOrder`, `derivation6o` and `derivation6n`.
* Greenberg's Universal 20 is read as the paper reads it, over the modifiers before and after
  the noun, and Hawkins's revision as the paper quotes it.

## References

* [cinque-2005]
* [greenberg-1963]
* [hawkins-1983]
* [kayne-1994]
-/

@[expose] public section

namespace Cinque2005

open Minimalist SyntacticObject RoseTree UnorderedTree

/-! ### The orders and their frequencies (6) -/

/-- The category a column of (6) names. -/
def Category.toCat : Category → Cat
  | .dem => .Dem
  | .num => .Num
  | .adj => .A
  | .noun => .N

/-- A row of (6): an order of Dem, Num, A and N, its frequency, and the number of marked options
the paper states for its derivation. -/
structure OrderRow where
  label : Label
  order : List Cat
  freq : Frequency
  stated : Option ℕ
  deriving DecidableEq

/-- The order is attested. -/
def OrderRow.Attested (r : OrderRow) : Prop := r.freq ≠ .unattested

instance (r : OrderRow) : Decidable r.Attested := inferInstanceAs (Decidable (_ ≠ _))

/-- (6a)–(6x). -/
def table : List OrderRow :=
  orders.map fun o ↦ ⟨o.label, o.order.map Category.toCat, o.frequency, o.markedOptions⟩

/-! ### Greenberg and Hawkins -/

/-- The modifiers before the noun. -/
def prenominal (ord : List Cat) : List Cat := ord.takeWhile (· ≠ .N)

/-- The modifiers after the noun. -/
def postnominal (ord : List Cat) : List Cat := (ord.dropWhile (· ≠ .N)).drop 1

/-- Greenberg's Universal 20: the modifiers before the noun come in the order Dem, Num, A, and
those after it in that order or its mirror image. -/
def Greenberg (ord : List Cat) : Prop :=
  (prenominal ord).Sublist [.Dem, .Num, .A] ∧
    ((postnominal ord).Sublist [.Dem, .Num, .A] ∨ (postnominal ord).Sublist [.A, .Num, .Dem])

/-- Hawkins's revision (1): the modifiers before the noun come in the order Dem, Num, A, and the
adjective does not precede the noun when the demonstrative or the numeral follows it. -/
def Hawkins (ord : List Cat) : Prop :=
  (prenominal ord).Sublist [.Dem, .Num, .A] ∧
    ¬ (.A ∈ prenominal ord ∧ (.Dem ∈ postnominal ord ∨ .Num ∈ postnominal ord))

instance (ord : List Cat) : Decidable (Greenberg ord) := inferInstanceAs (Decidable (_ ∧ _))
instance (ord : List Cat) : Decidable (Hawkins ord) := inferInstanceAs (Decidable (_ ∧ _))

/-- Greenberg's Universal 20 errs on exactly four orders: it excludes the attested (6l), (6p)
and (6t) and admits the unattested (6g). Hawkins's revision errs on exactly six: it admits the
unattested (6g) and (6h) and excludes the attested (6k), (6n), (6r) and (6w). -/
theorem greenberg_hawkins_mispredict :
    (table.filter fun r ↦ decide r.Attested != decide (Greenberg r.order)).map (·.label) =
        [.g, .l, .p, .t] ∧
      (table.filter fun r ↦ decide r.Attested != decide (Hawkins r.order)).map (·.label) =
        [.g, .h, .k, .n, .r, .w] := by
  decide +kernel

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
  let d := st.derivation.append [.em .left m]
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

/-- An order is reached by some derivation from the Merge order exactly when it is attested. -/
theorem u20_reachable_iff_attested :
    table.all fun r => decide (r.order ∈ reachableOrders) = decide r.Attested := by decide +kernel

/-! ### The pied-piping types (7b-ii, iv)

A pied-piped phrase keeps its internal order. In the derivation of (6o) the NP raises past A
with vacuous pied-piping of the whose-picture type, `[NP [XP]]`, and then pied-pipes `[N A]` past
Num; in that of (6n) `[A N]` pied-pipes past Num, of the picture-of-who type, `[XP [NP]]`. -/

/-- The Merge order (7a) with nothing moved. -/
def mergeOrder : Derivation :=
  ⟨leaf tokN, [.em .left tokA, .em .left tokNum, .em .left tokDem]⟩

/-- The derivation of (6o): NP raises past A, and `[N [A t]]` past Num. -/
def derivation6o : Derivation :=
  ⟨leaf tokN, [.em .left tokA, .im (leaf tokN), .em .left tokNum,
    .im (tokN * (tokA * .traceOf tokN) : LinearizedSyntacticObject), .em .left tokDem]⟩

/-- The derivation of (6n): `[A N]` raises past Num. -/
def derivation6n : Derivation :=
  ⟨leaf tokN, [.em .left tokA, .em .left tokNum,
    .im (tokA * tokN : LinearizedSyntacticObject), .em .left tokDem]⟩

-- (6a)
theorem surfaceCats_mergeOrder : mergeOrder.surfaceCats = [.Dem, .Num, .A, .N] := by decide

-- (6o)
theorem surfaceCats_derivation6o : derivation6o.surfaceCats = [.Dem, .N, .A, .Num] := by decide

-- (6n)
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
    (table.filter fun r => r.stated.isSome && r.label != .w).all fun r =>
      decide (markedOptions r.order = r.stated) := by decide +kernel

-- (6w), (7b-v)
theorem markedOptions_w : markedOptions [.A, .N, .Num, .Dem] = some 2 := by decide +kernel

-- (6p)
theorem markedOptions_p : markedOptions [.N, .Dem, .A, .Num] = some 1 := by decide +kernel

/-- The severity of a marked option (p. 321): partial movement, then movement without
pied-piping, then pied-piping of the picture-of-who type. -/
def Marked.severity : Marked → ℕ
  | .partialMovement => 1
  | .withoutPiedPiping => 2
  | .pictureOfWho => 3

/-- The markedness of a stage: the number of its distinct marked options, then the severity of
the most severe. -/
def Stage.markedness (st : Stage) : Lex (ℕ × ℕ) :=
  toLex (st.marked.eraseDups.length, (st.marked.map Marked.severity).foldr max 0)

/-- The markedness of the least marked derivation of an order. -/
def markedness (ord : List Cat) : Option (Lex (ℕ × ℕ)) :=
  ((stages.filter fun st => decide (st.order = ord)).map Stage.markedness).min?

/-- The rank of a frequency, higher for more languages. -/
def Frequency.rank : Frequency → ℕ
  | .veryMany => 3
  | .many => 2
  | .few => 1
  | .veryFew | .unattested => 0

/-- Of two attested orders, the more marked is attested in no more languages, but for (6s) and
(6p), which the paper sets aside. -/
theorem frequency_antitone :
    ∀ r ∈ table, ∀ r' ∈ table, r.Attested → r'.Attested → r.label ∉ [.s, .p] →
      r'.label ∉ [.s, .p] → ∀ m ∈ markedness r.order, ∀ m' ∈ markedness r'.order, m < m' →
        r'.freq.rank ≤ r.freq.rank := by
  decide +kernel

end Cinque2005
