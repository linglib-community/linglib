/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Multidominance

/-!
# de Vries (2009): On multidominance and linearization

Merge applies to roots and to terms alike, so a term can be remerged inside its own root, internal
remerge, which is movement, or with another root, external remerge, which is sharing (§2). PF
traverses the resulting graph and pronounces a remerged node once: at its highest position when it
moved, and at its last when it is shared. De Vries's spell-out of remerged nodes, (56), linearizes a
node with several parents when no parent dominates the current one and either every parent has
been traversed or the current parent dominates every parent not yet traversed; his algorithm (71)
implements it by indexing each node when it is visited.

## Main statements

* `linearization_examples`: (71) yields the strings the paper intends for its examples.
* `remergedYield_examples`: pronouncing each node under its highest mother pronounced last, the
  spell-out of `Linearization/Multidominance.lean`, yields them too.
* `linearization_double`, `remergedYield_double`: on a shared node whose other parent is itself
  shared, (71) pronounces the node twice, the spell-out once.
* `remergedYield_sharing`, `remergedYield_movement`: on the examples that remerge only externally
  each node is pronounced at its last occurrence, and on those that remerge only internally at its
  highest, whichever highest mother is chosen.

## Implementation notes

* A remerged node stands at each of its occurrences in a linearized syntactic object; its parents
  are the terms it is a daughter of, and dominance between them is proper containment. Where a
  figure has an unlabelled daughter (…) or omits the other material, as (51)–(54) do (p. 378), the
  example supplies tokens of its own.
* The current parent is the parent with the highest index, as in (71). It is the parent the
  traversal came from as long as no node is remerged to the right of a lower position of itself,
  as the paper assumes in denying rightward movement (p. 345).

## Errata

* (71) indexes a node before deciding whether to linearize it, so a parent whose linearization was
  omitted counts as traversed. In `double`, α is shared by γ₁ = [g α] and γ₂ = [w α], and γ₂ by δ₁
  and δ₂, with δ₁ before γ₁ before δ₂. α is linearized under γ₁, γ₂ having been traversed, and
  omitted, under δ₁, and again under γ₂ once δ₂ linearizes it, against the paper's requirement that
  only one occurrence of a linguistic object be overtly realized (p. 376).

## References

* [de-vries-2009]
-/

@[expose] public section

namespace DeVries2009

open Minimalist RoseTree SyntacticObject

/-! ### The algorithm (71) -/

section Algorithm

variable (t : LinearizedSyntacticObject)

/-- The index of `g` after the visits `log`: the position of its last visit, counting from one, and
zero when it has not been visited. -/
def index (log : List (RoseTree Vertex)) (g : RoseTree Vertex) : ℕ :=
  log.length - log.reverse.idxOf g

/-- Lines 9–13 of (71): the node `s`, just indexed, is linearized when it has at most one parent,
or when no parent dominates the current parent, the parent with the highest index, and either
every parent has an index or the current parent dominates every parent without one. -/
def Linearizes (s : RoseTree Vertex) (log : List (RoseTree Vertex)) : Prop :=
  (mothers t s).length ≤ 1 ∨
    ∃ c ∈ (mothers t s).find? (fun c ↦ ∀ g ∈ mothers t s, index log g ≤ index log c),
      (∀ g ∈ mothers t s, ¬ (IsSubtree c g ∧ c ≠ g)) ∧
        ((∀ g ∈ mothers t s, 0 < index log g) ∨
          ∀ g ∈ mothers t s, index log g = 0 → IsSubtree g c ∧ g ≠ c)

instance (s : RoseTree Vertex) (log : List (RoseTree Vertex)) : Decidable (Linearizes t s log) :=
  inferInstanceAs (Decidable (_ ∨ _))

mutual
/-- The procedure `scangraph` of (71): index the node, and when it is linearized traverse its
daughters in order, or add it to the string when it is a terminal. -/
def scan : RoseTree Vertex → List (RoseTree Vertex) →
    List (RoseTree Vertex) × List LexicalItem.Token
  | s@(.node a cs), log =>
    if Linearizes t s (log ++ [s]) then
      match cs with
      | [] => (log ++ [s], match a with | .inl (some tok) => [tok] | _ => [])
      | _ => scanList cs (log ++ [s])
    else (log ++ [s], [])

/-- `scangraph` on the daughters of a node, left to right. -/
def scanList : List (RoseTree Vertex) → List (RoseTree Vertex) →
    List (RoseTree Vertex) × List LexicalItem.Token
  | [], log => (log, [])
  | c :: cs, log =>
    let x := scan c log
    let y := scanList cs x.1
    (y.1, x.2 ++ y.2)
end

/-- The algorithm (71): the string of terminals `scangraph` produces from the root. -/
def linearization : List LexicalItem.Token := (scan t t.val []).2

end Algorithm

/-! ### The examples -/

/-- A terminal of the paper's diagrams. -/
def node (id : ℕ) (phon : String) : LexicalItem.Token := ⟨.of .D [] phon, id⟩

def A := node 1 "A"
def B := node 2 "B"
def D := node 3 "D"
def F := node 4 "F"
def Co := node 5 "Co"
def H := node 6 "H"
def x := node 7 "x"
def y := node 8 "y"
def δ := node 9 "δ"
def δ₁ := node 10 "δ1"
def δ₂ := node 11 "δ2"
def α := node 12 "α"
def β₁ := node 13 "β1"
def β₂ := node 14 "β2"
def y₁ := node 15 "y1"
def z₁ := node 16 "z1"
def y₂ := node 17 "y2"
def z₂ := node 18 "z2"
def X := node 19 "X"
def Y := node 20 "Y"
def Z := node 21 "Z"
def a := node 22 "a"
def b := node 23 "b"
def c := node 24 "c"
def g := node 25 "g"
def w := node 26 "w"
/-- Unlabelled daughters (…). -/
def e₁ := node 31 "…1"
def e₂ := node 32 "…2"
def e₃ := node 33 "…3"
def e₄ := node 34 "…4"
def e₅ := node 35 "…5"

/-- (41): B is remerged from C into the root R; /B D A/. -/
def ex41 : LinearizedSyntacticObject := B * (D * (A * B))

/-- (42): B is shared by C in the first conjunct and E in the second; /F A Co H D B/. -/
def ex42 : LinearizedSyntacticObject := (F * (A * B)) * (Co * (H * (D * B)))

/-- (47): the phrase α = [x y] is remerged from γ₁ into γ₂; /x y δ β1/. -/
def ex47 : LinearizedSyntacticObject :=
  let a : LinearizedSyntacticObject := x * y
  a * (δ * (a * β₁))

/-- (48): α is shared by γ₁ and γ₂; /δ1 β1 δ2 β2 α/. -/
def ex48 : LinearizedSyntacticObject := (δ₁ * (β₁ * α)) * (δ₂ * (β₂ * α))

/-- (44), (51): α is internally remerged twice and pronounced at its highest position. -/
def ex51 : LinearizedSyntacticObject := α * (e₃ * (α * (e₂ * (α * β₁))))

/-- (52): α is externally remerged twice and pronounced under the last parent. -/
def ex52 : LinearizedSyntacticObject := (e₁ * α) * ((e₂ * α) * (e₃ * α))

/-- (53): a shared α moves across the board and is pronounced at the position it moved to. -/
def ex53 : LinearizedSyntacticObject := α * ((e₂ * α) * (e₃ * α))

/-- (54): α moves within each conjunct and is pronounced at the higher position of the second. -/
def ex54 : LinearizedSyntacticObject := (α * (y₁ * (z₁ * α))) * (α * (y₂ * (z₂ * α)))

/-- (59): α moves within β, which moves in turn; β and, inside it, α are pronounced high. -/
def ex59 : LinearizedSyntacticObject :=
  let β : LinearizedSyntacticObject := e₁ * (α * (e₂ * (e₃ * α)))
  β * (e₄ * (e₅ * β))

/-- (60): roll-up movement pronounces the heads in the mirror order of first Merge, X Y Z. -/
def ex60 : LinearizedSyntacticObject :=
  let YP : LinearizedSyntacticObject := X * (Y * X)
  YP * (Z * YP)

/-- (64): remnant movement of β, out of which α has moved; α is pronounced only at its second
occurrence. -/
def ex64 : LinearizedSyntacticObject :=
  let β : LinearizedSyntacticObject := e₁ * (e₂ * α)
  β * (e₃ * (α * (e₄ * β)))

/-- (66): c is shared by Y and Z; /a b c/. -/
def ex66 : LinearizedSyntacticObject := (a * c) * (b * c)

/-- The examples with their strings: printed in the paper for (41), (42), (47) and (48), and
otherwise those its choice of the pronounced occurrence gives. -/
def examples : List (LinearizedSyntacticObject × List LexicalItem.Token) :=
  [(ex41, [B, D, A]), (ex42, [F, A, Co, H, D, B]), (ex47, [x, y, δ, β₁]),
    (ex48, [δ₁, β₁, δ₂, β₂, α]), (ex51, [α, e₃, e₂, β₁]), (ex52, [e₁, e₂, e₃, α]),
    (ex53, [α, e₂, e₃]), (ex54, [y₁, z₁, α, y₂, z₂]), (ex59, [e₁, α, e₂, e₃, e₄, e₅]),
    (ex60, [X, Y, Z]), (ex64, [e₁, e₂, e₃, α, e₄]), (ex66, [a, b, c])]

theorem linearization_examples : ∀ e ∈ examples, linearization e.1 = e.2 := by decide +kernel

theorem remergedYield_examples : ∀ e ∈ examples, remergedYield List.getLast? e.1 = e.2 := by
  decide +kernel

/-! ### Double pronunciation -/

/-- α is shared by γ₁ = [g α] and γ₂ = [w α], and γ₂ by δ₁ = [δ1 γ₂] and δ₂ = [δ2 γ₂], with δ₁
before γ₁ before δ₂. -/
def double : LinearizedSyntacticObject :=
  let γ₂ : LinearizedSyntacticObject := w * α
  (δ₁ * γ₂) * ((g * α) * (δ₂ * γ₂))

/-- (71) pronounces α twice. -/
theorem linearization_double : linearization double = [δ₁, g, α, δ₂, w, α] := by decide +kernel

/-- Pronouncing each node under its highest mother pronounced last pronounces α once. -/
theorem remergedYield_double : remergedYield List.getLast? double = [δ₁, g, δ₂, w, α] := by
  decide +kernel

/-! ### Internal and external remerge -/

/-- (42), (48), (52) and (66) remerge externally only: no parent of a node dominates another. -/
theorem sharing_examples : ∀ t ∈ [ex42, ex48, ex52, ex66], ∀ s ∈ t.val.subtrees,
    ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s, IsSubtree g g' → g = g' := by
  decide +kernel

/-- (41), (47), (51) and (60) remerge internally only: the parents of each node are ordered by
dominance, and no node is merged with itself. -/
theorem movement_examples : ∀ t ∈ [ex41, ex47, ex51, ex60],
    (∀ s ∈ t.val.subtrees, ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s,
      IsSubtree g g' ∨ IsSubtree g' g) ∧ ∀ g ∈ t.val.subtrees, g.children.Nodup := by
  decide +kernel

/-- (54) remerges α both ways, so it is neither. -/
theorem not_sharing_not_movement_ex54 :
    ¬ (∀ s ∈ ex54.val.subtrees, ∀ g ∈ mothers ex54 s, ∀ g' ∈ mothers ex54 s,
      IsSubtree g g' → g = g') ∧
    ¬ (∀ s ∈ ex54.val.subtrees, ∀ g ∈ mothers ex54 s, ∀ g' ∈ mothers ex54 s,
      IsSubtree g g' ∨ IsSubtree g' g) := by
  decide +kernel

/-- External remerge alone pronounces each node at its last occurrence. -/
theorem remergedYield_sharing (t) (ht : t ∈ [ex42, ex48, ex52, ex66]) :
    remergedYield List.getLast? t = tokens t :=
  remergedYield_getLast?_eq_tokens (sharing_examples t ht)

/-- Internal remerge alone pronounces each node at its highest occurrence, whichever highest
mother is chosen. -/
theorem remergedYield_movement (t) (ht : t ∈ [ex41, ex47, ex51, ex60]) :
    remergedYield List.head? t = remergedYield List.getLast? t :=
  remergedYield_eq_of_chain (fun _ hl ↦ ⟨_, List.head_mem hl, List.head?_eq_some_head hl⟩)
    (fun _ hl ↦ ⟨_, List.getLast_mem hl, List.getLast?_eq_some_getLast hl⟩)
    (movement_examples t ht).1 (movement_examples t ht).2

end DeVries2009
