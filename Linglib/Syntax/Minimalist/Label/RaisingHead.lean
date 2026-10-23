/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection

/-!
# The raising head

Marcolli, Chomsky and Berwick state labeling over a partial head function and require that
function to be raising: the object Internal Merge forms is headed by the head of what it raised out
of, so the landing site of a wh-phrase beside a C is headed by C. The raising head reads this off
the finished object from the selection head, a lower copy satisfying selection as the phrase it
copies and otherwise invisible (`CopyState`): where two phrases merge and the head of one has a
lower copy inside the other, the first has raised out of the second, which projects. A planar
embedding is a total head function extending it, and the head function `HeadFunction.raising`
takes the daughter carrying the raising head, and the embedding's head where there is none.

## Main definitions

* `Minimalist.CopyState`: a selection state or a lower copy, a commutative magma with zero.
* `Minimalist.RaisingState`, `Minimalist.SyntacticObject.raisingHead`: the raising state and the
  raising head of a syntactic object.
* `Minimalist.headIndex?`, `Minimalist.HeadFunction.raising`: the head daughter of a planar tree,
  and the head function it gives.

## Main results

* `Minimalist.SyntacticObject.raisingHead_merge`: the raising head of a merge is a daughter's.
* `Minimalist.exists_headIndex?_of_treeRaisingHead`: the head daughter carries the raising head
  wherever there is one.

## Implementation notes

* The drawing convention puts specifiers to the left of their heads and heads to the left of their
  complements: a left leaf that selects nothing is a specifier and the right daughter heads, a left
  leaf that selects is the head, and otherwise the right daughter heads. It decides only where the
  raising head is undefined, at a phrase merged in place beside another phrase, which the labeling
  algorithm leaves unlabeled until one of the two moves on (`HeadFunction.label`).
* The raising head also delimits the phases of `Locality/Phase.lean`.

## TODO

* The trace of a token is the lower copy of the phrase the token heads; a moved head, whose lower
  copy would still select, is not distinguished.
* The positions at or below the maximal projection of a head occurring once carry exactly the
  terms within its projection, where the raising head is defined along the projection line.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- A constituent's copy state is its selection state, or a lower copy of the phrase a token
heads, which satisfies selection as that phrase and is otherwise invisible to the raising
algorithm. -/
inductive CopyState where
  /-- The selection state of a constituent the raising head sees. -/
  | sel (x : SelectionState)
  /-- A lower copy of the phrase `tok` heads. -/
  | copy (tok : LexicalItem.Token)
  deriving DecidableEq

namespace CopyState

instance : Zero CopyState := ⟨sel 0⟩

/-- A lower copy satisfies the selection of a sister selecting the phrase it copies and is
otherwise invisible; two lower copies leave nothing to see. -/
instance : Mul CopyState where
  mul
    | sel x, sel y => sel (x * y)
    | copy a, sel y => if SelectionState.of a [] * y = 0 then sel y else sel (.of a [] * y)
    | sel x, copy a => if x * SelectionState.of a [] = 0 then sel x else sel (x * .of a [])
    | copy _, copy _ => 0

@[simp] theorem sel_mul_sel (x y : SelectionState) : sel x * sel y = sel (x * y) := rfl

theorem copy_mul_sel (a : LexicalItem.Token) (y : SelectionState) :
    copy a * sel y = if SelectionState.of a [] * y = 0 then sel y else sel (.of a [] * y) := rfl

theorem sel_mul_copy (x : SelectionState) (a : LexicalItem.Token) :
    sel x * copy a = if x * SelectionState.of a [] = 0 then sel x else sel (x * .of a []) := rfl

instance : CommMagma CopyState where
  mul_comm
    | sel x, sel y => congrArg sel (mul_comm x y)
    | copy a, sel y | sel y, copy a => by
      show (if _ = _ then _ else _) = (if _ = _ then _ else _)
      rw [mul_comm y]
    | copy _, copy _ => rfl

instance : MulZeroClass CopyState where
  zero_mul
    | sel _ => rfl
    | copy a => by rw [show (0 : CopyState) = sel 0 from rfl, sel_mul_copy]; simp
  mul_zero
    | sel x => congrArg sel (mul_zero x)
    | copy a => by rw [show (0 : CopyState) = sel 0 from rfl, copy_mul_sel]; simp

/-- The head a copy state provides is that of a visible constituent, and none for a lower
copy. -/
def head : CopyState → Option LexicalItem.Token
  | sel x => x.head
  | copy _ => none

/-- A copy state never combines with itself. -/
@[simp] theorem mul_self (l : CopyState) : l * l = 0 := by
  rcases l with x | a
  · show sel (x * x) = sel 0
    rw [SelectionState.mul_self]
  · rfl

/-- The head of a product of copy states is a factor's head. -/
instance : Head CopyState where
  head := head
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y h} hxy := by
    rcases x with x | a <;> rcases y with y | b
    · exact mem_head_or_mem_head_of_mem_head_mul (β := SelectionState) hxy
    · rw [sel_mul_copy] at hxy
      split_ifs at hxy with h0
      · exact .inl hxy
      · change (x * SelectionState.of b []).head = some h at hxy
        rw [_root_.mul_comm x] at hxy
        exact .inl (SelectionState.head_of_mul_of hxy)
    · rw [copy_mul_sel] at hxy
      split_ifs at hxy with h0
      · exact .inr hxy
      · exact .inr (SelectionState.head_of_mul_of hxy)
    · cases hxy

end CopyState

/-! ### The raising head -/

/-- The raising state of a constituent pairs its copy state with the tokens whose lower copies
it contains. -/
structure RaisingState where
  /-- The copy state. -/
  state : CopyState
  /-- The tokens heading the phrases of which the constituent contains a lower copy. -/
  copies : Multiset LexicalItem.Token
  deriving DecidableEq

namespace RaisingState

instance : Zero RaisingState := ⟨⟨0, 0⟩⟩

/-- Under raising, two merged constituents take the product of their copy states where it is
defined, and otherwise the copy state of the one containing a lower copy of the other's head,
since the other raised out of it and it projects. -/
def raise (x y : RaisingState) : CopyState :=
  if x.state * y.state ≠ 0 then x.state * y.state else
  match x.state.head, y.state.head with
  | some a, some b =>
    if a ∈ y.copies ∧ b ∉ x.copies then y.state
    else if b ∈ x.copies ∧ a ∉ y.copies then x.state else 0
  | _, _ => 0

instance : Mul RaisingState := ⟨fun x y ↦ ⟨raise x y, x.copies + y.copies⟩⟩

theorem mul_def (x y : RaisingState) : x * y = ⟨raise x y, x.copies + y.copies⟩ := rfl

theorem raise_comm (x y : RaisingState) : raise x y = raise y x := by
  unfold raise
  rw [mul_comm y.state]
  split_ifs with h₁
  · rfl
  · rcases hx : x.state.head with _ | a <;> rcases hy : y.state.head with _ | b <;> simp only
    grind

instance : CommMagma RaisingState where
  mul_comm x y := by simp only [mul_def, raise_comm, add_comm]

/-- The raising head of a product is a factor's raising head. -/
instance : Head RaisingState where
  head x := x.state.head
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y t} h := by
    simp only [mul_def, raise] at h
    split_ifs at h with h0
    · exact mem_head_or_mem_head_of_mem_head_mul (β := CopyState) h
    · rcases hx : x.state.head with _ | a <;> rcases hy : y.state.head with _ | b <;>
        simp only [hx, hy] at h ⊢
      · cases h
      · cases h
      · cases h
      · split_ifs at h
        · right; simp_all
        · left; simp_all
        · exact absurd (show (none : Option LexicalItem.Token) = some t from h) (by simp)

end RaisingState

/-- A trace's raising state is the lower copy of the phrase its token heads, with the token recorded
among the copies; the bare trace remembers no token. -/
def raisingTraceState : Option LexicalItem.Token → RaisingState
  | some tok => ⟨.copy tok, {tok}⟩
  | none => ⟨.sel (traceState none), 0⟩

namespace SyntacticObject

variable (s : SyntacticObject)

/-- The raising state of a syntactic object. -/
def raisingCheck : RaisingState :=
  liftFun (fun tok ↦ ⟨.sel (.of tok tok.item.sel), 0⟩) raisingTraceState s

/-- The raising head of a syntactic object, [marcolli-chomsky-berwick-2025]'s raising head
function: the selection head where there is one, and at a landing site the head of the phrase
moved out of. -/
def raisingHead : Option LexicalItem.Token := s.raisingCheck.state.head

@[simp] theorem raisingCheck_merge (l r : SyntacticObject) :
    (merge l r).raisingCheck = l.raisingCheck * r.raisingCheck :=
  liftFun_merge _ _ l r

/-- `raisingCheck` as a morphism of magmas. -/
noncomputable def raisingCheckHom : SyntacticObject →ₙ* RaisingState :=
  lift (fun tok ↦ ⟨.sel (.of tok tok.item.sel), 0⟩) raisingTraceState

/-- The raising head of a merge is a daughter's raising head
([marcolli-chomsky-berwick-2025] Lemma 1.13.7). -/
theorem raisingHead_merge {l r : SyntacticObject} {h : LexicalItem.Token}
    (hlr : (merge l r).raisingHead = some h) : l.raisingHead = some h ∨ r.raisingHead = some h :=
  mem_head_or_mem_head_of_mem_head_map_mul raisingCheckHom (x := l) (y := r) hlr

/-- An object merged with itself has no raising head. -/
@[simp] theorem raisingHead_merge_self (x : SyntacticObject) : (merge x x).raisingHead = none := by
  rw [raisingHead, raisingCheck_merge, RaisingState.mul_def]
  simp only [RaisingState.raise, CopyState.mul_self, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases x.raisingCheck.state.head with _ | a
  · rfl
  · dsimp only
    split_ifs with h₁ <;> first | rfl | exact (h₁.2 h₁.1).elim

end SyntacticObject

/-! ### Head daughters -/

/-- The raising head of a planar tree, that of its unordered image. -/
def treeRaisingHead (s : RoseTree Vertex) : Option LexicalItem.Token :=
  (liftN (fun tok ↦ (⟨.sel (.of tok tok.item.sel), 0⟩ : RaisingState)) raisingTraceState
    (UnorderedTree.mk s)).state.head

theorem treeRaisingHead_subtree {t : LinearizedSyntacticObject} (p : t.val.Positions) :
    treeRaisingHead p.subtree = (t.termAt p).raisingHead := rfl

/-- The drawing convention makes a token or trace leaf its own head; at a binary node it takes a
left leaf that selects nothing for a specifier and looks for the head in the right daughter, takes
a left leaf that selects for the head, and otherwise looks in the right daughter. This is the
head path it assigns. -/
def conventionHeadPos? : RoseTree Vertex → Option (List ℕ)
  | .node (.inl (some _)) _ | .node (.inr (some _)) _ => some []
  | .node (.inl none) [.node (.inl (some tok)) [], r] =>
      if tok.item.sel = [] then (conventionHeadPos? r).map (1 :: ·) else some [0]
  | .node (.inl none) [_, r] => (conventionHeadPos? r).map (1 :: ·)
  | .node (.inl none) _ => none
  | .node (.inr none) _ => none

/-- The head daughter of a planar tree is the first daughter carrying its raising head, and where
it has none, the first step of the drawing convention's head path. -/
def headIndex? (s : RoseTree Vertex) : Option ℕ :=
  ((treeRaisingHead s).bind fun h ↦ s.children.findIdx? (treeRaisingHead · = some h)) <|>
    (conventionHeadPos? s).bind List.head?

/-- The raising head function, [marcolli-chomsky-berwick-2025]'s raising head extended to a total
head function by the drawing convention: the head daughter of the subtree at each position,
`none` off the object. -/
def HeadFunction.raising : HeadFunction := fun t q ↦ (t.val.subtreeAt q.toList).bind headIndex?

/-- Where a linearized syntactic object with daughters has a raising head, its head daughter carries
it. -/
theorem exists_headIndex?_of_treeRaisingHead {s : RoseTree Vertex} {ℓ : LexicalItem.Token}
    (hs : IsSyntacticObject (UnorderedTree.mk s)) (hc : s.children ≠ [])
    (h : treeRaisingHead s = some ℓ) :
    ∃ i c, headIndex? s = some i ∧ s.children[i]? = some c ∧ treeRaisingHead c = some ℓ := by
  obtain ⟨v, cs⟩ := s
  obtain rfl := eq_bare_of_ne_nil hs hc
  obtain ⟨l, r, rfl⟩ : ∃ l r, cs = [l, r] :=
    List.length_eq_two.1 ((length_eq_zero_or_two hs).resolve_left fun h0 ↦
      hc (List.length_eq_zero_iff.1 h0))
  obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge l r).1 hs
  have hm : treeRaisingHead (.node Vertex.bare [l, r]) = (merge ⟨_, hl⟩ ⟨_, hr⟩).raisingHead := by
    simp only [raisingHead, raisingCheck, liftFun, merge_mk]; rfl
  by_cases hl' : treeRaisingHead l = some ℓ
  · exact ⟨0, l, by simp [headIndex?, h, hl', List.findIdx?_cons], rfl, hl'⟩
  · have hr' : treeRaisingHead r = some ℓ :=
      (raisingHead_merge (l := ⟨_, hl⟩) (r := ⟨_, hr⟩) (hm ▸ h)).resolve_left fun h' ↦ hl' h'
    exact ⟨1, r, by simp [headIndex?, h, hl', hr', List.findIdx?_cons], rfl, hr'⟩

end Minimalist
