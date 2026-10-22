/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# The raising head

Marcolli, Chomsky and Berwick state labeling over a partial head function and require that
function to be raising: the object Internal Merge forms is headed by the head of what it raised out
of, so the landing site of a wh-phrase beside a C is headed by C. The raising head reads this off
the finished object from the selection head, a lower copy satisfying selection as the phrase it
copies and otherwise invisible (`LabelState`): where two phrases merge and the head of one has a
lower copy inside the other, the first has raised out of the second, which projects.

## Main definitions

* `Minimalist.LabelState`: a selection state or a lower copy, a commutative magma with zero.
* `Minimalist.RaisingState`, `Minimalist.SyntacticObject.raisingHead`: the raising state and the
  raising head of a syntactic object.

## Main results

* `Minimalist.SyntacticObject.raisingHead_merge`: the raising head of a merge is a daughter's.

## Implementation notes

* The raising head delimits the phases of `SyntacticObject/Phase.lean` and gives the head daughters
  of `SyntacticObject/Position.lean`. Labeling by minimal search is `Probe/Label.lean`.

## TODO

The trace of a token is the lower copy of the phrase the token heads; a moved head, whose lower
copy would still select, is not distinguished.

## References

* [marcolli-chomsky-berwick-2025], Definitions 1.15.1 and 1.15.2
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- A constituent's labeling state is its selection state, or a lower copy of the phrase a token
heads, which satisfies selection as that phrase and is otherwise invisible to the labeling
algorithm. -/
inductive LabelState where
  /-- The selection state of a constituent the labeling algorithm sees. -/
  | sel (x : SelectionState)
  /-- A lower copy of the phrase `tok` heads. -/
  | copy (tok : LexicalItem.Token)
  deriving DecidableEq

namespace LabelState

instance : Zero LabelState := ⟨sel 0⟩

/-- A lower copy satisfies the selection of a sister selecting the phrase it copies and is
otherwise invisible; two lower copies leave nothing to see. -/
instance : Mul LabelState where
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

instance : CommMagma LabelState where
  mul_comm
    | sel x, sel y => congrArg sel (mul_comm x y)
    | copy a, sel y | sel y, copy a => by
      show (if _ = _ then _ else _) = (if _ = _ then _ else _)
      rw [mul_comm y]
    | copy _, copy _ => rfl

instance : MulZeroClass LabelState where
  zero_mul
    | sel _ => rfl
    | copy a => by rw [show (0 : LabelState) = sel 0 from rfl, sel_mul_copy]; simp
  mul_zero
    | sel x => congrArg sel (mul_zero x)
    | copy a => by rw [show (0 : LabelState) = sel 0 from rfl, copy_mul_sel]; simp

/-- The label a labeling state provides is the head of a visible constituent, and none for a lower
copy. -/
def label : LabelState → Option LexicalItem.Token
  | sel x => x.head
  | copy _ => none

/-- A labeling state never combines with itself. -/
@[simp] theorem mul_self (l : LabelState) : l * l = 0 := by
  rcases l with x | a
  · show sel (x * x) = sel 0
    rw [SelectionState.mul_self]
  · rfl

/-- The label of a labeling product is a factor's label. -/
instance : Head LabelState where
  head := label
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

end LabelState

/-! ### The raising head -/

/-- The raising state of a constituent pairs its labeling state with the tokens whose lower copies
it contains. -/
structure RaisingState where
  /-- The labeling state. -/
  label : LabelState
  /-- The tokens heading the phrases of which the constituent contains a lower copy. -/
  copies : Multiset LexicalItem.Token
  deriving DecidableEq

namespace RaisingState

instance : Zero RaisingState := ⟨⟨0, 0⟩⟩

/-- Under raising, two merged constituents take the labeling product where it is defined, and
otherwise the labeling state of the one containing a lower copy of the other's head, since the
other raised out of it and it projects. -/
def raise (x y : RaisingState) : LabelState :=
  if x.label * y.label ≠ 0 then x.label * y.label else
  match x.label.label, y.label.label with
  | some a, some b =>
    if a ∈ y.copies ∧ b ∉ x.copies then y.label
    else if b ∈ x.copies ∧ a ∉ y.copies then x.label else 0
  | _, _ => 0

instance : Mul RaisingState := ⟨fun x y ↦ ⟨raise x y, x.copies + y.copies⟩⟩

theorem mul_def (x y : RaisingState) : x * y = ⟨raise x y, x.copies + y.copies⟩ := rfl

theorem raise_comm (x y : RaisingState) : raise x y = raise y x := by
  unfold raise
  rw [mul_comm y.label]
  split_ifs with h₁
  · rfl
  · rcases hx : x.label.label with _ | a <;> rcases hy : y.label.label with _ | b <;> simp only
    grind

instance : CommMagma RaisingState where
  mul_comm x y := by simp only [mul_def, raise_comm, add_comm]

/-- The raising head of a product is a factor's raising head. -/
instance : Head RaisingState where
  head x := x.label.label
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y t} h := by
    simp only [mul_def, raise] at h
    split_ifs at h with h0
    · exact mem_head_or_mem_head_of_mem_head_mul (β := LabelState) h
    · rcases hx : x.label.label with _ | a <;> rcases hy : y.label.label with _ | b <;>
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
function: the label where there is one, and at a landing site the head of the phrase moved out
of. -/
def raisingHead : Option LexicalItem.Token := s.raisingCheck.label.label

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
  simp only [RaisingState.raise, LabelState.mul_self, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases x.raisingCheck.label.label with _ | a
  · rfl
  · dsimp only
    split_ifs with h₁ <;> first | rfl | exact (h₁.2 h₁.1).elim

end SyntacticObject

end Minimalist
