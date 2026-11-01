/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Reconstruction
public import Linglib.Syntax.Minimalist.SyntacticObject.ToTree

/-!
# The readings of a marked object

This file defines the objects a linearized object with its lower copies marked gives to the
semantic interface. A reading is the finite set of chains read low, a chain being named by its term
in the copy object. A chain read high keeps its higher copy, and its lower copies contract to
traces. A chain read low keeps its lowest copy, and its higher copies are deleted. With no chain
read low the result is the contraction, and a constituency tree adds a binder under each higher
copy of a chain read high, so that the type-driven composition engine interprets it.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.Marked.lf`: the object a reading gives.
* `Minimalist.LinearizedSyntacticObject.Marked.toTree`: its constituency tree, with binders.
* `Minimalist.LinearizedSyntacticObject.Marked.carrying`: the chains with a lower copy holding a
  token.

## Main results

* `Minimalist.LinearizedSyntacticObject.Marked.lf_empty`: with no chain read low, the contraction.
* `Minimalist.LinearizedSyntacticObject.Marked.lf_ofLinearized`,
  `Minimalist.LinearizedSyntacticObject.Marked.toTree_ofLinearized`: with no lower copy, the object
  and its tree.
* `Minimalist.LinearizedSyntacticObject.Marked.eraseBinders_toTree`: the tree of a reading is the
  tree of its object, binders aside.

## Implementation notes

* A movement node is found by search: a binary node one of whose daughters has the term of a marked
  subtree of the other. Recording it would put on the object a datum externalization never reads.
* A lower copy that is itself the higher copy of a lower one, at an intermediate site of a chain
  read high, gets a trace and a binder, `[t [λ …]]`, which denotes what its second daughter does.
* A trace and its binder share the index of the mark, so a chain with no head has the index-free
  trace, which no binder binds, as `LinearizedSyntacticObject.toTree` promises. A head and a phrase
  it projects share an index, and capture each other if the head leaves the phrase and the phrase
  then moves above the head.
* A remnant read high, with a chain that moved out of it also read high, leaves a free trace and a
  vacuous binder. `PhraseStructure.Tree.Closed` tells such a reading from one the engine can close.
* Marcolli, Chomsky and Berwick apply their quotients to the lower copy. Deleting the higher copy is
  their deletion quotient applied to the copy object at the other occurrence, which they do not do;
  it is the reading of Collins's work on the passive and on reconstruction.
* Binding at a reading is not in general binding at the copy object: an object that moves from
  itself, read low, comes to c-command the sister of its movement node. The reading `carrying` is
  the one that does agree with it (`Derivation.bindsAtReading_carrying_iff`).

## References

* [heim-kratzer-1998]
* [marcolli-chomsky-berwick-2025]
* [collins-2005]
* [collins-2026]
-/

@[expose] public section

namespace PhraseStructure.Tree

variable {C W : Type*}

/-- The tree with its binders removed, each binder giving way to its body. -/
def eraseBinders : Tree C W → Tree C W :=
  RoseTree.fold fun l cs ↦
    match l, cs with
    | .bind _ _, [c] => c
    | l, cs => RoseTree.node l cs

theorem eraseBinders_node {l : Tree.Label C W} (hl : ∀ n c, l ≠ .bind n c)
    (cs : List (Tree C W)) :
    eraseBinders (RoseTree.node l cs) = RoseTree.node l (cs.map eraseBinders) := by
  rw [eraseBinders, RoseTree.fold_node]
  cases l <;> first | rfl | exact absurd rfl (hl _ _)

@[simp] theorem eraseBinders_bind (n : ℕ) (c : C) (y : Tree C W) :
    eraseBinders (.bind n c y) = eraseBinders y := by
  simp [eraseBinders, RoseTree.fold_node]

end PhraseStructure.Tree

namespace Minimalist.LinearizedSyntacticObject.Marked

open RoseTree SyntacticObject PhraseStructure

/-- The term of the copy object a tree is a copy of, its marks forgotten. Marking leaves it
unchanged,
so it names a chain at every stage of a derivation. -/
def termOf (r : RoseTree (CopyMark × Vertex)) : UnorderedTree Vertex :=
  UnorderedTree.mk (r.map Prod.snd)

/-- The mark of a lower copy of `x` in `y`: a marked subtree of `y` with the term of `x`. -/
def lowerCopy? (x y : RoseTree (CopyMark × Vertex)) : Option (Option LexicalItem.Token) :=
  y.subtrees.findSome? fun r ↦ r.value.1.bind fun l ↦ if termOf r = termOf x then some l else none

/-- The chain of the copy `r` is read low in the reading `low`. -/
def ReadLow (low : Finset SyntacticObject) (r : RoseTree (CopyMark × Vertex)) : Prop :=
  ∃ m ∈ low, m.val = termOf r

instance (low : Finset SyntacticObject) : DecidablePred (ReadLow low) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ low, _))

@[simp] theorem not_readLow_empty (r : RoseTree (CopyMark × Vertex)) : ¬ ReadLow ∅ r := by
  simp [ReadLow]

section Reading

variable {β : Type*} (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
  (tr : Option LexicalItem.Token → β) (nd : Vertex → List β → β)
  (wrap : Option LexicalItem.Token → β → β)

/-- A node with its daughters, each paired with what it reads as. A copy of a chain read low is
deleted at its movement node, leaving the other daughter, and `wrap` goes around the other
daughter of a copy of a chain read high. A marked copy reads as `tr` of its mark if its chain is
read high. -/
def readStep (v : CopyMark × Vertex) (cs : List (RoseTree (CopyMark × Vertex) × β)) :
    RoseTree (CopyMark × Vertex) × β :=
  let raw := RoseTree.node v (cs.map Prod.fst)
  let plain : β :=
    match cs with
    | [x, y] =>
      match lowerCopy? x.1 y.1, lowerCopy? y.1 x.1 with
      | some l, _ => if low x.1 then y.2 else nd v.2 [x.2, wrap l y.2]
      | _, some l => if low y.1 then x.2 else nd v.2 [wrap l x.2, y.2]
      | none, none => nd v.2 [x.2, y.2]
    | _ => nd v.2 (cs.map Prod.snd)
  (raw, match v.1 with
    | some l => if low raw then plain else tr l
    | none => plain)

/-- What a marked tree reads as, under `readStep`. -/
def reading (t : RoseTree (CopyMark × Vertex)) : β :=
  (fold (readStep low tr nd wrap) t).2

theorem fold_readStep (t : RoseTree (CopyMark × Vertex)) :
    fold (readStep low tr nd wrap) t = (t, reading low tr nd wrap t) := by
  refine Prod.ext ?_ rfl
  induction t with
  | node v cs ih =>
    simp only [fold_node, readStep, List.map_map]
    congr 1
    exact (List.map_congr_left ih).trans (List.map_id' _)

theorem reading_node (v : CopyMark × Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    reading low tr nd wrap (.node v cs) =
      (readStep low tr nd wrap v (cs.map fun c ↦ (c, reading low tr nd wrap c))).2 := by
  rw [reading, fold_node]
  congr 2
  exact List.map_congr_left fun c _ ↦ fold_readStep low tr nd wrap c

end Reading

/-- The object a test of copies gives, as a tree of vertices. -/
def lfBy (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low] :
    RoseTree (CopyMark × Vertex) → RoseTree Vertex :=
  reading low (fun l ↦ .node (.inr l) []) .node fun _ y ↦ y

/-- The object a reading gives, as a tree of vertices. -/
abbrev lfTree (low : Finset SyntacticObject) : RoseTree (CopyMark × Vertex) → RoseTree Vertex :=
  lfBy (ReadLow low)

/-- The object a test gives at a node is a trace, the node with its daughters' objects, or a
daughter's object. -/
theorem lfBy_node_cases (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low] (k :
    CopyMark)
    (a : Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    (∃ l, lfBy low (.node (k, a) cs) = .node (.inr l) []) ∨
      lfBy low (.node (k, a) cs) = .node a (cs.map (lfBy low)) ∨
      ∃ c ∈ cs, lfBy low (.node (k, a) cs) = lfBy low c := by
  unfold lfBy
  rw [reading_node]
  simp only [readStep]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
    (try split) <;> (try split) <;> (try split_ifs) <;> simp_all

theorem isSyntacticObject_lfBy (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
    {t : RoseTree (CopyMark × Vertex)} (h : IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))) :
    IsSyntacticObject (UnorderedTree.mk (lfBy low t)) := by
  induction t with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [isSyntacticObject_mk, map_node, licensed_node_iff] at h
    rcases lfBy_node_cases low k a cs with ⟨l, hl⟩ | hn | ⟨c, hc, hl⟩
    · rw [hl]
      exact isSyntacticObject_mk_leaf (by simp)
    · rw [hn, isSyntacticObject_mk, licensed_node_iff]
      refine ⟨(Vertex.licenses_iff_of_card_eq (by simp)).1 h.1, fun c hc ↦ ?_⟩
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ih c' hc' (h.2 _ (List.mem_map_of_mem hc'))
    · rw [hl]
      exact ih c hc (h.2 _ (List.mem_map_of_mem hc))

/-- The object a reading gives: each chain in `low` keeps its lowest copy, and every other its
highest, its lower copies contracted. -/
def lf (t : Marked) (low : Finset SyntacticObject) : LinearizedSyntacticObject :=
  ⟨lfTree low t.val, isSyntacticObject_lfBy _ t.2⟩

/-- The constituency tree of a reading, the binder of a mark `some a` having the index of the trace
of `a`, and the index-free trace no binder. -/
def toTree (ι : LexicalItem.Token → ℕ) (t : Marked) (low : Finset SyntacticObject) :
    Tree Unit LexicalItem.Token :=
  reading (ReadLow low) (fun l ↦ RoseTree.node (Vertex.toLabel ι (.inr l)) [])
    (fun v cs ↦ RoseTree.node (Vertex.toLabel ι v) cs)
    (fun l y ↦ l.elim y fun a ↦ .bind (ι a + 1) () y) t.val

/-- The chains with a lower copy holding `y`. -/
def carrying (t : Marked) (y : LexicalItem.Token) : Finset SyntacticObject :=
  ((t.val.subtrees.filter fun r ↦
      r.value.1.isSome ∧ Sum.inl (some y) ∈ (r.map Prod.snd).leaves).filterMap fun r ↦
    if h : IsSyntacticObject (termOf r) then some ⟨termOf r, h⟩ else none).toFinset

/-! ### The contraction -/

theorem lfTree_empty (t : RoseTree (CopyMark × Vertex)) : lfTree ∅ t = contractTree t := by
  induction t with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    simp only [lfTree, lfBy] at ih ⊢
    rw [reading_node]
    simp only [readStep]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
      (try split) <;> (try split) <;> simp_all [contractTree_none, contractTree_some]

/-- With no chain read low, a reading gives the contraction. -/
@[simp] theorem lf_empty (t : Marked) : t.lf ∅ = t.contract :=
  Subtype.ext (lfTree_empty t.val)

/-! ### Objects with no lower copy -/

theorem lowerCopy?_map_none (x : RoseTree (CopyMark × Vertex)) (s : RoseTree Vertex) :
    lowerCopy? x (s.map ((none, ·) : Vertex → CopyMark × Vertex)) = none := by
  refine List.findSome?_eq_none_iff.2 fun r hr ↦ ?_
  rw [subtrees_map] at hr
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hr
  cases q
  simp

theorem lfBy_map_none (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
    (s : RoseTree Vertex) : lfBy low (s.map ((none, ·) : Vertex → CopyMark × Vertex)) = s := by
  induction s with
  | node a cs ih =>
    simp only [lfBy] at ih ⊢
    rw [map_node, reading_node]
    simp only [readStep, List.map_map]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;>
      simp_all [lowerCopy?_map_none, Function.comp_def]
    exact (List.map_congr_left ih.2.2.2).trans (List.map_id' _)

/-- An object with no lower copy gives itself under every reading. -/
@[simp] theorem lf_ofLinearized (p : LinearizedSyntacticObject) (low : Finset SyntacticObject) :
    (ofLinearized p).lf low = p :=
  Subtype.ext (lfBy_map_none _ p.val)

/-- An object with no lower copy has the tree it has as a linearized object. -/
@[simp] theorem toTree_ofLinearized (ι : LexicalItem.Token → ℕ) (p : LinearizedSyntacticObject)
    (low : Finset SyntacticObject) :
    (ofLinearized p).toTree ι low = p.toTree ι := by
  obtain ⟨s, hs⟩ := p
  simp only [toTree, ofLinearized, LinearizedSyntacticObject.toTree]
  clear hs
  induction s with
  | node a cs ih =>
    rw [map_node, reading_node]
    simp only [readStep, List.map_map, map_node]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;>
      simp_all [lowerCopy?_map_none, Function.comp_def, Vertex.toLabel]

/-! ### Trees and objects -/

theorem toLabel_ne_bind (ι : LexicalItem.Token → ℕ) (v : Vertex) (n : ℕ) (c : Unit) :
    Vertex.toLabel ι v ≠ .bind n c := by
  rcases v with (_ | _) | (_ | _) <;> simp [Vertex.toLabel]

@[simp] theorem eraseBinders_elim (ι : LexicalItem.Token → ℕ) (l : Option LexicalItem.Token)
    (y : Tree Unit LexicalItem.Token) :
    Tree.eraseBinders (l.elim y fun a ↦ .bind (ι a + 1) () y) = Tree.eraseBinders y := by
  cases l <;> simp

/-- The tree of a reading is the tree of the object it gives, binders aside. -/
theorem eraseBinders_toTree (ι : LexicalItem.Token → ℕ) (t : Marked)
    (low : Finset SyntacticObject) :
    Tree.eraseBinders (t.toTree ι low) = (t.lf low).toTree ι := by
  obtain ⟨s, hs⟩ := t
  simp only [toTree, lf, LinearizedSyntacticObject.toTree]
  clear hs
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    simp only [lfTree, lfBy] at ih ⊢
    rw [reading_node, reading_node]
    simp only [readStep]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
      (try split) <;> (try split) <;> (try split_ifs) <;>
      simp_all [Tree.eraseBinders_node, toLabel_ne_bind, map_node, Function.comp_def]

end Minimalist.LinearizedSyntacticObject.Marked

namespace Minimalist.Derivation

open SyntacticObject PhraseStructure
open LinearizedSyntacticObject (Marked)

variable {d : Derivation} {x y : SyntacticObject}

/-- The object a reading of the derivation gives. -/
def lf? (d : Derivation) (low : Finset SyntacticObject) : Option LinearizedSyntacticObject :=
  d.replayWithCopies?.map (·.current.lf low)

/-- The constituency tree of a reading of the derivation. -/
def toTree? (ι : LexicalItem.Token → ℕ) (d : Derivation) (low : Finset SyntacticObject) :
    Option (Tree Unit LexicalItem.Token) :=
  d.replayWithCopies?.map (·.current.toTree ι low)

/-- `x` c-commands `y` in the object a reading of the derivation gives. -/
def BindsAtReading (d : Derivation) (low : Finset SyntacticObject) (x y : SyntacticObject) : Prop :=
  ∃ p ∈ d.lf? low, CCommands p x y

instance (d : Derivation) (low : Finset SyntacticObject) (x y : SyntacticObject) :
    Decidable (d.BindsAtReading low x y) := by
  unfold BindsAtReading; infer_instance

/-- With no chain read low, a reading of the derivation gives what it externalizes. -/
@[simp] theorem lf?_empty (d : Derivation) : d.lf? ∅ = d.externalize? := by
  rw [lf?, externalize?, ← map_contract_replayWithCopies?, Option.map_map]
  exact Option.map_congr fun c _ ↦ Marked.lf_empty c.current

/-- Binding at the reading with no chain read low is surface binding. -/
theorem bindsAtReading_empty_iff : d.BindsAtReading ∅ x y ↔ d.BindsAtSurface x y := by
  simp [BindsAtReading, BindsAtSurface, CCommandsAt]

end Minimalist.Derivation
