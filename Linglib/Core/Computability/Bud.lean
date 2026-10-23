/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Lemmas
public import Mathlib.Logic.Relation

/-!
# Bud generating systems

A bud generating system consists of colored operations, the rules, and sets of initial and
terminal colors. One operation derives another when the second is reached from the first by
grafting rules onto inputs of matching color, and the system generates the operations derivable
from the unit of an initial color whose inputs are all terminal. This file develops bud
generating systems over the free binary operad, whose operations are binary trees and whose
partial composition grafts a tree onto a leaf.

## Main definitions

* `Bud.Tree`: binary trees with a color at every vertex.
* `Bud.Tree.graft`: grafting onto the `i`-th leaf, the partial composition of the operad.
* `Bud.System.Derives`, `Bud.System.language`: derivability and the generated language.
* `Bud.System.ofCherries`: the system whose rules are the cherries, single binary vertices,
  with colors in a given relation.

## Main statements

* `Bud.System.Derives.graft`: a derivation can be carried out at any input of a larger tree.
* `Bud.System.Derives.node`: joining derivable trees under a cherry rule is derivable.
* `Bud.System.ofCherries_derives_leaf_iff`: in a system of cherries, a tree is derivable from the
  unit of its root color iff every vertex and its two children form a rule.

## Implementation notes

`Derives` is the reflexive transitive closure of one grafting step, as `ContextFreeGrammar.Derives`
is of one rewriting step. An element of a bud operad records the output and input colors of a
tree but not the colors at its internal vertices; a `Bud.Tree` records those too, as in the
vertex colorings of Marcolli and Larson, so that a tree derived from cherries is also its own
decomposition into generators.

## References

* [giraudo-2019]
* [marcolli-larson-2025]
-/

@[expose] public section

namespace Bud

variable {Ω : Type*}

/-- A binary tree with a color at every vertex. The leaves carry the input colors and the root
the output color. -/
inductive Tree (Ω : Type*) where
  /-- The unit of color `c`, a single leaf. -/
  | leaf (c : Ω)
  /-- A binary vertex of color `c` over the trees `l` and `r`. -/
  | node (c : Ω) (l r : Tree Ω)
  deriving DecidableEq, Repr

namespace Tree

variable {x s y : Tree Ω} {c d a b : Ω} {i j : ℕ}

/-- The output color, at the root. -/
def out : Tree Ω → Ω
  | leaf c => c
  | node c _ _ => c

@[simp] theorem out_leaf : (leaf c).out = c := rfl

@[simp] theorem out_node {l r : Tree Ω} : (node c l r).out = c := rfl

/-- The input colors, at the leaves from left to right. -/
def inputs : Tree Ω → List Ω
  | leaf c => [c]
  | node _ l r => l.inputs ++ r.inputs

@[simp] theorem inputs_leaf : (leaf c).inputs = [c] := rfl

@[simp] theorem inputs_node {l r : Tree Ω} : (node c l r).inputs = l.inputs ++ r.inputs := rfl

/-- The number of inputs. -/
def numInputs : Tree Ω → ℕ
  | leaf _ => 1
  | node _ l r => l.numInputs + r.numInputs

@[simp] theorem numInputs_leaf : (leaf c).numInputs = 1 := rfl

@[simp] theorem numInputs_node {l r : Tree Ω} :
    (node c l r).numInputs = l.numInputs + r.numInputs := rfl

@[simp] theorem length_inputs (x : Tree Ω) : x.inputs.length = x.numInputs := by
  induction x <;> simp [*]

theorem lt_numInputs_of_getElem?_eq_some (h : x.inputs[i]? = some d) : i < x.numInputs := by
  simpa using of_getElem?_eq_some h

theorem getElem?_inputs_node {l r : Tree Ω} :
    (node c l r).inputs[i]? =
      if i < l.numInputs then l.inputs[i]? else r.inputs[i - l.numInputs]? := by
  split_ifs with h
  · exact List.getElem?_append_left (by simpa using h)
  · rw [inputs_node, List.getElem?_append_right (by simpa using h), length_inputs]

/-- The cherry of color `c` over the inputs `a` and `b`, a single binary vertex. -/
def cherry (c a b : Ω) : Tree Ω := node c (leaf a) (leaf b)

@[simp] theorem out_cherry : (cherry c a b).out = c := rfl

@[simp] theorem inputs_cherry : (cherry c a b).inputs = [a, b] := rfl

@[simp] theorem cherry_inj {c' a' b' : Ω} :
    cherry c a b = cherry c' a' b' ↔ c = c' ∧ a = a' ∧ b = b' := by
  simp [cherry]

/-- Graft `s` onto the `i`-th leaf of `x`, the partial composition `x ∘ᵢ s` of the free binary
operad. An index out of range leaves `x` unchanged. -/
def graft : Tree Ω → ℕ → Tree Ω → Tree Ω
  | leaf _, 0, s => s
  | leaf c, _ + 1, _ => leaf c
  | node c l r, i, s =>
      if i < l.numInputs then node c (l.graft i s) r
      else node c l (r.graft (i - l.numInputs) s)

@[simp] theorem graft_leaf_zero : (leaf c).graft 0 s = s := rfl

theorem graft_node {l r : Tree Ω} :
    (node c l r).graft i s =
      if i < l.numInputs then node c (l.graft i s) r
      else node c l (r.graft (i - l.numInputs) s) := rfl

theorem out_graft (h : x.inputs[i]? = some s.out) : (x.graft i s).out = x.out := by
  cases x with
  | leaf c => cases i <;> simp_all
  | node c l r => rw [graft_node]; split <;> rfl

theorem graft_unit (h : x.inputs[i]? = some d) : x.graft i (leaf d) = x := by
  induction x generalizing i with
  | leaf c => cases i <;> simp_all
  | node c l r ihl ihr =>
    rw [getElem?_inputs_node] at h
    rw [graft_node]
    split_ifs at h ⊢
    · rw [ihl h]
    · rw [ihr h]

theorem inputs_graft (h : i < x.numInputs) :
    (x.graft i s).inputs = x.inputs.take i ++ s.inputs ++ x.inputs.drop (i + 1) := by
  induction x generalizing i with
  | leaf c =>
    obtain rfl : i = 0 := by simpa using h
    simp
  | node c l r ihl ihr =>
    have hlen := l.length_inputs
    rw [graft_node]
    split_ifs with hi
    · simp [ihl hi, List.take_append, List.drop_append, Nat.sub_eq_zero_of_le hi.le,
        Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt hi)]
    · have h2 : i - l.numInputs < r.numInputs := by simp at h; omega
      simp [ihr h2, List.take_append, List.drop_append, List.take_of_length_le, hlen,
        List.drop_eq_nil_of_le, Nat.sub_add_comm (not_lt.1 hi), not_lt.1 hi,
        Nat.le_succ_of_le (not_lt.1 hi)]

theorem numInputs_graft (h : i < x.numInputs) :
    (x.graft i s).numInputs = x.numInputs + s.numInputs - 1 := by
  have := congrArg List.length (inputs_graft (s := s) h)
  simp only [length_inputs, List.length_append, List.length_take, List.length_drop] at this
  omega

theorem getElem?_inputs_graft (hi : i < x.numInputs) (hj : j < s.numInputs) :
    (x.graft i s).inputs[i + j]? = s.inputs[j]? := by
  have hA : (x.inputs.take i).length = i := by simp; omega
  rw [inputs_graft hi, List.getElem?_append_left (by simp [hA]; omega),
    List.getElem?_append_right (by omega), hA]
  simp

theorem graft_graft (hi : i < x.numInputs) (hj : j < s.numInputs) :
    (x.graft i s).graft (i + j) y = x.graft i (s.graft j y) := by
  induction x generalizing i with
  | leaf c =>
    obtain rfl : i = 0 := by simpa using hi
    simp
  | node c l r ihl ihr =>
    by_cases hil : i < l.numInputs
    · have hlg : i + j < (l.graft i s).numInputs := by rw [numInputs_graft hil]; omega
      simp only [graft_node, ite_eq_left hil, ite_eq_left hlg, ihl hil]
    · have hir : i - l.numInputs < r.numInputs := by simp at hi; omega
      simp only [graft_node, ite_eq_right hil, ite_eq_right (show ¬ i + j < l.numInputs by omega),
        show i + j - l.numInputs = i - l.numInputs + j by omega, ihr hir]

/-- `P` holds at every internal vertex, of its color and the output colors of its children. -/
def NodeLocal (P : Ω → Ω → Ω → Prop) : Tree Ω → Prop
  | leaf _ => True
  | node c l r => P c l.out r.out ∧ l.NodeLocal P ∧ r.NodeLocal P

variable {P : Ω → Ω → Ω → Prop}

@[simp] theorem nodeLocal_leaf : (leaf c).NodeLocal P := trivial

@[simp] theorem nodeLocal_node {l r : Tree Ω} :
    (node c l r).NodeLocal P ↔ P c l.out r.out ∧ l.NodeLocal P ∧ r.NodeLocal P := Iff.rfl

@[simp] theorem nodeLocal_cherry : (cherry c a b).NodeLocal P ↔ P c a b := by simp [cherry]

theorem NodeLocal.graft (hx : x.NodeLocal P) (hs : s.NodeLocal P)
    (h : x.inputs[i]? = some s.out) : (x.graft i s).NodeLocal P := by
  induction x generalizing i with
  | leaf c => cases i <;> simpa
  | node c l r ihl ihr =>
    obtain ⟨hP, hl, hr⟩ := hx
    rw [getElem?_inputs_node] at h
    rw [graft_node]
    split_ifs at h ⊢
    · exact ⟨(out_graft h).symm ▸ hP, ihl hl h, hr⟩
    · exact ⟨(out_graft h).symm ▸ hP, hl, ihr hr h⟩

end Tree

open Tree

/-- A bud generating system over the free binary operad, with colors in `Ω`. -/
structure System (Ω : Type*) where
  /-- The rules, grafted one at a time in a derivation. -/
  rules : Set (Tree Ω)
  /-- The colors whose units begin the derivations of generated trees. -/
  initial : Set Ω
  /-- The colors allowed at the inputs of generated trees. -/
  terminal : Set Ω

namespace System

variable {B : System Ω} {x y s t l r : Tree Ω} {c a b : Ω} {i : ℕ} {P : Ω → Ω → Ω → Prop}

/-- `B.Produces x y` means that grafting a rule of `B` onto an input of `x` of the matching color
gives `y`. -/
def Produces (B : System Ω) (x y : Tree Ω) : Prop :=
  ∃ r ∈ B.rules, ∃ i, x.inputs[i]? = some r.out ∧ x.graft i r = y

/-- `B.Derives x y` means that `B` can transform `x` into `y` in some number of grafting steps. -/
abbrev Derives (B : System Ω) : Tree Ω → Tree Ω → Prop :=
  Relation.ReflTransGen B.Produces

/-- A tree is in the language generated by `B` when its output color is initial, it is derivable
from the unit of that color, and its inputs are all terminal. -/
def language (B : System Ω) : Set (Tree Ω) :=
  {x | x.out ∈ B.initial ∧ B.Derives (leaf x.out) x ∧ ∀ c ∈ x.inputs, c ∈ B.terminal}

theorem Produces.single (h : B.Produces x y) : B.Derives x y := .single h

theorem Produces.out_eq (h : B.Produces x y) : y.out = x.out := by
  obtain ⟨r, -, i, hi, rfl⟩ := h
  exact out_graft hi

theorem Derives.out_eq (h : B.Derives x y) : y.out = x.out := by
  induction h with
  | refl => rfl
  | tail _ hyz ih => rw [hyz.out_eq, ih]

theorem Produces.graft (hi : i < x.numInputs) (h : B.Produces s t) :
    B.Produces (x.graft i s) (x.graft i t) := by
  obtain ⟨r, hr, j, hj, rfl⟩ := h
  have hj' := lt_numInputs_of_getElem?_eq_some hj
  exact ⟨r, hr, i + j, (getElem?_inputs_graft hi hj').trans hj, graft_graft hi hj'⟩

theorem Derives.graft (hi : i < x.numInputs) (h : B.Derives s t) :
    B.Derives (x.graft i s) (x.graft i t) :=
  h.lift (x.graft i) fun _ _ ↦ Produces.graft hi

theorem Derives.node_left (h : B.Derives s t) (c : Ω) (r : Tree Ω) :
    B.Derives (node c s r) (node c t r) := by
  simpa [graft_node] using h.graft (x := node c (leaf c) r) (i := 0) (by simp; omega)

theorem Derives.node_right (h : B.Derives s t) (c : Ω) (l : Tree Ω) :
    B.Derives (node c l s) (node c l t) := by
  simpa [graft_node] using h.graft (x := node c l (leaf c)) (i := l.numInputs) (by simp)

theorem Derives.node (hc : cherry c a b ∈ B.rules) (hl : B.Derives (leaf a) l)
    (hr : B.Derives (leaf b) r) : B.Derives (leaf c) (node c l r) :=
  (Produces.single ⟨_, hc, 0, rfl, rfl⟩).trans ((hl.node_left c _).trans (hr.node_right c l))

theorem Derives.nodeLocal (hB : ∀ r ∈ B.rules, r.NodeLocal P) (h : B.Derives x y)
    (hx : x.NodeLocal P) : y.NodeLocal P := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih =>
    obtain ⟨r, hr, i, hi, rfl⟩ := hyz
    exact ih.graft (hB r hr) hi

theorem derives_leaf_of_nodeLocal (hP : ∀ c a b, P c a b → cherry c a b ∈ B.rules)
    (h : x.NodeLocal P) : B.Derives (leaf x.out) x := by
  induction x with
  | leaf => rfl
  | node c l r ihl ihr => exact .node (hP _ _ _ h.1) (ihl h.2.1) (ihr h.2.2)

/-- The system whose rules are the cherries with colors in the relation `R`, with initial colors
`I` and terminal colors `T`. -/
def ofCherries (R : Ω → Ω → Ω → Prop) (I T : Set Ω) : System Ω where
  rules := {t | ∃ c a b, R c a b ∧ cherry c a b = t}
  initial := I
  terminal := T

variable {R : Ω → Ω → Ω → Prop} {I T : Set Ω}

@[simp] theorem cherry_mem_ofCherries : cherry c a b ∈ (ofCherries R I T).rules ↔ R c a b := by
  simp [ofCherries]

theorem ofCherries_derives_leaf_iff :
    (ofCherries R I T).Derives (leaf c) x ↔ x.out = c ∧ x.NodeLocal R := by
  refine ⟨fun h ↦ ⟨h.out_eq, h.nodeLocal ?_ trivial⟩, ?_⟩
  · rintro _ ⟨c, a, b, h, rfl⟩
    simpa
  · rintro ⟨rfl, h⟩
    exact derives_leaf_of_nodeLocal (fun _ _ _ ↦ cherry_mem_ofCherries.2) h

theorem mem_ofCherries_language_iff :
    x ∈ (ofCherries R I T).language ↔ x.out ∈ I ∧ x.NodeLocal R ∧ ∀ c ∈ x.inputs, c ∈ T := by
  change _ ∧ _ ∧ _ ↔ _
  rw [ofCherries_derives_leaf_iff, eq_self, true_and]
  rfl

end System

end Bud
