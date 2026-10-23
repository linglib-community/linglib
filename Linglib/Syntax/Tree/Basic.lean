module

public import Mathlib.Data.Finset.Basic
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Constituency trees

A constituency tree over a category type `C` and a word type `W` is a rose tree whose nodes carry
labels: a terminal carries a category and a word, an internal node a category, the mother of an
adjunction a category too, marking it a further segment of its host's category rather than a
projection above it, and the two nodes of Heim and Kratzer's trace theory of movement, an indexed
trace and an indexed binder over a body, carry a category each. Type-driven interpretation reads the
tree with `C = Unit`; structural operations on parse trees read it with a category system such as
`PhraseStructure.Cat`. Positions, subtrees, replacement and the frontier are those of the rose tree.

## Main declarations

* `PhraseStructure.Tree.Label`, `PhraseStructure.Tree`: the node labels and the trees over them,
  with the pattern-matchable constructors `terminal`, `node`, `adjoin`, `trace`, `bind` and the
  category-free `leaf`, `bin`, `tr`, `binder`.
* `PhraseStructure.Tree.Label.Licenses`, `PhraseStructure.Tree.IsWellFormed`: terminals and traces
  are leaves and binders have one body.
* `PhraseStructure.Tree.rec'`: induction over the five shapes, with a case for ill-formed nodes.
* `PhraseStructure.Tree.terminals`, `yield`, `cats`, `map`, `freeIndices`, `leafSubst`.
* `PhraseStructure.Tree.positionedTerminals`: the terminals with their positions, in the order of
  the yield, which is precedence (`pairwise_precedes_positionedTerminals`).

## Implementation notes

Daughters are a `List`, so a node is binary or n-ary by its list and sibling order is linear
precedence. Only the trace theory of movement is expressible: a copy or a multidominance
representation is not a tree over these labels. Ill-formed label and arity combinations, such as a
terminal with daughters, are expressible; `IsWellFormed` excludes them where a theorem needs it, and
the interpreter denotes them `none`. The mark on the mother of an adjunction follows May's and
Chomsky's segment theory, in which adjunction extends its host's category rather than projecting a
new one, and bare phrase structure labels the adjunction structure apart from a projection. That
each binder binds a trace of its index is a property of a tree, not a guarantee of the type, and
interpretation does not read the category on a binder.

`Tree C W` abbreviates `RoseTree (Label C W)`, so the rose tree's navigation (`children`,
`subtreeAt`) returns `RoseTree (Label C W)`. Dot notation for this file's operations does not
resolve on those results, so write `Tree.cat s`, and write constructor patterns on them as
`Tree.node`: an anonymous `.node` would elaborate as `RoseTree.node`, which matches any label.

## References

* [heim-kratzer-1998]
* [katzir-2007]
* [barker-pullum-1990]
* [may-1985]
* [chomsky-1995]
-/

@[expose] public section

namespace PhraseStructure

namespace Tree

/-- A node of a constituency tree carries a terminal's category and word, an internal node's
category, the category of an adjunction structure, or a trace's or binder's index and category. -/
inductive Label (C W : Type*) where
  | terminal : C → W → Label C W
  | node : C → Label C W
  /-- `segment c` labels the mother of an adjunction, a segment of the category `c` of its host
  daughter, not a projection above it. -/
  | segment : C → Label C W
  | trace : ℕ → C → Label C W
  | bind : ℕ → C → Label C W
  deriving DecidableEq, Repr

namespace Label

variable {C W W' : Type*}

/-- The category a label carries. -/
def cat : Label C W → C
  | .terminal c _ | .node c | .segment c | .trace _ c | .bind _ c => c

/-- A terminal label carries a category and a word; other labels carry none. -/
def terminal? : Label C W → Option (C × W)
  | .terminal c w => some (c, w)
  | _ => none

/-- `mapWord f` relabels the word of a terminal label. -/
def mapWord (f : W → W') : Label C W → Label C W'
  | .terminal c w => .terminal c (f w)
  | .node c => .node c
  | .segment c => .segment c
  | .trace n c => .trace n c
  | .bind n c => .bind n c

@[simp] theorem cat_mapWord (f : W → W') (l : Label C W) : (l.mapWord f).cat = l.cat := by
  cases l <;> rfl

@[simp] theorem mapWord_id (l : Label C W) : l.mapWord id = l := by cases l <;> rfl

@[simp] theorem mapWord_mapWord {W'' : Type*} (g : W' → W'') (f : W → W') (l : Label C W) :
    (l.mapWord f).mapWord g = l.mapWord (g ∘ f) := by
  cases l <;> rfl

/-- A label licenses its daughters when a terminal or a trace has none and a binder has one. -/
def Licenses : Label C W → List (Label C W) → Prop
  | .terminal _ _, ks => ks = []
  | .node _, _ => True
  | .segment _, _ => True
  | .trace _ _, ks => ks = []
  | .bind _ _, ks => ks.length = 1

instance : ∀ (l : Label C W) (ks : List (Label C W)), Decidable (Licenses l ks)
  | .terminal _ _, ks => inferInstanceAs (Decidable (ks = []))
  | .node _, _ => inferInstanceAs (Decidable True)
  | .segment _, _ => inferInstanceAs (Decidable True)
  | .trace _ _, ks => inferInstanceAs (Decidable (ks = []))
  | .bind _ _, ks => inferInstanceAs (Decidable (ks.length = 1))

/-- A label is phrasal when it puts a category over daughters, as a node's or an adjunction
mother's does. -/
def IsPhrase : Label C W → Prop
  | .node _ | .segment _ => True
  | _ => False

instance : DecidablePred (IsPhrase (C := C) (W := W)) := fun l ↦ by
  cases l <;> unfold IsPhrase <;> infer_instance

/-- A label is a segment label when it marks the mother of an adjunction. -/
def IsSegment : Label C W → Prop
  | .segment _ => True
  | _ => False

instance : DecidablePred (IsSegment (C := C) (W := W)) := fun l ↦ by
  cases l <;> unfold IsSegment <;> infer_instance

@[simp] theorem licenses_mapWord (f : W → W') (l : Label C W) (ks : List (Label C W)) :
    Licenses (l.mapWord f) (ks.map (mapWord f)) ↔ Licenses l ks := by
  cases l <;> simp [Licenses, mapWord]

end Label

end Tree

/-- In a constituency tree each node is labelled by a `Tree.Label`. -/
abbrev Tree (C W : Type*) := RoseTree (Tree.Label C W)

namespace Tree

variable {C W : Type*}

/-! ### The shapes -/

/-- `terminal c w` is the word `w` under category `c`. -/
@[match_pattern] abbrev terminal (c : C) (w : W) : Tree C W := RoseTree.node (.terminal c w) []

/-- `node c cs` is the category `c` over daughters `cs`. -/
@[match_pattern] abbrev node (c : C) (cs : List (Tree C W)) : Tree C W :=
  RoseTree.node (.node c) cs

/-- `adjoin c cs` is the category `c` over daughters `cs`, one of which is its host of category
`c`, the others adjoined to it. -/
@[match_pattern] abbrev adjoin (c : C) (cs : List (Tree C W)) : Tree C W :=
  RoseTree.node (.segment c) cs

/-- `trace n c` is a trace of index `n`. -/
@[match_pattern] abbrev trace (n : ℕ) (c : C) : Tree C W := RoseTree.node (.trace n c) []

/-- `bind n c t` is a binder of index `n` over `t`. -/
@[match_pattern] abbrev bind (n : ℕ) (c : C) (t : Tree C W) : Tree C W :=
  RoseTree.node (.bind n c) [t]

@[match_pattern] abbrev leaf (w : W) : Tree Unit W := terminal () w
@[match_pattern] abbrev bin (t₁ t₂ : Tree Unit W) : Tree Unit W := node () [t₁, t₂]
@[match_pattern] abbrev tr (n : ℕ) : Tree Unit W := trace n ()
@[match_pattern] abbrev binder (n : ℕ) (t : Tree Unit W) : Tree Unit W := bind n () t

/-- The category at the root. -/
def cat (t : Tree C W) : C := t.value.cat

@[simp] theorem cat_terminal (c : C) (w : W) : (terminal c w).cat = c := rfl
@[simp] theorem cat_node (c : C) (cs : List (Tree C W)) : (node c cs).cat = c := rfl
@[simp] theorem cat_adjoin (c : C) (cs : List (Tree C W)) : (adjoin c cs).cat = c := rfl
@[simp] theorem cat_trace (n : ℕ) (c : C) : (trace n c : Tree C W).cat = c := rfl
@[simp] theorem cat_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).cat = c := rfl

/-- A tree is well formed when every node has the daughters its label licenses. -/
def IsWellFormed (t : Tree C W) : Prop := t.Licensed Label.Licenses

instance (t : Tree C W) : Decidable t.IsWellFormed :=
  inferInstanceAs (Decidable (t.Licensed _))

/-! ### Induction -/

/-- Induction over the five shapes, with the hypothesis at every daughter, and a case for the
nodes whose daughters their label does not license. -/
@[elab_as_elim]
def rec' {motive : Tree C W → Sort*}
    (terminal : ∀ c w, motive (terminal c w))
    (node : ∀ c cs, (∀ t ∈ cs, motive t) → motive (node c cs))
    (adjoin : ∀ c cs, (∀ t ∈ cs, motive t) → motive (adjoin c cs))
    (trace : ∀ n c, motive (trace n c))
    (bind : ∀ n c t, motive t → motive (bind n c t))
    (junk : ∀ l cs, ¬ Label.Licenses l (cs.map RoseTree.value) → (∀ t ∈ cs, motive t) →
      motive (RoseTree.node l cs))
    (t : Tree C W) : motive t :=
  RoseTree.rec' (motive := motive) (fun l cs ih ↦
    match l, cs, ih with
    | .terminal c w, [], _ => terminal c w
    | .terminal _ _, _ :: _, ih => junk _ _ (by simp [Label.Licenses]) ih
    | .node c, cs, ih => node c cs ih
    | .segment c, cs, ih => adjoin c cs ih
    | .trace n c, [], _ => trace n c
    | .trace _ _, _ :: _, ih => junk _ _ (by simp [Label.Licenses]) ih
    | .bind n c, [t], ih => bind n c t (ih t List.mem_cons_self)
    | .bind _ _, [], ih => junk _ _ (by simp [Label.Licenses]) ih
    | .bind _ _, _ :: _ :: _, ih => junk _ _ (by simp [Label.Licenses]) ih) t

/-! ### Relabelling the words -/

section Map

variable {W' W'' : Type*}

/-- Relabel the words, keeping the shape. -/
def map (f : W → W') (t : Tree C W) : Tree C W' := RoseTree.map (Label.mapWord f) t

theorem map_rose (f : W → W') (l : Label C W) (cs : List (Tree C W)) :
    Tree.map f (RoseTree.node l cs) = RoseTree.node (l.mapWord f) (cs.map (map f)) := by
  simp [map]

@[simp] theorem value_map (f : W → W') (t : Tree C W) : (t.map f).value = t.value.mapWord f := by
  rcases t with ⟨l, cs⟩
  simp [map]

@[simp] theorem map_terminal (f : W → W') (c : C) (w : W) :
    (terminal c w).map f = terminal c (f w) := rfl

@[simp] theorem map_node (f : W → W') (c : C) (cs : List (Tree C W)) :
    (node c cs).map f = node c (cs.map (map f)) := by
  simp [map, node, Label.mapWord]

@[simp] theorem map_adjoin (f : W → W') (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).map f = adjoin c (cs.map (map f)) := by
  simp [map, adjoin, Label.mapWord]

@[simp] theorem map_trace (f : W → W') (n : ℕ) (c : C) : (trace n c).map f = trace n c := rfl

@[simp] theorem map_bind (f : W → W') (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).map f = bind n c (t.map f) := by
  simp [map, bind, Label.mapWord]

@[simp] theorem map_id (t : Tree C W) : t.map id = t := by
  rw [map, show Label.mapWord (C := C) (id : W → W) = id from funext Label.mapWord_id]
  exact RoseTree.id_map t

@[simp] theorem map_map (g : W' → W'') (f : W → W') (t : Tree C W) :
    (t.map f).map g = t.map (g ∘ f) := by
  simp only [map, ← RoseTree.comp_map]
  congr 1
  funext l
  exact Label.mapWord_mapWord g f l

@[simp] theorem cat_map (f : W → W') (t : Tree C W) : (t.map f).cat = t.cat := by
  rcases t with ⟨l, cs⟩
  simp [map, cat]

end Map

/-! ### The frontier -/

/-- The terminals, left to right, each with its category, are the word-bearing leaves. -/
def terminals (t : Tree C W) : List (C × W) := t.leafList.filterMap Label.terminal?

/-- The yield of a tree is the words at its terminals, left to right. -/
def yield (t : Tree C W) : List W := t.terminals.map Prod.snd

@[simp] theorem terminals_terminal (c : C) (w : W) : (terminal c w).terminals = [(c, w)] := rfl

@[simp] theorem terminals_node (c : C) (cs : List (Tree C W)) :
    (node c cs).terminals = cs.flatMap terminals := by
  rcases cs with _ | ⟨c', cs⟩
  · rfl
  · simp only [terminals, node, RoseTree.leafList_node_cons, List.filterMap_flatten, List.map_map,
      List.flatMap_def]
    rfl

@[simp] theorem terminals_adjoin (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).terminals = cs.flatMap terminals := by
  rcases cs with _ | ⟨c', cs⟩
  · rfl
  · simp only [terminals, adjoin, RoseTree.leafList_node_cons, List.filterMap_flatten,
      List.map_map, List.flatMap_def]
    rfl

@[simp] theorem terminals_trace (n : ℕ) (c : C) : (trace n c : Tree C W).terminals = [] := rfl

@[simp] theorem terminals_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).terminals = t.terminals := by
  simp [terminals, bind, RoseTree.leafList_node_of_ne_nil]

@[simp] theorem yield_terminal (c : C) (w : W) : (terminal c w).yield = [w] := rfl

@[simp] theorem yield_node (c : C) (cs : List (Tree C W)) :
    (node c cs).yield = cs.flatMap yield := by
  simp only [yield, terminals_node, List.map_flatMap]
  rfl

@[simp] theorem yield_adjoin (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).yield = cs.flatMap yield := by
  simp only [yield, terminals_adjoin, List.map_flatMap]
  rfl

@[simp] theorem yield_trace (n : ℕ) (c : C) : (trace n c : Tree C W).yield = [] := rfl

@[simp] theorem yield_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).yield = t.yield := by
  simp [yield]

/-! ### Categories and subtrees -/

/-- The categories at the nodes, in pre-order. -/
def cats (t : Tree C W) : List C := t.values.map Label.cat

theorem cats_rose (l : Label C W) (cs : List (Tree C W)) :
    Tree.cats (RoseTree.node l cs) = l.cat :: cs.flatMap cats := by
  simp only [cats, RoseTree.values_node, List.map_cons, List.map_flatten, List.map_map,
    List.flatMap_def]
  rfl

theorem mem_cats_rose {c : C} {l : Label C W} {cs : List (Tree C W)} :
    c ∈ Tree.cats (RoseTree.node l cs) ↔ c = l.cat ∨ ∃ t ∈ cs, c ∈ t.cats := by
  simp [cats_rose]

@[simp] theorem cats_terminal (c : C) (w : W) : (terminal c w).cats = [c] := rfl

@[simp] theorem cats_node (c : C) (cs : List (Tree C W)) :
    (node c cs).cats = c :: cs.flatMap cats := by
  simp only [cats, node, RoseTree.values_node, List.map_cons, List.map_flatten, List.map_map,
    List.flatMap_def]
  rfl

@[simp] theorem cats_adjoin (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).cats = c :: cs.flatMap cats := by
  simp only [cats, adjoin, RoseTree.values_node, List.map_cons, List.map_flatten, List.map_map,
    List.flatMap_def]
  rfl

@[simp] theorem cats_trace (n : ℕ) (c : C) : (trace n c : Tree C W).cats = [c] := rfl

@[simp] theorem cats_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).cats = c :: t.cats := by
  simp [cats, bind, Label.cat]

theorem mem_cats_node {c' c : C} {cs : List (Tree C W)} :
    c' ∈ (node c cs).cats ↔ c' = c ∨ ∃ t ∈ cs, c' ∈ t.cats := by
  simp

theorem mem_cats_bind {c' : C} {n : ℕ} {c : C} {t : Tree C W} :
    c' ∈ (bind n c t).cats ↔ c' = c ∨ c' ∈ t.cats := by
  simp

@[simp] theorem subtrees_terminal (c : C) (w : W) : (terminal c w).subtrees = [terminal c w] :=
  rfl

@[simp] theorem subtrees_node (c : C) (cs : List (Tree C W)) :
    (node c cs).subtrees = node c cs :: cs.flatMap RoseTree.subtrees :=
  RoseTree.subtrees_node _ cs

@[simp] theorem subtrees_adjoin (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).subtrees = adjoin c cs :: cs.flatMap RoseTree.subtrees :=
  RoseTree.subtrees_node _ cs

@[simp] theorem subtrees_trace (n : ℕ) (c : C) : (trace n c : Tree C W).subtrees = [trace n c] :=
  rfl

@[simp] theorem subtrees_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).subtrees = bind n c t :: t.subtrees := by
  simp [bind]

/-! ### Free traces -/

/-- The free indices of a tree are the indices of its traces, less those a dominating binder of
the same index binds. -/
def freeIndices : Tree C W → Finset ℕ :=
  RoseTree.fold fun l ss ↦ match l with
    | .trace n _ => {n}
    | .bind n _ => (ss.foldr (· ∪ ·) ∅).erase n
    | _ => ss.foldr (· ∪ ·) ∅

@[simp] theorem freeIndices_terminal (c : C) (w : W) : (terminal c w).freeIndices = ∅ := by
  simp [freeIndices]

theorem freeIndices_node (c : C) (cs : List (Tree C W)) :
    (node c cs).freeIndices = (cs.map freeIndices).foldr (· ∪ ·) ∅ := by
  simp [freeIndices, node]

theorem freeIndices_adjoin (c : C) (cs : List (Tree C W)) :
    (adjoin c cs).freeIndices = (cs.map freeIndices).foldr (· ∪ ·) ∅ := by
  simp [freeIndices, adjoin]

@[simp] theorem freeIndices_trace (n : ℕ) (c : C) : (trace n c : Tree C W).freeIndices = {n} := by
  simp [freeIndices]

@[simp] theorem freeIndices_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).freeIndices = t.freeIndices.erase n := by
  simp only [freeIndices, bind, RoseTree.fold_node, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil]
  congr 1
  ext
  simp

@[simp] theorem mem_freeIndices_node {i : ℕ} {c : C} {cs : List (Tree C W)} :
    i ∈ (node c cs).freeIndices ↔ ∃ t ∈ cs, i ∈ t.freeIndices := by
  rw [freeIndices_node]
  induction cs with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp] theorem mem_freeIndices_adjoin {i : ℕ} {c : C} {cs : List (Tree C W)} :
    i ∈ (adjoin c cs).freeIndices ↔ ∃ t ∈ cs, i ∈ t.freeIndices := by
  rw [freeIndices_adjoin]
  induction cs with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- A tree is closed when no trace is free in it. -/
def Closed (t : Tree C W) : Prop := t.freeIndices = ∅

instance [DecidableEq C] [DecidableEq W] (t : Tree C W) : Decidable t.Closed :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Word substitution -/

/-- Replace the word `w` by `w'` at every terminal of category `c`. -/
def leafSubst [DecidableEq C] [DecidableEq W] (w w' : W) (c : C) (t : Tree C W) : Tree C W :=
  RoseTree.map (fun
    | .terminal c' v => .terminal c' (if c = c' ∧ v = w then w' else v)
    | l => l) t

section LeafSubst

variable [DecidableEq C] [DecidableEq W] (w w' : W) (c : C)

@[simp] theorem leafSubst_terminal (c' : C) (v : W) :
    leafSubst w w' c (terminal c' v) = terminal c' (if c = c' ∧ v = w then w' else v) := rfl

@[simp] theorem leafSubst_node (c' : C) (cs : List (Tree C W)) :
    leafSubst w w' c (node c' cs) = node c' (cs.map (leafSubst w w' c)) := by
  simp [leafSubst, node]

@[simp] theorem leafSubst_adjoin (c' : C) (cs : List (Tree C W)) :
    leafSubst w w' c (adjoin c' cs) = adjoin c' (cs.map (leafSubst w w' c)) := by
  simp [leafSubst, adjoin]

@[simp] theorem leafSubst_trace (n : ℕ) (c' : C) :
    leafSubst w w' c (trace n c') = trace n c' := rfl

@[simp] theorem leafSubst_bind (n : ℕ) (c' : C) (t : Tree C W) :
    leafSubst w w' c (bind n c' t) = bind n c' (leafSubst w w' c t) := by
  simp [leafSubst, bind]

end LeafSubst

/-! ### Positions

A tree takes Gorn addresses as a rose tree, and with them the dominance order on its positions
and, in `Syntax/Command.lean`, the command relations. -/

open Core.Order

@[simp] theorem children_terminal (c : C) (w : W) : (terminal c w : Tree C W).children = [] :=
  rfl

@[simp] theorem children_node (c : C) (cs : List (Tree C W)) : (node c cs).children = cs := rfl

@[simp] theorem children_adjoin (c : C) (cs : List (Tree C W)) : (adjoin c cs).children = cs :=
  rfl

@[simp] theorem children_trace (n : ℕ) (c : C) : (trace n c : Tree C W).children = [] := rfl

@[simp] theorem children_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).children = [t] :=
  rfl

/-! ### Positions of the terminals

The terminals, paired with their positions, are the word-bearing leaves, so the order of the
yield is precedence (`RoseTree.pairwise_precedes_positionedLeaves`). -/

/-- The terminals, left to right, each paired with its position. -/
def positionedTerminals (t : Tree C W) : List (TreePath × (C × W)) :=
  t.positionedLeaves.filterMap fun x ↦ x.2.terminal?.map (x.1, ·)

theorem map_snd_positionedTerminals (t : Tree C W) :
    t.positionedTerminals.map Prod.snd = t.terminals := by
  rw [positionedTerminals, List.map_filterMap, terminals, ← RoseTree.map_snd_positionedLeaves,
    List.filterMap_map]
  congr 1
  funext x
  simp [Option.map_map, Function.comp_def]

theorem subtreeAt_of_mem_positionedTerminals {t : Tree C W} {x : TreePath × (C × W)}
    (h : x ∈ t.positionedTerminals) :
    RoseTree.subtreeAt t x.1.toList = some (terminal x.2.1 x.2.2) := by
  obtain ⟨⟨p, l⟩, hl, hx⟩ := List.mem_filterMap.mp h
  cases l with
  | terminal c w =>
    obtain rfl : (p, (c, w)) = x := by simpa [Label.terminal?] using hx
    exact RoseTree.subtreeAt_of_mem_positionedLeaves hl
  | _ => simp [Label.terminal?] at hx

theorem mem_positionedTerminals_of_subtreeAt {t : Tree C W} {p : List ℕ} {c : C} {w : W}
    (h : RoseTree.subtreeAt t p = some (terminal c w)) :
    (⟨p⟩, (c, w)) ∈ t.positionedTerminals :=
  List.mem_filterMap.mpr ⟨_, RoseTree.mem_positionedLeaves_of_subtreeAt h, rfl⟩

theorem pairwise_precedes_positionedTerminals (t : Tree C W) :
    t.positionedTerminals.Pairwise fun x y ↦ x.1.Precedes y.1 :=
  (RoseTree.pairwise_precedes_positionedLeaves _).filterMap _ fun _ _ h _ ha _ hb ↦ by
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact h

end Tree

end PhraseStructure
