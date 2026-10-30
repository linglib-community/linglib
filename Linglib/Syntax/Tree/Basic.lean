module

public import Mathlib.Data.Finset.Basic
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Constituency trees

A constituency tree over categories `C` and words `W` is a rose tree whose nodes carry labels: a
terminal carries a category and a word, a phrase a category and its kind, and the trace and binder
of [heim-kratzer-1998]'s trace theory of movement an index and a category. A phrase is a
projection or an adjunction structure, which on the segment theory of [may-1985] and
[chomsky-1995] is a further segment of its host's category; only the head relation of
`Syntax/Tree/Projection.lean` tells the two apart. Positions, subtrees and the frontier are the
rose tree's, and the terminals with their positions, in the order of the yield, ascend in
[precedence](##pairwise_precedes_positionedTerminals).

## Implementation notes

Daughters are a `List`, so a node is binary or n-ary by its list and sibling order is linear
precedence. Only the trace theory of movement is expressible: a copy or a multidominance
representation is not a tree over these labels. A binder is the node of Heim and Kratzer's
Predicate Abstraction rule, whose daughters are an index and a body, with the index in its label
rather than a daughter of its own. Ill-formed label and arity combinations, such as a terminal
with daughters, are expressible; `IsWellFormed` excludes them where a theorem needs it, and `rec'`
sends them to a case of their own. That each binder binds a trace of its index is a property of a
tree, not a guarantee of the type, and interpretation does not read the category on a binder.

`Tree C W` abbreviates `RoseTree (Label C W)`, so the rose tree's navigation (`children`,
`t[p]?`) returns `RoseTree (Label C W)`. Dot notation for this file's operations does not
resolve on those results, so write `Tree.cat s`, and write constructor patterns on them as
`Tree.node`: an anonymous `.node` would elaborate as `RoseTree.node`, which matches any label.

## References

* [heim-kratzer-1998]
* [may-1985]
* [chomsky-1995]
* [katzir-2007]
-/

@[expose] public section

namespace PhraseStructure

namespace Tree

/-- A phrase is a projection, or an adjunction structure, a further segment of the category of
its host daughter. -/
inductive PhraseKind where
  | projection
  | adjunction
  deriving DecidableEq, Repr

/-- A node of a constituency tree carries a terminal's category and word, a phrase's category and
kind, or a trace's or binder's index and category. -/
inductive Label (C W : Type*) where
  | terminal : C → W → Label C W
  | phrase : C → PhraseKind → Label C W
  | trace : ℕ → C → Label C W
  | bind : ℕ → C → Label C W
  deriving DecidableEq, Repr

namespace Label

variable {C W W' : Type*}

/-- The category a label carries. -/
def cat : Label C W → C
  | .terminal c _ | .phrase c _ | .trace _ c | .bind _ c => c

/-- A terminal label carries a category and a word; other labels carry none. -/
def terminal? : Label C W → Option (C × W)
  | .terminal c w => some (c, w)
  | _ => none

/-- `mapWord f` relabels the word of a terminal label. -/
def mapWord (f : W → W') : Label C W → Label C W'
  | .terminal c w => .terminal c (f w)
  | .phrase c k => .phrase c k
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
  | .phrase _ _, _ => True
  | .trace _ _, ks => ks = []
  | .bind _ _, ks => ks.length = 1

instance : ∀ (l : Label C W) (ks : List (Label C W)), Decidable (Licenses l ks)
  | .terminal _ _, ks => inferInstanceAs (Decidable (ks = []))
  | .phrase _ _, _ => inferInstanceAs (Decidable True)
  | .trace _ _, ks => inferInstanceAs (Decidable (ks = []))
  | .bind _ _, ks => inferInstanceAs (Decidable (ks.length = 1))

/-- A label is phrasal when it puts a category over daughters. -/
def IsPhrase : Label C W → Prop
  | .phrase _ _ => True
  | _ => False

instance : DecidablePred (IsPhrase (C := C) (W := W)) := fun l ↦ by
  cases l <;> unfold IsPhrase <;> infer_instance

/-- A label is a segment label when it marks the mother of an adjunction. -/
def IsSegment : Label C W → Prop
  | .phrase _ .adjunction => True
  | _ => False

instance : DecidablePred (IsSegment (C := C) (W := W)) := fun l ↦ by
  rcases l with _ | ⟨_, _ | _⟩ | _ | _ <;> unfold IsSegment <;> infer_instance

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

/-- `phrase c k cs` is the phrase of category `c` and kind `k` over daughters `cs`. -/
@[match_pattern] abbrev phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) : Tree C W :=
  RoseTree.node (.phrase c k) cs

/-- `node c cs` is the category `c` over daughters `cs`. -/
@[match_pattern] abbrev node (c : C) (cs : List (Tree C W)) : Tree C W := phrase c .projection cs

/-- `adjoin c cs` is the category `c` over daughters `cs`, one of which is its host of category
`c`, the others adjoined to it. -/
@[match_pattern] abbrev adjoin (c : C) (cs : List (Tree C W)) : Tree C W :=
  phrase c .adjunction cs

/-- `trace n c` is a trace of index `n`. -/
@[match_pattern] abbrev trace (n : ℕ) (c : C) : Tree C W := RoseTree.node (.trace n c) []

/-- `bind n c t` is a binder of index `n` over `t`. -/
@[match_pattern] abbrev bind (n : ℕ) (c : C) (t : Tree C W) : Tree C W :=
  RoseTree.node (.bind n c) [t]

/-- `leaf w` is the word `w`, in a tree without categories. -/
@[match_pattern] abbrev leaf (w : W) : Tree Unit W := terminal () w

/-- `bin t₁ t₂` is the binary node over `t₁` and `t₂`, in a tree without categories. -/
@[match_pattern] abbrev bin (t₁ t₂ : Tree Unit W) : Tree Unit W := node () [t₁, t₂]

/-- `tr n` is the trace of index `n`, in a tree without categories. -/
@[match_pattern] abbrev tr (n : ℕ) : Tree Unit W := trace n ()

/-- `binder n t` is the binder of index `n` over `t`, in a tree without categories. -/
@[match_pattern] abbrev binder (n : ℕ) (t : Tree Unit W) : Tree Unit W := bind n () t

/-- The category at the root. -/
def cat (t : Tree C W) : C := t.value.cat

@[simp] theorem cat_terminal (c : C) (w : W) : (terminal c w).cat = c := rfl
@[simp] theorem cat_phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).cat = c := rfl
@[simp] theorem cat_trace (n : ℕ) (c : C) : (trace n c : Tree C W).cat = c := rfl
@[simp] theorem cat_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).cat = c := rfl

/-- A tree is well formed when every node has the daughters its label licenses. -/
def IsWellFormed (t : Tree C W) : Prop := t.Licensed Label.Licenses

instance (t : Tree C W) : Decidable t.IsWellFormed :=
  inferInstanceAs (Decidable (t.Licensed _))

/-! ### Induction -/

/-- Induction over the four shapes, with the hypothesis at every daughter, and a case for the
nodes whose daughters their label does not license. -/
@[elab_as_elim]
def rec' {motive : Tree C W → Sort*}
    (terminal : ∀ c w, motive (terminal c w))
    (phrase : ∀ c k cs, (∀ t ∈ cs, motive t) → motive (phrase c k cs))
    (trace : ∀ n c, motive (trace n c))
    (bind : ∀ n c t, motive t → motive (bind n c t))
    (junk : ∀ l cs, ¬ Label.Licenses l (cs.map RoseTree.value) → (∀ t ∈ cs, motive t) →
      motive (RoseTree.node l cs))
    (t : Tree C W) : motive t :=
  RoseTree.rec' (motive := motive) (fun l cs ih ↦
    match l, cs, ih with
    | .terminal c w, [], _ => terminal c w
    | .terminal _ _, _ :: _, ih => junk _ _ (by simp [Label.Licenses]) ih
    | .phrase c k, cs, ih => phrase c k cs ih
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

@[simp] theorem map_phrase (f : W → W') (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).map f = phrase c k (cs.map (map f)) := by
  simp [map, phrase, Label.mapWord]

@[simp] theorem map_trace (f : W → W') (n : ℕ) (c : C) : (trace n c).map f = trace n c := rfl

@[simp] theorem map_bind (f : W → W') (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).map f = bind n c (t.map f) := by
  simp [map, bind, Label.mapWord]

section Inversion

variable {f : W → W'} {t : Tree C W} {c : C}

theorem map_eq_terminal_iff {w' : W'} :
    t.map f = terminal c w' ↔ ∃ w, t = terminal c w ∧ f w = w' := by
  refine ⟨fun h ↦ ?_, fun ⟨w, ht, hw⟩ ↦ by rw [ht, map_terminal, hw]⟩
  rcases t with ⟨l, cs⟩
  cases l <;> simp_all [map_rose, Label.mapWord]

theorem map_eq_phrase_iff {k : PhraseKind} {cs' : List (Tree C W')} :
    t.map f = phrase c k cs' ↔ ∃ cs, t = phrase c k cs ∧ cs.map (map f) = cs' := by
  refine ⟨fun h ↦ ?_, fun ⟨cs, ht, hcs⟩ ↦ by rw [ht, map_phrase, hcs]⟩
  rcases t with ⟨l, cs⟩
  cases l <;> simp_all [map_rose, Label.mapWord]

theorem map_eq_trace_iff {n : ℕ} : t.map f = trace n c ↔ t = trace n c := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_trace]⟩
  rcases t with ⟨l, cs⟩
  cases l <;> simp_all [map_rose, Label.mapWord]

theorem map_eq_bind_iff {n : ℕ} {b' : Tree C W'} :
    t.map f = bind n c b' ↔ ∃ b, t = bind n c b ∧ b.map f = b' := by
  refine ⟨fun h ↦ ?_, fun ⟨b, ht, hb⟩ ↦ by rw [ht, map_bind, hb]⟩
  rcases t with ⟨l, cs⟩
  cases l <;> simp_all [map_rose, Label.mapWord, List.map_eq_singleton_iff]

end Inversion

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

@[simp] theorem terminals_phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).terminals = cs.flatMap terminals := by
  rcases cs with _ | ⟨c', cs⟩
  · rfl
  · simp only [terminals, phrase, RoseTree.leafList_node_cons, List.filterMap_flatten,
      List.map_map, List.flatMap_def]
    rfl

@[simp] theorem terminals_trace (n : ℕ) (c : C) : (trace n c : Tree C W).terminals = [] := rfl

@[simp] theorem terminals_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).terminals = t.terminals := by
  simp [terminals, bind, RoseTree.leafList_node_of_ne_nil]

@[simp] theorem yield_terminal (c : C) (w : W) : (terminal c w).yield = [w] := rfl

@[simp] theorem yield_phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).yield = cs.flatMap yield := by
  simp only [yield, terminals_phrase, List.map_flatMap]
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

@[simp] theorem cats_phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).cats = c :: cs.flatMap cats :=
  cats_rose _ cs

@[simp] theorem cats_trace (n : ℕ) (c : C) : (trace n c : Tree C W).cats = [c] := rfl

@[simp] theorem cats_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).cats = c :: t.cats := by
  simp [cats, bind, Label.cat]

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

theorem freeIndices_phrase (c : C) (k : PhraseKind) (cs : List (Tree C W)) :
    (phrase c k cs).freeIndices = (cs.map freeIndices).foldr (· ∪ ·) ∅ := by
  simp [freeIndices, phrase]

@[simp] theorem freeIndices_trace (n : ℕ) (c : C) : (trace n c : Tree C W).freeIndices = {n} := by
  simp [freeIndices]

@[simp] theorem freeIndices_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).freeIndices = t.freeIndices.erase n := by
  simp only [freeIndices, bind, RoseTree.fold_node, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil]
  congr 1
  ext
  simp

@[simp] theorem mem_freeIndices_phrase {i : ℕ} {c : C} {k : PhraseKind} {cs : List (Tree C W)} :
    i ∈ (phrase c k cs).freeIndices ↔ ∃ t ∈ cs, i ∈ t.freeIndices := by
  rw [freeIndices_phrase]
  induction cs with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- A tree is closed when no trace is free in it. -/
def Closed (t : Tree C W) : Prop := t.freeIndices = ∅

instance [DecidableEq C] [DecidableEq W] (t : Tree C W) : Decidable t.Closed :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Word substitution -/

/-- Replace the word `w` by `w'` at every terminal of category `c`, the substitution of a
same-category lexical item of [katzir-2007]. -/
def leafSubst [DecidableEq C] [DecidableEq W] (w w' : W) (c : C) (t : Tree C W) : Tree C W :=
  RoseTree.map (fun
    | .terminal c' v => .terminal c' (if c = c' ∧ v = w then w' else v)
    | l => l) t

section LeafSubst

variable [DecidableEq C] [DecidableEq W] (w w' : W) (c : C)

@[simp] theorem leafSubst_terminal (c' : C) (v : W) :
    leafSubst w w' c (terminal c' v) = terminal c' (if c = c' ∧ v = w then w' else v) := rfl

@[simp] theorem leafSubst_phrase (c' : C) (k : PhraseKind) (cs : List (Tree C W)) :
    leafSubst w w' c (phrase c' k cs) = phrase c' k (cs.map (leafSubst w w' c)) := by
  simp [leafSubst, phrase]

@[simp] theorem leafSubst_trace (n : ℕ) (c' : C) :
    leafSubst w w' c (trace n c') = trace n c' := rfl

@[simp] theorem leafSubst_bind (n : ℕ) (c' : C) (t : Tree C W) :
    leafSubst w w' c (bind n c' t) = bind n c' (leafSubst w w' c t) := by
  simp [leafSubst, bind]

end LeafSubst

/-! ### Positions of the terminals

A tree takes Gorn addresses as a rose tree, and with them the dominance order on its positions and,
in `Syntax/Tree/Command.lean`, the command relations. The terminals, paired with their positions,
are the word-bearing leaves, so the order of the yield is precedence
(`RoseTree.pairwise_precedes_positionedLeaves`). -/

open Core.Order

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

theorem getElem?_of_mem_positionedTerminals {t : Tree C W} {x : TreePath × (C × W)}
    (h : x ∈ t.positionedTerminals) :
    t[x.1.toList]? = some (terminal x.2.1 x.2.2) := by
  obtain ⟨⟨p, l⟩, hl, hx⟩ := List.mem_filterMap.mp h
  cases l with
  | terminal c w =>
    obtain rfl : (p, (c, w)) = x := by simpa [Label.terminal?] using hx
    exact RoseTree.mem_positionedLeaves.mp hl
  | _ => simp [Label.terminal?] at hx

theorem mem_positionedTerminals_of_getElem? {t : Tree C W} {p : List ℕ} {c : C} {w : W}
    (h : t[p]? = some (terminal c w)) :
    (⟨p⟩, (c, w)) ∈ t.positionedTerminals :=
  List.mem_filterMap.mpr ⟨_, RoseTree.mem_positionedLeaves.mpr h, rfl⟩

/-- The terminal positions, in the order of the yield, ascend in precedence. -/
theorem pairwise_precedes_positionedTerminals (t : Tree C W) :
    t.positionedTerminals.Pairwise fun x y ↦ x.1.Precedes y.1 :=
  (RoseTree.pairwise_precedes_positionedLeaves _).filterMap _ fun _ _ h _ ha _ hb ↦ by
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact h

end Tree

end PhraseStructure
