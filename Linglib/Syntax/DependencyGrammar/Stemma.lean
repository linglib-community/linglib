/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity

/-!
# Stemmas

A stemma is a dependency tree as it is drawn: a head with its dependents to its left and to its
right, each dependent attached by a relation and heading a stemma of its own. Reading a stemma
from left to right spells out its sentence, and numbering the words of that sentence turns the
stemma into a dependency graph on positions, in which each word's head is the head it hangs from.
That graph is [a tree](##DependencyGrammar.Stemma.isTree_toGraph) and
[projective](##DependencyGrammar.Stemma.isProjective_toGraph): a stemma never draws crossing arcs.

## Main definitions

* `DependencyGrammar.Stemma`: the stemmas with relations in `L`.
* `Stemma.yield`: the sentence a stemma spells out.
* `Stemma.toGraph`, `Stemma.toTree`: the dependency graph on the positions of the sentence, and
  the same graph bundled as a tree.

## Implementation notes

The graph records, for each position, the position of its head and the relation to it
(`Stemma.heads`), so no position has two heads by construction.

## TODO

The converse: every projective tree is the graph of a stemma.

## References

* [tesniere-1959]
-/

@[expose] public section

namespace DependencyGrammar

open Morphology (Word)

/-- A stemma is a head word with its dependents to its left and to its right, in order, each
attached by a relation in `L` and heading a stemma of its own. -/
inductive Stemma (L : Type*) where
  | node (head : Word) (left right : List (L × Stemma L))

namespace Stemma

variable {L : Type*}

/-- The stemma of a word with no dependents. -/
abbrev leaf (w : Word) : Stemma L := node w [] []

mutual

/-- The sentence a stemma spells out: its left dependents, its head, its right dependents. -/
def yield : Stemma L → List Word
  | node w l r => yieldDeps l ++ w :: yieldDeps r

/-- The words a list of dependents spells out. -/
def yieldDeps : List (L × Stemma L) → List Word
  | [] => []
  | (_, d) :: ds => yield d ++ yieldDeps ds

end

mutual

/-- The number of words of a stemma. -/
def size : Stemma L → ℕ
  | node _ l r => sizeDeps l + 1 + sizeDeps r

/-- The number of words of a list of dependents. -/
def sizeDeps : List (L × Stemma L) → ℕ
  | [] => 0
  | (_, d) :: ds => size d + sizeDeps ds

end

/-- The position of a stemma's head in its sentence. -/
def headIndex : Stemma L → ℕ
  | node _ l _ => sizeDeps l

mutual

/-- The head and relation of each word of a stemma laid out from position `o`, the head word's
being `up`. -/
def heads (o : ℕ) (up : Option (ℕ × L)) : Stemma L → List (Option (ℕ × L))
  | node _ l r =>
    let h := o + sizeDeps l
    headsDeps h o l ++ up :: headsDeps h (h + 1) r

/-- The head and relation of each word of a list of dependents of the head at `h`, laid out from
position `o`. -/
def headsDeps (h o : ℕ) : List (L × Stemma L) → List (Option (ℕ × L))
  | [] => []
  | (rel, d) :: ds => heads o (some (h, rel)) d ++ headsDeps h (o + size d) ds

end

mutual

theorem length_yield : ∀ s : Stemma L, s.yield.length = s.size
  | node _ l r => by simp [yield, size, length_yieldDeps l, length_yieldDeps r]; omega

theorem length_yieldDeps : ∀ ds : List (L × Stemma L), (yieldDeps ds).length = sizeDeps ds
  | [] => rfl
  | (_, d) :: ds => by simp [yieldDeps, sizeDeps, length_yield d, length_yieldDeps ds]

end

theorem headIndex_lt_size (s : Stemma L) : s.headIndex < s.size := by
  cases s; simp only [headIndex, size]; omega

/-- A stemma has at least its head word, so numerals denote its positions. -/
instance (s : Stemma L) : NeZero s.size := ⟨by cases s; simp [size]⟩

/-- The dependency graph on the positions of a stemma's sentence: an arc from each word's head to
the word, labelled with its relation, rooted at the stemma's head. -/
def toGraph (s : Stemma L) : Graph L s.size where
  words v := s.yield[v.val]'(by rw [length_yield]; exact v.isLt)
  label v w := ((s.heads 0 none)[w.val]?.bind id).bind fun p ↦
    if p.1 = v.val then some p.2 else none
  root := ⟨s.headIndex, s.headIndex_lt_size⟩

mutual

theorem length_heads : ∀ (s : Stemma L) (o : ℕ) (up : Option (ℕ × L)),
    (s.heads o up).length = s.size
  | node _ l r, o, up => by
    simp only [heads, size, List.length_append, List.length_cons, length_headsDeps l _ o,
      length_headsDeps r _ (o + sizeDeps l + 1)]
    omega

theorem length_headsDeps : ∀ (ds : List (L × Stemma L)) (h o : ℕ),
    (headsDeps h o ds).length = sizeDeps ds
  | [], _, _ => rfl
  | (rel, d) :: ds, h, o => by
    simp only [headsDeps, sizeDeps, List.length_append, length_heads d o (some (h, rel)),
      length_headsDeps ds h (o + size d)]

end

/-- The head word of a stemma records the head it hangs from. -/
theorem getElem?_heads_headIndex (s : Stemma L) (o : ℕ) (up : Option (ℕ × L)) :
    (s.heads o up)[s.headIndex]? = some up := by
  cases s with
  | node w l r =>
    simp [heads, headIndex, length_headsDeps]

/-- Two positions are linked by an arc of a stemma's graph when the first is recorded as the
head of the second. -/
theorem toGraph_adj {s : Stemma L} {v w : Fin s.size} :
    s.toGraph.Adj v w ↔ ∃ r, (s.heads 0 none)[w.val]? = some (some (v.val, r)) := by
  simp only [Graph.Adj, toGraph]
  rcases h : (s.heads 0 none)[w.val]? with _ | _ | ⟨u, r⟩ <;> simp

/-! ### Tree-hood and projectivity -/

section Layout

open Relation

/-- `v` is the head recorded for `w` in the head list `H`. -/
private def HeadIn (H : List (Option (ℕ × L))) (v w : ℕ) : Prop :=
  ∃ r, H[w]? = some (some (v, r))

/-- `xs` occurs in `H` from position `o`. -/
private def Occurs {α : Type*} (H : List α) (o : ℕ) (xs : List α) : Prop :=
  ∀ i, i < xs.length → H[o + i]? = xs[i]?

private theorem occurs_append {α : Type*} {H xs ys : List α} {o : ℕ} :
    Occurs H o (xs ++ ys) → Occurs H o xs ∧ Occurs H (o + xs.length) ys := by
  intro h
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [h i (by simp; omega), List.getElem?_append_left hi]
  · rw [Nat.add_assoc, h (xs.length + i) (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp

private theorem occurs_cons {α : Type*} {H xs : List α} {x : α} {o : ℕ} :
    Occurs H o (x :: xs) → H[o]? = some x ∧ Occurs H (o + 1) xs := by
  intro h
  refine ⟨by simpa using h 0 (by simp), fun i hi ↦ ?_⟩
  rw [Nat.add_assoc, Nat.add_comm 1 i, h (i + 1) (by simp; omega)]
  simp

variable (H : List (Option (ℕ × L)))

mutual

/-- Laid out from `o`, a stemma's head dominates its block, and every arc into the block other
than the head's stays inside the block, its head dominating every position it spans. -/
private theorem layout : ∀ (s : Stemma L) (o : ℕ) (up : Option (ℕ × L)),
    Occurs H o (s.heads o up) →
      (∀ p, o ≤ p → p < o + s.size → ReflTransGen (HeadIn H) (o + s.headIndex) p) ∧
      ∀ v w, o ≤ w → w < o + s.size → w ≠ o + s.headIndex → HeadIn H v w →
        o ≤ v ∧ v < o + s.size ∧
          ∀ p, (v ≤ p ∧ p ≤ w ∨ w ≤ p ∧ p ≤ v) → ReflTransGen (HeadIn H) v p
  | node _ l r, o, up, hocc => by
    simp only [heads] at hocc
    obtain ⟨hl, hrest⟩ := occurs_append hocc
    rw [length_headsDeps] at hrest
    obtain ⟨-, hr⟩ := occurs_cons hrest
    have Ql := layoutDeps l (o + sizeDeps l) o hl
    have Qr := layoutDeps r (o + sizeDeps l) (o + sizeDeps l + 1) hr
    simp only [size, headIndex]
    have hA : ∀ p, o ≤ p → p < o + (sizeDeps l + 1 + sizeDeps r) →
        ReflTransGen (HeadIn H) (o + sizeDeps l) p := by
      intro p hp₁ hp₂
      rcases lt_trichotomy p (o + sizeDeps l) with hp | rfl | hp
      · exact Ql.1 p hp₁ hp
      · exact .refl
      · exact Qr.1 p (by omega) (by omega)
    refine ⟨hA, fun v w hw₁ hw₂ hne hvw ↦ ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with hw | hw
    · rcases Ql.2 v w hw₁ hw hvw with rfl | ⟨hv₁, hv₂, h⟩
      · exact ⟨by omega, by omega, fun p hp ↦ hA p (by omega) (by omega)⟩
      · exact ⟨hv₁, by omega, h⟩
    · rcases Qr.2 v w (by omega) (by omega) hvw with rfl | ⟨hv₁, hv₂, h⟩
      · exact ⟨by omega, by omega, fun p hp ↦ hA p (by omega) (by omega)⟩
      · exact ⟨by omega, by omega, h⟩

/-- Laid out from `o` under the head at `h`, a list of dependents is dominated by `h`, and every
arc into its block comes from `h` or stays inside the block, its head dominating every position
it spans. -/
private theorem layoutDeps : ∀ (ds : List (L × Stemma L)) (h o : ℕ),
    Occurs H o (headsDeps h o ds) →
      (∀ p, o ≤ p → p < o + sizeDeps ds → ReflTransGen (HeadIn H) h p) ∧
      ∀ v w, o ≤ w → w < o + sizeDeps ds → HeadIn H v w →
        v = h ∨ (o ≤ v ∧ v < o + sizeDeps ds ∧
          ∀ p, (v ≤ p ∧ p ≤ w ∨ w ≤ p ∧ p ≤ v) → ReflTransGen (HeadIn H) v p)
  | [], _, o, _ => by
    simp only [sizeDeps]
    exact ⟨fun p hp₁ hp₂ ↦ by omega, fun v w hw₁ hw₂ ↦ by omega⟩
  | (rel, d) :: ds, h, o, hocc => by
    simp only [headsDeps] at hocc
    obtain ⟨hd, hds⟩ := occurs_append hocc
    rw [length_heads] at hds
    have P := layout d o (some (h, rel)) hd
    have Q := layoutDeps ds h (o + size d) hds
    have hhead : H[o + d.headIndex]? = some (some (h, rel)) := by
      rw [hd d.headIndex (by rw [length_heads]; exact d.headIndex_lt_size),
        getElem?_heads_headIndex]
    simp only [sizeDeps]
    refine ⟨fun p hp₁ hp₂ ↦ ?_, fun v w hw₁ hw₂ hvw ↦ ?_⟩
    · by_cases hp : p < o + size d
      · exact .head ⟨rel, hhead⟩ (P.1 p hp₁ hp)
      · exact Q.1 p (by omega) (by omega)
    · by_cases hw : w < o + size d
      · by_cases he : w = o + d.headIndex
        · obtain ⟨r, hr⟩ := hvw
          rw [he, hhead] at hr
          exact .inl (by simp at hr; exact hr.1.symm)
        · obtain ⟨hv₁, hv₂, hreach⟩ := P.2 v w hw₁ hw he hvw
          exact .inr ⟨hv₁, by omega, hreach⟩
      · rcases Q.2 v w (by omega) (by omega) hvw with rfl | ⟨hv₁, hv₂, hreach⟩
        · exact .inl rfl
        · exact .inr ⟨by omega, by omega, hreach⟩

end

private theorem dominates_of_reflTransGen {s : Stemma L} {a b : ℕ} (ha : a < s.size)
    (h : ReflTransGen (HeadIn (s.heads 0 none)) a b) :
    ∃ hb : b < s.size, Dominates s.toGraph ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact ⟨ha, .refl⟩
  | tail _ hcb ih =>
    obtain ⟨hc, hd⟩ := ih
    obtain ⟨r, hr⟩ := hcb
    obtain ⟨hb, -⟩ := List.getElem?_eq_some_iff.1 hr
    rw [length_heads] at hb
    exact ⟨hb, hd.tail (toGraph_adj.2 ⟨r, hr⟩)⟩

private theorem occurs_self {α : Type*} (H : List α) : Occurs H 0 H := fun _ _ ↦ by simp

private theorem not_adj_root {s : Stemma L} {v : Fin s.size} : ¬ s.toGraph.Adj v s.toGraph.root :=
  fun hv ↦ by
    obtain ⟨r, hr⟩ := toGraph_adj.1 hv
    simp [toGraph, getElem?_heads_headIndex] at hr

/-- The graph of a stemma is a tree. -/
theorem isTree_toGraph (s : Stemma L) : s.toGraph.IsTree := by
  refine Graph.isTree_iff_leftUnique_adj.2 ⟨fun u v w hu hv ↦ ?_, fun _ ↦ not_adj_root, fun v ↦ ?_⟩
  · obtain ⟨r, hr⟩ := toGraph_adj.1 hu
    obtain ⟨r', hr'⟩ := toGraph_adj.1 hv
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    exact Fin.ext hr'.1
  · have := (layout _ s 0 none (occurs_self _)).1 v (Nat.zero_le _) (by simp)
    rw [Nat.zero_add] at this
    exact (dominates_of_reflTransGen s.headIndex_lt_size this).2

/-- The graph of a stemma is projective: a stemma never draws crossing arcs. -/
theorem isProjective_toGraph (s : Stemma L) : s.toGraph.IsProjective := by
  refine s.toGraph.isProjective_iff_isArcProjective.2 fun h d hhd p hp ↦ ?_
  obtain ⟨r, hr⟩ := toGraph_adj.1 hhd
  have hne : d.val ≠ 0 + s.headIndex := fun he ↦ not_adj_root (s := s) (v := h) <| by
    rw [Nat.zero_add] at he
    have : d = s.toGraph.root := Fin.ext he
    exact this ▸ hhd
  obtain ⟨-, -, hreach⟩ :=
    (layout _ s 0 none (occurs_self _)).2 h d (Nat.zero_le _) (by simp) hne ⟨r, hr⟩
  have hp' : h.val ≤ p.val ∧ p.val ≤ d.val ∨ d.val ≤ p.val ∧ p.val ≤ h.val := by
    rcases Set.mem_uIcc.1 hp with hp | hp
    exacts [.inl hp, .inr hp]
  exact (dominates_of_reflTransGen h.isLt (hreach p hp')).2

end Layout

/-- The dependency tree of a stemma. -/
def toTree (s : Stemma L) : Tree L s.size := ⟨s.toGraph, s.isTree_toGraph⟩

end Stemma

end DependencyGrammar
