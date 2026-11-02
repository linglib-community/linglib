/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Sections
public import Mathlib.Data.Multiset.Bind

/-!
# Sections of a replicated list

This file proves facts about `List.sections` of `replicate n l`, the list of words of length `n`
over the alphabet `l`: membership, compatibility with `map`, and the recursion in the length as a
multiset bind.
-/

public section

namespace List

variable {α β : Type*}

theorem sections_map_map (f : α → β) (L : List (List α)) :
    (L.map (map f)).sections = L.sections.map (map f) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [map_cons, sections, ih, flatMap_map, map_flatMap, map_map]
    exact flatMap_congr fun s _ => by simp [Function.comp_def]

theorem sections_replicate_map (f : α → β) (n : ℕ) (l : List α) :
    (replicate n (l.map f)).sections = (replicate n l).sections.map (map f) := by
  rw [← map_replicate, sections_map_map]

theorem mem_sections_replicate {n : ℕ} {l s : List α} :
    s ∈ (replicate n l).sections ↔ s.length = n ∧ ∀ a ∈ s, a ∈ l := by
  induction n generalizing s with
  | zero =>
    simp only [replicate_zero, sections, mem_singleton, length_eq_zero_iff]
    exact ⟨fun h => ⟨h, by simp [h]⟩, And.left⟩
  | succ n ih =>
    cases s with
    | nil => simp [replicate_succ, sections]
    | cons a s => simp [replicate_succ, sections, ih, and_left_comm]

@[simp] theorem sections_replicate_singleton (a : α) (n : ℕ) :
    (replicate n [a]).sections = [replicate n a] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, sections, ih]

theorem sections_singleton (l : List α) : [l].sections = l.map ([·]) := by
  simp [sections]

theorem coe_sections_replicate_succ (n : ℕ) (l : List α) :
    ((replicate (n + 1) l).sections : Multiset (List α)) =
      (l : Multiset α).bind fun a =>
        ((replicate n l).sections : Multiset (List α)).map (a :: ·) := by
  rw [replicate_succ, sections, ← Multiset.coe_bind]
  simp only [← Multiset.map_coe, ← Multiset.bind_singleton]
  exact Multiset.bind_bind _ _

end List
