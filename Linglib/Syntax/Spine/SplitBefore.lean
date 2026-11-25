/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Spine.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.SplitBy
public import Mathlib.Data.List.TakeWhile

/-!
# Splitting a spine before a class of heads

A class of heads `p` divides a spine into consecutive stretches: a new stretch begins at each
head satisfying `p`, and the heads below the first such head form a stretch of their own. We
define `s.splitBefore p`, the list of these stretches from the bottom up. The head chains of
[arregi-pietraszko-2021] are the stretches that begin at the heads not sharing an M-value with
the head below, and the last spell-out cycle of a complex head, in
`Linglib/Morphology/DistributedMorphology/Locality.lean`, is the highest stretch before its
cyclic heads.

The stretches of a spine are characterized by four conditions: they flatten to the spine, none
is empty, no head of a stretch but its lowest satisfies `p`, and the lowest head of every stretch
but the first does. Their number is one more than the number of heads satisfying `p` above the
lowest head of the spine, so that in a truncation of the spine the highest stretch is numbered
by the heads satisfying `p` it has passed.

## Main definitions

* `Spine.splitBefore`: the stretches of a spine, a new one beginning at each head of a class.

## Main results

* `Spine.splitBefore_eq_iff`: the characterization of the stretches.
* `Spine.splitBefore_cons`: the lowest stretch is the lowest head with the heads above it up to
  the first in the class, and the others are the stretches of the rest.
* `Spine.length_splitBefore`: the number of stretches.
* `Spine.splitBefore_append_singleton_of_pos`, `Spine.splitBefore_append_singleton_of_neg`: a head
  merged over a spine starts a new stretch if it is in the class and joins the highest if not.

## Implementation notes

`Spine.splitBefore` is `List.splitBy` at the relation joining a head to the one below it unless
it is in the class. The stretches are a list and not a partition of the positions, so that they
come in order and can be counted.

## References

* [arregi-pietraszko-2021]
-/

@[expose] public section

namespace Spine
variable {H : Type*} {s : Spine H} {p : H → Prop} [DecidablePred p] {b : List H} {a h : H}
  {l : List H}

/-- The stretches of a spine before the heads of a class, from the bottom up: a new stretch begins
at each head satisfying `p`. -/
def splitBefore (s : Spine H) (p : H → Prop) [DecidablePred p] : List (List H) :=
  s.heads.splitBy fun _ b ↦ !decide (p b)

@[simp] theorem flatten_splitBefore (s : Spine H) (p : H → Prop) [DecidablePred p] :
    (s.splitBefore p).flatten = s.heads :=
  List.flatten_splitBy _ _

theorem infix_of_mem_splitBefore (h : b ∈ s.splitBefore p) : b <:+: s.heads :=
  flatten_splitBefore s p ▸ List.infix_of_mem_flatten h

private theorem isChain_snd {α : Type*} {Q : α → Prop} {l : List α} :
    l.IsChain (fun _ y ↦ Q y) ↔ ∀ y ∈ l.tail, Q y := by
  induction l with
  | nil => simp
  | cons a l ih => cases l with
    | nil => simp
    | cons b l => simp_all [List.isChain_cons_cons]

/-- The stretches of a spine before a class of heads are the lists that flatten to it, none empty,
in which no head but the lowest of a stretch is in the class and the lowest of every stretch but
the first is. -/
theorem splitBefore_eq_iff {bs : List (List H)} :
    s.splitBefore p = bs ↔ s.heads = bs.flatten ∧ [] ∉ bs ∧ (∀ b ∈ bs, ∀ x ∈ b.tail, ¬ p x) ∧
      ∀ b ∈ bs.tail, ∀ x ∈ b.head?, p x := by
  rw [splitBefore, List.splitBy_eq_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun hn ↦ and_congr ?_ ?_
  · exact forall₂_congr fun b _ ↦ (List.IsChain.iff (by simp)).trans isChain_snd
  · rw [List.IsChain.iff_mem, ← isChain_snd (Q := fun b : List H ↦ ∀ x ∈ b.head?, p x),
      List.IsChain.iff_mem (R := fun _ b : List H ↦ ∀ x ∈ b.head?, p x)]
    refine List.IsChain.iff fun a b ↦ and_congr_right fun ha ↦ and_congr_right fun hb ↦ ?_
    have ha' : a ≠ [] := fun h ↦ hn (h ▸ ha)
    cases b with
    | nil => exact absurd hb hn
    | cons x b =>
      simp only [ha', ne_eq, not_false_eq_true, exists_true_left, List.head_cons,
        Bool.not_eq_false', List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq',
        reduceCtorEq, exists_const]
      exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The lowest stretch is the lowest head with the heads above it up to the first in the class,
and the others are the stretches of the rest. -/
theorem splitBefore_cons :
    (⟨a :: l⟩ : Spine H).splitBefore p =
      (a :: l.takeWhile (fun x ↦ !decide (p x))) ::
        (⟨l.dropWhile fun x ↦ !decide (p x)⟩ : Spine H).splitBefore p := by
  have h := List.splitBy_append (r := fun _ b ↦ !decide (p b))
    (l := a :: l.takeWhile fun x ↦ !decide (p x)) (m := l.dropWhile fun x ↦ !decide (p x))
    fun _ _ y hy ↦ by
      have := List.head?_dropWhile_not (fun x ↦ !decide (p x)) l
      rw [Option.mem_def.1 hy] at this
      exact this
  rw [List.cons_append, List.takeWhile_append_dropWhile] at h
  have hc : (a :: l.takeWhile fun x ↦ !decide (p x)).IsChain
      fun _ y ↦ (!decide (p y)) = true :=
    (List.IsChain.iff (by simp)).2 <| (isChain_snd (Q := fun y ↦ ¬ p y)).2 fun y hy ↦ by
      simpa using List.mem_takeWhile_imp hy
  rw [splitBefore, h, List.splitBy_of_isChain (List.cons_ne_nil _ _) hc]
  rfl

private theorem length_splitBy_aux : ∀ (n : ℕ) (l : List H), l.length = n → l ≠ [] →
    (l.splitBy fun _ b ↦ !decide (p b)).length = l.tail.countP (p ·) + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro (_ | ⟨a, l⟩) hn hl
    · exact absurd rfl hl
    have hc := splitBefore_cons (a := a) (l := l) (p := p)
    simp only [splitBefore] at hc
    rw [hc, List.length_cons, List.tail_cons,
      ← List.takeWhile_append_dropWhile (p := fun x ↦ !decide (p x)) (l := l), List.countP_append,
      List.takeWhile_append_dropWhile,
      List.countP_eq_zero.2 fun y hy ↦ by simpa using List.mem_takeWhile_imp hy, Nat.zero_add]
    rcases hd : l.dropWhile (fun x ↦ !decide (p x)) with _ | ⟨x, m⟩
    · simp
    · have hx : p x := by
        have := List.head?_dropWhile_not (fun x ↦ !decide (p x)) l
        simpa [hd] using this
      have hlen : (x :: m).length < n := by
        have := List.length_dropWhile_le (fun x ↦ !decide (p x)) l
        simp only [hd, List.length_cons] at this hn ⊢
        omega
      rw [ih _ hlen (x :: m) rfl (List.cons_ne_nil _ _)]
      simp [hx]

/-- A spine has one stretch, and one more for each head of the class above its lowest head. -/
theorem length_splitBefore (hs : s.heads ≠ []) :
    (s.splitBefore p).length = s.heads.tail.countP (p ·) + 1 :=
  length_splitBy_aux _ _ rfl hs
/-- Merging a head of the class starts a new stretch. -/
theorem splitBefore_append_singleton_of_pos (s : Spine H) (hp : p h) :
    (s.append [h]).splitBefore p = s.splitBefore p ++ [[h]] := by
  rw [splitBefore, heads_append, List.splitBy_append_cons [] fun _ _ ↦ by simpa using hp]
  rfl

/-- Merging a head outside the class extends the highest stretch. -/
theorem splitBefore_append_singleton_of_neg (s : Spine H) (hp : ¬ p h) :
    (s.append [h]).splitBefore p =
      (s.splitBefore p).dropLast ++ [(s.splitBefore p).getLast?.getD [] ++ [h]] := by
  obtain ⟨l⟩ := s
  rcases eq_or_ne l [] with rfl | hl
  · simp only [splitBefore, append, List.nil_append, List.splitBy_nil, List.dropLast_nil,
      List.getLast?_nil, Option.getD_none]
    rfl
  have hmain := (splitBefore_eq_iff (s := ⟨l⟩) (p := p)).1 rfl
  obtain ⟨d, last, hbs⟩ : ∃ d last, (⟨l⟩ : Spine H).splitBefore p = d ++ [last] :=
    ⟨_, _, (List.dropLast_append_getLast (List.splitBy_ne_nil.2 hl)).symm⟩
  rw [hbs] at hmain
  obtain ⟨hflat, hnil, htail, hhead⟩ := hmain
  have hlast : last ≠ [] := fun h ↦ hnil (by simp [h])
  have hl' : l = d.flatten ++ last := by simpa using hflat
  rw [hbs, List.dropLast_concat, List.getLast?_concat, Option.getD_some, splitBefore_eq_iff]
  refine ⟨by simp [hl'], ?_, ?_, ?_⟩
  · simpa using fun hd ↦ hnil (by simp [hd])
  · intro b hb x hx
    rcases List.mem_append.1 hb with hb | hb
    · exact htail b (List.mem_append_left _ hb) x hx
    · obtain rfl := List.mem_singleton.1 hb
      rw [List.tail_append_of_ne_nil hlast] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact htail last (by simp) x hx
      · simpa [List.mem_singleton.1 hx] using hp
  · intro b hb x hx
    cases d with
    | nil => simp at hb
    | cons d₀ d =>
      simp only [List.cons_append, List.tail_cons] at hb hhead
      rcases List.mem_append.1 hb with hb | hb
      · exact hhead b (List.mem_append_left _ hb) x hx
      · obtain rfl := List.mem_singleton.1 hb
        rw [List.head?_append_of_ne_nil _ hlast] at hx
        exact hhead last (by simp) x hx
end Spine
