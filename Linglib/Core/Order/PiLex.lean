module

public import Mathlib.Order.PiLex
public import Mathlib.Order.Cover
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin

/-!
# The lexicographic order on finite tuples

This file relates `Pi.Lex` on `Fin n → α` to the lexicographic order on lists and characterizes it
by the first differing coordinate. The order on `Fin (n + 1)`-tuples compares heads and then tails
(`Pi.toLex_lt_toLex_iff_succ`), so it is the order of the tuples' lists (`List.ofFn_lex_lt_iff`,
`List.ofFn_le_ofFn_iff`); since the list order is decidable, so is the tuple order
(`Pi.Lex.decidableLT`, `Pi.Lex.decidableLE`), where mathlib's `LinearOrder` on `Pi.Lex` carries only
a classical instance. A tuple is lexicographically at most another when every coordinate where it
exceeds the other is preceded by one where it falls short (`Pi.lex_le_iff_forall`), which is to say
that it falls short at the first coordinate where they differ (`Pi.lex_le_iff_find`). Reindexing
both tuples along an equivalence transports the index relation (`Pi.lex_comp_equiv`). Read along an
enumeration `e` of the coordinates, one vector is below another iff some coordinate where it is
below comes before every coordinate where it is above (`Pi.toLex_comp_lt_iff_exists`), and the
product order is the intersection of these lexicographic orders over all enumerations
(`Pi.forall_toLex_comp_lt_iff`). Two vectors ordered oppositely along enumerations that differ by
transposing adjacent positions agree before those positions and are ordered oppositely at them
(`Pi.eq_and_lt_and_gt_of_toLex_comp_swap`).

[UPSTREAM] candidates for `Mathlib/Order/PiLex.lean` and `Mathlib/Data/List/OfFn.lean`.
-/

@[expose] public section

namespace Pi

/-- Reindexing both tuples along an equivalence `e : κ ≃ ι` transports the index relation of
the lexicographic order to its preimage along `e.symm`. -/
theorem lex_comp_equiv {κ ι β : Type*} (e : κ ≃ ι) (r : κ → κ → Prop) (s : β → β → Prop)
    (x y : ι → β) :
    Pi.Lex r (fun {_} ↦ s) (x ∘ e) (y ∘ e) ↔
      Pi.Lex (fun i j ↦ r (e.symm i) (e.symm j)) (fun {_} ↦ s) x y := by
  constructor
  · rintro ⟨k, hk, hs⟩
    exact ⟨e k, fun j hj ↦ by simpa using hk (e.symm j) (by simpa using hj), hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨e.symm i, fun k hk ↦ by simpa using hi (e k) (by simpa using hk), by simpa using hs⟩

end Pi

namespace Pi

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- The lexicographic order on `Fin (n + 1)`-tuples compares heads, then tails. -/
theorem toLex_lt_toLex_iff_succ (f g : Fin (n + 1) → α) :
    toLex f < toLex g ↔ f 0 < g 0 ∨ f 0 = g 0 ∧ toLex (Fin.tail f) < toLex (Fin.tail g) := by
  constructor
  · rintro ⟨i, hb, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hb 0 (Fin.succ_pos i'),
        ⟨i', fun j hj ↦ hb j.succ (Fin.succ_lt_succ_iff.mpr hj), hi⟩⟩
  · rintro (hlt | ⟨h0, i', hb, hi⟩)
    · exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), hlt⟩
    · refine ⟨i'.succ, fun j hj ↦ ?_, hi⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact h0
      · exact hb j' (Fin.succ_lt_succ_iff.mp hj)

end Pi

namespace List

variable {α : Type*} [LinearOrder α]

/-- The lexicographic order on `Fin n`-tuples is the lexicographic order on their lists. -/
theorem ofFn_lex_lt_iff : ∀ {n : ℕ} (f g : Fin n → α),
    Lex (· < ·) (ofFn f) (ofFn g) ↔ toLex f < toLex g
  | 0, f, g => by
    rw [ofFn_zero, ofFn_zero]
    exact ⟨nofun, fun h ↦ by obtain ⟨i, -⟩ := h; exact i.elim0⟩
  | n + 1, f, g => by
    rw [ofFn_succ, ofFn_succ, cons_lex_cons_iff, ofFn_lex_lt_iff, Pi.toLex_lt_toLex_iff_succ]
    rfl

theorem ofFn_lt_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f < ofFn g ↔ toLex f < toLex g :=
  ofFn_lex_lt_iff f g

theorem ofFn_le_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f ≤ ofFn g ↔ toLex f ≤ toLex g := by
  rw [← not_lt, ← not_lt, ofFn_lt_ofFn_iff]

/-- The lexicographic order on lists compares heads, then tails. -/
theorem cons_le_cons_iff' {a b : α} {l₁ l₂ : List α} :
    a :: l₁ ≤ b :: l₂ ↔ a < b ∨ a = b ∧ l₁ ≤ l₂ := by
  rw [← not_lt, ← not_lt (a := l₂) (b := l₁),
    show b :: l₂ < a :: l₁ ↔ b < a ∨ b = a ∧ l₂ < l₁ from cons_lex_cons_iff]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.ne', h.not_gt]
  · simp
  · simp [h, h.ne', h.not_gt]

end List

namespace Pi.Lex

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- `<` on `Lex (Fin n → α)` is decided by comparing the tuples' lists. -/
instance decidableLT : DecidableLT (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff _ (List.ofFn_lex_lt_iff (ofLex a) (ofLex b))

instance decidableLE : DecidableLE (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff (¬ b < a) not_lt

end Pi.Lex

namespace Pi

variable {α : Type*} [LinearOrder α] {m : ℕ}

/-- A tuple is lexicographically at most another iff every coordinate where it strictly exceeds
the other is preceded by one where it is strictly below. -/
theorem lex_le_iff_forall (A B : Fin m → α) :
    toLex A ≤ toLex B ↔ ∀ p, B p < A p → ∃ p' < p, A p' < B p' := by
  rw [← not_lt]
  constructor
  · intro hnlt p hp
    by_contra hcon
    by_cases hS : (Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j)).Nonempty
    · set q := (Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j)).min' hS with hq
      have hmem := Finset.min'_mem _ hS
      rw [← hq] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      obtain ⟨hqp, hne⟩ := hmem
      have hbefore : ∀ j, j < q → B j = A j := by
        intro j hj
        by_contra hjne
        have hjmem : j ∈ Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨lt_trans hj hqp, hjne⟩
        have := Finset.min'_le _ _ hjmem
        rw [← hq] at this
        exact absurd hj (not_lt.mpr this)
      rcases lt_or_ge (B q) (A q) with hlt | hge
      · exact hnlt ⟨q, fun j hj ↦ hbefore j hj, hlt⟩
      · exact hcon ⟨q, hqp, lt_of_le_of_ne hge (fun h ↦ hne h.symm)⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      have hbefore : ∀ j, j < p → B j = A j := by
        intro j hj
        by_contra hjne
        have hjmem : j ∈ Finset.univ.filter (fun j : Fin m ↦ j < p ∧ B j ≠ A j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj, hjne⟩
        rw [hS] at hjmem; simp at hjmem
      exact hnlt ⟨p, fun j hj ↦ hbefore j hj, hp⟩
  · intro hY hlt
    obtain ⟨i, hpre, hi⟩ := hlt
    obtain ⟨p', hp'lt, hp'⟩ := hY i hi
    exact absurd (hpre p' hp'lt).symm (ne_of_lt hp')

/-- A tuple is lexicographically at most another iff it is strictly below at the first
coordinate where they differ, when one exists. -/
theorem lex_le_iff_find (A B : Fin m → α) [DecidablePred fun i ↦ B i ≠ A i] :
    toLex A ≤ toLex B ↔ ∀ he : ∃ i, B i ≠ A i, A (Fin.find _ he) < B (Fin.find _ he) := by
  rw [lex_le_iff_forall]
  constructor
  · intro h he
    by_contra hle
    obtain ⟨p', hlt, hp'⟩ := h _ ((not_lt.mp hle).lt_of_ne (Fin.find_spec he))
    exact Fin.find_min he hlt hp'.ne'
  · intro hlead p hp
    have he : ∃ i, B i ≠ A i := ⟨p, hp.ne⟩
    refine ⟨Fin.find _ he, ?_, hlead he⟩
    exact (Fin.find_le_of_pos he hp.ne).lt_of_ne fun h ↦
      absurd (h ▸ hlead he) hp.asymm

end Pi

namespace Pi

section Reindex

variable {ι κ β : Type*} [LinearOrder κ] [LinearOrder β] (e : κ ≃ ι) {v w : ι → β}

/-- Reading two vectors along an enumeration of their coordinates, the product order embeds in
the lexicographic order. -/
theorem toLex_comp_strictMono [WellFoundedLT κ] : StrictMono fun v : ι → β ↦ toLex (v ∘ e) :=
  fun v w h ↦ Pi.toLex_strictMono <| by
    obtain ⟨hle, i, hi⟩ := Pi.lt_def.1 h
    exact Pi.lt_def.2 ⟨fun k ↦ hle (e k), e.symm i, by simpa using hi⟩

/-- Transposing a covering pair `a ⋖ b` reverses the order of two positions only if they are
`a` and `b`. -/
private theorem eq_and_eq_of_swap_lt_swap [DecidableEq κ] {a b x y : κ} (hab : a ⋖ b)
    (hxy : x < y) (h : Equiv.swap a b y < Equiv.swap a b x) : x = a ∧ y = b := by
  have hlt : ∀ z, z ≠ a → z < b → z < a := fun z hza hzb ↦ (hab.le_of_lt hzb).lt_of_ne hza
  rcases eq_or_ne x a with rfl | hxa
  · rcases eq_or_ne y b with rfl | hyb
    · exact ⟨rfl, rfl⟩
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxy.ne' hyb] at h
      exact absurd (hlt y hxy.ne' h) hxy.not_gt
  · rcases eq_or_ne x b with rfl | hxb
    · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (hab.lt.trans hxy).ne' hxy.ne'] at h
      exact absurd (hab.lt.trans hxy) h.not_gt
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at h
      rcases eq_or_ne y a with rfl | hya
      · rw [Equiv.swap_apply_left] at h
        exact absurd (hxy.trans hab.lt) h.not_gt
      · rcases eq_or_ne y b with rfl | hyb
        · rw [Equiv.swap_apply_right] at h
          exact absurd (hlt x hxa hxy) h.not_gt
        · rw [Equiv.swap_apply_of_ne_of_ne hya hyb] at h
          exact absurd hxy h.not_gt

variable [WellFoundedLT κ]

/-- Read along an enumeration, one vector is lexicographically below another iff some coordinate
where it is below comes before every coordinate where it is above. -/
theorem toLex_comp_lt_iff_exists :
    toLex (v ∘ e) < toLex (w ∘ e) ↔ ∃ i, v i < w i ∧ ∀ j, w j < v j → e.symm i < e.symm j := by
  refine ⟨fun hlt ↦ ?_, fun ⟨i, hi, hd⟩ ↦ ?_⟩
  · obtain ⟨i, hi, hlt⟩ := (lex_comp_equiv e (· < ·) (· < ·) v w).1 hlt
    refine ⟨i, hlt, fun j hj ↦ ?_⟩
    rcases lt_trichotomy (e.symm i) (e.symm j) with h | h | h
    · exact h
    · exact absurd hj (e.symm.injective h ▸ hlt.asymm)
    · exact absurd (hi j h) hj.ne'
  · refine lt_of_le_of_ne (not_lt.1 fun hlt ↦ ?_) fun heq ↦ hi.ne ?_
    · obtain ⟨j, hj, hlt⟩ := (lex_comp_equiv e (· < ·) (· < ·) w v).1 hlt
      exact absurd (hj i (hd j hlt)) hi.ne'
    · simpa using congrArg (· (e.symm i)) heq

/-- Read along an enumeration, one vector is lexicographically at most another iff every
coordinate where it is above is preceded by one where it is below. -/
theorem toLex_comp_le_iff_forall_exists :
    toLex (v ∘ e) ≤ toLex (w ∘ e) ↔ ∀ j, w j < v j → ∃ i, v i < w i ∧ e.symm i < e.symm j := by
  rw [← not_lt, toLex_comp_lt_iff_exists]
  push Not
  refine forall₂_congr fun j hj ↦ exists_congr fun i ↦ and_congr_right fun hi ↦
    ⟨fun h ↦ h.lt_of_ne fun heq ↦ ?_, le_of_lt⟩
  obtain rfl := e.symm.injective heq
  exact lt_asymm hi hj

/-- Read along an enumeration, one vector is lexicographically at most another iff a single
coordinate where it is below precedes every coordinate where it is above. -/
theorem toLex_comp_le_iff_exists_forall [Nonempty κ] :
    toLex (v ∘ e) ≤ toLex (w ∘ e) ↔ ∃ i, ∀ j, w j < v j → v i < w i ∧ e.symm i < e.symm j := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · rcases h.lt_or_eq with h | h
    · obtain ⟨i, hi, hd⟩ := (toLex_comp_lt_iff_exists e).1 h
      exact ⟨i, fun j hj ↦ ⟨hi, hd j hj⟩⟩
    · refine ⟨e (Classical.arbitrary κ), fun j hj ↦ absurd hj (not_lt.2 (le_of_eq ?_))⟩
      simpa using congrArg (· (e.symm j)) h
  · by_cases hv : ∃ j, w j < v j
    · obtain ⟨j, hj⟩ := hv
      exact ((toLex_comp_lt_iff_exists e).2 ⟨i, (hi j hj).1, fun k hk ↦ (hi k hk).2⟩).le
    · push Not at hv
      exact Pi.toLex_monotone fun k ↦ hv (e k)

/-- Two vectors ordered oppositely along two enumerations that differ by transposing a covering
pair `a ⋖ b` agree at every position before `a`, and are ordered as the first enumeration orders
them at `a` and as the second does at `b`. -/
theorem eq_and_lt_and_gt_of_toLex_comp_swap [DecidableEq κ] {a b : κ} (hab : a ⋖ b)
    (h : toLex (v ∘ e) < toLex (w ∘ e))
    (h' : toLex (w ∘ (Equiv.swap a b).trans e) < toLex (v ∘ (Equiv.swap a b).trans e)) :
    (∀ c < a, v (e c) = w (e c)) ∧ v (e a) < w (e a) ∧ w (e b) < v (e b) := by
  obtain ⟨i, hi, hd⟩ := (toLex_comp_lt_iff_exists e).1 h
  obtain ⟨i', hi', hd'⟩ := (toLex_comp_lt_iff_exists ((Equiv.swap a b).trans e)).1 h'
  simp only [Equiv.symm_trans_apply, Equiv.symm_swap] at hd'
  obtain ⟨hia, hib⟩ := eq_and_eq_of_swap_lt_swap hab (hd i' hi') (hd' i hi)
  rw [Equiv.symm_apply_eq] at hia hib
  subst hia hib
  refine ⟨fun c hc ↦ ?_, hi, hi'⟩
  rcases lt_trichotomy (v (e c)) (w (e c)) with hvw | hvw | hvw
  · have := hd' (e c) hvw
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hc.ne (hc.trans hab.lt).ne] at this
    exact absurd hc this.not_gt
  · exact hvw
  · exact absurd hc (by simpa using (hd (e c) hvw).not_gt)

end Reindex

section Enumerations

variable {ι β : Type*} [Fintype ι] [LinearOrder β] {n : ℕ} {v w : ι → β}

/-- Any coordinate can be enumerated first. -/
private theorem exists_equiv_fin_symm_lt (i : ι) (hn : Fintype.card ι = n) :
    ∃ e : Fin n ≃ ι, ∀ j, j ≠ i → e.symm i < e.symm j := by
  classical
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  let r : Fin n ≃ ι := (Equiv.swap ⟨0, (e.symm i).pos⟩ (e.symm i)).trans e
  have hi : r.symm i = ⟨0, (e.symm i).pos⟩ := by simp [r]
  refine ⟨r, fun j hj ↦ ?_⟩
  rw [hi, Fin.lt_def]
  exact Nat.pos_of_ne_zero fun h0 ↦ hj <| r.symm.injective <|
    Fin.ext (h0.trans (congrArg Fin.val hi).symm)

/-- One vector is lexicographically below another under some enumeration of the coordinates iff
it is below it at some coordinate. -/
theorem exists_toLex_comp_lt_iff (hn : Fintype.card ι = n) :
    (∃ e : Fin n ≃ ι, toLex (v ∘ e) < toLex (w ∘ e)) ↔ ∃ i, v i < w i := by
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · obtain ⟨i, hi, -⟩ := (toLex_comp_lt_iff_exists e).1 he
    exact ⟨i, hi⟩
  · obtain ⟨e, he⟩ := exists_equiv_fin_symm_lt i hn
    exact ⟨e, (toLex_comp_lt_iff_exists e).2
      ⟨i, hi, fun j hj ↦ he j fun hji ↦ (hji ▸ hj).asymm hi⟩⟩

/-- The product order is the intersection of the lexicographic orders under all enumerations of
the coordinates. -/
theorem forall_toLex_comp_lt_iff (hn : Fintype.card ι = n) :
    (∀ e : Fin n ≃ ι, toLex (v ∘ e) < toLex (w ∘ e)) ↔ v < w := by
  refine ⟨fun h ↦ Pi.lt_def.2 ⟨fun i ↦ not_lt.1 fun hi ↦ ?_, ?_⟩,
    fun h e ↦ toLex_comp_strictMono e h⟩
  · obtain ⟨e, he⟩ := (exists_toLex_comp_lt_iff hn).2 ⟨i, hi⟩
    exact (h e).asymm he
  · exact (exists_toLex_comp_lt_iff hn).1 ⟨_, h (Fintype.equivFinOfCardEq hn).symm⟩

end Enumerations

end Pi
