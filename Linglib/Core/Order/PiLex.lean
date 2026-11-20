module

public import Mathlib.Order.PiLex
public import Mathlib.Order.Cover
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin

/-!
# The lexicographic order on functions, by a decisive coordinate

In the lexicographic order `Pi.Lex r (· < ·)` on functions `x y : ∀ i, β i`, mathlib defines `x`
to be below `y` when they agree at every index `r`-before some `i` with `x i < y i`. When `r` is a
well-founded strict total order and each `β i` is linearly ordered, the agreement clause can be
dropped: `x` is below `y` iff some index where `x` is smaller comes `r`-before every index where
`x` is larger (`Pi.lex_iff_exists_forall`). For a well-founded linear order on the indices this
gives `toLex x < toLex y ↔ ∃ i, x i < y i ∧ ∀ j, y j < x j → i < j`
(`Pi.toLex_lt_toLex_iff_exists`) and two forms of `≤`, one with the quantifiers in each order
(`Pi.toLex_le_toLex_iff_forall`, `Pi.toLex_le_toLex_iff_exists`).

For `e : κ ≃ ι`, a function `v : ι → β` read along `e` is `toLex (v ∘ e)`, and the same three
statements hold with the positions `e.symm i` compared in place of the indices
(`Pi.toLex_comp_lt_iff_exists`). Over all enumerations `e : Fin n ≃ ι` of a finite type, `v` is
below `w` along some `e` iff `v i < w i` for some `i` (`Pi.exists_toLex_comp_lt_iff`), and along
every `e` iff `v < w` in the product order (`Pi.forall_toLex_comp_lt_iff`). Two functions ordered
one way, and the other way once two adjacent indices are transposed, agree before those indices
and are ordered oppositely at them (`Pi.eq_and_lt_and_gt_of_toLex_comp_swap`).

On tuples `Fin n → α` the lexicographic order is the order of the lists `List.ofFn`
(`List.ofFn_lex_lt_iff`, `List.ofFn_le_ofFn_iff`).

## Implementation notes

Mathlib's `LinearOrder (Lex (∀ i, β i))` decides `<` and `≤` classically, since the indices are
only assumed well-founded. `Pi.Lex.decidableLT` and `Pi.Lex.decidableLE` decide them on
`Lex (Fin n → α)` by comparing lists, in time linear in `n`.

[UPSTREAM] candidates for `Mathlib/Order/PiLex.lean` and `Mathlib/Data/List/OfFn.lean`.
-/

@[expose] public section

namespace Pi

section Rel

variable {ι : Type*} {β : ι → Type*} {r : ι → ι → Prop} [∀ i, LinearOrder (β i)]
  {x y : ∀ i, β i}

/-- For a well-founded trichotomous relation on the indices, `x` is lexicographically below `y`
iff some index where `x` is smaller comes before every index where `x` is larger. -/
theorem lex_iff_exists_forall [Std.Trichotomous r] [wf : WellFounded r] :
    Pi.Lex r (· < ·) x y ↔ ∃ i, x i < y i ∧ ∀ j, y j < x j → r i j := by
  refine ⟨fun ⟨i, hi, hlt⟩ ↦ ⟨i, hlt, fun j hj ↦ by_contra fun hij ↦ ?_⟩, fun ⟨i, hi, hd⟩ ↦ ?_⟩
  · obtain rfl : i = j := Std.Trichotomous.trichotomous i j hij fun hji ↦ hj.ne' (hi j hji)
    exact lt_asymm hlt hj
  · have hne : {k | x k ≠ y k}.Nonempty := ⟨i, hi.ne⟩
    refine ⟨wf.min _ hne, fun k hk ↦ not_not.1 fun h ↦ wf.not_lt_min _ h hk, ?_⟩
    exact (wf.min_mem _ hne).lt_or_gt.resolve_right fun h ↦ wf.not_lt_min _ hi.ne (hd _ h)

variable [LinearOrder ι] [WellFoundedLT ι]

theorem toLex_lt_toLex_iff_exists :
    toLex x < toLex y ↔ ∃ i, x i < y i ∧ ∀ j, y j < x j → i < j :=
  lex_iff_exists_forall

theorem toLex_le_toLex_iff_forall :
    toLex x ≤ toLex y ↔ ∀ j, y j < x j → ∃ i < j, x i < y i := by
  rw [← not_lt, toLex_lt_toLex_iff_exists]
  push Not
  exact forall₂_congr fun j hj ↦ ⟨fun ⟨i, hi, hle⟩ ↦ ⟨i, hle.lt_of_ne fun h ↦ lt_asymm hi (h ▸ hj),
    hi⟩, fun ⟨i, hlt, hi⟩ ↦ ⟨i, hi, hlt.le⟩⟩

theorem toLex_le_toLex_iff_exists [Nonempty ι] :
    toLex x ≤ toLex y ↔ ∃ i, ∀ j, y j < x j → x i < y i ∧ i < j := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · rcases h.lt_or_eq with h | h
    · obtain ⟨i, hi, hd⟩ := toLex_lt_toLex_iff_exists.1 h
      exact ⟨i, fun j hj ↦ ⟨hi, hd j hj⟩⟩
    · exact ⟨Classical.arbitrary ι, fun j hj ↦ absurd (congrFun (toLex_inj.1 h) j) hj.ne'⟩
  · by_cases hv : ∃ j, y j < x j
    · obtain ⟨j, hj⟩ := hv
      exact (toLex_lt_toLex_iff_exists.2 ⟨i, (hi j hj).1, fun k hk ↦ (hi k hk).2⟩).le
    · push Not at hv
      exact toLex_monotone hv

end Rel

section Fin

variable {α : Type*} {n : ℕ}

theorem toLex_lt_toLex_iff_succ [LT α] (f g : Fin (n + 1) → α) :
    toLex f < toLex g ↔ f 0 < g 0 ∨ f 0 = g 0 ∧ toLex (Fin.tail f) < toLex (Fin.tail g) := by
  have h := Fin.pi_lex_lt_cons_cons (x₀ := f 0) (y₀ := g 0) (x := Fin.tail f) (y := Fin.tail g)
    (fun {_} ↦ (· < ·))
  rwa [Fin.cons_self_tail, Fin.cons_self_tail] at h

/-- A tuple is lexicographically at most another iff it is the smaller one at the first
coordinate where they differ. -/
theorem toLex_le_toLex_iff_find [LinearOrder α] (f g : Fin n → α)
    [DecidablePred fun i ↦ g i ≠ f i] :
    toLex f ≤ toLex g ↔ ∀ he : ∃ i, g i ≠ f i, f (Fin.find _ he) < g (Fin.find _ he) := by
  rw [toLex_le_toLex_iff_forall]
  refine ⟨fun h he ↦ by_contra fun hle ↦ ?_, fun hlead j hj ↦ ?_⟩
  · obtain ⟨i, hlt, hi⟩ := h _ ((not_lt.1 hle).lt_of_ne (Fin.find_spec he))
    exact Fin.find_min he hlt hi.ne'
  · have he : ∃ i, g i ≠ f i := ⟨j, hj.ne⟩
    exact ⟨Fin.find _ he, (Fin.find_le_of_pos he hj.ne).lt_of_ne fun h ↦
      absurd (h ▸ hlead he) hj.asymm, hlead he⟩

end Fin

end Pi

namespace List

variable {α : Type*}

theorem ofFn_lex_lt_iff [LT α] : ∀ {n : ℕ} (f g : Fin n → α),
    Lex (· < ·) (ofFn f) (ofFn g) ↔ toLex f < toLex g
  | 0, f, g => by
    rw [ofFn_zero, ofFn_zero]
    exact ⟨nofun, fun ⟨i, _⟩ ↦ i.elim0⟩
  | n + 1, f, g => by
    rw [ofFn_succ, ofFn_succ, cons_lex_cons_iff, ofFn_lex_lt_iff, Pi.toLex_lt_toLex_iff_succ]
    rfl

variable [LinearOrder α]

theorem ofFn_lt_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f < ofFn g ↔ toLex f < toLex g :=
  ofFn_lex_lt_iff f g

theorem ofFn_le_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f ≤ ofFn g ↔ toLex f ≤ toLex g := by
  rw [← not_lt, ← not_lt, ofFn_lt_ofFn_iff]

/-- The cons rule for mathlib's `≤` on lists, as `List.cons_le_cons_iff` is for core's. -/
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

variable {α : Type*} [LT α] [DecidableEq α] [DecidableLT α] {n : ℕ}

/-- `<` on `Lex (Fin n → α)` is decided by comparing the tuples' lists. -/
instance decidableLT : DecidableLT (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff _ (List.ofFn_lex_lt_iff (ofLex a) (ofLex b))

end Pi.Lex

namespace Pi.Lex

variable {α : Type*} [LinearOrder α] {n : ℕ}

instance decidableLE : DecidableLE (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff (¬ b < a) not_lt

end Pi.Lex

namespace Pi

section Reindex

variable {ι κ β : Type*} [LinearOrder κ] [LinearOrder β] (e : κ ≃ ι) {v w : ι → β}

theorem toLex_comp_strictMono [WellFoundedLT κ] : StrictMono fun v : ι → β ↦ toLex (v ∘ e) :=
  fun v w h ↦ Pi.toLex_strictMono <| by
    obtain ⟨hle, i, hi⟩ := Pi.lt_def.1 h
    exact Pi.lt_def.2 ⟨fun k ↦ hle (e k), e.symm i, by simpa using hi⟩

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

theorem toLex_comp_lt_iff_exists :
    toLex (v ∘ e) < toLex (w ∘ e) ↔ ∃ i, v i < w i ∧ ∀ j, w j < v j → e.symm i < e.symm j :=
  toLex_lt_toLex_iff_exists.trans <| e.exists_congr fun _ ↦ and_congr_right fun _ ↦
    e.forall_congr fun _ ↦ by simp

theorem toLex_comp_le_iff_forall_exists :
    toLex (v ∘ e) ≤ toLex (w ∘ e) ↔ ∀ j, w j < v j → ∃ i, v i < w i ∧ e.symm i < e.symm j :=
  toLex_le_toLex_iff_forall.trans <| e.forall_congr fun _ ↦ imp_congr_right fun _ ↦
    e.exists_congr fun _ ↦ by simp [and_comm]

theorem toLex_comp_le_iff_exists_forall [Nonempty κ] :
    toLex (v ∘ e) ≤ toLex (w ∘ e) ↔ ∃ i, ∀ j, w j < v j → v i < w i ∧ e.symm i < e.symm j :=
  toLex_le_toLex_iff_exists.trans <| e.exists_congr fun _ ↦ e.forall_congr fun _ ↦ by simp

/-- Two functions ordered one way, and the other way once the adjacent indices `a ⋖ b` are
transposed, agree before `a`, and the lower one is smaller at `a` and larger at `b`. -/
theorem eq_and_lt_and_gt_of_toLex_comp_swap [DecidableEq κ] {a b : κ} {x y : κ → β}
    (hab : a ⋖ b) (h : toLex x < toLex y)
    (h' : toLex (y ∘ Equiv.swap a b) < toLex (x ∘ Equiv.swap a b)) :
    (∀ c < a, x c = y c) ∧ x a < y a ∧ y b < x b := by
  obtain ⟨i, hi, hd⟩ := toLex_lt_toLex_iff_exists.1 h
  obtain ⟨i', hi', hd'⟩ := (toLex_comp_lt_iff_exists (Equiv.swap a b)).1 h'
  simp only [Equiv.symm_swap] at hd'
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_swap_lt_swap hab (hd i' hi') (hd' i hi)
  refine ⟨fun c hc ↦ ?_, hi, hi'⟩
  rcases lt_trichotomy (x c) (y c) with hxy | hxy | hxy
  · have := hd' c hxy
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hc.ne (hc.trans hab.lt).ne] at this
    exact absurd hc this.not_gt
  · exact hxy
  · exact absurd hc (hd c hxy).not_gt

end Reindex

section Enumerations

variable {ι β : Type*} [Fintype ι] [LinearOrder β] {n : ℕ} {v w : ι → β}

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

theorem exists_toLex_comp_lt_iff (hn : Fintype.card ι = n) :
    (∃ e : Fin n ≃ ι, toLex (v ∘ e) < toLex (w ∘ e)) ↔ ∃ i, v i < w i := by
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · obtain ⟨i, hi, -⟩ := (toLex_comp_lt_iff_exists e).1 he
    exact ⟨i, hi⟩
  · obtain ⟨e, he⟩ := exists_equiv_fin_symm_lt i hn
    exact ⟨e, (toLex_comp_lt_iff_exists e).2
      ⟨i, hi, fun j hj ↦ he j fun hji ↦ (hji ▸ hj).asymm hi⟩⟩

theorem forall_toLex_comp_lt_iff (hn : Fintype.card ι = n) :
    (∀ e : Fin n ≃ ι, toLex (v ∘ e) < toLex (w ∘ e)) ↔ v < w := by
  refine ⟨fun h ↦ Pi.lt_def.2 ⟨fun i ↦ not_lt.1 fun hi ↦ ?_, ?_⟩,
    fun h e ↦ toLex_comp_strictMono e h⟩
  · obtain ⟨e, he⟩ := (exists_toLex_comp_lt_iff hn).2 ⟨i, hi⟩
    exact (h e).asymm he
  · exact (exists_toLex_comp_lt_iff hn).1 ⟨_, h (Fintype.equivFinOfCardEq hn).symm⟩

end Enumerations

end Pi
