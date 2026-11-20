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
`x` is larger (`Pi.lex_iff_exists_forall`), and `y` is not below `x` iff every index where `x` is
larger comes `r`-after one where it is smaller (`Pi.not_lex_iff_forall_exists`).

For `e : κ ≃ ι`, a function `v : ι → β` read along `e` is `toLex (v ∘ e)`, and comparing two such
is `Pi.Lex` for the order of positions `InvImage (· < ·) e.symm` on `ι`
(`Pi.toLex_comp_lt_toLex_comp_iff`), so the statements above apply to it.

On tuples `Fin n → α` the lexicographic order compares heads and then tails
(`Pi.toLex_lt_toLex_iff_succ`), so it is the order of the lists `List.ofFn`
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

theorem not_lex_iff_forall_exists [IsStrictTotalOrder ι r] [wf : WellFounded r] :
    ¬ Pi.Lex r (· < ·) y x ↔ ∀ j, y j < x j → ∃ i, x i < y i ∧ r i j := by
  rw [lex_iff_exists_forall]
  push Not
  refine forall₂_congr fun j hj ↦ exists_congr fun i ↦ and_congr_right fun hi ↦
    ⟨fun h ↦ by_contra fun h' ↦ ?_, fun h ↦ asymm h⟩
  obtain rfl := Std.Trichotomous.trichotomous j i h h'
  exact lt_asymm hi hj

theorem toLex_le_toLex_iff_forall [LinearOrder ι] [WellFoundedLT ι] :
    toLex x ≤ toLex y ↔ ∀ j, y j < x j → ∃ i < j, x i < y i :=
  (not_lt.symm.trans not_lex_iff_forall_exists).trans <|
    forall₂_congr fun _ _ ↦ exists_congr fun _ ↦ and_comm

end Rel

/-- Read along `e`, the lexicographic order compares positions: it is `Pi.Lex` for the order of
the indices pulled back along `e.symm`. -/
theorem toLex_comp_lt_toLex_comp_iff {ι κ β : Type*} [LT κ] [LT β] (e : κ ≃ ι) {v w : ι → β} :
    toLex (v ∘ e) < toLex (w ∘ e) ↔ Pi.Lex (InvImage (· < ·) e.symm) (· < ·) v w := by
  constructor
  · rintro ⟨k, hk, hs⟩
    exact ⟨e k, fun j hj ↦ by simpa using hk (e.symm j) (by simpa [InvImage] using hj), hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨e.symm i, fun k hk ↦ by simpa using hi (e k) (by simpa [InvImage] using hk),
      by simpa using hs⟩

theorem toLex_lt_toLex_iff_succ {α : Type*} [LT α] {n : ℕ} (f g : Fin (n + 1) → α) :
    toLex f < toLex g ↔ f 0 < g 0 ∨ f 0 = g 0 ∧ toLex (Fin.tail f) < toLex (Fin.tail g) := by
  have h := Fin.pi_lex_lt_cons_cons (x₀ := f 0) (y₀ := g 0) (x := Fin.tail f) (y := Fin.tail g)
    (fun {_} ↦ (· < ·))
  rwa [Fin.cons_self_tail, Fin.cons_self_tail] at h

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

theorem ofFn_le_ofFn_iff {n : ℕ} (f g : Fin n → α) : ofFn f ≤ ofFn g ↔ toLex f ≤ toLex g :=
  not_lt.symm.trans <| (ofFn_lex_lt_iff g f).not.trans not_lt

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

variable {α : Type*} {n : ℕ}

/-- `<` on `Lex (Fin n → α)` is decided by comparing the tuples' lists. -/
instance decidableLT [LT α] [DecidableEq α] [DecidableLT α] : DecidableLT (Lex (Fin n → α)) :=
  fun a b ↦ decidable_of_iff _ (List.ofFn_lex_lt_iff (ofLex a) (ofLex b))

instance decidableLE [LinearOrder α] : DecidableLE (Lex (Fin n → α)) := fun a b ↦
  decidable_of_iff (¬ b < a) not_lt

end Pi.Lex
