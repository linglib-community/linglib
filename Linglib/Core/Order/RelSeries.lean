module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.RelSeries

/-!
# Concatenation of relation series

Two relation series `p` and `q` such that `p` ends where `q` starts concatenate to the series
`RelSeries.smash p q h`, which runs through `p` and then through `q`. This file describes the
values of a concatenation and counts the steps of a series.

A *step* of a series `p` is a pair of consecutive values `p i` and `p (i + 1)`. For a set `R`, an
*entry* is a step from outside `R` into `R`, and an *exit* is a step from inside `R` out of it.
We prove that the number of steps of a given kind adds under concatenation.

## Main definitions

* `RelSeries.stepCount`: the number of steps of a series that satisfy a relation.
* `RelSeries.entries`, `RelSeries.exits`: the number of entries into a set and of exits from it.

## Main results

* `RelSeries.smash_apply_of_le`, `RelSeries.smash_apply_of_ge`: the values of a concatenation
  before and after the junction.
* `RelSeries.forall_smash_apply`: a property holds at every value of a concatenation if and only
  if it holds at every value of both series.
* `RelSeries.stepCount_smash`: the step count of a concatenation is the sum of the step counts.
* `RelSeries.entries_add_head`: the number of entries, plus one if the series starts in the set,
  equals the number of exits, plus one if it ends in the set.
-/

@[expose] public section

namespace RelSeries

open scoped SetRel

variable {α β : Type*} {r : SetRel α α} {p q : RelSeries r} (h : p.last = q.head)

@[simp] theorem apply_bot (p : RelSeries r) : p ⊥ = p.head := rfl

@[simp] theorem apply_top (p : RelSeries r) : p ⊤ = p.last := rfl

/-- The positions of a concatenation up to the junction are those of its first series. -/
theorem smash_apply_of_le (k : Fin (p.length + q.length + 1)) (hk : (k : ℕ) ≤ p.length) :
    p.smash q h k = p ⟨k, by omega⟩ :=
  smash_castLE h ⟨k, by omega⟩

/-- The positions of a concatenation from the junction on are those of its second series. -/
theorem smash_apply_of_ge (k : Fin (p.length + q.length + 1)) (hk : p.length ≤ (k : ℕ)) :
    p.smash q h k = q ⟨k - p.length, by have := k.2; omega⟩ := by
  have hk' : k = Fin.natAdd p.length
      (⟨k - p.length, by have := k.2; omega⟩ : Fin (q.length + 1)) := by
    ext; simp; omega
  conv_lhs => rw [hk']
  simp only [smash]
  exact Fin.addCases_right _

theorem mem_smash_of_mem_left {x : α} (hx : x ∈ p) : x ∈ p.smash q h := by
  obtain ⟨i, rfl⟩ := hx
  exact ⟨_, smash_castLE h i⟩

variable [Preorder β] {d : α → β}

theorem forall_smash_apply {P : α → Prop} :
    (∀ k, P (p.smash q h k)) ↔ (∀ i, P (p i)) ∧ ∀ j, P (q j) := by
  have hl : (p.smash q h).length = p.length + q.length := rfl
  refine ⟨fun hr ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩, fun ⟨hp, hq⟩ k ↦ ?_⟩
  · simpa [smash_apply_of_le h ⟨i, by omega⟩ (by have := i.2; simp; omega)] using hr ⟨i, by omega⟩
  · simpa [smash_apply_of_ge h ⟨p.length + j, by omega⟩ (by simp)] using
      hr ⟨p.length + j, by omega⟩
  · rcases le_total (k : ℕ) p.length with hk | hk
    · rw [smash_apply_of_le h k hk]; exact hp _
    · rw [smash_apply_of_ge h k hk]; exact hq _

theorem strictMono_comp_smash (hp : StrictMono (d ∘ p)) (hq : StrictMono (d ∘ q)) :
    StrictMono (d ∘ p.smash q h) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  simp only [Function.comp_apply]
  rcases lt_or_ge (i : ℕ) p.length with hi | hi
  · rw [smash_apply_of_le h _ (by simpa using hi.le), smash_apply_of_le h _ (by simp; omega)]
    exact hp (by simp [Fin.lt_def])
  · rw [smash_apply_of_ge h _ (by simpa using hi), smash_apply_of_ge h _ (by simp; omega)]
    exact hq (by simp [Fin.lt_def]; omega)

theorem strictAnti_comp_smash (hp : StrictAnti (d ∘ p)) (hq : StrictAnti (d ∘ q)) :
    StrictAnti (d ∘ p.smash q h) :=
  strictMono_comp_smash h (d := OrderDual.toDual ∘ d) hp hq

/-! ### Counting steps -/

section StepCount

variable {P : α → α → Prop}

open Classical in
/-- The number of steps of a series that satisfy `P`. -/
noncomputable def stepCount (P : α → α → Prop) (p : RelSeries r) : ℕ :=
  ∑ i : Fin p.length, if P (p i.castSucc) (p i.succ) then 1 else 0

/-- The steps of a concatenation are those of its two series. -/
theorem stepCount_smash (P : α → α → Prop) :
    stepCount P (p.smash q h) = stepCount P p + stepCount P q := by
  classical
  show ∑ i : Fin (p.length + q.length), _ = _
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
  · exact if_congr (iff_of_eq (congrArg₂ P (smash_castAdd h i) (smash_succ_castAdd h i))) rfl rfl
  · exact if_congr (iff_of_eq (congrArg₂ P (smash_natAdd h i) (smash_succ_natAdd h i))) rfl rfl

theorem stepCount_eq_zero_iff {p : RelSeries r} :
    stepCount P p = 0 ↔ ∀ i : Fin p.length, ¬ P (p i.castSucc) (p i.succ) := by
  classical
  simp [stepCount]

theorem stepCount_le_one {p : RelSeries r}
    (hP : ∀ i j : Fin p.length, P (p i.castSucc) (p i.succ) → P (p j.castSucc) (p j.succ) →
      i = j) : stepCount P p ≤ 1 := by
  classical
  rw [stepCount, Finset.sum_boole, Nat.cast_id]
  exact Finset.card_le_one.2 fun i hi j hj ↦
    hP i j (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2

open Classical in
private theorem entries_add_exits {n : ℕ} (g : Fin (n + 1) → Prop) :
    (∑ i : Fin n, if ¬ g i.castSucc ∧ g i.succ then 1 else 0) + (if g 0 then 1 else 0) =
      (∑ i : Fin n, if g i.castSucc ∧ ¬ g i.succ then 1 else 0) +
        if g (Fin.last n) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := ih (g ∘ Fin.castSucc)
    simp only [Function.comp_apply, Fin.castSucc_zero, ← Fin.succ_castSucc] at this
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (n := n)]
    simp only [Fin.succ_last]
    simp only [Nat.succ_eq_add_one] at this ⊢
    by_cases hm : g (Fin.last n).castSucc <;> by_cases hl : g (Fin.last (n + 1)) <;>
      by_cases h0 : g 0 <;> simp only [hm, hl, h0, not_true_eq_false, not_false_eq_true,
        and_self, and_true, and_false, ite_true, ite_false] at this ⊢ <;>
      omega

/-- The number of steps of a series from outside `R` into it. -/
noncomputable def entries (R : Set α) (p : RelSeries r) : ℕ :=
  stepCount (fun a b ↦ a ∉ R ∧ b ∈ R) p

/-- The number of steps of a series from inside `R` out of it. -/
noncomputable def exits (R : Set α) (p : RelSeries r) : ℕ :=
  stepCount (fun a b ↦ a ∈ R ∧ b ∉ R) p

theorem entries_smash (R : Set α) : (p.smash q h).entries R = p.entries R + q.entries R :=
  stepCount_smash h _

theorem exits_smash (R : Set α) : (p.smash q h).exits R = p.exits R + q.exits R :=
  stepCount_smash h _

open Classical in
/-- The steps into a set, with the start of the series if it is inside, are as many as the
steps out of it, with the end of the series if it is inside. -/
theorem entries_add_head (R : Set α) (p : RelSeries r) :
    (p.entries R + if p.head ∈ R then 1 else 0) = p.exits R + if p.last ∈ R then 1 else 0 := by
  unfold entries exits stepCount
  convert entries_add_exits fun i ↦ p i ∈ R <;> rfl

end StepCount

end RelSeries
