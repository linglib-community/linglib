module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.RelSeries

/-!
# Positions of a concatenated series

`RelSeries.smash p q h` concatenates two series when `p` ends where `q` starts. This file gives
the value of the concatenation at a position on either side of the junction, and the properties
of the two series that the concatenation keeps.

## Main results

* `RelSeries.smash_apply_of_le`, `RelSeries.smash_apply_of_ge`: the values of a concatenation
  up to and from the junction.
* `RelSeries.forall_smash_apply`: a property holds along a concatenation if and only if it holds
  along both series.
* `RelSeries.strictMono_comp_smash`: a concatenation of two series increasing under a map is
  increasing under it.
* `RelSeries.not_ordConnected_preimage_smash`: the positions inside a set are not one stretch
  when both series meet the set and the junction does not.
-/

@[expose] public section

namespace RelSeries

open scoped SetRel

variable {α β : Type*} {r : SetRel α α} {p q : RelSeries r} (h : p.last = q.head)

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

/-- The positions of a concatenation inside `R` are not one stretch if both series meet `R` and
their junction is outside it. -/
theorem not_ordConnected_preimage_smash {R : Set α} (hlast : p.last ∉ R)
    {i : Fin (p.length + 1)} {j : Fin (q.length + 1)} (hi : p i ∈ R) (hj : q j ∈ R) :
    ¬ ((p.smash q h) ⁻¹' R).OrdConnected := fun hc ↦ by
  have hl : (p.smash q h).length = p.length + q.length := rfl
  have hn : p.length < p.length + q.length + 1 := by omega
  have ha := smash_apply_of_le h ⟨i, by omega⟩ (by have := i.2; simp; omega)
  have hb := smash_apply_of_le h ⟨p.length, hn⟩ le_rfl
  have hc' := smash_apply_of_ge h ⟨p.length + j, by omega⟩ (by simp)
  have hmem := hc.out (x := ⟨i, by omega⟩) (y := ⟨p.length + j, by omega⟩)
    (by simpa [ha] using hi) (by simpa [hc'] using hj)
    (a := ⟨p.length, hn⟩) ⟨by have := i.2; simp [Fin.le_def]; omega, by simp [Fin.le_def]⟩
  have htop : p ⟨p.length, by omega⟩ = p.last := rfl
  simp only [Set.mem_preimage, hb, htop] at hmem
  exact hlast hmem

end RelSeries
