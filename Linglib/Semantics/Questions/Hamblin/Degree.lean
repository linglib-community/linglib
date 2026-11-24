module

public import Linglib.Semantics.Questions.Hamblin.Exhaustification

/-!
# Degree questions

A degree question asks for the value of a measure `μ : W → α`, as *how many* and *how tall* do.
Its Hamblin set `degreeHamblin μ` has, for each degree `d`, the answer `μ ⁻¹' Ici d` that the
measure is at least `d`. These answers are nested, so at each world `w` the answer at the degree
`μ w` is the strongest true one, and exhaustifying it against the question gives the fibre
`μ ⁻¹' {μ w}`, the answer that the measure is exactly `μ w`.

The order a degree question induces on worlds is the order of its measure. In general a Hamblin
set with a strongest true answer at each world is a preorder on the worlds with a family of its
lower sets, as `premisePreorder_eq_of_isLowerSet` states; the degree questions are those
whose order comes from a measure.

## Main definitions

* `Question.degreeHamblin μ`: the Hamblin set of the degree question of `μ`.

## Main results

* `Question.karttunen_degreeHamblin`: the true answers at `w` are those at the degrees up to
  `μ w`.
* `Question.isStrongestTrueAnswer_degreeHamblin`: the answer at `μ w` is the strongest true answer
  at `w`.
* `Question.exh_degreeHamblin`: exhaustifying the answer at an attained degree gives the worlds
  where the measure is exactly that degree.
* `Question.premisePreorder_degreeHamblin`: the order a degree question induces on worlds is the order
  of the measure.

## References

* [beck-rullmann-1999]
* [dayal-1996]
* [fox-hackl-2006]
* [fox-2018]
-/

@[expose] public section

namespace Question

open Set Exhaustification

variable {W α : Type*}

section Preorder

variable [Preorder α] (μ : W → α)

/-- The Hamblin set of the degree question of a measure `μ`: for each degree `d`, the answer that
`μ` is at least `d`. -/
def degreeHamblin : Set (Set W) := range fun d ↦ μ ⁻¹' Ici d

variable {μ}

theorem preimage_Ici_mem_degreeHamblin (d : α) : μ ⁻¹' Ici d ∈ degreeHamblin μ :=
  mem_range_self d

theorem degreeHamblin_id : degreeHamblin (id : α → α) = range Ici := rfl

theorem karttunen_degreeHamblin (w : W) :
    karttunen (degreeHamblin μ) w = (fun d ↦ μ ⁻¹' Ici d) '' Iic (μ w) :=
  karttunen_range _ w

/-- At each world the answer at the degree the measure takes there is the strongest true one. -/
theorem isStrongestTrueAnswer_degreeHamblin (w : W) :
    IsStrongestTrueAnswer (degreeHamblin μ) w (μ ⁻¹' Ici (μ w)) := by
  refine ⟨⟨preimage_Ici_mem_degreeHamblin _, mem_preimage.2 self_mem_Ici⟩, ?_⟩
  rintro _ ⟨⟨d, rfl⟩, hw⟩
  exact preimage_mono (Ici_subset_Ici.2 hw)

theorem hasStrongestTrueAnswer_degreeHamblin (w : W) :
    HasStrongestTrueAnswer (degreeHamblin μ) w :=
  ⟨_, isStrongestTrueAnswer_degreeHamblin w⟩

/-- The order a degree question induces on worlds is the order of the measure, with the worlds of
greater measure below. -/
theorem premisePreorder_degreeHamblin :
    premisePreorder (degreeHamblin μ) = Preorder.lift (OrderDual.toDual ∘ μ) :=
  Preorder.ext fun v w ↦ by
    simp only [Preorder.ofCriteria_le_iff, degreeHamblin, forall_mem_range, mem_preimage, mem_Ici]
    exact ⟨fun h ↦ h (μ w) le_rfl, fun h d hd ↦ hd.trans h⟩

/-- Dayal's presupposition holds of a degree question at every world. -/
theorem presupposition_degreeHamblin : presupposition (degreeHamblin μ) = univ :=
  eq_univ_of_forall hasStrongestTrueAnswer_degreeHamblin

end Preorder

section PartialOrder

variable [PartialOrder α] {μ : W → α}

/-- Exhaustifying the answer at an attained degree gives the worlds where the measure is exactly
that degree. -/
theorem exh_degreeHamblin (v : W) :
    exh (degreeHamblin μ) (μ ⁻¹' Ici (μ v)) = μ ⁻¹' {μ v} := by
  ext w
  rw [mem_exh_iff_isStrongestTrueAnswer (preimage_Ici_mem_degreeHamblin _)]
  constructor
  · intro h
    have h1 : μ v ≤ μ w := h.1.2
    have h2 : μ w ≤ μ v :=
      h.2 ⟨preimage_Ici_mem_degreeHamblin (μ w), mem_preimage.2 self_mem_Ici⟩
        (mem_preimage.2 self_mem_Ici)
    exact le_antisymm h2 h1
  · intro h
    have h : μ w = μ v := h
    rw [← h]
    exact isStrongestTrueAnswer_degreeHamblin w

theorem exh_degreeHamblin_of_surjective (hμ : Function.Surjective μ) (d : α) :
    exh (degreeHamblin μ) (μ ⁻¹' Ici d) = μ ⁻¹' {d} := by
  obtain ⟨v, rfl⟩ := hμ d
  exact exh_degreeHamblin v

end PartialOrder

end Question
