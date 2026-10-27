module

public import Linglib.Semantics.Degree.Background
public import Linglib.Fragments.English.Adjectives

/-!
# Cariani, Santorio and Wellwood (2023): Positive gradable adjective ascriptions without positive morphemes

Cariani, Santorio and Wellwood give a gradable adjective a background ordering of states, the
states of having some heat for *hot*, and a context-dependent threshold property, the states that
count as hot. The positive form says that the subject holds a state with the threshold property;
the comparative bypasses the threshold, comparing an admissible measure of the subject's states
with the greatest degree of the standard's, Wellwood's comparative. The positive form therefore
needs no covert *pos*, and neither form entails the other. The framework, with its relations to
Klein's delineations and to degree thresholds, is `Semantics/Degree/Background.lean`; this file
checks the paper's claims against it. The paper argues from two cities of equal temperature that
the background is not linear, but its premises make the background total and refute only
antisymmetry, the two states sharing one degree.

* The examples check the inference (19) on a three-state model, the split verdict of the literal
  reading of §4, (24) against the English fragment, and the failure of the converse of (26).

## Implementation notes

The states of all holders form a type `S` with the background preorder, and `holder : S → X` is
a function, each state having one holder (fn. 9), but not injective, since the than-clause
maximum ranges over a holder's several states. The presupposition that a state lies in the
domain of the background is membership in `S`. The comparative's standard degree `d_b` is the
greatest measure of the standard's states. In (31) the comparative binds `g` but writes
`background(f)`.

## TODO

* The crispness contrast (8) and *for*-phrases (33), (34), for which the paper gives no semantics.

## References

* [cariani-santorio-wellwood-2023]
* [wellwood-2015]
* [klein-1980]
* [cresswell-1976]
-/

@[expose] public section

namespace CarianiSantorioWellwood2023

open Set Degree

variable {S X : Type*} [Preorder S] {holder : S → X}

/-! ### The inference (19) -/

/-- (19) on three heat states `0 < 1 < 2`, Barcelona holding `0` and `1` and Miami `2`, with *hot*
the states from `1` up and the identity as measure, *Barcelona is hot* and *Miami is hotter than
Barcelona*, and so, by upward monotonicity, *Miami is hot*. -/
example :
    let holder : Fin 3 → Bool := fun s ↦ decide (s = 2)
    false ∈ holder '' Ici 1 ∧ MaxComparative .gt (holder · = true) (holder · = false) id ∧
      true ∈ holder '' Ici 1 := by
  intro holder
  have hb : false ∈ holder '' Ici 1 := ⟨1, mem_Ici.2 le_rfl, by decide⟩
  have hc : MaxComparative .gt (holder · = true) (holder · = false) id := by
    refine ⟨1, ⟨⟨1, by decide, rfl⟩, ?_⟩, 2, by decide, by decide⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (by decide : ∀ s : Fin 3, decide (s = 2) = false → s ≤ 1) s hs
  exact ⟨hb, hc, mem_image_of_maxComparative (isUpperSet_Ici 1) strictMono_id hb hc⟩

/-! ### The equal-temperature cities (§4, fn. 10) -/

/-- In the cities of §4, states of distinct holders at equal measure are distinct but tied, and the
background is total. -/
theorem ne_and_antisymmRel_and_total {D : Type*} [LinearOrder D] {μ : S → D}
    (hμ : ∀ a b, μ a ≤ μ b → a ≤ b) {s t : S} (hne : holder s ≠ holder t) (heq : μ s = μ t) :
    s ≠ t ∧ AntisymmRel (· ≤ ·) s t ∧ ∀ u v : S, u ≤ v ∨ v ≤ u :=
  ⟨ne_of_apply_ne holder hne, ⟨hμ s t heq.le, hμ t s heq.ge⟩, total_of_reflect_le hμ⟩

/-- On the literal reading of §4 the two cities' states are unordered. Then a threshold can hold
of one and not of the other at the same temperature. On the componentwise order of `ℕ × ℕ` with
the sum as measure, `(1, 0)` and `(0, 1)` measure alike, and the states from `(1, 0)` up include
the one and not the other. -/
example :
    (1, 0).1 + (1, 0).2 = (0, 1).1 + (0, 1).2 ∧ ((1, 0) : ℕ × ℕ) ∈ Ici (1, 0) ∧
      ((0, 1) : ℕ × ℕ) ∉ Ici (1, 0) := by
  refine ⟨rfl, mem_Ici.2 le_rfl, ?_⟩
  simp [Prod.mk_le_mk]

/-! ### Scale-mates (24)–(26) -/

/-- In the English fragment, *hot* and *warm* measure one dimension (24). -/
example : English.Adjectives.hot.dimension = English.Adjectives.warm.dimension := rfl

/-- The converse of (26) fails. With *warm* the states from `1` up and *hot* the states from `2`
up on `Fin 3`, a city holding only the state `1` is warm and not hot. -/
example :
    let holder : Fin 3 → Bool := fun s ↦ decide (s = 1)
    true ∈ holder '' Ici 1 ∧ true ∉ holder '' Ici 2 := by
  intro holder
  refine ⟨⟨1, mem_Ici.2 le_rfl, by decide⟩, ?_⟩
  rintro ⟨s, hs, hs1⟩
  revert s
  decide

end CarianiSantorioWellwood2023
