module

public import Linglib.Semantics.Questions.Hamblin.Exhaustive
public import Linglib.Semantics.Questions.Inquisitive.Answerhood

/-!
# The alternatives of a question as a Hamblin set

The alternatives `alt Q` of an inquisitive question `Q : Question W` form a Hamblin set, so the
answerhood operators for Hamblin sets apply to them.

No alternative is included in another. It follows that an alternative is the strongest true answer
at a world exactly when it is the only alternative true there. See
`Question.isStrongestTrueAnswer_alt_iff`.

## References

* [ciardelli-groenendijk-roelofsen-2018]
* [dayal-1996]
* [dayal-2016]
-/

@[expose] public section

namespace Question

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### The strong answer as a complete answer -/

theorem completelyAnsweredBy_strongAnswer (Q : Question W) :
    CompletelyAnsweredBy Q (strongAnswer (alt Q) w) := by
  intro p hp
  by_cases hw : w ∈ p
  · exact Or.inl fun _ hv => (hv p hp).1 hw
  · exact Or.inr fun _ hv => (hv p hp).not.1 hw

theorem isStrongestTrueAnswer_alt_iff (Q : Question W) {p : Set W} :
    IsStrongestTrueAnswer (alt Q) w p ↔ trueAnswers (alt Q) w = {p} :=
  isStrongestTrueAnswer_iff_of_antichain _ w (alt_isAntichain Q)

/-! ### Polar and declarative questions -/

section Polar

variable {w} {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
include hne hnu

theorem trueAnswers_polar_of_pos (hwp : w ∈ p) :
    trueAnswers (alt (polar p)) w = {p} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hwq hwp).elim
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inl rfl), hwp⟩

theorem trueAnswers_polar_of_neg (hwp : w ∉ p) :
    trueAnswers (alt (polar p)) w = {pᶜ} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact (hwp hwq).elim
    · exact Set.mem_singleton _
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inr rfl), hwp⟩

theorem weakAnswer_polar_of_pos (hwp : w ∈ p) : weakAnswer (alt (polar p)) w = p := by
  rw [weakAnswer, trueAnswers_polar_of_pos hne hnu hwp, Set.sInter_singleton]

theorem weakAnswer_polar_of_neg (hwp : w ∉ p) : weakAnswer (alt (polar p)) w = pᶜ := by
  rw [weakAnswer, trueAnswers_polar_of_neg hne hnu hwp, Set.sInter_singleton]

theorem strongAnswer_polar_of_pos (hwp : w ∈ p) : strongAnswer (alt (polar p)) w = p := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.1.1 hwp,
    fun hv => ⟨iff_of_true hwp hv, iff_of_false (not_not.2 hwp) (not_not.2 hv)⟩⟩

theorem strongAnswer_polar_of_neg (hwp : w ∉ p) : strongAnswer (alt (polar p)) w = pᶜ := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.2.1 hwp, fun hv => ⟨iff_of_false hwp hv, iff_of_true hwp hv⟩⟩

theorem isStrongestTrueAnswer_polar_of_pos (hwp : w ∈ p) :
    IsStrongestTrueAnswer (alt (polar p)) w p := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_pos hne hnu hwp]
  exact isLeast_singleton p

theorem isStrongestTrueAnswer_polar_of_neg (hwp : w ∉ p) :
    IsStrongestTrueAnswer (alt (polar p)) w pᶜ := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_neg hne hnu hwp]
  exact isLeast_singleton pᶜ

theorem isExhaustivelyResolvable_polar_of_nontrivial (w : W) :
    IsExhaustivelyResolvable (alt (polar p)) w := by
  by_cases hwp : w ∈ p
  · exact ⟨p, isStrongestTrueAnswer_polar_of_pos hne hnu hwp⟩
  · exact ⟨pᶜ, isStrongestTrueAnswer_polar_of_neg hne hnu hwp⟩

end Polar

theorem weakAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    weakAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [weakAnswer, trueAnswers, alt_ofSet, hwp]

theorem strongAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    strongAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [strongAnswer, alt_ofSet, hwp]

end Question
