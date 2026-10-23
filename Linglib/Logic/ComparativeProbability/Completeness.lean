module

public import Linglib.Logic.ComparativeProbability.Representability
public import Linglib.Logic.ComparativeProbability.CancellationFin4
public import Mathlib.Data.Fin.VecNotation

/-! # Representation and completeness theorems

Kraft, Pratt and Seidenberg show that every qualitative probability on fewer than five atoms is
represented by a probability measure, and give one on five atoms that is not; padding it with
null atoms gives one at every larger size. Following van der Hoek, every qualitative
probability on a finite carrier is still represented by a qualitatively additive measure, since
any normalized numerical representation of it is one (`QualAddMeasure.ofRepr`).

## Main statements

* `ComparativeProbability.representable_of_card_lt_five`: below five atoms every order is
  representable.
* `ComparativeProbability.kps_not_representable`: the five-atom counterexample is not
  representable, by Scott's theorem.
* `ComparativeProbability.exists_nonrepresentable_fin`,
  `exists_nonrepresentable_of_five_le_card`: from five atoms on, some order is not
  representable.
* `ComparativeProbability.exists_qualAddMeasure_repr`: every qualitative probability on a finite
  carrier is represented by a qualitatively additive measure.
* `ComparativeProbability.axiomA_iff_fa`: qualitative additivity is equivalent to invariance
  under adding a disjoint set to both sides.

## References

* [kraft-pratt-seidenberg-1959]
* [van-der-hoek-1996]
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-! ### The Kraft–Pratt–Seidenberg counterexample -/

/-- `finsetIdx s` encodes a subset of `Fin 5` as a bitmask. -/
def finsetIdx (s : Finset (Fin 5)) : ℕ :=
  s.sum (fun i ↦ 2 ^ i.val)

/-- `kpsRankNat` ranks the 32 subsets of `Fin 5`, indexed by bitmask, in the
    Kraft–Pratt–Seidenberg order. With atoms `p, q, r, s, t` numbered `0, …, 4`, the lower half
    is `∅ < q < r < s < qr < qs < p < pq < rs < t < qrs < rp < ps < tq < qrp < rt`, and the
    complements follow in reverse order. -/
def kpsRankNat (idx : ℕ) : ℕ :=
  match idx with
  |  0 =>  0 |  1 =>  6 |  2 =>  1 |  3 =>  7
  |  4 =>  2 |  5 => 11 |  6 =>  4 |  7 => 14
  |  8 =>  3 |  9 => 12 | 10 =>  5 | 11 => 16
  | 12 =>  8 | 13 => 18 | 14 => 10 | 15 => 22
  | 16 =>  9 | 17 => 21 | 18 => 13 | 19 => 23
  | 20 => 15 | 21 => 26 | 22 => 19 | 23 => 28
  | 24 => 17 | 25 => 27 | 26 => 20 | 27 => 29
  | 28 => 24 | 29 => 30 | 30 => 25 | 31 => 31
  |  _ =>  0

/-- `kpsRank s` is the rank of `s` in the Kraft–Pratt–Seidenberg order. -/
def kpsRank (s : Finset (Fin 5)) : ℕ :=
  kpsRankNat (finsetIdx s)

theorem kps_mono_finset :
    ∀ (a b : Finset (Fin 5)), a ⊆ b → kpsRank b ≥ kpsRank a := by
  decide

private theorem kps_additive_finset :
    ∀ (a b : Finset (Fin 5)),
      (kpsRank a ≥ kpsRank b) ↔ (kpsRank (a \ b) ≥ kpsRank (b \ a)) := by
  decide

section KPSSystem

attribute [local instance] Classical.propDecidable

/-- `kpsRankSet A` is the Kraft–Pratt–Seidenberg rank of a set. -/
noncomputable def kpsRankSet (A : Set (Fin 5)) : ℕ := kpsRank A.toFinset

/-- `kpsGe A B` compares two sets by their Kraft–Pratt–Seidenberg rank. -/
noncomputable def kpsGe (A B : Set (Fin 5)) : Prop := kpsRankSet B ≤ kpsRankSet A

/-- The Kraft–Pratt–Seidenberg order is a qualitative probability on the subsets of
    `Fin 5`. -/
instance : IsQualitativeProbability kpsGe where
  refl _ := le_rfl
  trans _ _ _ hab hbc := le_trans hbc hab
  total A B := le_total (kpsRankSet B) (kpsRankSet A)
  mono A B hAB := kps_mono_finset _ _ (Set.toFinset_subset_toFinset.mpr hAB)
  qadd A B := by
    unfold kpsGe kpsRankSet
    rw [Set.toFinset_sdiff, Set.toFinset_sdiff]
    exact kps_additive_finset _ _
  bot_not_ge_top := by
    simp only [kpsGe, kpsRankSet, Set.top_eq_univ, Set.bot_eq_empty, Set.toFinset_univ,
      Set.toFinset_empty]; decide

/-- `kpsFamily` collects the four comparisons of the Kraft–Pratt–Seidenberg order that cancel,
    `p ≻ qs`, `pqs ≻ rt`, `rs ≻ pq` and `qt ≻ ps`. -/
private def kpsFamily : Multiset (Fin 5 → SignType) :=
  {![1, -1, 0, -1, 0], ![1, 1, -1, 1, -1], ![-1, -1, 1, 1, 0], ![-1, 1, 0, -1, 1]}

private theorem posSupport_eq_coe_filter (v : Fin 5 → SignType) :
    posSupport v = ↑(Finset.univ.filter fun i ↦ v i = 1) := by ext; simp

private theorem negSupport_eq_coe_filter (v : Fin 5 → SignType) :
    negSupport v = ↑(Finset.univ.filter fun i ↦ v i = -1) := by ext; simp

/-- **The Kraft–Pratt–Seidenberg order is not representable.** Its four comparisons
    `kpsFamily` hold strictly and their sign vectors cancel, so Scott's theorem
    (`representable_iff_cancellation`) would force `qs ≿ p`. -/
theorem kps_not_representable : ¬Representable kpsGe := fun h ↦ by
  have key := (representable_iff_cancellation kpsGe).mp h kpsFamily (fun v hv ↦ ?_)
    (by decide) ![1, -1, 0, -1, 0] (by simp [kpsFamily])
  · revert key
    show ¬kpsRank (posSupport _).toFinset ≤ kpsRank (negSupport _).toFinset
    rw [posSupport_eq_coe_filter, negSupport_eq_coe_filter, Finset.toFinset_coe,
      Finset.toFinset_coe]
    decide
  · show kpsRank (negSupport v).toFinset ≤ kpsRank (posSupport v).toFinset
    rw [posSupport_eq_coe_filter, negSupport_eq_coe_filter, Finset.toFinset_coe,
      Finset.toFinset_coe]
    simp only [kpsFamily, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

end KPSSystem

/-! ### Padding with null atoms -/

theorem representable_of_pad {n : ℕ} {r : Set (Fin n) → Set (Fin n) → Prop} [Std.Refl r]
    (h : Representable (Set.preimage Fin.castSucc ⁻¹'o r)) : Representable r := by
  obtain ⟨μ, hμ, hm⟩ := h
  have hinj := Fin.castSucc_injective n
  have hlast : μ {Fin.last n} = 0 := by
    have hnull : Fin.castSucc ⁻¹' {Fin.last n} = (∅ : Set (Fin n)) :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (Fin.castSucc_lt_last i).ne hi
    simpa using (hm ∅ {Fin.last n}).mp (by
      show r (Fin.castSucc ⁻¹' ∅) (Fin.castSucc ⁻¹' {Fin.last n})
      rw [Set.preimage_empty, hnull]; exact refl_of r ∅)
  have hcomap (A : Set (Fin n)) : μ.comap Fin.castSucc A = μ (Fin.castSucc '' A) :=
    Measure.comap_apply _ hinj (fun _ _ ↦ .of_discrete) μ .of_discrete
  have hcover : Fin.castSucc '' (Set.univ : Set (Fin n)) ∪ {Fin.last n} = Set.univ := by
    rw [Set.image_univ]
    ext i
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  have hdisj : Disjoint (Fin.castSucc '' (Set.univ : Set (Fin n))) {Fin.last n} :=
    Set.disjoint_singleton_right.mpr fun ⟨i, _, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi
  have htotal : μ (Fin.castSucc '' (Set.univ : Set (Fin n))) = 1 := by
    have := measure_union hdisj (.of_discrete) (μ := μ)
    rwa [hcover, measure_univ, hlast, add_zero, eq_comm] at this
  refine ⟨μ.comap Fin.castSucc, ⟨by rw [hcomap]; exact htotal⟩, fun A B ↦ ?_⟩
  rw [hcomap, hcomap]
  have key := hm (Fin.castSucc '' A) (Fin.castSucc '' B)
  simp only [Order.Preimage, Set.preimage_image_eq _ hinj] at key
  exact key

/-- For every `n ≥ 5` some qualitative probability on `Fin n` is not representable, as the
    Kraft–Pratt–Seidenberg counterexample padded with null atoms shows. -/
theorem exists_nonrepresentable_fin {n : ℕ} (h : 5 ≤ n) :
    ∃ r : Set (Fin n) → Set (Fin n) → Prop, IsQualitativeProbability r ∧ ¬Representable r := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨kpsGe, inferInstance, kps_not_representable⟩
  | succ n _ ih =>
    obtain ⟨r, _, hr⟩ := ih
    exact ⟨Set.preimage Fin.castSucc ⁻¹'o r, inferInstance, fun h ↦ hr (representable_of_pad h)⟩

/-! ### The Kraft–Pratt–Seidenberg theorems -/

/-- **Kraft–Pratt–Seidenberg below five atoms.** Every qualitative probability on fewer than
    five atoms is representable by a probability measure. -/
theorem representable_of_card_lt_five {W : Type*} [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] (r : Set W → Set W → Prop) [IsQualitativeProbability r]
    (hcard : Fintype.card W < 5) : Representable r := by
  classical
  exact perm_repr (Fintype.equivFin W) r (representable_of_le_four (by omega) _)

/-- **Kraft–Pratt–Seidenberg from five atoms on.** Some qualitative probability is not
    representable by any probability measure. -/
theorem exists_nonrepresentable_of_five_le_card {W : Type*} [Fintype W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] (hcard : 5 ≤ Fintype.card W) :
    ∃ r : Set W → Set W → Prop, IsQualitativeProbability r ∧ ¬Representable r := by
  classical
  obtain ⟨r, _, hr⟩ := exists_nonrepresentable_fin hcard
  exact ⟨Set.preimage (Fintype.equivFin W).symm ⁻¹'o r, inferInstance,
    fun h ↦ hr (perm_repr (Fintype.equivFin W).symm r h)⟩

/-! ### Qualitatively additive representation -/

attribute [local instance] Classical.propDecidable

section Repr

variable {W : Type*} [Fintype W] (r : Set W → Set W → Prop) [IsQualitativeProbability r]

/-- `belowCount r A` counts the finsets at most as likely as `A`. -/
private noncomputable def belowCount (A : Set W) : ℕ :=
  (Finset.univ.filter (fun S : Finset W ↦ r A ↑S)).card

private theorem belowCount_univ : belowCount r Set.univ = Fintype.card (Finset W) := by
  unfold belowCount
  rw [Finset.filter_true_of_mem fun S _ ↦ mono _ _ (Set.subset_univ _)]
  exact Finset.card_univ

private theorem belowCount_mono {A B : Set W} (h : r B A) : belowCount r A ≤ belowCount r B := by
  refine Finset.card_le_card fun S hS ↦ ?_
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, trans_of r h hS.2⟩

private theorem belowCount_strict {A B : Set W} (h : ¬r B A) :
    belowCount r B < belowCount r A := by
  refine Finset.card_lt_card ⟨fun S hS ↦ ?_, fun hsub ↦ ?_⟩
  · rw [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, trans_of r ((total_of r B A).resolve_left h) hS.2⟩
  · have : A.toFinset ∈ Finset.univ.filter (fun S : Finset W ↦ r B ↑S) :=
      hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Set.coe_toFinset]; exact refl_of r A⟩)
    rw [Finset.mem_filter, Set.coe_toFinset] at this
    exact h this.2

private theorem belowCount_le_iff (A B : Set W) : belowCount r B ≤ belowCount r A ↔ r A B :=
  ⟨fun hcount ↦ by_contra fun hng ↦ by have := belowCount_strict r hng; omega,
    belowCount_mono r⟩

/-- **Qualitatively additive representation.** Every qualitative probability on a finite
    carrier is represented by a qualitatively additive measure: the count of dominated sets,
    affinely renormalised so that `μ(∅) = 0` and `μ(Ω) = 1`, is a normalized numerical
    representation (`QualAddMeasure.ofRepr`). -/
theorem exists_qualAddMeasure_repr :
    ∃ m : QualAddMeasure ℚ W, ∀ A B, r A B ↔ m.inducedGe A B := by
  classical
  set E : ℚ := (belowCount r ∅ : ℚ) with hE
  set N : ℚ := (Fintype.card (Finset W) : ℚ) with hN
  have hd : (0 : ℚ) < N - E := by
    have := belowCount_strict r (A := Set.univ) (B := ∅) not_rel_empty_univ
    rw [belowCount_univ] at this
    exact sub_pos.mpr (by rw [hN, hE]; exact_mod_cast this)
  -- the affine map t ↦ (t − E)/(N − E) is an order isomorphism
  let f : Set W → ℚ := fun A ↦ ((belowCount r A : ℚ) - E) / (N - E)
  have hf : ∀ A B, r A B ↔ f B ≤ f A := fun A B ↦ by
    rw [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right, Nat.cast_le]
    exact (belowCount_le_iff r A B).symm
  have h1 : f Set.univ = 1 := by
    simp only [f]; rw [belowCount_univ, ← hN]; exact div_self hd.ne'
  exact ⟨QualAddMeasure.ofRepr f hf (by simp only [f, ← hE, sub_self, zero_div]) h1,
    fun A B ↦ hf A B⟩

end Repr

/-! ### Qualitative and finite additivity -/

private theorem union_diff_union_disjoint {W : Type*} (A B C : Set W)
    (hAC : ∀ x, x ∈ A → x ∉ C) : (A ∪ C) \ (B ∪ C) = A \ B := by
  ext x; simp only [Set.mem_sdiff, Set.mem_union]
  refine ⟨fun h ↦ h.1.elim (fun hx ↦ ⟨hx, fun hb ↦ h.2 (Or.inl hb)⟩)
    (fun hx ↦ absurd (Or.inr hx) h.2), fun ⟨hxA, hxnB⟩ ↦
    ⟨Or.inl hxA, fun h ↦ h.elim hxnB (hAC x hxA)⟩⟩

/-- For any comparison on sets, qualitative additivity is equivalent to finite additivity in
    the form that adding a disjoint set to both sides preserves the comparison. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    (∀ A B : Set W, ge A B ↔ ge (A \ B) (B \ A)) ↔
    (∀ A B C : Set W, (∀ x, x ∈ A → x ∉ C) → (∀ x, x ∈ B → x ∉ C) →
      (ge A B ↔ ge (A ∪ C) (B ∪ C))) := by
  constructor
  · intro hA A B C hAC hBC
    have h2 := hA (A ∪ C) (B ∪ C)
    rw [union_diff_union_disjoint A B C hAC, union_diff_union_disjoint B A C hBC] at h2
    exact (hA A B).trans h2.symm
  · intro hFA A B
    have h := hFA (A \ B) (B \ A) (A ∩ B)
      (fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ ↦ hxnB hxB) (fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ ↦ hxnA hxA)
    rw [Set.sdiff_union_inter A B, Set.inter_comm A B, Set.sdiff_union_inter B A] at h
    exact h.symm

end ComparativeProbability
