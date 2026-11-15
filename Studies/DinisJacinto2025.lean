module

public import Linglib.Core.Order.SuccPred.LinearLocallyFinite
public import Linglib.Semantics.Degree.Marginality.Hyperreal
public import Studies.Itzhaki2021
public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Dinis and Jacinto (2025): A Theory of Marginal and Large Difference

Dinis and Jacinto's ML theory is [eleven axioms](##IsMLModel) on marginally and largely smaller than
along a strict weak order. It has [no model on the naturals or the
reals](##instIsEmptyMarginalScale), but the hyperreals are one, with [infinitesimal differences
marginal](##Hyperreal.infinitesimalScale). A countable model whose blocks have [finite
intervals](##finitelyMarginal_iff) [maps homomorphically](##exists_isHom_lex_rat_int) into
rational-indexed blocks of integer-indexed locations, [uniquely up to
rescaling](##IsHom.exists_cautiouslyMonotone) the blocks and the locations within them. In a
Sorites the bald are [the blocks from the last member's on](##bald_iff_toBlock_le), so [no finite
series of marginal steps](##not_transGen_marginallyLT) reaches them from the not bald.

## Implementation notes

* The project's ML scales are those of [dinis-jacinto-2026], over a linear order with marginally
  smaller than primitive, and the results after the axioms are stated for them; a homomorphism
  then preserves and reflects smaller than and marginally smaller than, and is injective.
* The nonstandard models are `Hyperreal.infinitesimalScale` and `Hyperreal.finiteScale` on
  mathlib's hyperreals. The finite-difference reading of Dean and Itzhaki (§5, §6), stated for
  nonstandard integers, is taken on the hyperreals.

## TODO

* The arithmetical model `ℑ1` of §3.2 and the model `ℜ` with an initial block of §4.3 need a
  nonstandard model of arithmetic, which mathlib lacks.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
* [dean-2018]
* [itzhaki-2021]
-/

@[expose] public section

namespace DinisJacinto2025

open MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α} {x y : α}

/-! ### The theory -/

/-- The eleven axioms of §2 on marginally and largely smaller than, `M` and `L`, along a strict
weak order `R`, both relations primitive. -/
structure IsMLModel {β : Type*} (R M L : β → β → Prop) : Prop where
  isStrictWeakOrder : IsStrictWeakOrder β R
  exists_l : ∃ x y, L x y
  r_of_m : ∀ ⦃x y⦄, M x y → R x y
  r_of_l : ∀ ⦃x y⦄, L x y → R x y
  m_trans : ∀ ⦃x y z⦄, M x y → M y z → M x z
  not_l_of_m : ∀ ⦃x y⦄, M x y → ¬ L x y
  irrelevance : ∀ ⦃x y⦄ z, M x y → (L z y → L z x) ∧ (L x z → L y z)
  l_of_r_of_l : ∀ ⦃x y z⦄, R x y → L y z → L x z
  l_of_l_of_r : ∀ ⦃x y z⦄, L x y → R y z → L x z
  m_or_l_of_r : ∀ ⦃x y⦄, R x y → M x y ∨ L x y
  decomposition : ∀ ⦃x y⦄, L x y → (∃ z, M x z ∧ L z y) ∧ ∃ w, M w y ∧ L x w
  m_bounded : ∀ ⦃x y z⦄, M x z → R x y → R y z → M x y ∧ M y z

theorem IsMLModel.l_iff {M L : α → α → Prop} (h : IsMLModel (· < ·) M L) :
    L x y ↔ x < y ∧ ¬ M x y := by
  grind [h.r_of_l, h.not_l_of_m, h.m_or_l_of_r]

/-- No conditionally complete linear order carries an ML scale (Theorem 2.12). The supremum of
the degrees above `x` and largely below `y` would lie in the block of `y`, and a degree marginally
below it would be a smaller upper bound. -/
instance instIsEmptyMarginalScale {α : Type*} [ConditionallyCompleteLinearOrder α] :
    IsEmpty (MarginalScale α) := by
  refine ⟨fun ml ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := ml.exists_largelyLT
  set S := {z | x < z ∧ ml.LargelyLT z y}
  obtain ⟨z₀, hxz₀, hz₀y⟩ := hxy.exists_marginallyLT_largelyLT
  have hS : S.Nonempty := ⟨z₀, hxz₀.lt, hz₀y⟩
  have hb : BddAbove S := ⟨y, fun z hz ↦ hz.2.lt.le⟩
  have hxl : x < sSup S := hxz₀.lt.trans_le (le_csSup hb ⟨hxz₀.lt, hz₀y⟩)
  have hly : ml.AtMostMarginal (sSup S) y := atMostMarginal_iff_incompRel.2
    ⟨fun h ↦ by
      obtain ⟨w, hlw, hwy⟩ := h.exists_marginallyLT_largelyLT
      exact (le_csSup hb ⟨hxl.trans hlw.lt, hwy⟩).not_gt hlw.lt,
    fun h ↦ (csSup_le hS fun z hz ↦ hz.2.lt.le).not_gt h.lt⟩
  obtain ⟨w, -, hwl⟩ := (hly.largelyLT_congr_right.2 hxy).exists_largelyLT_marginallyLT
  exact (csSup_le hS fun a ha ↦ (hwl.atMostMarginal.largelyLT_congr_right.2
    (hly.largelyLT_congr_right.2 ha.2)).lt.le).not_gt hwl.lt

-- p. 521
theorem infinite_of_marginalScale (ml : MarginalScale α) : Infinite α :=
  let ⟨_, _, h⟩ := ml.exists_largelyLT
  Set.infinite_univ_iff.1 ((LargelyLT.infinite_Ioo h).mono (Set.subset_univ _))

example : IsEmpty (MarginalScale ℕ) := inferInstance

example : IsEmpty (MarginalScale ℝ) := inferInstance

/-! ### Nonstandard models -/

open ArchimedeanClass Hyperreal

-- Theorem 3.1: the model `ℑ2` is `Hyperreal.infinitesimalScale`.
example : infinitesimalScale.MarginallyLT 0 ε ∧ infinitesimalScale.LargelyLT 0 1 :=
  ⟨infinitesimalScale_marginallyLT_iff.2 ⟨epsilon_pos, by simp [archimedeanClassMk_epsilon_pos]⟩,
    zero_lt_one, fun h ↦ by simpa using (infinitesimalScale_marginallyLT_iff.1 h).2⟩

-- §5, §6: on the reading of Dean and of Itzhaki the scale is `Hyperreal.finiteScale`.
example : finiteScale.MarginallyLT 0 1 ∧ finiteScale.LargelyLT 0 ω :=
  ⟨finiteScale_marginallyLT_iff.2 ⟨zero_lt_one, by simp⟩, omega_pos,
    fun h ↦ (finiteScale_marginallyLT_iff.1 h).2.not_gt (by simp [archimedeanClassMk_omega_neg])⟩

/-! ### Representation -/

-- Definition 4.3: the blocks of the representative model are its rational coordinates.
example : (lex ℚ ℤ).toBlock (toLex (0, 5)) = (lex ℚ ℤ).toBlock (toLex (0, -3)) ∧
    (lex ℚ ℤ).toBlock (toLex (0, 5)) < (lex ℚ ℤ).toBlock (toLex (1, 0)) := by
  simp

variable (ml) in
/-- Definition 4.4: `y` is a weakly marginal successor of `x` when `x` is marginally smaller than
`y` and no degree marginally above `x` is marginally below `y`. -/
def MarginalSucc (x y : α) : Prop :=
  ml.MarginallyLT x y ∧ ∀ z, ml.MarginallyLT x z → ¬ ml.MarginallyLT z y

-- A weakly marginal successor is a successor: no large difference is a covering.
theorem marginalSucc_iff_covBy : MarginalSucc ml x y ↔ x ⋖ y := by
  refine ⟨fun h ↦ ⟨h.1.lt, fun z hxz hzy ↦ h.2 z (h.1.bounded hxz hzy).1 (h.1.bounded hxz hzy).2⟩,
    fun h ↦ ⟨(marginallyLT_or_largelyLT_of_lt h.lt).resolve_right fun hl ↦ ?_,
      fun z hxz hzy ↦ h.2 hxz.lt hzy.lt⟩⟩
  obtain ⟨z, hxz, hzy⟩ := hl.exists_marginallyLT_largelyLT
  exact h.2 hxz.lt hzy.lt

variable (ml) in
/-- Definition 4.5: an ML scale is finitely marginal when finitely many weakly marginal successions
lead from any degree to any marginally greater one. -/
def FinitelyMarginal : Prop :=
  ∀ ⦃x y⦄, ml.MarginallyLT x y → Relation.TransGen (MarginalSucc ml) x y

theorem finitelyMarginal_iff :
    FinitelyMarginal ml ↔ ∀ ⦃x y⦄, ml.AtMostMarginal x y → (Set.Icc x y).Finite := by
  have hs : MarginalSucc ml = (· ⋖ ·) := funext₂ fun _ _ ↦ propext marginalSucc_iff_covBy
  rw [FinitelyMarginal, hs]
  refine ⟨fun hf x y h ↦ ?_, fun hf x y h ↦ (hf h.atMostMarginal).transGen_covBy h.lt⟩
  rcases atMostMarginal_iff.1 h with rfl | h | h
  · simp
  · exact (hf h).finite_Icc
  · simp [h.lt]

/-- The degrees of a block of a finitely marginal scale are a locally finite order. -/
@[instance_reducible]
noncomputable def FinitelyMarginal.locallyFiniteOrder (hf : FinitelyMarginal ml) (q : ml.Block) :
    LocallyFiniteOrder {x // ml.toBlock x = q} :=
  .ofFiniteIcc fun a b ↦ (finitelyMarginal_iff.1 hf
    (toBlock_eq_toBlock.1 (a.2.trans b.2.symm))).preimage Subtype.val_injective.injOn

/-- Theorem 4.7: every countable, finitely marginal ML scale maps homomorphically into the
representative model. Its blocks, a countable linear order, embed in the rationals, and the
degrees of each block, a locally finite linear order, embed in the integers. -/
theorem exists_isHom_lex_rat_int [Countable α] (hf : FinitelyMarginal ml) :
    ∃ f : α → ℚ ×ₗ ℤ, ml.IsHom (lex ℚ ℤ) f := by
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense ml.Block ℚ
  have g (q : ml.Block) : Nonempty ({x // ml.toBlock x = q} ↪o ℤ) :=
    let := hf.locallyFiniteOrder q
    nonempty_orderEmbedding_int _
  exact ⟨_, isHom_toLex e fun q ↦ (g q).some⟩

-- §4.4
theorem exists_isHom_lex_rat_rat [Countable α] : ∃ f : α → ℚ ×ₗ ℚ, ml.IsHom (lex ℚ ℚ) f := by
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense ml.Block ℚ
  exact ⟨_, isHom_toLex e fun q ↦
    (Order.embedding_from_countable_to_dense {x // ml.toBlock x = q} ℚ).some⟩

/-! ### Uniqueness -/

section Uniqueness

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- Definition 4.8: a transformation of a set of pairs is cautiously monotone-increasing when it
maps blocks by one strictly increasing map and the locations within each block by strictly
increasing maps. -/
def CautiouslyMonotone (X : Set (β ×ₗ γ)) (τ : β ×ₗ γ → β ×ₗ γ) : Prop :=
  ∃ (f : β → β) (g : β → γ → γ), StrictMonoOn f ((fun p ↦ (ofLex p).1) '' X) ∧
    (∀ a, StrictMonoOn (g a) {b | toLex (a, b) ∈ X}) ∧
    ∀ p ∈ X, τ p = toLex (f (ofLex p).1, g (ofLex p).1 (ofLex p).2)

variable [Nontrivial β] [Nonempty γ] [NoMaxOrder γ] [NoMinOrder γ]

-- Theorem 4.9 (i)
theorem IsHom.comp_cautiouslyMonotone {h : α → β ×ₗ γ} (hh : ml.IsHom (lex β γ) h)
    {τ : β ×ₗ γ → β ×ₗ γ} (hτ : CautiouslyMonotone (Set.range h) τ) :
    ml.IsHom (lex β γ) (τ ∘ h) := by
  obtain ⟨f, g, hf, hg, hτ⟩ := hτ
  obtain ⟨hL, hM⟩ := isHom_lex_iff.1 hh
  refine isHom_lex_iff.2 ⟨fun x y ↦ ?_, fun x y hxy ↦ ?_⟩
  · simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, hL]
    exact (hf.lt_iff_lt ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, rfl⟩).symm
  · have he : (ofLex (h x)).1 = (ofLex (h y)).1 := hh.fst_eq_fst_iff.2 hxy.atMostMarginal
    simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, he]
    exact hg _ (by simp [← he]) ⟨y, rfl⟩ (hM hxy)

/-- Theorem 4.9 (ii): any two homomorphisms into lexicographic pairs differ by a cautiously
monotone-increasing transformation. -/
theorem IsHom.exists_cautiouslyMonotone {h u : α → β ×ₗ γ} (hh : ml.IsHom (lex β γ) h)
    (hu : ml.IsHom (lex β γ) u) : ∃ τ, CautiouslyMonotone (Set.range h) τ ∧ u = τ ∘ h := by
  obtain ⟨hhL, -⟩ := isHom_lex_iff.1 hh
  obtain ⟨huL, huM⟩ := isHom_lex_iff.1 hu
  let f := Function.extend (fun x ↦ (ofLex (h x)).1) (fun x ↦ (ofLex (u x)).1) id
  let g (a : β) (b : γ) : γ :=
    Function.extend (fun x ↦ ofLex (h x)) (fun x ↦ (ofLex (u x)).2) Prod.snd (a, b)
  have hf (x : α) : f (ofLex (h x)).1 = (ofLex (u x)).1 :=
    Function.FactorsThrough.extend_apply
      (fun _ _ he ↦ hu.fst_eq_fst_iff.2 (hh.fst_eq_fst_iff.1 he)) _ x
  have hg (x : α) : g (ofLex (h x)).1 (ofLex (h x)).2 = (ofLex (u x)).2 :=
    ((ofLex.injective.comp hh.strictMono.injective).factorsThrough _).extend_apply _ x
  refine ⟨fun p ↦ toLex (f (ofLex p).1, g (ofLex p).1 (ofLex p).2),
    ⟨f, g, ?_, fun a ↦ ?_, fun _ _ ↦ rfl⟩, funext fun x ↦ by rw [Function.comp_apply, hf, hg]; rfl⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩ hxy
    rw [hf, hf, ← huL, hhL]
    exact hxy
  · rintro b₁ ⟨x, hx⟩ b₂ ⟨y, hy⟩ hb
    have := huM ((hh.marginallyLT_iff x y).1
      (by rw [hx, hy]; exact lex_marginallyLT_iff.2 ⟨rfl, hb⟩))
    simp only [← hg, hx, hy, ofLex_toLex] at this ⊢
    exact this

end Uniqueness

/-! ### The Sorites -/

section Sorites

variable (ml) in
/-- In the Sorites of §5, to be bald is not to be largely less bald than the last member `e` of
the series. -/
def Bald (e x : α) : Prop := ¬ ml.LargelyLT x e

variable {e : α}

-- The bald are the degrees of the blocks from the last member's on.
theorem bald_iff_toBlock_le : Bald ml e x ↔ ml.toBlock e ≤ ml.toBlock x :=
  toBlock_le_toBlock.symm

theorem bald_of_le (h : e ≤ x) : Bald ml e x := bald_iff_toBlock_le.2 (ml.toBlock_mono h)

theorem bald_congr (h : ml.AtMostMarginal x y) : Bald ml e x ↔ Bald ml e y := by
  rw [bald_iff_toBlock_le, bald_iff_toBlock_le, toBlock_eq_toBlock.2 h]

-- Tolerance (i) and (ii), §5
theorem Bald.tolerance :
    (¬ Bald ml e x → ml.MarginallyLT x y → ¬ Bald ml e y) ∧
      (Bald ml e x → ml.MarginallyLT y x → Bald ml e y) :=
  ⟨fun hx h ↦ (bald_congr h.atMostMarginal).not.1 hx,
    fun hx h ↦ (bald_congr h.atMostMarginal).2 hx⟩

/-- No finite chain of marginal steps leads from someone not bald to the last member, so a
series in which each member is marginally balder than the one before satisfies the premises of
the Sorites only if it is infinite. -/
theorem not_transGen_marginallyLT (hx : ¬ Bald ml e x) :
    ¬ Relation.TransGen ml.MarginallyLT x e := fun h ↦ by
  rw [Relation.transGen_eq_self] at h
  exact h.not_largelyLT (not_not.1 hx)

example :
    ¬ Bald (lex ℚ ℤ) (toLex (1, 0)) (toLex (0, 0)) ∧ Bald (lex ℚ ℤ) (toLex (1, 0)) (toLex (1, 0)) :=
  ⟨not_not.2 (lex_largelyLT_iff.2 zero_lt_one), bald_of_le le_rfl⟩

end Sorites

/-! ### Itzhaki's nonstandard heuristics -/

theorem infinitesimalScale_atMostMarginal_iff_infinitesimallyClose {x y : ℝ*} :
    infinitesimalScale.AtMostMarginal x y ↔ Itzhaki2021.InfinitesimallyClose x y := by
  rw [infinitesimalScale_atMostMarginal_iff, Itzhaki2021.InfinitesimallyClose,
    Itzhaki2021.mem_infinitesimals, mk_sub_comm]

/-- Under Itzhaki's qualitative size, being a heap is the baldness of §5 on the finite scale (§6).
-/
theorem heap_iff_bald {De : Type*} {heap known : De → Prop} [DecidablePred heap]
    [DecidablePred known] {size : De → ℕ} {H : ℝ*} (hH : mk H < 0) (hpos : 0 < H) {e x : De}
    (he : heap e) : heap x ↔ Bald finiteScale (Itzhaki2021.qualSize heap known size H e)
      (Itzhaki2021.qualSize heap known size H x) := by
  rw [Bald, ← Itzhaki2021.infinitelyLess_iff_largelyLT]
  refine ⟨fun hx h ↦ h.2 (Itzhaki2021.finitelyClose_qualSize hx he),
    fun h ↦ by_contra fun hx ↦ h ?_⟩
  rw [Itzhaki2021.qualSize_of_not_heap hx]
  refine ⟨Itzhaki2021.natCast_lt_qualSize hH hpos he _, fun hf ↦ ?_⟩
  have hq := Itzhaki2021.finites.sub_mem
    (Itzhaki2021.mem_finites.2 (mk_natCast_nonneg (size x))) hf
  rw [sub_sub_cancel, Itzhaki2021.mem_finites] at hq
  exact hq.not_gt (Itzhaki2021.mk_qualSize_neg hH he)

end DinisJacinto2025
