module

public import Linglib.Core.Order.CountableDenseLinearOrder
public import Linglib.Core.Order.SuccPred.LinearLocallyFinite
public import Linglib.Semantics.Degree.Marginality
public import Studies.Itzhaki2021
public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Dinis and Jacinto (2025): A Theory of Marginal and Large Difference

Dinis and Jacinto propose ML theory, eleven axioms on marginally and largely smaller than along a
strict weak order, and give it a measurement theory. Every model is infinite, since a large
difference decomposes into a marginal step and a further large difference, and the theory has no
model on the naturals or the reals, but it has models in nonstandard analysis, where a marginal
difference is an infinitesimal one. Every countable, finitely marginal model maps homomorphically
into the representative model of rational-indexed blocks of integer-indexed locations, and any
two such maps differ by a transformation that rescales blocks and locations within blocks. In a
Sorites whose series is infinite, being bald as not being largely less bald than the last member
makes the premises jointly satisfiable.

## Main statements

* `instIsEmptyMarginalScale`: no conditionally complete order, such as the naturals or the
  reals, carries an ML scale.
* `exists_isHom_lex_rat_int`: every countable, finitely marginal ML scale maps homomorphically
  into the representative model `ℚ ×ₗ ℤ`.
* `heap_iff_bald`: Itzhaki's heaps are exactly what is not largely smaller than a clear case.
* `not_transGen_marginallyLT`: no finite chain of marginal steps leads from someone not bald to
  the last member of a Sorites series.

## Implementation notes

* The project's ML scales are those of [dinis-jacinto-2026], over a linear order with marginally
  smaller than primitive, and the results after the axioms are stated for them; a homomorphism
  then preserves and reflects smaller than and marginally smaller than, and is injective.
* The nonstandard models are mathlib's hyperreals, built from the infinitesimal and the finite
  numbers of [itzhaki-2021]. The finite-difference reading of Dean and Itzhaki (§5, §6), stated
  for nonstandard integers, is taken on the hyperreals.

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

open Degree MarginalScale

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
  obtain ⟨x, y, hxy⟩ := ml.exists_large
  set S := {z | x < z ∧ ml.LargelyLT z y}
  obtain ⟨z₀, hxz₀, hz₀y⟩ := (ml.decomposition hxy).1
  have hS : S.Nonempty := ⟨z₀, hxz₀.lt, hz₀y⟩
  have hb : BddAbove S := ⟨y, fun z hz ↦ hz.2.lt.le⟩
  have hxl : x < sSup S := hxz₀.lt.trans_le (le_csSup hb ⟨hxz₀.lt, hz₀y⟩)
  have hly : ml.AtMostMarginal (sSup S) y := atMostMarginal_iff_incompRel.2
    ⟨fun h ↦ by
      obtain ⟨w, hlw, hwy⟩ := (ml.decomposition h).1
      exact (le_csSup hb ⟨hxl.trans hlw.lt, hwy⟩).not_gt hlw.lt,
    fun h ↦ (csSup_le hS fun z hz ↦ hz.2.lt.le).not_gt h.lt⟩
  obtain ⟨w, hwl, -, hxw⟩ := (ml.decomposition (hly.largelyLT_congr_right.2 hxy)).2
  exact (csSup_le hS fun a ha ↦
    ((ml.irrelevance a hwl).1 (hly.largelyLT_congr_right.2 ha.2)).1.le).not_gt hwl.lt

/-- Every ML scale is infinite (p. 521). -/
theorem infinite_of_marginalScale (ml : MarginalScale α) : Infinite α :=
  let ⟨_, _, h⟩ := ml.exists_large
  Set.infinite_univ_iff.1 ((LargelyLT.infinite_Ioo h).mono (Set.subset_univ _))

example : IsEmpty (MarginalScale ℕ) := inferInstance

example : IsEmpty (MarginalScale ℝ) := inferInstance

/-! ### Nonstandard models -/

open ArchimedeanClass Hyperreal

/-- The hyperreals with infinitesimal differences marginal, the model `ℑ2` of Theorem 3.1. -/
noncomputable def infinitesimal : MarginalScale ℝ* :=
  ofAddSubgroup Itzhaki2021.infinitesimals (ordConnected_ballAddSubgroup 0)
    (fun h ↦ by
      have := Itzhaki2021.mem_infinitesimals.2 archimedeanClassMk_epsilon_pos
      rw [h, AddSubgroup.mem_bot] at this
      exact epsilon_ne_zero this)
    (fun h ↦ by
      have : (1 : ℝ*) ∈ Itzhaki2021.infinitesimals := h ▸ AddSubgroup.mem_top _
      simp at this)

theorem infinitesimal_marginallyLT_iff {x y : ℝ*} :
    infinitesimal.MarginallyLT x y ↔ x < y ∧ 0 < mk (y - x) := by
  rw [infinitesimal, ofAddSubgroup_marginallyLT_iff, Itzhaki2021.mem_infinitesimals]

/-- The hyperreals with finite differences marginal, the reading of Dean (§5) and of Itzhaki
(§6). -/
noncomputable def finite : MarginalScale ℝ* :=
  ofAddSubgroup Itzhaki2021.finites (ordConnected_closedBallAddSubgroup 0)
    (fun h ↦ by
      have : (1 : ℝ*) ∈ Itzhaki2021.finites := Itzhaki2021.mem_finites.2 (by simp)
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this)
    (fun h ↦ by
      have : ω ∈ Itzhaki2021.finites := h ▸ AddSubgroup.mem_top _
      exact (Itzhaki2021.mem_finites.1 this).not_gt archimedeanClassMk_omega_neg)

theorem finite_marginallyLT_iff {x y : ℝ*} : finite.MarginallyLT x y ↔ x < y ∧ 0 ≤ mk (y - x) := by
  rw [finite, ofAddSubgroup_marginallyLT_iff, Itzhaki2021.mem_finites]

example : infinitesimal.MarginallyLT 0 ε ∧ infinitesimal.LargelyLT 0 1 :=
  ⟨infinitesimal_marginallyLT_iff.2 ⟨epsilon_pos, by simp [archimedeanClassMk_epsilon_pos]⟩,
    zero_lt_one, fun h ↦ by simpa using (infinitesimal_marginallyLT_iff.1 h).2⟩

example : finite.MarginallyLT 0 1 ∧ finite.LargelyLT 0 ω :=
  ⟨finite_marginallyLT_iff.2 ⟨zero_lt_one, by simp⟩, omega_pos,
    fun h ↦ (finite_marginallyLT_iff.1 h).2.not_gt (by simp [archimedeanClassMk_omega_neg])⟩

/-! ### Representation -/

variable (ml) in
/-- `y` is a weakly marginal successor of `x` when `x` is marginally smaller than `y` and no
degree marginally above `x` is marginally below `y` (Definition 4.4). -/
def MarginalSucc (x y : α) : Prop :=
  ml.MarginallyLT x y ∧ ∀ z, ml.MarginallyLT x z → ¬ ml.MarginallyLT z y

variable (ml) in
/-- An ML scale is finitely marginal when finitely many weakly marginal successions lead from
any degree to any marginally greater one (Definition 4.5). -/
def FinitelyMarginal : Prop :=
  ∀ ⦃x y⦄, ml.MarginallyLT x y → Relation.TransGen (MarginalSucc ml) x y

theorem MarginalSucc.Icc_subset (h : MarginalSucc ml x y) : Set.Icc x y ⊆ {x, y} :=
  fun z ⟨hxz, hzy⟩ ↦ by
    rcases hxz.eq_or_lt with rfl | hxz; · exact .inl rfl
    rcases hzy.eq_or_lt with rfl | hzy; · exact .inr rfl
    exact absurd (h.1.bounded hxz hzy).2 (h.2 z (h.1.bounded hxz hzy).1)

theorem FinitelyMarginal.finite_Icc (hf : FinitelyMarginal ml) (h : ml.AtMostMarginal x y) :
    (Set.Icc x y).Finite := by
  rcases h with _ | h | h
  · simp
  · obtain hc := hf h
    clear h
    induction hc with
    | single hs => exact (Set.toFinite _).subset hs.Icc_subset
    | tail _ hs ih =>
      exact (ih.union ((Set.toFinite _).subset hs.Icc_subset)).subset Set.Icc_subset_Icc_union_Icc
  · simp [h.lt]

theorem FinitelyMarginal.finite_Icc_block (hf : FinitelyMarginal ml)
    (q : Quotient ml.atMostMarginalSetoid) (a b : {y // ⟦y⟧ = q}) : (Set.Icc a b).Finite :=
  (hf.finite_Icc (Quotient.exact (a.2.trans b.2.symm))).preimage Subtype.val_injective.injOn

theorem exists_lt_of_marginallyLT {γ : Type*} [Preorder γ]
    (h : ∀ q : Quotient ml.atMostMarginalSetoid, ∃ g : {y // ⟦y⟧ = q} → γ, StrictMono g) :
    ∃ G : α → γ, ∀ ⦃x y⦄, ml.MarginallyLT x y → G x < G y := by
  choose g hg using h
  have e (z : α) (q) (h : ⟦z⟧ = q) : g ⟦z⟧ ⟨z, rfl⟩ = g q ⟨z, h⟩ := by subst h; rfl
  refine ⟨fun z ↦ g ⟦z⟧ ⟨z, rfl⟩, fun x y h ↦ ?_⟩
  have hxy : (⟦x⟧ : Quotient ml.atMostMarginalSetoid) = ⟦y⟧ := Quotient.sound (.single (.inl h))
  simp only [e x _ hxy]
  exact hg _ h.lt

/-- Every countable, finitely marginal ML scale maps homomorphically into the representative
model (Theorem 4.7). -/
theorem exists_isHom_lex_rat_int [Countable α] (hf : FinitelyMarginal ml) :
    ∃ f : α → ℚ ×ₗ ℤ, ml.IsHom (lex ℚ ℤ) f := by
  obtain ⟨F, hF⟩ := Order.exists_rat_rel_iff_lt ml.LargelyLT
  obtain ⟨G, hG⟩ := exists_lt_of_marginallyLT fun q ↦ by
    let := LocallyFiniteOrder.ofFiniteIcc (hf.finite_Icc_block q)
    obtain ⟨e⟩ := nonempty_orderEmbedding_int {y // ⟦y⟧ = q}
    exact ⟨e, e.strictMono⟩
  exact ⟨fun x ↦ toLex (F x, G x), isHom_lex_iff.2 ⟨hF, hG⟩⟩

/-- Every countable ML scale maps homomorphically into rational-indexed blocks of
rational-indexed locations (§4.4). -/
theorem exists_isHom_lex_rat_rat [Countable α] : ∃ f : α → ℚ ×ₗ ℚ, ml.IsHom (lex ℚ ℚ) f := by
  obtain ⟨F, hF⟩ := Order.exists_rat_rel_iff_lt ml.LargelyLT
  obtain ⟨G, hG⟩ := exists_lt_of_marginallyLT (γ := ℚ) fun q ↦ by
    obtain ⟨e⟩ := Order.embedding_from_countable_to_dense {y : α // ⟦y⟧ = q} ℚ
    exact ⟨e, e.strictMono⟩
  exact ⟨fun x ↦ toLex (F x, G x), isHom_lex_iff.2 ⟨hF, hG⟩⟩

/-! ### Uniqueness -/

section Uniqueness

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- A transformation of a set of pairs is cautiously monotone-increasing when it maps blocks by
one strictly increasing map and the locations within each block by strictly increasing maps
(Definition 4.8). -/
def CautiouslyMonotone (X : Set (β ×ₗ γ)) (τ : β ×ₗ γ → β ×ₗ γ) : Prop :=
  ∃ (f : β → β) (g : β → γ → γ), StrictMonoOn f ((fun p ↦ (ofLex p).1) '' X) ∧
    (∀ a, StrictMonoOn (g a) {b | toLex (a, b) ∈ X}) ∧
    ∀ p ∈ X, τ p = toLex (f (ofLex p).1, g (ofLex p).1 (ofLex p).2)

variable [Nontrivial β] [Nonempty γ] [NoMaxOrder γ] [NoMinOrder γ]

/-- A representation composed with a cautiously monotone-increasing transformation is a
representation (Theorem 4.9). -/
theorem IsHom.comp_cautiouslyMonotone {h : α → β ×ₗ γ} (hh : ml.IsHom (lex β γ) h)
    {τ : β ×ₗ γ → β ×ₗ γ} (hτ : CautiouslyMonotone (Set.range h) τ) :
    ml.IsHom (lex β γ) (τ ∘ h) := by
  obtain ⟨f, g, hf, hg, hτ⟩ := hτ
  obtain ⟨hL, hM⟩ := isHom_lex_iff.1 hh
  refine isHom_lex_iff.2 ⟨fun x y ↦ ?_, fun x y hxy ↦ ?_⟩
  · simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, hL]
    exact (hf.lt_iff_lt ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, rfl⟩).symm
  · have he : (ofLex (h x)).1 = (ofLex (h y)).1 := hh.fst_eq_fst_iff.2 (.single (.inl hxy))
    simp only [Function.comp, hτ _ ⟨x, rfl⟩, hτ _ ⟨y, rfl⟩, ofLex_toLex, he]
    exact hg _ (by simp [← he]) ⟨y, rfl⟩ (hM hxy)

/-- Any two representations differ by a cautiously monotone-increasing transformation
(Theorem 4.9). -/
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

theorem bald_of_le (h : e ≤ x) : Bald ml e x := fun hl ↦ (hl.lt.trans_le h).false

theorem Bald.tolerance :
    (¬ Bald ml e x → ml.MarginallyLT x y → ¬ Bald ml e y) ∧
      (Bald ml e x → ml.MarginallyLT y x → Bald ml e y) := by
  unfold Bald
  grind [ml.irrelevance, LargelyLT]

theorem not_transGen_marginallyLT (hx : ¬ Bald ml e x) :
    ¬ Relation.TransGen ml.MarginallyLT x e := fun h ↦ by
  rw [Relation.transGen_eq_self] at h
  exact h.not_largelyLT (not_not.1 hx)

example :
    ¬ Bald (lex ℚ ℤ) (toLex (1, 0)) (toLex (0, 0)) ∧ Bald (lex ℚ ℤ) (toLex (1, 0)) (toLex (1, 0)) :=
  ⟨not_not.2 (lex_largelyLT_iff.2 zero_lt_one), bald_of_le le_rfl⟩

end Sorites

/-! ### Itzhaki's nonstandard heuristics -/

theorem infinitesimal_atMostMarginal_iff {x y : ℝ*} :
    infinitesimal.AtMostMarginal x y ↔ Itzhaki2021.InfinitesimallyClose x y := by
  rw [infinitesimal, ofAddSubgroup_atMostMarginal_iff, Itzhaki2021.InfinitesimallyClose,
    ← AddSubgroup.neg_mem_iff, neg_sub]

/-- Itzhaki's finite closeness is at most marginal difference on the finite scale (§6). -/
theorem finite_atMostMarginal_iff {x y : ℝ*} :
    finite.AtMostMarginal x y ↔ Itzhaki2021.FinitelyClose x y := by
  rw [finite, ofAddSubgroup_atMostMarginal_iff, Itzhaki2021.FinitelyClose,
    ← AddSubgroup.neg_mem_iff, neg_sub]

/-- Being infinitely less, in Itzhaki's sense, is being largely smaller on the finite scale
(§6). -/
theorem finite_largelyLT_iff {x y : ℝ*} :
    finite.LargelyLT x y ↔ Itzhaki2021.InfinitelyLess x y := by
  rw [LargelyLT, Itzhaki2021.InfinitelyLess, marginallyLT_iff_lt_and_atMostMarginal,
    finite_atMostMarginal_iff]
  tauto

/-- Under Itzhaki's qualitative size, the heaps are exactly what is not largely smaller than a
clear case on the finite scale, the baldness of §5 (§6). -/
theorem heap_iff_bald {De : Type*} {heap known : De → Prop} [DecidablePred heap]
    [DecidablePred known] {size : De → ℕ} {H : ℝ*} (hH : mk H < 0) (hpos : 0 < H) {e x : De}
    (he : heap e) : heap x ↔ Bald finite (Itzhaki2021.qualSize heap known size H e)
      (Itzhaki2021.qualSize heap known size H x) := by
  rw [Bald, finite_largelyLT_iff]
  refine ⟨fun hx h ↦ h.2 (Itzhaki2021.finitelyClose_qualSize hx he),
    fun h ↦ by_contra fun hx ↦ h ?_⟩
  rw [Itzhaki2021.qualSize_of_not_heap hx]
  refine ⟨Itzhaki2021.natCast_lt_qualSize hH hpos he _, fun hf ↦ ?_⟩
  have hq := Itzhaki2021.finites.sub_mem
    (Itzhaki2021.mem_finites.2 (mk_natCast_nonneg (size x))) hf
  rw [sub_sub_cancel, Itzhaki2021.mem_finites] at hq
  exact hq.not_gt (Itzhaki2021.mk_qualSize_neg hH he)

end DinisJacinto2025
