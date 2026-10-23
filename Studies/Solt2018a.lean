module

public import Linglib.Core.SocialChoice.Rules
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Comparable

/-!
# Solt (2018): Multidimensionality, subjectivity and scales

This file formalizes [solt-2018a]'s account of ordering subjectivity, the faultless disagreement
some gradable adjectives allow about their comparatives: which of two dishes is tastier, but not
which of two people is taller. A gradable adjective lexicalizes a family of measure functions
indexed by contexts (35). Its comparative is subjective for a pair when two contexts order the
pair oppositely (`OrderingSubjective`), which is incomparability with the contexts read as
dimensions (`orderingSubjective_iff_incompRel`), and settled when every context orders it alike
(`Settled`). Objectivity is a single measure that every context agrees with (`Externalizable`).
Additive measures that never reverse a pair differ only in unit (`eq_smul_of_forall_lt_imp_le`,
the uniqueness half of Hölder's theorem), so an additive family (36) is externalizable exactly
when it has no ordering subjectivity (`externalizable_iff_forall_not_orderingSubjective`), and so
is a homogeneous function of such measures (38) (`externalizable_derived`), such as fullness (39)
(`fullness_eq`).

For a multidimensional adjective such as *dirty* (41) the context weights the kinds of dirt, and
the verdict that all weightings share is the Pareto rule (`forall_dirty_le_iff`). A pair is
settled when one object carries at least as much of every kind of dirt per unit of size and more
of some (`settled_dirty_iff`), and subjective when neither dominates the other
(`orderingSubjective_dirty_iff`), so the class is mixed. A judge-dependent adjective (42) has
unconstrained measures, so every pair of distinct individuals is subjective
(`orderingSubjective_of_surjective`) and none is settled (`not_settled_of_surjective`). These are
the three classes of Table 1, matching the experiment of section 2: speakers judged disagreements
about the comparatives of measurable adjectives factual, those about evaluative adjectives
matters of opinion, and the rest mixed.

## Implementation notes

* `OrderingSubjective` asks for a strict reversal, the disagreement of the dialogues (2) and
  (5)–(7); section 5.3's "difference in the relative ordering" is broader, but the two coincide
  on the families formalized.
* Concatenation (36) is the addition of an `AddCommMonoid`. Additivity alone does not exclude
  ordering subjectivity, since a positive weighting of additive measures is additive; that the
  measures of height differ only in unit is what section 5.1 suggests ("this might be the only
  sort of variation that is possible"). Likewise (38) needs `f` homogeneous.
* In (41) a context is a weighting positive on every kind of dirt, the kinds and amounts being
  fixed; the units of amount and size only rescale the score. With unbounded weights a pair is
  settled exactly when it is Pareto-ordered, where "contexts can only vary so much" (section 5.4)
  suggests bounded ones.
* "Not constrained in any formal way" (section 5.4) is `Function.Surjective`, a strong
  idealization.

## TODO

* The five stimulus categories of section 2.2, their rates of 'fact' judgments in Figure 1 (98,
  94, 67, 55 and 4 %) and the appendix dialogues are not encoded as example rows; the rates of
  single adjectives are drawn only in a bar chart.
* The rows of Table 1 for ambiguous adjectives (*bumpy*, *salty*) are not formalized. Read as one
  family over both readings' contexts, such an adjective would settle no pair.
* Section 5.5's *intelligent*, multidimensional yet purely subjective, and the externally
  anchored measures of time and temperature are not formalized.

## References

* [solt-2018a]
-/

@[expose] public section

namespace Solt2018a

open SocialChoice Matrix

variable {C E K : Type*}

/-! ### Ordering subjectivity -/

section Preorder

variable [Preorder K] (μ : C → E → K)

/-- Ordering subjectivity (section 5.3) holds of `a` and `b` when two contexts order them
oppositely, as in the faultless disagreements (2a–b). -/
def OrderingSubjective (a b : E) : Prop := ∃ c c', μ c b < μ c a ∧ μ c' a < μ c' b

/-- The comparative *`a` is Adj-er than `b`* is settled when every context ranks `a` above `b`,
so that a disagreement about it is factual, as in (2c). -/
def Settled (a b : E) : Prop := ∀ c, μ c b < μ c a

/-- A family is externalizable when one measure `ν` orders every pair as every context does,
the principled order-preserving mapping to the numbers of section 5.2. -/
def Externalizable : Prop := ∃ ν : E → K, ∀ c a b, μ c b < μ c a ↔ ν b < ν a

variable {μ} {a b : E}

theorem OrderingSubjective.symm (h : OrderingSubjective μ a b) : OrderingSubjective μ b a :=
  let ⟨c, c', h, h'⟩ := h
  ⟨c', c, h', h⟩

theorem orderingSubjective_comm : OrderingSubjective μ a b ↔ OrderingSubjective μ b a :=
  ⟨.symm, .symm⟩

theorem Settled.not_orderingSubjective (h : Settled μ a b) : ¬ OrderingSubjective μ a b :=
  fun ⟨_, c', _, h'⟩ ↦ (h c').not_gt h'

theorem Externalizable.not_orderingSubjective (h : Externalizable μ) :
    ¬ OrderingSubjective μ a b := fun ⟨c, c', h₁, h₂⟩ ↦
  let ⟨_, hν⟩ := h
  ((hν c a b).1 h₁).not_gt ((hν c' b a).1 h₂)

theorem Externalizable.settled_iff (h : Externalizable μ) (c : C) :
    Settled μ a b ↔ μ c b < μ c a :=
  let ⟨_, hν⟩ := h
  ⟨fun h' ↦ h' c, fun hab c' ↦ (hν c' a b).2 ((hν c a b).1 hab)⟩

end Preorder

theorem orderingSubjective_iff_incompRel [LinearOrder K] {μ : C → E → K} {a b : E} :
    OrderingSubjective μ a b ↔ IncompRel (· ≤ ·) (fun c ↦ μ c a) (fun c ↦ μ c b) := by
  simp only [OrderingSubjective, IncompRel, Pi.le_def, not_forall, not_le]
  exact ⟨fun ⟨c, c', h, h'⟩ ↦ ⟨⟨c, h⟩, c', h'⟩, fun ⟨⟨c, h⟩, c', h'⟩ ↦ ⟨c, c', h, h'⟩⟩

theorem Externalizable.of_forall_eq_smul [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {μ : C → E → K} (h : ∀ c c', ∃ k : K, 0 < k ∧ μ c' = k • μ c) : Externalizable μ := by
  rcases isEmpty_or_nonempty C with hC | ⟨⟨c₀⟩⟩
  · exact ⟨0, fun c ↦ isEmptyElim c⟩
  refine ⟨μ c₀, fun c a b ↦ ?_⟩
  obtain ⟨k, hk, e⟩ := h c₀ c
  rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_lt_mul_iff_of_pos_left hk]

/-! ### Additive measures -/

section Additive

variable [AddCommMonoid E] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]

private theorem not_div_lt_div {μ μ' : E →+ K} {u : E} (hu : 0 < μ u) (hu' : 0 < μ' u)
    (h : ∀ a b, μ b < μ a → μ' b ≤ μ' a) (x : E) : ¬ μ x / μ u < μ' x / μ' u := by
  intro hlt
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
  have hn : (0 : K) < q.den := by exact_mod_cast q.den_pos
  have hz : (q.num : K) = (q.num.toNat : K) - ((-q.num).toNat : K) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg q.num).symm
  have hq : (q.den : K) * q = q.num := by
    rw [Rat.cast_def]
    field_simp
  have h₁ := mul_lt_mul_of_pos_left ((div_lt_iff₀ hu).1 hq₁) hn
  have h₂ := mul_lt_mul_of_pos_left ((lt_div_iff₀ hu').1 hq₂) hn
  rw [← mul_assoc, hq, hz] at h₁ h₂
  refine (h (q.num.toNat • u) (q.den • x + (-q.num).toNat • u) ?_).not_gt ?_ <;>
    simp only [map_add, map_nsmul, nsmul_eq_mul] <;> linarith

private theorem eq_smul_of_pos {μ μ' : E →+ K} {u : E} (hu : 0 < μ u) (hu' : 0 < μ' u)
    (h : ∀ a b, μ b < μ a → μ' b ≤ μ' a) : ⇑μ' = (μ' u / μ u) • ⇑μ := by
  have h' : ∀ a b, μ' b < μ' a → μ b ≤ μ a :=
    fun a b hab ↦ not_lt.1 fun hba ↦ (h b a hba).not_gt hab
  funext x
  have := le_antisymm (not_lt.1 (not_div_lt_div hu' hu h' x))
    (not_lt.1 (not_div_lt_div hu hu' h x))
  rw [div_eq_div_iff hu.ne' hu'.ne'] at this
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hu.ne']
  linarith

/-- Additive measures (36) that never order a pair oppositely differ only in unit, each being the
other rescaled by their ratio at a standard element `u`. This is the uniqueness half of Hölder's
theorem. -/
theorem eq_smul_of_forall_lt_imp_le {μ μ' : E →+ K} {u : E} (hu : 0 < μ u)
    (h : ∀ a b, μ b < μ a → μ' b ≤ μ' a) : ⇑μ' = (μ' u / μ u) • ⇑μ := by
  have h0 : 0 ≤ μ' u := by simpa using h u 0 (by simpa using hu)
  -- `μ' + μ` is positive at the standard and still never reverses `μ`
  have e := eq_smul_of_pos (μ' := μ' + μ) hu (add_pos_of_nonneg_of_pos h0 hu)
    fun a b hab ↦ by simpa using add_le_add (h a b hab) hab.le
  funext x
  have hx := congrFun e x
  simp only [AddMonoidHom.add_apply, Pi.smul_apply, smul_eq_mul, add_div, div_self hu.ne',
    add_mul, one_mul] at hx
  rw [Pi.smul_apply, smul_eq_mul]
  linarith

variable {μ : C → E →+ K} {u : E}

/-- An additive family (36) has no ordering subjectivity exactly when its measures differ in unit
alone, as height in inches and height in centimeters do (section 5.1). -/
theorem forall_not_orderingSubjective_iff (hu : ∀ c, 0 < μ c u) :
    (∀ a b, ¬ OrderingSubjective (fun c ↦ ⇑(μ c)) a b) ↔
      ∀ c c', ⇑(μ c') = (μ c' u / μ c u) • ⇑(μ c) :=
  ⟨fun h c c' ↦ eq_smul_of_forall_lt_imp_le (hu c) fun a b hab ↦
    not_lt.1 fun hab' ↦ h a b ⟨c, c', hab, hab'⟩, fun h _ _ ↦
    (Externalizable.of_forall_eq_smul fun c c' ↦
      ⟨_, div_pos (hu c') (hu c), h c c'⟩).not_orderingSubjective⟩

/-- An additive family (36) with a positive standard is externalizable exactly when it has no
ordering subjectivity (section 5.2). -/
theorem externalizable_iff_forall_not_orderingSubjective (hu : ∀ c, 0 < μ c u) :
    Externalizable (fun c ↦ ⇑(μ c)) ↔ ∀ a b, ¬ OrderingSubjective (fun c ↦ ⇑(μ c)) a b :=
  ⟨fun h _ _ ↦ h.not_orderingSubjective, fun h ↦ .of_forall_eq_smul fun c c' ↦
    ⟨_, div_pos (hu c') (hu c), (forall_not_orderingSubjective_iff hu).1 h c c'⟩⟩

end Additive

/-! ### Derived measures -/

section Derived

variable [Field K] {X : Type*} {content capacity : X → E}

/-- Fullness (39) is the volume of a container's contents over the volume it can hold. -/
def fullness (vol : E → K) (content capacity : X → E) (x : X) : K :=
  vol (content x) / vol (capacity x)

theorem fullness_smul {k : K} (hk : k ≠ 0) (vol : E → K) :
    fullness (k • vol) content capacity = fullness vol content capacity := by
  funext x
  simp only [fullness, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hk]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A context-independent derived family (38), a fixed function `f` of component measures, is
externalizable when the components differ across contexts only in unit and rescaling the
components rescales `f` by a positive factor. -/
theorem externalizable_derived {ι : Type*} {m : C → ι → E → K} {f : (ι → K) → K}
    (hf : ∀ k : ι → K, (∀ i, 0 < k i) → ∃ φ : K, 0 < φ ∧ ∀ y, f (k * y) = φ * f y)
    (hm : ∀ c c', ∃ k : ι → K, (∀ i, 0 < k i) ∧ ∀ i x, m c' i x = k i * m c i x) :
    Externalizable fun c x ↦ f fun i ↦ m c i x := by
  refine .of_forall_eq_smul fun c c' ↦ ?_
  obtain ⟨k, hk, e⟩ := hm c c'
  obtain ⟨φ, hφ, hf⟩ := hf k hk
  refine ⟨φ, hφ, funext fun x ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, ← hf]
  exact congrArg f (funext fun i ↦ e i x)

variable [AddCommMonoid E] [Archimedean K] {μ : C → E →+ K} {u : E}

theorem fullness_eq (hu : ∀ c, 0 < μ c u)
    (h : ∀ a b, ¬ OrderingSubjective (fun c ↦ ⇑(μ c)) a b) (c c' : C) :
    fullness (μ c') content capacity = fullness (μ c) content capacity := by
  rw [(forall_not_orderingSubjective_iff hu).1 h c c',
    fullness_smul (div_pos (hu c') (hu c)).ne']

end Derived

/-! ### Multidimensional measures -/

section Multidimensional

variable {ι : Type*} [Fintype ι] [Field K] [LinearOrder K] (amount : Profile ι E K)
  (size : E → K)

/-- *Dirty* (41) is the weighted sum of the amounts of the kinds of dirt on an object over its
size, the context being a weighting positive on every kind. -/
def dirty (k : {k : ι → K // ∀ i, 0 < k i}) (x : E) : K :=
  k.1 ⬝ᵥ amount x / size x

variable {amount size} {a b : E}

theorem dirty_eq (k : {k : ι → K // ∀ i, 0 < k i}) (x : E) :
    dirty amount size k x = k.1 ⬝ᵥ (size x)⁻¹ • amount x := by
  rw [dirty, dotProduct_smul, smul_eq_mul, div_eq_inv_mul]

variable [IsStrictOrderedRing K]

theorem forall_dirty_le_iff :
    (∀ k, dirty amount size k a ≤ dirty amount size k b) ↔
      (size a)⁻¹ • amount a ≤ (size b)⁻¹ • amount b := by
  simp only [dirty_eq, Subtype.forall]
  exact (paretoRule_iff_forall_utilitarian (v := fun x ↦ (size x)⁻¹ • amount x)).symm

theorem orderingSubjective_dirty_iff :
    OrderingSubjective (dirty amount size) a b ↔
      IncompRel (· ≤ ·) ((size a)⁻¹ • amount a) ((size b)⁻¹ • amount b) := by
  rw [orderingSubjective_iff_incompRel]
  exact and_congr (not_congr forall_dirty_le_iff) (not_congr forall_dirty_le_iff)

theorem settled_dirty_iff :
    Settled (dirty amount size) a b ↔ (size b)⁻¹ • amount b < (size a)⁻¹ • amount a := by
  have := asymmRel_paretoRule_iff_forall_utilitarian
    (v := fun x ↦ (size x)⁻¹ • amount x) (x := a) (y := b)
  simp only [AsymmRel, paretoRule, utilitarian, ← lt_iff_le_not_ge] at this
  simp only [Settled, dirty_eq, Subtype.forall, this]

end Multidimensional

/-! ### Judge-dependent measures -/

section Judge

variable {J : Type*} [LinearOrder K] {μ : J → E → K} {a b : E}

/-- A judge-dependent adjective (42) has a measure per judge, and when the judges' tastes are
unconstrained any two individuals can be ranked either way. -/
theorem orderingSubjective_of_surjective [Nontrivial K] (hμ : Function.Surjective μ)
    (hab : a ≠ b) : OrderingSubjective μ a b := by
  classical
  obtain ⟨d, d', hd⟩ := exists_pair_lt K
  obtain ⟨j, hj⟩ := hμ fun x ↦ if x = a then d' else d
  obtain ⟨j', hj'⟩ := hμ fun x ↦ if x = a then d else d'
  exact ⟨j, j', by simp [hj, hab.symm, hd], by simp [hj', hab.symm, hd]⟩

theorem not_settled_of_surjective [Nonempty K] (hμ : Function.Surjective μ) :
    ¬ Settled μ a b := fun h ↦
  let ⟨j, hj⟩ := hμ fun _ ↦ Classical.arbitrary K
  (h j).ne (by simp [hj])

end Judge

end Solt2018a
