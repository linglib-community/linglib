module

public import Linglib.Core.Combinatorics.SimpleGraph.MaximalIndepSet
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Dimensions of social evaluation

Two properties are incompatible when they are distinct values of one dimension, and an
incompatibility [comes from dimensions](##SocialMeaning.isCompleteMultipartite_compl_iff) exactly
when its complement is complete multipartite. A set of properties is then consistent when
[the dimension map is injective on it](##SocialMeaning.isIndepSet_dimensionalIncompatibility_iff),
and [a persona](##SocialMeaning.mem_maximalIndepSets_dimensionalIncompatibility_iff) when it
takes one value of each dimension. When every dimension has two poles, the
consistent sets are [the poles of sign vectors](##SocialMeaning.exists_poles_eq), the personae
those of [vectors with no zero](##SocialMeaning.poles_mem_maximalIndepSets_iff), and a vector with
$z$ zeros over $n$ dimensions has
[$2^z$ personae with all its properties](##SocialMeaning.card_filter_poles_subset) and
[$2^n - 2^z$ sharing one](##SocialMeaning.card_filter_not_disjoint_poles). The dimensions of
social evaluation are the competence and warmth of the Stereotype Content Model and the
anti-solidarity of Beltrama, Solt and Burnett's ratings.

## References

* [fiske-cuddy-glick-xu-2002]
* [fiske-cuddy-glick-2007]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

@[expose] public section

namespace SocialMeaning

section Dimensional

universe u

variable {P : Type u} {D : Type*} {dim : P → D} {G : SimpleGraph P}

/-- The incompatibility of a family of dimensions joins two properties when they are distinct
values of one dimension. -/
def dimensionalIncompatibility (dim : P → D) : SimpleGraph P where
  Adj p q := p ≠ q ∧ dim p = dim q
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp] theorem dimensionalIncompatibility_adj {p q : P} :
    (dimensionalIncompatibility dim).Adj p q ↔ p ≠ q ∧ dim p = dim q := Iff.rfl

instance [DecidableEq P] [DecidableEq D] : DecidableRel (dimensionalIncompatibility dim).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem compl_dimensionalIncompatibility :
    (dimensionalIncompatibility dim)ᶜ = (⊤ : SimpleGraph D).comap dim := by
  ext p q
  simp only [SimpleGraph.compl_adj, dimensionalIncompatibility_adj, SimpleGraph.comap_adj,
    SimpleGraph.top_adj]
  exact ⟨fun ⟨hne, h⟩ hd ↦ h ⟨hne, hd⟩, fun hd ↦ ⟨fun e ↦ hd (congrArg dim e), fun h ↦ hd h.2⟩⟩

theorem isCompleteMultipartite_compl_dimensionalIncompatibility :
    (dimensionalIncompatibility dim)ᶜ.IsCompleteMultipartite := by
  rw [compl_dimensionalIncompatibility]
  exact ⟨fun _ _ _ hab hbc ↦ by simp_all⟩

/-- An incompatibility graph comes from dimensions exactly when its compatibility graph is
complete multipartite; the dimensions are then the parts. -/
theorem isCompleteMultipartite_compl_iff :
    Gᶜ.IsCompleteMultipartite ↔
      ∃ (D : Type u) (dim : P → D), dimensionalIncompatibility dim = G := by
  refine ⟨fun h ↦ ⟨_, Quotient.mk h.setoid, ?_⟩, ?_⟩
  · ext p q
    simp only [dimensionalIncompatibility_adj, Quotient.eq]
    change p ≠ q ∧ ¬Gᶜ.Adj p q ↔ G.Adj p q
    rw [SimpleGraph.compl_adj]
    exact ⟨fun ⟨hne, h⟩ ↦ by_contra fun hn ↦ h ⟨hne, hn⟩, fun hadj ↦ ⟨hadj.ne, fun h ↦ h.2 hadj⟩⟩
  · rintro ⟨D, dim, rfl⟩
    exact isCompleteMultipartite_compl_dimensionalIncompatibility

/-- A set of properties is consistent exactly when it takes at most one value of each dimension. -/
theorem isIndepSet_dimensionalIncompatibility_iff {s : Set P} :
    (dimensionalIncompatibility dim).IsIndepSet s ↔ s.InjOn dim := by
  simp only [SimpleGraph.IsIndepSet, Set.Pairwise, dimensionalIncompatibility_adj, Set.InjOn]
  exact forall₂_congr fun p _ ↦ forall₂_congr fun q _ ↦
    ⟨fun h hd ↦ by_contra fun hne ↦ h hne ⟨hne, hd⟩, fun h hne hpq ↦ hne (h hpq.2)⟩

/-- A maximal consistent set of properties takes exactly one value of each dimension. -/
theorem maximal_isIndepSet_dimensionalIncompatibility_iff {s : Set P} :
    Maximal (dimensionalIncompatibility dim).IsIndepSet s ↔ s.BijOn dim (Set.range dim) := by
  rw [SimpleGraph.maximal_isIndepSet_iff_forall_exists_adj,
    isIndepSet_dimensionalIncompatibility_iff]
  refine ⟨fun ⟨hi, hd⟩ ↦ ⟨fun p _ ↦ ⟨p, rfl⟩, hi, ?_⟩, fun ⟨_, hi, hs⟩ ↦ ⟨hi, fun p hp ↦ ?_⟩⟩
  · rintro _ ⟨p, rfl⟩
    by_cases hp : p ∈ s
    · exact ⟨p, hp, rfl⟩
    · obtain ⟨q, hq, -, h⟩ := hd p hp
      exact ⟨q, hq, h.symm⟩
  · obtain ⟨q, hq, h⟩ := hs ⟨p, rfl⟩
    exact ⟨q, hq, fun e ↦ hp (e ▸ hq), h.symm⟩

theorem mem_maximalIndepSets_dimensionalIncompatibility_iff [Fintype P] [DecidableEq P]
    [DecidableEq D] {s : Finset P} :
    s ∈ (dimensionalIncompatibility dim).maximalIndepSets ↔
      (s : Set P).BijOn dim (Set.range dim) := by
  rw [SimpleGraph.mem_maximalIndepSets, maximal_isIndepSet_dimensionalIncompatibility_iff]

end Dimensional

section Bipolar

variable {P D : Type*} [Fintype P] {dim : P → D} {pol : P → SignType} {σ τ : D → SignType}
  {p : P}

/-- The poles a sign vector points to: of each dimension, the property whose polarity is the sign
the vector gives the dimension, and neither where that sign is zero. -/
def poles (dim : P → D) (pol : P → SignType) (σ : D → SignType) : Finset P :=
  Finset.univ.filter fun p ↦ σ (dim p) = pol p

@[simp] theorem mem_poles : p ∈ poles dim pol σ ↔ σ (dim p) = pol p := by simp [poles]

variable (hb : Set.BijOn (fun p ↦ (dim p, pol p)) Set.univ {x | x.2 ≠ 0})
include hb

omit [Fintype P] in
private theorem pol_ne_zero (p : P) : pol p ≠ 0 := hb.mapsTo (Set.mem_univ p)

omit [Fintype P] in
private theorem eq_of_dim_eq_of_pol_eq {q : P} (hd : dim p = dim q) (hp : pol p = pol q) :
    p = q :=
  hb.injOn (Set.mem_univ p) (Set.mem_univ q) (Prod.ext hd hp)

omit [Fintype P] in
private theorem exists_pole (d : D) {s : SignType} (hs : s ≠ 0) : ∃ p, dim p = d ∧ pol p = s := by
  obtain ⟨p, -, hp⟩ := hb.surjOn (show (d, s) ∈ {x : D × SignType | x.2 ≠ 0} from hs)
  exact ⟨p, congrArg Prod.fst hp, congrArg Prod.snd hp⟩

private theorem mem_poles_of_ne_zero {d : D} (hd : σ d ≠ 0) :
    ∃ p ∈ poles dim pol σ, dim p = d := by
  obtain ⟨p, rfl, hp⟩ := exists_pole hb d hd
  exact ⟨p, mem_poles.2 hp.symm, rfl⟩

theorem isIndepSet_poles (σ : D → SignType) :
    (dimensionalIncompatibility dim).IsIndepSet (poles dim pol σ : Set P) :=
  isIndepSet_dimensionalIncompatibility_iff.2 fun p hp q hq hd ↦ eq_of_dim_eq_of_pol_eq hb hd
    (by rw [← mem_poles.1 hp, ← mem_poles.1 hq, hd])

/-- Every consistent set of properties is the set of poles of a sign vector. -/
theorem exists_poles_eq {s : Finset P}
    (hs : (dimensionalIncompatibility dim).IsIndepSet (s : Set P)) : ∃ σ, poles dim pol σ = s := by
  classical
  have hinj := isIndepSet_dimensionalIncompatibility_iff.1 hs
  refine ⟨fun d ↦ if h : ∃ q ∈ s, dim q = d then pol h.choose else 0, Finset.ext fun p ↦ ?_⟩
  rw [mem_poles]
  by_cases h : ∃ q ∈ s, dim q = dim p
  · obtain ⟨hq, hd⟩ := h.choose_spec
    simp only [h, ↓reduceDIte]
    exact ⟨fun hp ↦ eq_of_dim_eq_of_pol_eq hb hd hp ▸ hq, fun hp ↦ by rw [hinj hq hp hd]⟩
  · simp only [h, ↓reduceDIte]
    exact ⟨fun hp ↦ absurd hp.symm (pol_ne_zero hb p), fun hp ↦ absurd ⟨p, hp, rfl⟩ h⟩

private theorem eq_of_poles_subset (h : poles dim pol σ ⊆ poles dim pol τ) {d : D}
    (hd : σ d ≠ 0) : σ d = τ d := by
  obtain ⟨p, hp, rfl⟩ := mem_poles_of_ne_zero hb hd
  rw [mem_poles.1 hp, mem_poles.1 (h hp)]

theorem poles_injective : Function.Injective (poles dim pol) := fun σ τ h ↦ funext fun d ↦ by
  by_cases hσ : σ d = 0
  · by_cases hτ : τ d = 0
    · rw [hσ, hτ]
    · exact (eq_of_poles_subset hb h.ge hτ).symm
  · exact eq_of_poles_subset hb h.le hσ

/-- The poles of one vector lie among those of another exactly when the second agrees with the
first wherever the first is nonzero. -/
theorem poles_subset_poles_iff : poles dim pol σ ⊆ poles dim pol τ ↔ ∀ d, σ d ≠ 0 → σ d = τ d :=
  ⟨fun h _ ↦ eq_of_poles_subset hb h, fun h p hp ↦ by
    rw [mem_poles] at hp ⊢
    rw [← h _ (hp ▸ pol_ne_zero hb p), hp]⟩

theorem disjoint_poles_iff :
    Disjoint (poles dim pol σ) (poles dim pol τ) ↔ ∀ d, σ d ≠ 0 → σ d ≠ τ d := by
  refine ⟨fun h d hd he ↦ ?_, fun h ↦ Finset.disjoint_left.2 fun p hp hq ↦ ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_poles_of_ne_zero hb hd
    exact Finset.disjoint_left.1 h hp (mem_poles.2 (he ▸ mem_poles.1 hp))
  · rw [mem_poles] at hp hq
    exact h _ (hp ▸ pol_ne_zero hb p) (hp.trans hq.symm)

/-- The poles of a vector form a persona exactly when the vector has no zero. -/
theorem poles_mem_maximalIndepSets_iff [DecidableEq P] [DecidableEq D] :
    poles dim pol σ ∈ (dimensionalIncompatibility dim).maximalIndepSets ↔ ∀ d, σ d ≠ 0 := by
  rw [mem_maximalIndepSets_dimensionalIncompatibility_iff]
  refine ⟨fun ⟨_, _, hs⟩ d hd ↦ ?_, fun h ↦ ⟨fun p _ ↦ ⟨p, rfl⟩,
    isIndepSet_dimensionalIncompatibility_iff.1 (isIndepSet_poles hb σ), ?_⟩⟩
  · obtain ⟨p, rfl, -⟩ := exists_pole hb d one_ne_zero
    obtain ⟨q, hq, he⟩ := hs ⟨p, rfl⟩
    exact pol_ne_zero hb q (by rw [← mem_poles.1 hq, he, hd])
  · rintro _ ⟨p, rfl⟩
    exact mem_poles_of_ne_zero hb (h (dim p))

/-- The properties a vector with no zero does not point to are the poles of its negation. -/
theorem compl_poles [DecidableEq P] (hσ : ∀ d, σ d ≠ 0) :
    (poles dim pol σ)ᶜ = poles dim pol (-σ) := by
  ext p
  rw [Finset.mem_compl, mem_poles, mem_poles, Pi.neg_apply]
  have h₁ := hσ (dim p)
  have h₂ := pol_ne_zero hb p
  revert h₁ h₂
  generalize σ (dim p) = s
  generalize pol p = t
  revert s t
  decide

/-- The poles of one vector are the properties another does not point to exactly when the other
has no zero and the first is its negation. -/
theorem poles_eq_compl_poles_iff [DecidableEq P] :
    poles dim pol τ = (poles dim pol σ)ᶜ ↔ (∀ d, σ d ≠ 0) ∧ τ = -σ := by
  refine ⟨fun h ↦ ?_, fun ⟨hσ, h⟩ ↦ h ▸ (compl_poles hb hσ).symm⟩
  have hσ (d : D) : σ d ≠ 0 := fun hd ↦ by
    obtain ⟨p, rfl, hp⟩ := exists_pole hb d one_ne_zero
    obtain ⟨q, hq, hpq⟩ := exists_pole hb (dim p) (by decide : (-1 : SignType) ≠ 0)
    have h₁ := mem_poles.1 (h ▸ Finset.mem_compl.2 fun hm ↦ pol_ne_zero hb p
      (hp ▸ (mem_poles.1 hm).symm.trans hd) : p ∈ poles dim pol τ)
    have h₂ := mem_poles.1 (h ▸ Finset.mem_compl.2 fun hm ↦ pol_ne_zero hb q
      ((mem_poles.1 hm).symm.trans (hq ▸ hd)) : q ∈ poles dim pol τ)
    rw [hq, hpq] at h₂
    rw [hp, h₂] at h₁
    exact absurd h₁ (by decide)
  exact ⟨hσ, poles_injective hb (h.trans (compl_poles hb hσ))⟩

section Card

variable [Fintype D] [DecidableEq P] [DecidableEq D]

private theorem filter_poles_subset_eq (σ : D → SignType) :
    (dimensionalIncompatibility dim).maximalIndepSets.filter (poles dim pol σ ⊆ ·) =
      (Fintype.piFinset fun d ↦ if σ d = 0 then {1, -1} else {σ d}).image (poles dim pol) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hs, hσ⟩
    obtain ⟨τ, rfl⟩ := exists_poles_eq hb ((SimpleGraph.mem_maximalIndepSets _).1 hs).prop
    have hτ := (poles_mem_maximalIndepSets_iff hb).1 hs
    refine ⟨τ, fun d ↦ ?_, rfl⟩
    split_ifs with hd
    · have := hτ d
      revert this
      generalize τ d = t
      revert t
      decide
    · exact Finset.mem_singleton.2 ((poles_subset_poles_iff hb).1 hσ d hd).symm
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(poles_mem_maximalIndepSets_iff hb).2 fun d ↦ ?_,
      (poles_subset_poles_iff hb).2 fun d hd ↦ ?_⟩
    · have := hτ d
      split_ifs at this with hd
      · revert this
        generalize τ d = t
        revert t
        decide
      · exact Finset.mem_singleton.1 this ▸ hd
    · have := hτ d
      simp only [hd, ↓reduceIte] at this
      exact (Finset.mem_singleton.1 this).symm

/-- The personae with every property a sign vector points to number two to the power of its
zeros. -/
theorem card_filter_poles_subset (σ : D → SignType) :
    ((dimensionalIncompatibility dim).maximalIndepSets.filter (poles dim pol σ ⊆ ·)).card =
      2 ^ (Finset.univ.filter (σ · = 0)).card := by
  rw [filter_poles_subset_eq hb, Finset.card_image_of_injective _ (poles_injective hb),
    Fintype.card_piFinset]
  have h (d : D) : (if σ d = 0 then ({1, -1} : Finset SignType) else {σ d}).card =
      if σ d = 0 then 2 else 1 := by
    split_ifs <;> rfl
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem card_maximalIndepSets : (dimensionalIncompatibility dim).maximalIndepSets.card =
    2 ^ Fintype.card D := by
  have h := card_filter_poles_subset hb 0
  have h₀ : poles dim pol 0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun p hp ↦ pol_ne_zero hb p (mem_poles.1 hp).symm
  simp only [h₀, Finset.empty_subset, Pi.zero_apply, Finset.filter_true, Finset.card_univ] at h
  exact h

/-- The personae sharing a property with a sign vector number two to the power of the dimensions
less two to the power of its zeros. -/
theorem card_filter_not_disjoint_poles (σ : D → SignType) :
    ((dimensionalIncompatibility dim).maximalIndepSets.filter
        (¬Disjoint (poles dim pol σ) ·)).card =
      2 ^ Fintype.card D - 2 ^ (Finset.univ.filter (σ · = 0)).card := by
  have h : (dimensionalIncompatibility dim).maximalIndepSets.filter (¬Disjoint (poles dim pol σ) ·)
      = (dimensionalIncompatibility dim).maximalIndepSets.filter (¬poles dim pol (-σ) ⊆ ·) := by
    refine Finset.filter_congr fun s hs ↦ not_congr ?_
    obtain ⟨τ, rfl⟩ := exists_poles_eq hb ((SimpleGraph.mem_maximalIndepSets _).1 hs).prop
    have hτ := (poles_mem_maximalIndepSets_iff hb).1 hs
    rw [disjoint_poles_iff hb, poles_subset_poles_iff hb]
    refine forall_congr' fun d ↦ ?_
    have := hτ d
    rw [Pi.neg_apply]
    revert this
    generalize σ d = s
    generalize τ d = t
    revert s t
    decide
  have hz : (Finset.univ.filter ((-σ) · = 0)) = Finset.univ.filter (σ · = 0) :=
    Finset.filter_congr fun d _ ↦ by rw [Pi.neg_apply, SignType.neg_eq_zero_iff]
  rw [h, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    card_filter_poles_subset hb, hz, card_maximalIndepSets hb]

end Card

end Bipolar

/-- The dimensions of social evaluation are competence and warmth, and anti-solidarity, the
factor on which pedantic and uptight load apart from the warmth scales. -/
inductive Dimension where
  | competence
  | warmth
  | antiSolidarity
  deriving DecidableEq

instance : Fintype Dimension :=
  ⟨{.competence, .warmth, .antiSolidarity}, fun d ↦ by cases d <;> simp⟩

/-- A pole is one end of a dimension of social evaluation. -/
inductive Pole where
  | competent
  | incompetent
  | warm
  | cold
  | solidary
  | antiSolidary
  deriving DecidableEq

instance : Fintype Pole :=
  ⟨{.competent, .incompetent, .warm, .cold, .solidary, .antiSolidary}, fun p ↦ by cases p <;> simp⟩

/-- The dimension a pole is an end of. -/
def Pole.dimension : Pole → Dimension
  | .competent | .incompetent => .competence
  | .warm | .cold => .warmth
  | .solidary | .antiSolidary => .antiSolidarity

/-- The polarity of a pole is positive at the end its dimension is named for, competent, warm
and antisolidary, and negative at the other. -/
def Pole.polarity : Pole → SignType
  | .competent | .warm | .antiSolidary => 1
  | .incompetent | .cold | .solidary => -1

/-- The other end of a pole's dimension. -/
def Pole.opposite : Pole → Pole
  | .competent => .incompetent
  | .incompetent => .competent
  | .warm => .cold
  | .cold => .warm
  | .solidary => .antiSolidary
  | .antiSolidary => .solidary

@[simp] theorem Pole.opposite_opposite (p : Pole) : p.opposite.opposite = p := by cases p <;> rfl

@[simp] theorem Pole.dimension_opposite (p : Pole) : p.opposite.dimension = p.dimension := by
  cases p <;> rfl

@[simp] theorem Pole.polarity_opposite (p : Pole) : p.opposite.polarity = -p.polarity := by
  cases p <;> rfl

/-- `Pole.opposite` as an involutive permutation. -/
def Pole.oppositeEquiv : Equiv.Perm Pole := Function.Involutive.toPerm _ Pole.opposite_opposite

@[simp] theorem Pole.oppositeEquiv_apply (p : Pole) : Pole.oppositeEquiv p = p.opposite := rfl

@[simp] theorem Pole.oppositeEquiv_symm : Pole.oppositeEquiv.symm = Pole.oppositeEquiv := rfl

/-- Two poles are incompatible when one is opposite the other. -/
theorem Pole.incompatible_adj_iff {p q : Pole} :
    (dimensionalIncompatibility Pole.dimension).Adj p q ↔ q = p.opposite := by
  revert p q; decide

/-- A pole is a dimension with a nonzero sign. -/
theorem Pole.bijOn :
    Set.BijOn (fun p : Pole ↦ (p.dimension, p.polarity)) Set.univ {x | x.2 ≠ 0} := by
  refine ⟨fun p _ ↦ by cases p <;> decide, fun p _ q _ h ↦ ?_, fun x hx ↦ ?_⟩
  · revert h; revert p q; decide
  · obtain ⟨d, s⟩ := x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and] at hx ⊢
    revert hx; revert d s; decide

end SocialMeaning
