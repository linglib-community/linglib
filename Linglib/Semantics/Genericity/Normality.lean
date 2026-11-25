module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Quantifier.Basic

/-!
# Normality and the generic operator

A *normality* on a type `X` of cases is a function `normal : Set X → Set X` with
`normal R ⊆ R`: it selects, from each set `R` of cases, the normal ones. The generic operator GEN
of characterizing sentences such as *a cat has a tail* relates a restrictor to a matrix, and over
a normality `N` we define it as the determiner `N.gen R S ↔ N.normal R ⊆ S`: the matrix holds of
every normal case of the restrictor.

Normalities are ordered pointwise. The greatest one is the identity, and its GEN is *every*
(`Normality.gen_top`); fewer normal cases make more generics true (`Normality.gen_anti`). Since
normal cases are cases of the restrictor, GEN is conservative (`Normality.conservative_gen`), and
two generics with one restrictor whose matrices are disjoint on it leave the restrictor no normal
case (`Normality.normal_eq_empty_of_disjoint`).

Normalities compose (`Normality.comp`), and two of them generate the ones in use.
`Normality.restrict B` selects the cases in a fixed set, `R ↦ B ∩ R`, and these are the
normalities that are monotone and satisfy the contraction condition
`normal R ∩ R' ⊆ normal R'` for `R' ⊆ R` (`Normality.exists_eq_restrict_iff`).
`Normality.minimals p` selects the minimal cases under a preorder `p`, and these are, for
well-founded total `p`, the normalities whose GEN is a rational consequence relation that
preserves consistency (`Normality.exists_eq_minimals_iff`), equivalently those with a normal case
in every nonempty set and `normal (R ∩ B) = normal R ∩ B` whenever the right-hand side is nonempty
(`Normality.exists_eq_minimals_iff_forall_inter`). The minimal cases within a fixed set
are the composite, whose GEN is `Conditional.orderingImp` (`Normality.gen_minimals_comp_restrict`).
Without well-foundedness the variably strict conditional is the GEN of no normality
(`Normality.not_exists_gen_iff_variablyStrictImp`).

## Implementation notes

* A normality carries no index. A GEN evaluated at worlds, times or contexts is a family
  `N : I → Normality X`, and the proposition it expresses is `{i | (N i).gen R S}`, which is
  `Conditional.ofDomain fun i ↦ (N i).normal`. The domain of `Conditional.ofDomain` is not
  required to lie in the antecedent, so it is not stated over normalities.
* A normality is the selection function of [asher-morreau-1995] and [pelletier-asher-1997] at a
  world under Facticity (`Normality.normal_subset`), the one constraint they place on every
  frame. It is also the typicality operator of the prototype analysis in [krifka-etal-1995],
  applied to the restrictor. No further law is assumed, and `Normality.normal` is in general not
  monotone: the normal cases of a restrictor need not be normal cases of a weaker one.
  [pelletier-asher-1997] state cut, cautious monotonicity and rational monotonicity as the
  principles of a rational conditional and do not impose them; by
  `Normality.exists_eq_minimals_iff` these, with consistency preservation, are what selecting the
  minimal cases of a well-founded total preorder adds.
* The conditions on choice functions are those of [arrow-1959]: the contraction condition of
  `Normality.exists_eq_restrict_iff` is his (C3), and the condition of
  `Normality.exists_eq_minimals_iff_forall_inter` his (C4), from which he derives the ordering
  on finite sets. [eckardt-2000] takes a normality on properties, sets of pairs of a world and
  an individual, with the same two conditions as axioms.
* A GEN that depends on the matrix as well as the restrictor is a family of normalities:
  [nickel-2009] quantifies existentially over the ways of being normal in the respect the matrix
  fixes.
* GEN is a `Quantifier.Det`, so that it is compared with *every*, *most* and the probabilistic
  generic of `Studies/Cohen1999` as one determiner among others.

## TODO

* The homogeneity presupposition of GEN of `Studies/Magri2009`, beside
  `Conditional.homogeneityCounterfactual`.

## References

* [krifka-etal-1995]
* [asher-morreau-1995]
* [pelletier-asher-1997]
* [arrow-1959]
* [eckardt-2000]
* [nickel-2009]
* [kraus-lehmann-magidor-1990]
* [lehmann-magidor-1992]
-/

@[expose] public section

namespace Genericity

open Conditional Quantifier Set

/-- A normality on cases `X` selects from each set of cases its normal cases. -/
@[ext]
structure Normality (X : Type*) where
  /-- The normal cases of a set of cases. -/
  normal : Set X → Set X
  /-- The normal cases of a set are among its cases. -/
  normal_subset (R : Set X) : normal R ⊆ R

namespace Normality

variable {X : Type*} (N : Normality X) {N₁ N₂ : Normality X} {B R R' S S' : Set X}

/-- GEN with restrictor `R` and matrix `S` holds when every normal case of `R` is a case of
`S`. -/
def gen : Det X := fun R S ↦ N.normal R ⊆ S

@[simp]
theorem gen_iff : N.gen R S ↔ N.normal R ⊆ S := Iff.rfl

theorem conservative_gen : N.gen.Conservative :=
  fun R S ↦ by simp [N.normal_subset R]

theorem scopeMonotone_gen : N.gen.ScopeMonotone :=
  fun _ _ _ h hS ↦ hS.trans h

/-- The universal generalization entails the generic one. -/
theorem gen_of_subset (h : R ⊆ S) : N.gen R S :=
  (N.normal_subset R).trans h

theorem disjoint_normal_of_disjoint (hS : N.gen R S) (hS' : N.gen R' S') (h : Disjoint S S') :
    Disjoint (N.normal R) (N.normal R') :=
  h.mono hS hS'

/-- Two generics with one restrictor whose matrices are disjoint on it leave the restrictor no
normal case. -/
theorem normal_eq_empty_of_disjoint (hS : N.gen R S) (hS' : N.gen R S')
    (h : Disjoint (R ∩ S) S') : N.normal R = ∅ :=
  disjoint_self.1 (h.mono (subset_inter (N.normal_subset R) hS) hS')

/-! ### The order on normalities -/

/-- Normalities are ordered pointwise by inclusion of the normal cases. -/
instance : PartialOrder (Normality X) := .lift normal fun _ _ ↦ Normality.ext

theorem le_def : N₁ ≤ N₂ ↔ ∀ R, N₁.normal R ⊆ N₂.normal R := Iff.rfl

/-- The greatest normality counts every case as normal. -/
instance : OrderTop (Normality X) where
  top := ⟨id, fun _ ↦ subset_rfl⟩
  le_top N := N.normal_subset

@[simp]
theorem normal_top : (⊤ : Normality X).normal R = R := rfl

theorem gen_top : (⊤ : Normality X).gen = Det.every := rfl

/-- Fewer normal cases make more generics true. -/
theorem gen_anti (h : N₁ ≤ N₂) (hS : N₂.gen R S) : N₁.gen R S :=
  (h R).trans hS

/-! ### Composition -/

/-- The composite of two normalities selects the normal cases of the first among the normal
cases of the second. -/
@[simps]
def comp (N M : Normality X) : Normality X :=
  ⟨fun R ↦ N.normal (M.normal R), fun R ↦ (N.normal_subset _).trans (M.normal_subset R)⟩

@[simp]
theorem top_comp : (⊤ : Normality X).comp N = N := rfl

@[simp]
theorem comp_top : N.comp ⊤ = N := rfl

theorem comp_assoc (N M L : Normality X) : (N.comp M).comp L = N.comp (M.comp L) := rfl

theorem comp_le_right (N M : Normality X) : N.comp M ≤ M :=
  fun R ↦ N.normal_subset (M.normal R)

/-! ### Normal cases in a fixed set -/

/-- The normality of a fixed set of cases `B`: the normal cases of `R` are its cases in `B`. -/
@[simps]
def restrict (B : Set X) : Normality X :=
  ⟨fun R ↦ B ∩ R, fun _ ↦ inter_subset_right⟩

@[simp]
theorem restrict_univ : restrict (univ : Set X) = ⊤ :=
  Normality.ext <| funext fun _ ↦ univ_inter _

theorem monotone_normal_restrict (B : Set X) : Monotone (restrict B).normal :=
  fun _ _ h ↦ inter_subset_inter_right _ h

/-- A normality selects the cases in a fixed set exactly when it is monotone and a normal case of
a set is a normal case of every subset it belongs to. -/
theorem exists_eq_restrict_iff :
    (∃ B, N = restrict B) ↔
      Monotone N.normal ∧ ∀ ⦃R R'⦄, R' ⊆ R → N.normal R ∩ R' ⊆ N.normal R' := by
  refine ⟨?_, fun ⟨hm, hc⟩ ↦ ⟨N.normal univ, Normality.ext <| funext fun R ↦ ?_⟩⟩
  · rintro ⟨B, rfl⟩
    exact ⟨monotone_normal_restrict B, fun _ _ _ _ hx ↦ ⟨hx.1.1, hx.2⟩⟩
  · exact (subset_inter (hm (subset_univ R)) (N.normal_subset R)).antisymm (hc (subset_univ R))

/-! ### Normal cases under a preorder -/

/-- The normality of a preorder on the cases: the normal cases of a set are its minimal ones. -/
@[simps]
def minimals (p : Preorder X) : Normality X :=
  ⟨p.minimals, p.minimals_subset⟩

/-- A normality selects the minimal cases of a well-founded total preorder exactly when its GEN is
rational and no nonempty restrictor has the empty matrix. -/
theorem exists_eq_minimals_iff :
    (∃ p : Preorder X, Std.Total p.le ∧ WellFounded p.lt ∧ N = minimals p) ↔
      Nonmonotonic.IsRational N.gen ∧ ∀ R, N.gen R ∅ → R = ∅ := by
  refine Iff.trans ?_ (Nonmonotonic.exists_minimals_eq_iff (C := N.normal))
  exact exists_congr fun p ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h ↦ h ▸ rfl, fun h ↦ Normality.ext h.symm⟩

/-- A normality selects the minimal cases of a well-founded total preorder exactly when every
nonempty set has a normal case and the normal cases of `R` in `B`, where there are any, are the
normal cases of `R ∩ B`. -/
theorem exists_eq_minimals_iff_forall_inter :
    (∃ p : Preorder X, Std.Total p.le ∧ WellFounded p.lt ∧ N = minimals p) ↔
      (∀ R : Set X, R.Nonempty → (N.normal R).Nonempty) ∧
        ∀ R B : Set X, (N.normal R ∩ B).Nonempty → N.normal (R ∩ B) = N.normal R ∩ B := by
  rw [exists_eq_minimals_iff]
  refine ⟨fun ⟨h, hc⟩ ↦ ⟨fun R hR ↦ nonempty_iff_ne_empty.2 fun he ↦ hR.ne_empty (hc R he.subset),
    fun _ _ ↦ h.inter_eq⟩, fun ⟨hne, hi⟩ ↦ ⟨?_, fun R hR ↦ not_nonempty_iff_eq_empty.1 fun hR' ↦
      (hne R hR').ne_empty (subset_empty_iff.1 hR)⟩⟩
  refine ⟨⟨N.normal_subset, fun h h' ↦ h.trans h', fun h h' ↦ subset_inter h h', ?_, ?_⟩, ?_⟩
  · intro φ ψ χ h h' x hx
    rcases N.normal_subset _ hx with hφ | hψ
    · exact h (union_inter_cancel_left (s := φ) (t := ψ) ▸ (hi _ φ ⟨x, hx, hφ⟩).symm ▸ ⟨hx, hφ⟩)
    · exact h' (union_inter_cancel_right (s := φ) (t := ψ) ▸ (hi _ ψ ⟨x, hx, hψ⟩).symm ▸ ⟨hx, hψ⟩)
  · intro φ ψ χ h h'
    rcases (N.normal φ ∩ ψ).eq_empty_or_nonempty with he | hn
    · have hφ : φ = ∅ := not_nonempty_iff_eq_empty.1 fun hφ ↦
        (hne φ hφ).ne_empty ((inter_eq_left.2 h).symm.trans he)
      exact fun x hx ↦ absurd (N.normal_subset _ hx).1 (hφ ▸ notMem_empty x)
    · exact (hi φ ψ hn).subset.trans (inter_subset_left.trans h')
  · intro φ ψ χ h h'
    obtain ⟨x, hx, hxψ⟩ := not_subset.1 h'
    exact (hi φ ψ ⟨x, hx, not_not.1 hxψ⟩).subset.trans (inter_subset_left.trans h)

/-- GEN over the minimal cases of a preorder within a set of accessible cases is the conditional
over the best accessible cases. -/
theorem gen_minimals_comp_restrict {I : Type*} (access : I → Set X) (ord : I → Preorder X) :
    {i | ((minimals (ord i)).comp (restrict (access i))).gen R S} = orderingImp access ord R S :=
  rfl

private theorem notMem_variablyStrictImp_empty :
    () ∉ variablyStrictImp (fun _ ↦ univ) (fun _ ↦ (inferInstance : Preorder ℤ)) univ ∅ :=
  fun h ↦ by
    rw [mem_variablyStrictImp, Filter.mem_atBotOn] at h
    obtain ⟨v, hv, -, hvt⟩ := h 0 ⟨trivial, trivial⟩
    exact hvt v hv le_rfl

private theorem mem_variablyStrictImp_Iic (n : ℤ) :
    () ∈ variablyStrictImp (fun _ ↦ univ) (fun _ ↦ (inferInstance : Preorder ℤ)) univ (Iic n) := by
  rw [mem_variablyStrictImp, Filter.mem_atBotOn]
  exact fun u _ ↦ ⟨min u n, ⟨trivial, trivial⟩, min_le_left u n,
    fun _ _ hw ↦ hw.trans (min_le_right u n)⟩

/-- Without the Limit Assumption the variably strict conditional is the GEN of no normality: on the
integers it holds of every down-ray under the trivial restrictor and not of the empty matrix, so
the normal cases would lie in every down-ray and be none. -/
theorem not_exists_gen_iff_variablyStrictImp :
    ¬ ∃ N : Normality ℤ, ∀ R S,
      N.gen R S ↔ () ∈ variablyStrictImp (fun _ ↦ univ) (fun _ ↦ inferInstance) R S := by
  rintro ⟨N, hN⟩
  refine notMem_variablyStrictImp_empty ((hN _ _).1 fun x hx ↦ ?_)
  exact absurd (mem_Iic.1 ((hN _ _).2 (mem_variablyStrictImp_Iic (x - 1)) hx)) (by omega)

end Normality

end Genericity
