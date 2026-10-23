module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Data.Fin.VecNotation

/-!
# Heim (2001): Degree Operators and Scope

Heim asks how far a degree phrase moves at LF, given the max semantics of the comparative, on
which *-er than t* says that the greatest degree of its
argument exceeds *t*, `Degree.MaxIn (Ioi t)`, and a DegP scopes under a quantifier or over it,
`Degree.LowScope` and `Degree.HighScope`. Over a monotone increasing quantifier on a finite
domain the two scopes coincide and under a monotone decreasing one the maximum is undefined,
so the *exactly*-differential and *less*, whose intervals are not upper sets, are the
diagnostic cases: under *every girl* their high scope is a weaker reading the sentence lacks,
which Kennedy's generalization, the Heim–Kennedy constraint `Degree.IsHeimKennedy`,
excludes, while over the intensional verbs both scopes are attested. For the neg-raising verbs
the maximum redefined as the greatest lower bound of the false degrees collapses the scopes
(`negRaising_collapse`), and *-est*, using its complement twice, is the absolute superlative
(`est_iff_absoluteSuperlative`).

## Implementation notes

* Quantifiers over individuals and over worlds are the same `Quantifier.NP`, so
  the intensional cases of Sections 2.1 and 2.3 are the theorems at a type of worlds.
* A high-scope truth condition carries the definedness presupposition of the maximum as an
  existence conjunct; the paper's undefined maxima are the negations of those conjuncts.
* The de re and de dicto than-clauses of Section 2.4 are von Stechow's diagnosis and
  are formalized in `Studies/VonStechow1984.lean`; the examples are typed in
  `Data/Examples/Heim2001.json`.

## References

* [heim-2001]
* [von-stechow-1984]
* [heim-1999]
-/

@[expose] public section

namespace Heim2001

open Degree Quantifier Quantifier.GQ Set

variable {Entity W D : Type*} [LinearOrder D]

/-! ### Monotone increasing quantifiers -/

/-- On a finite domain the two scopes of an upper-interval DegP under *every girl* coincide,
covering (10), (13a) and (16) (Section 2.1). -/
theorem forall_collapse [Finite Entity] {girl : Entity → Prop} (hg : ∃ x, girl x)
    (μ : Entity → D) {U : Set D} (hU : IsUpperSet U) :
    HighScope (MaxIn U) (every girl) (Iic ∘ μ) ↔ LowScope (MaxIn U) (every girl) (Iic ∘ μ) :=
  highScope_maxIn_iff_lowScope (monotone_every girl) (fun h ↦ let ⟨x, hx⟩ := hg; h x hx) hU

/-- Likewise under *some girl*, (12), (13b), and the possibility operator (15b). -/
theorem exists_collapse [Finite Entity] (girl : Entity → Prop) (μ : Entity → D) {U : Set D}
    (hU : IsUpperSet U) :
    HighScope (MaxIn U) (GQ.some girl) (Iic ∘ μ) ↔ LowScope (MaxIn U) (GQ.some girl) (Iic ∘ μ) :=
  highScope_maxIn_iff_lowScope (monotone_some girl) (fun ⟨_, _, h⟩ ↦ h) hU

/-! ### Monotone decreasing and non-monotone operators -/

/-- The degrees to which Mary is not tall have no maximum (17c). -/
theorem negation_high_undefined [NoMaxOrder D] (μ : Entity → D) (a : Entity) :
    ¬ ∃ m, IsGreatest (scopeDegrees (fun S ↦ ¬ S a) (Iic ∘ μ)) m :=
  not_isGreatest_scopeDegrees (Q := fun S ↦ ¬ S a) (fun _ _ h hT hS ↦ hT (h a hS))
    (fun _ ↦ isLowerSet_Iic _)

/-- The degrees to which at most two girls are tall have no maximum (18c). -/
theorem atMost_high_undefined [Fintype Entity] [NoMaxOrder D] (girl : Entity → Prop)
    (μ : Entity → D) : ¬ ∃ m, IsGreatest (scopeDegrees (atMost 2 girl) (Iic ∘ μ)) m :=
  not_isGreatest_scopeDegrees (antitone_atMost (α := Entity) 2 girl) (fun _ ↦ isLowerSet_Iic _)

/-- The high scope (20c) of *exactly two girls* means *at least two girls are taller than 5 feet*
(20). -/
theorem exactly_high_atLeast [Fintype Entity] {girl : Entity → Prop} {μ : Entity → D} {m : D}
    (h : IsGreatest (scopeDegrees (exactly 2 girl) (Iic ∘ μ)) m) :
    IsGreatest (scopeDegrees (atLeast 2 girl) (Iic ∘ μ)) m := by
  rw [exactly_eq_atLeast_inf_atMost] at h
  exact isGreatest_scopeDegrees_of_inf (antitone_atMost 2 girl) (fun _ ↦ isLowerSet_Iic _) h

/-! ### Exactly-differentials and less -/

/-- Under *every girl* the low scope entails the high scope, so (22c), (24c), (28c) and (30c) are
weaker than (22b), (24b), (28b) and (30b). -/
theorem forall_high_of_low [Finite Entity] {girl : Entity → Prop} (hg : ∃ x, girl x)
    (μ : Entity → D) (U : Set D) :
    LowScope (MaxIn U) (every girl) (Iic ∘ μ) → HighScope (MaxIn U) (every girl) (Iic ∘ μ) :=
  have : Nonempty {x // girl x} := let ⟨x, hx⟩ := hg; ⟨⟨x, hx⟩⟩
  let ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min fun x : {x // girl x} ↦ μ x.1
  highScope_every_of_lowScope ⟨x₀, hx₀, fun y hy ↦ hmin ⟨y, hy⟩⟩

/-- Under *some girl* the high scope entails the low scope, so (21c), (29c) and (31c) are stronger
than (21b), (29b) and (31b). -/
theorem exists_low_of_high (girl : Entity → Prop) (μ : Entity → D) (U : Set D) :
    HighScope (MaxIn U) (GQ.some girl) (Iic ∘ μ) → LowScope (MaxIn U) (GQ.some girl) (Iic ∘ μ) :=
  lowScope_some_of_highScope

private theorem scopeDegrees_heights :
    scopeDegrees (every fun _ : Fin 2 ↦ True) (Iic ∘ ![49, 50]) = Iic 49 := by
  ext d
  simp [scopeDegrees, every, Fin.forall_fin_two]
  omega

/-- When the shortest girl is exactly 4'1'' and another is taller, the high scope is true and the
low false, so (22c) is no reading of (22). -/
theorem exactly_high_not_low :
    HighScope (MaxIn {49}) (every fun _ : Fin 2 ↦ True) (Iic ∘ ![49, 50]) ∧
      ¬ LowScope (MaxIn {49}) (every fun _ : Fin 2 ↦ True) (Iic ∘ ![49, 50]) :=
  ⟨⟨49, rfl, scopeDegrees_heights ▸ isGreatest_Iic⟩,
    fun h ↦ by simpa using lowScope_maxIn.1 h 1 trivial⟩

/-- The high scope of *every girl is less tall than that* is true where the sentence is false (24).
-/
theorem less_high_not_low :
    HighScope (MaxIn (Iio 50)) (every fun _ : Fin 2 ↦ True) (Iic ∘ ![49, 50]) ∧
      ¬ LowScope (MaxIn (Iio 50)) (every fun _ : Fin 2 ↦ True) (Iic ∘ ![49, 50]) :=
  ⟨⟨49, by decide, scopeDegrees_heights ▸ isGreatest_Iic⟩,
    fun h ↦ by simpa using lowScope_maxIn.1 h 1 trivial⟩

/-! ### Intensional verbs -/

/-- The high scope of *required to be less long than t* means *not required to be as long as t*
(30c). -/
theorem required_less [Finite W] {Acc : Set W} (hAcc : Acc.Nonempty) (ℓ : W → D) (t : D) :
    HighScope (MaxIn (Iio t)) (every (· ∈ Acc)) (Iic ∘ ℓ) ↔ ¬ every (· ∈ Acc) fun w ↦ t ≤ ℓ w := by
  have : Nonempty W := hAcc.to_type
  obtain ⟨w₀, hw₀⟩ := Finite.exists_min ℓ
  exact highScope_maxIn_Iio_iff (monotone_every _) (fun h ↦ let ⟨w, hw⟩ := hAcc; h w hw)
    ⟨ℓ w₀, fun v _ ↦ hw₀ v⟩

/-- The high scope of *allowed to be less long than t* means *not allowed to be as long as t* (31c).
-/
theorem allowed_less [Finite W] {Acc : Set W} (hAcc : Acc.Nonempty) (ℓ : W → D) (t : D) :
    HighScope (MaxIn (Iio t)) (GQ.some (· ∈ Acc)) (Iic ∘ ℓ) ↔ ¬ GQ.some (· ∈ Acc) fun w ↦ t ≤ ℓ w :=
  highScope_maxIn_Iio_iff (monotone_some _) (fun ⟨_, _, h⟩ ↦ h)
    (let ⟨w, hw⟩ := hAcc; ⟨ℓ w, w, hw, le_rfl⟩)

/-- With the maximum of (35), the DegP over *want* in *I want the paper to be less long than t*
yields the low-scope reading (36a). -/
theorem negRaising_collapse [Finite W] [DenselyOrdered D] {Des : Set W} (hDes : Des.Nonempty)
    (ℓ : W → D) (t : D) :
    (∃ m ∈ Iio t, IsGLB (scopeDegrees (no (· ∈ Des)) (Iic ∘ ℓ)) m) ↔
      LowScope (MaxIn (Iio t)) (every (· ∈ Des)) (Iic ∘ ℓ) := by
  have hex : ∃ m, IsGreatest (scopeDegrees (GQ.some (· ∈ Des)) (Iic ∘ ℓ)) m :=
    let ⟨w, hw⟩ := exists_isGreatest_scopeDegrees (monotone_some _) (fun ⟨_, _, h⟩ ↦ h)
      (let ⟨w, hw⟩ := hDes; ⟨ℓ w, w, hw, le_rfl⟩)
    ⟨_, hw⟩
  rw [scopeDegrees_no, lowScope_maxIn]
  refine (exists_congr fun m ↦ and_congr_right fun _ ↦
    isGLB_compl_scopeDegrees_iff (monotone_some _) (fun _ ↦ isLowerSet_Iic _) hex).trans
    ((allowed_less hDes ℓ t).trans ?_)
  exact not_exists.trans (forall_congr' fun _ ↦ not_and.trans (imp_congr_right fun _ ↦ not_le))

/-! ### The superlative -/

/-- The entry for *-est* (59a), `λx. max{d : R(x, d)} > max{d : ∃y ≠ x. R(y, d)}`, over a
monotone adjective and a comparison class `C` is the max-quantified comparative of `x` against
the other members. -/
def est (μ : Entity → D) (C : Set Entity) (x : Entity) : Prop :=
  MaxComparative .gt (· = x) (fun y ↦ y ∈ C ∧ y ≠ x) μ

/-- Over a comparison class with someone else in it, *-est* is the absolute superlative (59). -/
theorem est_iff_absoluteSuperlative [Finite Entity] {μ : Entity → D} {C : Set Entity}
    {x : Entity} (hx : x ∈ C) (hC : ∃ y ∈ C, y ≠ x) : est μ C x ↔ AbsoluteSuperlative μ C x := by
  have h := highScope_maxIn_Iio_iff (μ := μ) (t := μ x) (monotone_some fun y ↦ y ∈ C ∧ y ≠ x)
    (fun ⟨_, _, h⟩ ↦ h) (let ⟨y, hy, hyx⟩ := hC; ⟨μ y, y, ⟨hy, hyx⟩, le_rfl⟩)
  have hS (δ : D) : IsGreatest (scopeDegrees (GQ.some fun y ↦ y ∈ C ∧ y ≠ x) (Iic ∘ μ)) δ ↔
      IsGreatest (μ '' {y | y ∈ C ∧ y ≠ x}) δ := by
    rw [scopeDegrees_some_Iic, isGreatest_lowerClosure_iff]
  refine (⟨fun ⟨δ, hδ, _, rfl, hlt⟩ ↦ ⟨δ, hlt, (hS δ).2 hδ⟩,
    fun ⟨δ, hlt, hδ⟩ ↦ ⟨δ, (hS δ).1 hδ, x, rfl, hlt⟩⟩ :
    est μ C x ↔ HighScope (MaxIn (Iio (μ x))) (GQ.some fun y ↦ y ∈ C ∧ y ≠ x) (Iic ∘ μ)).trans
    (h.trans (Iff.trans ?_ (and_iff_right hx).symm))
  exact not_exists.trans (forall_congr' fun _ ↦ not_and.trans (and_imp.trans
    (imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ not_le)))

end Heim2001
