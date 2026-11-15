module

public import Linglib.Semantics.Aggregation.Rules
public import Linglib.Semantics.Degree.Measurement
public import Linglib.Semantics.Degree.UniversalScale

/-!
# van Rooij (2011): Measurement and Interadjective Comparisons

Van Rooij measures individual–adjective pairs on one scale, so that *x is P-er than y is Q* compares
two values of a single measure, and asks which changes of scale such a statement survives. The
changes that preserve every comparison of pairs are [exactly the strictly increasing maps applied
to all adjectives alike](##forall_comparative_comp_iff), a co-ordinal scale; [a separate
origin for each adjective](##not_comparative_cardinalUnit) already undoes the comparison. A
differential across adjectives needs a common unit and origin, a co-interval scale, on which a
factor across adjectives [survives only as the factor $1$](##factor_cardinalFull_iff). Bale's
universal degrees normalize each adjective's ranking and so [make ratios across adjectives
meaningful](##factor_universal_ordinal) from merely ordinal measures, which van Rooij counts
against them. On a shared scale the dimensions of a multidimensional adjective combine into a weak
order, by their minimum on a co-ordinal scale and [by a weighted sum only on a co-interval
one](##utilitarian_coInterval).

## Implementation notes

* A measure on individual–adjective pairs is an `Aggregation.Profile` with adjectives as its
  individuals, following the paper's analogy with interpersonal comparisons of utility. The
  co-ordinal, co-interval and co-ratio scales are Sen's comparability classes `ordinalLevel`,
  `cardinalFull` and `ratioFull`, separate scales per adjective are `ordinal`, and a common unit
  with an origin per adjective is `cardinalUnit`.
* Measures are real-valued, as in the paper; universal degrees are rational. They are Bale's
  `universalDegree`, the share of classes at or below an individual, where the paper's rank counts
  the classes strictly below.

## TODO

* Section 2's choice structures, after van Benthem, and section 4.3's constructions of a
  co-ordinal scale from a choice function on pairs and from Klein's modifiers.
* Section 5's ranking by the highest dimension and by a weighted product, and the derivation of
  the minimum from invariance and the absence of a dictating dimension.
* The paper's example sentences as `Data/Examples` rows.

## References

* [van-rooij-2011]
* [bale-2008]
* [sassoon-2010]
* [sen-1970]
-/

@[expose] public section

namespace VanRooij2011

open Aggregation Finset Function

variable {X Ad : Type*}

/-! ### Comparisons across adjectives -/

/-- *x is P-er than y is Q* holds when the pair of `x` and P measures more than the pair of `y`
and Q. -/
def comparative (x : X) (P : Ad) (y : X) (Q : Ad) (v : Profile Ad X ℝ) : Prop :=
  v y Q < v x P

/-- *x is d-much P-er than y is Q*. -/
def differential (x : X) (P : Ad) (y : X) (Q : Ad) (d : ℝ) (v : Profile Ad X ℝ) : Prop :=
  DifferentialComparative (uncurry v) (x, P) (y, Q) d

/-- *x is n times as P as y is Q*. -/
def factor (x : X) (P : Ad) (y : X) (Q : Ad) (n : ℝ) (v : Profile Ad X ℝ) : Prop :=
  FactorEquative (uncurry v) (x, P) (y, Q) n

/-- *x is P-er than y by more than z is Q-er than w*. -/
def differenceComparative (x y : X) (P : Ad) (z w : X) (Q : Ad) (v : Profile Ad X ℝ) : Prop :=
  v z Q - v w Q < v x P - v y P

section Sentences

variable (x y z w : X) (P Q : Ad)

theorem comparative_ordinalLevel : Invariant ordinalLevel (comparative x P y Q) :=
  (invariant_strictMono_lt (x, P) (y, Q)).uncurry

/-- A change of scale preserves every comparison of individual–adjective pairs exactly when it
applies one strictly increasing map to all adjectives, so the measure of pairs is unique up to the
transformations of a co-ordinal scale. -/
-- pp. 348–349
theorem forall_comparative_comp_iff [Nontrivial X] {g : (Ad → ℝ) → Ad → ℝ} :
    (∀ (v : Profile Ad X ℝ) x P y Q,
      comparative x P y Q (g ∘ v) ↔ comparative x P y Q v) ↔ g ∈ ordinalLevel := by
  refine ⟨fun h ↦ ?_, fun hg v x P y Q ↦ (comparative_ordinalLevel x y P Q g hg v).to_iff⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  classical
  have key (p q : Ad → ℝ) (P Q : Ad) : g q Q < g p P ↔ q Q < p P := by
    simpa [comparative, hxy.symm] using h (fun z ↦ if z = x then p else q) x P y Q
  have hconst (p : Ad → ℝ) (P P' : Ad) : g p P = g (fun _ ↦ p P) P' :=
    le_antisymm (not_lt.1 fun hlt ↦ lt_irrefl (p P) ((key p _ P P').1 hlt))
      (not_lt.1 fun hlt ↦ lt_irrefl (p P) ((key _ p P' P).1 hlt))
  rcases isEmpty_or_nonempty Ad with _ | ⟨⟨P₀⟩⟩
  · exact ⟨id, strictMono_id, Subsingleton.elim _ _⟩
  · exact ⟨fun t ↦ g (fun _ ↦ t) P₀, fun s t hst ↦ (key _ _ P₀ P₀).2 hst,
      funext₂ fun p P ↦ (hconst p P P₀).symm⟩

/-- A common unit with a separate origin for each adjective does not make a comparison across two
adjectives meaningful. -/
-- p. 349, note 17
theorem not_comparative_cardinalUnit (hPQ : P ≠ Q) :
    ¬ Invariant cardinalUnit (comparative x P y Q) := by
  intro h
  classical
  let v : Profile Ad X ℝ := fun _ i ↦ if i = P then 1 else 0
  let g : (Ad → ℝ) → Ad → ℝ := fun p i ↦ 1 * p i + if i = Q then 2 else 0
  have h₁ : comparative x P y Q v := by simp [comparative, v, hPQ.symm]
  have h₂ : ¬ comparative x P y Q (g ∘ v) := by
    norm_num [comparative, v, g, hPQ, hPQ.symm]
  exact h₂ (h g (mem_cardinalUnit.2 ⟨1, one_pos, _, rfl⟩) v ▸ h₁)

theorem not_comparative_ordinal (hPQ : P ≠ Q) : ¬ Invariant ordinal (comparative x P y Q) :=
  fun h ↦ not_comparative_cardinalUnit x y P Q hPQ (h.mono cardinalUnit_subset_ordinal)

-- p. 349: a co-interval scale makes "5 cm taller than Mary is wide" meaningful
theorem differential_cardinalFull {g : (Ad → ℝ) → Ad → ℝ} (hg : g ∈ cardinalFull) :
    ∃ a > 0, ∀ d (v : Profile Ad X ℝ),
      differential x P y Q (a * d) (g ∘ v) ↔ differential x P y Q d v := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨a, ha, h⟩ := exists_differentialComparative_comp_iff (E := X × Ad) hu
  exact ⟨a, ha, fun d v ↦ h (uncurry v) _ _ d⟩

-- p. 349: a co-ratio scale
theorem factor_ratioFull (n : ℝ) : Invariant ratioFull (factor x P y Q n) :=
  (invariant_similarity_factorEquative (x, P) (y, Q) n).uncurry

/-- On a co-interval scale *x is n times as P as y is Q* is meaningful only for the factor $1$,
since a common change of origin moves every other ratio. -/
theorem factor_cardinalFull_iff {n : ℝ} (hne : (x, P) ≠ (y, Q)) :
    Invariant cardinalFull (factor x P y Q n) ↔ n = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · classical
    have hyQ : ¬ (y = x ∧ Q = P) := fun ⟨h₁, h₂⟩ ↦ hne (by rw [h₁, h₂])
    let v : Profile Ad X ℝ := fun z i ↦ if z = x ∧ i = P then n else 1
    have h₁ : factor x P y Q n v := by simp [factor, FactorEquative, v, hyQ]
    have h₂ := (h _ ⟨fun t ↦ 1 * t + 1, ⟨1, one_pos, 1, fun _ ↦ rfl⟩, rfl⟩ v).mpr h₁
    simp only [factor, FactorEquative, uncurry_apply_pair, comp_apply, smul_eq_mul, v,
      and_self, ite_true, hyQ, ite_false] at h₂
    linarith
  · rintro rfl _ ⟨u, ⟨a, ha, b, hu⟩, rfl⟩ v
    simp [factor, FactorEquative, hu, ha.ne']

-- p. 349, note 17: each origin cancels within its own difference
theorem differenceComparative_cardinalUnit :
    Invariant cardinalUnit (differenceComparative x y P z w Q) := by
  rintro g hg v
  obtain ⟨a, ha, b, rfl⟩ := mem_cardinalUnit.1 hg
  simp only [differenceComparative, comp_apply]
  rw [show ∀ s t c : ℝ, a * s + c - (a * t + c) = a * (s - t) from fun _ _ _ ↦ by ring,
    show ∀ s t c : ℝ, a * s + c - (a * t + c) = a * (s - t) from fun _ _ _ ↦ by ring,
    mul_lt_mul_iff_of_pos_left ha]

end Sentences

/-! ### Bale's universal degrees -/

section Universal

/-- Bale's universal degrees of a profile on the comparison class `C`, adjective by adjective. -/
noncomputable def universal (v : Profile Ad X ℝ) (C : Finset X) : Profile Ad X ℚ :=
  fun x P ↦ universalDegree (v · P) C x

theorem universal_comp {g : (Ad → ℝ) → Ad → ℝ} (hg : g ∈ ordinal) (v : Profile Ad X ℝ)
    (C : Finset X) : universal (g ∘ v) C = universal v C := by
  obtain ⟨f, hf, rfl⟩ := mem_ordinal.1 hg
  exact funext₂ fun x P ↦ congrFun
    (universalDegree_comp (OrderEmbedding.ofStrictMono (f P) (hf P)) (v · P) C) x

theorem universal_ordinal {β : Type*} (C : Finset X) (a : Profile Ad X ℚ → β) :
    Invariant ordinal fun v : Profile Ad X ℝ ↦ a (universal v C) :=
  fun _ hg v ↦ congrArg a (universal_comp hg v C)

/-- Read through universal degrees, *x is n times as P as y is Q* survives a separate strictly
increasing map per adjective, so a ratio across adjectives becomes meaningful although each
adjective's measure is only ordinal. -/
-- p. 346
theorem factor_universal_ordinal (C : Finset X) (x y : X) (P Q : Ad) (n : ℚ) :
    Invariant ordinal fun v : Profile Ad X ℝ ↦
      FactorEquative (uncurry (universal v C)) (x, P) (y, Q) n :=
  universal_ordinal C fun w ↦ FactorEquative (uncurry w) (x, P) (y, Q) n

-- p. 346, note 15: a relative measure is not a linear transformation of the direct measure
theorem universal_not_affine :
    ¬ ∃ a b : ℚ, ∀ i, universalDegree ![(1 : ℕ), 2, 4] univ i = a * ![(1 : ℚ), 2, 4] i + b := by
  rintro ⟨a, b, h⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 0 = 1 / 3 by decide +kernel] at h₀
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 1 = 2 / 3 by decide +kernel] at h₁
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 2 = 1 by decide +kernel] at h₂
  simp at h₀ h₁ h₂
  linarith

end Universal

/-! ### Negative adjectives -/

-- p. 343: shortness $-6$ is three times shortness $-2$, and five times it once the zero moves
theorem three_times_as_short :
    FactorEquative ![(-6 : ℝ), -2] 0 1 3 ∧ FactorEquative (fun i ↦ ![(-6 : ℝ), -2] i + 1) 0 1 5 :=
  ⟨by norm_num [FactorEquative], by norm_num [FactorEquative]⟩

/-! ### Multidimensional adjectives -/

section Multidimensional

variable [Fintype Ad]

-- p. 355: the lowest dimension ranks individuals in a weak order on a co-ordinal scale, with no
-- dimension dictating it and none privileged
theorem maximin_coOrdinal [Nontrivial Ad] [Nontrivial X] :
    Arrovian ordinalLevel (maximin : Rule Ad X ℝ) ∧ Anonymous (maximin : Rule Ad X ℝ) :=
  ⟨maximin_arrovian_ordinalLevel, maximin_anonymous⟩

/-- Ranking by a weighted sum of two or more dimensions needs a co-interval scale: it survives a
common change of unit and origin but not every common strictly increasing map. -/
-- p. 355
theorem utilitarian_coInterval [Nontrivial X] (c : Ad → ℝ) {P Q : Ad} (hPQ : P ≠ Q)
    (hP : 0 < c P) (hQ : 0 < c Q) :
    Invariant cardinalFull (utilitarian c : Rule Ad X ℝ) ∧
      ¬ Invariant ordinalLevel (utilitarian c : Rule Ad X ℝ) :=
  ⟨(utilitarian_cardinalUnitInvariant c).mono cardinalFull_subset_cardinalUnit,
    not_ordinalLevelInvariant_utilitarian c hPQ hP hQ⟩

end Multidimensional

end VanRooij2011
