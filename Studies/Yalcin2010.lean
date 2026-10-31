module

public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Logic.ComparativeProbability.Content
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Data.Examples.Yalcin2010
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FinCases

/-!
# Yalcin (2010): Probability operators

Yalcin asks what formal structure the semantics of *probably*, *likely* and the comparative
*at least as likely as* requires, and runs three candidate semantics against a list of
inference patterns: the intuitively valid V1–V12, the invalid I1–I3, and the questionable
Conjunctivitis E1. Kratzer's relative likelihood account lifts the preorder an ordering source
induces on worlds to propositions by Lewis's clause; Hamblin's possibility space account
measures a proposition by its most possible world; the probability space account measures it
by a finitely additive probability. In the paper's verdict Kratzer's account validates V1–V10
but fails positive form transfer and validates Halpern's union property I1, whose special case
I2 collapses equiprobability into certainty; Hamblin's validates I1–I3 and Conjunctivitis; and
the probability space account validates V1–V12 and none of I1–I3 or E1.

## Implementation notes

* Each account is a likelihood relation on `Set W` with the comparative probability mixins, so
  most patterns come from `Logic/ComparativeProbability/Patterns` by instance resolution. V6
  and V7 take Kratzer's human necessity and possibility for his account and the quantifiers
  `A = Set.univ` and `A.Nonempty` over the epistemic space for the other two; V8–V10 take
  Kratzer's restricted necessity or, for probability, entailment.
* The refutations are the paper's: footnote 8's two tied worlds against V11, the coin against
  I1 and I2, the twelve-sided die against E1.
* Two of the paper's verdicts do not survive formalization. V12, which the paper counts among
  Kratzer's failures, follows from I2, which the paper shows the account validates
  (`kratzer_V12`); for the same reason it is no point of Hamblin's account over Kratzer's. And
  Hamblin's account, which the paper credits with V11, refutes it (`hamblin_refutes_V11`). The
  paper's claim that Kratzer's account does not validate Conjunctivitis is confirmed by a
  four-world countermodel (`kratzer_refutes_E1`).
* Section numbers and example labels follow the author's June 2010 draft in Zotero and are
  unverified against the Philosophy Compass pagination.

## References

* [yalcin-2010]
* [kratzer-1991]
* [lewis-1973b]
* [hamblin-1959]
* [halpern-2003]
-/

@[expose] public section

namespace Yalcin2010

open ComparativeProbability ComparativePossibility Modality MeasureTheory ProbabilityTheory

/-! ### §3: the relative likelihood approach

The ordering source `O` induces the preorder `v ≤[O] u`, `v` at least as high as `u`; the
comparative is Lewis's lift of it. -/

section Kratzer

variable {W : Type*} (O : Set (W → Prop))

instance : IsPreorder W (premisePreorder O).le where
  refl := (premisePreorder O).le_refl
  trans _ _ _ := (premisePreorder _).le_trans _ _ _

/-- On Kratzer's account `A` is at least as likely as `B` when every world of `B` is matched by
an at least as high world of `A`. -/
abbrev likelihood : Set W → Set W → Prop := Lewis (premisePreorder O).le

/-- Epistemic *must* at `w` is Kratzer's human necessity over the whole space. -/
def must (A : Set W) (w : W) : Prop :=
  humanNecessity ⊥ (fun _ ↦ O) (· ∈ A) w

/-- Epistemic *might* at `w` is human possibility, the dual of `must`. -/
def might (A : Set W) (w : W) : Prop :=
  humanPossibility ⊥ (fun _ ↦ O) (· ∈ A) w

/-- The indicative *if A, B*, with its tacit *must*, is human necessity over the base
restricted by the antecedent, as in Kratzer's restrictor analysis. -/
def ifThen (A B : Set W) (w : W) : Prop :=
  humanNecessity (Background.restrict ⊥ (· ∈ A)) (fun _ ↦ O) (· ∈ B) w

theorem must_iff (A : Set W) (w : W) :
    must O A w ↔ ∀ u, ∃ v, (v ≤[O] u) ∧ ∀ z, (z ≤[O] v) → z ∈ A := by
  simp [must, humanNecessity_iff, Background.accessibleWorlds_bot]

theorem ifThen_iff (A B : Set W) (w : W) :
    ifThen O A B w ↔
      ∀ u ∈ A, ∃ v ∈ A, (v ≤[O] u) ∧ ∀ z ∈ A, (z ≤[O] v) → z ∈ B := by
  simp only [ifThen, humanNecessity_iff, Background.mem_accessibleWorlds_restrict,
    Background.accessibleWorlds_bot, Set.mem_univ, true_and]

theorem kratzer_V1 : ProbablyToNotProbablyNot (likelihood O) := probablyToNotProbablyNot
theorem kratzer_V2 : ProbablyDistribInf (likelihood O) := probablyDistribInf
theorem kratzer_V3 : ChancyDisjunctionIntro (likelihood O) := chancyDisjunctionIntro
theorem kratzer_V4 : Minimality (likelihood O) := minimality
theorem kratzer_V5 : Maximality (likelihood O) := maximality

theorem kratzer_V6 [Nonempty W] (w : W) : MustToProbably (likelihood O) (must O · w) := by
  intro A hA
  rw [must_iff] at hA
  refine ⟨fun u _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, hvu, hv⟩ := hA u
    exact ⟨v, hv v ((premisePreorder O).le_refl v), hvu⟩
  · obtain ⟨w₀⟩ := ‹Nonempty W›
    obtain ⟨v, -, hv⟩ := hA w₀
    obtain ⟨u, hu, huv⟩ := h (hv v ((premisePreorder O).le_refl v))
    exact hu (hv u huv)

theorem kratzer_V7 [Nonempty W] (w : W) : ProbablyToMight (likelihood O) (might O · w) :=
  fun A hA hmust ↦ probablyToNotProbablyNot A hA (kratzer_V6 O w Aᶜ hmust)

theorem kratzer_V10 (w : W) : ConditionalToComparative (likelihood O) (ifThen O · · w) := by
  intro A B hAB u hu
  obtain ⟨v, hvA, hvu, hall⟩ := (ifThen_iff O A B w).1 hAB u hu
  exact ⟨v, hall v hvA ((premisePreorder O).le_refl v), hvu⟩

theorem kratzer_V8 (w : W) : ChancyModusPonens (likelihood O) (ifThen O · · w) := by
  intro A B hAB ⟨hA, hAnot⟩
  rw [ifThen_iff] at hAB
  refine ⟨fun u hu ↦ ?_, fun h ↦ ?_⟩
  · by_cases huA : u ∈ A
    · obtain ⟨v, hvA, hvu, hall⟩ := hAB u huA
      exact ⟨v, hall v hvA ((premisePreorder O).le_refl v), hvu⟩
    · obtain ⟨a, ha, hau⟩ := hA huA
      obtain ⟨v, hvA, hva, hall⟩ := hAB a ha
      exact ⟨v, hall v hvA ((premisePreorder O).le_refl v),
        (premisePreorder _).le_trans _ _ _ hva hau⟩
  · apply hAnot
    by_contra hcon
    have hex : ∃ a ∈ A, ∀ u ∈ Aᶜ, ¬(u ≤[O] a) := by
      by_contra hall
      push Not at hall
      exact hcon fun a ha ↦ hall a ha
    obtain ⟨a, ha, hnone⟩ := hex
    obtain ⟨v, hvA, hva, hall⟩ := hAB a ha
    obtain ⟨u, hu, huv⟩ := h (hall v hvA ((premisePreorder O).le_refl v))
    have huA : u ∈ A := by
      by_contra huA
      exact hnone u huA ((premisePreorder _).le_trans _ _ _ huv hva)
    exact hu (hall u huA huv)

theorem kratzer_V9 (w : W) : ChancyModusTollens (likelihood O) (ifThen O · · w) :=
  chancyModusTollens_iff.2 (kratzer_V8 O w)

theorem kratzer_I1 : RightUnion (likelihood O) := rightUnion_lewis

theorem kratzer_I2 : EquiprobabilityCollapse (likelihood O) :=
  equiprobabilityCollapse_of_rightUnion (kratzer_I1 O)

/-- Complement transfer V12 holds for the lift of every preorder, though the paper lists it with
V11, which its footnote 8 refutes. -/
theorem kratzer_V12 : ComplementTransfer (likelihood O) :=
  complementTransfer_of_equiprobabilityCollapse (kratzer_I2 O)

end Kratzer

theorem kratzer_refutes_V11 : ¬PositiveFormTransfer (likelihood (∅ : Set (Fin 2 → Prop))) := by
  intro h
  exact (h Set.univ {0} (fun _ _ ↦ ⟨0, rfl, (fun _ h ↦ h.elim)⟩) probably_top).2
    fun _ _ ↦ ⟨1, by simp, (fun _ h ↦ h.elim)⟩

theorem kratzer_refutes_E1 :
    ¬Conjunctivitis (likelihood {(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))}) := by
  intro h
  have hle : ∀ v u : Fin 4, (v ≤[{(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))}] u)
      ↔ (u ∈ ({0, 1} : Set (Fin 4)) → v ∈ ({0, 1} : Set (Fin 4))) ∧
        (u ∈ ({2, 3} : Set (Fin 4)) → v ∈ ({2, 3} : Set (Fin 4))) := fun v u ↦ by
    simp [Preorder.ofCriteria_le_iff]
  have hφ : Probably (likelihood {(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))})
      {0, 2, 3} := by
    refine ⟨fun u hu ↦ ⟨0, by simp, ?_⟩, fun hc ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hle]
      have : u = 1 := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
        omega
      subst this; simp
    · obtain ⟨u, hu, hu2⟩ := @hc 2 (by simp)
      simp only [Set.mem_ofPred_eq] at hu2
      rw [hle] at hu2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      have : u = 1 := by omega
      subst this; simp at hu2
  have hψ : Probably (likelihood {(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))})
      {1, 2, 3} := by
    refine ⟨fun u hu ↦ ⟨1, by simp, ?_⟩, fun hc ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hle]
      have : u = 0 := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
        omega
      subst this; simp
    · obtain ⟨u, hu, hu2⟩ := @hc 2 (by simp)
      simp only [Set.mem_ofPred_eq] at hu2
      rw [hle] at hu2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      have : u = 0 := by omega
      subst this; simp at hu2
  have hinter : ({0, 2, 3} : Set (Fin 4)) ∩ {1, 2, 3} = {2, 3} := by
    ext x; fin_cases x <;> simp
  have := (h _ _ hφ hψ).1
  simp only [Set.inf_eq_inter, hinter] at this
  obtain ⟨a, ha, ha0⟩ := @this 0 (by simp)
  simp only [Set.mem_ofPred_eq] at ha0
  rw [hle] at ha0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> simp at ha0

/-! ### §4: the possibility space approach -/

section Hamblin

variable {W : Type*} [Fintype W]

/-- Hamblin's plausibility is a possibility measure on a finite epistemic space, given by values
on worlds that are at most `1` and attain `1`, so that the whole space measures `1` and every
proposition or its complement is fully possible. -/
structure Possibility (W : Type*) where
  /-- `poss w` is the possibility of the world `w`. -/
  poss : W → ℚ≥0
  le_one : ∀ w, poss w ≤ 1
  exists_eq_one : ∃ w, poss w = 1

namespace Possibility

variable (m : Possibility W)

open scoped Classical in
/-- The possibility of a proposition is the greatest possibility of its worlds. -/
noncomputable def measure (A : Set W) : ℚ≥0 := (Finset.univ.filter (· ∈ A)).sup m.poss

theorem measure_le_one (A : Set W) : m.measure A ≤ 1 :=
  Finset.sup_le fun v _ ↦ m.le_one v

theorem measure_eq_one_iff (A : Set W) : m.measure A = 1 ↔ ∃ w ∈ A, m.poss w = 1 := by
  classical
  constructor
  · intro h
    by_cases hA : (Finset.univ.filter (· ∈ A)).Nonempty
    · obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup' hA m.poss
      refine ⟨w, (Finset.mem_filter.1 hw).2, ?_⟩
      rw [← hsup, Finset.sup'_eq_sup hA]
      exact h
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      simp [measure, hA] at h
  · rintro ⟨w, hw, hw1⟩
    refine le_antisymm (m.measure_le_one A) ?_
    rw [← hw1]
    exact Finset.le_sup (f := m.poss) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)

theorem measure_mono {A B : Set W} (h : A ⊆ B) : m.measure A ≤ m.measure B := by
  classical
  exact Finset.sup_mono fun x hx ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h (Finset.mem_filter.1 hx).2⟩

theorem measure_empty : m.measure ∅ = 0 := by simp [measure]

theorem measure_univ : m.measure Set.univ = 1 :=
  (m.measure_eq_one_iff _).2 (let ⟨w, hw⟩ := m.exists_eq_one; ⟨w, Set.mem_univ w, hw⟩)

theorem measure_singleton (w : W) : m.measure {w} = m.poss w := by
  rw [measure]
  convert Finset.sup_singleton (f := m.poss) (b := w)
  ext; simp

theorem measure_union (A B : Set W) : m.measure (A ∪ B) = m.measure A ⊔ m.measure B := by
  classical
  simp only [measure]
  rw [← Finset.sup_union]
  congr 1
  ext; simp

theorem measure_eq_one_or_compl (A : Set W) : m.measure A = 1 ∨ m.measure Aᶜ = 1 := by
  have h := m.measure_union A Aᶜ
  rw [Set.union_compl_self, m.measure_univ] at h
  rcases le_total (m.measure A) (m.measure Aᶜ) with hle | hle
  · exact Or.inr (by rw [sup_eq_right.2 hle] at h; exact h.symm)
  · exact Or.inl (by rw [sup_eq_left.2 hle] at h; exact h.symm)

/-- On Hamblin's account `A` is at least as likely as `B` when it is at least as possible. -/
def likelihood (A B : Set W) : Prop := m.measure B ≤ m.measure A

instance : IsLikelihoodMono m.likelihood := ⟨fun _ _ h ↦ m.measure_mono h⟩
instance : IsTrans (Set W) m.likelihood := ⟨fun _ _ _ hab hbc ↦ le_trans hbc hab⟩
instance : Std.Refl m.likelihood := ⟨fun _ ↦ le_rfl⟩
instance : IsNontrivial m.likelihood :=
  ⟨fun h ↦ absurd (m.measure_univ ▸ m.measure_empty ▸ h : (1 : ℚ≥0) ≤ 0) (not_le.2 one_pos)⟩

theorem measure_eq_one_of_probably {A : Set W} (h : Probably m.likelihood A) :
    m.measure A = 1 ∧ m.measure Aᶜ < 1 := by
  obtain ⟨hle, hnot⟩ := h
  have hlt : m.measure Aᶜ < m.measure A := lt_of_le_not_ge hle hnot
  rcases m.measure_eq_one_or_compl A with h1 | h1
  · exact ⟨h1, h1 ▸ hlt⟩
  · exact absurd (h1 ▸ hlt) (not_lt.2 (m.measure_le_one A))

theorem hamblin_V1 : ProbablyToNotProbablyNot m.likelihood := probablyToNotProbablyNot
theorem hamblin_V2 : ProbablyDistribInf m.likelihood := probablyDistribInf
theorem hamblin_V3 : ChancyDisjunctionIntro m.likelihood := chancyDisjunctionIntro
theorem hamblin_V4 : Minimality m.likelihood := minimality
theorem hamblin_V5 : Maximality m.likelihood := maximality

-- §4
theorem hamblin_V6 : MustToProbably m.likelihood (· = Set.univ) := mustToProbably

theorem hamblin_V7 : ProbablyToMight m.likelihood Set.Nonempty :=
  fun A hA ↦ Set.nonempty_iff_ne_empty.2 (probablyToMight A hA)

theorem hamblin_E1 : Conjunctivitis m.likelihood := by
  intro A B hA hB
  obtain ⟨hA1, hAc⟩ := m.measure_eq_one_of_probably hA
  obtain ⟨hB1, hBc⟩ := m.measure_eq_one_of_probably hB
  obtain ⟨w, hwA, hw⟩ := (m.measure_eq_one_iff A).1 hA1
  have hwB : w ∈ B := by
    by_contra hwB
    have := m.measure_mono (Set.singleton_subset_iff.2 (Set.mem_compl hwB))
    rw [m.measure_singleton, hw] at this
    exact absurd (this.trans_lt hBc) (lt_irrefl _)
  have hAB : m.measure (A ⊓ B) = 1 :=
    (m.measure_eq_one_iff _).2 ⟨w, ⟨hwA, hwB⟩, hw⟩
  have hABc : m.measure (A ⊓ B)ᶜ < 1 := by
    show m.measure (A ∩ B)ᶜ < 1
    rw [Set.compl_inter, m.measure_union]
    exact max_lt hAc hBc
  exact ⟨by rw [likelihood, hAB]; exact m.measure_le_one _,
    fun h ↦ absurd (hAB ▸ h) (not_le.2 hABc)⟩

theorem hamblin_I1 : RightUnion m.likelihood := fun A B C hAB hAC ↦ by
  show m.measure (B ∪ C) ≤ m.measure A
  rw [m.measure_union]; exact max_le hAB hAC

theorem hamblin_I2 : EquiprobabilityCollapse m.likelihood :=
  equiprobabilityCollapse_of_rightUnion m.hamblin_I1

theorem hamblin_I3 : HamblinCollapse m.likelihood :=
  hamblinCollapse_of_equiprobabilityCollapse m.hamblin_I2

theorem hamblin_V12 : ComplementTransfer m.likelihood :=
  complementTransfer_of_equiprobabilityCollapse m.hamblin_I2

end Possibility

/-- `threeWorlds` makes the first two of three worlds fully possible and the third half
possible. Here `{0, 1}` is probable and `{0, 2}` is as possible as it, yet `{0, 2}` is not
probable, since its complement `{1}` is fully possible. The paper credits Hamblin's account
with positive form transfer; it fails. -/
def threeWorlds : Possibility (Fin 3) :=
  ⟨![1, 1, 1 / 2], fun w ↦ by fin_cases w <;> norm_num, ⟨0, rfl⟩⟩

theorem hamblin_refutes_V11 : ¬PositiveFormTransfer threeWorlds.likelihood := by
  intro h
  have hpair : ∀ a b : Fin 3, threeWorlds.measure {a, b} =
      threeWorlds.poss a ⊔ threeWorlds.poss b := fun a b ↦ by
    rw [Set.insert_eq, Possibility.measure_union, Possibility.measure_singleton,
      Possibility.measure_singleton]
  have hc01 : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have hc02 : ({0, 2} : Set (Fin 3))ᶜ = {1} := by ext x; fin_cases x <;> simp
  have half_lt : (1 / 2 : ℚ≥0) < 1 := by rw [← NNRat.coe_lt_coe]; push_cast; norm_num
  have h0 : threeWorlds.poss 0 = 1 := rfl
  have h1 : threeWorlds.poss 1 = 1 := rfl
  have h2 : threeWorlds.poss 2 = 1 / 2 := rfl
  have m01 : threeWorlds.measure {0, 1} = 1 := by rw [hpair, h0, h1, sup_idem]
  have m02 : threeWorlds.measure {0, 2} = 1 := by rw [hpair, h0, h2, sup_eq_left.2 half_lt.le]
  have m2 : threeWorlds.measure {2} = 1 / 2 := by rw [Possibility.measure_singleton, h2]
  have m1 : threeWorlds.measure {1} = 1 := by rw [Possibility.measure_singleton, h1]
  have hA : Probably threeWorlds.likelihood {0, 1} := by
    refine ⟨?_, fun h ↦ ?_⟩
    · show threeWorlds.measure ({0, 1} : Set (Fin 3))ᶜ ≤ threeWorlds.measure {0, 1}
      rw [hc01, m2, m01]; exact half_lt.le
    · have : threeWorlds.measure {0, 1} ≤ threeWorlds.measure ({0, 1} : Set (Fin 3))ᶜ := h
      rw [hc01, m2, m01] at this
      exact absurd this (not_le.2 half_lt)
  have hBA : threeWorlds.likelihood {0, 2} {0, 1} := by
    show threeWorlds.measure {0, 1} ≤ threeWorlds.measure {0, 2}
    rw [m01, m02]
  apply (h _ _ hBA hA).2
  show threeWorlds.measure {0, 2} ≤ threeWorlds.measure ({0, 2} : Set (Fin 3))ᶜ
  rw [hc02, m1, m02]

end Hamblin

/-! ### §5: semantics with probability spaces -/

section Probability

variable {W : Type*} [MeasurableSpace W] (P : Measure W)

theorem prob_V1 : ProbablyToNotProbablyNot P.inducedGe := probablyToNotProbablyNot

variable [DiscreteMeasurableSpace W] [IsProbabilityMeasure P]

theorem prob_V2 : ProbablyDistribInf P.inducedGe := probablyDistribInf
theorem prob_V3 : ChancyDisjunctionIntro P.inducedGe := chancyDisjunctionIntro
theorem prob_V4 : Minimality P.inducedGe := minimality
theorem prob_V5 : Maximality P.inducedGe := maximality

theorem prob_V6 : MustToProbably P.inducedGe (· = Set.univ) := mustToProbably

theorem prob_V7 : ProbablyToMight P.inducedGe Set.Nonempty :=
  fun A hA ↦ Set.nonempty_iff_ne_empty.2 (probablyToMight A hA)

theorem prob_V8 : ChancyModusPonens P.inducedGe (· ⊆ ·) := chancyModusPonens_le
theorem prob_V9 : ChancyModusTollens P.inducedGe (· ⊆ ·) := chancyModusTollens_le
theorem prob_V10 : ConditionalToComparative P.inducedGe (· ⊆ ·) := conditionalToComparative_le
theorem prob_V11 : PositiveFormTransfer P.inducedGe := positiveFormTransfer
theorem prob_V12 : ComplementTransfer P.inducedGe := complementTransfer

end Probability

private theorem uniform_inducedGe_iff {n : ℕ} [NeZero n] {A B : Set (Fin n)} :
    (uniformOn (Set.univ : Set (Fin n))).inducedGe A B ↔ B.ncard ≤ A.ncard :=
  uniformOn_univ_le_iff

theorem prob_refutes_I1_I2 :
    ¬RightUnion (uniformOn (Set.univ : Set (Fin 2))).inducedGe ∧
      ¬EquiprobabilityCollapse (uniformOn (Set.univ : Set (Fin 2))).inducedGe := by
  have hc : ({0} : Set (Fin 2))ᶜ = {1} := by ext x; fin_cases x <;> simp
  have hu : ({1} : Set (Fin 2)) ⊔ {0} = Set.univ := by ext x; fin_cases x <;> simp
  constructor
  · intro h
    have := h {0} {1} {0} (by simp [uniform_inducedGe_iff]) (by simp [uniform_inducedGe_iff])
    rw [hu, uniform_inducedGe_iff] at this
    simp at this
  · intro h
    have := h {0} Set.univ (by simp [hc, uniform_inducedGe_iff])
    rw [uniform_inducedGe_iff] at this
    simp at this

theorem prob_refutes_I3 : ¬HamblinCollapse (uniformOn (Set.univ : Set (Fin 3))).inducedGe := by
  intro h
  have hA : ({0, 1} : Set (Fin 3)).ncard = 2 := Set.ncard_pair (by decide)
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have := h {0, 1} Set.univ ⟨by rw [uniform_inducedGe_iff, hc, hA, Set.ncard_singleton]; omega,
    by rw [uniform_inducedGe_iff, hc, hA, Set.ncard_singleton]; omega⟩
  rw [uniform_inducedGe_iff, hA] at this
  simp at this

-- §4
theorem prob_refutes_E1 : ¬Conjunctivitis (uniformOn (Set.univ : Set (Fin 12))).inducedGe := by
  intro h
  have hcard : ∀ A : Set (Fin 12), A.ncard + Aᶜ.ncard = 12 := fun A ↦ by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hprob : ∀ A : Set (Fin 12), 6 < A.ncard →
      Probably (uniformOn (Set.univ : Set (Fin 12))).inducedGe A := fun A hA ↦ by
    have := hcard A
    exact ⟨uniform_inducedGe_iff.2 (by omega), fun h ↦ by rw [uniform_inducedGe_iff] at h; omega⟩
  have hlow : ({n : Fin 12 | n.val < 8} : Set (Fin 12)).ncard = 8 := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have hhigh : ({n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)).ncard = 8 := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have hint : ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)) =
      {n : Fin 12 | 4 ≤ n.val ∧ n.val < 8} := by
    ext n; simp [and_comm]
  have hmid : ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)).ncard = 4 := by
    rw [hint, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have := hcard ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val})
  exact (h {n | n.val < 8} {n | 4 ≤ n.val} (hprob _ (by omega)) (hprob _ (by omega))).2
    (uniform_inducedGe_iff.2 (by omega))

/-! ### §6: scales

*Probably* as a relative adjective compares the probability with a contextual threshold
`n`; V1 survives exactly the thresholds at or above one half. -/

section Threshold

variable {W : Type*} [MeasurableSpace W] (P : Measure W)

/-- *Probably* with threshold `n` holds when `Pr(A) > n`, the strict positive form of the
probability scale. -/
def probablyAt (n : ℝ) (A : Set W) : Prop := A ∈ P.real ⁻¹' Set.Ioi n

theorem probablyAt_V1 [DiscreteMeasurableSpace W] [IsProbabilityMeasure P] {n : ℝ}
    (hn : 1 / 2 ≤ n) (A : Set W) : probablyAt P n A → ¬probablyAt P n Aᶜ := by
  intro hA hAc
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  simp only [probablyAt, Set.mem_preimage, Set.mem_Ioi] at hA hAc
  linarith

end Threshold

theorem probablyAt_refutes_V1 :
    probablyAt (uniformOn (Set.univ : Set (Fin 2))) (1 / 3) {0} ∧
      probablyAt (uniformOn (Set.univ : Set (Fin 2))) (1 / 3) ({0} : Set (Fin 2))ᶜ := by
  have hc : ({0} : Set (Fin 2))ᶜ = {1} := by ext x; fin_cases x <;> simp
  simp only [probablyAt, Set.mem_preimage, Set.mem_Ioi, hc,
    uniformOn_univ_real_singleton, Fintype.card_fin]
  norm_num

end Yalcin2010
