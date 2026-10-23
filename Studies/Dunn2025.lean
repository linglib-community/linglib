module

public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Core.Probability.Moments.Standardize
public import Linglib.Core.Probability.UniformOn
public import Linglib.Syntax.ConstructionGrammar.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Probability.UniformOn

/-!
# Dunn (2025): Syntactic Variation from Individuals to Populations: Language as a Complex System

Dunn measures syntactic variation as differences in how individuals, populations and
registers use one umbrella construction grammar. A construction is a contiguous sequence of
slot-constraints, each drawn from one of three ontologies, lexical, syntactic or semantic. The
grammar emerges in stages: two early grammars each draw on one ontology, lexical or syntactic, and
the late grammar on all three. First-order constructions are bundled into third-order
constructions and these into fourth-order ones, and a construction is central or peripheral by its
frequency in a reference corpus. Two samples of usage are compared by the pipeline of Figure 3:
token frequencies are standardized across the samples, weighted by how much the classifiers rely
on each construction, compared by cosine distance, and the distances standardized across the
sampled comparisons.

The two standardizations do what the book says they are for. Standardizing frequencies makes the
distances blind to how frequent a construction is overall, standardizing distances keeps their
ranking, and the sign of a set of comparisons' mean standardized distance says whether its
samples are more or less similar than the average pair.

## Main statements

* `Stage.eq_semPlus_of_admits_of_ne`: a construction that mixes ontologies emerges only in the
  late grammar.
* `standardizedDistance_const_mul_add_const`: rescaling a construction's frequencies across the
  samples changes no standardized distance.
* `standardizedDistance_le_standardizedDistance_iff`: the standardized distances rank the
  comparisons as the cosine distances do.
* `sign_integral_standardizedDistance`: the sign of a set of comparisons' mean standardized
  distance says whether its samples are more or less similar than average.

## Implementation notes

* Learned syntactic categories are rendered by the part of speech of their exemplars, noun phrase
  slots as phrasal slots, and semantic constraints by their human-readable labels.
* The book does not say how the frequency of a higher-order construction is counted, so the
  pipeline is stated for any type of constructions and the network carries no frequencies.
* The sampled comparisons are a finite type mapped to pairs of samples, so a pair may be drawn
  twice.
* Grammar induction, the classifiers, the Bayesian confidence intervals, Figure 1's counts and
  the accuracy tables are not represented; the classifiers enter only through their weights.

## TODO

* The accuracy tables, such as Table 6, belong in `Data/Experiments`.

## References

* [dunn-2025]
-/

@[expose] public section

open ConstructionGrammar Finset InnerProductGeometry MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Dunn2025

/-! ### Constructions and the stages of emergence -/

/-- (1a) is a ditransitive, with a semantic constraint on the verb and two noun phrases, as in
*send me the bill*. -/
def example1a : TypedForm String :=
  [{ filler := .semantic "transfer-event" }, { filler := .phrasal }, { filler := .phrasal }]

/-- (1c) puts lexical constraints in place of the semantic one and of the second noun phrase, as
in *give me a hand*. -/
def example1c : TypedForm String :=
  [{ filler := .fixed "give" }, { filler := .phrasal }, { filler := .fixed "a hand" }]

/-- (2) is an early noun phrase with two syntactic constraints, as in *peanut butter cup*. -/
def example2 : TypedForm String :=
  [{ filler := .open_ .NOUN }, { filler := .open_ .NOUN }]

/-- (3) is a late noun phrase drawing on all three ontologies, as in *the happiest person*. -/
def example3 : TypedForm String :=
  [{ filler := .semantic "which-whereas" }, { filler := .open_ .ADJ },
    { filler := .fixed "person" }]

/-- (5) is a late construction with semantic constraints only, as in *i know i'm*. -/
def example5 : TypedForm String :=
  [{ filler := .semantic "he-we" }, { filler := .semantic "think-know" },
    { filler := .semantic "he-we" }, { filler := .semantic "now" }]

/-- The stages of emergence are the columns of Figure 1, two early grammars and a late one. -/
inductive Stage
  /-- LEX-Only is an early grammar with lexical constraints only. -/
  | lexOnly
  /-- SYN-Only is an early grammar with syntactic constraints only. -/
  | synOnly
  /-- SEM+ is the late grammar, with constraints from all three ontologies. -/
  | semPlus
  deriving DecidableEq, Fintype

/-- `st.levels` are the representation levels the grammar of stage `st` draws on. -/
def Stage.levels : Stage → Finset RepresentationLevel
  | .lexOnly => {.lex}
  | .synOnly => {.syn}
  | .semPlus => univ

section Admits

variable {Lex : Type*}

/-- The grammar of a stage can contain a construction when it draws on the level of each of the
construction's slot-constraints. -/
def Stage.Admits (st : Stage) (form : TypedForm Lex) : Prop :=
  ∀ s ∈ form, s.filler.level ∈ st.levels

instance (st : Stage) (form : TypedForm Lex) : Decidable (st.Admits form) :=
  inferInstanceAs (Decidable (∀ s ∈ form, _))

variable {st : Stage} {form : TypedForm Lex} {s t : Slot Lex}

theorem Stage.eq_semPlus_of_admits_of_ne (h : st.Admits form) (hs : s ∈ form) (ht : t ∈ form)
    (hst : s.filler.level ≠ t.filler.level) : st = .semPlus := by
  have := h s hs; have := h t ht
  cases st <;> simp_all [Stage.levels]

theorem Stage.eq_semPlus_of_admits_of_sem (h : st.Admits form) (hs : s ∈ form)
    (hsem : s.filler.level = .sem) : st = .semPlus := by
  have := h s hs
  cases st <;> simp_all [Stage.levels]

end Admits

/-- (2) fits the syntactic grammar; (1c) mixes lexical and syntactic constraints and (1a), (3)
and (5) carry semantic ones, so only the late grammar admits them. -/
example : Stage.synOnly.Admits example2 := by decide
example : ∀ st : Stage, st.Admits example1a ↔ st = .semPlus := by decide
example : ∀ st : Stage, st.Admits example1c ↔ st = .semPlus := by decide
example : ∀ st : Stage, st.Admits example3 ↔ st = .semPlus := by decide
example : ∀ st : Stage, st.Admits example5 ↔ st = .semPlus := by decide

/-! ### The network -/

/-- A network bundles every first-order construction into a third-order construction and every
third-order construction into a fourth-order one. -/
structure Network (C₁ C₃ C₄ : Type*) where
  /-- `thirdOrder c` is the third-order construction bundling `c`. -/
  thirdOrder : C₁ → C₃
  /-- `fourthOrder d` is the fourth-order construction bundling `d`. -/
  fourthOrder : C₃ → C₄

namespace Network

variable {C₁ C₃ C₄ : Type*} (n : Network C₁ C₃ C₄)

/-- Two first-order constructions are siblings when they belong to one third-order construction. -/
def siblings : Setoid C₁ := Setoid.ker n.thirdOrder

/-- Two first-order constructions are cousins when they belong to one fourth-order construction. -/
def cousins : Setoid C₁ := Setoid.ker (n.fourthOrder ∘ n.thirdOrder)

instance [DecidableEq C₃] : DecidableRel n.siblings := Setoid.ker.decidableRel _

instance [DecidableEq C₄] : DecidableRel n.cousins := Setoid.ker.decidableRel _

theorem siblings_le_cousins : n.siblings ≤ n.cousins := Setoid.ker_le_ker_comp _ _

end Network

/-- This network places (6) to (11), indexed in order. (6), (7) and (8) are siblings, and (9), (10)
and (11) belong to other third-order constructions of the same fourth-order construction, here
each to its own. -/
def network6to11 : Network (Fin 6) (Fin 4) Unit where
  thirdOrder := ![0, 0, 0, 1, 2, 3]
  fourthOrder _ := ()

/-- (6) and (8) are siblings, and (6) and (9) are cousins but not siblings. -/
example : network6to11.siblings 0 2 ∧ network6to11.cousins 0 3 ∧ ¬ network6to11.siblings 0 3 := by
  decide

/-! ### Centrality, footnote 2 -/

section Centrality

variable {C : Type*} [MeasurableSpace C] (ref : C → ℝ)

/-- A construction is central when its frequency in the reference corpus is more than one standard
deviation above the mean over the grammar's constructions. -/
def IsCentral (c : C) : Prop := 1 < standardize ref (uniformOn Set.univ) c

/-- A construction is peripheral when its frequency in the reference corpus is below the mean; the
constructions neither central nor peripheral are mid-frequency. -/
def IsPeripheral (c : C) : Prop := standardize ref (uniformOn Set.univ) c < 0

variable {ref} {c : C}

theorem IsCentral.not_isPeripheral (h : IsCentral ref c) : ¬ IsPeripheral ref c :=
  fun h' ↦ lt_irrefl _ (h'.trans (zero_lt_one.trans h))

theorem isCentral_iff (h : 0 < Var[ref; uniformOn Set.univ]) :
    IsCentral ref c ↔ (uniformOn Set.univ)[ref] + √Var[ref; uniformOn Set.univ] < ref c :=
  one_lt_standardize_iff h

theorem isPeripheral_iff (h : 0 < Var[ref; uniformOn Set.univ]) :
    IsPeripheral ref c ↔ ref c < (uniformOn Set.univ)[ref] :=
  standardize_neg_iff h

end Centrality

/-! ### The similarity pipeline, Figure 3 -/

section Pipeline

variable {S C K P : Type*} [MeasurableSpace S] [Fintype K]

/-- The saliency of a construction is the mean absolute weight the classifiers give it across
their classes. -/
noncomputable def saliency (W : K → C → ℝ) (c : C) : ℝ := 𝔼 k, |W k c|

/-- The standardized usage of a sample, steps 1 to 3, weights each construction's token frequency,
standardized across the samples, by the construction's saliency. -/
noncomputable def standardizedUsage (freq : S → C → ℝ) (W : K → C → ℝ) (s : S) :
    EuclideanSpace ℝ C :=
  WithLp.toLp 2 fun c ↦ saliency W c * standardize (freq · c) (uniformOn Set.univ) s

variable {freq : S → C → ℝ} {W : K → C → ℝ} {pair : P → S × S}

theorem standardizedUsage_const_mul_add_const [Finite S] [Nonempty S]
    [MeasurableSingletonClass S] {a : C → ℝ} (ha : ∀ c, 0 < a c) (b : C → ℝ) :
    standardizedUsage (fun s c ↦ a c * freq s c + b c) W = standardizedUsage freq W := by
  funext s
  ext c
  simp only [standardizedUsage, PiLp.toLp_apply]
  rw [standardize_const_mul_add_const (X := (freq · c)) .of_discrete (ha c)]

/-- The cosine distance of two vectors is one minus the cosine of the angle between them. -/
noncomputable def cosineDistance {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : ℝ :=
  1 - Real.cos (angle x y)

theorem cosineDistance_comm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) :
    cosineDistance x y = cosineDistance y x := by
  rw [cosineDistance, cosineDistance, angle_comm]

variable [Fintype C]

/-- The distance of a sampled comparison, step 4, is the cosine distance between the standardized
usage of its two samples. -/
noncomputable def sampleDistance (freq : S → C → ℝ) (W : K → C → ℝ) (pair : P → S × S) (p : P) :
    ℝ :=
  cosineDistance (standardizedUsage freq W (pair p).1) (standardizedUsage freq W (pair p).2)

theorem sampleDistance_swap :
    sampleDistance freq W (Prod.swap ∘ pair) = sampleDistance freq W pair := by
  funext p
  exact cosineDistance_comm _ _

variable [MeasurableSpace P]

/-- The standardized distances, step 5, are the sample distances standardized across the
comparisons. -/
noncomputable def standardizedDistance (freq : S → C → ℝ) (W : K → C → ℝ) (pair : P → S × S) :
    P → ℝ :=
  standardize (sampleDistance freq W pair) (uniformOn Set.univ)

theorem standardizedDistance_const_mul_add_const [Finite S] [Nonempty S]
    [MeasurableSingletonClass S] {a : C → ℝ} (ha : ∀ c, 0 < a c) (b : C → ℝ) :
    standardizedDistance (fun s c ↦ a c * freq s c + b c) W pair =
      standardizedDistance freq W pair := by
  unfold standardizedDistance sampleDistance
  rw [standardizedUsage_const_mul_add_const ha]

theorem standardizedDistance_le_standardizedDistance_iff
    (h : 0 < Var[sampleDistance freq W pair; uniformOn Set.univ]) {p q : P} :
    standardizedDistance freq W pair p ≤ standardizedDistance freq W pair q ↔
      sampleDistance freq W pair p ≤ sampleDistance freq W pair q :=
  standardize_le_standardize_iff h

variable [Finite P] [MeasurableSingletonClass P]

theorem integral_standardizedDistance [Nonempty P] :
    (uniformOn Set.univ)[standardizedDistance freq W pair] = 0 :=
  integral_standardize .of_discrete

theorem sign_integral_standardizedDistance {T : Finset P} (hT : T.Nonempty) :
    SignType.sign (uniformOn ↑T)[standardizedDistance freq W pair] =
      SignType.sign ((uniformOn ↑T)[sampleDistance freq W pair] -
        (uniformOn Set.univ)[sampleDistance freq W pair]) := by
  have : Nonempty P := ⟨hT.choose⟩
  have := isProbabilityMeasure_uniformOn T.finite_toSet hT
  exact sign_integral_standardize .of_discrete
    (uniformOn_absolutelyContinuous_of_subset Set.finite_univ (Set.subset_univ _)) .of_finite

end Pipeline

end Dunn2025
