module

public import Linglib.Core.Probability.Decision.Blackwell
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Data.Examples.Ochs1992
public import Linglib.Data.Examples.Readers
public import Linglib.Data.StructureDataset.Ochs1992
public import Linglib.Fragments.Japanese.Particles

/-!
# Ochs (1992): Indexing gender

A speaker of some social identity takes up a social meaning, a stance, act or activity, at rates
the norms of a community set, and a linguistic form realizes that meaning, so the use of a form
across identities is a composition of Markov kernels. The relations of Ochs's model are the supports
of those kernels: a form indexes an identity exactly when [it directly indexes a meaning that helps
to constitute the identity](##indexes_comp), and [it indexes one identity exclusively only if its
stance does](##ExclusivelyIndexes.comp_iff). Identities [differ in a form of a stance exactly as
they differ in the stance](##ExclusivelyIndexes.comp_apply_lt_iff), and [in two forms of one stance
by the same proportion](##ExclusivelyIndexes.comp_apply_mul_comm). A hearer [learns no more about a
speaker from the form than from the stance](##blackwellDominates_comp), while a catalogue of
correlations between forms and speakers [need not be mediated at
all](##not_isGarblingOf_of_apply_eq). [The indirect indexes of two Japanese
particles](##rows_figure_14_1) follow from one difference between men and women, [each cell of the
comparison of caregivers](##rows_figure_14_3) is one difference between two communities, and [a
later *maaloo* changes what a past activity has been](##credited_exchange).

## Implementation notes

* The chapter calls the relation of language to gender distributional and probabilistic and prints
  no numbers, so the kernels are arbitrary and the comparisons it states are hypotheses.
* The kernels run from identity to form, the direction of use. Indexing reads them backwards, as
  their support. A direct index of gender is mediation through the identity itself, `Kernel.id`.
* A strategy's orientation is who accommodates in the dyad of caregiver and child, the caregiver in
  a child-centered strategy, and the child in an other-centered one.
* The comparison of rates reads the "little simplification" of Figure 14.3 and the "rarely" of
  p. 351, not the "do not use" of p. 350.

## Errata

* The chapter first says that *ze* and *wa* pragmatically presuppose the sex of the speaker
  (p. 339), then that features used by both sexes cannot be said to do so (p. 340), and that one sex
  may assume the "voice" of the other (p. 343), without saying which holds of the two particles. On
  the model the first holds [only if the stance is closed to the other
  sex](##ExclusivelyIndexes.comp_iff), which rules out the last.

## TODO

* Precontextualization, the expectations a first pair part sets up (pp. 345-346), and markedness,
  which the chapter leaves to "a more refined model" (p. 343).

## References

* [ochs-1992]
* [uyeno-1971]
* [west-zimmerman-1987]
* [blackwell-1953]
-/

@[expose] public section

namespace Ochs1992

open MeasureTheory ProbabilityTheory
open CLDF.StructureDataset (Language Coded)
open Japanese.Particles (ze wa)
open scoped ENNReal

/-! ### Direct and constitutive relations -/

section Model

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A form `f` *indexes* `a` under a kernel from such `a`s to forms when `a` yields `f` with nonzero
mass. A kernel from social meanings to forms gives the direct indexical relation, and one from
identities to meanings the relation in which a meaning helps to constitute an identity. -/
def Indexes (κ : Kernel A B) (f : B) (a : A) : Prop := κ a {f} ≠ 0

/-- A form *exclusively indexes* `a` when it indexes `a` and nothing else, the strict,
presuppositional relation of pp. 339-340. -/
def ExclusivelyIndexes (κ : Kernel A B) (f : B) (a : A) : Prop := ∀ a', Indexes κ f a' ↔ a' = a

variable {I M F : Type*} [MeasurableSpace I] [MeasurableSpace M] [MeasurableSpace F]
  {η : Kernel M F} {κ : Kernel I M} {f f' : F} {m : M} {i i' : I}

-- p. 342: differences of use with no difference of stance cannot be mediated by the stance.
theorem not_isGarblingOf_of_apply_eq {u : Kernel I F} (h : κ i = κ i') (hu : u i ≠ u i') :
    ¬ u.IsGarblingOf κ := by
  rintro ⟨η, -, rfl⟩
  exact hu (by rw [Kernel.comp_apply, Kernel.comp_apply, h])

-- p. 342: whatever a hearer has to decide about a speaker, the form tells no more than the stance.
theorem blackwellDominates_comp (η : Kernel M F) [IsMarkovKernel η] (κ : Kernel I M) :
    κ.BlackwellDominates (η ∘ₖ κ) :=
  blackwellDominates_of_isGarblingOf ⟨η, inferInstance, rfl⟩

private theorem apply_compl_lt_iff [IsMarkovKernel κ] {s : Set M} (hs : MeasurableSet s) :
    κ i' sᶜ < κ i sᶜ ↔ κ i s < κ i' s := by
  rw [prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs]
  exact (ENNReal.cancel_of_ne (measure_ne_top _ _)).tsub_lt_tsub_iff_left_of_le_of_le
    (ENNReal.cancel_of_ne (ENNReal.sub_ne_top ENNReal.one_ne_top)) prob_le_one prob_le_one

variable [Fintype M] [MeasurableSingletonClass M] [MeasurableSingletonClass F]

/-- A form indexes an identity exactly when it directly indexes a social meaning that helps to
constitute the identity: the solid and the dashed arrows of Figure 14.2 (pp. 342-343). -/
theorem indexes_comp (η : Kernel M F) (κ : Kernel I M) :
    Indexes (η ∘ₖ κ) = Relation.Comp (Indexes η) (Indexes κ) := by
  ext f i
  simp only [Indexes, Relation.Comp, Kernel.comp_apply, Measure.comp_apply_singleton_ne_zero_iff]
  exact ⟨fun ⟨m, h₁, h₂⟩ ↦ ⟨m, h₂, h₁⟩, fun ⟨m, h₁, h₂⟩ ↦ ⟨m, h₂, h₁⟩⟩

-- p. 340: a form associated with an identity through a meaning open to another is not exclusive.
theorem not_exclusivelyIndexes_comp {i₁ i₂ : I} (hne : i₁ ≠ i₂) (hm : Indexes η f m)
    (h₁ : Indexes κ m i₁) (h₂ : Indexes κ m i₂) : ¬ ExclusivelyIndexes (η ∘ₖ κ) f i := fun h ↦ by
  have key {x} (hx : Indexes κ m x) : x = i :=
    (h x).1 (by rw [indexes_comp]; exact ⟨m, hm, hx⟩)
  exact hne ((key h₁).trans (key h₂).symm)

namespace ExclusivelyIndexes

theorem comp_apply (h : ExclusivelyIndexes η f m) (i : I) :
    (η ∘ₖ κ) i {f} = κ i {m} * η m {f} := by
  rw [Kernel.comp_apply, Measure.comp_apply_singleton]
  refine Finset.sum_eq_single m (fun m' _ hm' ↦ ?_) (by simp)
  rw [show η m' {f} = 0 from by_contra fun hne ↦ hm' ((h m').1 hne), mul_zero]

-- p. 350: the identities a form indexes are settled by the community, whose kernel `κ` alone
-- decides them, so the simplified register, directly indexing accommodation in both communities,
-- indirectly indexes caregivers with children in one and members with foreign dignitaries in the
-- other.
theorem indexes_comp_iff (h : ExclusivelyIndexes η f m) :
    Indexes (η ∘ₖ κ) f i ↔ Indexes κ m i := by
  simp [Indexes, h.comp_apply, show η m {f} ≠ 0 from (h m).2 rfl]

/-- A form of one stance exclusively indexes an identity exactly when the stance does, so that a
form used to convey a stance open to both sexes does not pragmatically presuppose either
(pp. 340-341). -/
theorem comp_iff (h : ExclusivelyIndexes η f m) :
    ExclusivelyIndexes (η ∘ₖ κ) f i ↔ ExclusivelyIndexes κ m i :=
  forall_congr' fun _ ↦ by rw [h.indexes_comp_iff]

-- p. 341: the dispositions a form indexes "motivate [its] differential use by men and women".
theorem comp_apply_lt_iff [IsFiniteKernel η] (h : ExclusivelyIndexes η f m) :
    (η ∘ₖ κ) i {f} < (η ∘ₖ κ) i' {f} ↔ κ i {m} < κ i' {m} := by
  rw [h.comp_apply, h.comp_apply]
  exact ENNReal.mul_lt_mul_iff_left ((h m).2 rfl) (measure_ne_top _ _)

-- Two forms of one stance differ between identities in the same proportion.
theorem comp_apply_mul_comm (h : ExclusivelyIndexes η f m) (h' : ExclusivelyIndexes η f' m) :
    (η ∘ₖ κ) i {f} * (η ∘ₖ κ) i' {f'} = (η ∘ₖ κ) i' {f} * (η ∘ₖ κ) i {f'} := by
  rw [h.comp_apply, h.comp_apply, h'.comp_apply, h'.comp_apply]
  ring

end ExclusivelyIndexes

end Model

/-! ### Indexing gender in Japanese -/

section Japanese

/-- The stances that the particles of Figure 14.1 directly index. -/
inductive Stance where
  | coarseIntensity
  | delicateIntensity
  deriving DecidableEq, Fintype

/-- The genders of the figure's indirect indexes, a male and a female "voice". -/
inductive Gender where
  | male
  | female
  deriving DecidableEq, Fintype

instance : MeasurableSpace Stance := ⊤
instance : DiscreteMeasurableSpace Stance := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Gender := ⊤
instance : DiscreteMeasurableSpace Gender := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Particle := ⊤
instance : DiscreteMeasurableSpace Particle := ⟨fun _ ↦ trivial⟩

/-- The rows of Figure 14.1 with their particles. -/
def figure141 : List (Datum × Particle) := [(Examples.ze, ze), (Examples.wa, wa)]

/-- The direct index a row of Figure 14.1 prints. -/
def direct (d : Datum) : Option Stance :=
  d.parse? "directIndex"
    [("coarse intensity", .coarseIntensity), ("delicate intensity", .delicateIntensity)]

/-- The indirect index a row of Figure 14.1 prints. -/
def voice (d : Datum) : Option Gender :=
  d.parse? "indirectIndex" [("male voice", .male), ("female voice", .female)]

example : ∀ x ∈ figure141, x.1.primaryText = x.2.form := by decide

variable {η : Kernel Stance Particle} [IsFiniteKernel η]
  {κ : Kernel Gender Stance} [IsMarkovKernel κ]

/-- Given the direct indexes of Figure 14.1 and one difference between men and women, in coarse
intensity, each particle is used more by the gender of its indirect index (pp. 341-342). -/
theorem rows_figure_14_1
    (hη : ∀ x ∈ figure141, ∀ s, direct x.1 = some s → ExclusivelyIndexes η x.2 s)
    (h : κ .female {.coarseIntensity} < κ .male {.coarseIntensity}) :
    ∀ x ∈ figure141, ∀ g, voice x.1 = some g → ∀ g' ≠ g, (η ∘ₖ κ) g' {x.2} < (η ∘ₖ κ) g {x.2} := by
  have hze : ExclusivelyIndexes η ze .coarseIntensity :=
    hη (Examples.ze, ze) (by simp [figure141]) _ (by decide)
  have hwa : ExclusivelyIndexes η wa .delicateIntensity :=
    hη (Examples.wa, wa) (by simp [figure141]) _ (by decide)
  have hcompl : ({.delicateIntensity} : Set Stance) = {.coarseIntensity}ᶜ := by
    ext s; cases s <;> simp
  intro x hx g hg g' hne
  simp only [figure141, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · obtain rfl : g = .male := Option.some.inj (hg.symm.trans (by decide))
    cases g' with
    | male => exact absurd rfl hne
    | female => exact hze.comp_apply_lt_iff.2 h
  · obtain rfl : g = .female := Option.some.inj (hg.symm.trans (by decide))
    cases g' with
    | female => exact absurd rfl hne
    | male =>
      refine hwa.comp_apply_lt_iff.2 ?_
      rw [hcompl]
      exact (apply_compl_lt_iff (.singleton _)).2 h

end Japanese

/-! ### Communicative styles of caregivers -/

section Caregivers

open StructureDataset

deriving instance Fintype for Orientation
deriving instance Fintype for Strategy

namespace StructureDataset

/-- A strategy of Figure 14.3 is child-centered when the caregiver accommodates to the child and
other-centered when the child accommodates to others. Simplifying and guessing take the child's
point of view, and leaving a child's speech unsimplified or unclear leaves the child to attend and
to reformulate (pp. 350-352). Unidirectional praise denies the caregiver's part in an activity, and
bidirectional praise has the child articulate it (pp. 353-354). -/
def Strategy.orientation : Strategy → Orientation
  | .extensiveSimplification | .expressGuess | .unidirectional => .childCentered
  | .littleSimplification | .displayMinimalGrasp | .bidirectional => .otherCentered

/-- The strategies of a community in Figure 14.3. -/
def Row.strategies (r : Row) : List (Coded Strategy) :=
  r.production ++ r.interpretive ++ r.praising

end StructureDataset

instance : MeasurableSpace Language := ⊤
instance : DiscreteMeasurableSpace Language := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Orientation := ⊤
instance : DiscreteMeasurableSpace Orientation := ⟨fun _ ↦ trivial⟩
instance : MeasurableSpace Strategy := ⊤
instance : DiscreteMeasurableSpace Strategy := ⟨fun _ ↦ trivial⟩

-- Figure 14.3's column heads: each column has the orientation its head prints.
theorem orientation_figure143 :
    ∀ r ∈ figure143, ∀ o ∈ r.orientation, ∀ c ∈ r.strategies, c.code.orientation = o.code := by
  decide

variable {η : Kernel Orientation Strategy} [IsFiniteKernel η]
  {κ : Kernel Language Orientation} [IsMarkovKernel κ]

/-- Each cell of Figure 14.3, that its community uses its strategy more than the other community
does, is equivalent to one comparison: caregivers are more often child-centered in the one community
than in the other. The cells are "manifestations" of one orientation (p. 351), and that comparison
is the communicative level of the Samoan mother's "more prestigious position" (p. 354). -/
theorem rows_figure_14_3 (hη : ∀ s : Strategy, ExclusivelyIndexes η s s.orientation) {r r' : Row}
    (hr : r ∈ figure143) (hr' : r' ∈ figure143) (hne : r ≠ r') {c : Coded Strategy}
    (hc : c ∈ r.strategies) :
    (η ∘ₖ κ) r'.language {c.code} < (η ∘ₖ κ) r.language {c.code} ↔
      κ samoan {.childCentered} < κ american {.childCentered} := by
  have hcompl : ({.otherCentered} : Set Orientation) = {.childCentered}ᶜ := by
    ext o; cases o <;> simp
  rw [(hη c.code).comp_apply_lt_iff]
  simp only [figure143, List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
  · exact absurd rfl hne
  · rw [orientation_figure143 _ (by simp [figure143]) ⟨.childCentered, false, false, false⟩
      (by simp) c hc]
  · rw [orientation_figure143 _ (by simp [figure143]) ⟨.otherCentered, false, false, false⟩
      (by simp) c hc, hcompl]
    exact apply_compl_lt_iff (.singleton _)
  · exact absurd rfl hne

/-- Who is credited with a past activity by an exchange of praises, each a praiser and an addressee
in order of utterance: a praise recontextualizes the activity as an accomplishment of its addressee
(p. 353). -/
def credited {P : Type*} (e : List (P × P)) : Set P := {p | ∃ q, (q, p) ∈ e}

/-- An exchange is bidirectional when every praise is answered by a praise of the praiser. -/
def Bidirectional {P : Type*} (e : List (P × P)) : Prop := ∀ x ∈ e, x.swap ∈ e

-- p. 354: a second *maaloo* makes the congratulator "someone to be congratulated as well".
theorem Bidirectional.fst_mem_credited {P : Type*} {e : List (P × P)} (h : Bidirectional e)
    {x : P × P} (hx : x ∈ e) : x.1 ∈ credited e :=
  ⟨x.2, h x hx⟩

/-- The parties to a joint activity of caregiver and child. -/
inductive Party where
  | caregiver
  | child
  deriving DecidableEq

/-- The exchange of a praising strategy of Figure 14.3 over an activity of caregiver and child. -/
def StructureDataset.Strategy.exchange : Strategy → List (Party × Party)
  | .unidirectional => [(.caregiver, .child)]
  | .bidirectional => [(.caregiver, .child), (.child, .caregiver)]
  | _ => []

/-- A caregiver's praise makes a past joint activity solely the child's accomplishment, and a second
*maaloo*, said later, makes the same activity jointly accomplished, so that what the activity has
been depends on talk that follows it (pp. 345, 353-354). -/
theorem credited_exchange :
    credited Strategy.unidirectional.exchange = {.child} ∧
      Strategy.bidirectional.exchange =
        Strategy.unidirectional.exchange ++ [(.child, .caregiver)] ∧
      credited Strategy.bidirectional.exchange = Set.univ := by
  refine ⟨?_, rfl, ?_⟩ <;> ext p <;> cases p <;> simp [credited, Strategy.exchange]

-- pp. 347, 353-354: the praising row of Figure 14.3 from the exchanges: a caregiver is credited
-- exactly under the other-centered strategy, which is exactly the bidirectional one.
theorem rows_praising : ∀ r ∈ figure143, ∀ c ∈ r.praising,
    (Bidirectional c.code.exchange ↔ c.code = .bidirectional) ∧
      (.caregiver ∈ credited c.code.exchange ↔ c.code.orientation = .otherCentered) := by
  simp [figure143, Bidirectional, credited, Strategy.exchange, Strategy.orientation]
  rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The strategy a printed form of the chapter exemplifies. -/
def strategy (d : Datum) : Option Strategy :=
  d.parse? "strategy"
    [("Extensive simplification", .extensiveSimplification),
     ("Little simplification", .littleSimplification),
     ("Express guess and negotiate meaning", .expressGuess),
     ("Display minimal grasp", .displayMinimalGrasp),
     ("Unidirectional", .unidirectional), ("Bidirectional", .bidirectional)]

/-- The community a printed form of the chapter is reported from, when it is reported from one. -/
def community (d : Datum) : Option Language :=
  d.parse? "community" [("Mainstream American", american), ("Samoan", samoan)]

-- The forms the text prints sit in the columns of Figure 14.3.
theorem rows_strategy : ∀ d ∈ Examples.all, ∀ s ∈ strategy d, ∀ l ∈ community d,
    ∃ r ∈ figure143, r.language = l ∧ ∃ c ∈ r.strategies, c.code = s := by
  decide

end Caregivers

/-! ### Witnesses -/

section Witnesses

open StructureDataset

/-- Rates of the two stances at which each gender takes up both, each favouring its own. -/
private noncomputable def stanceRates : Kernel Gender Stance :=
  Kernel.ofWeights fun g s ↦ match g, s with
    | .male, .coarseIntensity | .female, .delicateIntensity => 3
    | _, _ => 1

private instance : IsMarkovKernel stanceRates :=
  Kernel.isMarkovKernel_ofWeights (fun g ↦ ⟨.coarseIntensity, by cases g <;> simp⟩)
    (fun g s ↦ by cases g <;> cases s <;> simp)

private theorem stanceRates_lt : stanceRates .female {.coarseIntensity} <
    stanceRates .male {.coarseIntensity} := by
  have hsum : ∀ w : Stance → ℝ≥0∞, ∑ s, w s = w .coarseIntensity + w .delicateIntensity :=
    fun w ↦ by
      rw [show (Finset.univ : Finset Stance) = {.coarseIntensity, .delicateIntensity} from rfl,
        Finset.sum_pair (by decide)]
  simp only [stanceRates, Kernel.ofWeights_apply_singleton, hsum]
  rw [add_comm (1 : ℝ≥0∞) 3]
  exact ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)

/-- Each stance realized by its particle. -/
private noncomputable def particleOf : Kernel Stance Particle :=
  Kernel.deterministic (fun s ↦ match s with | .coarseIntensity => ze | .delicateIntensity => wa)
    .of_discrete

private instance : IsMarkovKernel particleOf := by unfold particleOf; infer_instance

private theorem particleOf_ze : ExclusivelyIndexes particleOf ze .coarseIntensity := fun s ↦ by
  cases s <;> simp [Indexes, particleOf, Kernel.deterministic_apply, Set.indicator, ze, wa]

-- The whole pipeline: *ze* is used by women as well as men, more by men, and exclusively by
-- neither.
example : Indexes (particleOf ∘ₖ stanceRates) ze .female ∧
    (particleOf ∘ₖ stanceRates) .female {ze} < (particleOf ∘ₖ stanceRates) .male {ze} ∧
    ¬ ExclusivelyIndexes (particleOf ∘ₖ stanceRates) ze .male := by
  have hg (g : Gender) : Indexes stanceRates Stance.coarseIntensity g :=
    Kernel.ofWeights_apply_singleton_ne_zero (by cases g <;> simp)
      (fun s ↦ by cases g <;> cases s <;> simp)
  exact ⟨particleOf_ze.indexes_comp_iff.2 (hg _), particleOf_ze.comp_apply_lt_iff.2 stanceRates_lt,
    not_exclusivelyIndexes_comp (i₁ := .male) (i₂ := .female) (by decide) ((particleOf_ze _).2 rfl)
      (hg _) (hg _)⟩

-- A catalogue that sets men's forms apart from women's is not mediated by a stance they share.
example : ¬ (Kernel.deterministic (fun g : Gender ↦ match g with | .male => ze | .female => wa)
    .of_discrete).IsGarblingOf (Kernel.const Gender (Measure.dirac Stance.coarseIntensity)) :=
  not_isGarblingOf_of_apply_eq (i := .male) (i' := .female) rfl fun h ↦ by
    have := congrArg (· {ze}) h
    simp [Kernel.deterministic_apply, Set.indicator, ze, wa] at this

-- A direct index of an identity is mediation through the identity itself.
example {I F : Type*} [MeasurableSpace I] [MeasurableSpace F] (u : Kernel I F) [IsMarkovKernel u] :
    u.IsGarblingOf Kernel.id :=
  ⟨u, inferInstance, (Kernel.comp_id u).symm⟩

/-- Each orientation yields its three strategies. -/
private noncomputable def strategyOf : Kernel Orientation Strategy :=
  Kernel.ofWeights fun o s ↦ if s.orientation = o then 1 else 0

private instance : IsFiniteKernel strategyOf := by unfold strategyOf; infer_instance

/-- Each community keeps to its own orientation. -/
private noncomputable def orientationOf : Kernel Language Orientation :=
  Kernel.deterministic (fun l ↦ if l = american then .childCentered else .otherCentered)
    .of_discrete

private instance : IsMarkovKernel orientationOf := by unfold orientationOf; infer_instance

private theorem strategyOf_exclusive (s : Strategy) :
    ExclusivelyIndexes strategyOf s s.orientation := fun o ↦
  ⟨fun h ↦ by_contra fun hne ↦ h (Kernel.ofWeights_apply_singleton_eq_zero (by simp [Ne.symm hne])),
    fun h ↦ Kernel.ofWeights_apply_singleton_ne_zero (by simp [h]) fun _ ↦ by split <;> simp⟩

-- Figure 14.3 is satisfiable: at these kernels every cell of the figure holds.
example : ∀ r ∈ figure143, ∀ r' ∈ figure143, r ≠ r' → ∀ c ∈ r.strategies,
    (strategyOf ∘ₖ orientationOf) r'.language {c.code} <
      (strategyOf ∘ₖ orientationOf) r.language {c.code} := fun r hr r' hr' hne c hc ↦
  (rows_figure_14_3 strategyOf_exclusive hr hr' hne hc).2 (by
    simp [orientationOf, Kernel.deterministic_apply, Set.indicator, samoan, american])

end Witnesses

end Ochs1992
