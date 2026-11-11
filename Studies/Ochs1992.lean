module

public import Linglib.Core.Probability.Decision.Blackwell
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Data.Examples.Ochs1992
public import Linglib.Data.Examples.Readers
public import Linglib.Data.StructureDataset.Ochs1992
public import Linglib.Fragments.Japanese.Particles
public import Linglib.Pragmatics.SocialMeaning.IndexicalField

/-!
# Ochs (1992): Indexing gender

A speaker of some social identity takes up a social meaning, a stance, act or activity, at rates
the norms of a community set, and a linguistic form realizes that meaning, so the use of a form
across identities is a composition of Markov kernels and the relations of Ochs's model are their
supports. A form indexes an identity exactly when [it directly indexes a meaning that helps to
constitute the identity](##SocialMeaning.AssociationField.indexes_ofKernel_comp), and [exclusively
only if every such meaning points to that identity alone](##exclusivelyIndexes_comp_iff). Identities
[differ in a form of one stance exactly as they differ in the
stance](##ExclusivelyIndexes.comp_apply_lt_iff), and a hearer [learns no more about a speaker from
the form than from the stance](##blackwellDominates_comp). [The indirect indexes of two Japanese
particles](##rows_figure_14_1) follow from one difference between men and women, [each cell of the
comparison of caregivers](##rows_figure_14_3) is one difference between two communities, and [a
later *maaloo* changes what a past activity has been](##credited_exchange).

## Implementation notes

* The chapter calls the relation of language to gender distributional and probabilistic and prints
  no numbers, so the kernels are arbitrary and the comparisons it states are hypotheses.
* The kernels run from identity to form, the direction of use. Indexing reads them backwards, as
  the positive associations of `SocialMeaning.AssociationField.ofKernel`: the direct relation for a
  kernel from meanings to forms, and the constitutive relation for one from identities to meanings.
  A direct index of gender is mediation through the identity itself, `Kernel.id`.
* The dashed arrows of Figure 14.2 are two-headed. A chain of kernels [through several
  domains](##indexes_comp_comp) takes one direction at a time, since closing a symmetric relation
  under transitivity would join the two voices through any stance open to both.
* The chapter names the tag question (p. 340) but prints none, so it has no row and appears only in
  a witness.
* A strategy's orientation is who accommodates in the dyad of caregiver and child, the caregiver in
  a child-centered strategy, and the child in an other-centered one.
* The comparison of rates reads the "little simplification" of Figure 14.3 and the "rarely" of
  p. 351, not the "do not use" of p. 350.

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
open SocialMeaning.AssociationField (indexes_ofKernel indexes_ofKernel_comp ofKernel)
open scoped ENNReal

/-! ### Direct and constitutive relations -/

section Model

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A form *exclusively indexes* `a` when it indexes `a` and nothing else, the strict,
presuppositional relation of pp. 339-340. -/
def ExclusivelyIndexes (κ : Kernel A B) (f : B) (a : A) : Prop :=
  ∀ a', (ofKernel κ).Indexes f a' ↔ a' = a

-- p. 340: the chapter's two senses of non-exclusive, that a form is used by both sexes and that it
-- marks other social information as well, are this one fact at the two kernels.
theorem not_exclusivelyIndexes_of_indexes {κ : Kernel A B} {f : B} {a a₁ a₂ : A} (hne : a₁ ≠ a₂)
    (h₁ : (ofKernel κ).Indexes f a₁) (h₂ : (ofKernel κ).Indexes f a₂) :
    ¬ ExclusivelyIndexes κ f a := fun h ↦
  hne (((h a₁).1 h₁).trans ((h a₂).1 h₂).symm)

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

-- p. 343: "particular social meanings may be constituted through other social meanings".
theorem indexes_comp_comp {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    (η : Kernel M F) (κ : Kernel S M) (σ : Kernel I S) :
    (ofKernel (η ∘ₖ κ ∘ₖ σ)).Indexes =
      Relation.Comp (ofKernel η).Indexes
        (Relation.Comp (ofKernel κ).Indexes (ofKernel σ).Indexes) := by
  rw [indexes_ofKernel_comp, indexes_ofKernel_comp, Relation.comp_assoc]

/-- A form exclusively indexes an identity exactly when it indexes the identity and every meaning it
directly indexes helps to constitute that identity alone, so a form used to convey anything open to
both sexes does not pragmatically presuppose either (pp. 340-341). -/
theorem exclusivelyIndexes_comp_iff :
    ExclusivelyIndexes (η ∘ₖ κ) f i ↔
      (∃ m, (ofKernel η).Indexes f m ∧ (ofKernel κ).Indexes m i) ∧
        ∀ m, (ofKernel η).Indexes f m → ∀ i', (ofKernel κ).Indexes m i' → i' = i := by
  simp only [ExclusivelyIndexes, indexes_ofKernel_comp, Relation.Comp]
  exact ⟨fun h ↦ ⟨(h i).2 rfl, fun m hm i' hi' ↦ (h i').1 ⟨m, hm, hi'⟩⟩,
    fun ⟨⟨m, hm, hi⟩, hall⟩ a' ↦ ⟨fun ⟨m', hm', ha'⟩ ↦ hall m' hm' a' ha', fun e ↦ e ▸ ⟨m, hm, hi⟩⟩⟩

-- p. 340: a form associated with an identity through a meaning open to another is not exclusive.
theorem not_exclusivelyIndexes_comp {i₁ i₂ : I} (hne : i₁ ≠ i₂) (hm : (ofKernel η).Indexes f m)
    (h₁ : (ofKernel κ).Indexes m i₁) (h₂ : (ofKernel κ).Indexes m i₂) :
    ¬ ExclusivelyIndexes (η ∘ₖ κ) f i := fun h ↦
  hne (((exclusivelyIndexes_comp_iff.1 h).2 m hm i₁ h₁).trans
    ((exclusivelyIndexes_comp_iff.1 h).2 m hm i₂ h₂).symm)

-- p. 340: a form with several meanings, such as a tag question, is used more by an identity that
-- takes up each of them at least as often and one of them more often.
theorem comp_apply_lt_of_forall_le [IsFiniteKernel η] [IsFiniteKernel κ]
    (h : ∀ m, (ofKernel η).Indexes f m → κ i {m} ≤ κ i' {m}) (hm : (ofKernel η).Indexes f m)
    (hlt : κ i {m} < κ i' {m}) :
    (η ∘ₖ κ) i {f} < (η ∘ₖ κ) i' {f} := by
  classical
  have hterm (m' : M) : κ i {m'} * η m' {f} ≤ κ i' {m'} * η m' {f} := by
    by_cases hm' : η m' {f} = 0
    · simp [hm']
    · exact mul_le_mul' (h m' (indexes_ofKernel.2 hm')) le_rfl
  rw [Kernel.comp_apply_singleton, Kernel.comp_apply_singleton,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ m),
    ← Finset.add_sum_erase _ (fun m' ↦ κ i' {m'} * η m' {f}) (Finset.mem_univ m)]
  exact ENNReal.add_lt_add_of_lt_of_le
    (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    ((ENNReal.mul_lt_mul_iff_left (indexes_ofKernel.1 hm) (measure_ne_top _ _)).2 hlt)
    (Finset.sum_le_sum fun m' _ ↦ hterm m')

namespace ExclusivelyIndexes

theorem comp_apply (h : ExclusivelyIndexes η f m) (i : I) :
    (η ∘ₖ κ) i {f} = κ i {m} * η m {f} := by
  rw [Kernel.comp_apply_singleton]
  refine Finset.sum_eq_single m (fun m' _ hm' ↦ ?_) (by simp)
  rw [show η m' {f} = 0 from by_contra fun hne ↦ hm' ((h m').1 (indexes_ofKernel.2 hne)),
    mul_zero]

-- p. 350: the identities a form indexes are settled by the community, whose kernel `κ` alone
-- decides them, so the simplified register, directly indexing accommodation in both communities,
-- indirectly indexes caregivers with children in one and members with foreign dignitaries in the
-- other.
theorem indexes_comp_iff (h : ExclusivelyIndexes η f m) :
    (ofKernel (η ∘ₖ κ)).Indexes f i ↔ (ofKernel κ).Indexes m i := by
  simp [indexes_ofKernel, h.comp_apply, indexes_ofKernel.1 ((h m).2 rfl)]

-- pp. 340-341: a form of one stance exclusively indexes an identity exactly when the stance does.
theorem comp_iff (h : ExclusivelyIndexes η f m) :
    ExclusivelyIndexes (η ∘ₖ κ) f i ↔ ExclusivelyIndexes κ m i :=
  forall_congr' fun _ ↦ by rw [h.indexes_comp_iff]

-- p. 341: the dispositions a form indexes "motivate [its] differential use by men and women".
theorem comp_apply_lt_iff [IsFiniteKernel η] (h : ExclusivelyIndexes η f m) :
    (η ∘ₖ κ) i {f} < (η ∘ₖ κ) i' {f} ↔ κ i {m} < κ i' {m} := by
  rw [h.comp_apply, h.comp_apply]
  exact ENNReal.mul_lt_mul_iff_left (indexes_ofKernel.1 ((h m).2 rfl)) (measure_ne_top _ _)

-- Two forms of one stance differ between identities in the same proportion.
theorem comp_apply_mul_comm (h : ExclusivelyIndexes η f m) (h' : ExclusivelyIndexes η f' m) :
    (η ∘ₖ κ) i {f} * (η ∘ₖ κ) i' {f'} = (η ∘ₖ κ) i' {f} * (η ∘ₖ κ) i {f'} := by
  rw [h.comp_apply, h.comp_apply, h'.comp_apply, h'.comp_apply]
  ring

end ExclusivelyIndexes

-- p. 343: a difference in a stance reaches a form through an act the stance helps to constitute.
example {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S] [IsFiniteKernel η]
    {ξ : Kernel S M} [IsFiniteKernel ξ] {σ : Kernel I S} {s : S} (h : ExclusivelyIndexes η f m)
    (h' : ExclusivelyIndexes ξ m s) :
    (η ∘ₖ ξ ∘ₖ σ) i {f} < (η ∘ₖ ξ ∘ₖ σ) i' {f} ↔ σ i {s} < σ i' {s} :=
  (h.comp_iff.2 h').comp_apply_lt_iff

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

/-- The exchange of praises over an activity of caregiver and child under an orientation: the
caregiver praises the child, and under the other-centered orientation the child, expected to answer,
praises the caregiver in turn (pp. 353-354). -/
def StructureDataset.Orientation.exchange : Orientation → List (Party × Party)
  | .childCentered => [(.caregiver, .child)]
  | .otherCentered => [(.caregiver, .child), (.child, .caregiver)]

/-- A caregiver's praise makes a past joint activity solely the child's accomplishment, and a second
*maaloo*, said later, makes the same activity jointly accomplished, so that what the activity has
been depends on talk that follows it (pp. 345, 353-354). -/
theorem credited_exchange :
    credited Orientation.childCentered.exchange = {.child} ∧
      Orientation.otherCentered.exchange =
        Orientation.childCentered.exchange ++ [(.child, .caregiver)] ∧
      credited Orientation.otherCentered.exchange = Set.univ := by
  refine ⟨?_, rfl, ?_⟩ <;> ext p <;> cases p <;> simp [credited, Orientation.exchange]

-- pp. 347, 353-354: the praising row of Figure 14.3 from the exchanges: a caregiver is credited
-- exactly under the other-centered strategy, which is exactly the bidirectional one.
theorem rows_praising : ∀ r ∈ figure143, ∀ c ∈ r.praising,
    (Bidirectional c.code.orientation.exchange ↔ c.code = .bidirectional) ∧
      (.caregiver ∈ credited c.code.orientation.exchange ↔
        c.code.orientation = .otherCentered) := by
  simp [figure143, Bidirectional, credited, Orientation.exchange, Strategy.orientation]
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
  cases s <;> simp [indexes_ofKernel, particleOf, Kernel.deterministic_apply, Set.indicator, ze, wa]

-- The whole pipeline: *ze* is used by women as well as men, more by men, and exclusively by
-- neither.
example : (ofKernel (particleOf ∘ₖ stanceRates)).Indexes ze .female ∧
    (particleOf ∘ₖ stanceRates) .female {ze} < (particleOf ∘ₖ stanceRates) .male {ze} ∧
    ¬ ExclusivelyIndexes (particleOf ∘ₖ stanceRates) ze .male := by
  have hg (g : Gender) : (ofKernel stanceRates).Indexes Stance.coarseIntensity g :=
    indexes_ofKernel.2 <| Kernel.ofWeights_apply_singleton_ne_zero (by cases g <;> simp)
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
  ⟨fun h ↦ by_contra fun hne ↦ indexes_ofKernel.1 h
      (Kernel.ofWeights_apply_singleton_eq_zero (by simp [Ne.symm hne])),
    fun h ↦ indexes_ofKernel.2 <|
      Kernel.ofWeights_apply_singleton_ne_zero (by simp [h]) fun _ ↦ by split <;> simp⟩

-- Figure 14.3 is satisfiable: at these kernels every cell of the figure holds.
example : ∀ r ∈ figure143, ∀ r' ∈ figure143, r ≠ r' → ∀ c ∈ r.strategies,
    (strategyOf ∘ₖ orientationOf) r'.language {c.code} <
      (strategyOf ∘ₖ orientationOf) r.language {c.code} := fun r hr r' hr' hne c hc ↦
  (rows_figure_14_3 strategyOf_exclusive hr hr' hne hc).2 (by
    simp [orientationOf, Kernel.deterministic_apply, Set.indicator, samoan, american])

/-- The two meanings of a tag question (p. 340), and whatever else a speaker does. -/
private inductive TagMeaning where
  | hesitancy
  | confirmationCheck
  | other
  deriving DecidableEq, Fintype

private inductive TagForm where
  | tagQuestion
  | other
  deriving DecidableEq

private instance : MeasurableSpace TagMeaning := ⊤
private instance : DiscreteMeasurableSpace TagMeaning := ⟨fun _ ↦ trivial⟩
private instance : MeasurableSpace TagForm := ⊤
private instance : DiscreteMeasurableSpace TagForm := ⟨fun _ ↦ trivial⟩

/-- A tag question conveys either of its meanings. -/
private noncomputable def tagOf : Kernel TagMeaning TagForm :=
  Kernel.deterministic (fun m ↦ match m with | .other => .other | _ => .tagQuestion) .of_discrete

private instance : IsMarkovKernel tagOf := by unfold tagOf; infer_instance

private theorem tagOf_apply (m : TagMeaning) :
    tagOf m {.tagQuestion} = if m = .other then 0 else 1 := by
  cases m <;> simp [tagOf, Kernel.deterministic_apply, Set.indicator]

private theorem sum_tagMeaning (g : TagMeaning → ℝ≥0∞) :
    ∑ m, g m = g .hesitancy + g .confirmationCheck + g .other := by
  rw [show (Finset.univ : Finset TagMeaning) = {.hesitancy, .confirmationCheck, .other} from rfl,
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), add_assoc]

-- The second sense of non-exclusive: a tag question exclusively indexes none of its meanings.
example (m : TagMeaning) : ¬ ExclusivelyIndexes tagOf .tagQuestion m :=
  not_exclusivelyIndexes_of_indexes (a₁ := .hesitancy) (a₂ := .confirmationCheck) (by decide)
    (by simp [indexes_ofKernel, tagOf_apply]) (by simp [indexes_ofKernel, tagOf_apply])

/-- Rates at which women take up hesitancy more and each gender confirmation checks alike. -/
private noncomputable def tagRates : Kernel Gender TagMeaning :=
  Kernel.ofWeights fun g m ↦ match g, m with
    | .female, .hesitancy | .male, .other => 2
    | _, _ => 1

private instance : IsFiniteKernel tagRates := by unfold tagRates; infer_instance

private theorem tagRates_apply (g : Gender) (m : TagMeaning) :
    tagRates g {m} = (match g, m with
      | .female, .hesitancy | .male, .other => 2
      | _, _ => 1) / 4 := by
  have h4 : (1 : ℝ≥0∞) + 1 + 2 = 4 := by norm_num
  have h4' : (2 : ℝ≥0∞) + 1 + 1 = 4 := by norm_num
  cases g <;> cases m <;>
    simp only [tagRates, Kernel.ofWeights_apply_singleton, sum_tagMeaning, h4, h4']

-- A difference in use follows from differences in the meanings taken together.
example :
    (tagOf ∘ₖ tagRates) .male {.tagQuestion} < (tagOf ∘ₖ tagRates) .female {.tagQuestion} := by
  have hlt : (1 : ℝ≥0∞) / 4 < 2 / 4 :=
    ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)
  refine comp_apply_lt_of_forall_le (m := .hesitancy) (fun m hm ↦ ?_)
    (by simp [indexes_ofKernel, tagOf_apply]) (by simpa only [tagRates_apply] using hlt)
  cases m with
  | hesitancy => simpa only [tagRates_apply] using hlt.le
  | confirmationCheck => simp only [tagRates_apply, le_refl]
  | other => exact absurd hm (by simp [indexes_ofKernel, tagOf_apply])

/-- Rates at which women take up only hesitancy, and men confirmation checks and other things. -/
private noncomputable def splitRates : Kernel Gender TagMeaning :=
  Kernel.ofWeights fun g m ↦ match g, m with
    | .female, .hesitancy | .male, .confirmationCheck | .male, .other => 1
    | _, _ => 0

-- But not conversely: women use the form more here though men take up one of its meanings more, so
-- `ExclusivelyIndexes.comp_apply_lt_iff` needs its hypothesis.
example : (tagOf ∘ₖ splitRates) .male {.tagQuestion} <
      (tagOf ∘ₖ splitRates) .female {.tagQuestion} ∧
    splitRates .female {.confirmationCheck} < splitRates .male {.confirmationCheck} := by
  constructor
  · norm_num [Kernel.comp_apply_singleton, sum_tagMeaning, tagOf_apply, splitRates,
      Kernel.ofWeights_apply_singleton]
  · simp [splitRates, Kernel.ofWeights_apply_singleton, sum_tagMeaning]

-- Closing a symmetric relation under transitivity joins any two things related to a common third.
example {α : Type*} {r : α → α → Prop} {m g₁ g₂ : α} (h₁ : r m g₁) (h₂ : r m g₂) :
    Relation.EqvGen r g₁ g₂ :=
  .trans _ _ _ (.symm _ _ (.rel _ _ h₁)) (.rel _ _ h₂)

end Witnesses

end Ochs1992
