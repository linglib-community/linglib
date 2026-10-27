module

public import Linglib.Core.Order.Flat
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Independence.Basic
public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Examples.SableMeyerMascarenhas2022
public import Linglib.Data.Experiments.SableMeyerMascarenhas2022
public import Linglib.Processing.Reasoning.Erotetic
public import Linglib.Semantics.Exhaustification.ConjunctiveDisjunct

/-!
# Sablé-Meyer and Mascarenhas (2022): Indirect illusory inferences from disjunction: A new bridge between deductive inference and representativeness

In an indirect illusory inference the second premise `d` matches no conjunct of the disjunctive
first premise `(a ∧ b) ∨ c` but is causally linked to `a`, and reasoners still conclude `b`
((2), (6)). Exact matching, the selection step of the mental-models account and of the erotetic
theory, certifies the classical illusion and nothing in the indirect one
(`Erotetic.indirect_not_illusory_matches`, §5.1), while acceptance tracks the normed strength of
the link, the matching case being its limit (`matching_limit`). The paper's replacement selects
the alternative the hint confirms most (§5.4): with the Difference measure and `b` independent of
`a` and `d`, the first disjunct is selected and the illusion goes through
(`indirect_illusory_bestConfirmed`), and the second disjunct never is
(`not_bestConfirmed_right`); the conjunction fallacy is the same selection over `(f ∧ b) ∨ b`
(`conjunctionFallacy_bestConfirmed`). Example (2) is a model of all three
(`brake_illusory`, `brake_not_illusory_matches`, `brake_not_bestConfirmed_attic`).

The rivals fare no better. The revised mental model theory's weak necessity certifies `b` and
`c` alike (`system2_overgenerates`, §5.2.1); its System 1, with gaps behaving as negations, reads
the premise as the strongly exhaustive (16) (`gapNegation_eq_exh`), under which the conclusion is
valid (`gapNegation_valid`, §5.2.2). Posteriors cannot separate `b` from `c` under either reading
of the disjunction (`flat_posterior`, `exclusive_posterior`), and neither conclusion is p-valid
(`not_pValid`, §5.3).

## Implementation notes

* A mental model assigns each atom a literal or a gap, a `Flat Bool` with the gap at `⊥`; model
  inclusion is the pointwise flat order.
* Selection rules are predicates on alternatives (`Erotetic.Problem.Illusory`); `BestConfirmed`
  is a strict argmax, the paper not discussing ties.
* The §5.4 argument needs `b ⟂ a` and `b ⟂ (a ∩ d)`, more than the printed "b and d are
  independent by design" and what the norming study's weak a-to-b and d-to-b ratings support;
  the supplementary proof is not in the article.
* §5.3's exclusive reading is the symmetric difference of the disjuncts, not §5.2.2's strongly
  exhaustive (16), under which the posteriors do separate the conclusions.

## TODO

* The paper notes the selection asymmetry holds for all confirmation measures of
  [tentori-crupi-bonini-osherson-2007]; only the Difference measure is formalized.
* The graded conclusion step of Experiment 2 ((10): conclude `a` from the selected `b ∧ d`
  via the causal link) has no formal account in the paper; `exp2_illusory_a` states the
  deterministic limit `d ⊆ a`.

## References

* [sable-meyer-mascarenhas-2022]
* [walsh-johnson-laird-2004]
* [johnson-laird-savary-1999]
* [koralus-mascarenhas-2013]
* [khemlani-byrne-johnson-laird-2018]
* [johnson-laird-ragni-2019]
* [spector-2007]
* [mascarenhas-2014]
* [picat-2019]
* [oaksford-chater-2007]
* [crupi-fitelson-tentori-2008]
* [tentori-crupi-bonini-osherson-2007]
* [tversky-kahneman-1983]
* [cummins-1995]
-/

@[expose] public section

namespace SableMeyerMascarenhas2022

open Set Erotetic Exhaustification MeasureTheory ProbabilityTheory

/-! ### The indirect schema (§2.3, §4) -/

section Schema

variable {W : Type*} {a b c d : Set W}

-- (10)
theorem exp2_illusory_d (hbd : (b ∩ d).Nonempty) (h : ((c ∩ b) \ d).Nonempty) :
    (disjunction b d c).Illusory (disjunction b d c).Matches d :=
  disjunction_illusory_matches hbd h

/-- In the deterministic limit `d ⊆ a`, the Experiment 2 conclusion `a` is illusory ((10)/(11)). -/
theorem exp2_illusory_a (hda : d ⊆ a) (hbd : (b ∩ d).Nonempty)
    (h : ((c ∩ b) \ a).Nonempty) :
    (disjunction b d c).Illusory (disjunction b d c).Matches a := by
  refine ⟨⟨b ∩ d, by simp [disjunction], fun _ hw ↦ hw.1,
    hbd.elim fun w ⟨hwb, hwd⟩ ↦ ⟨w, ⟨hwb, hwd⟩, hwb⟩, fun _ hw ↦ hda hw.1.2⟩, ?_⟩
  obtain ⟨w, ⟨hwc, hwb⟩, hwa⟩ := h
  exact fun hent ↦ hwa (hent (by simpa using ⟨Or.inr hwc, hwb⟩))

end Schema

/-! ### Mental models and weak necessity (§5.2.1) -/

/-- The three atoms of the schema. -/
inductive Atom
  | a | b | c
  deriving DecidableEq, Fintype

/-- A mental model: at each atom a literal, or a gap at `⊥`. -/
abbrev MentalModel := Atom → Flat Bool

/-- The model with the given literals. -/
def model (xa xb xc : Flat Bool) : MentalModel
  | .a => xa
  | .b => xb
  | .c => xc

/-- Weak necessity, as the paper states the revised theory's low-γ System 2: every model of
the conclusion is included in some model of the premises, and some model of the premises
contains no model of the conclusion. -/
def WeakNecessity (Ps C : List MentalModel) : Prop :=
  (∀ m ∈ C, ∃ m' ∈ Ps, m ≤ m') ∧ ∃ m' ∈ Ps, ∀ m ∈ C, ¬ m ≤ m'

instance (Ps C : List MentalModel) : Decidable (WeakNecessity Ps C) := by
  unfold WeakNecessity; infer_instance

/-- Strong necessity: every model of the premises includes a model of the conclusion. -/
def StrongNecessity (Ps C : List MentalModel) : Prop := ∀ m' ∈ Ps, ∃ m ∈ C, m ≤ m'

instance (Ps C : List MentalModel) : Decidable (StrongNecessity Ps C) := by
  unfold StrongNecessity; infer_instance

/-- (12): the two fully explicit models of the premises. -/
def system2Premises : List MentalModel := [model true true false, model true false true]

/-- The conclusion consisting of the one positive literal. -/
def concl (x : Atom) : List MentalModel := [Function.update ⊥ x true]

/-- Both the attractive `b` and the unattractive `c` are weak necessities of (12), so low-γ System 2
misses the asymmetry of (13) (§5.2.1). -/
theorem system2_overgenerates :
    WeakNecessity system2Premises (concl .b) ∧ WeakNecessity system2Premises (concl .c) := by
  decide

theorem system2_not_strong :
    ¬ StrongNecessity system2Premises (concl .b) ∧
      ¬ StrongNecessity system2Premises (concl .c) := by
  decide

/-! ### Gaps as negations and the strongly exhaustive reading (§5.2.2) -/

/-- (14): the System-1 models of the premise, with gaps. -/
def system1P1 : List MentalModel := [model true true ⊥, model ⊥ ⊥ true]

/-- Under model conjunction a gap behaves as a negation: fill it with `false`. -/
def fillGaps (m : MentalModel) : Atom → Bool := fun x ↦ (m x).unbotD false

-- (16)
theorem fillGaps_system1P1 :
    system1P1.map fillGaps = [fun x ↦ decide (x ≠ Atom.c), fun x ↦ decide (x = Atom.c)] := by
  simp only [system1P1, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  constructor <;> funext x <;> cases x <;> rfl

/-- Worlds are total assignments. -/
abbrev World := Atom → Bool

/-- The coordinate propositions. -/
abbrev A : Set World := {w | w .a = true}
abbrev B : Set World := {w | w .b = true}
abbrev C : Set World := {w | w .c = true}

/-- §5.2.2: the gaps-as-negations interpretation of the premise is exactly the strongly
exhaustive reading, innocent exclusion against the substitution alternatives. -/
theorem gapNegation_eq_exh :
    exhIE (conjDisjAlternatives A B C) ((A ∩ B) ∪ C) =
      {w | ∃ m ∈ system1P1, w = fillGaps m} := by
  rw [exhIE_conjDisjAlternatives ⟨fillGaps (model true true ⊥), by decide⟩
    ⟨fillGaps (model ⊥ ⊥ true), by decide⟩]
  ext w
  simp only [system1P1, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  revert w; decide

theorem gapNegation_valid : {w | ∃ m ∈ system1P1, w = fillGaps m} ∩ A ⊆ B := by
  rw [← gapNegation_eq_exh, exhIE_conjDisjAlternatives ⟨fillGaps (model true true ⊥), by decide⟩
    ⟨fillGaps (model ⊥ ⊥ true), by decide⟩]
  exact stronglyExhaustive_inter_subset

/-! ### Posteriors and p-validity (§5.3) -/

/-- The premises of the classical schema. -/
abbrev E : Set World := ((A ∩ B) ∪ C) ∩ A

/-- The premises under the exclusive reading: the symmetric difference of the disjuncts. -/
abbrev Exor : Set World := (((A ∩ B) \ C) ∪ (C \ (A ∩ B))) ∩ A

theorem flat_posterior :
    (uniformOn (univ : Set World))[|E].real B = 2 / 3 ∧
      (uniformOn (univ : Set World))[|E].real C = 2 / 3 := by
  rw [uniformOn_cond finite_univ .of_discrete, univ_inter, uniformOn_real_apply,
    uniformOn_real_apply]
  have h1 : (E ∩ B).ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h2 : (E ∩ C).ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h3 : E.ncard = 3 := by rw [Set.ncard_eq_toFinset_card']; decide
  rw [h1, h2, h3]; norm_num

theorem exclusive_posterior :
    (uniformOn (univ : Set World))[|Exor].real B = 1 / 2 ∧
      (uniformOn (univ : Set World))[|Exor].real C = 1 / 2 := by
  rw [uniformOn_cond finite_univ .of_discrete, univ_inter, uniformOn_real_apply,
    uniformOn_real_apply]
  have h1 : (Exor ∩ B).ncard = 1 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h2 : (Exor ∩ C).ncard = 1 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h3 : Exor.ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  rw [h1, h2, h3]; norm_num

/-- p-validity: the conclusion is at least as probable as the premises under every
probability distribution. -/
def PValid (E q : Set World) : Prop :=
  ∀ μ : Measure World, IsProbabilityMeasure μ → μ E ≤ μ q

theorem not_pValid_of {E q s : Set World} (hs : s.Nonempty) (hE : s ⊆ E) (hq : ¬ s ⊆ q) :
    ¬ PValid E q := fun h ↦ by
  have := isProbabilityMeasure_uniformOn s.toFinite hs
  exact hq ((uniformOn_eq_one_iff s.toFinite hs).1 (le_antisymm prob_le_one
    ((uniformOn_eq_one_of s.toFinite hs hE).symm.le.trans (h _ this))))

/-- The two fully explicit models of (12) as worlds. -/
abbrev witness : Set World := {w | ∃ m ∈ system2Premises, w = fillGaps m}

private theorem witness_subset_iff {s : Set World} :
    witness ⊆ s ↔ ∀ m ∈ system2Premises, fillGaps m ∈ s :=
  ⟨fun h m hm ↦ h ⟨m, hm, rfl⟩, fun h _ ⟨m, hm, e⟩ ↦ e ▸ h m hm⟩

/-- Neither conclusion of (12) is p-valid under either reading of the disjunction (§5.3, fn 1). -/
theorem not_pValid :
    ¬ PValid E B ∧ ¬ PValid E C ∧ ¬ PValid Exor B ∧ ¬ PValid Exor C := by
  have hw : witness.Nonempty := ⟨_, _, List.mem_cons_self, rfl⟩
  refine ⟨not_pValid_of hw ?_ ?_, not_pValid_of hw ?_ ?_, not_pValid_of hw ?_ ?_,
    not_pValid_of hw ?_ ?_⟩ <;> simp only [witness_subset_iff] <;> decide

/-! ### Confirmation and selection (§5.4) -/

section Confirmation

variable {W : Type*} [MeasurableSpace W] (μ : Measure W)

/-- The Difference measure of confirmation, `D(h, e) = P(h|e) − P(h)`. -/
noncomputable def confirmationD (h e : Set W) : ℝ := μ[|e].real h - μ.real h

/-- Selection by confirmation: the alternative whose probability the hint raises most. -/
def BestConfirmed (P : Problem W) (p : Set W) : Prop :=
  ∀ p' ∈ P.alts, p' ≠ p → confirmationD μ p' P.hint < confirmationD μ p P.hint

variable {μ} {a b c d f : Set W}

-- §5.4
theorem confirmationD_inter_eq_mul (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) :
    confirmationD μ (a ∩ b) d = μ.real b * confirmationD μ a d := by
  have h : d ∩ (a ∩ b) = a ∩ d ∩ b := by ext; simp; tauto
  rw [confirmationD, confirmationD, cond_real_apply μ hd, cond_real_apply μ hd, h,
    hadb.measureReal_inter_eq_mul, hab.measureReal_inter_eq_mul, Set.inter_comm d a]
  ring

variable [IsFiniteMeasure μ]

theorem confirmationD_eq_zero (hd : MeasurableSet d) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) :
    confirmationD μ c d = 0 := by
  have hd0 : μ.real d ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
  rw [confirmationD, cond_real_apply μ hd, Set.inter_comm, hcd.measureReal_inter_eq_mul,
    mul_div_assoc, div_self hd0, mul_one, sub_self]

-- §5.4
theorem confirmationD_inter_pos (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hb : μ b ≠ 0) (ha : 0 < confirmationD μ a d) :
    0 < confirmationD μ (a ∩ b) d := by
  rw [confirmationD_inter_eq_mul hd hab hadb]
  exact mul_pos (ENNReal.toReal_pos hb (measure_ne_top _ _)) ha

theorem indirect_bestConfirmed (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hb : μ b ≠ 0)
    (ha : 0 < confirmationD μ a d) :
    BestConfirmed μ (indirect a b c d) (a ∩ b) := by
  rintro p' hp' hne
  simp only [indirect, mem_insert_iff, mem_singleton_iff] at hp'
  rcases hp' with rfl | rfl
  · exact (hne rfl).elim
  · show confirmationD μ p' d < confirmationD μ (a ∩ b) d
    rw [confirmationD_eq_zero hd hcd h0]
    exact confirmationD_inter_pos hd hab hadb hb ha

theorem indirect_illusory_bestConfirmed (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hb : μ b ≠ 0)
    (ha : 0 < confirmationD μ a d) (hne : (a ∩ b ∩ d).Nonempty) (h : ((c ∩ d) \ b).Nonempty) :
    (indirect a b c d).Illusory (BestConfirmed μ (indirect a b c d)) b :=
  indirect_illusory (indirect_bestConfirmed hd hab hadb hcd h0 hb ha) hne h

/-- The second disjunct is never selected: the (13) asymmetry at the selection step. -/
theorem not_bestConfirmed_right (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hb : μ b ≠ 0)
    (ha : 0 < confirmationD μ a d) (hne : a ∩ b ≠ c) :
    ¬ BestConfirmed μ (indirect a b c d) c := fun h ↦
  lt_asymm (indirect_bestConfirmed hd hab hadb hcd h0 hb ha c (by simp [indirect]) hne.symm)
    (h (a ∩ b) (by simp [indirect]) hne)

/-- The conjunction fallacy (18) is the indirect schema at `(f ∧ b) ∨ b`, whose best-confirmed
option is the conjunction. -/
theorem conjunctionFallacy_bestConfirmed (hd : MeasurableSet d) (hfb : IndepSet f b μ)
    (hfdb : IndepSet (f ∩ d) b μ) (hbd : IndepSet b d μ) (h0 : μ d ≠ 0) (hb : μ b ≠ 0)
    (hf : 0 < confirmationD μ f d) : BestConfirmed μ (indirect f b b d) (f ∩ b) :=
  indirect_bestConfirmed hd hfb hfdb hbd h0 hb hf

end Confirmation

/-! ### Example (2) as a model

Seven equiprobable situations settle whether the car slowed down and whether the brake was
depressed: two with both, two with the car alone, one with the brake alone, two with neither.
Whether the guitar was out of tune and whether someone was in the attic are independent fair
coins. The brake then raises the probability that the car slowed down from 4/7 to 2/3 without
carrying the content of either alternative. -/

section Example2

/-- A situation: the car-and-brake case, the guitar, the attic. -/
abbrev Situation := Fin 7 × Bool × Bool

/-- The car slowed down. -/
abbrev car : Set Situation := {s | s.1.val < 4}

/-- The brake was depressed. -/
abbrev brake : Set Situation := {s | s.1.val < 2 ∨ s.1.val = 4}

/-- The guitar was out of tune. -/
abbrev guitar : Set Situation := {s | s.2.1 = true}

/-- Someone was in the attic. -/
abbrev attic : Set Situation := {s | s.2.2 = true}

private theorem card_situation : (Fintype.card Situation : ℝ) = 28 := by
  simp [Fintype.card_prod]

private theorem indepSet_car_guitar : IndepSet car guitar (uniformOn univ) := by
  rw [indepSet_iff_measureReal_inter_eq_mul .of_discrete .of_discrete, uniformOn_univ_real_apply,
    uniformOn_univ_real_apply, uniformOn_univ_real_apply, card_situation,
    show (car ∩ guitar).ncard = 8 by rw [Set.ncard_eq_toFinset_card']; decide,
    show car.ncard = 16 by rw [Set.ncard_eq_toFinset_card']; decide,
    show guitar.ncard = 14 by rw [Set.ncard_eq_toFinset_card']; decide]
  norm_num

private theorem indepSet_car_brake_guitar : IndepSet (car ∩ brake) guitar (uniformOn univ) := by
  rw [indepSet_iff_measureReal_inter_eq_mul .of_discrete .of_discrete, uniformOn_univ_real_apply,
    uniformOn_univ_real_apply, uniformOn_univ_real_apply, card_situation,
    show (car ∩ brake ∩ guitar).ncard = 4 by rw [Set.ncard_eq_toFinset_card']; decide,
    show (car ∩ brake).ncard = 8 by rw [Set.ncard_eq_toFinset_card']; decide,
    show guitar.ncard = 14 by rw [Set.ncard_eq_toFinset_card']; decide]
  norm_num

private theorem indepSet_attic_brake : IndepSet attic brake (uniformOn univ) := by
  rw [indepSet_iff_measureReal_inter_eq_mul .of_discrete .of_discrete, uniformOn_univ_real_apply,
    uniformOn_univ_real_apply, uniformOn_univ_real_apply, card_situation,
    show (attic ∩ brake).ncard = 6 by rw [Set.ncard_eq_toFinset_card']; decide,
    show attic.ncard = 14 by rw [Set.ncard_eq_toFinset_card']; decide,
    show brake.ncard = 12 by rw [Set.ncard_eq_toFinset_card']; decide]
  norm_num

private theorem uniformOn_ne_zero {s : Set Situation} (hs : s.Nonempty) : uniformOn univ s ≠ 0 :=
  by rw [Ne, uniformOn_eq_zero_iff finite_univ, univ_inter]; exact hs.ne_empty

theorem confirmationD_car_brake : confirmationD (uniformOn univ) car brake = 2 / 21 := by
  rw [confirmationD, uniformOn_cond finite_univ .of_discrete, univ_inter, uniformOn_real_apply,
    uniformOn_univ_real_apply, card_situation,
    show (brake ∩ car).ncard = 8 by rw [Set.ncard_eq_toFinset_card']; decide,
    show brake.ncard = 12 by rw [Set.ncard_eq_toFinset_card']; decide,
    show car.ncard = 16 by rw [Set.ncard_eq_toFinset_card']; decide]
  norm_num

/-- In problem (2), selection by confirmation makes the conclusion that the guitar was out of
tune illusory. -/
theorem brake_illusory :
    (indirect car guitar attic brake).Illusory
      (BestConfirmed (uniformOn univ) (indirect car guitar attic brake)) guitar :=
  indirect_illusory_bestConfirmed .of_discrete indepSet_car_guitar indepSet_car_brake_guitar
    indepSet_attic_brake (uniformOn_ne_zero ⟨(0, true, true), by decide⟩)
    (uniformOn_ne_zero ⟨(0, true, true), by decide⟩) (by rw [confirmationD_car_brake]; norm_num)
    ⟨(0, true, false), by decide⟩ ⟨(0, false, true), by decide⟩

/-- Exact matching certifies no conclusion in problem (2): the brake carries the content of
neither alternative. -/
theorem brake_not_illusory_matches (q : Set Situation) :
    ¬ (indirect car guitar attic brake).Illusory (indirect car guitar attic brake).Matches q :=
  indirect_not_illusory_matches ⟨(2, true, false), by decide⟩ ⟨(5, false, true), by decide⟩ q

/-- Nor does confirmation select the second disjunct of problem (2). -/
theorem brake_not_bestConfirmed_attic :
    ¬ BestConfirmed (uniformOn univ) (indirect car guitar attic brake) attic :=
  not_bestConfirmed_right .of_discrete indepSet_car_guitar indepSet_car_brake_guitar
    indepSet_attic_brake (uniformOn_ne_zero ⟨(0, true, true), by decide⟩)
    (uniformOn_ne_zero ⟨(0, true, true), by decide⟩) (by rw [confirmationD_car_brake]; norm_num)
    fun h ↦ absurd (h ▸ show ((0, true, false) : Situation) ∈ car ∩ guitar by decide) (by decide)

end Example2

/-! ### The experiments (§3, §4) -/

/-- §5: in the matching limit `P(a|d) = 1` the printed Experiment 1 regression predicts the
literature's acceptance: intercept plus slope is the printed 0.92. -/
theorem matching_limit :
    (regressions .experimentOne).intercept.map
        (·.toRat + (regressions .experimentOne).slope.toRat) =
      some matchingLimitAcceptance.toRat := by
  simp [regressions, matchingLimitAcceptance, Data.Experiments.Decimal.toRat]
  norm_num

end SableMeyerMascarenhas2022
