module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Studies.Fox2007

/-!
# Champollion, Alsop and Grosu (2019): Free Choice Disjunction as a Rational Speech Act

Free choice, by which *You may take an apple or a pear* conveys that each fruit may be taken by
itself, does not follow from modal logic, and a speaker who prefers informative utterances never
has reason to choose the disjunction over a disjunct. The paper adds semantic uncertainty: two
interpretation functions, the classical (6) and the exhaustified (7), over which the pragmatic
listener reasons jointly with states and utterances (8). The exhaustified meanings follow from
innocent exclusion at the logical forms the paper gives them, the disjunction exhaustified below
the modal, so that *or* is [true wherever one fruit may be taken by itself](##I2_or). Under the
exhaustified function a bare disjunct risks the reading *only that fruit*, so at the free-choice
states Only One and Any Number the disjunction is the speaker's safe choice
(`speaker_or_onlyOne_exh`, `speaker_prefers_a_at_onlyA_exh`), and the listener inverts the
avoidance: hearing *or*, each free-choice state outweighs each other state at the paper's α = 100
(`fci_derived`, Table 5), and the free-choice states already carry the majority at α = 2
(`fci_majority_low_alpha`).

Exclusivity, that not both may be taken, tracks the prior instead. Under a prior favouring Any
Number the listener hearing *or* ranks Any Number above every other state, at every rationality
(`anyNumber_of_prior`, Table 6), which is the paper's account of why exclusivity, unlike free
choice, is cancelable. Under negation the negated disjunction is unambiguous and maximally
strong, so the listener assigns no mass to the states at which free choice would survive
(`no_fci_under_negation`, Table 9). The variants without the conjunctive alternative
(Tables 7–8) are not formalized.

## Implementation notes

* A state is read as the set of actions it permits, among taking an apple alone, a pear alone,
  or both, as §3.1 describes them, and `◇p` holds at a state that permits some action in `p`.
  Interpretation function 1 is `◇` of each utterance's prejacent and gives the lists (6).
* Interpretation function 2 is the logical forms of footnote 3, with `exhIE` for the paper's
  innocent exclusion after [fox-2007]. The footnote writes `C` both for the alternatives of an
  exhaustifier above the modal and for those of one below it. Here the first are the four
  utterances under interpretation function 1, the second the disjunction, the disjuncts and
  their conjunction, and the alternatives `C′` of the conjunction's outer exhaustifier are the
  second set exhaustified and put under the modal. So read, the logical forms give the lists (7)
  exactly.
* The placement matters for *or*. Exhaustified above the modal against the four utterances,
  `◇(A ∨ B)` denies only `◇(A ∧ B)` and holds at Only A, Only B and Only One but not at Any
  Number, unlike (7c).

## References

* [champollion-alsop-grosu-2019]
* [franke-2011]
* [fox-2007]
* [bergen-levy-goodman-2016]
* [frank-goodman-2012]
* [kratzer-shimoyama-2002]
* [simons-2005]
-/

@[expose] public section

namespace ChampollionAlsopGrosu2019

open MeasureTheory ProbabilityTheory RSA Exhaustification
open scoped ENNReal

/-! ### States, utterances, interpretation functions (Table 2, (5)–(7)) -/

/-- The permission states of Table 2 split Franke's All True into Any Number and Only Both. -/
inductive FCState where
  | onlyA | onlyB | onlyOne | anyNumber | onlyBoth
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace FCState := ⊤
instance : DiscreteMeasurableSpace FCState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass FCState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The four utterances (5). -/
inductive Utterance where
  | a | b | or_ | and_
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Utterance := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- An interpretation function is classical modal logic or its exhaustification. -/
inductive Interp where
  | literal | exhaustified
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Interp := ⊤
instance : DiscreteMeasurableSpace Interp := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Interp := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Free choice holds when each fruit may be taken by itself. -/
def HasFCI : FCState → Prop
  | .onlyOne | .anyNumber => True
  | _ => False

instance : DecidablePred HasFCI
  | .onlyA | .onlyB | .onlyBoth => .isFalse id
  | .onlyOne | .anyNumber => .isTrue trivial

/-- What a permission can be used for: an apple alone, a pear alone, or both fruit. -/
inductive Action where
  | apple | pear | both
  deriving DecidableEq, Fintype

/-- The actions a state permits. -/
def permitted : FCState → Set Action
  | .onlyA => {.apple}
  | .onlyB => {.pear}
  | .onlyOne => {.apple, .pear}
  | .anyNumber => Set.univ
  | .onlyBoth => {.both}

/-- Deontic accessibility relates a state to the actions it permits, so `◇p` is
`access.preimage p`. -/
def access : SetRel FCState Action := {p | p.2 ∈ permitted p.1}

/-- Taking an apple, alone or with a pear. -/
def takeApple : Set Action := {.apple, .both}

/-- Taking a pear, alone or with an apple. -/
def takePear : Set Action := {.pear, .both}

/-- The proposition each utterance (5) puts under the modal. -/
def prejacent : Utterance → Set Action
  | .a => takeApple
  | .b => takePear
  | .or_ => takeApple ∪ takePear
  | .and_ => takeApple ∩ takePear

/-- (6): Interpretation function 1 is classical modal logic, `◇` of the prejacent. -/
def I1 (u : Utterance) : Set FCState := access.preimage (prejacent u)

/-- The alternatives of the embedded exhaustifier: the disjunction, the disjuncts and their
conjunction. -/
def embeddedAlts : Set (Set Action) :=
  {takeApple ∪ takePear, takeApple, takePear, takeApple ∩ takePear}

/-- (7): Interpretation function 2, by the logical forms of footnote 3. A disjunct is
exhaustified above the modal against the utterances under interpretation function 1, the
disjunction below it, and the conjunction below it and then above it against the embedded
exhaustifications of the alternatives under the modal. -/
def I2 : Utterance → Set FCState
  | .a => exhIE {I1 .or_, I1 .a, I1 .b, I1 .and_} (I1 .a)
  | .b => exhIE {I1 .or_, I1 .a, I1 .b, I1 .and_} (I1 .b)
  | .or_ => access.preimage (exhIE embeddedAlts (takeApple ∪ takePear))
  | .and_ => exhIE ((access.preimage ∘ exhIE embeddedAlts) '' embeddedAlts)
      (access.preimage (exhIE embeddedAlts (takeApple ∩ takePear)))

@[simp] private theorem mem_access {s : FCState} {x : Action} :
    (s, x) ∈ access ↔ x ∈ permitted s :=
  Iff.rfl

private theorem isDiamond_I1 : Fox2007.IsDiamond (I1 .or_) (I1 .a) (I1 .b) (I1 .and_) :=
  Fox2007.isDiamond_sauerlandAlt (O := access.preimage) SetRel.preimage_mono
    (SetRel.preimage_union ..).le
    ⟨.onlyA, by simp [permitted, takeApple, takePear]⟩
    ⟨.onlyB, by simp [permitted, takeApple, takePear]⟩

private theorem isDiamond_embeddedAlts :
    Fox2007.IsDiamond (takeApple ∪ takePear) takeApple takePear (takeApple ∩ takePear) :=
  Fox2007.isDiamond_or ⟨.apple, by simp [takeApple, takePear]⟩
    ⟨.pear, by simp [takeApple, takePear]⟩

-- (6a)
theorem I1_a : I1 .a = {.onlyA, .onlyOne, .anyNumber, .onlyBoth} := by
  ext s; cases s <;> simp [I1, prejacent, permitted, takeApple]

-- (6b)
theorem I1_b : I1 .b = {.onlyB, .onlyOne, .anyNumber, .onlyBoth} := by
  ext s; cases s <;> simp [I1, prejacent, permitted, takePear]

-- (6c)
theorem I1_or : I1 .or_ = Set.univ := by
  ext s; cases s <;> simp [I1, prejacent, permitted, takeApple, takePear]

-- (6d)
theorem I1_and : I1 .and_ = {.anyNumber, .onlyBoth} := by
  ext s; cases s <;> simp [I1, prejacent, permitted, takeApple, takePear]

-- (7a)
theorem I2_a : I2 .a = {.onlyA} := by
  rw [I2, isDiamond_I1.exhIE_s, I1_a, I1_b]
  ext s; cases s <;> simp

-- (7b)
theorem I2_b : I2 .b = {.onlyB} := by
  rw [I2, isDiamond_I1.exhIE_n, I1_a, I1_b]
  ext s; cases s <;> simp

-- (7c)
theorem I2_or : I2 .or_ = {.onlyA, .onlyB, .onlyOne, .anyNumber} := by
  rw [I2, embeddedAlts, isDiamond_embeddedAlts.exhIE_w]
  ext s
  cases s <;> simp [permitted, takeApple, takePear]
  decide

-- (7d)
theorem I2_and : I2 .and_ = {.onlyBoth} := by
  have h := isDiamond_embeddedAlts
  have hC : (access.preimage ∘ exhIE embeddedAlts) '' embeddedAlts =
      {access.preimage ((takeApple ∪ takePear) \ (takeApple ∩ takePear)),
        access.preimage (takeApple \ takePear), access.preimage (takePear \ takeApple),
        access.preimage (takeApple ∩ takePear)} := by
    simp only [embeddedAlts, Set.image_insert_eq, Set.image_singleton, Function.comp_apply,
      h.exhIE_w, h.exhIE_s, h.exhIE_n, h.exhIE_e]
  have hM : IsMinimalCover
      {access.preimage ((takeApple ∪ takePear) \ (takeApple ∩ takePear)),
        access.preimage (takeApple \ takePear), access.preimage (takePear \ takeApple),
        access.preimage (takeApple ∩ takePear)}
      (access.preimage (takeApple ∩ takePear)) {.onlyBoth} := by
    refine .singleton (by simp [permitted, takeApple, takePear]) fun q hq hq₀ ↦ ?_
    rcases hq with rfl | rfl | rfl | rfl <;>
      first | exact subset_rfl | simp [permitted, takeApple, takePear] at hq₀
  rw [I2, hC, embeddedAlts, h.exhIE_e, hM.exhIE_eq]
  ext s; cases s <;> simp [permitted, takeApple, takePear]

theorem I2_subset_I1 : ∀ u, I2 u ⊆ I1 u
  | .a | .b => exhIE_subset _ _
  | .or_ => SetRel.preimage_mono (exhIE_subset _ _)
  | .and_ => (exhIE_subset _ _).trans (SetRel.preimage_mono (exhIE_subset _ _))

/-- Meaning indexed by interpretation function. -/
def interpMeaning : Interp → Utterance → Set FCState
  | .literal => I1
  | .exhaustified => I2

/-- Membership in a set proved equal to a finset is decided by the finset. -/
abbrev decidableMemOfEq {s : Set FCState} (F : Finset FCState) (h : s = ↑F) :
    DecidablePred (· ∈ s) :=
  fun w ↦ decidable_of_iff (w ∈ F) (by rw [h]; exact Finset.mem_coe.symm)

/-- Membership in a meaning is decided by the lists (6) and (7) it is proved equal to. -/
instance : ∀ i u, DecidablePred (· ∈ interpMeaning i u)
  | .literal, .a =>
    decidableMemOfEq {.onlyA, .onlyOne, .anyNumber, .onlyBoth} (by simp [interpMeaning, I1_a])
  | .literal, .b =>
    decidableMemOfEq {.onlyB, .onlyOne, .anyNumber, .onlyBoth} (by simp [interpMeaning, I1_b])
  | .literal, .or_ => decidableMemOfEq Finset.univ (by simp [interpMeaning, I1_or])
  | .literal, .and_ => decidableMemOfEq {.anyNumber, .onlyBoth} (by simp [interpMeaning, I1_and])
  | .exhaustified, .a => decidableMemOfEq {.onlyA} (by simp [interpMeaning, I2_a])
  | .exhaustified, .b => decidableMemOfEq {.onlyB} (by simp [interpMeaning, I2_b])
  | .exhaustified, .or_ =>
    decidableMemOfEq {.onlyA, .onlyB, .onlyOne, .anyNumber} (by simp [interpMeaning, I2_or])
  | .exhaustified, .and_ => decidableMemOfEq {.onlyBoth} (by simp [interpMeaning, I2_and])

/-- The extension of each utterance under each interpretation function. -/
def sem (i : Interp) (u : Utterance) : Finset FCState :=
  Finset.univ.filter (· ∈ interpMeaning i u)

@[simp] theorem mem_sem {i : Interp} {u : Utterance} {w : FCState} :
    w ∈ sem i u ↔ w ∈ interpMeaning i u := by simp [sem]

/-! ### The model (8) -/

/-- The literal listener under an interpretation function (8a) conditions the state prior on the
meaning of the utterance. -/
noncomputable abbrev literal (μ : Measure FCState) (i : Interp) : Kernel Utterance FCState :=
  RSA.listener μ (truthful fun u ↦ (sem i u : Set FCState))

/-- The speaker under an interpretation function (8b) knows the state and addresses that
function's literal listener. -/
noncomputable abbrev speaker (μ : Measure FCState) (i : Interp) (α : ℝ) :
    Kernel FCState Utterance :=
  RSA.speaker α 0 (literal μ i) Measure.dirac

/-- The uniform prior over the states. -/
local notation "υ" => uniformOn (Set.univ : Set FCState)

/-- The pragmatic listener (8c) at a uniform prior over states and interpretation functions
inverts the speaker of each function, and her first marginal is her belief about the state. -/
noncomputable abbrev listener (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  RSA.listener (uniformOn Set.univ) fun p : FCState × Interp ↦ speaker υ p.2 α p.1

/-- Under the exhaustified function at Only One, *or* is the only true utterance, so the
speaker produces it with certainty at every rationality (§3.3). -/
theorem speaker_or_onlyOne_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .onlyOne {.or_} = 1 :=
  speaker_listener_truthful_dirac_eq_one hα _ _ _ (uniformOn_univ_singleton_ne_zero _) (by decide)
    (by decide)

theorem speaker_or_anyNumber_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .anyNumber {.or_} = 1 :=
  speaker_listener_truthful_dirac_eq_one hα _ _ _ (uniformOn_univ_singleton_ne_zero _) (by decide)
    (by decide)

theorem speaker_or_onlyBoth_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .onlyBoth {.or_} = 0 :=
  speaker_listener_truthful_dirac_apply_singleton_eq_zero hα _ _ _ (by decide)

/-- Under the exhaustified function at Only A the speaker prefers the bare disjunct to the
disjunction at every rationality, the avoidance mechanism. -/
theorem speaker_prefers_a_at_onlyA_exh {α : ℝ} (hα : 0 < α) :
    (speaker υ .exhaustified α .onlyA).real {.or_} <
      (speaker υ .exhaustified α .onlyA).real {.a} :=
  speaker_uniformOn_dirac_real_singleton_lt_of_card_lt _ hα (by decide) (by decide) (by decide)

/-- Hearing *or* at α = 100, the listener ranks each free-choice state above each of Only A, Only B
and Only Both (Table 5). -/
theorem fci_derived :
    ∀ w ∈ ({.onlyA, .onlyB, .onlyBoth} : Finset FCState),
      ∀ w' ∈ ({.onlyOne, .anyNumber} : Finset FCState),
        (listener 100 .or_).fst.real {w} < (listener 100 .or_).fst.real {w'} := by
  intro w hw w' hw'
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton]
  fin_cases hw <;> fin_cases hw' <;>
    exact listener_uniformOn_family_real_lt_of_divPowSum sem (k := 100) (D := 20)
      (by decide +kernel) (by decide +kernel)

/-- The free-choice pairs of the joint listener. -/
def fciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => HasFCI p.1

/-- The remaining pairs. -/
def nonFciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => ¬ HasFCI p.1

/-- At α = 2 the free-choice states still carry the majority of the posterior given *or*
(the paper's "only 70%"). -/
theorem fci_majority_low_alpha :
    (listener 2 .or_).real ↑nonFciPairs < (listener 2 .or_).real ↑fciPairs :=
  listener_uniformOn_family_real_lt_of_divPowSum sem (k := 2) (D := 20) (by decide +kernel)
    (by decide +kernel)

/-! ### Prior sensitivity (Table 6)

The prior enters the literal listener (8a) and the pragmatic listener (8c) alike. -/

/-- These prior weights favour Any Number, 12 against 1 for each other state (75%). -/
def biasedWeight : FCState → ℕ
  | .anyNumber => 12
  | _ => 1

/-- The state prior. -/
noncomputable def priorB : Measure FCState := ∑ w, (biasedWeight w : ℝ≥0∞) • Measure.dirac w

/-- The joint prior, the interpretation function drawn uniformly. -/
noncomputable def jointPriorB : Measure (FCState × Interp) :=
  ∑ p, (biasedWeight p.1 : ℝ≥0∞) • Measure.dirac p

theorem priorB_singleton (w : FCState) : priorB {w} = biasedWeight w :=
  Measure.sum_smul_dirac_apply_singleton (fun w => (biasedWeight w : ℝ≥0∞)) w

theorem jointPriorB_singleton (p : FCState × Interp) : jointPriorB {p} = biasedWeight p.1 :=
  Measure.sum_smul_dirac_apply_singleton (fun p : FCState × Interp => (biasedWeight p.1 : ℝ≥0∞)) p

instance : IsFiniteMeasure priorB :=
  ⟨by
    rw [priorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun w _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

instance : IsFiniteMeasure jointPriorB :=
  ⟨by
    rw [jointPriorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun p _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

/-- The pragmatic listener at the biased prior. -/
noncomputable def listenerB (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  RSA.listener jointPriorB fun p ↦ speaker priorB p.2 α p.1

theorem jointPriorB_real_singleton (p : FCState × Interp) :
    jointPriorB.real {p} = biasedWeight p.1 := by
  rw [measureReal_def, jointPriorB_singleton, ENNReal.toReal_natCast]

/-- With 75% of the prior on Any Number, the listener hearing *or* ranks Any Number above every
other state at every rationality (Table 6). -/
theorem anyNumber_of_prior {α : ℝ} (hα : 0 < α) {w : FCState} (hw : w ≠ .anyNumber) :
    (listenerB α .or_).fst.real {w} < (listenerB α .or_).fst.real {.anyNumber} := by
  have hμ : priorB {.anyNumber} ≠ 0 := by rw [priorB_singleton]; simp [biasedWeight]
  have hone : speaker priorB .exhaustified α .anyNumber {.or_} = 1 :=
    speaker_listener_truthful_dirac_eq_one hα _ _ _ hμ (by decide) (by decide)
  have hlt : (∑ p ∈ ({w} ×ˢ Finset.univ : Finset (FCState × Interp)), jointPriorB.real {p})
      < jointPriorB.real {(.anyNumber, .exhaustified)} := by
    rw [Finset.sum_product, Finset.sum_singleton]
    simp only [jointPriorB_real_singleton, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      show Fintype.card Interp = 2 from rfl]
    cases w <;> first | exact absurd rfl hw | norm_num [biasedWeight]
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton, listenerB]
  exact listener_real_lt_of_certain _ _ (w₀ := ((.anyNumber, .exhaustified) : FCState × Interp))
    (by simp) (fun p ↦ speaker_real_singleton_le_one α 0 (literal priorB p.2) Measure.dirac p.1 _)
    hone hlt

/-! ### No free choice under negation (§4, Table 9) -/

/-- The states of the negation model. -/
inductive NegState where
  | onlyA | onlyB | onlyOne | neither
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegState := ⊤
instance : DiscreteMeasurableSpace NegState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The negated utterances (10). -/
inductive NegUtterance where
  | notA | notB | notOr | notAnd
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegUtterance := ⊤
instance : DiscreteMeasurableSpace NegUtterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegUtterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Interpretation function 1 under negation (11). -/
def N1 : NegUtterance → NegState → Prop
  | .notA, .onlyB | .notA, .neither => True
  | .notA, _ => False
  | .notB, .onlyA | .notB, .neither => True
  | .notB, _ => False
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

/-- Under negation, interpretation function 2 (12) weakens rather than strengthens. -/
def N2 : NegUtterance → NegState → Prop
  | .notA, .onlyA => False
  | .notA, _ => True
  | .notB, .onlyB => False
  | .notB, _ => True
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

instance : ∀ u, DecidablePred (N1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

instance : ∀ u, DecidablePred (N2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- The negated meanings indexed by interpretation function. -/
def negMeaning : Interp → NegUtterance → NegState → Prop
  | .literal => N1
  | .exhaustified => N2

instance : ∀ i u, DecidablePred (negMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (N1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (N2 u))

/-- The extensions of the negation model. -/
def negSem (i : Interp) (u : NegUtterance) : Finset NegState :=
  Finset.univ.filter (negMeaning i u)

@[simp] theorem mem_negSem {i : Interp} {u : NegUtterance} {w : NegState} :
    w ∈ negSem i u ↔ negMeaning i u w := by simp [negSem]

theorem negSem_notOr : ∀ i, negSem i .notOr = {.neither} := by decide

/-- The listener of the negation model. -/
noncomputable abbrev negListener (α : ℝ) : Kernel NegUtterance (NegState × Interp) :=
  RSA.listener (uniformOn Set.univ) fun p : NegState × Interp ↦ RSA.speaker α 0
    (RSA.listener (uniformOn Set.univ) (truthful fun u ↦ (negSem p.2 u : Set NegState)))
    Measure.dirac p.1

/-- Hearing *you may not take an apple or a pear*, the listener assigns no mass to any state but
Neither, so there is no free choice under negation (Table 9). -/
theorem no_fci_under_negation {α : ℝ} (hα : 0 < α) {p : NegState × Interp}
    (hp : p.1 ≠ .neither) : negListener α .notOr {p} = 0 :=
  listener_apply_singleton_eq_zero (speaker_listener_truthful_dirac_apply_singleton_eq_zero hα _ _
    _ (by rw [negSem_notOr]; simpa using hp))

end ChampollionAlsopGrosu2019
