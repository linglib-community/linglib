module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Core.MeasureTheory.Measure.AE

/-!
# Anderson (2021): Tell Me Everything You Know

A single RSA turn leaves no trace. Anderson makes the common ground a distribution over
worlds, substitutes it for the world prior of every agent in the chain (the literal
listener conditions the common ground on the utterance, the pragmatic listener inverts the
speaker against it), and after each turn increments it with the pragmatic listener's
posterior, discounted by a learning rate. Worlds can then regain probability, since the update
is a mixture and not an intersection, which is its limit at learning rate one: the update joins
the common ground with the posterior's (`ae_updateCG`) where Stalnaker's assertion meets it, and a
speaker
whose literal listener reads the common ground prefers what is new to what is already
established. Observations are sampled from the speaker's private beliefs: by weight,
above a confidence threshold (a speaker with nothing to say passes with the null utterance),
or by their positive difference from the common ground. On the MutualFriends worlds,
*they like being outdoors* leaves Nancy and Katie tied at the first turn and
favours Nancy once *they study a humanity* is in the common ground.

## References

* [anderson-2021]
* [frank-goodman-2012]
* [stalnaker-2002]
-/

@[expose] public section

namespace Anderson2021

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

/-! ### Updating the common ground -/

section Update

variable {W : Type*} [MeasurableSpace W]

/-- The common ground of §6 is incremented by the pragmatic listener's posterior, discounted by
the learning rate `lr`, as the convex mixture of the two. -/
noncomputable def updateCG (cg post : Measure W) (lr : ℝ≥0) : Measure W :=
  (1 - lr) • cg + lr • post

instance (cg post : Measure W) [IsFiniteMeasure cg] [IsFiniteMeasure post] (lr : ℝ≥0) :
    IsFiniteMeasure (updateCG cg post lr) :=
  inferInstanceAs (IsFiniteMeasure ((1 - lr) • cg + lr • post))

theorem updateCG_apply (cg post : Measure W) (lr : ℝ≥0) (s : Set W) :
    updateCG cg post lr s = ((1 - lr : ℝ≥0) : ℝ≥0∞) * cg s + (lr : ℝ≥0∞) * post s := by
  rw [updateCG, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
    ENNReal.smul_def, smul_eq_mul, smul_eq_mul]

theorem updateCG_zero (cg post : Measure W) : updateCG cg post 0 = cg := by
  rw [updateCG, tsub_zero, one_smul, zero_smul, add_zero]

theorem updateCG_one (cg post : Measure W) : updateCG cg post 1 = post := by
  rw [updateCG, tsub_self, zero_smul, one_smul, zero_add]

theorem notMem_contextSet_updateCG_one (cg post : Measure W) {w : W} (h : post {w} = 0) :
    w ∉ (ae (updateCG cg post 1)).ker := by
  rw [updateCG_one, ker_ae]
  exact fun hw => hw h

/-- Below learning rate one the prior keeps every world it supports, so a world the posterior
rules out can regain probability (footnote 7). -/
theorem mem_contextSet_updateCG (cg post : Measure W) {lr : ℝ≥0} (hlr : lr < 1) {w : W}
    (hcg : cg {w} ≠ 0) : w ∈ (ae (updateCG cg post lr)).ker := by
  rw [ker_ae]
  show updateCG cg post lr {w} ≠ 0
  rw [updateCG_apply]
  exact fun h => hcg ((mul_eq_zero.mp (add_eq_zero.mp h).1).resolve_left
    (ENNReal.coe_ne_zero.mpr (tsub_pos_of_lt hlr).ne'))

/-- Strictly between learning rates `0` and `1` the update joins the prior's almost-everywhere
filter with the posterior's, where Stalnaker's assertion would meet them. -/
theorem ae_updateCG (cg post : Measure W) {lr : ℝ≥0} (h0 : lr ≠ 0) (h1 : lr < 1) :
    ae (updateCG cg post lr) = ae cg ⊔ ae post := by
  rw [updateCG, ae_add_measure_eq, Measure.ae_smul_measure_eq (tsub_pos_of_lt h1).ne',
    Measure.ae_smul_measure_eq h0]

/-- The context set of the update is the union of the prior's and the posterior's. -/
theorem ker_ae_updateCG (cg post : Measure W) {lr : ℝ≥0} (h0 : lr ≠ 0) (h1 : lr < 1) :
    (ae (updateCG cg post lr)).ker = (ae cg).ker ∪ (ae post).ker := by
  rw [ae_updateCG cg post h0 h1, Filter.ker_sup]

/-! ### Selecting observations (§7) -/

/-- In weighted sampling a world's weight is its probability under the speaker's beliefs. -/
noncomputable def weightedSample (bel : Measure W) (w : W) : ℝ := bel.real {w}

/-- Thresholded sampling drops the worlds below the confidence threshold. -/
noncomputable def thresholdedSample (bel : Measure W) (θ : ℝ) (w : W) : ℝ :=
  if θ ≤ bel.real {w} then bel.real {w} else 0

/-- In difference-based sampling a world's weight is its positive gain over the common ground,
since reductions are not assertable (footnote 14). -/
noncomputable def differenceSample (bel cg : Measure W) (w : W) : ℝ :=
  max 0 (bel.real {w} - cg.real {w})

/-- A speaker with uniform beliefs weights every world alike — the noncommittal speaker of
Figure 12. -/
theorem weightedSample_uniformOn [Fintype W] [MeasurableSingletonClass W] (w w' : W) :
    weightedSample (uniformOn Set.univ) w = weightedSample (uniformOn Set.univ) w' := by
  simp [weightedSample, uniformOn_univ_real_singleton]

/-- A threshold above one drops every world, and the speaker passes (Figure 13). -/
theorem thresholdedSample_eq_zero (bel : Measure W) [IsProbabilityMeasure bel] {θ : ℝ}
    (hθ : 1 < θ) (w : W) : thresholdedSample bel θ w = 0 :=
  ite_eq_right (not_le.mpr (lt_of_le_of_lt measureReal_le_one hθ))

/-- Beliefs already in the common ground contribute nothing (Figure 14). -/
theorem differenceSample_self (cg : Measure W) (w : W) : differenceSample cg cg w = 0 := by
  simp [differenceSample]

theorem differenceSample_pos {bel cg : Measure W} {w : W} (h : cg.real {w} < bel.real {w}) :
    0 < differenceSample bel cg w :=
  lt_max_of_lt_right (sub_pos.2 h)

end Update

/-! ### The MutualFriends worlds -/

/-- The four individuals of Figure 3. -/
inductive World
  | ina
  | katie
  | nancy
  | sally
  deriving DecidableEq, Fintype

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ => trivial⟩
instance : Nonempty World := ⟨.ina⟩

inductive Major
  | astronomy
  | german
  deriving DecidableEq

inductive Location
  | indoors
  | outdoors
  deriving DecidableEq

def World.major : World → Major
  | .ina | .katie => .astronomy
  | .nancy | .sally => .german

def World.location : World → Location
  | .ina | .sally => .indoors
  | .katie | .nancy => .outdoors

/-- The utterances of Figure 5, plus the null utterance of §7.1.1. -/
inductive Utterance
  | studyHumanity
  | studyScience
  | likeIndoors
  | likeOutdoors
  | null
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩

def Utterance.holds : Utterance → World → Prop
  | .studyHumanity, w => w.major = .german
  | .studyScience, w => w.major = .astronomy
  | .likeIndoors, w => w.location = .indoors
  | .likeOutdoors, w => w.location = .outdoors
  | .null, _ => True

instance (u : Utterance) : DecidablePred u.holds := fun _ => by
  cases u <;> unfold Utterance.holds <;> infer_instance

/-- The extension of each utterance. -/
def sem (u : Utterance) : Finset World := Finset.univ.filter u.holds

/-- The extension as a set. -/
abbrev semSet (u : Utterance) : Set World := ↑(sem u)

/-! ### The Figure-4 agents at a common ground -/

/-- The literal listener conditions the common ground on the utterance. -/
noncomputable abbrev L0 (cg : Measure World) : Kernel Utterance World :=
  listener cg (truthful semSet)

/-- The pragmatic speaker, without softmax terms or costs (footnote 3). -/
noncomputable abbrev S1 (cg : Measure World) : Kernel World Utterance :=
  speaker 1 0 (L0 cg) Measure.dirac

/-- The pragmatic listener inverts the speaker against the common ground. -/
noncomputable abbrev L1 (cg : Measure World) : Kernel Utterance World :=
  listener cg (S1 cg)

/-- In one Figure-2 turn the listener's posterior is mixed into the common ground unless the
speaker passed (§7.1.1). -/
noncomputable def step (cg : Measure World) [IsFiniteMeasure cg] (u : Utterance) (lr : ℝ≥0) :
    Measure World :=
  if u = .null then cg else updateCG cg (L1 cg u) lr

section Agents

variable {cg : Measure World}

theorem L1_apply_singleton_eq_zero {u : Utterance} {w : World} (hw : w ∉ sem u) :
    L1 cg u {w} = 0 :=
  listener_apply_singleton_eq_zero (speaker_dirac_apply_singleton_eq_zero one_pos
    (listener_truthful_apply_singleton_of_notMem cg semSet (Finset.mem_coe.not.mpr hw)))

theorem S1_real_singleton (w : World) (u : Utterance) :
    (S1 cg w).real {u} = (L0 cg u {w}).toReal / ∑ u', (L0 cg u' {w}).toReal := by
  rw [S1, speaker_dirac_zero_real_singleton zero_le_one]
  simp only [ENNReal.rpow_one]

theorem L0_toReal_of_notMem {u : Utterance} {w : World} (hw : w ∉ sem u) :
    (L0 cg u {w}).toReal = 0 := by
  rw [listener_truthful_apply_singleton_of_notMem cg semSet (Finset.mem_coe.not.mpr hw),
    ENNReal.toReal_zero]

variable [IsFiniteMeasure cg]

theorem L0_apply_singleton_ne_zero {u : Utterance} {w : World} (hw : w ∈ sem u)
    (hcg : cg {w} ≠ 0) : L0 cg u {w} ≠ 0 := by
  rw [listener_truthful_apply_singleton cg semSet (Finset.mem_coe.mpr hw)]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hcg

theorem S1_apply_singleton_ne_zero {u : Utterance} {w : World} (hw : w ∈ sem u)
    (hcg : cg {w} ≠ 0) : S1 cg w {u} ≠ 0 :=
  speaker_dirac_apply_singleton_ne_zero zero_le_one (L0_apply_singleton_ne_zero hw hcg)

theorem L1_apply_singleton_ne_zero {u : Utterance} {w : World} (hw : w ∈ sem u)
    (hcg : cg {w} ≠ 0) : L1 cg u {w} ≠ 0 :=
  listener_apply_singleton_ne_zero hcg (S1_apply_singleton_ne_zero hw hcg)

theorem L0_toReal {u : Utterance} {w : World} (hw : w ∈ sem u) :
    (L0 cg u {w}).toReal = cg.real {w} / ∑ x ∈ sem u, cg.real {x} := by
  rw [listener_truthful_apply_singleton cg semSet (Finset.mem_coe.mpr hw),
    ENNReal.toReal_mul,
    ENNReal.toReal_inv, sum_measureReal_singleton, measureReal_def, measureReal_def,
    inv_mul_eq_div]

end Agents

/-! ### The first turn -/

/-- The empty common ground (Figure 2). -/
noncomputable abbrev cg₁ : Measure World := uniformOn Set.univ

/-- The first speaker never produces a false utterance, prefers a specific true utterance to
the null one, and ties the two specific true utterances. -/
theorem s1_turn1_informativity :
    (S1 cg₁ .nancy).real {.studyScience} = 0 ∧
    (S1 cg₁ .nancy).real {.null} < (S1 cg₁ .nancy).real {.studyHumanity} ∧
    (S1 cg₁ .nancy).real {.studyHumanity} = (S1 cg₁ .nancy).real {.likeOutdoors} := by
  refine ⟨speaker_listener_truthful_dirac_real_singleton_eq_zero one_pos _ _ _ (by decide),
    speaker_uniformOn_dirac_real_singleton_lt_of_card_lt sem one_pos (by decide) (by decide)
      (by decide), ?_⟩
  rw [speaker_uniformOn_dirac_real_singleton sem one_pos,
    speaker_uniformOn_dirac_real_singleton sem one_pos, ite_eq_left (by decide),
    ite_eq_left (by decide), show (sem .studyHumanity).card = (sem .likeOutdoors).card by decide]

theorem profile_eq (w w' : World) : profile sem Finset.univ w = profile sem Finset.univ w' := by
  cases w <;> cases w' <;> decide

theorem l1_turn1_inferences :
    L1 cg₁ .studyHumanity {.ina} = 0 ∧ L1 cg₁ .studyHumanity {.nancy} ≠ 0 ∧
    L1 cg₁ .likeOutdoors {.katie} = L1 cg₁ .likeOutdoors {.nancy} :=
  ⟨L1_apply_singleton_eq_zero (by decide),
    L1_apply_singleton_ne_zero (by decide) (uniformOn_univ_singleton_ne_zero _),
    listener_apply_singleton_congr _ _
      (speaker_uniformOn_dirac_apply_singleton_of_profile_eq sem one_pos (profile_eq _ _)
        (u := .likeOutdoors) (by decide) (by decide))
      (uniformOn_univ_singleton_eq _ _)⟩

theorem l1_null_uniform (w w' : World) : L1 cg₁ .null {w} = L1 cg₁ .null {w'} :=
  listener_apply_singleton_congr _ _
    (speaker_uniformOn_dirac_apply_singleton_of_profile_eq sem one_pos (profile_eq _ _) (u := .null)
      (by cases w <;> decide) (by cases w' <;> decide))
    (uniformOn_univ_singleton_eq _ _)

/-! ### The second turn -/

/-- The common ground after *they study a humanity* at learning rate 0.2 (footnote 9). -/
noncomputable def cg₂ : Measure World := updateCG cg₁ (L1 cg₁ .studyHumanity) (1/5)

instance : IsFiniteMeasure cg₂ := inferInstanceAs (IsFiniteMeasure (updateCG _ _ _))

theorem cg₂_ina_eq_katie : cg₂ {.ina} = cg₂ {.katie} := by
  rw [cg₂, updateCG_apply, updateCG_apply, uniformOn_univ_singleton_eq World.ina .katie,
    L1_apply_singleton_eq_zero (by decide), L1_apply_singleton_eq_zero (by decide)]

theorem cg₂_nancy_eq_sally : cg₂ {.nancy} = cg₂ {.sally} := by
  have h : L1 cg₁ .studyHumanity {.nancy} = L1 cg₁ .studyHumanity {.sally} :=
    listener_apply_singleton_congr _ _
      (speaker_uniformOn_dirac_apply_singleton_of_profile_eq sem one_pos (profile_eq _ _)
        (u := .studyHumanity) (by decide) (by decide))
      (uniformOn_univ_singleton_eq _ _)
  rw [cg₂, updateCG_apply, updateCG_apply, uniformOn_univ_singleton_eq World.nancy .sally, h]

theorem cg₂_ina_ne_zero : cg₂ {.ina} ≠ 0 := by
  rw [cg₂, updateCG_apply]
  exact fun h => uniformOn_univ_singleton_ne_zero _
    ((mul_eq_zero.mp (add_eq_zero.mp h).1).resolve_left
    (ENNReal.coe_ne_zero.mpr (tsub_pos_of_lt (by norm_num)).ne'))

theorem cg₂_ina_lt_nancy : cg₂ {.ina} < cg₂ {.nancy} := by
  rw [cg₂, updateCG_apply, updateCG_apply, uniformOn_univ_singleton_eq World.ina .nancy,
    L1_apply_singleton_eq_zero (by decide), mul_zero]
  refine ENNReal.add_lt_add_left (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)) ?_
  exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (by norm_num))
    (L1_apply_singleton_ne_zero (by decide) (uniformOn_univ_singleton_ne_zero _))

/-! Predictions at any common ground favouring the German-studying worlds by a common margin,
as `cg₂` does. -/

section Shaped

variable (μ : Measure World) [IsFiniteMeasure μ]

theorem sum_L0_toReal (w : World) :
    ∑ u, (L0 μ u {w}).toReal =
      ∑ u ∈ Finset.univ.filter (w ∈ sem ·), μ.real {w} / ∑ x ∈ sem u, μ.real {x} := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs with h
  · exact L0_toReal h
  · exact L0_toReal_of_notMem h

theorem real_univ : μ.real Set.univ =
    μ.real {.ina} + μ.real {.katie} + μ.real {.nancy} + μ.real {.sally} := by
  rw [← Finset.coe_univ, ← sum_measureReal_singleton,
    show (Finset.univ : Finset World) = {.ina, .katie, .nancy, .sally} from rfl,
    Finset.sum_insert (by decide : World.ina ∉ ({.katie, .nancy, .sally} : Finset World)),
    Finset.sum_insert (by decide : World.katie ∉ ({.nancy, .sally} : Finset World)),
    Finset.sum_pair (by decide : World.nancy ≠ .sally), add_assoc, add_assoc]

variable (hik : μ {.ina} = μ {.katie}) (hns : μ {.nancy} = μ {.sally})
  (hlt : μ {.ina} < μ {.nancy}) (hi : μ {.ina} ≠ 0)

include hik hns hlt hi

/-- Nancy's speaker now prefers *they like being outdoors* to re-asserting *they study a
humanity*, and Ina's *they study a science* to *they like being indoors*. This is redundancy
aversion, since the literal listener reads the common ground and an established utterance
discriminates less. -/
theorem s1_prefers_new :
    (S1 μ .nancy).real {.studyHumanity} < (S1 μ .nancy).real {.likeOutdoors} ∧
    (S1 μ .ina).real {.likeIndoors} < (S1 μ .ina).real {.studyScience} := by
  have hn : μ {.nancy} ≠ 0 := (zero_le.trans_lt hlt).ne'
  constructor
  · rw [speaker_dirac_real_singleton_lt_iff (L := L0 μ) (w := .nancy) zero_le_one
      ⟨.studyHumanity, L0_apply_singleton_ne_zero (cg := μ) (u := .studyHumanity) (w := .nancy)
        (by decide) hn⟩]
    simp only [ENNReal.rpow_one, Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, mul_one]
    rw [listener_truthful_apply_singleton μ semSet (u := .studyHumanity) (by decide),
      listener_truthful_apply_singleton μ semSet (u := .likeOutdoors) (by decide),
      ENNReal.mul_lt_mul_iff_left hn (measure_ne_top _ _), ENNReal.inv_lt_inv,
      ← sum_measure_singleton, ← sum_measure_singleton,
      show sem .likeOutdoors = {.katie, .nancy} by decide,
      show sem .studyHumanity = {.nancy, .sally} by decide, Finset.sum_pair (by decide),
      Finset.sum_pair (by decide), ← hik, ← hns, add_comm]
    exact ENNReal.add_lt_add_left (measure_ne_top μ _) hlt
  · rw [speaker_dirac_real_singleton_lt_iff (L := L0 μ) (w := .ina) zero_le_one
      ⟨.studyScience, L0_apply_singleton_ne_zero (cg := μ) (u := .studyScience) (w := .ina)
        (by decide) hi⟩]
    simp only [ENNReal.rpow_one, Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, mul_one]
    rw [listener_truthful_apply_singleton μ semSet (u := .likeIndoors) (by decide),
      listener_truthful_apply_singleton μ semSet (u := .studyScience) (by decide),
      ENNReal.mul_lt_mul_iff_left hi (measure_ne_top _ _), ENNReal.inv_lt_inv,
      ← sum_measure_singleton, ← sum_measure_singleton,
      show sem .studyScience = {.ina, .katie} by decide,
      show sem .likeIndoors = {.ina, .sally} by decide, Finset.sum_pair (by decide),
      Finset.sum_pair (by decide), ← hik, ← hns]
    exact ENNReal.add_lt_add_left (measure_ne_top μ _) hlt

theorem l1_katie_lt_nancy :
    (L1 μ .likeOutdoors).real {.katie} < (L1 μ .likeOutdoors).real {.nancy} := by
  rw [listener_real_singleton_lt_iff, S1_real_singleton, S1_real_singleton,
    sum_L0_toReal, sum_L0_toReal, L0_toReal (by decide), L0_toReal (by decide),
    show Finset.univ.filter (World.katie ∈ sem ·) = {.studyScience, .likeOutdoors, .null} by
      decide,
    show Finset.univ.filter (World.nancy ∈ sem ·) = {.studyHumanity, .likeOutdoors, .null} by
      decide,
    Finset.sum_insert (by decide : Utterance.studyScience ∉
      ({.likeOutdoors, .null} : Finset Utterance)),
    Finset.sum_insert (by decide : Utterance.studyHumanity ∉
      ({.likeOutdoors, .null} : Finset Utterance)),
    Finset.sum_pair (by decide : Utterance.likeOutdoors ≠ .null),
    Finset.sum_pair (by decide : Utterance.likeOutdoors ≠ .null),
    show sem .studyScience = {.ina, .katie} by decide,
    show sem .studyHumanity = {.nancy, .sally} by decide,
    show sem .likeOutdoors = {.katie, .nancy} by decide, show sem .null = Finset.univ by decide,
    Finset.sum_pair (by decide : World.ina ≠ .katie),
    Finset.sum_pair (by decide : World.nancy ≠ .sally),
    Finset.sum_pair (by decide : World.katie ≠ .nancy), sum_measureReal_singleton,
    Finset.coe_univ, real_univ]
  have hk : μ.real {.katie} = μ.real {.ina} := by rw [measureReal_def, measureReal_def, hik]
  have hs : μ.real {.sally} = μ.real {.nancy} := by rw [measureReal_def, measureReal_def, hns]
  have ha : 0 < μ.real {.ina} := ENNReal.toReal_pos hi (measure_ne_top _ _)
  have hab : μ.real {.ina} < μ.real {.nancy} :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hlt
  rw [hk, hs]
  set a := μ.real {.ina}
  set b := μ.real {.nancy}
  have hb : 0 < b := ha.trans hab
  have hSk : a / (a + b) / (a / (a + a) + (a / (a + b) + a / (a + a + b + b))) =
      2 * a / (4 * a + b) := by
    field_simp
    ring
  have hSn : b / (a + b) / (b / (b + b) + (b / (a + b) + b / (a + a + b + b))) =
      2 * b / (a + 4 * b) := by
    field_simp
    ring
  rw [hSk, hSn, mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos ha hb) (sub_pos.2 hab),
    mul_pos (sub_pos.2 hab) (by positivity : 0 < b ^ 2 + a * b + a ^ 2)]

end Shaped

theorem turn2_breaks_symmetry :
    L1 cg₁ .likeOutdoors {.katie} = L1 cg₁ .likeOutdoors {.nancy} ∧
    (L1 cg₂ .likeOutdoors).real {.katie} < (L1 cg₂ .likeOutdoors).real {.nancy} :=
  ⟨l1_turn1_inferences.2.2,
    l1_katie_lt_nancy cg₂ cg₂_ina_eq_katie cg₂_nancy_eq_sally cg₂_ina_lt_nancy cg₂_ina_ne_zero⟩

end Anderson2021
