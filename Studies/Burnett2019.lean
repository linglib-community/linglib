module

public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Linglib.Data.Experiments.Burnett2019
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Studies.Eckert2008
public import Studies.Labov2012

/-!
# Burnett (2019): Signalling games, sociolinguistic variation and the construction of style

A social meaning game reads the social meaning of a sociolinguistic variable off a signalling
game over personae, the maximal consistent sets of social properties. The literal listener
conditions a prior over personae on those a variant's properties meet, the speaker chooses a
variant by the softmax of its informativity about the persona she constructs, and the naive
listener inverts the speaker against the prior. When the two variants index complementary
personae, as those of (ING) and /t/ release do, each rules out exactly the persona its rival
indexes, and the paper's predictions come out in closed form from the prior mass of those two.

## Implementation notes

Priors are integer weights read off the paper's tables, the listener normalizing them, and the
speaker's rationality is a parameter, `6` where the paper computes a number. Persona selection
is the sequential rule (15). Table 9 states no rationality. Its 33, 50 and 66 for the classes are
what the joint rule (16) gives at rationality 6, and what the sequential rule gives at a
persona-selection rationality of `ln 5`; at 6 the sequential rule gives about 25, 50 and 75.

## TODO

* The joint selection rule (16) and the uncovering listener (20).

## References

* [burnett-2019]
* [eckert-2008]
* [labov-2012]
* [lewis-1969]
* [podesva-reynolds-callier-baptiste-2015]
-/

@[expose] public section

namespace Burnett2019

open MeasureTheory ProbabilityTheory RSA SocialMeaning
open scoped ENNReal
open Eckert2008 (INGVariant)

/-! ### Social meaning games -/

section Game

variable {V P : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph P} [DecidableRel G.Adj]
  (F : GroundedField V G)

/-- A speaker selects a persona by the softmax of her values at rationality `α'` (14). -/
noncomputable def select (α' : ℝ) (value : Persona G → ℝ) : Measure (Persona G) :=
  Measure.count.tilted fun π ↦ α' * value π

@[simp] theorem select_real_singleton (α' : ℝ) (value : Persona G → ℝ) (π : Persona G) :
    (select α' value).real {π} = Real.softmax (fun π ↦ α' * value π) π :=
  count_tilted_real_singleton _ π

variable [Nonempty (Persona G)]

instance (α' : ℝ) (value : Persona G → ℝ) : IsProbabilityMeasure (select α' value) :=
  isProbabilityMeasure_tilted .of_finite

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The literal listener conditions the prior on the variant's Eckert–Montague field (11). -/
noncomputable abbrev L0 (prior : Measure (Persona G)) : Kernel V (Persona G) :=
  listener prior (truthful fun v ↦ ↑(F.personae v))

/-- The speaker is the softmax of the literal listener's informativity at rationality `α`, the
variants costing nothing (12), (13). -/
noncomputable abbrev S1 (α : ℝ) (prior : Measure (Persona G)) : Kernel (Persona G) V :=
  speaker α 0 (L0 F prior) Measure.dirac

/-- The naive listener inverts the speaker against the prior (18). -/
noncomputable abbrev L1 (α : ℝ) (prior : Measure (Persona G)) : Kernel V (Persona G) :=
  listener prior (S1 F α prior)

end Game

private theorem ofWeights_ne_zero {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {w : β → ℕ} (hw : ∀ b, w b ≠ 0) (b : β) :
    (Measure.ofWeights fun b ↦ (w b : ℝ≥0∞)) {b} ≠ 0 :=
  Measure.ofWeights_apply_singleton_ne_zero (Nat.cast_ne_zero.2 (hw b))

private theorem ofWeights_real_univ {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (w : β → ℕ) :
    (Measure.ofWeights fun b ↦ (w b : ℝ≥0∞)).real Set.univ = ((∑ b, w b : ℕ) : ℝ) := by
  rw [measureReal_def, ← Finset.coe_univ, Measure.ofWeights_apply_finset, ← Nat.cast_sum,
    ENNReal.toReal_natCast]

private theorem ofWeights_real_singleton {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (w : β → ℕ) (b : β) :
    (Measure.ofWeights fun b ↦ (w b : ℝ≥0∞)).real {b} = w b := by
  rw [Measure.ofWeights_real_singleton, ENNReal.toReal_natCast]

/-! ### Binary variables

Two variants index complementary personae, `h.persona` and `h.symm.persona`; every other
persona both convey. -/

section Binary

variable {V P : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph P} [DecidableRel G.Adj]
  {F : GroundedField V G} {v w : V} (h : F.Complementary v w)
include h

section Exclusion

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] {prior : Measure (Persona G)}
  {α : ℝ} (hα : 0 < α)
include hα

theorem S1_symm_persona_real_singleton : (S1 F α prior h.symm.persona).real {v} = 0 :=
  speaker_listener_truthful_dirac_real_singleton_eq_zero hα 0 prior _
    (Finset.mem_coe.not.2 h.symm_persona_notMem_personae)

theorem L1_real_singleton_symm_persona : (L1 F α prior v).real {h.symm.persona} = 0 := by
  rw [measureReal_def, listener_speaker_listener_truthful_apply_singleton_of_notMem hα 0 prior
    (fun u ↦ ↑(F.personae u)) (w := h.symm.persona)
    (Finset.mem_coe.not.2 h.symm_persona_notMem_personae), ENNReal.toReal_zero]

end Exclusion

variable {prior : Measure (Persona G)} {α : ℝ}

/-- The share of the first variant among the personae both variants convey, the `α`-th power of
the second's extension over the sum of the powers of both. -/
noncomputable def share (prior : Measure (Persona G)) (α : ℝ) : ℝ :=
  (prior.real Set.univ - prior.real {h.persona}) ^ α /
    ((prior.real Set.univ - prior.real {h.symm.persona}) ^ α +
      (prior.real Set.univ - prior.real {h.persona}) ^ α)

theorem share_ofWeights (wt : Persona G → ℕ) :
    share h (Measure.ofWeights (wt ·)) α =
      (((∑ p, wt p : ℕ) : ℝ) - wt h.persona) ^ α /
        ((((∑ p, wt p : ℕ) : ℝ) - wt h.symm.persona) ^ α +
          (((∑ p, wt p : ℕ) : ℝ) - wt h.persona) ^ α) := by
  simp only [share, ofWeights_real_univ, ofWeights_real_singleton]

variable [IsFiniteMeasure prior]

theorem measureReal_personae :
    prior.real ↑(F.personae v) = prior.real Set.univ - prior.real {h.symm.persona} := by
  rw [h.personae_eq_compl, Finset.coe_compl, Finset.coe_singleton,
    measureReal_compl (measurableSet_singleton _)]

section Consensus

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] (hvw : ∀ u, u = v ∨ u = w)
  (hα : 0 < α)
include hvw hα

/-- Every persona both variants convey is produced alike, so speakers constructing different
personae shift between the variants together. -/
theorem S1_eq {p p' : Persona G} (hp : prior {p} ≠ 0) (hp' : prior {p'} ≠ 0)
    (hl : p ≠ h.persona) (hr : p ≠ h.symm.persona) (hl' : p' ≠ h.persona)
    (hr' : p' ≠ h.symm.persona) : S1 F α prior p' = S1 F α prior p :=
  speaker_listener_truthful_dirac_congr hα 0 prior _ hp hp' fun u ↦ by
    simp only [Finset.mem_coe, h.mem_personae_of_ne hl hr (hvw u),
      h.mem_personae_of_ne hl' hr' (hvw u)]

end Consensus

variable [Nonempty P]

theorem share_eq_half (hp : prior {h.persona} ≠ 0)
    (hpr : prior {h.persona} = prior {h.symm.persona}) : share h prior α = 1 / 2 := by
  have hlr : prior.real {h.persona} = prior.real {h.symm.persona} := by
    simp only [measureReal_def, hpr]
  have hpos : 0 < prior.real Set.univ - prior.real {h.symm.persona} := by
    rw [← measureReal_personae h]
    exact (ENNReal.toReal_pos hp (measure_ne_top _ _)).trans_le
      (measureReal_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 h.persona_mem_personae)))
  have := Real.rpow_pos_of_pos hpos α
  rw [share, hlr]
  field_simp
  ring

/-- A persona both variants convey prefers the first exactly when the persona it rules out is the
likelier, the more informative variant being the one that rules out more. -/
theorem half_lt_share_iff (hα : 0 < α) (hp : prior {h.persona} ≠ 0)
    (hp' : prior {h.symm.persona} ≠ 0) :
    1 / 2 < share h prior α ↔ prior.real {h.persona} < prior.real {h.symm.persona} := by
  have hA : 0 < prior.real Set.univ - prior.real {h.persona} := by
    rw [← measureReal_personae h.symm]
    exact (ENNReal.toReal_pos hp' (measure_ne_top _ _)).trans_le
      (measureReal_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 h.symm.persona_mem_personae)))
  have hB : 0 < prior.real Set.univ - prior.real {h.symm.persona} := by
    rw [← measureReal_personae h]
    exact (ENNReal.toReal_pos hp (measure_ne_top _ _)).trans_le
      (measureReal_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 h.persona_mem_personae)))
  have := Real.rpow_pos_of_pos hA α
  have := Real.rpow_pos_of_pos hB α
  have key := Real.rpow_lt_rpow_iff hB.le hA.le hα
  rw [share, lt_div_iff₀ (by positivity)]
  constructor
  · intro h₁
    linarith [key.1 (by linarith)]
  · intro h₁
    linarith [key.2 (by linarith)]

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] (hvw : ∀ u, u = v ∨ u = w)
  (hα : 0 < α)
include hvw hα

/-- A persona both variants convey produces the first in its share, each extension being every
persona but the one its rival indexes. -/
theorem S1_real_singleton_of_ne {p : Persona G} (hp : prior {p} ≠ 0) (hl : p ≠ h.persona)
    (hr : p ≠ h.symm.persona) : (S1 F α prior p).real {v} = share h prior α := by
  rw [speaker_listener_truthful_dirac_zero_real_singleton_of_pair hα prior _ hp h.ne
    (h.mem_personae_of_ne hl hr (.inl rfl)) (h.mem_personae_of_ne hl hr (.inr rfl))
    fun u _ ↦ hvw u, measureReal_personae h, measureReal_personae h.symm, share]

theorem S1_persona_real_singleton (hp : prior {h.persona} ≠ 0) :
    (S1 F α prior h.persona).real {v} = 1 := by
  rw [measureReal_def, speaker_listener_truthful_dirac_eq_one (u := v) hα 0 prior
    (fun u ↦ ↑(F.personae u)) hp (Finset.mem_coe.2 h.persona_mem_personae) fun u hu ↦ ?_,
    ENNReal.toReal_one]
  obtain rfl := (hvw u).resolve_left hu
  exact Finset.mem_coe.not.2 h.symm.symm_persona_notMem_personae

variable (hprior : ∀ p, prior {p} ≠ 0)
include hprior

theorem comp_real_singleton (ρ : Measure (Persona G)) [IsFiniteMeasure ρ] :
    (S1 F α prior ∘ₘ ρ).real {v} = ρ.real {h.persona} +
      share h prior α * (ρ.real Set.univ - ρ.real {h.persona} - ρ.real {h.symm.persona}) := by
  have hrow (p : Persona G) : ρ.real {p} * (S1 F α prior p).real {v} =
      ρ.real {p} * share h prior α + (if p = h.persona then ρ.real {p} * (1 - share h prior α)
        else 0) - (if p = h.symm.persona then ρ.real {p} * share h prior α else 0) := by
    by_cases hl : p = h.persona
    · subst hl
      rw [S1_persona_real_singleton h hvw hα (hprior _), ite_eq_left rfl,
        ite_eq_right h.persona_ne]
      ring
    by_cases hr : p = h.symm.persona
    · subst hr
      rw [S1_symm_persona_real_singleton h hα, ite_eq_right hl, ite_eq_left rfl]
      ring
    rw [S1_real_singleton_of_ne h hvw hα (hprior p) hl hr, ite_eq_right hl, ite_eq_right hr]
    ring
  rw [Measure.comp_real_singleton, Finset.sum_congr rfl fun p _ ↦ hrow p, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ,
    Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
    ite_eq_left (Finset.mem_univ _)]
  ring

theorem mul_L1_real_singleton (p : Persona G) :
    (prior.real {h.persona} + share h prior α *
        (prior.real Set.univ - prior.real {h.persona} - prior.real {h.symm.persona})) *
      (L1 F α prior v).real {p} = prior.real {p} * (S1 F α prior p).real {v} := by
  rw [← comp_real_singleton h hvw hα hprior]
  exact comp_real_mul_listener_real _ _ v p

variable (hpr : prior {h.persona} = prior {h.symm.persona})
include hpr

private theorem mul_L1_real_singleton_of_eq (p : Persona G) :
    prior.real Set.univ / 2 * (L1 F α prior v).real {p} =
      prior.real {p} * (S1 F α prior p).real {v} := by
  have hlr : prior.real {h.persona} = prior.real {h.symm.persona} := by
    simp only [measureReal_def, hpr]
  rw [← mul_L1_real_singleton h hvw hα hprior, share_eq_half h (hprior _) hpr, hlr]
  ring

/-- When the two personae the variants index are equally likely, hearing the first variant leaves
every persona both convey at its prior, so a listener already sure of such a persona stays sure
whatever the speaker says. -/
theorem L1_real_singleton_of_ne {p : Persona G} (hl : p ≠ h.persona) (hr : p ≠ h.symm.persona) :
    (L1 F α prior v).real {p} = prior.real {p} / prior.real Set.univ := by
  have key := mul_L1_real_singleton_of_eq h hvw hα hprior hpr p
  rw [S1_real_singleton_of_ne h hvw hα (hprior p) hl hr, share_eq_half h (hprior _) hpr] at key
  have : 0 < prior.real Set.univ := (ENNReal.toReal_pos (hprior h.persona)
    (measure_ne_top _ _)).trans_le (measureReal_mono (Set.subset_univ _))
  field_simp at key ⊢
  linarith

/-- When the two personae the variants index are equally likely, hearing the first variant
doubles the probability of the persona only it conveys. -/
theorem L1_real_singleton_persona :
    (L1 F α prior v).real {h.persona} = 2 * prior.real {h.persona} / prior.real Set.univ := by
  have key := mul_L1_real_singleton_of_eq h hvw hα hprior hpr h.persona
  rw [S1_persona_real_singleton h hvw hα (hprior _)] at key
  have : 0 < prior.real Set.univ := (ENNReal.toReal_pos (hprior h.persona)
    (measure_ne_top _ _)).trans_le (measureReal_mono (Set.subset_univ _))
  field_simp at key ⊢
  linarith

end Binary

/-! ### (ING)

The universe of example (5) has two dimensions, competence and warmth, its personae (6) are the
four maximal consistent sets, and the Eckert fields (10) of *-ing* and *-in'* are the stern
leader and the doofus, so each variant meets every persona but the other's (Table 1). -/

/-- The social properties of example (5), two poles of competence and two of warmth. -/
inductive PersonaTrait where
  | competent
  | incompetent
  | friendly
  | aloof
  deriving DecidableEq

instance : Fintype PersonaTrait :=
  ⟨{.competent, .incompetent, .friendly, .aloof}, fun x ↦ by cases x <;> simp⟩

/-- The dimension a trait is a pole of. -/
def PersonaTrait.dimension : PersonaTrait → Dimension
  | .competent | .incompetent => .competence
  | .friendly | .aloof => .warmth

/-- A persona of the example is a maximal consistent set of its properties, the two poles of
each dimension being incompatible. -/
abbrev Persona := SocialMeaning.Persona (dimensionalIncompatibility PersonaTrait.dimension)

/-- The cool guy, competent and friendly. -/
def coolGuy : Persona := ⟨{.competent, .friendly}, by decide +kernel⟩

/-- The stern leader, competent and aloof. -/
def sternLeader : Persona := ⟨{.competent, .aloof}, by decide +kernel⟩

/-- The doofus, incompetent and friendly. -/
def doofus : Persona := ⟨{.incompetent, .friendly}, by decide +kernel⟩

/-- The arrogant asshole, incompetent and aloof. -/
def asshole : Persona := ⟨{.incompetent, .aloof}, by decide +kernel⟩

-- (6)
theorem personae_eq : (Finset.univ : Finset Persona) = {coolGuy, sternLeader, doofus, asshole} := by
  decide +kernel

instance : Nonempty Persona := ⟨coolGuy⟩

instance : Nonempty PersonaTrait := ⟨.competent⟩

/-- The Eckert fields of example (10), *-ing* indexing competence and aloofness and *-in'*
incompetence and friendliness. -/
def ingField : GroundedField INGVariant (dimensionalIncompatibility PersonaTrait.dimension) where
  indexes
    | .velar => {.competent, .aloof}
    | .apical => {.incompetent, .friendly}
  isIndepSet := by intro v; cases v <;> decide

instance : MeasurableSpace INGVariant := ⊤
instance : MeasurableSingletonClass INGVariant :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

private theorem apical_or_velar (u : INGVariant) : u = .apical ∨ u = .velar :=
  u.eq_velar_or_eq_apical.symm

theorem ing : ingField.Complementary .velar .apical where
  left_mem := by decide +kernel
  right_mem := by decide +kernel
  indexes_eq_compl := by decide +kernel

@[simp] theorem ing_persona : ing.persona = sternLeader := rfl

@[simp] theorem ing_symm_persona : ing.symm.persona = doofus := rfl

-- Table 1
theorem personae_velar : ingField.personae .velar = {doofus}ᶜ := ing.personae_eq_compl

-- Table 1
theorem personae_apical : ingField.personae .apical = {sternLeader}ᶜ := ing.symm.personae_eq_compl

/-! #### Style shifting

At the barbecue the listener takes Obama to be aloof (Table 2) and with the journalists
incompetent (Table 5). The cool guy says *-in'* with probability `8 ^ 6 / (7 ^ 6 + 8 ^ 6)`, about
69%, at the first and `7 ^ 6 / (7 ^ 6 + 8 ^ 6)`, about 31%, at the second, and the asshole says
it exactly as often: style shifting changes the prior, not the speaker. -/

/-- At the barbecue the aloof personae carry more mass (Table 2). -/
def casualWeight (π : Persona) : ℕ := if .aloof ∈ π.1 then 3 else 2

/-- With the journalists the incompetent personae carry more mass (Table 5). -/
def carefulWeight (π : Persona) : ℕ := if .incompetent ∈ π.1 then 3 else 2

/-- The barbecue's prior. -/
noncomputable abbrev casual : Measure Persona := Measure.ofWeights (casualWeight ·)

/-- The journalists' prior. -/
noncomputable abbrev careful : Measure Persona := Measure.ofWeights (carefulWeight ·)

private theorem casual_ne_zero : ∀ π, casual {π} ≠ 0 :=
  ofWeights_ne_zero fun π ↦ by unfold casualWeight; split_ifs <;> decide

private theorem careful_ne_zero : ∀ π, careful {π} ≠ 0 :=
  ofWeights_ne_zero fun π ↦ by unfold carefulWeight; split_ifs <;> decide

/-- At the barbecue the cool guy says *-in'* with probability `8 ^ 6 / (7 ^ 6 + 8 ^ 6)`, about
69% (p. 435). -/
theorem casual_apical :
    (S1 ingField 6 casual coolGuy).real {.apical} = 8 ^ 6 / (7 ^ 6 + 8 ^ 6) := by
  rw [S1_real_singleton_of_ne ing.symm apical_or_velar (by norm_num) (casual_ne_zero _) (by decide)
    (by decide), share_ofWeights, ing_symm_persona, ing_persona,
    show ∑ π, casualWeight π = 10 by decide +kernel, show casualWeight doofus = 2 by decide +kernel,
    show casualWeight sternLeader = 3 by decide +kernel]
  norm_num

/-- With the journalists the cool guy says *-in'* with probability `7 ^ 6 / (7 ^ 6 + 8 ^ 6)`,
about 31% (p. 436). -/
theorem careful_apical :
    (S1 ingField 6 careful coolGuy).real {.apical} = 7 ^ 6 / (7 ^ 6 + 8 ^ 6) := by
  rw [S1_real_singleton_of_ne ing.symm apical_or_velar (by norm_num) (careful_ne_zero _) (by decide)
    (by decide), share_ofWeights, ing_symm_persona, ing_persona,
    show ∑ π, carefulWeight π = 10 by decide +kernel,
    show carefulWeight doofus = 3 by decide +kernel,
    show carefulWeight sternLeader = 2 by decide +kernel]
  norm_num

theorem S1_asshole {prior : Measure Persona} [IsFiniteMeasure prior] {α : ℝ} (hα : 0 < α)
    (hprior : ∀ π, prior {π} ≠ 0) : S1 ingField α prior asshole = S1 ingField α prior coolGuy :=
  S1_eq ing INGVariant.eq_velar_or_eq_apical hα (hprior _) (hprior _) (by decide) (by decide)
    (by decide) (by decide)

/-! #### Labov's occasions

On each of the three occasions Labov recorded, Obama constructs a persona against his
listeners' prior (pp. 435–436): the cool guy at the barbecue and with the journalists, and the
stern leader at the convention, where aloofness is valued and which *-in'* cannot convey. The
paper gives no prior for the convention, and none is needed. -/

/-- The persona Obama constructs in each of Labov's styles. -/
def occasionPersona : Labov2012.Style → Persona
  | .casual | .careful => coolGuy
  | .formal => sternLeader

/-- The prior of each of Labov's styles, the convention's left open. -/
noncomputable def occasionPrior (formal : Measure Persona) : Labov2012.Style → Measure Persona
  | .casual => casual
  | .careful => careful
  | .formal => formal

/-- The model's rate of *-in'* in each of Labov's styles. -/
noncomputable def apicalRate (formal : Measure Persona) (s : Labov2012.Style) : ℝ :=
  (S1 ingField 6 (occasionPrior formal s) (occasionPersona s)).real {.apical}

theorem apicalRate_strictAnti (formal : Measure Persona) : StrictAnti (apicalRate formal) := by
  have hcasual : apicalRate formal .casual = 8 ^ 6 / (7 ^ 6 + 8 ^ 6) := casual_apical
  have hcareful : apicalRate formal .careful = 7 ^ 6 / (7 ^ 6 + 8 ^ 6) := careful_apical
  have hformal : apicalRate formal .formal = 0 :=
    S1_symm_persona_real_singleton ing.symm (by norm_num)
  intro s t h
  cases s <;> cases t <;> first | exact absurd h (by decide) | (simp only [*]; norm_num)

/-- The model orders Labov's styles as Obama's observed rates of *-in'* do, whatever the prior
at the convention. -/
theorem apicalRate_lt_iff (formal : Measure Persona) {s t : Labov2012.Style} :
    apicalRate formal s < apicalRate formal t
      ↔ (Labov2012.ingByStyle s).percent < (Labov2012.ingByStyle t).percent :=
  (apicalRate_strictAnti formal).lt_iff_gt.trans Labov2012.ingByStyle_strictAnti.lt_iff_gt.symm

/-! #### Persona selection

Obama's values at the barbecue (Table 6) count the properties of competence and friendliness a
persona has. Selected by them, the personae only one variant conveys are equally likely, so
selection only dilutes the cool guy's preference and *-in'* stays the likelier variant (p. 438). -/

/-- Obama's values at the barbecue (Table 6) count how many of competence and friendliness a
persona has. -/
def obamaValue (π : Persona) : ℝ := (π.1 ∩ {.competent, .friendly}).card

-- p. 438
theorem obama_apical : 1 / 2 < (S1 ingField 6 casual ∘ₘ select 6 obamaValue).real {.apical} := by
  have hs : share ing.symm casual 6 = 8 ^ 6 / (7 ^ 6 + 8 ^ 6) := by
    rw [← S1_real_singleton_of_ne ing.symm apical_or_velar (by norm_num) (casual_ne_zero coolGuy)
      (by decide) (by decide)]
    exact casual_apical
  have hsum := probReal_univ (μ := select 6 obamaValue)
  rw [← Finset.coe_univ, ← sum_measureReal_singleton, personae_eq,
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton] at hsum
  have heq : (select 6 obamaValue).real {doofus} = (select 6 obamaValue).real {sternLeader} := by
    simp only [select_real_singleton, Real.softmax_apply,
      show obamaValue doofus = obamaValue sternLeader by
        unfold obamaValue; exact congrArg Nat.cast (by decide +kernel)]
  have hpos : 0 < (select 6 obamaValue).real {coolGuy} := by
    rw [select_real_singleton]
    exact Real.softmax_pos _ _
  have hnn : 0 ≤ (select 6 obamaValue).real {asshole} := measureReal_nonneg
  rw [comp_real_singleton ing.symm apical_or_velar (by norm_num) casual_ne_zero,
    ing_symm_persona, ing_persona, hs, probReal_univ]
  linarith

/-! #### Stratification

Interviewed by a stranger, a speaker faces a listener with no strong beliefs about her, a
uniform prior (p. 439), so the two excluded personae are equally likely and every persona both
variants convey says *-in'* half the time. A class's rate of *-in'* is then one half plus half
the difference between how often it selects the doofus and the stern leader, and the value
functions of Table 8 order the classes as Labov's rates do (Table 7), whatever the
rationalities. -/

/-- The uniform prior of the sociolinguistic interview (p. 439). -/
noncomputable abbrev uniform : Measure Persona := Measure.ofWeights fun _ ↦ ((1 : ℕ) : ℝ≥0∞)

private theorem uniform_ne_zero : ∀ π, uniform {π} ≠ 0 :=
  ofWeights_ne_zero fun _ ↦ one_ne_zero

/-- Social classes are ordered from the highest, `upperMiddle < lowerMiddle < working < lower`. -/
instance : LinearOrder SocialClass := LinearOrder.lift' SocialClass.ctorIdx (by decide)

-- Table 7
theorem ingByClass_strictMono : StrictMono fun c ↦ (ingByClass c).percent := by decide

/-- The classes Table 8 gives values for, every class of Table 7 but the lower class. -/
abbrev ValuedClass := {c : SocialClass // c ≠ .lower}

/-- The value functions of Table 8, by which the working class prefers friendly personae, the
upper middle class competent ones, and the lower middle class neither. -/
def classValue : ValuedClass → Persona → ℝ
  | ⟨.working, _⟩, π => if .friendly ∈ π.1 then 2 else 1
  | ⟨.lowerMiddle, _⟩, _ => 1
  | ⟨.upperMiddle, _⟩, π => if .competent ∈ π.1 then 2 else 1
  | ⟨.lower, h⟩, _ => absurd rfl h

/-- A class's rate of *-in'*, its speaker selecting personae by its values at rationality `α'`
and choosing variants at rationality `α` against the uniform prior (15). -/
noncomputable def classRate (α α' : ℝ) (c : ValuedClass) : ℝ :=
  (S1 ingField α uniform ∘ₘ select α' (classValue c)).real {.apical}

theorem classRate_eq {α : ℝ} (hα : 0 < α) (α' : ℝ) (c : ValuedClass) :
    classRate α α' c = 1 / 2 + ((select α' (classValue c)).real {doofus} -
      (select α' (classValue c)).real {sternLeader}) / 2 := by
  rw [classRate, comp_real_singleton ing.symm apical_or_velar hα uniform_ne_zero,
    ing_symm_persona, ing_persona, share_eq_half ing.symm (uniform_ne_zero _)
      (by simp [Measure.ofWeights_apply_singleton]), probReal_univ]
  ring

private theorem strictMono_of_lt_half_eq_half_lt {f : ValuedClass → ℝ}
    (h₁ : f ⟨.upperMiddle, by decide⟩ < 1 / 2) (h₂ : f ⟨.lowerMiddle, by decide⟩ = 1 / 2)
    (h₃ : 1 / 2 < f ⟨.working, by decide⟩) : StrictMono f := by
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  cases c <;> cases c' <;> first | contradiction | linarith

theorem classRate_strictMono {α α' : ℝ} (hα : 0 < α) (hα' : 0 < α') :
    StrictMono (classRate α α') := by
  have hsel (c : ValuedClass) (π π' : Persona) : (select α' (classValue c)).real {π} <
      (select α' (classValue c)).real {π'} ↔ classValue c π < classValue c π' := by
    rw [select_real_singleton, select_real_singleton, Real.softmax_lt_softmax_iff,
      mul_lt_mul_iff_right₀ hα']
  have hwc := (hsel ⟨.working, by decide⟩ sternLeader doofus).2
    (by simp [classValue, sternLeader, doofus])
  have humc := (hsel ⟨.upperMiddle, by decide⟩ doofus sternLeader).2
    (by simp [classValue, sternLeader, doofus])
  have hlmc : (select α' (classValue ⟨.lowerMiddle, by decide⟩)).real {doofus} =
      (select α' (classValue ⟨.lowerMiddle, by decide⟩)).real {sternLeader} := by
    simp only [select_real_singleton, Real.softmax_apply, classValue]
  refine strictMono_of_lt_half_eq_half_lt ?_ ?_ ?_ <;> rw [classRate_eq hα] <;> linarith

/-- The model orders the classes as Labov's rates of *-in'* do (Tables 7 and 9)
(Table 8, Table 7). -/
theorem classRate_lt_classRate_iff {α α' : ℝ} (hα : 0 < α) (hα' : 0 < α') {c c' : ValuedClass} :
    classRate α α' c < classRate α α' c' ↔ (ingByClass c).percent < (ingByClass c').percent := by
  have : StrictMono fun c : ValuedClass ↦ (ingByClass c).percent :=
    ingByClass_strictMono.comp (Subtype.strictMono_coe _)
  exact (classRate_strictMono hα hα').lt_iff_lt.trans this.lt_iff_lt.symm

/-! ### /t/ release

The /t/ game replaces competence with articulateness (19): released /t/ indexes articulateness
and aloofness, the flap inarticulateness and friendliness. Its listeners' beliefs about Rice are
uniform, about Pelosi that she is inarticulate, and about Bush that he is almost surely
inarticulate and aloof (Tables 10, 13, 15). -/

namespace Release

/-- The social properties of the /t/ game, two poles of articulateness and two of warmth. -/
inductive Trait where
  | articulate
  | inarticulate
  | friendly
  | aloof
  deriving DecidableEq

instance : Fintype Trait :=
  ⟨{.articulate, .inarticulate, .friendly, .aloof}, fun x ↦ by cases x <;> simp⟩

instance : Nonempty Trait := ⟨.articulate⟩

/-- The dimension a trait is a pole of. -/
def Trait.dimension : Trait → Dimension
  | .articulate | .inarticulate => .competence
  | .friendly | .aloof => .warmth

/-- A persona of the /t/ game. -/
abbrev Persona := SocialMeaning.Persona (dimensionalIncompatibility Trait.dimension)

/-- The articulate aloof persona, the one released /t/ indexes. -/
def articulateAloof : Persona := ⟨{.articulate, .aloof}, by decide +kernel⟩

/-- The articulate friendly persona. -/
def articulateFriendly : Persona := ⟨{.articulate, .friendly}, by decide +kernel⟩

/-- The inarticulate aloof persona. -/
def inarticulateAloof : Persona := ⟨{.inarticulate, .aloof}, by decide +kernel⟩

/-- The inarticulate friendly persona, the one the flap indexes. -/
def inarticulateFriendly : Persona := ⟨{.inarticulate, .friendly}, by decide +kernel⟩

theorem personae_eq : (Finset.univ : Finset Persona) =
    {articulateAloof, articulateFriendly, inarticulateAloof, inarticulateFriendly} := by
  decide +kernel

instance : Nonempty Persona := ⟨articulateAloof⟩

/-- Released and flapped /t/. -/
inductive Variant where
  | released
  | flapped
  deriving DecidableEq, Fintype

instance : MeasurableSpace Variant := ⊤
instance : MeasurableSingletonClass Variant :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

theorem Variant.eq_released_or_eq_flapped (u : Variant) : u = .released ∨ u = .flapped := by
  cases u <;> simp

private theorem released_or_flapped (u : Variant) : u = .released ∨ u = .flapped :=
  u.eq_released_or_eq_flapped

private theorem flapped_or_released (u : Variant) : u = .flapped ∨ u = .released :=
  u.eq_released_or_eq_flapped.symm

/-- The Eckert fields of (19). -/
def field : GroundedField Variant (dimensionalIncompatibility Trait.dimension) where
  indexes
    | .released => {.articulate, .aloof}
    | .flapped => {.inarticulate, .friendly}
  isIndepSet := by intro v; cases v <;> decide

theorem release : field.Complementary .released .flapped where
  left_mem := by decide +kernel
  right_mem := by decide +kernel
  indexes_eq_compl := by decide +kernel

@[simp] theorem release_persona : release.persona = articulateAloof := rfl

@[simp] theorem release_symm_persona : release.symm.persona = inarticulateFriendly := rfl

variable {α : ℝ}

/-! #### Rice -/

/-- Rice is unfamiliar, so the listener's beliefs about her are uniform (Table 10). -/
noncomputable abbrev rice : Measure Persona := Measure.ofWeights fun _ ↦ ((1 : ℕ) : ℝ≥0∞)

private theorem rice_ne_zero : ∀ π, rice {π} ≠ 0 :=
  ofWeights_ne_zero fun _ ↦ one_ne_zero

private theorem rice_eq : rice {articulateAloof} = rice {inarticulateFriendly} := by
  simp [Measure.ofWeights_apply_singleton]

private theorem rice_real (π : Persona) : rice.real {π} / rice.real Set.univ = 1 / 4 := by
  rw [ofWeights_real_singleton, ofWeights_real_univ, show ∑ _ : Persona, 1 = 4 by decide +kernel]
  norm_num

-- Table 11
theorem rice_S1 (hα : 0 < α) {p : Persona} (hl : p ≠ articulateAloof)
    (hr : p ≠ inarticulateFriendly) : (S1 field α rice p).real {.released} = 1 / 2 := by
  rw [S1_real_singleton_of_ne release released_or_flapped hα (rice_ne_zero p) hl hr,
    share_eq_half release (rice_ne_zero _) rice_eq]

-- Table 12
theorem rice_released (hα : 0 < α) :
    (L1 field α rice .released).real {articulateAloof} = 1 / 2 ∧
      (L1 field α rice .released).real {articulateFriendly} = 1 / 4 ∧
      (L1 field α rice .released).real {inarticulateAloof} = 1 / 4 ∧
      (L1 field α rice .released).real {inarticulateFriendly} = 0 := by
  have hl := L1_real_singleton_persona release released_or_flapped hα rice_ne_zero
    rice_eq
  have hn (p : Persona) (hl : p ≠ articulateAloof) (hr : p ≠ inarticulateFriendly) :=
    L1_real_singleton_of_ne release released_or_flapped hα rice_ne_zero rice_eq
      hl hr
  refine ⟨?_, ?_, ?_, L1_real_singleton_symm_persona release hα⟩
  · rw [release_persona] at hl
    rw [hl, mul_div_assoc, rice_real]
    norm_num
  · rw [hn _ (by decide) (by decide), rice_real]
  · rw [hn _ (by decide) (by decide), rice_real]

-- Table 12
theorem rice_flapped (hα : 0 < α) :
    (L1 field α rice .flapped).real {articulateAloof} = 0 ∧
      (L1 field α rice .flapped).real {articulateFriendly} = 1 / 4 ∧
      (L1 field α rice .flapped).real {inarticulateAloof} = 1 / 4 ∧
      (L1 field α rice .flapped).real {inarticulateFriendly} = 1 / 2 := by
  have hl := L1_real_singleton_persona release.symm flapped_or_released hα rice_ne_zero
    rice_eq.symm
  have hn (p : Persona) (hl : p ≠ inarticulateFriendly) (hr : p ≠ articulateAloof) :=
    L1_real_singleton_of_ne release.symm flapped_or_released hα rice_ne_zero
      rice_eq.symm hl hr
  refine ⟨L1_real_singleton_symm_persona release.symm hα, ?_, ?_, ?_⟩
  · rw [hn _ (by decide) (by decide), rice_real]
  · rw [hn _ (by decide) (by decide), rice_real]
  · rw [release_symm_persona] at hl
    rw [hl, mul_div_assoc, rice_real]
    norm_num

-- p. 442
theorem rice_articulate (hα : 0 < α) :
    (L1 field α rice .released).real {articulateAloof} +
        (L1 field α rice .released).real {articulateFriendly} = 3 / 4 ∧
      (L1 field α rice .flapped).real {articulateAloof} +
        (L1 field α rice .flapped).real {articulateFriendly} = 1 / 4 := by
  obtain ⟨h₁, h₂, -⟩ := rice_released hα
  obtain ⟨h₃, h₄, -⟩ := rice_flapped hα
  constructor <;> norm_num [*]

/-! #### Pelosi -/

/-- The listener takes Pelosi to be inarticulate (Table 13). -/
def pelosiWeight (π : Persona) : ℕ := if .inarticulate ∈ π.1 then 9 else 1

/-- The listener's beliefs about Pelosi. -/
noncomputable abbrev pelosi : Measure Persona := Measure.ofWeights (pelosiWeight ·)

private theorem pelosi_ne_zero : ∀ π, pelosi {π} ≠ 0 :=
  ofWeights_ne_zero fun π ↦ by unfold pelosiWeight; split_ifs <;> decide

private theorem pelosi_univ : pelosi.real Set.univ = 20 := by
  rw [ofWeights_real_univ, show ∑ π, pelosiWeight π = 20 by decide +kernel]
  norm_num

private theorem pelosi_aa : pelosi.real {articulateAloof} = 1 := by
  rw [ofWeights_real_singleton, show pelosiWeight articulateAloof = 1 by decide +kernel]
  norm_num

private theorem pelosi_ia : pelosi.real {inarticulateAloof} = 9 := by
  rw [ofWeights_real_singleton, show pelosiWeight inarticulateAloof = 9 by decide +kernel]
  norm_num

private theorem pelosi_if : pelosi.real {inarticulateFriendly} = 9 := by
  rw [ofWeights_real_singleton, show pelosiWeight inarticulateFriendly = 9 by decide +kernel]
  norm_num

theorem pelosi_share : share release pelosi 6 = 19 ^ 6 / (11 ^ 6 + 19 ^ 6) := by
  rw [share_ofWeights, release_persona, release_symm_persona,
    show ∑ π, pelosiWeight π = 20 by decide +kernel,
    show pelosiWeight articulateAloof = 1 by decide +kernel,
    show pelosiWeight inarticulateFriendly = 9 by decide +kernel]
  norm_num

theorem pelosi_symm_share : share release.symm pelosi 6 = 11 ^ 6 / (19 ^ 6 + 11 ^ 6) := by
  rw [share_ofWeights, release_symm_persona, release_persona,
    show ∑ π, pelosiWeight π = 20 by decide +kernel,
    show pelosiWeight articulateAloof = 1 by decide +kernel,
    show pelosiWeight inarticulateFriendly = 9 by decide +kernel]
  norm_num

-- Table 14, p. 443
theorem pelosi_L1 : 4 / 5 < (L1 field 6 pelosi .released).real {inarticulateAloof} ∧
    19 / 20 < (L1 field 6 pelosi .flapped).real {inarticulateFriendly} := by
  have h₁ := mul_L1_real_singleton release released_or_flapped (by norm_num : (0 : ℝ) < 6)
    pelosi_ne_zero inarticulateAloof
  rw [S1_real_singleton_of_ne release released_or_flapped (by norm_num)
      (pelosi_ne_zero _) (by decide) (by decide), pelosi_share, release_persona,
    release_symm_persona,
    pelosi_univ, pelosi_aa, pelosi_ia, pelosi_if] at h₁
  have h₂ := mul_L1_real_singleton release.symm flapped_or_released (by norm_num : (0 : ℝ) < 6)
    pelosi_ne_zero release.symm.persona
  rw [S1_persona_real_singleton release.symm flapped_or_released (by norm_num) (pelosi_ne_zero _),
    pelosi_symm_share, release_symm_persona, release_persona, pelosi_univ, pelosi_aa,
    pelosi_if] at h₂
  constructor <;> norm_num at h₁ h₂ ⊢ <;> linarith

/-! #### Bush -/

/-- The listener is almost sure Bush is inarticulate and aloof (Table 15). -/
def bushWeight (π : Persona) : ℕ := if π = inarticulateAloof then 97 else 1

/-- The listener's beliefs about Bush. -/
noncomputable abbrev bush : Measure Persona := Measure.ofWeights (bushWeight ·)

private theorem bush_ne_zero : ∀ π, bush {π} ≠ 0 :=
  ofWeights_ne_zero fun π ↦ by unfold bushWeight; split_ifs <;> decide

private theorem bush_eq : bush {articulateAloof} = bush {inarticulateFriendly} := by
  simp only [Measure.ofWeights_apply_singleton, bushWeight]
  rfl

/-- The listener remains 97% sure that Bush is inarticulate and aloof whatever variant he uses
(Table 16, p. 444). -/
theorem bush_bulletproof (hα : 0 < α) (u : Variant) :
    (L1 field α bush u).real {inarticulateAloof} = 97 / 100 := by
  have hreal : bush.real {inarticulateAloof} / bush.real Set.univ = 97 / 100 := by
    rw [ofWeights_real_singleton, ofWeights_real_univ,
      show ∑ π, bushWeight π = 100 by decide +kernel,
      show bushWeight inarticulateAloof = 97 by decide +kernel]
    norm_num
  rcases u.eq_released_or_eq_flapped with rfl | rfl
  · rw [L1_real_singleton_of_ne release released_or_flapped hα bush_ne_zero
      bush_eq (by decide) (by decide), hreal]
  · rw [L1_real_singleton_of_ne release.symm flapped_or_released hα bush_ne_zero
      bush_eq.symm (by decide) (by decide), hreal]

end Release

end Burnett2019
