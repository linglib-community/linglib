module

public import Studies.ZaslavskyKempRegierTishby2018

/-!
# Zaslavsky, Maldonado and Culbertson (2021): Person systems and efficient compression

Zaslavsky, Maldonado and Culbertson apply the Information Bottleneck to personal pronouns. The
person space has eleven referents, built from the speaker, the addressee and others, one, exactly
two or more of them. A speaker's meaning for a referent spreads over the space in proportion to
$\exp(-\gamma d)$, $d$ a weighted Hamming distance between the referents' features, and a pronoun
system is an encoder of meanings into forms. Zwicky's generalization, that no language gives the
inclusive the form of the second person to the exclusion of the exclusive, is where the paper's
models part: weighting the speaker and the addressee alike rates the unattested second-inclusive
system as efficient as attested ones, while weighting the speaker sixteen times the addressee, the
egocentric model, separates them. With the weights alike, exchanging the speaker and the addressee
is a symmetry of the meanings, and under a need distribution that the exchange also preserves an
encoder and its exchange have [the same complexity](##complexity_comap) and [the same
accuracy](##accuracy_comap). The second-inclusive system is the exchange of a first-inclusive one,
so the unbiased model [values the two exactly alike](##objective_secondInclusive) unless the need
distribution tells the speaker from the addressee: the separation needs the egocentric weights or an
asymmetric need.

## Implementation notes

The paper encodes number in two bits that its unbiased model counts as one feature; here the
number term of the distance is whether the numbers differ. The precision $\gamma$, which the
paper fixes from the speaker's memory capacity, and the need distribution, which it infers from
corpora, are parameters.

## References

* [zaslavsky-maldonado-culbertson-2021]
* [zaslavsky-kemp-regier-tishby-2018]
-/

@[expose] public section

namespace ZaslavskyMaldonadoCulbertson2021

open MeasureTheory ProbabilityTheory InformationTheory ZaslavskyKempRegierTishby2018
open scoped ENNReal

/-! ### Symmetries of the Information Bottleneck -/

section Symmetry

variable {M U W : Type*} [MeasurableSpace M] [MeasurableSpace U] [MeasurableSpace W]
  [Fintype M] [Fintype U] [Fintype W] [DiscreteMeasurableSpace M] [DiscreteMeasurableSpace U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] [MeasurableSingletonClass W]
  [Nonempty M] (meanings : Kernel M U) [IsMarkovKernel meanings] (source : Measure M)
  [IsProbabilityMeasure source] (encoder : Kernel M W) [IsMarkovKernel encoder]

private theorem map_apply_singleton {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSingletonClass α] (g : α ≃ α) (μ : Measure α) (a : α) :
    μ.map g {a} = μ {g.symm a} := by
  rw [Measure.map_apply .of_discrete (.singleton a)]
  congr 1
  ext x
  simp [Equiv.eq_symm_apply]

private theorem klDiv_map_equiv {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (g : α ≃ α) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map g) (ν.map g) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le _ _ .of_discrete) ?_
  calc klDiv μ ν = klDiv ((μ.map g).map g.symm) ((ν.map g).map g.symm) := by
        simp [Measure.map_map .of_discrete .of_discrete, Function.comp_def]
    _ ≤ klDiv (μ.map g) (ν.map g) := klDiv_map_le _ _ .of_discrete

variable {e : M ≃ M} {source}

omit [Fintype M] [Nonempty M] [IsProbabilityMeasure source] in
private theorem apply_singleton_of_map_eq (he : source.map e = source) (m : M) :
    source {e m} = source {m} := by
  conv_lhs => rw [← he]
  rw [map_apply_singleton, Equiv.symm_apply_apply]

omit [Nonempty M] [IsProbabilityMeasure source] [IsMarkovKernel encoder] in
private theorem comp_comap (he : source.map e = source) :
    encoder.comap e .of_discrete ∘ₘ source = encoder ∘ₘ source := by
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [Measure.comp_apply_singleton, Measure.comp_apply_singleton,
    ← Equiv.sum_comp e (fun m ↦ source {m} * encoder m {w})]
  simp only [Kernel.comap_apply, apply_singleton_of_map_eq he]

omit [Nonempty M] in
/-- An encoder relabelled by a symmetry of the source has the encoder's complexity. -/
theorem complexity_comap (he : source.map e = source) :
    complexity source (encoder.comap e .of_discrete) = complexity source encoder := by
  rw [complexity_eq, complexity_eq, comp_comap encoder he, ← Equiv.sum_comp e
    (fun m ↦ source.real {m} * (klDiv (encoder m) (encoder ∘ₘ source)).toReal)]
  simp only [Kernel.comap_apply, measureReal_def, apply_singleton_of_map_eq he]

private theorem posterior_comap (he : source.map e = source) {w : W}
    (hw : (encoder ∘ₘ source) {w} ≠ 0) :
    ((encoder.comap e .of_discrete)†source) w = ((encoder†source) w).map e.symm := by
  have hw' : (encoder.comap e .of_discrete ∘ₘ source) {w} ≠ 0 := by rwa [comp_comap encoder he]
  refine Measure.ext_of_singleton fun m ↦ ?_
  rw [posterior_apply_singleton _ _ hw', map_apply_singleton, Equiv.symm_symm,
    posterior_apply_singleton _ _ hw, comp_comap encoder he, Kernel.comap_apply,
    apply_singleton_of_map_eq he]

variable {f : U ≃ U}

omit [IsMarkovKernel meanings] in
private theorem decoder_comap (he : source.map e = source)
    (hm : ∀ m, meanings (e m) = (meanings m).map f) {w : W} (hw : (encoder ∘ₘ source) {w} ≠ 0) :
    decoder meanings source (encoder.comap e .of_discrete) w =
      (decoder meanings source encoder w).map f.symm := by
  have hm' (m : M) (u : U) : meanings (e.symm m) {u} = meanings m {f u} := by
    rw [← e.apply_symm_apply m, hm, map_apply_singleton, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  refine Measure.ext_of_singleton fun u ↦ ?_
  rw [map_apply_singleton, Equiv.symm_symm, decoder, decoder, Kernel.comp_apply,
    Kernel.comp_apply, Measure.comp_apply_singleton, Measure.comp_apply_singleton,
    posterior_comap encoder he hw, ← Equiv.sum_comp e.symm]
  simp only [map_apply_singleton, Equiv.symm_symm, Equiv.apply_symm_apply, hm']

omit [Fintype U] [DiscreteMeasurableSpace M] [DiscreteMeasurableSpace U]
  [MeasurableSingletonClass U] [IsMarkovKernel meanings] in
private theorem distortion_eq_sum (q : Kernel M W) [IsMarkovKernel q] :
    distortion meanings source q = ∑ m, ∑ w, source.real {m} * (q m).real {w} *
      (klDiv (meanings m) (decoder meanings source q w)).toReal := by
  rw [distortion, integral_fintype .of_finite, Fintype.sum_prod_type]
  simp only [Measure.compProd_real_singleton, smul_eq_mul]

theorem distortion_comap (he : source.map e = source)
    (hm : ∀ m, meanings (e m) = (meanings m).map f) :
    distortion meanings source (encoder.comap e .of_discrete) =
      distortion meanings source encoder := by
  rw [distortion_eq_sum, distortion_eq_sum]
  conv_rhs => rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [Kernel.comap_apply, measureReal_def, apply_singleton_of_map_eq he]
  obtain h | h := eq_or_ne (source {m} * encoder (e m) {w}) 0
  · rw [← ENNReal.toReal_mul, h, ENNReal.toReal_zero, zero_mul, zero_mul]
  obtain ⟨hs, hq⟩ := mul_ne_zero_iff.1 h
  have hw : (encoder ∘ₘ source) {w} ≠ 0 :=
    Measure.comp_apply_singleton_ne_zero encoder source
      (by rwa [apply_singleton_of_map_eq he]) hq
  rw [decoder_comap meanings encoder he hm hw, hm,
    ← klDiv_map_equiv f.symm ((meanings m).map f) (decoder meanings source encoder w),
    Measure.map_map .of_discrete .of_discrete, Equiv.symm_comp_self, Measure.map_id]

/-- An encoder relabelled by a symmetry of the source that the meanings follow has the
encoder's accuracy. -/
theorem accuracy_comap (he : source.map e = source)
    (hm : ∀ m, meanings (e m) = (meanings m).map f) :
    accuracy meanings source (encoder.comap e .of_discrete) = accuracy meanings source encoder := by
  have h₁ := distortion_eq meanings source (encoder.comap e .of_discrete)
  have h₂ := distortion_eq meanings source encoder
  rw [distortion_comap meanings encoder he hm] at h₁
  linarith

end Symmetry

/-! ### The person space -/

/-- Fig. 1A: the referents of the person space, by the speaker, the addressee and others they
hold and by number, one, exactly two or more than two. -/
inductive Referent
  /-- The speaker. -/
  | s
  /-- The speaker and one other. -/
  | so
  /-- The speaker and several others. -/
  | soo
  /-- The speaker and the addressee. -/
  | sa
  /-- The speaker, the addressee and others. -/
  | sao
  /-- The addressee. -/
  | a
  /-- The addressee and one other. -/
  | ao
  /-- The addressee and several others. -/
  | aoo
  /-- One other. -/
  | o
  /-- Two others. -/
  | oo
  /-- More than two others. -/
  | ooo
  deriving DecidableEq, Fintype

namespace Referent

instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩
instance : Nonempty Referent := ⟨s⟩

/-- The referent holds the speaker. -/
def speaker : Referent → Bool
  | s | so | soo | sa | sao => true
  | _ => false

/-- The referent holds the addressee. -/
def addressee : Referent → Bool
  | sa | sao | a | ao | aoo => true
  | _ => false

/-- The referent holds an other. -/
def others : Referent → Bool
  | s | sa | a => false
  | _ => true

/-- The referent's number: one, exactly two, or more than two. -/
def number : Referent → Fin 3
  | s | a | o => 0
  | so | sa | ao | oo => 1
  | soo | sao | aoo | ooo => 2

/-- Exchanging the speaker and the addressee. -/
def swap : Referent → Referent
  | s => a
  | so => ao
  | soo => aoo
  | a => s
  | ao => so
  | aoo => soo
  | r => r

@[simp] theorem swap_swap (r : Referent) : r.swap.swap = r := by cases r <;> rfl

/-- The exchange of the speaker and the addressee as a permutation. -/
def swapEquiv : Referent ≃ Referent := Function.Involutive.toPerm swap swap_swap

end Referent

open Referent

/-- The weights of the speaker, addressee, others and number features. -/
structure Weights where
  /-- The weight of the speaker feature. -/
  speaker : ℝ
  /-- The weight of the addressee feature. -/
  addressee : ℝ
  /-- The weight of the others feature. -/
  others : ℝ
  /-- The weight of number. -/
  number : ℝ

/-- The weighted Hamming distance between two referents' features. -/
def Weights.dist (w : Weights) (u t : Referent) : ℝ :=
  (if u.speaker = t.speaker then 0 else w.speaker) +
    (if u.addressee = t.addressee then 0 else w.addressee) +
    (if u.others = t.others then 0 else w.others) +
    if u.number = t.number then 0 else w.number

/-- The egocentric weights of the paper's egocentric model. -/
def egocentric : Weights := ⟨16, 1, 0.1, 1⟩

theorem dist_swap {w : Weights} (h : w.speaker = w.addressee) (u t : Referent) :
    w.dist u.swap t.swap = w.dist u t := by
  cases u <;> cases t <;> simp [Weights.dist, Referent.swap, speaker, addressee, others, number,
    h]

-- the egocentric weights make the exchange no symmetry of the distance
theorem egocentric_dist_swap_ne : egocentric.dist s.swap o.swap ≠ egocentric.dist s o := by
  norm_num [Weights.dist, egocentric, Referent.swap, speaker, addressee, others, number]

/-- The speaker's meaning of a referent `t` with precision `γ`, the distribution
$m_t(u) \propto \exp(-\gamma d(u, t))$. -/
noncomputable def meanings (w : Weights) (γ : ℝ) : Kernel Referent Referent :=
  Kernel.ofWeights fun t u ↦ ENNReal.ofReal (Real.exp (-γ * w.dist u t))

instance (w : Weights) (γ : ℝ) : IsMarkovKernel (meanings w γ) :=
  Kernel.isMarkovKernel_ofWeights (fun t ↦ ⟨t, (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'⟩)
    fun _ _ ↦ ENNReal.ofReal_ne_top

/-- With the speaker and the addressee weighted alike, the meaning of the exchanged referent is
the exchanged meaning. -/
theorem meanings_swap {w : Weights} (h : w.speaker = w.addressee) (γ : ℝ) (t : Referent) :
    meanings w γ (swapEquiv t) = (meanings w γ t).map swapEquiv := by
  have hd (u : Referent) : w.dist u t.swap = w.dist u.swap t := by
    simpa using dist_swap h u.swap t
  refine Measure.ext_of_singleton fun u ↦ ?_
  rw [map_apply_singleton, meanings, Kernel.ofWeights_apply_singleton,
    Kernel.ofWeights_apply_singleton, ← Equiv.sum_comp swapEquiv]
  simp [swapEquiv, hd]

/-! ### Inclusive systems -/

/-- The first-inclusive system of Spanish in Fig. 1B: a form for each person alone and another
for its groups, the inclusive taking the form of the speaker's groups. -/
def firstInclusive : Referent → Fin 6
  | s => 0
  | so | soo | sa | sao => 1
  | a => 2
  | ao | aoo => 3
  | o => 4
  | oo | ooo => 5

/-- The unattested second-inclusive system of Fig. 1B, the inclusive taking the form of the
addressee's groups. -/
def secondInclusive : Referent → Fin 6
  | s => 2
  | so | soo => 3
  | a => 0
  | ao | aoo | sa | sao => 1
  | o => 4
  | oo | ooo => 5

theorem secondInclusive_eq : secondInclusive = firstInclusive ∘ swapEquiv := by
  funext r; cases r <;> rfl

/-- Weighting the speaker and the addressee alike, under a need distribution that their exchange
preserves, the second-inclusive system and the first-inclusive system have the same value of the
Information Bottleneck objective at every trade-off. -/
theorem objective_secondInclusive {w : Weights} (h : w.speaker = w.addressee) (γ : ℝ)
    (need : Measure Referent) [IsProbabilityMeasure need] (hneed : need.map swapEquiv = need)
    (β : ℝ) :
    objective (meanings w γ) need (Kernel.deterministic secondInclusive .of_discrete) β =
      objective (meanings w γ) need (Kernel.deterministic firstInclusive .of_discrete) β := by
  have hq : Kernel.deterministic secondInclusive .of_discrete =
      (Kernel.deterministic firstInclusive .of_discrete).comap swapEquiv .of_discrete := by
    ext1 r
    rw [Kernel.comap_apply, Kernel.deterministic_apply, Kernel.deterministic_apply,
      secondInclusive_eq, Function.comp_apply]
  simp only [objective, hq, complexity_comap _ hneed, accuracy_comap _ _ hneed (meanings_swap h γ)]

end ZaslavskyMaldonadoCulbertson2021
