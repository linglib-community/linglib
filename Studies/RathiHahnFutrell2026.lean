module

public import Linglib.Core.InformationTheory.BinaryEntropy
public import Linglib.Core.InformationTheory.EntropyRate
public import Linglib.Core.InformationTheory.Surprisal
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.UniformOn

/-!
# Rathi, Hahn, and Futrell (2026): Toward an information-theoretic model of morphological fusion based on an efficient tradeoff of memory and surprisal

Rathi, Hahn and Futrell measure the informational fusion of a form as its surprisal under a
learner that has seen no form with the same features, and explain which features a language
fuses by the tradeoff of memory and surprisal. Their simulations measure a language by the
surprisal of its characters given `t` characters of context, on the stream of its words. We
prove the appendix's two arguments for arbitrary languages, show that the second needs joint
independence, build the stream and compute its surprisal, and derive the paper's claims about
the toy languages of Tables 4 to 6 from it. The corpus studies rest on estimated language models
and a neural learner, and are not formalized.

## Main statements

* `condEntropy_le_condEntropy_fused`, `VoiceTense.condEntropy_fused_lt`: fusing a first feature
  with a second leaves the third its entropy given the second when the first is independent of
  the other two jointly, and can fail to when it is independent of each separately.
* `pastCondEntropy_char_of_le`: once the context spans a word, a stream whose characters reveal
  their position has the entropy of a word per character.
* `VoiceTense.pastCondEntropy_fus_lt_agg_zero_iff`,
  `VoiceAspectTense.pastCondEntropy_agg_lt_fuseLow_one_iff`: fusing dependent features lowers
  the surprisal without context, and fusing independent features raises it given one character.
* `VoiceTense.pastCondEntropy_nonclustered_zero`, `VoiceTense.pastCondEntropy_tagged_agg_one_lt`:
  category clustering leaves the surprisal without context unchanged and lowers it given one
  character.

## Implementation notes

* Entropies are in nats. Feature values are `Bool`s, with `false` for active, present and
  perfect. Tables 4 and 5 are the toy languages at `d = 1/4`, and Table 6 at `d = 1/2`.
* A learner is any function from a data set, a lexeme and a cell to a measure on forms, and
  informational fusion is Core's `surprisal`. A form the learner rules out has informational
  fusion `∞` in the paper and the junk value `0` of `Real.log` here.
* The stream writes the words of independent meanings one after another and starts at a
  uniformly random position of the first, which makes it stationary. The toy languages write
  each slot from its own alphabet (`tagged`), except the nonclustered language of Table 6, whose
  characters are morphemes tagged by category. The clustered language of Table 6 is the
  agglutinative language of Table 4.
* The appendix's second argument assumes only that the first feature is independent of the
  second, and its step dropping the fused part's information about the third needs joint
  independence. Its third argument compares slots: dropping category clustering raises the
  entropy of the first slot, but also of the second, and on the stream the random start absorbs
  the difference without context, as the low-memory end of Figure 6 shows.

## References

* [N. Rathi, M. Hahn, R. Futrell, *Toward an information-theoretic model of morphological
  fusion based on an efficient tradeoff of memory and surprisal* (2026)][rathi-hahn-futrell-2026]
* [N. Rathi, M. Hahn, R. Futrell, *An information-theoretic characterization of morphological
  fusion* (2021)][rathi-hahn-futrell-2021]
* [M. Hahn, J. Degen, R. Futrell, *Modeling word and morpheme order in natural language as an
  efficient trade-off of memory and surprisal* (2021)][hahn-degen-futrell-2021]
* [S. Wu, R. Cotterell, T. O'Donnell, *Morphological irregularity correlates with frequency*
  (2019)][wu-cotterell-odonnell-2019]
* [J. Mansfield, S. Stoll, B. Bickel, *Category clustering: a probabilistic bias in the
  morphology of verbal agreement marking* (2020)][mansfield-stoll-bickel-2020]
* [T. M. Cover, J. A. Thomas, *Elements of information theory* (2006)][cover-thomas-2006]
-/

@[expose] public section

namespace RathiHahnFutrell2026

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

/-! ### Informational fusion -/

section Fusion

variable {Lex K Form : Type*} {V : K → Type*} [MeasurableSpace Form]
  (learner : Set (Lex × (∀ k, V k) × Form) → Lex → (∀ k, V k) → Measure Form)
  (L : Lex → (∀ k, V k) → Form)

/-- The fusion of the form of the lexeme `ℓ` in the cell `σ` of the language `L`, over the
categories `J`, is its surprisal under a learner trained on the words of `L` whose cells differ
from `σ` in some category of `J`. A cell gives each category `k` a value in `V k`, and a word is
a lexeme, a cell and a form. Where fusion holds out cells, [wu-cotterell-odonnell-2019]'s
irregularity holds out a lexeme. -/
noncomputable def fusion (J : Set K) (ℓ : Lex) (σ : ∀ k, V k) : ℝ :=
  surprisal (learner {w | w.2.1 ∉ J.pi (fun k ↦ {σ k}) ∧ w.2.2 = L w.1 w.2.1} ℓ σ) (L ℓ σ)

theorem fusion_univ (ℓ : Lex) (σ : ∀ k, V k) :
    fusion learner L .univ ℓ σ
      = surprisal (learner {w | w.2.1 ≠ σ ∧ w.2.2 = L w.1 w.2.1} ℓ σ) (L ℓ σ) := by
  simp [fusion, Set.univ_pi_singleton]

theorem fusion_pair_eq_fusion_univ {k₁ k₂ : K} (h : ∀ k, k = k₁ ∨ k = k₂) :
    fusion learner L {k₁, k₂} = fusion learner L .univ := by
  rw [show ({k₁, k₂} : Set K) = .univ from Set.eq_univ_of_forall h]

end Fusion

/-! ### The appendix's arguments -/

section Appendix

variable {Ω S₁ S₂ S₃ F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Fintype S₁]
  [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Fintype S₂]
  [MeasurableSpace S₃] [MeasurableSingletonClass S₃] [Fintype S₃]
  [MeasurableSpace F] [MeasurableSingletonClass F] [Fintype F]
  {X₁ : Ω → S₁} {X₂ : Ω → S₂} {X₃ : Ω → S₃}

theorem entropy_fused_eq (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) {g : S₁ → S₂ → F}
    (hg : ∀ a, (g a).Injective) :
    H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] = H[X₂ | X₁ ; μ] + I[fun ω ↦ g (X₁ ω) (X₂ ω) : X₁ ; μ] := by
  have hY : Measurable fun ω ↦ g (X₁ ω) (X₂ ω) :=
    (measurable_of_finite (Function.uncurry g)).comp (hX₁.prodMk hX₂)
  rw [mutualInfo_eq_entropy_sub_condEntropy μ hY hX₁, condEntropy_of_injective μ hX₂ hX₁ g hg]
  ring

theorem condEntropy_le_entropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    {g : S₁ → S₂ → F} (hg : ∀ a, (g a).Injective) :
    H[X₂ | X₁ ; μ] ≤ H[fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] :=
  (entropy_fused_eq hX₁ hX₂ hg).ge.trans' <| le_add_of_nonneg_right <|
    mutualInfo_nonneg μ ((measurable_of_finite (Function.uncurry g)).comp (hX₁.prodMk hX₂)) hX₁

/-- A part fusing a feature independent of the other two with the second leaves the third
feature at least its entropy given the second, the appendix's second argument. -/
theorem condEntropy_le_condEntropy_fused (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hX₃ : Measurable X₃) (hind : X₁ ⟂ᵢ[μ] fun ω ↦ (X₂ ω, X₃ ω)) (g : S₁ → S₂ → F) :
    H[X₃ | X₂ ; μ] ≤ H[X₃ | fun ω ↦ g (X₁ ω) (X₂ ω) ; μ] := by
  rw [← condEntropy_prod_eq_of_indepFun μ hX₃ hX₂ hX₁
    (hind.comp measurable_id measurable_swap).symm]
  exact condEntropy_le_condEntropy_comp μ hX₃ (hX₂.prodMk hX₁) fun p ↦ g p.2 p.1

theorem condEntropy_xor_eq_entropy {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) : H[fun ω ↦ xor (V ω) (D ω) | D ; μ] = H[V ; μ] := by
  rw [show (fun ω ↦ xor (V ω) (D ω)) = fun ω ↦ (fun b v ↦ xor v b) (D ω) (V ω) from rfl,
    condEntropy_of_injective μ hV hD (fun b v ↦ xor v b) fun _ _ _ ↦ Bool.xor_left_inj.mp,
    hind.condEntropy_eq_entropy hV hD]

theorem entropy_xor_eq_log_two {V D : Ω → Bool} (hV : Measurable V) (hD : Measurable D)
    (hind : V ⟂ᵢ[μ] D) (hfair : H[V ; μ] = log 2) :
    H[fun ω ↦ xor (V ω) (D ω) ; μ] = log 2 := by
  refine le_antisymm (by simpa using entropy_le_log_card (fun ω ↦ xor (V ω) (D ω)) μ) ?_
  rw [← hfair, ← condEntropy_xor_eq_entropy hV hD hind]
  exact condEntropy_le_entropy μ (measurable_of_finite (Function.uncurry xor) |>.comp
    (hV.prodMk hD)) hD

end Appendix

/-! ### Independent words -/

section IID

variable {M B ι : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype M]
  (P : Measure M) [IsProbabilityMeasure P]

/-- A language whose slots have disjoint alphabets writes each slot's value tagged by the slot,
as the paper's toy languages write `A` or `B` first and `C` or `D` second. -/
def tagged (L : M → ι → B) (m : M) (p : ι) : ι × B := (p, L m p)

section Measurable

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem entropy_eval (f : M → S) (n : ℕ) :
    H[fun w : ℕ → M ↦ f (w n) ; Measure.infinitePi fun _ ↦ P] = H[f ; P] := by
  rw [entropy_def, entropy_def, show (fun w : ℕ → M ↦ f (w n)) = f ∘ fun w ↦ w n from rfl,
    ← Measure.map_map (measurable_of_finite f) (measurable_pi_apply n),
    Measure.infinitePi_map_eval]

private theorem indepFun_eval (f : M → S) (g : M → T) {n n' : ℕ} (h : n ≠ n') :
    IndepFun (fun w : ℕ → M ↦ f (w n)) (fun w ↦ g (w n')) (Measure.infinitePi fun _ ↦ P) :=
  ((iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ ↦ id)
    fun _ ↦ measurable_id).indepFun h).comp (measurable_of_finite f) (measurable_of_finite g)

variable [MeasurableSingletonClass S] [Fintype S] [MeasurableSingletonClass T] [Fintype T]

theorem condEntropy_eval (f : M → S) (g : M → T) (n : ℕ) :
    H[fun w : ℕ → M ↦ f (w n) | fun w ↦ g (w n) ; Measure.infinitePi fun _ ↦ P] = H[f | g ; P] :=
  IdentDistrib.condEntropy_eq ((measurable_of_finite f).comp (measurable_pi_apply n))
    ((measurable_of_finite g).comp (measurable_pi_apply n)) (measurable_of_finite f)
    (measurable_of_finite g)
    ⟨(((measurable_of_finite f).prodMk (measurable_of_finite g)).comp
        (measurable_pi_apply n)).aemeasurable,
      ((measurable_of_finite f).prodMk (measurable_of_finite g)).aemeasurable, by
      rw [show (fun w : ℕ → M ↦ (f (w n), g (w n))) = (fun m ↦ (f m, g m)) ∘ fun w ↦ w n
        from rfl, ← Measure.map_map ((measurable_of_finite f).prodMk (measurable_of_finite g))
        (measurable_pi_apply n), Measure.infinitePi_map_eval]⟩

theorem condEntropy_eval_of_ne (f : M → S) (g : M → T) {n n' : ℕ} (h : n ≠ n') :
    H[fun w : ℕ → M ↦ f (w n) | fun w ↦ g (w n') ; Measure.infinitePi fun _ ↦ P] = H[f ; P] := by
  rw [(indepFun_eval P f g h).condEntropy_eq_entropy
    ((measurable_of_finite f).comp (measurable_pi_apply n))
    ((measurable_of_finite g).comp (measurable_pi_apply n'))]
  exact entropy_eval P f n

theorem entropy_eval_pair (f : M → S) (g : M → T) {n n' : ℕ} (h : n ≠ n') :
    H[fun w : ℕ → M ↦ (f (w n), g (w n')) ; Measure.infinitePi fun _ ↦ P]
      = H[f ; P] + H[g ; P] := by
  rw [(indepFun_eval P f g h).entropy_pair_eq_add
    ((measurable_of_finite f).comp (measurable_pi_apply n))
    ((measurable_of_finite g).comp (measurable_pi_apply n')), entropy_eval, entropy_eval]

end Measurable

variable [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]

private theorem condEntropy_tag (p q : ι) (X Y : M → B) :
    H[fun m ↦ (q, X m) | fun m ↦ (p, Y m) ; P] = H[X | Y ; P] := by
  have hY : H[fun m ↦ (q, X m) | fun m ↦ (p, Y m) ; P] = H[fun m ↦ (q, X m) | Y ; P] :=
    le_antisymm (condEntropy_le_condEntropy_comp P (measurable_of_finite _)
        (measurable_of_finite (fun m ↦ (p, Y m))) Prod.snd)
      (condEntropy_le_condEntropy_comp P (measurable_of_finite _) (measurable_of_finite Y)
        (Prod.mk p))
  rw [hY]
  exact condEntropy_of_injective P (measurable_of_finite X) (measurable_of_finite Y)
    (fun _ b ↦ (q, b)) fun _ ↦ Prod.mk_right_injective q

end IID

/-! ### The character stream

The paper measures a language by the surprisal of its characters under an `(t + 1)`-gram model,
the forms of independent meanings written one after another. Read from a uniformly random
position of the first word, that stream is stationary, and its surprisal given `t` characters of
context is `pastCondEntropy (char L) (stream k P) t`. -/

private theorem measurable_phase {Ω J S : Type*} [MeasurableSpace Ω] [MeasurableSpace J]
    [Countable J] [MeasurableSingletonClass J] [MeasurableSpace S] {X : J → Ω → S}
    (hX : ∀ j, Measurable (X j)) : Measurable fun ω : J × Ω ↦ X ω.1 ω.2 :=
  measurable_from_prod_countable_right hX

private theorem mod_lt_mod_of_not_div_lt {a b k : ℕ} (hab : a < b) (h : ¬ a / k < b / k) :
    a % k < b % k := by
  have := Nat.div_le_div_right (c := k) hab.le
  grind [Nat.div_add_mod]

section Char

variable {M A : Type*} {k : ℕ} [NeZero k]

/-- The character at time `t` of the stream of the language `L`, whose words have `k`
characters, read from position `ω.1` of the first of the words `ω.2`. -/
def char (L : M → Fin k → A) (t : ℕ) (ω : Fin k × (ℕ → M)) : A :=
  L (ω.2 ((t + ω.1) / k)) (Fin.ofNat k (t + ω.1))

/-- Advancing the stream by one character moves the start one position on, and past the last
position on to the next word. -/
def advance (ω : Fin k × (ℕ → M)) : Fin k × (ℕ → M) :=
  (ω.1 + 1, if (ω.1 : ℕ) + 1 = k then fun n ↦ ω.2 (n + 1) else ω.2)

/-- The word of `L` as a process over its positions. -/
private def word (L : M → Fin k → A) (n : ℕ) (m : M) : A := L m (Fin.ofNat k n)

theorem char_succ (L : M → Fin k → A) (t : ℕ) : char L (t + 1) = char L t ∘ advance := by
  funext ⟨φ, w⟩
  have hk := NeZero.pos k
  simp only [char, advance, Function.comp_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  split_ifs with h
  · rw [h, Nat.mod_self, add_zero, show t + 1 + φ = t + k by omega, Nat.add_div_right t hk]
    congr 1
    exact Fin.ext (by simp [Nat.add_mod_right])
  · rw [Nat.mod_eq_of_lt (lt_of_le_of_ne φ.isLt h), show t + (φ + 1) = t + 1 + φ by omega]

theorem char_zero (L : M → Fin k → A) : char L 0 = fun ω ↦ L (ω.2 0) ω.1 := by
  funext ⟨φ, w⟩
  simp [char, Nat.div_eq_of_lt φ.isLt]

theorem map_add_uniformOn (c : Fin k) :
    (uniformOn (Set.univ : Set (Fin k))).map (· + c) = uniformOn Set.univ := by
  refine Measure.ext_iff_singleton.mpr fun a ↦ ?_
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton a), uniformOn_univ,
    uniformOn_univ, show (fun x : Fin k ↦ x + c) ⁻¹' {a} = {a - c} by
      ext; exact eq_sub_iff_add_eq.symm,
    Measure.count_singleton, Measure.count_singleton]

private theorem block_word (L : M → Fin k → A) : block (word L) 0 k = fun m ↦ L m := by
  funext m i
  simp [block, word]

private theorem fin_ofNat_mod (n : ℕ) : Fin.ofNat k (n % k) = Fin.ofNat k n := by
  simp [Fin.ext_iff]

private theorem isProbabilityMeasure_uniformOn_fin :
    IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin k))) :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

end Char

section Stream

variable {M A : Type*} {k : ℕ}

variable [MeasurableSpace M]

/-- Words of independent meanings with law `P`, read from a uniformly random position of the
first. -/
noncomputable def stream (k : ℕ) (P : Measure M) : Measure (Fin k × (ℕ → M)) :=
  (uniformOn Set.univ).prod (Measure.infinitePi fun _ ↦ P)

variable (P : Measure M) [IsProbabilityMeasure P]

theorem measureReal_fst (j : Fin k) : (stream k P).real (Prod.fst ⁻¹' {j}) = (k : ℝ)⁻¹ := by
  rw [measureReal_def, ← Set.prod_univ, stream, Measure.prod_prod, measure_univ, mul_one,
    uniformOn_univ_apply_singleton, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]

private theorem identDistrib_dirac_prod {S : Type*} [MeasurableSpace S]
    {X : Fin k → (ℕ → M) → S} (hX : ∀ j, Measurable (X j)) (j : Fin k) :
    IdentDistrib (fun ω : Fin k × (ℕ → M) ↦ X ω.1 ω.2) (X j)
      ((Measure.dirac j).prod (Measure.infinitePi fun _ ↦ P)) (Measure.infinitePi fun _ ↦ P) :=
  ⟨(measurable_phase hX).aemeasurable, (hX j).aemeasurable, by
    rw [Measure.dirac_prod, Measure.map_map (measurable_phase hX) measurable_prodMk_left]
    rfl⟩

variable [NeZero k]

instance : IsProbabilityMeasure (stream k P) := by
  have := isProbabilityMeasure_uniformOn_fin (k := k)
  unfold stream; infer_instance

theorem measurePreserving_advance :
    MeasurePreserving (advance (M := M) (k := k)) (stream k P) (stream k P) := by
  have := isProbabilityMeasure_uniformOn_fin (k := k)
  exact MeasurePreserving.skew_product (μa := uniformOn Set.univ) (μb := uniformOn Set.univ)
    (μc := Measure.infinitePi fun _ ↦ P) (μd := Measure.infinitePi fun _ ↦ P)
    (f := (· + 1)) (g := fun φ w ↦ if (φ : ℕ) + 1 = k then fun n ↦ w (n + 1) else w)
    ⟨measurable_of_finite _, map_add_uniformOn 1⟩
    (measurable_from_prod_countable_right fun φ ↦ by
      simp only [Function.uncurry_apply_pair]; split_ifs <;> fun_prop)
    (Filter.Eventually.of_forall fun φ ↦ by
      split_ifs
      · exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ ↦ P) Nat.succ_injective
      · exact Measure.map_id)

theorem cond_fst (j : Fin k) :
    (stream k P)[|Prod.fst ⁻¹' {j}] = (Measure.dirac j).prod (Measure.infinitePi fun _ ↦ P) := by
  have hk : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne k
  rw [ProbabilityTheory.cond, ← Set.prod_univ, stream, ← Measure.prod_restrict,
    Measure.restrict_singleton, Measure.restrict_univ, Measure.prod_prod, measure_univ, mul_one,
    uniformOn_univ_apply_singleton, Fintype.card_fin, Measure.prod_smul_left, smul_smul, inv_inv,
    ENNReal.mul_inv_cancel hk (ENNReal.natCast_ne_top k), one_smul]

theorem entropy_fst : H[Prod.fst ; stream k P] = log k := by
  have := isProbabilityMeasure_uniformOn_fin (k := k)
  rw [entropy_def, stream, Measure.map_fst_prod, measure_univ, one_smul, ← Finset.coe_univ,
    measureEntropy_uniformOn Finset.univ_nonempty, Finset.card_univ, Fintype.card_fin]

section Phase

variable {S T : Type*} [MeasurableSpace S] {X : Fin k → (ℕ → M) → S}
  (hX : ∀ j, Measurable (X j))
include hX

variable [MeasurableSingletonClass S] [Fintype S]

theorem entropy_fst_prod :
    H[fun ω ↦ (ω.1, X ω.1 ω.2) ; stream k P]
      = log k + (k : ℝ)⁻¹ * ∑ j, H[X j ; Measure.infinitePi fun _ ↦ P] := by
  have hX' : Measurable fun ω : Fin k × (ℕ → M) ↦ X ω.1 ω.2 :=
    measurable_phase hX
  rw [entropy_comm _ measurable_fst hX', chain_rule _ hX' measurable_fst, entropy_fst,
    condEntropy_eq_sum _ measurable_fst, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [measureReal_fst, cond_fst, (identDistrib_dirac_prod P hX j).entropy_eq]

variable [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]

theorem condEntropy_fst_prod {Y : Fin k → (ℕ → M) → T} (hY : ∀ j, Measurable (Y j)) :
    H[fun ω ↦ X ω.1 ω.2 | fun ω ↦ (ω.1, Y ω.1 ω.2) ; stream k P]
      = (k : ℝ)⁻¹ * ∑ j, H[X j | Y j ; Measure.infinitePi fun _ ↦ P] := by
  have hXY : ∀ j, Measurable fun w ↦ (X j w, Y j w) := fun j ↦ (hX j).prodMk (hY j)
  have hpair := entropy_fst_prod P hXY
  have hsnd := entropy_fst_prod P hY
  have hre : H[fun ω ↦ (X ω.1 ω.2, ω.1, Y ω.1 ω.2) ; stream k P]
      = H[fun ω ↦ (ω.1, X ω.1 ω.2, Y ω.1 ω.2) ; stream k P] :=
    entropy_comp_of_injective _
      (measurable_fst.prodMk (measurable_phase hXY))
      (f := fun p : Fin k × S × T ↦ (p.2.1, p.1, p.2.2)) (measurable_of_finite _)
      fun a b h ↦ by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  have hc := chain_rule (stream k P) (measurable_phase hX)
    (measurable_fst.prodMk (measurable_phase hY))
  have hcj (j : Fin k) := chain_rule (Measure.infinitePi fun _ ↦ P) (hX j) (hY j)
  simp_rw [hcj, Finset.sum_add_distrib] at hpair
  linarith

end Phase

variable [MeasurableSingletonClass M] [Fintype M] [MeasurableSpace A] (L : M → Fin k → A)

theorem measurable_char (t : ℕ) : Measurable (char L t) :=
  measurable_from_prod_countable_right fun φ ↦
    (measurable_of_finite fun m : M ↦ L m (Fin.ofNat k (t + φ))).comp
      (measurable_pi_apply ((t + φ) / k))

theorem isStationary_char : IsStationary (char L) (stream k P) :=
  .of_measurePreserving (measurePreserving_advance P) (measurable_char L) (char_succ L)

/-- The character at time `t` of the stream started at position `j`. -/
private abbrev cur (t : ℕ) (j : Fin k) (w : ℕ → M) : A := char L t (j, w)

/-- The `t` characters before it. -/
private abbrev past (t : ℕ) (j : Fin k) (w : ℕ → M) : Fin t → A := block (char L) 0 t (j, w)

/-- The characters of its word before it. -/
private abbrev pre (t : ℕ) (j : Fin k) (w : ℕ → M) : Fin ((t + j) % k) → A :=
  block (word L) 0 ((t + j) % k) (w ((t + j) / k))

private theorem measurable_cur (t : ℕ) (j : Fin k) : Measurable (cur L t j) :=
  (measurable_char L t).comp measurable_prodMk_left

private theorem measurable_past (t : ℕ) (j : Fin k) : Measurable (past L t j) :=
  (measurable_block (measurable_char L) 0 t).comp measurable_prodMk_left

private theorem measurable_pre (t : ℕ) (j : Fin k) : Measurable (pre L t j) :=
  (measurable_of_finite (block (word L) 0 ((t + j) % k))).comp
    (measurable_pi_apply ((t + j) / k))

variable [MeasurableSingletonClass A] [Fintype A]

private theorem condEntropy_cur_pre (t : ℕ) (j : Fin k) :
    H[cur L t j | pre L t j ; Measure.infinitePi fun _ ↦ P]
      = pastCondEntropy (word L) P ((t + j) % k) := by
  have := condEntropy_eval P (word L ((t + j) % k)) (block (word L) 0 ((t + j) % k))
    ((t + j) / k)
  simp only [word, fin_ofNat_mod] at this
  exact this

private theorem condEntropy_cur_pre_le (t : ℕ) (j : Fin k) :
    H[cur L t j | pre L t j ; Measure.infinitePi fun _ ↦ P]
      ≤ H[cur L t j | past L t j ; Measure.infinitePi fun _ ↦ P] := by
  set m := (t + j) / k
  have hearly : Measurable fun w : ℕ → M ↦ fun i : Fin m ↦ w i := by fun_prop
  let G : (Fin ((t + j) % k) → A) × (Fin m → M) → Fin t → A := fun x i ↦
    if h : ((i : ℕ) + j) / k < m then L (x.2 ⟨((i : ℕ) + j) / k, h⟩) (Fin.ofNat k (i + j))
    else x.1 ⟨((i : ℕ) + j) % k, mod_lt_mod_of_not_div_lt (by have := i.isLt; omega) h⟩
  have hG : past L t j = G ∘ fun w ↦ (pre L t j w, fun i : Fin m ↦ w i) := by
    funext w i
    simp only [past, pre, block, char, word, G, Function.comp_apply, add_zero, fin_ofNat_mod]
    split_ifs with h
    · rfl
    · have hle : ((i : ℕ) + (j : ℕ)) / k ≤ m :=
        Nat.div_le_div_right (by have := i.isLt; omega)
      rw [show ((i : ℕ) + (j : ℕ)) / k = m by omega]
  have hind : (fun w ↦ (cur L t j w, pre L t j w)) ⟂ᵢ[Measure.infinitePi fun _ ↦ P]
      fun w : ℕ → M ↦ fun i : Fin m ↦ w i := by
    have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ ↦ id)
      fun _ ↦ measurable_id).indepFun_finset {m} (Finset.range m) (by simp)
      (fun i ↦ measurable_pi_apply i)
    exact h.comp (φ := fun v ↦ (L (v ⟨m, Finset.mem_singleton_self m⟩) (Fin.ofNat k (t + j)),
      block (word L) 0 ((t + j) % k) (v ⟨m, Finset.mem_singleton_self m⟩)))
      (ψ := fun v (i : Fin m) ↦ v ⟨i, Finset.mem_range.mpr i.isLt⟩)
      (measurable_of_finite _) (measurable_of_finite _)
  rw [← condEntropy_prod_eq_of_indepFun _ (measurable_cur L t j) (measurable_pre L t j) hearly
    hind, hG]
  exact condEntropy_le_condEntropy_comp _ (measurable_cur L t j)
    ((measurable_pre L t j).prodMk hearly) G

private theorem condEntropy_cur_past_le {t : ℕ} (hkt : k ≤ t + 1) (j : Fin k) :
    H[cur L t j | past L t j ; Measure.infinitePi fun _ ↦ P]
      ≤ H[cur L t j | pre L t j ; Measure.infinitePi fun _ ↦ P] := by
  have hk := NeZero.pos k
  have hpk := Nat.mod_lt (t + (j : ℕ)) hk
  have hdm := Nat.div_add_mod (t + (j : ℕ)) k
  have hE : pre L t j = (fun (b : Fin t → A) (i : Fin ((t + j) % k)) ↦
      b ⟨t - (t + j) % k + i, by have := i.isLt; omega⟩) ∘ past L t j := by
    funext w i
    have hi : t - (t + (j : ℕ)) % k + i + j = i + k * ((t + j) / k) := by
      have := i.isLt; omega
    simp only [pre, past, block, char, word, Function.comp_apply, add_zero]
    rw [hi, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (i.isLt.trans hpk), zero_add]
    congr 1
    simp [Fin.ext_iff, Nat.add_mul_mod_self_left]
  rw [hE]
  exact condEntropy_le_condEntropy_comp _ (measurable_cur L t j) (measurable_past L t j) _

private theorem condEntropy_char_fst_past (t : ℕ) :
    H[char L t | fun ω ↦ (ω.1, block (char L) 0 t ω) ; stream k P]
      = (k : ℝ)⁻¹ * ∑ j, H[cur L t j | past L t j ; Measure.infinitePi fun _ ↦ P] :=
  condEntropy_fst_prod P (measurable_cur L t) (measurable_past L t)

private theorem sum_pastCondEntropy_word (t : ℕ) :
    ∑ j : Fin k, pastCondEntropy (word L) P ((t + (j : ℕ)) % k) = H[fun m ↦ L m ; P] := by
  have hw : ∀ n, Measurable (word L n) := fun _ ↦ measurable_of_finite _
  rw [← block_word L, entropy_block hw,
    ← Fin.sum_univ_eq_sum_range (fun n ↦ pastCondEntropy (word L) P n)]
  exact Fintype.sum_equiv (Equiv.addLeft (Fin.ofNat k t)) _ _ fun j ↦ by
    simp [Fin.val_add, Nat.add_mod]

theorem le_pastCondEntropy_char (t : ℕ) :
    (k : ℝ)⁻¹ * H[fun m ↦ L m ; P] ≤ pastCondEntropy (char L) (stream k P) t :=
  calc (k : ℝ)⁻¹ * H[fun m ↦ L m ; P]
      = (k : ℝ)⁻¹ * ∑ j : Fin k, pastCondEntropy (word L) P ((t + (j : ℕ)) % k) := by
        rw [sum_pastCondEntropy_word]
    _ ≤ (k : ℝ)⁻¹ * ∑ j, H[cur L t j | past L t j ; Measure.infinitePi fun _ ↦ P] := by
        gcongr with j
        rw [← condEntropy_cur_pre]
        exact condEntropy_cur_pre_le P L t j
    _ = H[char L t | fun ω ↦ (ω.1, block (char L) 0 t ω) ; stream k P] :=
        (condEntropy_char_fst_past P L t).symm
    _ ≤ pastCondEntropy (char L) (stream k P) t :=
        condEntropy_le_condEntropy_comp _ (measurable_char L t)
          (measurable_fst.prodMk (measurable_block (measurable_char L) 0 t)) Prod.snd

theorem condEntropy_char_one :
    H[char L 1 | fun ω ↦ (ω.1, char L 0 ω) ; stream k P]
      = (k : ℝ)⁻¹ * ∑ j : Fin k, if (j : ℕ) + 1 < k
          then H[fun m ↦ L m (j + 1) | fun m ↦ L m j ; P] else H[fun m ↦ L m 0 ; P] := by
  have hk := NeZero.pos k
  rw [char_zero]
  refine (condEntropy_fst_prod P (X := fun j w ↦ char L 1 (j, w))
    (Y := fun j w ↦ L (w 0) j) (fun j ↦ (measurable_char L 1).comp measurable_prodMk_left)
    (fun j ↦ (measurable_of_finite fun m ↦ L m j).comp (measurable_pi_apply 0))).trans ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with h
  · have e : (fun w : ℕ → M ↦ char L 1 (j, w)) = fun w ↦ L (w 0) (j + 1) := by
      funext w
      simp only [char, Nat.div_eq_of_lt (by omega : 1 + (j : ℕ) < k)]
      congr 1
      simp [Fin.ext_iff, Fin.val_add, add_comm]
    rw [e]
    exact condEntropy_eval P (fun m ↦ L m (j + 1)) (fun m ↦ L m j) 0
  · have e : (fun w : ℕ → M ↦ char L 1 (j, w)) = fun w ↦ L (w 1) 0 := by
      funext w
      simp only [char, show 1 + (j : ℕ) = k by have := j.isLt; omega, Nat.div_self hk]
      congr 1
      simp
    rw [e]
    exact condEntropy_eval_of_ne P (fun m ↦ L m 0) (fun m ↦ L m j) one_ne_zero

variable {L} {pos : A → Fin k} (hpos : ∀ m p, pos (L m p) = p)
include hpos

private theorem condEntropy_char_le_fst_past {t : ℕ} (ht : 0 < t) :
    pastCondEntropy (char L) (stream k P) t
      ≤ H[char L t | fun ω ↦ (ω.1, block (char L) 0 t ω) ; stream k P] := by
  have h : (fun ω ↦ (ω.1, block (char L) 0 t ω))
      = (fun b ↦ (pos (b ⟨0, ht⟩), b)) ∘ block (char L) 0 t := by
    funext ω
    simp [block, char_zero, hpos]
  rw [h]
  exact condEntropy_le_condEntropy_comp _ (measurable_char L t)
    (measurable_block (measurable_char L) 0 t) _

/-- Once the context spans a word, a language whose characters reveal their position has the
entropy of a word per character. -/
theorem pastCondEntropy_char_of_le {t : ℕ} (ht : 0 < t) (hkt : k ≤ t + 1) :
    pastCondEntropy (char L) (stream k P) t = (k : ℝ)⁻¹ * H[fun m ↦ L m ; P] := by
  refine le_antisymm ?_ (le_pastCondEntropy_char P L t)
  calc pastCondEntropy (char L) (stream k P) t
      ≤ H[char L t | fun ω ↦ (ω.1, block (char L) 0 t ω) ; stream k P] :=
        condEntropy_char_le_fst_past P hpos ht
    _ = (k : ℝ)⁻¹ * ∑ j, H[cur L t j | past L t j ; Measure.infinitePi fun _ ↦ P] :=
        condEntropy_char_fst_past P L t
    _ ≤ (k : ℝ)⁻¹ * ∑ j : Fin k, pastCondEntropy (word L) P ((t + (j : ℕ)) % k) := by
        gcongr with j
        rw [← condEntropy_cur_pre]
        exact condEntropy_cur_past_le P L hkt j
    _ = (k : ℝ)⁻¹ * H[fun m ↦ L m ; P] := by rw [sum_pastCondEntropy_word]

theorem entropyRate_char :
    entropyRate (char L) (stream k P) = (k : ℝ)⁻¹ * H[fun m ↦ L m ; P] := by
  refine le_antisymm ?_ (le_ciInf fun t ↦ le_pastCondEntropy_char P L t)
  rw [← pastCondEntropy_char_of_le P hpos (NeZero.pos k) (Nat.le_succ k)]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ condEntropy_nonneg _ _ _⟩ k

theorem pastCondEntropy_char_zero :
    pastCondEntropy (char L) (stream k P) 0 = log k + (k : ℝ)⁻¹ * ∑ p, H[fun m ↦ L m p ; P] := by
  have hX : ∀ j : Fin k, Measurable fun w : ℕ → M ↦ L (w 0) j :=
    fun j ↦ (measurable_of_finite fun m ↦ L m j).comp (measurable_pi_apply 0)
  rw [pastCondEntropy_zero (measurable_char L), char_zero,
    ← entropy_comp_of_injective _ (measurable_phase hX)
      (f := fun a ↦ (pos a, a)) (measurable_of_finite _) fun a b h ↦ (Prod.ext_iff.mp h).2,
    show (fun a ↦ (pos a, a)) ∘ (fun ω : Fin k × (ℕ → M) ↦ L (ω.2 0) ω.1)
      = fun ω ↦ (ω.1, L (ω.2 0) ω.1) by funext ω; simp [hpos],
    entropy_fst_prod P hX]
  congr 2
  exact Finset.sum_congr rfl fun j _ ↦ entropy_eval P (fun m ↦ L m j) 0

theorem pastCondEntropy_char_one :
    pastCondEntropy (char L) (stream k P) 1
      = H[char L 1 | fun ω ↦ (ω.1, char L 0 ω) ; stream k P] := by
  refine le_antisymm ?_ ?_
  · have h : (fun ω ↦ (ω.1, char L 0 ω)) = (fun b ↦ (pos (b 0), b 0)) ∘ block (char L) 0 1 := by
      funext ω
      simp [block, char_zero, hpos]
    rw [pastCondEntropy, h]
    exact condEntropy_le_condEntropy_comp _ (measurable_char L 1)
      (measurable_block (measurable_char L) 0 1) _
  · have h : block (char L) 0 1 = (fun x _ ↦ x.2) ∘ fun ω ↦ (ω.1, char L 0 ω) := by
      funext ω i
      simp [block, Fin.fin_one_eq_zero i]
    rw [pastCondEntropy, h]
    exact condEntropy_le_condEntropy_comp _ (measurable_char L 1)
      (measurable_fst.prodMk (measurable_char L 0)) _

end Stream

section Tagged

variable {M B : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype M]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B] {k : ℕ} [NeZero k]
  (P : Measure M) [IsProbabilityMeasure P] (L : M → Fin k → B)

theorem pastCondEntropy_tagged_zero :
    pastCondEntropy (char (tagged L)) (stream k P) 0
      = log k + (k : ℝ)⁻¹ * ∑ p, H[fun m ↦ L m p ; P] := by
  rw [pastCondEntropy_char_zero P (L := tagged L) (pos := Prod.fst) fun _ _ ↦ rfl]
  congr 2
  exact Finset.sum_congr rfl fun p _ ↦ entropy_comp_of_injective P (measurable_of_finite _)
    (f := Prod.mk p) (measurable_of_finite _) (Prod.mk_right_injective p)

theorem pastCondEntropy_tagged_one :
    pastCondEntropy (char (tagged L)) (stream k P) 1
      = (k : ℝ)⁻¹ * ∑ j : Fin k, if (j : ℕ) + 1 < k
          then H[fun m ↦ L m (j + 1) | fun m ↦ L m j ; P] else H[fun m ↦ L m 0 ; P] := by
  rw [pastCondEntropy_char_one P (L := tagged L) (pos := Prod.fst) (fun _ _ ↦ rfl),
    condEntropy_char_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs
  · exact condEntropy_tag P j (j + 1) _ _
  · exact entropy_comp_of_injective P (measurable_of_finite _) (f := Prod.mk 0)
      (measurable_of_finite _) (Prod.mk_right_injective 0)

theorem pastCondEntropy_tagged_of_le {t : ℕ} (ht : 0 < t) (hkt : k ≤ t + 1) :
    pastCondEntropy (char (tagged L)) (stream k P) t = (k : ℝ)⁻¹ * H[fun m ↦ L m ; P] := by
  rw [pastCondEntropy_char_of_le P (L := tagged L) (pos := Prod.fst) (fun _ _ ↦ rfl) ht hkt]
  congr 1
  exact entropy_comp_of_injective P (measurable_of_finite fun m ↦ L m) (f := fun v p ↦ (p, v p))
    (measurable_of_finite _) fun _ _ h ↦ funext fun p ↦ (Prod.ext_iff.mp (congrFun h p)).2

end Tagged

/-! ### The toy languages -/

section Bits

open unitInterval

/-- The fair coin as a point of the unit interval. -/
noncomputable def half : I := ⟨2⁻¹, by norm_num, by norm_num⟩

/-- Independent bits, bit `i` being `true` with probability `p i`. -/
noncomputable def bits {n : ℕ} (p : Fin n → I) : Measure (Fin n → Bool) :=
  Measure.pi fun i ↦ Ber(true, false, p i)

variable {n : ℕ} (p : Fin n → I)

instance : IsProbabilityMeasure (bits p) := by unfold bits; infer_instance

theorem iIndepFun_bits : iIndepFun (fun i (ω : Fin n → Bool) ↦ ω i) (bits p) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

theorem entropy_bit (i : Fin n) :
    H[fun ω : Fin n → Bool ↦ ω i ; bits p] = binEntropy (p i) := by
  show Hm[(bits p).map (Function.eval i)] = _
  rw [bits, (measurePreserving_eval _ i).map_eq,
    measureEntropy_bernoulliMeasure (by decide : true ≠ false)]

theorem bits_real_singleton (x : Fin n → Bool) :
    (bits p).real {x} = ∏ i, if x i then (p i : ℝ) else 1 - p i := by
  rw [← Set.univ_pi_singleton, measureReal_def, bits, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases x i <;> simp

end Bits

/-! #### Fusion lowers local surprisal, Table 4 -/

namespace VoiceTense

open unitInterval

/-- The meanings of Tables 4 and 6 when tense disagrees with voice with probability `d`. The
first bit is the voice, a fair coin, and the second says whether tense disagrees with voice. -/
noncomputable def meanings (d : I) : Measure (Fin 2 → Bool) := bits ![half, d]

/-- The voice feature, `false` for active. -/
def voice (ω : Fin 2 → Bool) : Bool := ω 0

/-- The tense feature, `false` for present. -/
def tense (ω : Fin 2 → Bool) : Bool := xor (ω 0) (ω 1)

variable (d : I)

instance : IsProbabilityMeasure (meanings d) := by unfold meanings; infer_instance

private theorem indep : (fun ω : Fin 2 → Bool ↦ ω 0) ⟂ᵢ[meanings d] fun ω ↦ ω 1 :=
  (iIndepFun_bits _).indepFun (i := 0) (j := 1) (by decide)

/-- Voice and tense agree with probability `1 - d`, as in the probabilities of Table 4. -/
theorem meanings_real (v t : Bool) :
    (meanings d).real {ω | voice ω = v ∧ tense ω = t} = (if v = t then 1 - (d : ℝ) else d) / 2 := by
  have : {ω : Fin 2 → Bool | voice ω = v ∧ tense ω = t} = {![v, xor v t]} := by
    ext ω
    refine ⟨fun ⟨hv, ht⟩ ↦ ?_, fun (h : ω = _) ↦ by simp [h, voice, tense]⟩
    subst hv ht
    ext i; fin_cases i <;> simp [voice, tense]
  rw [this, meanings, bits_real_singleton]
  cases v <;> cases t <;> simp [Fin.prod_univ_two, half] <;> ring

theorem entropy_voice : H[voice ; meanings d] = log 2 := by
  rw [show voice = fun ω : Fin 2 → Bool ↦ ω 0 from rfl, meanings, entropy_bit]
  simp [half]

theorem condEntropy_tense_voice : H[tense | voice ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) | fun ω ↦ ω 0 ; meanings d] = _
  rw [condEntropy_of_injective (meanings d) (measurable_pi_apply 1) (measurable_pi_apply 0) xor
    fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d).symm.condEntropy_eq_entropy (measurable_pi_apply 1) (measurable_pi_apply 0),
    meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (measurable_pi_apply 0) (measurable_pi_apply 1) (indep d)
    (entropy_voice d)

theorem mutualInfo_tense_voice : I[tense : voice ; meanings d] = log 2 - binEntropy d := by
  rw [mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense)
    (measurable_of_finite voice), entropy_tense, condEntropy_tense_voice]

/-- The agglutinative language `Lagg` writes voice in its first slot and tense in its second.
Tagged by slot, it is also the language `Lclustered` of Table 6, which writes the voice morpheme
and then the tense morpheme, the category clustering of [mansfield-stoll-bickel-2020]. -/
def agg (ω : Fin 2 → Bool) : Fin 2 → Bool := ![voice ω, tense ω]

/-- The fusional language `Lfus` writes voice and then the exclusive or of the two features. -/
def fus (ω : Fin 2 → Bool) : Fin 2 → Bool := ![voice ω, xor (voice ω) (tense ω)]

theorem entropy_fus_one : H[fun ω ↦ fus ω 1 ; meanings d] = binEntropy d := by
  rw [show (fun ω ↦ fus ω 1) = fun ω : Fin 2 → Bool ↦ ω 1 by
    funext ω; simp [fus, voice, tense], meanings, entropy_bit]
  rfl

private theorem entropy_meaning :
    H[fun ω : Fin 2 → Bool ↦ ω ; meanings d] = log 2 + binEntropy d := by
  rw [← entropy_comp_of_injective _ measurable_id' (f := fun ω : Fin 2 → Bool ↦ (ω 0, ω 1))
    (measurable_of_finite _) (by decide)]
  rw [show (fun ω : Fin 2 → Bool ↦ (ω 0, ω 1)) ∘ (fun ω ↦ ω) = fun ω ↦ (ω 0, ω 1) from rfl,
    (indep d).entropy_pair_eq_add (measurable_pi_apply 0) (measurable_pi_apply 1),
    show (fun ω : Fin 2 → Bool ↦ ω 0) = voice from rfl, entropy_voice, meanings, entropy_bit]
  rfl

private theorem entropy_injective {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    {f : (Fin 2 → Bool) → B} (hf : f.Injective) : H[f ; meanings d] = log 2 + binEntropy d := by
  rw [← entropy_meaning d]
  exact entropy_comp_of_injective _ measurable_id' (measurable_of_finite f) hf

/-- With no context, the fusional language is less surprising exactly when the features are
dependent. -/
theorem pastCondEntropy_fus_lt_agg_zero_iff :
    pastCondEntropy (char (tagged fus)) (stream 2 (meanings d)) 0
      < pastCondEntropy (char (tagged agg)) (stream 2 (meanings d)) 0 ↔ (d : ℝ) ≠ 2⁻¹ := by
  rw [pastCondEntropy_tagged_zero, pastCondEntropy_tagged_zero, Fin.sum_univ_two,
    Fin.sum_univ_two, ← binEntropy_lt_log_two]
  simp only [agg, fus, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (fun ω ↦ xor (voice ω) (tense ω)) = fun ω ↦ fus ω 1 from rfl, entropy_fus_one,
    entropy_voice, entropy_tense]
  constructor <;> intro h <;> linarith

theorem pastCondEntropy_fus_eq_agg {t : ℕ} (ht : 0 < t) :
    pastCondEntropy (char (tagged fus)) (stream 2 (meanings d)) t
      = pastCondEntropy (char (tagged agg)) (stream 2 (meanings d)) t := by
  rw [pastCondEntropy_tagged_of_le _ _ ht (by omega),
    pastCondEntropy_tagged_of_le _ _ ht (by omega),
    entropy_injective d (f := fus) (by decide), entropy_injective d (f := agg) (by decide)]

theorem mutualInfo_disagree_tense : I[fun ω ↦ ω 1 : tense ; meanings d] = 0 := by
  rw [mutualInfo_comm _ (measurable_pi_apply 1) (measurable_of_finite tense),
    mutualInfo_eq_entropy_sub_condEntropy _ (measurable_of_finite tense) (measurable_pi_apply 1),
    show tense = fun ω : Fin 2 → Bool ↦ xor (ω 0) (ω 1) from rfl,
    condEntropy_xor_eq_entropy (measurable_pi_apply 0) (measurable_pi_apply 1) (indep d)]
  exact sub_eq_zero.mpr ((entropy_tense d).trans (entropy_voice d).symm)

/-- The hypotheses the appendix states for its second argument do not suffice. Take the
disagreement bit as a first feature: it is independent of voice and of tense, and voice and
tense share information, yet a part that fuses it with voice determines tense. -/
theorem condEntropy_fused_lt (h₀ : 0 < (d : ℝ)) (h₁ : (d : ℝ) < 1) (hd : (d : ℝ) ≠ 2⁻¹) :
    I[fun ω ↦ ω 1 : voice ; meanings d] = 0 ∧ I[fun ω ↦ ω 1 : tense ; meanings d] = 0 ∧
      0 < I[tense : voice ; meanings d] ∧
      H[tense | fun ω ↦ (ω 1, voice ω) ; meanings d] < H[tense | voice ; meanings d] := by
  have h0 : H[tense | fun ω ↦ (ω 1, voice ω) ; meanings d] = 0 :=
    condEntropy_comp_self _ ((measurable_pi_apply 1).prodMk (measurable_of_finite voice))
      fun p : Bool × Bool ↦ xor p.2 p.1
  refine ⟨(mutualInfo_eq_zero_iff _ (measurable_pi_apply 1) (measurable_pi_apply 0)).mpr
    (indep d).symm, mutualInfo_disagree_tense d, ?_, ?_⟩
  · rw [mutualInfo_tense_voice, sub_pos]
    exact binEntropy_lt_log_two.mpr hd
  · rw [h0, condEntropy_tense_voice]
    exact binEntropy_pos h₀ h₁

/-! #### Category clustering, Table 6 -/

/-- The language `Lnonclustered` of Table 6 writes the tense morpheme first when tense disagrees
with voice. A morpheme is its category, `0` for voice and `1` for tense, and its value. -/
def nonclustered (ω : Fin 2 → Bool) : Fin 2 → Fin 2 × Bool :=
  if ω 1 then ![(1, tense ω), (0, voice ω)] else ![(0, voice ω), (1, tense ω)]

theorem entropy_nonclustered_fst :
    H[fun ω ↦ nonclustered ω 0 ; meanings d] = log 2 + binEntropy d :=
  entropy_injective d (by decide)

theorem entropy_nonclustered_fst_half :
    H[fun ω ↦ nonclustered ω 0 ; meanings half] = 2 * H[voice ; meanings half] := by
  rw [entropy_nonclustered_fst, entropy_voice]
  simp [half]
  ring

theorem entropy_nonclustered_snd :
    H[fun ω ↦ nonclustered ω 1 ; meanings d] = log 2 + binEntropy d :=
  entropy_injective d (by decide)

/-- The start of the stream flipped where tense disagrees with voice. -/
private def flip (ω : Fin 2 × (ℕ → Fin 2 → Bool)) : Fin 2 × (ℕ → Fin 2 → Bool) :=
  (ω.1 + if ω.2 0 1 then 1 else 0, ω.2)

private theorem char_nonclustered_zero :
    char nonclustered 0 = char (tagged agg) 0 ∘ flip := by
  funext ⟨φ, w⟩
  simp only [char_zero, Function.comp_apply, flip]
  fin_cases φ <;> by_cases h : w 0 1 <;> simp [nonclustered, tagged, agg, h]

private theorem measurePreserving_flip :
    MeasurePreserving flip (stream 2 (meanings d)) (stream 2 (meanings d)) := by
  have := isProbabilityMeasure_uniformOn_fin (k := 2)
  have hS : MeasurePreserving
      (fun p : (ℕ → Fin 2 → Bool) × Fin 2 ↦ (p.1, p.2 + if p.1 0 1 then 1 else 0))
      ((Measure.infinitePi fun _ ↦ meanings d).prod (uniformOn Set.univ))
      ((Measure.infinitePi fun _ ↦ meanings d).prod (uniformOn Set.univ)) :=
    (MeasurePreserving.id (Measure.infinitePi fun _ ↦ meanings d)).skew_product
      (μc := uniformOn Set.univ) (μd := uniformOn Set.univ)
      (g := fun w φ ↦ φ + if w 0 1 then 1 else 0)
      (measurable_from_prod_countable_left fun φ ↦ (measurable_of_finite
        fun b : Bool ↦ φ + if b then 1 else 0).comp
        ((measurable_pi_apply 1).comp (measurable_pi_apply 0)))
      (Filter.Eventually.of_forall fun w ↦ map_add_uniformOn _)
  exact Measure.measurePreserving_swap.comp (hS.comp Measure.measurePreserving_swap)

/-- Without context, dropping category clustering leaves the surprisal unchanged: the uniformly
random start averages away which category comes first. -/
theorem pastCondEntropy_nonclustered_zero :
    pastCondEntropy (char nonclustered) (stream 2 (meanings d)) 0
      = pastCondEntropy (char (tagged agg)) (stream 2 (meanings d)) 0 := by
  rw [pastCondEntropy_zero (measurable_char _), pastCondEntropy_zero (measurable_char _),
    char_nonclustered_zero]
  exact ((measurePreserving_flip d).identDistrib_comp (measurable_char _ 0)).entropy_eq

theorem pastCondEntropy_tagged_agg_one_le :
    pastCondEntropy (char (tagged agg)) (stream 2 (meanings d)) 1
      ≤ pastCondEntropy (char nonclustered) (stream 2 (meanings d)) 1 := by
  rw [pastCondEntropy_tagged_of_le _ _ one_pos le_rfl, entropy_injective d (f := agg) (by decide),
    ← entropy_injective d (f := nonclustered) (by decide)]
  exact le_pastCondEntropy_char _ _ 1

/-- At the paper's uniform weights, the clustered language is strictly less surprising with one
character of context: in the nonclustered stream two consecutive characters still carry
information about where the stream started, since two voice morphemes in a row cross a word
boundary. -/
theorem pastCondEntropy_tagged_agg_one_lt :
    pastCondEntropy (char (tagged agg)) (stream 2 (meanings half)) 1
      < pastCondEntropy (char nonclustered) (stream 2 (meanings half)) 1 := by
  set μ := stream 2 (meanings half)
  set c := char nonclustered
  have hc : ∀ t, Measurable (c t) := measurable_char nonclustered
  have hZ : Measurable fun ω ↦ (c 0 ω, c 1 ω) := (hc 0).prodMk (hc 1)
  have h2 : binEntropy ((half : I) : ℝ) = log 2 := by simp [half]
  -- the clustered language reaches the entropy rate with one character of context
  have hclu : pastCondEntropy (char (tagged agg)) μ 1 = log 2 := by
    rw [pastCondEntropy_tagged_of_le _ _ one_pos le_rfl,
      entropy_injective half (f := agg) (by decide), h2]
    push_cast; ring
  -- the nonclustered surprisal is the entropy of a pair less that of its first character
  have hb : block c 0 1 = (fun x (_ : Fin 1) ↦ x) ∘ c 0 := by
    funext ω i
    simp [block, Fin.fin_one_eq_zero i]
  have hblock : pastCondEntropy c μ 1 = H[c 1 | c 0 ; μ] := le_antisymm
    (condEntropy_le_condEntropy_comp μ (hc 1) (measurable_block hc 0 1) (fun b ↦ b 0))
    (by rw [pastCondEntropy, hb]; exact condEntropy_le_condEntropy_comp μ (hc 1) (hc 0) _)
  have hc0 : H[c 0 ; μ] = 2 * log 2 := by
    rw [← pastCondEntropy_zero hc, pastCondEntropy_nonclustered_zero,
      pastCondEntropy_tagged_zero, Fin.sum_univ_two]
    simp only [agg, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [entropy_voice, entropy_tense]
    push_cast; ring
  -- averaged over the start, the pair is a word or two independent characters
  have hphase : H[fun ω ↦ (ω.1, c 0 ω, c 1 ω) ; μ] = 4 * log 2 := by
    rw [entropy_fst_prod (meanings half) (X := fun j w ↦ (c 0 (j, w), c 1 (j, w)))
      fun j ↦ ((hc 0).prodMk (hc 1)).comp measurable_prodMk_left, Fin.sum_univ_two]
    rw [show (fun w : ℕ → Fin 2 → Bool ↦ (c 0 (0, w), c 1 (0, w)))
        = fun w ↦ (nonclustered (w 0) 0, nonclustered (w 0) 1) by
        funext w; simp [c, char],
      show (fun w : ℕ → Fin 2 → Bool ↦ (c 0 (1, w), c 1 (1, w)))
        = fun w ↦ (nonclustered (w 0) 1, nonclustered (w 1) 0) by
        funext w; simp [c, char],
      entropy_eval (meanings half) (fun m ↦ (nonclustered m 0, nonclustered m 1)) 0,
      entropy_eval_pair (meanings half) (fun m ↦ nonclustered m 1) (fun m ↦ nonclustered m 0)
        zero_ne_one,
      entropy_injective half (by decide), entropy_nonclustered_fst, entropy_nonclustered_snd, h2]
    push_cast; ring
  -- the start is not independent of two consecutive characters
  have hdep : ¬ (Prod.fst ⟂ᵢ[μ] fun ω ↦ (c 0 ω, c 1 ω)) := by
    intro hind
    set x : (Fin 2 × Bool) × (Fin 2 × Bool) := ((0, false), (0, false))
    have h := hind.measure_inter_preimage_eq_mul {0} {x} (measurableSet_singleton _)
      (measurableSet_singleton _)
    have hempty : Prod.fst ⁻¹' {(0 : Fin 2)} ∩ (fun ω ↦ (c 0 ω, c 1 ω)) ⁻¹' {x} = ∅ := by
      ext ⟨φ, w⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      by_cases h1 : w 0 1 <;> simp [c, char, nonclustered, x, h1]
    have hfst : μ (Prod.fst ⁻¹' {(0 : Fin 2)}) ≠ 0 := by
      intro h0
      have := measureReal_fst (meanings half) (0 : Fin 2)
      rw [measureReal_def, h0] at this
      norm_num at this
    set a : Fin 2 → Bool := ![false, true]
    set b : Fin 2 → Bool := ![false, false]
    have hsub : ({(1 : Fin 2)} : Set (Fin 2)) ×ˢ ((fun w : ℕ → Fin 2 → Bool ↦ (w 0, w 1)) ⁻¹'
        {(a, b)}) ⊆ (fun ω ↦ (c 0 ω, c 1 ω)) ⁻¹' {x} := by
      rintro ⟨φ, w⟩ ⟨hφ, hw⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Prod.mk.injEq] at hφ hw
      simp [c, char, nonclustered, hφ, hw.1, hw.2, x, a, b, voice, tense]
    have hpos (m : Fin 2 → Bool) : (meanings half) {m} ≠ 0 := by
      intro h0
      have := bits_real_singleton ![half, half] m
      rw [measureReal_def, ← meanings, h0] at this
      fin_cases m <;> simp [half] at this <;> norm_num at this
    have hpair : μ (({(1 : Fin 2)} : Set (Fin 2)) ×ˢ
        ((fun w : ℕ → Fin 2 → Bool ↦ (w 0, w 1)) ⁻¹' {(a, b)})) ≠ 0 := by
      have := isProbabilityMeasure_uniformOn_fin (k := 2)
      rw [show μ = stream 2 (meanings half) from rfl, stream, Measure.prod_prod,
        ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
        Measure.infinitePi_map_eval_prod zero_ne_one, ← Set.singleton_prod_singleton,
        Measure.prod_prod, uniformOn_univ_apply_singleton, Fintype.card_fin]
      simp [hpos]
    rw [hempty, measure_empty] at h
    exact mul_ne_zero hfst (fun h0 ↦ hpair (measure_mono_null hsub h0)) h.symm
  have hI : 0 < I[Prod.fst : fun ω ↦ (c 0 ω, c 1 ω) ; μ] :=
    (mutualInfo_nonneg μ measurable_fst hZ).lt_of_ne fun h0 ↦
      hdep ((mutualInfo_eq_zero_iff μ measurable_fst hZ).mp h0.symm)
  rw [mutualInfo_eq_entropy_sub_condEntropy μ measurable_fst hZ, entropy_fst,
    Nat.cast_ofNat] at hI
  rw [hclu, hblock]
  linarith [chain_rule μ (hc 1) (hc 0), entropy_comm μ (hc 1) (hc 0),
    chain_rule μ measurable_fst hZ]

end VoiceTense

/-! #### Fusing independent features raises long-range surprisal, Table 5 -/

namespace VoiceAspectTense

open unitInterval

/-- The meanings of Table 5 when tense disagrees with aspect with probability `d`. Voice and
aspect are fair coins, and the third bit says whether tense disagrees with aspect. -/
noncomputable def meanings (d : I) : Measure (Fin 3 → Bool) := bits ![half, half, d]

/-- The voice feature, `false` for active. -/
def voice (ω : Fin 3 → Bool) : Bool := ω 0

/-- The aspect feature, `false` for perfect. -/
def aspect (ω : Fin 3 → Bool) : Bool := ω 1

/-- The tense feature, `false` for present. -/
def tense (ω : Fin 3 → Bool) : Bool := xor (ω 1) (ω 2)

/-- The agglutinative language `Lagg` writes each feature in its own slot. -/
def agg (ω : Fin 3 → Bool) : Fin 3 → Bool := ![voice ω, aspect ω, tense ω]

/-- The language `Lfuse-low` fuses the independent voice and aspect in its second slot. -/
def fuseLow (ω : Fin 3 → Bool) : Fin 3 → Bool := ![voice ω, xor (voice ω) (aspect ω), tense ω]

/-- The language `Lfuse-high` fuses the dependent aspect and tense in its third slot. -/
def fuseHigh (ω : Fin 3 → Bool) : Fin 3 → Bool := ![voice ω, aspect ω, xor (aspect ω) (tense ω)]

variable (d : I)

instance : IsProbabilityMeasure (meanings d) := by unfold meanings; infer_instance

private theorem indep {i j : Fin 3} (hij : i ≠ j) :
    (fun ω : Fin 3 → Bool ↦ ω i) ⟂ᵢ[meanings d] fun ω ↦ ω j :=
  (iIndepFun_bits _).indepFun hij

private theorem entropy_fair {i : Fin 3} (hi : i ≠ 2) :
    H[fun ω : Fin 3 → Bool ↦ ω i ; meanings d] = log 2 := by
  rw [meanings, entropy_bit]
  fin_cases i <;> simp_all [half]

/-- Aspect and tense agree with probability `1 - d`, as in the probabilities of Table 5. -/
theorem meanings_real (v a t : Bool) :
    (meanings d).real {ω | voice ω = v ∧ aspect ω = a ∧ tense ω = t}
      = (if a = t then 1 - (d : ℝ) else d) / 4 := by
  have : {ω : Fin 3 → Bool | voice ω = v ∧ aspect ω = a ∧ tense ω = t} = {![v, a, xor a t]} := by
    ext ω
    refine ⟨fun ⟨hv, ha, ht⟩ ↦ ?_, fun (h : ω = _) ↦ by simp [h, voice, aspect, tense]⟩
    subst hv ha ht
    ext i; fin_cases i <;> simp [voice, aspect, tense]
  rw [this, meanings, bits_real_singleton]
  cases v <;> cases a <;> cases t <;> simp [Fin.prod_univ_three, half] <;> ring

theorem condEntropy_tense_aspect : H[tense | aspect ; meanings d] = binEntropy d := by
  show H[fun ω : Fin 3 → Bool ↦ xor (ω 1) (ω 2) | fun ω ↦ ω 1 ; meanings d] = _
  rw [condEntropy_of_injective (meanings d) (measurable_pi_apply 2) (measurable_pi_apply 1) xor
    fun _ _ _ ↦ Bool.xor_right_inj.mp,
    (indep d (by decide)).condEntropy_eq_entropy (measurable_pi_apply 2) (measurable_pi_apply 1),
    meanings, entropy_bit]
  rfl

theorem entropy_tense : H[tense ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (measurable_pi_apply 1) (measurable_pi_apply 2) (indep d (by decide))
    (entropy_fair d (by decide))

theorem condEntropy_fuseHigh :
    H[fun ω ↦ fuseHigh ω 2 | fun ω ↦ fuseHigh ω 1 ; meanings d] = binEntropy d := by
  rw [show (fun ω ↦ fuseHigh ω 2) = fun ω : Fin 3 → Bool ↦ ω 2 by
      funext ω; simp [fuseHigh, aspect, tense]]
  show H[fun ω : Fin 3 → Bool ↦ ω 2 | fun ω ↦ ω 1 ; meanings d] = _
  rw [(indep d (by decide)).condEntropy_eq_entropy (measurable_pi_apply 2) (measurable_pi_apply 1),
    meanings, entropy_bit]
  rfl

theorem condEntropy_agg_le_fuseLow :
    H[fun ω ↦ agg ω 2 | fun ω ↦ agg ω 1 ; meanings d]
      ≤ H[fun ω ↦ fuseLow ω 2 | fun ω ↦ fuseLow ω 1 ; meanings d] := by
  have hind : voice ⟂ᵢ[meanings d] fun ω ↦ (aspect ω, tense ω) :=
    (((iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 2 0 (by decide)
      (by decide)).symm).comp measurable_id (measurable_of_finite fun p : Bool × Bool ↦
        (p.1, xor p.1 p.2))
  exact condEntropy_le_condEntropy_fused (measurable_pi_apply 0) (measurable_pi_apply 1)
    (measurable_of_finite tense) hind xor

theorem condEntropy_fuseLow :
    H[fun ω ↦ fuseLow ω 2 | fun ω ↦ fuseLow ω 1 ; meanings d] = log 2 := by
  show H[tense | fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) ; meanings d] = _
  have hY : Measurable fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1) := measurable_of_finite _
  refine le_antisymm ((condEntropy_le_entropy _ (measurable_of_finite tense) hY).trans
    (entropy_tense d).le) ?_
  -- given the disagreement bit, `(tense, xor voice aspect)` is a recoding of `(aspect, voice)`
  have h10 : Measurable fun ω : Fin 3 → Bool ↦ (ω 1, ω 0) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 0)
  have hinj : ∀ b : Bool, (fun p : Bool × Bool ↦ (xor p.1 b, xor p.2 p.1)).Injective := by
    decide
  have hrec : H[fun ω ↦ (tense ω, xor (ω 0) (ω 1)) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d]
      = H[fun ω ↦ (ω 1, ω 0) | fun ω : Fin 3 → Bool ↦ ω 2 ; meanings d] :=
    condEntropy_of_injective _ h10 (measurable_pi_apply 2)
      (fun b (p : Bool × Bool) ↦ (xor p.1 b, xor p.2 p.1)) hinj
  have hpair := condEntropy_le_entropy (meanings d)
    ((measurable_of_finite tense).prodMk hY) (measurable_pi_apply 2)
  have hind : (fun ω : Fin 3 → Bool ↦ (ω 1, ω 0)) ⟂ᵢ[meanings d] fun ω ↦ ω 2 :=
    (iIndepFun_bits _).indepFun_prodMk (fun i ↦ measurable_pi_apply i) 1 0 2 (by decide)
      (by decide)
  rw [hrec, hind.condEntropy_eq_entropy h10 (measurable_pi_apply 2),
    (indep d (by decide)).entropy_pair_eq_add (measurable_pi_apply 1) (measurable_pi_apply 0),
    entropy_fair d (by decide), entropy_fair d (by decide)] at hpair
  linarith [chain_rule (meanings d) (measurable_of_finite tense) hY,
    show H[fun ω ↦ xor (ω 0) (ω 1) ; meanings d] ≤ log 2 by
      simpa using entropy_le_log_card (fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1)) (meanings d)]

private theorem pastCondEntropy_zero_three (L : (Fin 3 → Bool) → Fin 3 → Bool) :
    pastCondEntropy (char (tagged L)) (stream 3 (meanings d)) 0 = log 3 + 3⁻¹ *
      (H[fun ω ↦ L ω 0 ; meanings d] + H[fun ω ↦ L ω 1 ; meanings d]
        + H[fun ω ↦ L ω 2 ; meanings d]) := by
  rw [pastCondEntropy_tagged_zero, Fin.sum_univ_three]
  norm_num

private theorem pastCondEntropy_one_three (L : (Fin 3 → Bool) → Fin 3 → Bool) :
    pastCondEntropy (char (tagged L)) (stream 3 (meanings d)) 1 = 3⁻¹ *
      (H[fun ω ↦ L ω 1 | fun ω ↦ L ω 0 ; meanings d]
        + H[fun ω ↦ L ω 2 | fun ω ↦ L ω 1 ; meanings d] + H[fun ω ↦ L ω 0 ; meanings d]) := by
  rw [pastCondEntropy_tagged_one, Fin.sum_univ_three]
  norm_num

private theorem entropy_aspect : H[fun ω ↦ agg ω 1 ; meanings d] = log 2 :=
  entropy_fair d (i := 1) (by decide)

private theorem entropy_fuseLow_one : H[fun ω ↦ fuseLow ω 1 ; meanings d] = log 2 :=
  entropy_xor_eq_log_two (measurable_pi_apply 0) (measurable_pi_apply 1) (indep d (by decide))
    (entropy_fair d (by decide))

private theorem entropy_fuseHigh_two : H[fun ω ↦ fuseHigh ω 2 ; meanings d] = binEntropy d := by
  rw [show (fun ω ↦ fuseHigh ω 2) = fun ω : Fin 3 → Bool ↦ ω 2 by
    funext ω; simp [fuseHigh, aspect, tense], meanings, entropy_bit]
  rfl

private theorem condEntropy_aspect_voice :
    H[fun ω ↦ agg ω 1 | fun ω ↦ agg ω 0 ; meanings d] = log 2 :=
  ((indep d (i := 1) (j := 0) (by decide)).condEntropy_eq_entropy (measurable_pi_apply 1)
    (measurable_pi_apply 0)).trans (entropy_fair d (by decide))

theorem pastCondEntropy_fuseLow_zero :
    pastCondEntropy (char (tagged fuseLow)) (stream 3 (meanings d)) 0
      = pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) 0 := by
  rw [pastCondEntropy_zero_three, pastCondEntropy_zero_three, entropy_fuseLow_one, entropy_aspect]
  rfl

theorem pastCondEntropy_fuseHigh_lt_agg_zero_iff :
    pastCondEntropy (char (tagged fuseHigh)) (stream 3 (meanings d)) 0
      < pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) 0 ↔ (d : ℝ) ≠ 2⁻¹ := by
  rw [pastCondEntropy_zero_three, pastCondEntropy_zero_three, entropy_fuseHigh_two,
    show (fun ω ↦ agg ω 2) = tense from rfl, entropy_tense, ← binEntropy_lt_log_two,
    show (fun ω ↦ fuseHigh ω 0) = fun ω ↦ agg ω 0 from rfl,
    show (fun ω ↦ fuseHigh ω 1) = fun ω ↦ agg ω 1 from rfl]
  constructor <;> intro h <;> linarith

theorem pastCondEntropy_fuseHigh_one :
    pastCondEntropy (char (tagged fuseHigh)) (stream 3 (meanings d)) 1
      = pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) 1 := by
  rw [pastCondEntropy_one_three, pastCondEntropy_one_three, condEntropy_fuseHigh,
    show (fun ω ↦ agg ω 2) = tense from rfl, show (fun ω ↦ agg ω 1) = aspect from rfl,
    condEntropy_tense_aspect]
  rfl

/-- With one character of context, fusing the independent voice and aspect raises the surprisal
exactly when aspect and tense are dependent: the second character no longer reveals aspect. -/
theorem pastCondEntropy_agg_lt_fuseLow_one_iff :
    pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) 1
      < pastCondEntropy (char (tagged fuseLow)) (stream 3 (meanings d)) 1 ↔ (d : ℝ) ≠ 2⁻¹ := by
  rw [pastCondEntropy_one_three, pastCondEntropy_one_three, condEntropy_fuseLow,
    condEntropy_aspect_voice, show (fun ω ↦ agg ω 2) = tense from rfl,
    show (fun ω ↦ agg ω 1) = aspect from rfl, condEntropy_tense_aspect,
    show (fun ω ↦ fuseLow ω 1) = fun ω ↦ xor (ω 0) (ω 1) from rfl,
    show (fun ω ↦ fuseLow ω 0) = fun ω : Fin 3 → Bool ↦ ω 0 from rfl,
    show (fun ω ↦ agg ω 0) = fun ω : Fin 3 → Bool ↦ ω 0 from rfl,
    show (fun ω : Fin 3 → Bool ↦ xor (ω 0) (ω 1)) = fun ω ↦ xor (ω 1) (ω 0) by
      funext ω; exact Bool.xor_comm _ _,
    condEntropy_xor_eq_entropy (measurable_pi_apply 1) (measurable_pi_apply 0)
      (indep d (by decide)), entropy_fair d (i := 1) (by decide), ← binEntropy_lt_log_two]
  constructor <;> intro h <;> linarith

theorem pastCondEntropy_eq_agg {t : ℕ} (ht : 2 ≤ t) :
    pastCondEntropy (char (tagged fuseLow)) (stream 3 (meanings d)) t
        = pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) t ∧
      pastCondEntropy (char (tagged fuseHigh)) (stream 3 (meanings d)) t
        = pastCondEntropy (char (tagged agg)) (stream 3 (meanings d)) t := by
  have h (L : (Fin 3 → Bool) → Fin 3 → Bool) (hL : L.Injective) :
      pastCondEntropy (char (tagged L)) (stream 3 (meanings d)) t
        = 3⁻¹ * H[fun ω : Fin 3 → Bool ↦ ω ; meanings d] := by
    rw [pastCondEntropy_tagged_of_le _ _ (by omega) (by omega)]
    norm_num
    exact entropy_comp_of_injective _ measurable_id' (measurable_of_finite L) hL
  rw [h fuseLow (by decide), h fuseHigh (by decide), h agg (by decide)]
  exact ⟨rfl, rfl⟩

end VoiceAspectTense

end RathiHahnFutrell2026
