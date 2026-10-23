module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.RSA.Incremental

/-!
# Cohn-Gordon, Goodman and Potts (2019): An Incremental Iterated Response Model of Pragmatics

Iterated response models compute pragmatic reasoning over complete utterances; the paper
moves the reasoning inside the utterance. Utterances are word sequences from a closed set,
an incremental semantics scores a prefix at a referent by the fraction of its complete
extensions true of the referent among those true of some referent (§2.2), a word-level
literal listener renormalizes that score (eq. 4), a word-level speaker best-responds at
each prefix (eq. 5, with probability distributed evenly over words with viable
continuations when no continuation is true), and the chain rule multiplies the word
choices into an utterance-level speaker (eq. 7). On the Figure 1 reference game the
architectures come apart: the global speaker prefers the fully informative *red dress*
for the red dress while the incremental product prefers bare *dress* (Figures 1b, 1e),
and upon hearing *red* the incremental listener already favours the red hat at 0.64,
the anticipatory implicature (Figure 1d). The abstract two-letter game of Figure 3
separates the architectures even at equal global informativity. Any complete utterance
true of its referent is weakly informative, in that the literal listener assigns the referent
at least chance probability, which is the paper's certificate for greedy word-by-word
unrolling (§2.4).

With a cost of one per word and none for the STOP token (§3.1), the global speaker
prefers the bare noun in English and Spanish alike, but the incremental speaker is
indifferent between *dress* and *red dress* while preferring *vestido* to *vestido
rojo*: after *red* the English speaker is committed to the over-modified continuation,
after *vestido* the Spanish speaker may stop, which is Rubio-Fernández's over-modification
asymmetry between adjective–noun and noun–adjective languages. Hearing *tall* in
Sedivy's display, the incremental pragmatic listener favours the tall cup over the tall
pitcher at 0.6, since a speaker referring to the pitcher had no use for the modifier
(§3.2); the implicature cancels, since after *tall pitcher* the listener excludes every
referent but the pitcher.

## Implementation notes

* The reference game carries an utterance-level Boolean semantics, as the paper's
  incremental semantics is "defined in terms of a global semantics and the set of
  available complete utterances" (§2.2); word-conjunctive semantics is a constructor,
  since Figure 3's semantics is not compositional.
* Word-level agents are the kernel pipeline at prefix-indexed graded meanings; the
  uniform prior and the viable-extension denominator cancel in the literal listener, so
  every cell is a ratio of extension counts, which `decide` evaluates.
* Chain-rule trajectory probabilities are real-valued products of speaker masses, so the
  §3.1 comparisons are real arithmetic in the content-word cost factor `exp (-c)`, the
  paper's cost of one generalized to any positive cost.
* Kernels are noncomputable, so the greedy unroller is a per-referent table, certified
  to land in the utterance set and to be true of its target, which is all that §2.4's bound
  uses.

## TODO

* §4's TUNA-corpus comparison (the share of two-word optima under each architecture) is
  an experiment over corpus trials, not formalizable content.
* The general §2.4 claim that greedy unrolling always terminates in a true complete
  utterance is argued informally in the paper; here it is certified for Figure 1.

## References

* [R. Cohn-Gordon, N. D. Goodman and C. Potts, *An Incremental Iterated Response Model
  of Pragmatics* (2019)][cohn-gordon-goodman-potts-2019]
* [P. Rubio-Fernández, *How Redundant Are Redundant Color Adjectives? An Efficiency-Based
  Analysis of Color Overspecification* (2016)][rubio-fernandez-2016]
* [J. C. Sedivy, *Implicature During Real Time Conversation: A View from Language
  Processing Research* (2007)][sedivy-2007]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace CohnGordonEtAl2019

/-! ### Reference games and the incremental semantics (§2.2) -/

/-- A reference game (Figure 1a) has a closed set of complete utterances over words `U`, an
utterance-level Boolean semantics, and the referents on display. -/
structure ReferenceGame (U W : Type) where
  /-- The closed set of available complete utterances. -/
  utterances : List (List U)
  /-- The global semantics `⟦·⟧` gives the truth of a complete utterance at a referent. -/
  sem : List U → W → Bool
  /-- The referents on display. -/
  worlds : List W

namespace ReferenceGame

variable {U W : Type}

/-- A game whose semantics is word-conjunctive, from a lexicon of word extensions. -/
def ofLexicon (applies : U → W → Bool) (utts : List (List U)) (ws : List W) :
    ReferenceGame U W :=
  ⟨utts, fun u r ↦ u.all fun w ↦ applies w r, ws⟩

private theorem sum_map_ite {α : Type*} (l : List α) (p : α → Bool) :
    (l.map fun a ↦ if p a then (1 : ℝ) else 0).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih, add_comm]

variable [DecidableEq U] (g : ReferenceGame U W)

/-- The number of complete extensions of `pfx` true of `r`. -/
def trueExts (pfx : List U) (r : W) : ℕ :=
  (g.utterances.filter fun u ↦ pfx.isPrefixOf u && g.sem u r).length

/-- The number of complete extensions of `pfx` true of some referent on display. -/
def viableExts (pfx : List U) : ℕ :=
  (g.utterances.filter fun u ↦ pfx.isPrefixOf u && g.worlds.any fun r ↦ g.sem u r).length

theorem trueExts_le_viableExts (hw : ∀ r : W, r ∈ g.worlds) (pfx : List U) (r : W) :
    g.trueExts pfx r ≤ g.viableExts pfx := by
  simp only [trueExts, viableExts, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun u _ h ↦ by
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, List.any_eq_true.mpr ⟨r, hw r, h.2⟩⟩

/-- The complete utterances true of some referent on display. -/
def viable : List (List U) :=
  g.utterances.filter fun u ↦ g.worlds.any fun r ↦ g.sem u r

/-- The incremental semantics `⟦pfx⟧(r)` (§2.2) is the string meaning of the prefix at the truth
of the complete utterances, the fraction of the viable extensions of `pfx` that are true of
`r`. -/
noncomputable def incSem (pfx : List U) (r : W) : ℝ≥0∞ :=
  ENNReal.ofReal (stringMeaning g.viable (fun u r ↦ if g.sem u r then 1 else 0) pfx r)

theorem incSem_eq_div {r : W} (hr : r ∈ g.worlds) (pfx : List U) :
    g.incSem pfx r = (g.trueExts pfx r : ℝ≥0∞) / (g.viableExts pfx : ℝ≥0∞) := by
  have hp (u : List U) : decide (pfx <+: u) = pfx.isPrefixOf u := by
    rw [Bool.eq_iff_iff]; simp
  have ht : (continuations g.viable pfx).countP (g.sem · r) = g.trueExts pfx r := by
    rw [continuations, viable, List.filter_filter, List.countP_filter, trueExts,
      ← List.countP_eq_length_filter]
    refine List.countP_congr fun u _ ↦ ?_
    by_cases hs : g.sem u r
    · simp [hs, hp, List.any_eq_true.mpr ⟨r, hr, hs⟩]
    · simp [hs]
  have hv : (continuations g.viable pfx).length = g.viableExts pfx := by
    rw [continuations, viable, List.filter_filter, viableExts]
    simp only [hp]
  rw [incSem, stringMeaning, sum_map_ite, ht, hv]
  rcases Nat.eq_zero_or_pos (g.viableExts pfx) with h0 | hpos
  · have : g.trueExts pfx r = 0 := Nat.le_zero.mp (h0 ▸ by
      rw [← ht, ← hv]; exact List.countP_le_length)
    simp [h0, this]
  · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hpos), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]

variable [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-! ### The global model (§2.1) -/

/-- The complete utterances of the game, as a type. -/
def Complete : Type := {u : List U // u ∈ g.utterances}

instance : Fintype g.Complete :=
  Fintype.subtype g.utterances.toFinset fun _ ↦ List.mem_toFinset

instance : MeasurableSpace g.Complete := ⊤
instance : DiscreteMeasurableSpace g.Complete := ⟨fun _ ↦ trivial⟩
instance : DecidableEq g.Complete := Subtype.instDecidableEq

/-- The global literal listener (eq. 1) conditions the uniform prior on the utterance's
truth. -/
noncomputable def globalL0 : Kernel g.Complete W :=
  Kernel.ofDensity (uniformOn Set.univ) fun u r ↦ if g.sem u.val r then 1 else 0

instance : IsFiniteKernel g.globalL0 := inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

/-- The global pragmatic speaker (eq. 2). -/
noncomputable def globalS1 (cost : g.Complete → ℝ) : Kernel W g.Complete :=
  speaker 1 cost g.globalL0 Measure.dirac

/-- An utterance costs the sum of its words' costs (§3.1). -/
def uttCost (cost : U → ℝ) (u : List U) : ℝ := (u.map cost).sum

theorem globalL0_apply (u : g.Complete) (r : W) :
    g.globalL0 u {r}
      = (if g.sem u.val r then 1 else 0)
        / ((Finset.univ.filter fun r' ↦ g.sem u.val r').card : ℝ≥0∞) := by
  have : Nonempty W := ⟨r⟩
  rw [globalL0, Kernel.ofDensity_uniformOn_apply_singleton]
  congr 1
  rw [Finset.sum_boole]

/-- A complete utterance true of a referent gives the literal listener at least chance
probability of it, the weak informativity of §2.4. -/
theorem globalL0_ge_inv_card {u : g.Complete} {r : W} (htrue : g.sem u.val r = true) :
    ((Fintype.card W : ℝ≥0∞))⁻¹ ≤ g.globalL0 u {r} := by
  rw [globalL0_apply, ite_eq_left htrue]
  calc ((Fintype.card W : ℝ≥0∞))⁻¹
      ≤ (((Finset.univ.filter fun r' ↦ g.sem u.val r').card : ℕ) : ℝ≥0∞)⁻¹ := by
        refine ENNReal.inv_le_inv' ?_
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    _ = 1 / _ := (one_div _).symm

/-! ### The word-level pipeline (eqs. 4–6) -/

variable [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

/-- The incremental literal listener at context `ctx` (eq. 4) reweights the uniform prior by
`⟦ctx ++ [u]⟧`. -/
noncomputable def l0 (ctx : List U) : Kernel U W :=
  Kernel.ofDensity (uniformOn Set.univ) fun u ↦ g.incSem (ctx ++ [u])

instance (ctx : List U) : IsFiniteKernel (g.l0 ctx) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

theorem l0_apply (hw : ∀ r : W, r ∈ g.worlds) (ctx : List U) (u : U) (r : W) :
    g.l0 ctx u {r}
      = (g.trueExts (ctx ++ [u]) r : ℝ≥0∞) / (∑ r', (g.trueExts (ctx ++ [u]) r' : ℕ) : ℕ) := by
  have : Nonempty W := ⟨r⟩
  rw [l0, Kernel.ofDensity_uniformOn_apply_singleton]
  simp_rw [g.incSem_eq_div (hw _)]
  push_cast
  rcases Nat.eq_zero_or_pos (g.viableExts (ctx ++ [u])) with hv | hv
  · have ht : ∀ r' : W, g.trueExts (ctx ++ [u]) r' = 0 := fun r' ↦
      Nat.le_zero.mp (hv ▸ g.trueExts_le_viableExts hw _ r')
    simp [ht]
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact ENNReal.mul_div_mul_right _ _
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hv.ne'))

/-- A context `ctx` is a dead end for `r` (§2.2) when no continuation of it is true of `r`. -/
def DeadEnd (ctx : List U) (r : W) : Prop :=
  ∀ u : U, g.trueExts (ctx ++ [u]) r = 0

instance (ctx : List U) (r : W) : Decidable (g.DeadEnd ctx r) :=
  inferInstanceAs (Decidable (∀ u : U, g.trueExts (ctx ++ [u]) r = 0))

/-- The word-level speaker at context `ctx` (eq. 5) is the best response to the incremental
literal listener. At a dead end, probability is distributed evenly over the words with viable
continuations. -/
noncomputable def s1 (cost : U → ℝ) (ctx : List U) : Kernel W U :=
  Kernel.ofFunOfCountable fun r ↦
    if g.DeadEnd ctx r then
      uniformOn ↑(Finset.univ.filter fun u : U ↦ 0 < g.viableExts (ctx ++ [u]))
    else speaker 1 cost (g.l0 ctx) Measure.dirac r

theorem s1_apply {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r) (cost : U → ℝ) :
    g.s1 cost ctx r = speaker 1 cost (g.l0 ctx) Measure.dirac r := by
  rw [s1, Kernel.ofFunOfCountable_apply, ite_eq_right hnd]

theorem s1_apply_deadEnd {ctx : List U} {r : W} (hd : g.DeadEnd ctx r) (cost : U → ℝ) :
    g.s1 cost ctx r
      = uniformOn ↑(Finset.univ.filter fun u : U ↦ 0 < g.viableExts (ctx ++ [u])) := by
  rw [s1, Kernel.ofFunOfCountable_apply, ite_eq_left hd]

instance (cost : U → ℝ) (ctx : List U) : IsFiniteKernel (g.s1 cost ctx) :=
  ⟨⟨1, ENNReal.one_lt_top, fun r ↦ by
    rw [s1, Kernel.ofFunOfCountable_apply]
    split_ifs with h
    · exact prob_le_one
    · exact Kernel.ofWeights_apply_univ_le_one _ r⟩⟩

/-- The incremental pragmatic listener at context `ctx` (eq. 6) inverts the word-level speaker
against the uniform prior. -/
noncomputable def l1 (cost : U → ℝ) (ctx : List U) : Kernel U W :=
  RSA.listener (uniformOn Set.univ) (g.s1 cost ctx)

instance (cost : U → ℝ) (ctx : List U) : IsFiniteKernel (g.l1 cost ctx) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ _))

/-- The utterance-level incremental speaker (eq. 7) is the chain-rule product of the
word-level speaker's choices along the utterance. -/
noncomputable def s1Utt (cost : U → ℝ) (r : W) (u : List U) : ℝ :=
  chain (g.s1 cost) r [] u

theorem s1_real_singleton {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ}
    (u : U) :
    (g.s1 cost ctx r).real {u}
      = (g.l0 ctx u {r}).toReal * Real.exp (-cost u)
        / ∑ u', (g.l0 ctx u' {r}).toReal * Real.exp (-cost u') := by
  rw [s1_apply g hnd, speaker_dirac_real_singleton zero_le_one]
  simp only [ENNReal.rpow_one, one_mul]

/-! ### Evaluation lemmas -/

theorem l0_apply_ne_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {u : U} {r : W}
    (ht : g.trueExts (ctx ++ [u]) r ≠ 0) : g.l0 ctx u {r} ≠ 0 := by
  rw [l0_apply g hw, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast ht, ENNReal.natCast_ne_top _⟩

theorem l0_apply_eq_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {u : U} {r : W}
    (ht : g.trueExts (ctx ++ [u]) r = 0) : g.l0 ctx u {r} = 0 := by
  rw [l0_apply g hw, ht, Nat.cast_zero, ENNReal.zero_div]

theorem l0_real (hw : ∀ r : W, r ∈ g.worlds) (ctx : List U) (u : U) (r : W) :
    (g.l0 ctx u {r}).toReal
      = (g.trueExts (ctx ++ [u]) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u]) r' : ℕ) := by
  rw [l0_apply g hw, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Row preference of the incremental speaker compares weighted listener cells. -/
theorem s1_real_lt_iff {ctx : List U} {r : W} (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ}
    {u₀ : U} (h0 : g.l0 ctx u₀ {r} ≠ 0) {u u' : U} :
    (g.s1 cost ctx r).real {u} < (g.s1 cost ctx r).real {u'} ↔
      g.l0 ctx u {r} * ENNReal.ofReal (Real.exp (-cost u))
        < g.l0 ctx u' {r} * ENNReal.ofReal (Real.exp (-cost u')) := by
  rw [s1_apply g hnd, speaker_dirac_real_singleton_lt_iff zero_le_one ⟨u₀, h0⟩]
  simp only [ENNReal.rpow_one, one_mul]

theorem s1_apply_ne_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ} (ht : g.trueExts (ctx ++ [u]) r ≠ 0) :
    g.s1 cost ctx r {u} ≠ 0 := by
  rw [s1_apply g hnd]
  exact speaker_dirac_apply_singleton_ne_zero zero_le_one (g.l0_apply_ne_zero hw ht)

theorem s1_apply_eq_zero (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) (cost : U → ℝ)
    (ht : g.trueExts (ctx ++ [u]) r = 0) : g.s1 cost ctx r {u} = 0 := by
  rw [s1_apply g hnd]
  exact speaker_dirac_apply_singleton_eq_zero one_pos (g.l0_apply_eq_zero hw ht)

theorem s1_apply_eq_one (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W} {u : U}
    (hnd : ¬ g.DeadEnd ctx r) {cost : U → ℝ} (ht : g.trueExts (ctx ++ [u]) r ≠ 0)
    (hother : ∀ u' ≠ u, g.trueExts (ctx ++ [u']) r = 0) :
    g.s1 cost ctx r {u} = 1 := by
  rw [s1_apply g hnd]
  exact speaker_dirac_apply_singleton_eq_one one_pos (g.l0_apply_ne_zero hw ht)
    fun u' hu' ↦ g.l0_apply_eq_zero hw (hother u' hu')

/-- Listener preference upon a word compares the speaker's masses, since the uniform prior
cancels. -/
theorem l1_real_lt_iff {cost : U → ℝ} {ctx : List U} {u : U} {r r' : W} :
    (g.l1 cost ctx u).real {r} < (g.l1 cost ctx u).real {r'} ↔
      (g.s1 cost ctx r).real {u} < (g.s1 cost ctx r').real {u} :=
  RSA.listener_uniformOn_real_lt_iff _ u r r'

theorem l1_real_singleton {cost : U → ℝ} {ctx : List U} {u : U} (r : W) :
    (g.l1 cost ctx u).real {r}
      = (g.s1 cost ctx r).real {u} / ∑ r', (g.s1 cost ctx r').real {u} := by
  have : Nonempty W := ⟨r⟩
  simpa [l1] using RSA.listener_uniformOn_univ_real_finset (g.s1 cost ctx) u {r}

theorem s1_real_counts (hw : ∀ r : W, r ∈ g.worlds) {ctx : List U} {r : W}
    (hnd : ¬ g.DeadEnd ctx r) (u : U) :
    (g.s1 0 ctx r).real {u}
      = ((g.trueExts (ctx ++ [u]) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u]) r' : ℕ))
        / ∑ u', ((g.trueExts (ctx ++ [u']) r : ℝ) / (∑ r', g.trueExts (ctx ++ [u']) r' : ℕ)) := by
  rw [s1_real_singleton g hnd]
  simp_rw [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one, l0_real g hw]

end ReferenceGame

private theorem natCast_div_lt {a b c d : ℕ} (hd : d ≠ 0) (hab : a * d < c * b) :
    (a : ℝ≥0∞) / (b : ℕ) < (c : ℝ≥0∞) / (d : ℕ) := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness), ENNReal.toReal_div,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast,
    div_lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hb)
      (by exact_mod_cast Nat.pos_of_ne_zero hd)]
  exact_mod_cast hab

/-! ### Figure 1: the reference game -/

/-- The words of Figure 1a. -/
inductive Word
  | red | dress | object
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.red⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The referents of Figure 1a are the red dress R1, the blue dress R2, and the red hat R3. -/
inductive Referent
  | redDress | blueDress | redHat
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.redDress⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- Figure 1a has three utterances with word-conjunctive semantics over three referents. -/
def figureOne : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r ↦ match u, r with
      | .red, .redDress | .red, .redHat | .dress, .redDress | .dress, .blueDress
      | .object, _ => true
      | _, _ => false)
    [[.dress], [.red, .dress], [.red, .object]]
    [.redDress, .blueDress, .redHat]

private theorem fig1_hw : ∀ r : Referent, r ∈ figureOne.worlds := by decide

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Word → M) :
    ∑ u, f u = f .red + (f .dress + f .object) := by
  rw [show (Finset.univ : Finset Word) = {.red, .dress, .object} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-- For R1 the speaker leads with *red*, keeping both red referents viable, while *dress*
dilutes the listener over the two dresses (Figure 1c). -/
theorem adj_first_for_target :
    (figureOne.s1 0 [] .redDress).real {Word.dress}
      < (figureOne.s1 0 [] .redDress).real {Word.red} := by
  rw [figureOne.s1_real_lt_iff (by decide)
    (figureOne.l0_apply_ne_zero (u := Word.dress) fig1_hw (by decide))]
  simp only [Pi.zero_apply, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [figureOne.l0_apply fig1_hw, figureOne.l0_apply fig1_hw]
  exact natCast_div_lt (by decide) (by decide)

/-- For R1 after *red* the speaker completes with *dress*, unique to R1 (Figure 1c). -/
theorem noun_after_adj :
    (figureOne.s1 0 [.red] .redDress).real {Word.object}
      < (figureOne.s1 0 [.red] .redDress).real {Word.dress} := by
  rw [figureOne.s1_real_lt_iff (by decide)
    (figureOne.l0_apply_ne_zero (u := Word.dress) fig1_hw (by decide))]
  simp only [Pi.zero_apply, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [figureOne.l0_apply fig1_hw, figureOne.l0_apply fig1_hw]
  exact natCast_div_lt (by decide) (by decide)

/-- The blue dress R2 forces *dress* as the first word (Figure 1c). -/
theorem noun_only_for_r2 : figureOne.s1 0 [] .blueDress {Word.dress} = 1 :=
  figureOne.s1_apply_eq_one fig1_hw (by decide) (by decide) (by decide)

/-- The red hat R3 forces *red* as the first word (Figure 1c). -/
theorem adj_only_for_r3 : figureOne.s1 0 [] .redHat {Word.red} = 1 :=
  figureOne.s1_apply_eq_one fig1_hw (by decide) (by decide) (by decide)

/-- For R2 after *red*, the dead end of §2.2, probability splits evenly over the words with viable
continuations (Figure 1c). -/
theorem uniform_after_red_for_r2 :
    (figureOne.s1 0 [.red] .blueDress).real {Word.dress} = 1 / 2 ∧
    (figureOne.s1 0 [.red] .blueDress).real {Word.object} = 1 / 2 ∧
    (figureOne.s1 0 [.red] .blueDress).real {Word.red} = 0 := by
  have h := figureOne.s1_apply_deadEnd (ctx := [.red]) (r := .blueDress) (by decide) 0
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [measureReal_def, h, uniformOn_finset_apply_singleton] <;>
    · rw [show (Finset.univ.filter fun u : Word ↦
          0 < figureOne.viableExts ([Word.red] ++ [u])) = {Word.dress, Word.object} from by
          decide]
      norm_num [show ({Word.dress, Word.object} : Finset Word).card = 2 from rfl,
        show (Word.red = Word.dress ∨ Word.red = Word.object) = False from by simp]

/-! ### Figure 1d: the anticipatory implicature -/

/-- The four speaker cells behind Figures 1c–1e, at no cost, in closed form. -/
theorem s1_figureOne_values :
    (figureOne.s1 0 [] .redDress).real {Word.red} = 4 / 7 ∧
    (figureOne.s1 0 [] .redDress).real {Word.dress} = 3 / 7 ∧
    (figureOne.s1 0 [.red] .redDress).real {Word.dress} = 2 / 3 ∧
    (figureOne.s1 0 [] .redHat).real {Word.red} = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red] .redDress = 2 from rfl,
      show ∑ r', figureOne.trueExts [Word.red] r' = 3 from rfl,
      show figureOne.trueExts [Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.dress] r' = 2 from rfl,
      show figureOne.trueExts [Word.object] .redDress = 0 from rfl]
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red] .redDress = 2 from rfl,
      show ∑ r', figureOne.trueExts [Word.red] r' = 3 from rfl,
      show figureOne.trueExts [Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.dress] r' = 2 from rfl,
      show figureOne.trueExts [Word.object] .redDress = 0 from rfl]
  · rw [figureOne.s1_real_counts fig1_hw (by decide), sum_word]
    norm_num [show figureOne.trueExts [Word.red, Word.dress] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.red, Word.dress] r' = 1 from rfl,
      show figureOne.trueExts [Word.red, Word.object] .redDress = 1 from rfl,
      show ∑ r', figureOne.trueExts [Word.red, Word.object] r' = 2 from rfl,
      show figureOne.trueExts [Word.red, Word.red] .redDress = 0 from rfl]
  · rw [measureReal_def, adj_only_for_r3, ENNReal.toReal_one]

/-- On hearing *red*, the incremental listener favours the red hat over the red dress, the
anticipatory implicature (Figure 1d). -/
theorem listener_anticipation :
    (figureOne.l1 0 [] .red).real {Referent.redDress}
      < (figureOne.l1 0 [] .red).real {Referent.redHat} := by
  rw [figureOne.l1_real_lt_iff]
  rw [s1_figureOne_values.1, measureReal_def, adj_only_for_r3, ENNReal.toReal_one]
  norm_num

private theorem r2_never_opens_red : (figureOne.s1 0 [] .blueDress).real {Word.red} = 0 := by
  rw [figureOne.s1_real_counts fig1_hw (by decide)]
  norm_num [show figureOne.trueExts [Word.red] .blueDress = 0 from rfl]

/-- Exactly, `L1(R3 | red) = 1 / (4/7 + 0 + 1) = 7/11 ≈ 0.64`, the paper's 0.64
(Figure 1d). -/
theorem listener_anticipation_value :
    (figureOne.l1 0 [] .red).real {Referent.redHat} = 7 / 11 := by
  rw [figureOne.l1_real_singleton,
    show (Finset.univ : Finset Referent) = {.redDress, .blueDress, .redHat} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    s1_figureOne_values.1, r2_never_opens_red, measureReal_def, adj_only_for_r3,
    ENNReal.toReal_one]
  norm_num

/-! ### Figure 1e: the chain-rule wedge -/

/-- For R1 the chain-rule speaker (eq. 7) prefers bare *dress* to *red dress*, unlike the global
speaker of Figure 1b (Figure 1e). -/
theorem incremental_prefers_bare_noun :
    figureOne.s1Utt 0 .redDress [.red, .dress] < figureOne.s1Utt 0 .redDress [.dress] := by
  obtain ⟨h1, h2, h3, -⟩ := s1_figureOne_values
  simp only [ReferenceGame.s1Utt, chain_cons, chain_nil, List.nil_append, mul_one]
  rw [h1, h2, h3]
  norm_num

/-! ### The global model on Figure 1 (§2.1, Figure 1b) -/

theorem fig1_mem_dress : [Word.dress] ∈ figureOne.utterances := by decide
theorem fig1_mem_redDress : [Word.red, Word.dress] ∈ figureOne.utterances := by decide

/-- For the red dress the global pragmatic speaker prefers *red dress* (1/2) to bare *dress*
(1/4), the preference the chain rule reverses (Figure 1b). -/
theorem global_prefers_red_dress :
    (figureOne.globalS1 0 .redDress).real {⟨[.dress], fig1_mem_dress⟩}
      < (figureOne.globalS1 0 .redDress).real {⟨[.red, .dress], fig1_mem_redDress⟩} := by
  have key : ∀ (u : figureOne.Complete),
      figureOne.globalL0 u {Referent.redDress}
        = (if figureOne.sem u.val .redDress then 1 else 0)
          / ((Finset.univ.filter fun r' ↦ figureOne.sem u.val r').card : ℝ≥0∞) :=
    fun u ↦ figureOne.globalL0_apply u .redDress
  refine (speaker_dirac_real_singleton_lt_iff zero_le_one
    ⟨⟨[.red, .dress], fig1_mem_redDress⟩, by
      rw [key]
      norm_num [show figureOne.sem [Word.red, Word.dress] .redDress = true from rfl,
        show (Finset.univ.filter fun r' ↦
          figureOne.sem [Word.red, Word.dress] r').card = 1 from rfl]⟩).mpr ?_
  simp only [ENNReal.rpow_one, Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, mul_one, key]
  rw [show figureOne.sem [Word.dress] .redDress = true from rfl,
    show figureOne.sem [Word.red, Word.dress] .redDress = true from rfl,
    show (Finset.univ.filter fun r' ↦ figureOne.sem [Word.dress] r').card = 2 from rfl,
    show (Finset.univ.filter fun r' ↦ figureOne.sem [Word.red, Word.dress] r').card = 1
      from rfl, Nat.cast_one, Nat.cast_ofNat, div_one]
  exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top

/-! ### §2.4: greedy unrolling and weak informativity -/

/-- The greedy unrolling of Figure 1 (§2.3) takes the word-by-word argmax trajectory per
referent. -/
def greedyUnroll : Referent → List Word
  | .redDress => [.red, .dress]
  | .blueDress => [.dress]
  | .redHat => [.red, .object]

theorem greedyUnroll_complete (r : Referent) : greedyUnroll r ∈ figureOne.utterances := by
  cases r <;> decide

theorem greedyUnroll_true (r : Referent) : figureOne.sem (greedyUnroll r) r = true := by
  cases r <;> decide

/-- In Figure 1 the global literal listener gives the target of each greedy output at least
chance probability, the weak informativity of §2.4. -/
theorem greedyUnroll_weakly_informative (r : Referent) :
    ((Fintype.card Referent : ℝ≥0∞))⁻¹
      ≤ figureOne.globalL0 ⟨greedyUnroll r, greedyUnroll_complete r⟩ {r} :=
  figureOne.globalL0_ge_inv_card (greedyUnroll_true r)

/-! ### Figure 3: the abstract two-letter game

Four utterances AA, AB, BA, BB over two worlds; every pair is true except (AB, W1). The
global speaker is indifferent among W1's three true utterances, while the chain rule
prefers AA: choosing A first costs informativity (AB is false of W1), but the second
letter is then forced, and 2/5 · 1 beats 3/5 · 1/2. -/

/-- The two letters. -/
inductive Letter
  | A | B
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Letter := ⟨.A⟩
instance : MeasurableSpace Letter := ⊤
instance : DiscreteMeasurableSpace Letter := ⟨fun _ ↦ trivial⟩

/-- The two worlds. -/
inductive AbstractWorld
  | W1 | W2
  deriving DecidableEq, Fintype, Repr

instance : Nonempty AbstractWorld := ⟨.W1⟩
instance : MeasurableSpace AbstractWorld := ⊤
instance : DiscreteMeasurableSpace AbstractWorld := ⟨fun _ ↦ trivial⟩

/-- In Figure 3's game the semantics is a table, not word-conjunctive. -/
def figureThree : ReferenceGame Letter AbstractWorld where
  utterances := [[.A, .A], [.A, .B], [.B, .A], [.B, .B]]
  sem u r := !(decide (u = [.A, .B]) && decide (r = .W1))
  worlds := [.W1, .W2]

private theorem fig3_hw : ∀ r : AbstractWorld, r ∈ figureThree.worlds := by decide

private theorem sum_letter {M : Type*} [AddCommMonoid M] (f : Letter → M) :
    ∑ u, f u = f .A + f .B := by
  rw [show (Finset.univ : Finset Letter) = {.A, .B} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- For W1 the chain rule strictly prefers AA (0.4) to BA (0.3) (Figure 3, red). -/
theorem figureThree_incremental_prefers_AA :
    figureThree.s1Utt 0 .W1 [.B, .A] < figureThree.s1Utt 0 .W1 [.A, .A] := by
  simp only [ReferenceGame.s1Utt, chain_cons, chain_nil, List.nil_append, mul_one]
  rw [figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter,
    figureThree.s1_real_counts fig3_hw (by decide), sum_letter]
  norm_num [show figureThree.trueExts [Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.B] .W1 = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A] r' = 3 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B] r' = 4 from by decide,
    show figureThree.trueExts [Letter.A, Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.A, Letter.B] .W1 = 0 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A, Letter.A] r' = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.A, Letter.B] r' = 1 from by decide,
    show figureThree.trueExts [Letter.B, Letter.A] .W1 = 1 from by decide,
    show figureThree.trueExts [Letter.B, Letter.B] .W1 = 1 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B, Letter.A] r' = 2 from by decide,
    show ∑ r', figureThree.trueExts [Letter.B, Letter.B] r' = 2 from by decide]

theorem fig3_mem_AA : [Letter.A, Letter.A] ∈ figureThree.utterances := by decide
theorem fig3_mem_BA : [Letter.B, Letter.A] ∈ figureThree.utterances := by decide

/-- For W1 the global speaker is indifferent between AA and BA, which are equally true and
informative (Figure 3, green). -/
theorem figureThree_global_indifferent :
    figureThree.globalS1 0 .W1 {⟨[.A, .A], fig3_mem_AA⟩}
      = figureThree.globalS1 0 .W1 {⟨[.B, .A], fig3_mem_BA⟩} := by
  have key : ∀ (u : figureThree.Complete), figureThree.sem u.val .W1 = true →
      (Finset.univ.filter fun r' ↦ figureThree.sem u.val r').card = 2 →
      figureThree.globalL0 u {AbstractWorld.W1} = 1 / 2 := by
    intro u htrue hcard
    rw [figureThree.globalL0_apply, htrue, hcard, ite_eq_left rfl, Nat.cast_ofNat]
  rw [ReferenceGame.globalS1, speaker_dirac_apply_singleton, speaker_dirac_apply_singleton,
    key ⟨[.A, .A], fig3_mem_AA⟩ (by decide) (by decide),
    key ⟨[.B, .A], fig3_mem_BA⟩ (by decide) (by decide)]
  simp only [Pi.zero_apply]

/-! ### §3.1: over-modification and the STOP token

English: a red dress R1 and a blue hat R2, utterances *dress*, *red dress*, *hat*,
*blue hat*, each closed by STOP. Every content word carries the same cost `c` and STOP
is free. The incremental speaker is indifferent between *dress* and *red dress* at every
`c`: the first choice weighs *dress* and *red* equally, and each continuation is then
forced. Spanish puts the noun first, so *vestido* alone opens R1's utterances; the choice
between STOP and *rojo* is then cost-driven, and any dispreference for longer utterances
(`0 < c`) yields the paper's preference for the bare noun — at `c = 1`, 0.73 against
0.27. -/

namespace English

/-- English puts the adjective before the noun, and STOP closes the utterance. -/
inductive Word
  | dress | red | hat | blue | stop
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.dress⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The two referents are a red dress and a blue hat. -/
inductive Referent
  | redDress | blueHat
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.redDress⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- The English game has adjective–noun order and STOP-terminated utterances. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r ↦ match u, r with
      | .dress, .redDress | .red, .redDress | .hat, .blueHat | .blue, .blueHat
      | .stop, _ => true
      | _, _ => false)
    [[.dress, .stop], [.red, .dress, .stop], [.hat, .stop], [.blue, .hat, .stop]]
    [.redDress, .blueHat]

theorem sem_append_stop (u : List Word) (r : Referent) :
    game.sem (u ++ [.stop]) r = game.sem u r := by
  simp only [game, ReferenceGame.ofLexicon, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]

theorem utterances_stop_terminated :
    ∀ u ∈ game.utterances, u.getLast? = some Word.stop := by decide

/-- Under the cost of §3.1 every content word costs `c` and STOP nothing. -/
def cost (c : ℝ) : Word → ℝ := fun u ↦ if u = .stop then 0 else c

private theorem hw : ∀ r : Referent, r ∈ game.worlds := by decide

private theorem step1 (c : ℝ) (u : Word) (hu : u = .dress ∨ u = .red) :
    (game.s1 (cost c) [] .redDress).real {u} = 1 / 2 := by
  rw [game.s1_real_singleton (by decide)]
  rw [show (Finset.univ : Finset Word) = {.dress, .red, .hat, .blue, .stop} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have hd : (game.l0 [] .dress {Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.dress] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.dress] r' = 1 from by decide]
  have hr : (game.l0 [] .red {Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.red] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.red] r' = 1 from by decide]
  have hz : ∀ u' ∈ [Word.hat, Word.blue, Word.stop],
      (game.l0 [] u' {Referent.redDress}).toReal = 0 := by
    intro u' hu'
    fin_cases hu' <;>
      · rw [game.l0_apply_eq_zero hw (by decide), ENNReal.toReal_zero]
  have hc : ∀ u' : Word, u' ≠ .stop → Real.exp (-cost c u') = Real.exp (-c) := fun u' hu' ↦ by
    rw [cost, ite_eq_right hu']
  rcases hu with rfl | rfl <;>
    · rw [hd, hr, hz .hat (by decide), hz .blue (by decide), hz .stop (by decide),
        hc .dress (by decide), hc .red (by decide)]
      rw [div_eq_div_iff (by positivity) two_ne_zero]
      ring

private theorem forced_dress_after_red (c : ℝ) :
    game.s1 (cost c) [.red] .redDress {Word.dress} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by decide) (by decide)

private theorem forced_stop_after_dress (c : ℝ) :
    game.s1 (cost c) [.dress] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by decide) (by decide)

private theorem forced_stop_after_red_dress (c : ℝ) :
    game.s1 (cost c) [.red, .dress] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by decide) (by decide)

/-- In English (§3.1) the incremental speaker is indifferent between *dress* and *red dress* at
every content-word cost, the paper's 0.5/0.5. -/
theorem incremental_indifferent (c : ℝ) :
    game.s1Utt (cost c) .redDress [.dress, .stop]
      = game.s1Utt (cost c) .redDress [.red, .dress, .stop] := by
  simp only [ReferenceGame.s1Utt, chain_cons, chain_nil, List.nil_append,
    List.cons_append, mul_one]
  rw [step1 c .dress (Or.inl rfl), step1 c .red (Or.inr rfl), measureReal_def,
    forced_stop_after_dress, measureReal_def, forced_dress_after_red, measureReal_def,
    forced_stop_after_red_dress]
  norm_num

theorem mem_dress : [Word.dress, Word.stop] ∈ game.utterances := by decide
theorem mem_redDress : [Word.red, Word.dress, Word.stop] ∈ game.utterances := by
  decide

/-- In English (§3.1), with any length cost the global speaker prefers bare *dress*, the paper's
0.73 against 0.27 at `c = 1`. -/
theorem global_prefers_bare_noun {c : ℝ} (hc : 0 < c) :
    (game.globalS1 (fun u ↦ ReferenceGame.uttCost (cost c) u.val) .redDress).real
        {⟨[.red, .dress, .stop], mem_redDress⟩}
      < (game.globalS1 (fun u ↦ ReferenceGame.uttCost (cost c) u.val) .redDress).real
        {⟨[.dress, .stop], mem_dress⟩} := by
  have hL : ∀ u : game.Complete, game.sem u.val .redDress = true →
      (Finset.univ.filter fun r' ↦ game.sem u.val r').card = 1 →
      game.globalL0 u {Referent.redDress} = 1 := by
    intro u htrue hcard
    rw [game.globalL0_apply, htrue, hcard, ite_eq_left rfl, Nat.cast_one, div_one]
  have hc1 : ReferenceGame.uttCost (cost c) [Word.dress, Word.stop] = c := by
    simp [ReferenceGame.uttCost, cost]
  have hc2 : ReferenceGame.uttCost (cost c) [Word.red, Word.dress, Word.stop] = c + c := by
    simp [ReferenceGame.uttCost, cost]
  refine (speaker_dirac_real_singleton_lt_iff zero_le_one
    ⟨⟨[.dress, .stop], mem_dress⟩, by rw [hL _ (by decide) (by decide)]; exact one_ne_zero⟩).mpr ?_
  simp only [ENNReal.rpow_one, one_mul]
  rw [hL _ (by decide) (by decide), hL _ (by decide) (by decide), one_mul, one_mul, hc1, hc2,
    ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
  exact Real.exp_lt_exp.2 (by linarith)

end English

namespace Spanish

/-- Spanish puts the noun before the adjective, and STOP closes the utterance. -/
inductive Word
  | vestido | rojo | sombrero | azul | stop
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.vestido⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The Spanish game over the same referents has noun–adjective order and STOP-terminated
utterances. -/
def game : ReferenceGame Word English.Referent :=
  .ofLexicon
    (fun u r ↦ match u, r with
      | .vestido, .redDress | .rojo, .redDress | .sombrero, .blueHat
      | .azul, .blueHat | .stop, _ => true
      | _, _ => false)
    [[.vestido, .stop], [.vestido, .rojo, .stop], [.sombrero, .stop],
      [.sombrero, .azul, .stop]]
    [.redDress, .blueHat]

/-- The §3.1 cost, as in English. -/
def cost (c : ℝ) : Word → ℝ := fun u ↦ if u = .stop then 0 else c

private theorem hw : ∀ r : English.Referent, r ∈ game.worlds := by decide

private theorem forced_vestido (c : ℝ) : game.s1 (cost c) [] .redDress {Word.vestido} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by decide) (by decide)

private theorem forced_stop_after_rojo (c : ℝ) :
    game.s1 (cost c) [.vestido, .rojo] .redDress {Word.stop} = 1 :=
  game.s1_apply_eq_one hw (by decide) (by decide) (by decide)

private theorem step2 (c : ℝ) :
    (game.s1 (cost c) [.vestido] .redDress).real {Word.stop} = 1 / (1 + Real.exp (-c)) ∧
    (game.s1 (cost c) [.vestido] .redDress).real {Word.rojo} =
      Real.exp (-c) / (1 + Real.exp (-c)) := by
  have hs : (game.l0 [.vestido] .stop {English.Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.vestido, Word.stop] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.vestido, Word.stop] r' = 1 from by decide]
  have hr : (game.l0 [.vestido] .rojo {English.Referent.redDress}).toReal = 1 := by
    rw [game.l0_real hw]
    norm_num [show game.trueExts [Word.vestido, Word.rojo] .redDress = 1 from by decide,
      show ∑ r', game.trueExts [Word.vestido, Word.rojo] r' = 1 from by decide]
  have hz : ∀ u' ∈ [Word.vestido, Word.sombrero, Word.azul],
      (game.l0 [.vestido] u' {English.Referent.redDress}).toReal = 0 := by
    intro u' hu'
    fin_cases hu' <;>
      · rw [game.l0_apply_eq_zero hw (by decide), ENNReal.toReal_zero]
  have hcs : Real.exp (-cost c .stop) = 1 := by simp [cost]
  have hcr : Real.exp (-cost c .rojo) = Real.exp (-c) := by simp [cost]
  have hpos : (0 : ℝ) < 1 + Real.exp (-c) := by positivity
  constructor <;>
    · rw [game.s1_real_singleton (by decide)]
      rw [show (Finset.univ : Finset Word) = {.vestido, .rojo, .sombrero, .azul, .stop} from
        by decide]
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton, hs, hr, hz .vestido (by decide), hz .sombrero (by decide),
        hz .azul (by decide), hcs, hcr]
      rw [div_eq_div_iff (by positivity) hpos.ne']
      ring

/-- In Spanish (§3.1), with any length cost the incremental speaker prefers bare *vestido* to
*vestido rojo*, the paper's 0.73 against 0.27 at `c = 1`. -/
theorem incremental_prefers_bare_noun {c : ℝ} (hc : 0 < c) :
    game.s1Utt (cost c) .redDress [.vestido, .rojo, .stop]
      < game.s1Utt (cost c) .redDress [.vestido, .stop] := by
  obtain ⟨hstop, hrojo⟩ := step2 c
  simp only [ReferenceGame.s1Utt, chain_cons, chain_nil, List.nil_append,
    List.cons_append, mul_one]
  rw [measureReal_def (μ := game.s1 (cost c) [] .redDress), forced_vestido,
    measureReal_def (μ := game.s1 (cost c) [.vestido, .rojo] .redDress),
    forced_stop_after_rojo, hstop, hrojo]
  simp only [ENNReal.toReal_one, one_mul, mul_one]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  exact Real.exp_lt_one_iff.2 (by linarith)

end Spanish

/-! ### §3.2: the anticipatory implicature in Sedivy's display

A tall cup, a short cup, a tall pitcher and a key; utterances *tall cup*, *short cup*,
*tall pitcher*, *cup*, *pitcher*, *key*. Upon hearing *tall* the incremental pragmatic
listener favours the tall cup at 3/5 against the tall pitcher at 2/5: a speaker meaning the
pitcher had *pitcher* alone, so *tall* was a third of her choices, while the cup's speaker,
whose bare *cup* is ambiguous with the short cup, uses *tall* half the time. The §3.1 cost
is common to every content word, so it cancels within each row, and the scene is evaluated
at zero cost. The implicature cancels: were the next word *pitcher*,
the listener who has updated on *tall* excludes every referent but the pitcher. -/

namespace Sedivy

/-- The scene's words are the two scalar adjectives and three category nouns. -/
inductive Word
  | tall | short | cup | pitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.tall⟩
instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The four objects on display. -/
inductive Referent
  | tallCup | shortCup | tallPitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.tallCup⟩
instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- Sedivy's display is a reference game with six utterances and word-conjunctive
semantics. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun u r ↦ match u, r with
      | .tall, .tallCup | .tall, .tallPitcher | .short, .shortCup | .cup, .tallCup
      | .cup, .shortCup | .pitcher, .tallPitcher | .key, .key => true
      | _, _ => false)
    [[.tall, .cup], [.short, .cup], [.tall, .pitcher], [.cup], [.pitcher], [.key]]
    [.tallCup, .shortCup, .tallPitcher, .key]

private theorem hw : ∀ r : Referent, r ∈ game.worlds := by decide

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Word → M) :
    ∑ u, f u = f .tall + (f .short + (f .cup + (f .pitcher + f .key))) := by
  rw [show (Finset.univ : Finset Word) = {.tall, .short, .cup, .pitcher, .key} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

theorem s1_tall_values :
    (game.s1 0 [] .tallCup).real {Word.tall} = 1 / 2 ∧
    (game.s1 0 [] .tallPitcher).real {Word.tall} = 1 / 3 ∧
    (game.s1 0 [] .shortCup).real {Word.tall} = 0 ∧
    (game.s1 0 [] .key).real {Word.tall} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [game.s1_real_counts hw (by decide), sum_word]
      norm_num [show game.trueExts [Word.tall] .tallCup = 1 from by decide,
        show game.trueExts [Word.tall] .tallPitcher = 1 from by decide,
        show game.trueExts [Word.tall] .shortCup = 0 from by decide,
        show game.trueExts [Word.tall] .key = 0 from by decide,
        show ∑ r', game.trueExts [Word.tall] r' = 2 from by decide,
        show game.trueExts [Word.short] .tallCup = 0 from by decide,
        show game.trueExts [Word.short] .tallPitcher = 0 from by decide,
        show game.trueExts [Word.cup] .tallCup = 1 from by decide,
        show game.trueExts [Word.cup] .tallPitcher = 0 from by decide,
        show ∑ r', game.trueExts [Word.cup] r' = 2 from by decide,
        show game.trueExts [Word.pitcher] .tallCup = 0 from by decide,
        show game.trueExts [Word.pitcher] .tallPitcher = 1 from by decide,
        show ∑ r', game.trueExts [Word.pitcher] r' = 1 from by decide,
        show game.trueExts [Word.key] .tallCup = 0 from by decide,
        show game.trueExts [Word.key] .tallPitcher = 0 from by decide]

/-- Upon hearing *tall*, the incremental listener favours the tall cup over the tall pitcher,
the anticipatory contrastive inference of §3.2. -/
theorem listener_prefers_tall_cup :
    (game.l1 0 [] .tall).real {Referent.tallPitcher}
      < (game.l1 0 [] .tall).real {Referent.tallCup} := by
  rw [game.l1_real_lt_iff, s1_tall_values.1, s1_tall_values.2.1]
  norm_num

/-- Exactly, the listener puts 3/5 on the tall cup and 2/5 on the pitcher, the paper's 0.6 and
0.4 (§3.2). -/
theorem listener_tall_values :
    (game.l1 0 [] .tall).real {Referent.tallCup} = 3 / 5 ∧
    (game.l1 0 [] .tall).real {Referent.tallPitcher} = 2 / 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := s1_tall_values
  have hsum : ∑ r', (game.s1 0 [] r').real {Word.tall} = 5 / 6 := by
    rw [show (Finset.univ : Finset Referent) = {.tallCup, .shortCup, .tallPitcher, .key}
      from by decide]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton, h1, h2, h3, h4]
    norm_num
  constructor <;>
    · rw [game.l1_real_singleton, hsum]
      first | rw [h1] | rw [h2]
      norm_num

/-- The listener who has heard *tall* and then hears *pitcher* takes the posterior of the
word-level speaker at context *tall* against the updated prior. -/
noncomputable def afterTallPitcher : Measure Referent :=
  RSA.listener (game.l1 0 [] .tall) (game.s1 0 [.tall]) .pitcher

theorem afterTallPitcher_eq_one : afterTallPitcher {Referent.tallPitcher} = 1 := by
  have hcup : game.s1 0 [.tall] .tallCup {Word.pitcher} = 0 :=
    game.s1_apply_eq_zero hw (by decide) 0 (by decide)
  have hpit : game.s1 0 [.tall] .tallPitcher {Word.pitcher} = 1 :=
    game.s1_apply_eq_one hw (by decide) (by decide) (by decide)
  have hprior : ∀ r, r = Referent.shortCup ∨ r = .key → game.l1 0 [] .tall {r} = 0 := by
    rintro r (rfl | rfl) <;>
      exact RSA.listener_apply_singleton_eq_zero
        (game.s1_apply_eq_zero hw (by decide) 0 (by decide))
  have hpos : game.l1 0 [] .tall {Referent.tallPitcher} ≠ 0 :=
    RSA.listener_apply_singleton_ne_zero (uniformOn_univ_singleton_ne_zero _)
      (game.s1_apply_ne_zero hw (by decide) (by decide))
  rw [afterTallPitcher, RSA.listener_apply_singleton_eq_div, Measure.comp_apply_singleton,
    show (Finset.univ : Finset Referent) = {.tallCup, .shortCup, .tallPitcher, .key}
      from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, hcup, hpit, hprior .shortCup (Or.inl rfl),
    hprior .key (Or.inr rfl), mul_zero, zero_mul, zero_mul, mul_one, zero_add, add_zero,
    zero_add]
  exact ENNReal.div_self hpos (measure_ne_top _ _)

end Sedivy

end CohnGordonEtAl2019
