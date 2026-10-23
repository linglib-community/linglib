module

public import Linglib.Logic.Trivalent.Probability
public import Studies.EgreRossiSprenger2026a
public import Studies.Yalcin2007
public import Linglib.Semantics.Dynamic.Update

/-!
# Égré, Rossi and Sprenger (2026): Trivalent Conditionals, Kratzer Style

Égré, Rossi and Sprenger extend the trivalent semantics of indicative conditionals to epistemic
*might* and *must*. A sentence takes a trivalent value at a context and a world; the modals
quantify over the context with the trivalent quantifiers that skip void instances; and the
conditional stays a binary connective while hard-wiring Kratzer's restriction into its truth
conditions: it asserts its consequent at the context updated with its antecedent, and is void
where the world drops out or the update collapses. Acceptance is non-falsity throughout the
context, equivalently probability 1 under every credence mirroring it, and the Restrictor View's
predictions (the covert *must*, the test behaviour of modals, epistemic and if-might
contradictions) come out at the level of acceptance and inference, not truth conditions.

## Main statements

* `Sentence.cond_ofCooper`, `ofFormula_cond`: on nonmodal sentences the conditional is Cooper's,
  so the semantics extends the Cooper valuations of [egre-rossi-sprenger-2026a].
* `Sentence.ContextFree.update_eq_restrict` (Fact 1); `Sentence.update_box_of_accepts`,
  `Sentence.update_dia_of` and their converses (Fact 2), which on a conditional-free prejacent is
  [veltman-1996]'s test (`update_dia_ofSet`).
* `Sentence.cond_box_eq_neg_one` (Fact 3), `Sentence.neg_cond` (Proposition 2),
  `Sentence.ContextFree.update_update` (Proposition 3), `Sentence.ContextFree.cond_cond`
  (Corollary 1), and `import_export_fails` for a modal antecedent, (18) against (19).
* `not_accepts_contra'`, `update_contra'` (Fact 5): through `Agrees`, the semantics is
  [yalcin-2007]'s domain semantics on conditional-free sentences, and Fact 5 is
  `Yalcin2007.not_accepted_contra'`.
* `Mirrors.prob_eq_one_iff`, `accepts_iff_forall_mirrors` (Definition 7); `prob_box_eq_zero_or_one`
  (Fact 4); `accepts_cond_box_iff`, `prob_cond_box_le`, `prob_cond_box_eq_prob_box_cond`
  (Theorem 1); `cEntails_iff_entails` (Theorem 2).
* `schema_K` (Fact 6), `entails_box` (Fact 7), `entails_cond_box` (Corollary 2),
  `accepts_cond_dia_iff` (Fact 8), `entails_dia_conj`, `entails_cond_dia` (Fact 9),
  `eq_empty_of_accepts_neg_dia`, `eq_empty_of_if_might`, `not_entails_of_dia` (Proposition 5),
  `modus_ponens` (Fact 10), `modus_tollens` and its failures (Fact 11), the structural rules and
  failures of Proposition 4, and `entails_insert_iff` (Theorem 3) with the Conditional Proof
  counterexample.
* `cond_ofSet`, `prob_cond_ofSet` (Adams's Thesis, through [egre-rossi-sprenger-2026a]'s
  conditional events), `prob_cond_contra` (footnote 11), `prob_contra'_coin`
  (footnote 12), `die_bare_vs_must` ((20) and (21)).

## Implementation notes

* A sentence denotes its valuation, a function `Set W → W → SignType`, so the semantics is
  compositional by construction (Proposition 1), and a schema proved for all such functions holds
  of the formulas of every model. Definition 3's degenerate clause `⟦A⟧^{s,w} := ⟦A⟧^{{w},w}`
  for `w ∉ s` is stated for every `A`; the modal and conditional clauses evaluate at `Sentence.ctx`
  to build it in. Nonmodal sentences are then context-independent at every world, as the proof of
  Fact 1 asserts (`Sentence.ContextFree`), and conditional-free ones are `Sentence.ofSet`.
* The value `1/2` is `0` in `SignType`, so `⟦A⟧ ≥ 1/2` is `0 ≤ ⟦A⟧`.
* Definition 6 requires only that the credence give the context probability 1, but footnote 8
  and the proofs of Theorems 1 and 2 use a credence positive exactly on the context. `Mirrors` is
  that regular reading; under the literal one the probability half of Theorem 1 fails
  (`not_prob_cond_box_eq_of_literal`).
* Footnote 18 prints its premise as `q ∧ ¬◇p`, which its own model does not accept
  (`not_accepts_fn18_printed`); the main text's `◇¬p` is meant.
* Consequence is stated for a fixed world space, quantifying over its contexts, which is what the
  proofs of Theorems 2 and 3 use; countermodels are concrete world spaces.

## TODO

* The pragmatic acceptance condition for disjunctions in §4.3, under which disjunctions of
  epistemic contradictions are unacceptable.
* The motivating clause (4), which makes (15) false, and the §4.4 discussion of how speakers
  negate conditionals.

## References

* [egre-rossi-sprenger-2026b]
* [egre-rossi-sprenger-2026a]
* [cooper-1968]
* [kratzer-1986]
* [yalcin-2007]
* [yalcin-2012]
* [veltman-1996]
-/

@[expose] public section

namespace EgreRossiSprenger2026b

open SignType Trivalent MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {W : Type*}

/-- A sentence of the conditional–modal language denotes a trivalent value at each context–world
pair. -/
abbrev Sentence (W : Type*) := Set W → W → SignType

namespace Sentence

open Classical in
/-- The context a sentence is evaluated in, `s` itself when the world belongs to it and the
singleton `{w}` otherwise, which is Definition 3's degenerate stipulation read globally. -/
noncomputable def ctx (s : Set W) (w : W) : Set W := if w ∈ s then s else {w}

theorem ctx_of_mem {s : Set W} {w : W} (h : w ∈ s) : ctx s w = s := ite_eq_left h

theorem ctx_of_notMem {s : Set W} {w : W} (h : w ∉ s) : ctx s w = {w} := ite_eq_right h

@[simp] theorem ctx_singleton (w : W) : ctx {w} w = {w} := ctx_of_mem rfl

theorem mem_ctx (s : Set W) (w : W) : w ∈ ctx s w := by
  by_cases h : w ∈ s
  · rwa [ctx_of_mem h]
  · rw [ctx_of_notMem h]; exact rfl

/-- A sentence respects the degenerate stipulation when, outside the context, it is evaluated at
its own singleton. The operators below produce only normalized sentences. -/
def Normalized (φ : Sentence W) : Prop := ∀ s w, w ∉ s → φ s w = φ {w} w

/-- A nonmodal sentence places no condition on the context. -/
def ContextFree (φ : Sentence W) : Prop := ∀ s s' w, φ s w = φ s' w

theorem ContextFree.normalized {φ : Sentence W} (h : ContextFree φ) : Normalized φ :=
  fun s w _ ↦ h s {w} w

open Classical in
/-- The `L`-sentence expressing the classical proposition `p`. -/
noncomputable def ofSet (p : Set W) : Sentence W := fun _ w ↦ ofProp (w ∈ p)

open Classical in
@[simp] theorem ofSet_apply (p : Set W) (s : Set W) (w : W) :
    ofSet p s w = ofProp (w ∈ p) := rfl

theorem contextFree_ofSet (p : Set W) : ContextFree (ofSet p) := fun _ _ _ ↦ rfl

@[simp] theorem neg_apply (φ : Sentence W) (s : Set W) (w : W) : (-φ) s w = -φ s w := rfl

theorem neg_ofSet (p : Set W) : -ofSet p = ofSet pᶜ := by
  funext s w
  by_cases h : w ∈ p <;> simp [ofSet, h]

/-- Cooper conjunction, pointwise. -/
def conj (φ ψ : Sentence W) : Sentence W := fun s w ↦ meetBelnap (φ s w) (ψ s w)

/-- Cooper disjunction, pointwise. -/
def disj (φ ψ : Sentence W) : Sentence W := fun s w ↦ joinBelnap (φ s w) (ψ s w)

@[simp] theorem conj_apply (φ ψ : Sentence W) (s : Set W) (w : W) :
    conj φ ψ s w = meetBelnap (φ s w) (ψ s w) := rfl

@[simp] theorem disj_apply (φ ψ : Sentence W) (s : Set W) (w : W) :
    disj φ ψ s w = joinBelnap (φ s w) (ψ s w) := rfl

theorem ContextFree.neg {φ : Sentence W} (h : ContextFree φ) : ContextFree (-φ) :=
  fun s s' w ↦ by simp [h s s' w]

theorem ContextFree.conj {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ) :
    ContextFree (conj φ ψ) := fun s s' w ↦ by simp [hφ s s' w, hψ s s' w]

theorem ContextFree.disj {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ) :
    ContextFree (disj φ ψ) := fun s s' w ↦ by simp [hφ s s' w, hψ s s' w]

/-! ### Restriction and update (Definition 2) -/

/-- The restriction `s/A` keeps the worlds of `s` where `A` is not false. -/
def restrict (s : Set W) (φ : Sentence W) : Set W := {w ∈ s | 0 ≤ φ s w}

@[simp] theorem mem_restrict {s : Set W} {φ : Sentence W} {w : W} :
    w ∈ restrict s φ ↔ w ∈ s ∧ 0 ≤ φ s w := Iff.rfl

theorem restrict_subset (s : Set W) (φ : Sentence W) : restrict s φ ⊆ s := fun _ h ↦ h.1

open Classical in
/-- The update `s[A]` is the restriction if the restriction still accepts `A`, and the collapsed
context `∅` if the update would be self-defeating. -/
noncomputable def update (s : Set W) (φ : Sentence W) : Set W :=
  if ∀ w ∈ restrict s φ, 0 ≤ φ (restrict s φ) w then restrict s φ else ∅

theorem update_eq_restrict {s : Set W} {φ : Sentence W}
    (h : ∀ w ∈ restrict s φ, 0 ≤ φ (restrict s φ) w) : update s φ = restrict s φ :=
  ite_eq_left h

theorem update_eq_empty {s : Set W} {φ : Sentence W}
    (h : ¬ ∀ w ∈ restrict s φ, 0 ≤ φ (restrict s φ) w) : update s φ = ∅ :=
  ite_eq_right h

theorem update_subset (s : Set W) (φ : Sentence W) : update s φ ⊆ s := by
  rw [update]
  split_ifs
  · exact restrict_subset s φ
  · exact Set.empty_subset s

theorem update_subset_restrict (s : Set W) (φ : Sentence W) : update s φ ⊆ restrict s φ := by
  rw [update]
  split_ifs
  · exact subset_rfl
  · exact Set.empty_subset _

theorem mem_update_iff {s : Set W} {φ : Sentence W} {w : W} :
    w ∈ update s φ ↔ w ∈ restrict s φ ∧ ∀ w' ∈ restrict s φ, 0 ≤ φ (restrict s φ) w' := by
  rw [update]
  split_ifs with h
  · exact (and_iff_left h).symm
  · exact iff_of_false (Set.notMem_empty w) fun hc ↦ h hc.2

/-- Restriction and update agree on nonmodal sentences, whose evaluation does not move with the
context (**Fact 1**). -/
theorem ContextFree.update_eq_restrict {φ : Sentence W} (h : ContextFree φ) (s : Set W) :
    update s φ = restrict s φ :=
  Sentence.update_eq_restrict fun w hw ↦ h (restrict s φ) s w ▸ hw.2

@[simp] theorem update_ofSet (s : Set W) (p : Set W) : update s (ofSet p) = s ∩ p := by
  rw [(contextFree_ofSet p).update_eq_restrict]
  ext w
  simp

/-! ### The modals (Definition 3)

`□` and `◇` generalize Cooper conjunction and disjunction over the worlds of the context: false
when some instance is false, void when every instance is void, true otherwise — Haug's trivalent
quantifiers over the context, in the form [belnap-1970] gave restricted quantification. -/

/-- Epistemic *must* is Haug's universal quantifier over the context. -/
noncomputable def box (φ : Sentence W) : Sentence W := fun s w ↦
  forallHaug ((ctx s w).indicator fun w' ↦ φ (ctx s w) w')

/-- Epistemic *might* is Haug's existential quantifier over the context. -/
noncomputable def dia (φ : Sentence W) : Sentence W := fun s w ↦
  existsHaug ((ctx s w).indicator fun w' ↦ φ (ctx s w) w')

theorem box_normalized (φ : Sentence W) : Normalized (box φ) := fun s w h ↦ by
  rw [box, box, ctx_of_notMem h, ctx_singleton]

theorem dia_normalized (φ : Sentence W) : Normalized (dia φ) := fun s w h ↦ by
  rw [dia, dia, ctx_of_notMem h, ctx_singleton]

section ModalValues

variable {φ : Sentence W} {s : Set W} {w : W}

theorem box_apply_of_mem (h : w ∈ s) :
    box φ s w = forallHaug (s.indicator fun w' ↦ φ s w') := by
  rw [box, ctx_of_mem h]

theorem dia_apply_of_mem (h : w ∈ s) :
    dia φ s w = existsHaug (s.indicator fun w' ↦ φ s w') := by
  rw [dia, ctx_of_mem h]

theorem box_eq_neg_one_iff (h : w ∈ s) : box φ s w = -1 ↔ ∃ w' ∈ s, φ s w' = -1 := by
  rw [box_apply_of_mem h, forallHaug_eq_neg_one_iff]
  exact exists_congr fun w' ↦ by
    by_cases hw' : w' ∈ s <;> simp [hw']

theorem box_eq_zero_iff (h : w ∈ s) : box φ s w = 0 ↔ ∀ w' ∈ s, φ s w' = 0 := by
  rw [box_apply_of_mem h, forallHaug_eq_zero_iff]
  constructor
  · exact fun hall w' hw' ↦ by simpa [hw'] using hall w'
  · intro hall w'
    by_cases hw' : w' ∈ s <;> simp [hw', hall]

theorem dia_eq_one_iff (h : w ∈ s) : dia φ s w = 1 ↔ ∃ w' ∈ s, φ s w' = 1 := by
  rw [dia_apply_of_mem h, existsHaug_eq_one_iff]
  exact exists_congr fun w' ↦ by
    by_cases hw' : w' ∈ s <;> simp [hw']

theorem dia_eq_zero_iff (h : w ∈ s) : dia φ s w = 0 ↔ ∀ w' ∈ s, φ s w' = 0 := by
  rw [dia_apply_of_mem h, existsHaug_eq_zero_iff]
  constructor
  · exact fun hall w' hw' ↦ by simpa [hw'] using hall w'
  · intro hall w'
    by_cases hw' : w' ∈ s <;> simp [hw', hall]

theorem box_apply_congr {w' : W} (h : w ∈ s) (h' : w' ∈ s) : box φ s w = box φ s w' := by
  rw [box_apply_of_mem h, box_apply_of_mem h']

theorem dia_apply_congr {w' : W} (h : w ∈ s) (h' : w' ∈ s) : dia φ s w = dia φ s w' := by
  rw [dia_apply_of_mem h, dia_apply_of_mem h']

theorem dia_eq_neg_box_neg (φ : Sentence W) : dia φ = -box (-φ) := by
  funext s w
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · simp only [dia, box, neg_apply, SignType.neg_eq_zero_iff, existsHaug_eq_zero_iff,
      forallHaug_eq_zero_iff]
    exact forall_congr' fun w' ↦ by by_cases h : w' ∈ ctx s w <;> simp [h]
  · simp only [dia, box, neg_apply, SignType.neg_eq_one_iff, existsHaug_eq_one_iff,
      forallHaug_eq_neg_one_iff]
    exact exists_congr fun w' ↦ by by_cases h : w' ∈ ctx s w <;> simp [h]

theorem box_eq_neg_dia_neg (φ : Sentence W) : box φ = -dia (-φ) := by
  rw [dia_eq_neg_box_neg, neg_neg, neg_neg]

end ModalValues

/-! ### The conditional (Definition 3)

`A → B` asserts `B` at the context updated with `A`, and is void where the world of evaluation
drops out of the update or the update collapses. -/

open Classical in
/-- The trivalent, Kratzer-style conditional. -/
noncomputable def cond (φ ψ : Sentence W) : Sentence W := fun s w ↦
  if w ∈ update (ctx s w) φ then ψ (update (ctx s w) φ) w else 0

theorem cond_apply_of_mem {φ ψ : Sentence W} {s : Set W} {w : W} (hw : w ∈ s)
    (h : w ∈ update s φ) : cond φ ψ s w = ψ (update s φ) w := by
  rw [cond, ctx_of_mem hw]
  exact ite_eq_left h

theorem cond_apply_of_notMem {φ ψ : Sentence W} {s : Set W} {w : W} (hw : w ∈ s)
    (h : w ∉ update s φ) : cond φ ψ s w = 0 := by
  rw [cond, ctx_of_mem hw]
  exact ite_eq_right h

theorem cond_normalized (φ ψ : Sentence W) : Normalized (cond φ ψ) := fun s w h ↦ by
  rw [cond, cond, ctx_of_notMem h, ctx_singleton]

/-- Negation commutes with the conditional at every context–world pair (**Proposition 2**). -/
theorem neg_cond (φ ψ : Sentence W) : -cond φ ψ = cond φ (-ψ) := by
  funext s w
  rw [neg_apply, cond, cond]
  split_ifs <;> simp

/-- Where `A → B` is false, so is `A → □B` (**Fact 3**), so the bare conditional has the less
demanding non-falsity condition. -/
theorem cond_box_eq_neg_one {φ ψ : Sentence W} {s : Set W} {w : W}
    (h : cond φ ψ s w = -1) : cond φ (box ψ) s w = -1 := by
  rw [cond] at h ⊢
  split_ifs at h ⊢ with hw
  exact (box_eq_neg_one_iff hw).2 ⟨w, hw, h⟩

/-! ### Acceptance and the test behaviour of modals -/

/-- A context accepts a sentence when the sentence is not false at any of its worlds, evaluated
at the context itself (Definition 7). -/
def Accepts (s : Set W) (φ : Sentence W) : Prop := ∀ w ∈ s, 0 ≤ φ s w

section Accepts

variable {φ ψ : Sentence W} {s : Set W}

@[simp] theorem accepts_empty (φ : Sentence W) : Accepts ∅ φ := fun _ h ↦ absurd h (by simp)

theorem accepts_update (s : Set W) (φ : Sentence W) : Accepts (update s φ) φ := by
  rw [update]
  split_ifs with h
  · exact h
  · exact accepts_empty φ

theorem update_eq_self_of_accepts (h : Accepts s φ) : update s φ = s := by
  have hr : restrict s φ = s := Set.sep_eq_self_iff_mem_true.2 h
  rw [update_eq_restrict (by rw [hr]; exact h), hr]

theorem update_eq_empty_of_uniform (hu : ∀ w ∈ s, ∀ w' ∈ s, φ s w = φ s w')
    (h : ¬ Accepts s φ) : update s φ = ∅ := by
  obtain ⟨w₀, hw₀, hneg⟩ : ∃ w₀ ∈ s, ¬ 0 ≤ φ s w₀ := by simpa [Accepts] using h
  refine Set.subset_eq_empty (update_subset_restrict s φ) (Set.eq_empty_of_forall_notMem ?_)
  rintro w ⟨hw, hle⟩
  exact hneg (hu w hw w₀ hw₀ ▸ hle)

theorem update_eq_empty_of_forall_not_accepts (h : ∀ t : Set W, t.Nonempty → ¬ Accepts t φ)
    (s : Set W) : update s φ = ∅ :=
  Set.not_nonempty_iff_eq_empty.1 fun hne ↦ h _ hne (accepts_update s φ)

/-- A context accepts `□A` exactly when it accepts `A`, which gives Łukasiewicz's Principle and
Strong *must* (**Fact 7**). -/
theorem accepts_box_iff : Accepts s (box φ) ↔ Accepts s φ := by
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · rw [SignType.nonneg_iff_ne_neg_one]
    exact fun hc ↦ SignType.nonneg_iff_ne_neg_one.1 (h w hw) ((box_eq_neg_one_iff hw).2 ⟨w, hw, hc⟩)
  · rw [SignType.nonneg_iff_ne_neg_one]
    intro hc
    obtain ⟨w', hw', h'⟩ := (box_eq_neg_one_iff hw).1 hc
    exact SignType.nonneg_iff_ne_neg_one.1 (h w' hw') h'

theorem accepts_dia_iff : Accepts s (dia φ) ↔ (∃ w ∈ s, φ s w = 1) ∨ ∀ w ∈ s, φ s w = 0 := by
  constructor
  · intro h
    by_cases hs : s.Nonempty
    · obtain ⟨w, hw⟩ := hs
      have hle := h w hw
      cases hv : dia φ s w with
      | zero => exact .inr ((dia_eq_zero_iff hw).1 hv)
      | neg => rw [hv] at hle; exact absurd hle (by decide)
      | pos => exact .inl ((dia_eq_one_iff hw).1 hv)
    · exact .inr fun w hw ↦ absurd ⟨w, hw⟩ hs
  · rintro (h | h) w hw
    · rw [(dia_eq_one_iff hw).2 h]; decide
    · rw [(dia_eq_zero_iff hw).2 h]

/-- The update on `□A` keeps the context if it accepts `A` (**Fact 2** for *must*)... -/
theorem update_box_of_accepts (h : Accepts s φ) : update s (box φ) = s :=
  update_eq_self_of_accepts (accepts_box_iff.2 h)

theorem update_box_of_not_accepts (h : ¬ Accepts s φ) : update s (box φ) = ∅ :=
  update_eq_empty_of_uniform (fun _ hw _ hw' ↦ box_apply_congr hw hw') (mt accepts_box_iff.1 h)

/-- The update on `◇A` keeps the context if `A` is true somewhere in it or void throughout it
(**Fact 2** for *might*)... -/
theorem update_dia_of (h : (∃ w ∈ s, φ s w = 1) ∨ ∀ w ∈ s, φ s w = 0) : update s (dia φ) = s :=
  update_eq_self_of_accepts (accepts_dia_iff.2 h)

theorem update_dia_of_not (h : ¬ ((∃ w ∈ s, φ s w = 1) ∨ ∀ w ∈ s, φ s w = 0)) :
    update s (dia φ) = ∅ :=
  update_eq_empty_of_uniform (fun _ hw _ hw' ↦ dia_apply_congr hw hw') (mt accepts_dia_iff.1 h)

theorem accepts_cond_iff : Accepts s (cond φ ψ) ↔ Accepts (update s φ) ψ := by
  constructor
  · intro h w hw
    have := h w (update_subset s φ hw)
    rwa [cond_apply_of_mem (update_subset s φ hw) hw] at this
  · intro h w hw
    by_cases hu : w ∈ update s φ
    · rw [cond_apply_of_mem hw hu]; exact h w hu
    · rw [cond_apply_of_notMem hw hu]

end Accepts

/-! ### Nonmodal sentences and Cooper's conditional -/

/-- The nonmodal sentence with Cooper value `p` at each world, whatever the context. -/
def ofCooper (p : W → SignType) : Sentence W := fun _ ↦ p

@[simp] theorem ofCooper_apply (p : W → SignType) (s : Set W) (w : W) : ofCooper p s w = p w :=
  rfl

theorem contextFree_ofCooper (p : W → SignType) : ContextFree (ofCooper p) := fun _ _ _ ↦ rfl

theorem ContextFree.eq_ofCooper {φ : Sentence W} (h : ContextFree φ) :
    φ = ofCooper fun w ↦ φ ∅ w :=
  funext fun s ↦ funext fun w ↦ h s ∅ w

/-- On nonmodal sentences the conditional is Cooper's connective at every world, inside the
context or outside it, the reduction (i) of §3.5. -/
theorem cond_ofCooper (p q : W → SignType) :
    cond (ofCooper p) (ofCooper q) = ofCooper fun w ↦ condAssert .lp (p w) (q w) := by
  funext s w
  have hu : update (ctx s w) (ofCooper p) = {v ∈ ctx s w | 0 ≤ p v} :=
    (contextFree_ofCooper p).update_eq_restrict _
  by_cases h : 0 ≤ p w
  · rw [cond, ite_eq_left (by rw [hu]; exact ⟨mem_ctx s w, h⟩), ofCooper_apply, ofCooper_apply,
      condAssert_of_le h]
  · rw [cond, ite_eq_right (by rw [hu]; exact fun hc ↦ h hc.2), ofCooper_apply,
      condAssert_of_not_le h]

theorem ContextFree.cond {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ) :
    ContextFree (cond φ ψ) := by
  rw [hφ.eq_ofCooper, hψ.eq_ofCooper, cond_ofCooper]
  exact contextFree_ofCooper _

/-- Updating on nonmodal sentences in turn is updating on their conjunction (**Update
Commutativity**, Proposition 3). -/
theorem ContextFree.update_update {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ)
    (s : Set W) : update (update s φ) ψ = update s (Sentence.conj φ ψ) := by
  rw [hψ.update_eq_restrict, hφ.update_eq_restrict, (hφ.conj hψ).update_eq_restrict]
  ext w
  simp only [mem_restrict, conj_apply, zero_le_meetBelnap_iff, hψ (restrict s φ) s w, and_assoc]

theorem ContextFree.update_comm {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ)
    (s : Set W) : update (update s φ) ψ = update (update s ψ) φ := by
  rw [hφ.update_update hψ, hψ.update_update hφ]
  congr 1
  funext t w
  exact meetBelnap_comm _ _

/-- **Corollary 1**, Import-Export for nonmodal antecedents, whatever the consequent. -/
theorem ContextFree.cond_cond {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : ContextFree ψ)
    (χ : Sentence W) :
    Sentence.cond φ (Sentence.cond ψ χ) = Sentence.cond (Sentence.conj φ ψ) χ := by
  funext s w
  by_cases hu : w ∈ update (ctx s w) φ
  · rw [Sentence.cond, ite_eq_left hu, Sentence.cond, ctx_of_mem hu, hφ.update_update hψ]
    rfl
  · rw [Sentence.cond, ite_eq_right hu, Sentence.cond, ite_eq_right]
    intro h
    rw [← hφ.update_update hψ] at h
    exact hu (update_subset _ ψ h)

end Sentence

/-! ### Consequence (Definition 9)

TT-consequence preserves acceptance across every context of the world space; with the meanings
fixed, a schema valid for all meanings holds in particular for those the paper's formulas take in
any model. -/

section Consequence

open Sentence

variable {φ ψ χ : Sentence W} {s : Set W} {Γ Δ Θ : Set (Sentence W)}

/-- TT-consequence: every context accepting the premises accepts the conclusion. -/
def Entails (Γ : Set (Sentence W)) (ψ : Sentence W) : Prop :=
  ∀ s, (∀ φ ∈ Γ, Accepts s φ) → Accepts s ψ

theorem Sentence.Accepts.of_cond (h₁ : Accepts s (cond φ ψ)) (h₂ : Accepts s φ) :
    Accepts s ψ := by
  rwa [accepts_cond_iff, update_eq_self_of_accepts h₂] at h₁

/-- **Fact 10**, Modus Ponens, for arbitrary sentences. -/
theorem modus_ponens (φ ψ : Sentence W) : Entails {cond φ ψ, φ} ψ := fun _ h ↦
  (h _ (Set.mem_insert _ _)).of_cond (h _ (Set.mem_insert_of_mem _ rfl))

/-- A context accepts `A → B` exactly when it accepts `A → □B` (**Theorem 1**, acceptance
half)... -/
theorem accepts_cond_box_iff : Accepts s (cond φ (box ψ)) ↔ Accepts s (cond φ ψ) := by
  rw [accepts_cond_iff, accepts_cond_iff, accepts_box_iff]

theorem accepts_box_cond_iff : Accepts s (box (cond φ ψ)) ↔ Accepts s (cond φ ψ) :=
  accepts_box_iff

/-- `A → B` and `A → □B` entail each other, the covert epistemic *must* (**Corollary 2**). -/
theorem entails_cond_box (φ ψ : Sentence W) :
    Entails {cond φ ψ} (cond φ (box ψ)) ∧ Entails {cond φ (box ψ)} (cond φ ψ) :=
  ⟨fun _ h ↦ accepts_cond_box_iff.2 (h _ rfl), fun _ h ↦ accepts_cond_box_iff.1 (h _ rfl)⟩

/-- `A` and `□A` entail each other, Łukasiewicz's Principle and Strong *must* (**Fact 7**). -/
theorem entails_box (φ : Sentence W) : Entails {φ} (box φ) ∧ Entails {box φ} φ :=
  ⟨fun _ h ↦ accepts_box_iff.2 (h _ rfl), fun _ h ↦ accepts_box_iff.1 (h _ rfl)⟩

/-- Every context accepts `□(A → B) → (□A → □B)` (**Schema K**, Fact 6). -/
theorem schema_K (φ ψ : Sentence W) (s : Set W) :
    Accepts s (cond (box (cond φ ψ)) (cond (box φ) (box ψ))) := by
  rw [accepts_cond_iff]
  by_cases h₁ : Accepts s (cond φ ψ)
  · rw [update_box_of_accepts h₁, accepts_cond_iff]
    by_cases h₂ : Accepts s φ
    · rw [update_box_of_accepts h₂, accepts_box_iff]
      exact h₁.of_cond h₂
    · rw [update_box_of_not_accepts h₂]
      exact accepts_empty _
  · rw [update_box_of_not_accepts h₁]
    exact accepts_empty _

/-- *Might* commutes with the conditional at the level of acceptance (**Fact 8**). -/
theorem accepts_cond_dia_iff : Accepts s (cond φ (dia ψ)) ↔ Accepts s (dia (cond φ ψ)) := by
  rw [accepts_cond_iff, accepts_dia_iff, accepts_dia_iff]
  refine or_congr ⟨fun ⟨w, hw, h⟩ ↦ ⟨w, update_subset s φ hw, ?_⟩, fun ⟨w, hw, h⟩ ↦ ?_⟩
    ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · rw [cond_apply_of_mem (update_subset s φ hw) hw, h]
  · by_cases hu : w ∈ update s φ
    · exact ⟨w, hu, by rwa [cond_apply_of_mem hw hu] at h⟩
    · rw [cond_apply_of_notMem hw hu] at h
      exact absurd h (by decide)
  · by_cases hu : w ∈ update s φ
    · rw [cond_apply_of_mem hw hu]
      exact h w hu
    · rw [cond_apply_of_notMem hw hu]
  · have := h w (update_subset s φ hw)
    rwa [cond_apply_of_mem (update_subset s φ hw) hw] at this

/-- **Fact 8**, the *must* half, is Theorem 1. -/
theorem accepts_cond_box_iff_box_cond :
    Accepts s (cond φ (box ψ)) ↔ Accepts s (box (cond φ ψ)) :=
  accepts_cond_box_iff.trans accepts_box_cond_iff.symm

/-! #### Structural properties (Proposition 4) -/

theorem entails_refl (φ : Sentence W) : Entails {φ} φ := fun _ h ↦ h _ rfl

theorem Entails.mono (h : Entails Γ ψ) (hΓΔ : Γ ⊆ Δ) : Entails Δ ψ :=
  fun s hs ↦ h s fun φ hφ ↦ hs φ (hΓΔ hφ)

theorem Entails.trans (hΘ : ∀ φ ∈ Θ, Entails Γ φ) (h : Entails (Θ ∪ Δ) ψ) :
    Entails (Γ ∪ Δ) ψ := fun s hs ↦
  h s fun φ hφ ↦ hφ.elim (fun hφ ↦ hΘ φ hφ s fun χ hχ ↦ hs χ (.inl hχ)) (fun hφ ↦ hs φ (.inr hφ))

/-- For nonmodal premises the Deduction Theorem holds (**Theorem 3**), because their acceptance
survives the update on the hypothesis. -/
theorem entails_insert_iff (hΓ : ∀ χ ∈ Γ, ContextFree χ) :
    Entails (insert φ Γ) ψ ↔ Entails Γ (cond φ ψ) := by
  constructor
  · intro h s hs
    rw [accepts_cond_iff]
    refine h _ fun χ hχ ↦ ?_
    rcases hχ with rfl | hχ
    · exact accepts_update s χ
    · exact fun w hw ↦ hΓ χ hχ (update s φ) s w ▸ hs χ hχ w (update_subset s φ hw)
  · intro h s hs
    exact (h s fun χ hχ ↦ hs χ (Set.mem_insert_of_mem _ hχ)).of_cond (hs φ (Set.mem_insert _ _))

end Consequence

/-! ### Domain semantics on the conditional-free fragment

On sentences without conditionals, the valuations of Definition 3 are [yalcin-2007]'s domain
semantics, equation (1): a trivalent sentence agrees with a domain-semantic one when it is
two-valued at every world of every context and true exactly where the other is. The Boolean
connectives and the modals preserve agreement, so the paper's verdicts on epistemic
contradictions are Yalcin's theorems (Fact 5). -/

section DomainSemantics

open Sentence Classical

/-- `φ` agrees with the domain-semantic sentence `ψ` at every world of every context. -/
def Agrees (φ : Sentence W) (ψ : Yalcin2007.Sentence W) : Prop :=
  ∀ s, ∀ w ∈ s, φ s w = ofProp (ψ s w)

variable {φ φ' : Sentence W} {ψ ψ' : Yalcin2007.Sentence W}

theorem agrees_ofSet (p : Set W) : Agrees (ofSet p) (Yalcin2007.Sentence.ofProp p) :=
  fun _ _ _ ↦ rfl

theorem Agrees.neg (h : Agrees φ ψ) : Agrees (-φ) ψᶜ := fun s w hw ↦ by
  rw [neg_apply, h s w hw, ← ofProp_not]
  exact ofProp_congr Iff.rfl

theorem Agrees.conj (h : Agrees φ ψ) (h' : Agrees φ' ψ') : Agrees (conj φ φ') (ψ ⊓ ψ') :=
  fun s w hw ↦ by
    rw [conj_apply, h s w hw, h' s w hw,
      meetBelnap_eq_inf_of_ne_zero ofProp_ne_zero ofProp_ne_zero, ← ofProp_and]
    exact ofProp_congr Iff.rfl

theorem Agrees.dia (h : Agrees φ ψ) : Agrees (dia φ) ψ.might := fun s w hw ↦ by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [dia_eq_zero_iff hw]
    exact iff_of_false (fun hall ↦ ofProp_ne_zero ((h s w hw).symm.trans (hall w hw)))
      ofProp_ne_zero
  · rw [dia_eq_one_iff hw, ofProp_eq_one_iff]
    show _ ↔ ∃ w' ∈ s, ψ s w'
    refine exists_congr fun w' ↦ and_congr_right fun hw' ↦ ?_
    rw [h s w' hw', ofProp_eq_one_iff]

theorem Agrees.box (h : Agrees φ ψ) : Agrees (box φ) ψ.must := by
  rw [box_eq_neg_dia_neg, Yalcin2007.Sentence.must_eq_compl_might_compl]
  exact h.neg.dia.neg

theorem Agrees.accepts_iff (h : Agrees φ ψ) {s : Set W} : Accepts s φ ↔ ψ.AcceptedIn s :=
  forall₂_congr fun w hw ↦ by rw [h s w hw, zero_le_ofProp_iff]

/-- No nonempty context accepts the epistemic contradiction `q ∧ ◇¬q` (**Fact 5**), which on the
conditional-free fragment is `Yalcin2007.not_accepted_contra'`... -/
theorem not_accepts_contra' {s : Set W} (hs : s.Nonempty) (q : Set W) :
    ¬ Accepts s (conj (ofSet q) (dia (-ofSet q))) := by
  rw [((agrees_ofSet q).conj (agrees_ofSet q).neg.dia).accepts_iff]
  exact Yalcin2007.not_accepted_contra' hs

theorem update_contra' (s q : Set W) : update s (conj (ofSet q) (dia (-ofSet q))) = ∅ :=
  update_eq_empty_of_forall_not_accepts (fun _ ht ↦ not_accepts_contra' ht q) s

theorem not_accepts_contra {s : Set W} (hs : s.Nonempty) (p : Set W) :
    ¬ Accepts s (conj (-ofSet p) (dia (ofSet p))) := by
  rw [((agrees_ofSet p).neg.conj (agrees_ofSet p).dia).accepts_iff]
  exact Yalcin2007.not_accepted_contra hs

/-- ... and so is its mirror image `◇p ∧ ¬p`, the antecedent of (19). -/
theorem not_accepts_dia_conj_neg {s : Set W} (hs : s.Nonempty) (p : Set W) :
    ¬ Accepts s (conj (dia (ofSet p)) (-ofSet p)) := by
  rw [((agrees_ofSet p).dia.conj (agrees_ofSet p).neg).accepts_iff, inf_comm]
  exact Yalcin2007.not_accepted_contra hs

/-- **Import-Export fails for a modal antecedent**, (18) against (19): where `p` is possible the
update on `◇p` is idle, so `◇p → (¬p → q)` is `¬p → q` and true at a `¬p`-world where `q` holds,
while the update on `◇p ∧ ¬p` collapses and `(◇p ∧ ¬p) → q` is void. -/
theorem import_export_fails :
    cond (dia (ofSet {true})) (cond (-ofSet {true}) (ofSet Set.univ)) Set.univ false = 1 ∧
      cond (conj (dia (ofSet {true})) (-ofSet {true})) (ofSet Set.univ) Set.univ false = 0 := by
  have hdia : update Set.univ (dia (ofSet ({true} : Set Bool))) = Set.univ :=
    update_dia_of (.inl ⟨true, trivial, by simp⟩)
  have hneg : update Set.univ (-ofSet ({true} : Set Bool)) = {false} := by
    rw [neg_ofSet, update_ofSet]
    ext w
    cases w <;> simp
  refine ⟨?_, ?_⟩
  · rw [cond_apply_of_mem (Set.mem_univ _) (by rw [hdia]; exact Set.mem_univ _), hdia,
      cond_apply_of_mem (Set.mem_univ _) (by rw [hneg]; exact Set.mem_singleton _), hneg]
    simp
  · refine cond_apply_of_notMem (Set.mem_univ _) ?_
    rw [update_eq_empty_of_forall_not_accepts fun _ ht ↦ not_accepts_dia_conj_neg ht _]
    exact Set.notMem_empty _

end DomainSemantics

/-! ### Inference with conditionals and modals (§5) -/

section Inference

open Sentence Classical

variable {s : Set W}

theorem accepts_ofSet_iff {p : Set W} : Accepts s (ofSet p) ↔ s ⊆ p :=
  ⟨fun h _ hw ↦ zero_le_ofProp_iff.1 (h _ hw), fun h _ hw ↦ zero_le_ofProp_iff.2 (h hw)⟩

theorem accepts_cond_ofSet_iff {p : Set W} {φ : Sentence W} :
    Accepts s (cond (ofSet p) φ) ↔ Accepts (s ∩ p) φ := by
  rw [accepts_cond_iff, update_ofSet]

theorem conj_ofSet (p q : Set W) : conj (ofSet p) (ofSet q) = ofSet (p ∩ q) := by
  funext s w
  by_cases hp : w ∈ p <;> by_cases hq : w ∈ q <;> simp [ofSet, hp, hq]

theorem disj_ofSet (p q : Set W) : disj (ofSet p) (ofSet q) = ofSet (p ∪ q) := by
  funext s w
  by_cases hp : w ∈ p <;> by_cases hq : w ∈ q <;> simp [ofSet, hp, hq]

theorem accepts_dia_ofSet_iff {p : Set W} :
    Accepts s (dia (ofSet p)) ↔ (s.Nonempty → (s ∩ p).Nonempty) := by
  rw [(agrees_ofSet p).dia.accepts_iff]
  exact ⟨fun h ⟨w, hw⟩ ↦ h w hw, fun h w hw ↦ h ⟨w, hw⟩⟩

theorem cond_ofSet_empty (φ : Sentence W) : cond (ofSet ∅) φ = 0 := by
  funext s w
  rw [Sentence.cond, ite_eq_right (by simp)]
  rfl

theorem accepts_zero (s : Set W) : Accepts s 0 := fun _ _ ↦ le_rfl

/-- **Fact 2** on a conditional-free prejacent is [veltman-1996]'s *might*: the update on `◇p`
tests whether `p` is open in the context. -/
theorem update_dia_ofSet (s p : Set W) :
    update s (dia (ofSet p)) = DynamicSemantics.CCP.might (DynamicSemantics.CCP.up p) s := by
  by_cases h : (s ∩ p).Nonempty
  · rw [update_eq_self_of_accepts (accepts_dia_ofSet_iff.2 fun _ ↦ h)]
    exact (DynamicSemantics.CCP.guard_pos (C := fun s ↦ (DynamicSemantics.CCP.up p s).Nonempty)
      h).symm
  · rw [DynamicSemantics.CCP.might,
      DynamicSemantics.CCP.guard_neg (C := fun s ↦ (DynamicSemantics.CCP.up p s).Nonempty) h]
    by_cases hs : s.Nonempty
    · exact update_eq_empty_of_uniform (fun _ hw _ hw' ↦ dia_apply_congr hw hw')
        fun hacc ↦ h (accepts_dia_ofSet_iff.1 hacc hs)
    · exact Set.subset_eq_empty (update_subset s _) (Set.not_nonempty_iff_eq_empty.1 hs)

/-- For conditional-free `A` and `B`, `◇A, A → ◇B ⊨ ◇(A ∧ B)` (**Fact 9**)... -/
theorem entails_dia_conj (a b : Set W) :
    Entails {dia (ofSet a), cond (ofSet a) (dia (ofSet b))} (dia (conj (ofSet a) (ofSet b))) := by
  intro s h
  have h₁ := accepts_dia_ofSet_iff.1 (h _ (Set.mem_insert _ _))
  have h₂ :=
    accepts_dia_ofSet_iff.1 (accepts_cond_ofSet_iff.1 (h _ (Set.mem_insert_of_mem _ rfl)))
  rw [conj_ofSet, accepts_dia_ofSet_iff, ← Set.inter_assoc]
  exact fun hs ↦ h₂ (h₁ hs)

theorem entails_cond_dia (a b : Set W) :
    Entails {dia (conj (ofSet a) (ofSet b))} (cond (ofSet a) (dia (ofSet b))) := by
  intro s h
  have h₁ := h _ rfl
  rw [conj_ofSet, accepts_dia_ofSet_iff, ← Set.inter_assoc] at h₁
  rw [accepts_cond_ofSet_iff, accepts_dia_ofSet_iff]
  exact fun hsa ↦ h₁ (hsa.mono Set.inter_subset_left)

/-- Without the premise `◇A` the first entailment fails. *If my team wins out, they might win it
all* (27) does not entail *it might turn out that my team wins out and wins it all* (26), since
a context excluding `A` accepts the conditional vacuously. -/
theorem not_entails_dia_conj :
    ¬ Entails {cond (ofSet (∅ : Set Unit)) (dia (ofSet Set.univ))}
      (dia (conj (ofSet ∅) (ofSet Set.univ))) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, cond_ofSet_empty]
    exact accepts_zero _
  rw [conj_ofSet, accepts_dia_ofSet_iff] at this
  simpa using this Set.univ_nonempty

/-- A sentence never void at a world of its context, as every conditional-free sentence is. -/
def NeverVoid (φ : Sentence W) : Prop := ∀ s, ∀ w ∈ s, φ s w ≠ 0

theorem neverVoid_ofSet (p : Set W) : NeverVoid (ofSet p) := fun _ _ _ ↦ ofProp_ne_zero

/-- **Proposition 5**, the is-might contradiction: no nonempty context accepts both `¬B` and
`◇B` for a never-void `B`, that is, `¬B, ◇B ⊨ ⊥`. -/
theorem eq_empty_of_accepts_neg_dia {φ : Sentence W} (hφ : NeverVoid φ)
    (h₁ : Accepts s (-φ)) (h₂ : Accepts s (dia φ)) : s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
  rcases accepts_dia_iff.1 h₂ with ⟨v, hv, h1⟩ | h0
  · have := h₁ v hv
    rw [neg_apply, h1] at this
    exact absurd this (by decide)
  · exact hφ s w hw (h0 w hw)

/-- **Proposition 5**, the if-might contradiction: for nonmodal `A` and never-void `B`,
`◇A, A → ¬B, A → ◇B ⊨ ⊥`. -/
theorem eq_empty_of_if_might {φ ψ : Sentence W} (hφ : ContextFree φ) (hψ : NeverVoid ψ)
    (h₀ : Accepts s (dia φ)) (h₁ : Accepts s (cond φ (-ψ))) (h₂ : Accepts s (cond φ (dia ψ))) :
    s = ∅ := by
  rw [accepts_cond_iff] at h₁ h₂
  have hu := eq_empty_of_accepts_neg_dia hψ h₁ h₂
  rw [hφ.update_eq_restrict] at hu
  refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
  rcases accepts_dia_iff.1 h₀ with ⟨v, hv, h1⟩ | h0
  · exact (Set.eq_empty_iff_forall_notMem.1 hu) v ⟨hv, by rw [h1]; decide⟩
  · exact (Set.eq_empty_iff_forall_notMem.1 hu) w ⟨hw, (h0 w hw).ge⟩

/-- **Proposition 5**, non-veridical *might*: `◇C ⊭ C`. -/
theorem not_entails_of_dia : ¬ Entails {dia (ofSet ({true} : Set Bool))} (ofSet {true}) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, accepts_dia_ofSet_iff]
    exact fun _ ↦ ⟨true, Set.mem_univ _, rfl⟩
  exact absurd (accepts_ofSet_iff.1 this (Set.mem_univ false)) (by simp)

/-- Replacement of Logical Equivalents fails for *must* (§5), since `□A ⊨ A` but `¬□A ⊭ ¬A`. -/
theorem not_entails_neg_box : ¬ Entails {-box (ofSet ({true} : Set Bool))} (-ofSet {true}) := by
  intro h
  have := h Set.univ fun φ hφ w hw ↦ by
    rw [Set.mem_singleton_iff.1 hφ, neg_apply,
      (box_eq_neg_one_iff hw).2 ⟨false, Set.mem_univ _, by simp⟩]
    decide
  rw [neg_ofSet, accepts_ofSet_iff] at this
  exact this (Set.mem_univ true) rfl

/-- Modus Tollens holds for conditional-free sentences (**Fact 11**)... -/
theorem modus_tollens (a b : Set W) :
    Entails {cond (ofSet a) (ofSet b), -ofSet b} (-ofSet a) := by
  intro s h
  have h₁ := accepts_ofSet_iff.1 (accepts_cond_ofSet_iff.1 (h _ (Set.mem_insert _ _)))
  have h₂ := h _ (Set.mem_insert_of_mem _ rfl)
  rw [neg_ofSet, accepts_ofSet_iff] at h₂ ⊢
  exact fun w hw hwa ↦ h₂ hw (h₁ ⟨hw, hwa⟩)

theorem not_modus_tollens_void :
    ¬ Entails {cond (ofSet (Set.univ : Set Unit)) (cond (ofSet ∅) (ofSet ∅)),
      -cond (ofSet ∅) (ofSet ∅)} (-ofSet Set.univ) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rcases hφ with rfl | rfl
    · rw [cond_ofSet_empty, accepts_cond_ofSet_iff]
      exact accepts_zero _
    · rw [cond_ofSet_empty, neg_zero]
      exact accepts_zero _
  rw [neg_ofSet, Set.compl_univ, accepts_ofSet_iff] at this
  exact this (Set.mem_univ ())

private theorem marble_box (w : Bool) : box (ofSet {false}) Set.univ w = -1 :=
  (box_eq_neg_one_iff (Set.mem_univ w)).2 ⟨true, Set.mem_univ _, by simp⟩

private theorem marble_must : Accepts Set.univ (cond (-ofSet {true}) (box (ofSet {false}))) := by
  rw [neg_ofSet, accepts_cond_ofSet_iff, accepts_box_iff, accepts_ofSet_iff]
  intro w hw
  simpa using hw.2

private theorem marble_not_must : Accepts Set.univ (-box (ofSet ({false} : Set Bool))) :=
  fun w _ ↦ by rw [neg_apply, marble_box]; decide

/-- ... and fails for a modal consequent, [yalcin-2012]'s marble (28): with a green and a black
marble possible, *if the marble is not green, it must be black* and *it is not the case that it
must be black* are accepted, *the marble is green* is not. -/
theorem not_modus_tollens_box :
    ¬ Entails {cond (-ofSet {true}) (box (ofSet {false})), -box (ofSet {false})}
      (ofSet ({true} : Set Bool)) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rcases hφ with rfl | rfl
    · exact marble_must
    · exact marble_not_must
  exact absurd (accepts_ofSet_iff.1 this (Set.mem_univ false)) (by simp)

theorem not_contraposition_box :
    ¬ Entails {cond (-ofSet {true}) (box (ofSet {false}))}
      (cond (-box (ofSet {false})) (ofSet ({true} : Set Bool))) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by rw [Set.mem_singleton_iff.1 hφ]; exact marble_must
  rw [accepts_cond_iff, update_eq_self_of_accepts marble_not_must] at this
  exact absurd (accepts_ofSet_iff.1 this (Set.mem_univ false)) (by simp)

/-- Uniform Substitution fails (Proposition 4). Although `p ⊨ p ∨ q` for conditional-free `p`... -/
theorem entails_disj_ofSet (p q : Set W) : Entails {ofSet p} (disj (ofSet p) (ofSet q)) := by
  intro s h
  rw [disj_ofSet, accepts_ofSet_iff]
  exact (accepts_ofSet_iff.1 (h _ rfl)).trans Set.subset_union_left

theorem not_entails_disj_cond :
    ¬ Entails {cond (ofSet (∅ : Set Unit)) (ofSet ∅)}
      (disj (cond (ofSet ∅) (ofSet ∅)) (ofSet ∅)) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, cond_ofSet_empty]
    exact accepts_zero _
  have h0 := this () (Set.mem_univ _)
  rw [cond_ofSet_empty, disj_apply] at h0
  exact absurd h0 (by simp)

/-- Replacement of Logical Equivalents fails (Proposition 4). For conditional-free `p` and `q`,
`p → q` and `¬p ∨ q` are equivalent... -/
theorem entails_cond_iff_disj (p q : Set W) :
    Entails {cond (ofSet p) (ofSet q)} (disj (-ofSet p) (ofSet q)) ∧
      Entails {disj (-ofSet p) (ofSet q)} (cond (ofSet p) (ofSet q)) := by
  refine ⟨fun s h ↦ ?_, fun s h ↦ ?_⟩ <;> have h₀ := h _ rfl <;>
    rw [neg_ofSet, disj_ofSet, accepts_ofSet_iff] at * <;>
    rw [accepts_cond_ofSet_iff, accepts_ofSet_iff] at *
  · intro w hw
    by_cases hp : w ∈ p
    · exact .inr (h₀ ⟨hw, hp⟩)
    · exact .inl hp
  · exact fun w hw ↦ (h₀ hw.1).resolve_left (not_not.2 hw.2)

theorem not_entails_neg_cond_neg_disj :
    ¬ Entails {-cond (ofSet (∅ : Set Unit)) (ofSet ∅)} (-disj (-ofSet ∅) (ofSet ∅)) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, cond_ofSet_empty, neg_zero]
    exact accepts_zero _
  rw [neg_ofSet, disj_ofSet, neg_ofSet, Set.compl_empty, Set.univ_union, Set.compl_univ,
    accepts_ofSet_iff] at this
  exact this (Set.mem_univ ())

/-- Conditional Proof fails with modal premises (§5). `q, ◇¬p, p ⊨ ¬q`, since no nonempty context
accepts both `p` and `◇¬p`... -/
theorem entails_of_dia_neg (p q : Set W) :
    Entails {ofSet p, ofSet q, dia (-ofSet p)} (-ofSet q) := by
  intro s h
  have hp := accepts_ofSet_iff.1 (h _ (Set.mem_insert _ _))
  have hd := h _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rw [neg_ofSet, accepts_dia_ofSet_iff] at hd
  intro w hw
  obtain ⟨v, hvs, hvp⟩ := hd ⟨w, hw⟩
  exact absurd (hp hvs) hvp

/-- ... yet `q, ◇¬p ⊭ p → ¬q`, in footnote 18's model of a `pq`-world and a `¬pq`-world. -/
theorem not_entails_cond_of_dia_neg :
    ¬ Entails {ofSet (Set.univ : Set Bool), dia (-ofSet {true})}
      (cond (ofSet {true}) (-ofSet Set.univ)) := by
  intro h
  have := h Set.univ fun φ hφ ↦ by
    rcases hφ with rfl | rfl
    · exact accepts_ofSet_iff.2 subset_rfl
    · rw [neg_ofSet, accepts_dia_ofSet_iff]
      exact fun _ ↦ ⟨false, Set.mem_univ _, by simp⟩
  rw [accepts_cond_ofSet_iff, neg_ofSet, Set.compl_univ, accepts_ofSet_iff] at this
  exact this ⟨Set.mem_univ true, rfl⟩

theorem not_accepts_fn18_printed :
    ¬ Accepts Set.univ (conj (ofSet (Set.univ : Set Bool)) (-dia (ofSet {true}))) := by
  intro h
  have := h true (Set.mem_univ _)
  rw [conj_apply, neg_apply, (dia_eq_one_iff (Set.mem_univ _)).2 ⟨true, Set.mem_univ _, by simp⟩]
    at this
  simp at this

end Inference

/-! ### Probability and acceptance (§4)

A credence over the worlds gives each sentence, at a context, the trivalent probability of
[egre-rossi-sprenger-2026a] (Definition 5). Mirroring coordinates the credence with the context.
Definition 6 asks only that the credence give the context probability 1, but the paper uses it as
regularity on the context, a credence positive at exactly the context's worlds (footnote 8 and
the proof of Theorem 2), and under the literal reading the probability half of Theorem 1 fails
(`not_prob_cond_box_eq_of_literal`). `Mirrors` is the regular reading. -/

section Probability

open Sentence Classical

variable [MeasurableSpace W] {μ : Measure W} {s : Set W} {φ ψ : Sentence W}

/-- A credence mirrors a context when its positive-weight worlds are exactly the context's. -/
def Mirrors (μ : Measure W) (s : Set W) : Prop := ∀ w, μ {w} ≠ 0 ↔ w ∈ s

theorem Mirrors.measure_eq_zero_iff [Countable W] (h : Mirrors μ s) {t : Set W} :
    μ t = 0 ↔ ∀ w ∈ t, w ∉ s := by
  rw [measure_null_iff_singleton t.to_countable]
  exact forall₂_congr fun w _ ↦ by simpa using (h w).not

variable [Countable W] [DiscreteMeasurableSpace W]

theorem Mirrors.prob_eq_one_iff' [IsFiniteMeasure μ] (h : Mirrors μ s) {f : W → SignType} :
    prob μ f = 1 ↔ ∀ w ∈ s, f w ≠ -1 := by
  rw [Trivalent.prob_eq_one_iff, h.measure_eq_zero_iff]
  exact ⟨fun H w hw hf ↦ H w hf hw, fun H w hf hw ↦ H w hw hf⟩

theorem Mirrors.prob_eq_zero_iff' [IsFiniteMeasure μ] (h : Mirrors μ s) {f : W → SignType} :
    prob μ f = 0 ↔ (∀ w ∈ s, f w ≠ 1) ∧ ∃ w ∈ s, f w = -1 := by
  rw [Trivalent.prob_eq_zero_iff, h.measure_eq_zero_iff, Ne, h.measure_eq_zero_iff]
  push Not
  exact and_congr ⟨fun H w hw hf ↦ H w hf hw, fun H w hf hw ↦ H w hw hf⟩
    ⟨fun ⟨w, hf, hw⟩ ↦ ⟨w, hw, hf⟩, fun ⟨w, hw, hf⟩ ↦ ⟨w, hf, hw⟩⟩

/-- Under mirroring, probability 1 is acceptance (§4.1). -/
theorem Mirrors.prob_eq_one_iff [IsFiniteMeasure μ] (h : Mirrors μ s) :
    prob μ (φ s) = 1 ↔ Accepts s φ := by
  rw [h.prob_eq_one_iff']
  exact forall₂_congr fun _ _ ↦ SignType.nonneg_iff_ne_neg_one.symm

theorem Mirrors.prob_eq_zero_or_one [IsFiniteMeasure μ] (h : Mirrors μ s) {f : W → SignType}
    (hu : ∀ w ∈ s, ∀ w' ∈ s, f w = f w') : prob μ f = 0 ∨ prob μ f = 1 := by
  by_cases hacc : ∀ w ∈ s, f w ≠ -1
  · exact .inr (h.prob_eq_one_iff'.2 hacc)
  · push Not at hacc
    obtain ⟨w₀, hw₀, hf⟩ := hacc
    refine .inl (h.prob_eq_zero_iff'.2 ⟨fun w hw ↦ ?_, w₀, hw₀, hf⟩)
    rw [hu w hw w₀ hw₀, hf]
    decide

/-- Under a mirroring credence, *must* sentences have probability 0 or 1 (**Fact 4**)... -/
theorem prob_box_eq_zero_or_one [IsFiniteMeasure μ] (h : Mirrors μ s) :
    prob μ (box φ s) = 0 ∨ prob μ (box φ s) = 1 :=
  h.prob_eq_zero_or_one fun _ hw _ hw' ↦ box_apply_congr hw hw'

theorem prob_dia_eq_zero_or_one [IsFiniteMeasure μ] (h : Mirrors μ s) :
    prob μ (dia φ s) = 0 ∨ prob μ (dia φ s) = 1 :=
  h.prob_eq_zero_or_one fun _ hw _ hw' ↦ dia_apply_congr hw hw'

theorem prob_cond_box_eq_zero [IsFiniteMeasure μ] (h : Mirrors μ s)
    (hn : ¬ Accepts s (cond φ ψ)) : prob μ (cond φ (box ψ) s) = 0 := by
  obtain ⟨w₀, hw₀, hneg⟩ : ∃ w ∈ s, cond φ ψ s w = -1 := by
    simpa [Accepts, SignType.nonneg_iff_ne_neg_one] using hn
  have hu₀ : w₀ ∈ update s φ := by
    by_contra hu
    rw [cond_apply_of_notMem hw₀ hu] at hneg
    exact absurd hneg (by decide)
  rw [cond_apply_of_mem hw₀ hu₀] at hneg
  have hbox : ∀ w ∈ update s φ, box ψ (update s φ) w = -1 :=
    fun w hw ↦ (box_eq_neg_one_iff hw).2 ⟨w₀, hu₀, hneg⟩
  refine h.prob_eq_zero_iff'.2 ⟨fun w hw ↦ ?_, w₀, hw₀, ?_⟩
  · by_cases hu : w ∈ update s φ
    · rw [cond_apply_of_mem hw hu, hbox w hu]; decide
    · rw [cond_apply_of_notMem hw hu]; decide
  · rw [cond_apply_of_mem hw₀ hu₀, hbox w₀ hu₀]

theorem prob_box_cond_eq_zero [IsFiniteMeasure μ] (h : Mirrors μ s)
    (hn : ¬ Accepts s (cond φ ψ)) : prob μ (box (cond φ ψ) s) = 0 := by
  obtain ⟨w₀, hw₀, hneg⟩ : ∃ w ∈ s, cond φ ψ s w = -1 := by
    simpa [Accepts, SignType.nonneg_iff_ne_neg_one] using hn
  have hbox : ∀ w ∈ s, box (cond φ ψ) s w = -1 :=
    fun w hw ↦ (box_eq_neg_one_iff hw).2 ⟨w₀, hw₀, hneg⟩
  exact h.prob_eq_zero_iff'.2 ⟨fun w hw ↦ by rw [hbox w hw]; decide, w₀, hw₀, hbox w₀ hw₀⟩

/-- Under a mirroring credence `A → □B` is never more probable than `A → B` (**Theorem 1**,
probability half)... -/
theorem prob_cond_box_le [IsFiniteMeasure μ] (h : Mirrors μ s) :
    prob μ (cond φ (box ψ) s) ≤ prob μ (cond φ ψ s) := by
  by_cases ha : Accepts s (cond φ ψ)
  · rw [h.prob_eq_one_iff.2 (accepts_cond_box_iff.2 ha), h.prob_eq_one_iff.2 ha]
  · rw [prob_cond_box_eq_zero h ha]
    exact zero_le

theorem prob_cond_box_eq_prob_box_cond [IsFiniteMeasure μ] (h : Mirrors μ s) :
    prob μ (cond φ (box ψ) s) = prob μ (box (cond φ ψ) s) := by
  by_cases ha : Accepts s (cond φ ψ)
  · rw [h.prob_eq_one_iff.2 (accepts_cond_box_iff.2 ha),
      h.prob_eq_one_iff.2 (accepts_box_cond_iff.2 ha)]
  · rw [prob_cond_box_eq_zero h ha, prob_box_cond_eq_zero h ha]

/-- Under Definition 6 read literally, a credence giving the context probability 1 without
positive weight at each of its worlds, the probability half of Theorem 1 fails: concentrated on a
`¬p`-world, the credence makes `p → □¬p` certain by All Void and `□(p → ¬p)` impossible. -/
theorem not_prob_cond_box_eq_of_literal :
    ∃ μ : Measure Bool, IsProbabilityMeasure μ ∧ μ Set.univ = 1 ∧
      prob μ (cond (ofSet {true}) (box (-ofSet {true})) Set.univ) ≠
        prob μ (box (cond (ofSet {true}) (-ofSet {true})) Set.univ) := by
  refine ⟨Measure.dirac false, inferInstance, by simp, fun heq ↦ ?_⟩
  have h1 : prob (Measure.dirac false)
      (cond (ofSet {true}) (box (-ofSet {true})) Set.univ) = 1 := by
    rw [prob_dirac_eq_one_iff, cond_apply_of_notMem (Set.mem_univ _) (by simp)]
  have h2 : box (cond (ofSet ({true} : Set Bool)) (-ofSet {true})) Set.univ false = -1 :=
    (box_eq_neg_one_iff (Set.mem_univ _)).2 ⟨true, Set.mem_univ _, by
      rw [cond_apply_of_mem (Set.mem_univ _) (by simp)]
      simp⟩
  rw [h1, eq_comm, prob_dirac_eq_one_iff, h2] at heq
  exact absurd heq (by decide)

variable [Finite W]

theorem mirrors_uniformOn (s : Set W) : Mirrors (uniformOn s) s := fun w ↦ by
  rw [Ne, uniformOn_eq_zero_iff s.toFinite, Set.inter_singleton_eq_empty, not_not]

theorem exists_mirrors (hs : s.Nonempty) : ∃ μ : Measure W, IsProbabilityMeasure μ ∧ Mirrors μ s :=
  ⟨uniformOn s, isProbabilityMeasure_uniformOn' s.toFinite hs .of_discrete, mirrors_uniformOn s⟩

/-- Acceptance is probability 1 under every credence mirroring the context (**Definition 7**). -/
theorem accepts_iff_forall_mirrors :
    Accepts s φ ↔ ∀ μ : Measure W, IsProbabilityMeasure μ → Mirrors μ s → prob μ (φ s) = 1 := by
  refine ⟨fun h μ _ hμ ↦ hμ.prob_eq_one_iff.2 h, fun h ↦ ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact accepts_empty φ
  · obtain ⟨μ, hμ, hm⟩ := exists_mirrors hs
    exact hm.prob_eq_one_iff.1 (h μ hμ hm)

/-- An inference preserves certainty (Definition 8) when every credence mirroring a context that
makes the premises certain makes the conclusion certain. -/
def CEntails (Γ : Set (Sentence W)) (ψ : Sentence W) : Prop :=
  ∀ s (μ : Measure W), IsProbabilityMeasure μ → Mirrors μ s →
    (∀ φ ∈ Γ, prob μ (φ s) = 1) → prob μ (ψ s) = 1

/-- Certainty preservation is acceptance preservation (**Theorem 2**). -/
theorem cEntails_iff_entails {Γ : Set (Sentence W)} : CEntails Γ ψ ↔ Entails Γ ψ := by
  refine ⟨fun h s hs ↦ accepts_iff_forall_mirrors.2 fun μ hμ hm ↦
    h s μ hμ hm fun φ hφ ↦ hm.prob_eq_one_iff.2 (hs φ hφ), fun h s μ _ hm hΓ ↦ ?_⟩
  exact hm.prob_eq_one_iff.2 (h s fun φ hφ ↦ hm.prob_eq_one_iff.1 (hΓ φ hφ))

end Probability

/-! #### Predictions -/

section Predictions

open Sentence Classical

theorem cond_ofSet (a b : Set W) :
    cond (ofSet a) (ofSet b) = ofCooper (EgreRossiSprenger2026a.ofAdams ⟨a, b⟩) := by
  change cond (ofCooper fun w ↦ ofProp (w ∈ a)) (ofCooper fun w ↦ ofProp (w ∈ b)) = _
  rw [cond_ofCooper]
  rfl

variable [MeasurableSpace W]

/-- A conditional whose antecedent is an epistemic contradiction is void throughout, so its
probability is 1 by All Void, under every credence and at every context (footnote 11). -/
theorem prob_cond_contra (μ : Measure W) (q : Set W) (φ : Sentence W) (s : Set W) :
    prob μ (cond (conj (-ofSet q) (dia (ofSet q))) φ s) = 1 := by
  have h0 : cond (conj (-ofSet q) (dia (ofSet q))) φ s = 0 := by
    funext w
    rw [Sentence.cond, ite_eq_right, Pi.zero_apply]
    rw [update_eq_empty_of_forall_not_accepts fun _ ht ↦ not_accepts_contra ht q]
    exact Set.notMem_empty _
  rw [h0, prob_of_measure_support_eq_zero (by simp)]

variable [DiscreteMeasurableSpace W]

/-- For conditional-free `A` and `B`, the probability of `A → B` is the conditional probability of
`B` given `A` (**Adams's Thesis**, §4.1), at every context and under every credence, since the
degenerate clause makes nonmodal sentences context-independent. -/
theorem prob_cond_ofSet {μ : Measure W} {a : Set W} (b : Set W) (h : μ a ≠ 0) (s : Set W) :
    prob μ (cond (ofSet a) (ofSet b) s) = μ[b | a] := by
  rw [cond_ofSet]
  exact EgreRossiSprenger2026a.prob_ofAdams h

/-- On a fair coin the epistemic contradiction *the coin is facing heads and might not face heads*
has probability `1/2`, true at the heads world and false at the tails world (footnote 12). -/
theorem prob_contra'_coin :
    prob (uniformOn Set.univ) (conj (ofSet {true}) (dia (-ofSet {true})) Set.univ) = 1 / 2 := by
  have hval : conj (ofSet ({true} : Set Bool)) (dia (-ofSet {true})) Set.univ =
      fun w ↦ ofProp (w = true) := by
    funext w
    have hd : dia (-ofSet ({true} : Set Bool)) Set.univ w = 1 :=
      (dia_eq_one_iff (Set.mem_univ _)).2 ⟨false, Set.mem_univ _, by simp⟩
    rw [conj_apply, hd]
    refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_ <;> cases w <;> simp
  rw [hval, prob_uniformOn_univ,
    prob_count_eq (P := {true}) (S := Finset.univ) (by decide) (by decide) Finset.univ_nonempty]
  simp

/-- *If the die has been tossed, the outcome is greater than 1* (20) has probability `5/6` and *if
the die has been tossed, the outcome must be greater than 1* (21) probability `0`, though a
context accepts the one exactly when it accepts the other. -/
theorem die_bare_vs_must :
    prob (uniformOn Set.univ) (cond (ofSet Set.univ) (ofSet {w : Fin 6 | w ≠ 0}) Set.univ) =
        5 / 6 ∧
      prob (uniformOn Set.univ)
        (cond (ofSet Set.univ) (box (ofSet {w : Fin 6 | w ≠ 0})) Set.univ) = 0 := by
  constructor
  · rw [prob_cond_ofSet _ (by simp), cond_univ, uniformOn_univ,
      show {w : Fin 6 | w ≠ 0} = ↑({1, 2, 3, 4, 5} : Finset (Fin 6)) by ext w; revert w; decide,
      Measure.count_apply_finset, show ({1, 2, 3, 4, 5} : Finset (Fin 6)).card = 5 from rfl]
    simp
  · refine prob_cond_box_eq_zero (mirrors_uniformOn Set.univ) fun h ↦ ?_
    have := h 0 (Set.mem_univ _)
    rw [cond_apply_of_mem (Set.mem_univ _) (by simp)] at this
    simp at this

end Predictions

/-! ### The nonmodal fragment is the Mind paper's language

The Cooper valuations of Definition 1 are those of [egre-rossi-sprenger-2026a], and the
conditional–modal semantics extends them: a formula of that paper's language denotes the
nonmodal sentence of its Cooper values, and the connectives commute with the embedding. -/

section MindLanguage

open Sentence EgreRossiSprenger2026a

variable {ι : Type*} (t : W → ι → Bool)

/-- The nonmodal sentence a formula of the conditional language expresses, at worlds whose atoms
`t` values. -/
def ofFormula (A : Formula ι) : Sentence W := ofCooper (value t A)

theorem contextFree_ofFormula (A : Formula ι) : ContextFree (ofFormula t A) :=
  contextFree_ofCooper _

@[simp] theorem ofFormula_neg (A : Formula ι) : ofFormula t (.neg A) = -ofFormula t A := rfl

@[simp] theorem ofFormula_conj (A B : Formula ι) :
    ofFormula t (.conj A B) = conj (ofFormula t A) (ofFormula t B) := rfl

@[simp] theorem ofFormula_disj (A B : Formula ι) :
    ofFormula t (.disj A B) = disj (ofFormula t A) (ofFormula t B) := rfl

@[simp] theorem ofFormula_cond (A B : Formula ι) :
    ofFormula t (.cond A B) = cond (ofFormula t A) (ofFormula t B) :=
  (cond_ofCooper _ _).symm

end MindLanguage

end EgreRossiSprenger2026b
