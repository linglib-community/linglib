module

public import Linglib.Fragments.English.Adjectives
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Studies.CarianiSantorioWellwood2023

/-!
# Cariani, Santorio and Wellwood (2024): Confidence Reports

Cariani, Santorio and Wellwood give adjectival *confident* and nominal *confidence* one
denotation, a property of confidence states. Each state carries a proposition as its theme, and
a background ordering ranks a holder's states. *σ is confident that p* says that some state of
σ's with theme `p` lies at or above a contrast state, and *certain* is the same ordering with
the contrast state at the top. The comparative instead compares degrees, assigned by a measure
that preserves the strict ordering. This is the two-component analysis of the authors' 2023 paper
on positive adjectives, and the file sorts the paper's inferences by whether they use the ordering
or the degree scale.

## Implementation notes

* A holder's confidence states form a type `S` with its background preorder, and `θ : S → Set W`
  assigns themes; the states of all holders are the disjoint sum `Σ a, S a`.
* The positive form is `p ∈ θ '' Set.Ici c` for a contrast state `c`, *certain* is
  `p ∈ θ '' {s | IsMax s}`, and the comparative is `Degree.MaxComparative .gt (θ · = p) (θ · = q) μ`
  for `StrictMono μ`.
* Totality of the ordering is a hypothesis of the theorems that use it.
* The paper states no semantics for *doubt*, so (63c) is not formalized.

## TODO

* The conditional (59) under a contrast that maps a proposition to its negation, and the two
  objections to it, (60) and fn. 31. With the weak positive form (40) the entailment needs the
  `p`-state strictly above the `¬p`-state, since a tie satisfies (59a) and refutes (59b); the
  paper's gloss ("ranked higher") reads the contrast strictly.
* Conditional confidence (61), (62), with the ordering indexed by an information state.

## References

* [cariani-santorio-wellwood-2024]
* [cariani-santorio-wellwood-2023]
* [wellwood-2015]
* [tversky-kahneman-1983]
* [lassiter-2017]
-/

@[expose] public section

namespace CarianiSantorioWellwood2024

open Set Degree
open MeasureTheory
open scoped ENNReal

variable {S W D : Type*} [Preorder S] [Preorder D] {θ : S → Set W} {μ : S → D}

/-! ### The comparative and the positive form -/

omit [Preorder S] in
-- (47), (37)
theorem maxComparative_theme_iff (hθ : θ.Injective) (s t : S) :
    MaxComparative .gt (θ · = θ s) (θ · = θ t) μ ↔ μ t < μ s := by
  simp only [hθ.eq_iff]
  exact maxComparative_eq_iff μ s t

/-- Upward monotonicity (53) holds over the region above a contrast state. If σ is confident
that `p` and more confident of `q` than of `p`, then σ is confident that `q`. -/
example [@Std.Total S (· ≤ ·)] (hμ : StrictMono μ) {c : S} {p q : Set W}
    (hp : p ∈ θ '' Ici c) (h : MaxComparative .gt (θ · = q) (θ · = p) μ) : q ∈ θ '' Ici c :=
  CarianiSantorioWellwood2023.mem_image_of_maxComparative (isUpperSet_Ici c) hμ hp h

/-! ### The conjunction fallacy (52) -/

/-- (52a) *John is not confident that Linda is a bankteller* and (52b) *John is confident that
Linda is a feminist bankteller* are true together. Whenever `φ ∩ ψ` differs from `φ`, a two-state
total ordering with the `φ ∩ ψ`-state above the `φ`-state and the contrast state at the top
makes the holder confident of the conjunction but not of the conjunct. -/
theorem exists_conjunctionFallacy {φ ψ : Set W} (h : ¬ φ ⊆ ψ) :
    ∃ θ : Bool → Set W, φ ∩ ψ ∈ θ '' Ici true ∧ φ ∉ θ '' Ici true := by
  refine ⟨fun b ↦ if b then φ ∩ ψ else φ, ⟨true, mem_Ici.2 le_rfl, rfl⟩, ?_⟩
  rintro ⟨b, hb, hbφ⟩
  obtain rfl : b = true := top_le_iff.1 hb
  exact h (by simpa using hbφ.symm ▸ inter_subset_right (s := φ) (t := ψ))

/-- On the threshold account of §2 (7), no holder is confident of a conjunction but not of its
conjunct. -/
theorem image_Ici_ne_ge_over [MeasurableSpace W] (P : Measure W) (t : ℝ≥0∞) {c : S}
    {φ ψ : Set W} (h₁ : φ ∩ ψ ∈ θ '' Ici c) (h₂ : φ ∉ θ '' Ici c) :
    θ '' Ici c ≠ P ⁻¹' Set.Ici t :=
  fun h ↦ h₂ <| h ▸ (show φ ∈ P ⁻¹' Set.Ici t from
    le_trans (show φ ∩ ψ ∈ P ⁻¹' Set.Ici t from h ▸ h₁) (measure_mono inter_subset_left))

/-! ### *Certain* and *confident* (§5.2) -/

-- (65b), (66b)
theorem image_Ici_subset_image_Ici_of_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m)
    (c : S) : θ '' Ici m ⊆ θ '' Ici c :=
  image_mono (Ici_subset_Ici.2 ((total_of (· ≤ ·) c m).elim id fun h ↦ hm h))

-- (65a), (66a)
theorem not_image_Ici_subset_image_Ici (hθ : θ.Injective) {c m : S} (hmc : ¬ m ≤ c) :
    ¬ θ '' Ici c ⊆ θ '' Ici m :=
  mt (CarianiSantorioWellwood2023.image_Ici_subset_image_Ici_iff hθ).1 hmc

/-- *Confident* entails *certain* exactly when its contrast state is maximal, so (65a) needs a
contrast state below the top of an ordering with maxima (69). -/
theorem image_Ici_subset_image_Ici_iff_isMax [@Std.Total S (· ≤ ·)] (hθ : θ.Injective) {m : S}
    (hm : IsMax m) {c : S} : θ '' Ici c ⊆ θ '' Ici m ↔ IsMax c := by
  rw [CarianiSantorioWellwood2023.image_Ici_subset_image_Ici_iff hθ]
  exact ⟨hm.mono, fun hc ↦ (total_of (· ≤ ·) m c).elim id fun h ↦ hc h⟩

open English.Adjectives in
/-- The English fragment agrees with Figure 3, in which *confident* and *certain* measure on one
upper-closed scale, *certain* at its maximum and *confident* at a contextual standard. -/
example : confident.dimension = certain.dimension ∧ confident.boundedness = .upperClosed ∧
    certain.standard = .maxEndpoint ∧ confident.standard = .contextual := by
  decide

-- (71), Figure 3
theorem Ici_eq_setOf_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m) :
    Ici m = {s | IsMax s} := by
  ext s
  exact ⟨fun hs t hst ↦ (hm (hs.trans hst)).trans hs,
    fun hs ↦ (total_of (· ≤ ·) m s).elim id fun h ↦ hs h⟩

/-- Under a monotone measure nothing is more confident than a certainty (68), which admissibility
(21) alone does not ensure. -/
theorem not_maxComparative_of_isMax [@Std.Total S (· ≤ ·)] (hμ : Monotone μ) {s : S}
    (hs : IsMax s) {p q : Set W} (hsp : θ s = p) : ¬ MaxComparative .gt (θ · = q) (θ · = p) μ :=
  fun h ↦
    let ⟨y, _, hlt⟩ := h.exists_lt hsp
    (hμ ((total_of (· ≤ ·) y s).elim id fun h ↦ hs h)).not_gt hlt

-- (68)
theorem maxComparative_of_isMax (hθ : θ.Injective) {s t : S} (hs : IsMax s) (hlt : μ s < μ t) :
    θ s ∈ θ '' {s | IsMax s} ∧ MaxComparative .gt (θ · = θ t) (θ · = θ s) μ :=
  ⟨⟨s, hs, rfl⟩, (maxComparative_theme_iff hθ t s).2 hlt⟩

/-- Two tied maximal states, as at the top of Figure 3, can be measured apart by an admissible
measure, since with every state tied every measure is admissible. The preorder is passed explicitly,
since `Bool`'s own order would otherwise be found. -/
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @StrictMono _ _ tied _ Bool.toNat ∧ @IsMax _ tied.toLE false ∧
      Bool.toNat false < Bool.toNat true :=
  ⟨fun _ _ h ↦ absurd h (lt_irrefl ()), fun _ _ ↦ trivial, Nat.zero_lt_one⟩

end CarianiSantorioWellwood2024
