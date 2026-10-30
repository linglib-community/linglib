module

public import Linglib.Fragments.English.Adjectives
public import Studies.CarianiSantorioWellwood2023
public import Studies.Lassiter2017

/-!
# Cariani, Santorio and Wellwood (2024): Confidence Reports

Cariani, Santorio and Wellwood give adjectival *confident* and nominal *confidence* one
denotation, a property of confidence states, each with a proposition as its theme and ranked by a
total preorder on its holder's states. *σ is confident that p* says that some state of σ's with
theme `p` lies at or above a contrast state, so σ can be [confident of a conjunction and not of
its conjunct](##exists_conjunctionFallacy), which [no threshold on a probability
allows](##image_Ici_ne_likely). *Certain* puts the contrast state at the top, and
*confident* [entails it only there](##image_Ici_subset_image_Ici_iff_isMax). The comparative
compares degrees under a measure that preserves the strict ordering, so its
[transitivity](##Degree.MaxComparative.trans), [antisymmetry](##Degree.MaxComparative.antisymm)
and [connectedness](##Degree.maxComparative_ge_total) hold on any background, while upward
monotonicity [needs a total one](##CarianiSantorioWellwood2023.not_mem_image_Ici_of_not_le) and
[nothing outranks a certainty](##not_maxComparative_of_isMax) only under a monotone measure.

## Implementation notes

* A holder's confidence states form a type `S` with the background preorder, and `θ : S → Set W`
  assigns themes. Orderings vary from holder to holder, so the theorems fix one holder.
* The positive form is `p ∈ θ '' Set.Ici c` for a contrast state `c`, *certain* is
  `p ∈ θ '' {s | IsMax s}`, and the comparative is `Degree.MaxComparative .gt (θ · = p) (θ · = q) μ`
  for an admissible measure, `StrictMono μ`.
* The paper takes the ordering to be a total preorder; the theorems that need totality assume it.
* The paper states no semantics for *doubt*, so (63c) is not formalized.

## Errata

* §4.6 would drop Connectedness (56) by replacing the total order of confidence states with a
  partial order. Connectedness compares degrees on a linear scale and survives any background
  (`Degree.maxComparative_ge_total`); a partial order costs the inference (53) instead
  (`CarianiSantorioWellwood2023.not_mem_image_Ici_of_not_le`).
* (40) puts the state at or above the contrast state, though its prose says "ordered higher".
  With the contrast of a proposition its negation, the corollary that no one is confident of both
  `p` and `¬p`, and the entailment (59), need the strict reading (`maxComparative_compl_of_lt`): a
  tie between the `p`-state and the `¬p`-state satisfies (59a) for both and refutes (59b).
* The upper bound that (68) draws for certainty needs a monotone measure
  (`not_maxComparative_of_isMax`): (21) constrains only strictly ordered states, and the tied
  maximal states of Figure 3 can be measured apart.

## TODO

* The objections to the negation as contrast, (60) and fn. 31.
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

variable {S W D : Type*} [Preorder S] [Preorder D] {θ : S → Set W} {μ : S → D}

/-! ### The positive form and the comparative -/

-- (53): if σ is confident that `p` and more confident of `q` than of `p`, σ is confident that `q`.
example [@Std.Total S (· ≤ ·)] (hμ : StrictMono μ) {c : S} {p q : Set W}
    (hp : p ∈ θ '' Ici c) (h : MaxComparative .gt (θ · = q) (θ · = p) μ) : q ∈ θ '' Ici c :=
  CarianiSantorioWellwood2023.mem_image_of_maxComparative (isUpperSet_Ici c) hμ hp h

/-- The entailment (59) under a contrast mapping `p` to its negation, read strictly: if the
`p`-state lies above the `¬p`-state, its holder is more confident that `p` than that `¬p`. -/
theorem maxComparative_compl_of_lt (hθ : θ.Injective) (hμ : StrictMono μ) {s c : S}
    (hc : θ c = (θ s)ᶜ) (hlt : c < s) : MaxComparative .gt (θ · = θ s) (θ · = (θ s)ᶜ) μ := by
  rw [← hc]
  exact (maxComparative_iff_of_unique (P := (θ · = θ s)) (Q := (θ · = θ c)) rfl (fun _ h ↦ hθ h)
    rfl (fun _ h ↦ hθ h)).2 (hμ hlt)

-- Read weakly, as (40) prints it, (59) fails at a tie: of two tied states, the `p`-state `false`
-- and the `¬p`-state `true`, each lies at or above the other, and a measure that keeps ties level
-- does not put `false` above `true`.
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @LE.le _ tied.toLE true false ∧ @LE.le _ tied.toLE false true ∧
      ¬ MaxComparative .gt (· = false) (· = true) (fun _ : Bool ↦ (0 : ℕ)) :=
  ⟨trivial, trivial, fun h ↦ lt_irrefl 0 ((maxComparative_eq_iff _ _ _).1 h)⟩

/-! ### The conjunction fallacy -/

/-- (52a) *John is not confident that Linda is a bankteller* and (52b) *John is confident that
Linda is a feminist bankteller* are true together whenever `φ ∩ ψ` differs from `φ`, on a
two-state ordering with the `φ ∩ ψ`-state above the `φ`-state and the contrast at the top. -/
theorem exists_conjunctionFallacy {φ ψ : Set W} (h : ¬ φ ⊆ ψ) :
    ∃ θ : Bool → Set W, φ ∩ ψ ∈ θ '' Ici true ∧ φ ∉ θ '' Ici true := by
  refine ⟨fun b ↦ if b then φ ∩ ψ else φ, ⟨true, self_mem_Ici, rfl⟩, ?_⟩
  rintro ⟨b, hb, hbφ⟩
  obtain rfl : b = true := top_le_iff.1 hb
  exact h (by simpa using hbφ.symm ▸ inter_subset_right (s := φ) (t := ψ))

/-- No threshold on a finite measure, Lassiter's *likely*, gives the positive region of a holder
who is confident of a conjunction and not of its conjunct (§4.6, §5.3). -/
theorem image_Ici_ne_likely [MeasurableSpace W] (P : Measure W) [IsFiniteMeasure P] (t : ℝ)
    {c : S} {φ ψ : Set W} (h₁ : φ ∩ ψ ∈ θ '' Ici c) (h₂ : φ ∉ θ '' Ici c) :
    θ '' Ici c ≠ Lassiter2017.likely P t := fun h ↦ by
  have h₃ : φ ∩ ψ ∈ Lassiter2017.likely P t := h ▸ h₁
  exact h₂ (h ▸ (show t < P.real φ from
    (show t < P.real (φ ∩ ψ) from h₃).trans_le (measureReal_mono inter_subset_left)))

/-! ### *Certain* and *confident* -/

-- (65b), (66b)
theorem image_Ici_subset_image_Ici_of_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m)
    (c : S) : θ '' Ici m ⊆ θ '' Ici c :=
  image_mono (Ici_subset_Ici.2 ((total_of (· ≤ ·) c m).elim id fun h ↦ hm h))

/-- *Confident* entails *certain* exactly when its contrast state is maximal, so (65a) and (66a)
need a contrast state below the top of an ordering with maxima. -/
theorem image_Ici_subset_image_Ici_iff_isMax [@Std.Total S (· ≤ ·)] (hθ : θ.Injective) {m : S}
    (hm : IsMax m) {c : S} : θ '' Ici c ⊆ θ '' Ici m ↔ IsMax c := by
  rw [CarianiSantorioWellwood2023.image_Ici_subset_image_Ici_iff hθ]
  exact ⟨hm.mono, fun hc ↦ (total_of (· ≤ ·) m c).elim id fun h ↦ hc h⟩

-- (71) and Figure 3: the states at or above a maximal state are the maximal states.
theorem Ici_eq_setOf_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m) :
    Ici m = {s | IsMax s} := by
  ext s
  exact ⟨fun hs t hst ↦ (hm (hs.trans hst)).trans hs,
    fun hs ↦ (total_of (· ≤ ·) m s).elim id fun h ↦ hs h⟩

/-- Under a monotone measure nothing is more confident than a certainty (68). -/
theorem not_maxComparative_of_isMax [@Std.Total S (· ≤ ·)] (hμ : Monotone μ) {s : S}
    (hs : IsMax s) {p q : Set W} (hsp : θ s = p) : ¬ MaxComparative .gt (θ · = q) (θ · = p) μ :=
  fun h ↦
    let ⟨y, _, hlt⟩ := h.exists_lt hsp
    (hμ ((total_of (· ≤ ·) y s).elim id fun h ↦ hs h)).not_gt hlt

-- Admissibility (21) alone allows it: of two tied maximal states, as at the top of Figure 3, every
-- measure is admissible, and `Bool.toNat` puts `true` above the certainty `false`.
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @StrictMono _ _ tied _ Bool.toNat ∧ @IsMax _ tied.toLE false ∧
      MaxComparative .gt (· = true) (· = false) Bool.toNat :=
  ⟨fun _ _ h ↦ absurd h (lt_irrefl ()), fun _ _ ↦ trivial,
    (maxComparative_eq_iff _ _ _).2 Nat.zero_lt_one⟩

open English.Adjectives in
-- Figure 3 in the fragment: *confident* and *certain* share one upper-closed scale, *certain* at
-- its maximum and *confident* at a contextual standard.
example : confident.dimension = certain.dimension ∧ confident.boundedness = .upperClosed ∧
    certain.standard = .maxEndpoint ∧ confident.standard = .contextual := by
  decide

end CarianiSantorioWellwood2024
