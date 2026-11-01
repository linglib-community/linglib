module

public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.Events.Basic
public import Studies.KennedyLevin2008

/-!
# Beavers (2011): On Affectedness

This file formalizes Beavers's analysis of affectedness as specificity about scalar change. A
predicate relates its theme to a scale, and how strongly it affects the theme is how much it says
about where the theme ends up on that scale. Change is an increase from a contextually given source
to a later goal, following Hay, Kennedy and Levin, so *the soup cooled 5 degrees* effects a
quantized change, *the soup cooled* a non-quantized one, and both entail that the soup changed. The
telic reading that Kennedy and Levin derive for a degree achievement on a scale closed above is a
quantized change to the maximum, and the atelic reading a non-quantized change.

Each degree of affectedness is an existential generalization of the one above it, so the
entailments a predicate has about its theme form one of four sets. These are exactly the four
contentful thematic roles of patienthood in Beavers's earlier work, [each the entailment set of some
predicate](##ArgumentStructure.exists_affectednessRole_eq).

## Implementation notes

* A scale `s` indexes a measure function `m s`. An event's result on `s` is where its theme ends,
  provided the theme started at the contextual source `b` and ended higher, which is SOURCE and
  GOAL (48) with the increase of (43).
* The goal of the measure-phrase reading is `b + n`, fixed only relative to the contextual source,
  whereas Beavers's exemplars of quantized change such as *break* have a lexical goal.
* Hay, Kennedy and Levin judge *broaden the investigation significantly* telic, since its
  difference value has a lower bound (`HayKennedyLevin1999.isBounded_significantly`). A
  lower-bounded change is non-quantized, and the diagnostics of (63) count only quantized change
  as telic. The two papers define telicity differently, as a bounded difference value and as a
  predicate that describes no proper part of its events.

## TODO

* Derive the telicity of quantized change, the first row of (63), from the Figure/Path Relation
  (53), with scales as Krifka's paths (`Krifka1998.isTelic_sourceGoal`).
* The remaining diagnostics of (63)–(66) and the result-phrase data of §5.

## References

* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [J. Hay, C. Kennedy and B. Levin, *Scalar Structure Underlies Telicity in “Degree
  Achievements”* (1999)][hay-kennedy-levin-1999]
* [C. Kennedy and B. Levin, *Measure of Change: The Adjectival Core of Degree Achievements*
  (2008)][kennedy-levin-2008]
* [J. Beavers, *The structure of lexical meaning: Why semantics really matters*
  (2010)][beavers-2010]
-/

@[expose] public section

namespace Beavers2011

open Event (τ)

open ArgumentStructure HayKennedyLevin1999 Set

variable {α S D T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Scalar change (§4.1) -/

section Result

variable [LinearOrder D]

/-- `Result m b x s g e` holds when the theme `x` starts the event `e` at the contextual source `b`
on the scale `s` and ends it at the higher goal `g`, the result relation of (48). -/
def Result (m : S → α → T → D) (b : D) (x : α) (s : S) (g : D) (e : E) : Prop :=
  m s x (τ e).fst = b ∧ b < g ∧ m s x (τ e).snd = g

variable {m : S → α → T → D} {b : D} {θ : α → S → E → Prop} {φ : α → E → Prop}

-- (59)
theorem exists_lt_of_nonQuantizedChange (h : NonQuantizedChange θ (Result m b) φ) {x : α}
    {e : E} (hx : φ x e) : ∃ s, θ x s e ∧ m s x (τ e).fst < m s x (τ e).snd :=
  let ⟨s, hs, _, h₁, h₂, h₃⟩ := h x e hx
  ⟨s, hs, h₁ ▸ h₃ ▸ h₂⟩

theorem snd_eq_of_quantizedChange {s₀ : S} {g : D} (hθ : ∀ x s e, θ x s e → s = s₀)
    (h : QuantizedChange θ (Result m b) φ g) {x : α} {e : E} (hx : φ x e) :
    m s₀ x (τ e).snd = g :=
  let ⟨s, hs, _, _, h₃⟩ := h x e hx
  hθ x s e hs ▸ h₃

-- p. 357
theorem not_quantizedChange_of_snd_ne {s₀ : S} (hθ : ∀ x s e, θ x s e → s = s₀) {x x' : α}
    {e e' : E} (hx : φ x e) (hx' : φ x' e') (hne : m s₀ x (τ e).snd ≠ m s₀ x' (τ e').snd) :
    ¬ ∃ g, QuantizedChange θ (Result m b) φ g := fun ⟨_, h⟩ ↦
  hne ((snd_eq_of_quantizedChange hθ h hx).trans (snd_eq_of_quantizedChange hθ h hx').symm)

end Result

/-! ### Quantized and non-quantized change as difference values ((58)) -/

section HayKennedyLevin

variable [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] {m : S → α → T → D} {b : D}
  {s₀ : S} {φ : α → E → Prop}

-- (58a) [hay-kennedy-levin-1999]
theorem quantizedChange_iff_describes_measurePhrase {n : D} (hn : 0 < n) :
    QuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ (b + n) ↔
      ∀ x e, φ x e → m s₀ x (τ e).fst = b ∧
        Describes (m s₀) x (measurePhrase n) (τ e).fst (τ e).snd := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, describes_iff_sub_mem, measurePhrase,
    Degree.Comparison.mem_interval, Degree.Comparison.rel_eq, lt_add_iff_pos_right, hn, true_and]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by rw [h₁, h₂, add_sub_cancel_left]⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, by rw [← h₂, h₁, add_sub_cancel]⟩

-- (58b) [hay-kennedy-levin-1999]
theorem nonQuantizedChange_iff_describes_someAmount :
    NonQuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ ↔
      ∀ x e, φ x e → m s₀ x (τ e).fst = b ∧
        Describes (m s₀) x someAmount (τ e).fst (τ e).snd := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, describes_iff_sub_mem, someAmount,
    Degree.Comparison.mem_interval, Degree.Comparison.rel_gt, sub_pos]
  constructor
  · rintro ⟨g, h₁, h₂, h₃⟩
    exact ⟨h₁, by rw [h₁, h₃]; exact h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, h₁, h₁ ▸ h₂, rfl⟩

end HayKennedyLevin

/-! ### Degree achievements ((60a), (60b)) -/

section KennedyLevin

open KennedyLevin2008 Degree

variable [LinearOrder D] {m : S → α → T → D} {b : D} {s₀ : S} {φ : α → E → Prop}

-- [kennedy-levin-2008]
theorem quantizedChange_top_iff_maxStandard [OrderTop D] (hb : b ≠ ⊤) :
    QuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ ⊤ ↔
      ∀ x e, φ x e → m s₀ x (τ e).fst = b ∧
        (τ e).snd ∈ measureOfChange (m s₀) x (τ e).fst ⁻¹' Set.Ici ⊤ := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, hb.lt_top, true_and]
  exact and_congr_right fun h ↦ by rw [preimage_measureOfChange_Ici_top (h ▸ hb)]; simp

-- [kennedy-levin-2008]
theorem nonQuantizedChange_iff_minStandard :
    NonQuantizedChange (fun _ s _ ↦ s = s₀) (Result m b) φ ↔
      ∀ x e, φ x e → m s₀ x (τ e).fst = b ∧
        (τ e).snd ∈ measureOfChange (m s₀) x (τ e).fst ⁻¹' Set.Ioi ⊥ := by
  refine forall₂_congr fun x e ↦ imp_congr_right fun _ ↦ ?_
  simp only [Result, exists_eq_left, preimage_measureOfChange_Ioi_bot, Set.mem_preimage,
    Set.mem_Ioi, exists_and_left, exists_eq_right']
  exact and_congr_right fun h ↦ by rw [h]

end KennedyLevin

end Beavers2011
