module

public import Linglib.Semantics.Degree.Adjective
public import Linglib.Fragments.English.Adjectives

/-!
# Kennedy (2007): Vagueness and Grammar

Kennedy separates relative gradable adjectives (*tall*, *long*), whose positive form compares
with a contextual standard, from absolute ones, whose standard is an endpoint of the scale: the
minimum (*wet*, *bent*) or the maximum (*full*, *dry*). The positive form is
`⟦pos⟧ = λg λx. g(x) ≥ s(g)` (27), with the standard `s` fixed by the scale rather than by a
comparison class, and Interpretive Economy (66) derives it from the scale structure. This file
checks the diagnostics of Section 3.2 that separate the positive forms at the three standards,
the preimages of `Set.Ioi θ`, `Set.Ioi ⊥` and `Set.Ici ⊤` under the measure.

## Main results

* `definite_relative`, `definite_maximum`: definite descriptions, (53)–(54).
* `sorites_maximum`, `sorites_minimum`: the Sorites second premise, (57)–(58).
* `antonyms_isCompl`: the denial of a minimum-standard adjective asserts its maximum-standard
  antonym, (47).
* `wet_of_wetter`, `not_dry_of_drier`, `long_undetermined_of_longer`: comparatives, (49)–(51).
* `table61_iff_licenses`: maximizers and minimizers follow the endpoints of the scale, (61).
* `bent_straight_absolute`: Interpretive Economy selects the endpoint standard of *bent* and
  *straight* over a relative one, p. 37.
* `closed_admits_both_endpoints`: a totally closed scale admits both endpoint standards,
  (67)–(68).

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [rotstein-winter-2004]
-/

@[expose] public section

namespace Kennedy2007

open Degree

variable {Entity D : Type*} [LinearOrder D]

/-! ### Definite descriptions (§3.2, (53)–(54)) -/

/-- *The long one* succeeds because two objects of different length can always be told apart by
a contextual standard. -/
theorem definite_relative (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    ∃ θ, a ∈ μ ⁻¹' Set.Ioi θ ∧ b ∉ μ ⁻¹' Set.Ioi θ :=
  ⟨μ b, h, lt_irrefl _⟩

/-- A maximum-standard adjective distinguishes two objects only when exactly one is at the maximum,
as in *the full one* (54). -/
theorem definite_maximum [OrderTop D] (μ : Entity → D) (a b : Entity) :
    a ∈ μ ⁻¹' Set.Ici ⊤ ∧ b ∉ μ ⁻¹' Set.Ici ⊤ ↔ μ a = ⊤ ∧ μ b ≠ ⊤ := by
  simp

/-! ### The Sorites second premise (§3.2, (57)–(58)) -/

/-- A theater with one fewer occupied seat than a full one is not full (57), since any degree
below the maximum fails a maximum standard. -/
theorem sorites_maximum [OrderTop D] {μ : Entity → D} {x : Entity} (h : μ x < ⊤) :
    x ∉ μ ⁻¹' Set.Ici ⊤ :=
  h.not_ge

/-- A rod with no bend is not bent (58), since exactly the minimum fails a minimum standard. -/
theorem sorites_minimum [OrderBot D] (μ : Entity → D) (x : Entity) :
    x ∉ μ ⁻¹' Set.Ioi ⊥ ↔ μ x = ⊥ := by
  simp

/-- A minimum standard and its antonym's maximum standard on the dual scale partition the domain, so
*the door is not open* entails *the door is closed* (47). -/
theorem antonyms_isCompl [OrderBot D] (μ : Entity → D) :
    IsCompl (μ ⁻¹' Set.Ioi ⊥) ((OrderDual.toDual ∘ μ) ⁻¹' Set.Ici ⊤) := by
  have : (OrderDual.toDual ∘ μ) ⁻¹' Set.Ici ⊤ = (μ ⁻¹' Set.Ioi ⊥)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Ici, top_le_iff,
      Set.mem_compl_iff, Set.mem_Ioi, not_lt, le_bot_iff]
    exact OrderDual.toDual.injective.eq_iff
  rw [this]
  exact isCompl_compl

/-! ### Comparatives (§3.2, (49)–(52)) -/

/-- *The floor is wetter than the countertop* entails *the floor is wet* (49): the comparative is
the positive form at the countertop's degree, a stronger standard than the minimum. -/
theorem wet_of_wetter [OrderBot D] (μ : Entity → D) (b : Entity) :
    μ ⁻¹' Set.Ioi (μ b) ⊆ μ ⁻¹' Set.Ioi ⊥ :=
  Set.preimage_mono (Set.Ioi_subset_Ioi bot_le)

/-- *The floor is drier than the countertop* entails *the countertop is not dry* (50). -/
theorem not_dry_of_drier [OrderTop D] {μ : Entity → D} {a b : Entity} (h : μ b < μ a) :
    b ∉ μ ⁻¹' Set.Ici ⊤ :=
  sorites_maximum (h.trans_le le_top)

/-- *Rod A is longer than rod B* entails neither that A is long nor that it is not (51). -/
theorem long_undetermined_of_longer (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    (∃ θ, a ∈ μ ⁻¹' Set.Ioi θ) ∧ ∃ θ, a ∉ μ ⁻¹' Set.Ioi θ :=
  ⟨⟨μ b, h⟩, μ a, lt_irrefl _⟩

/-! ### Degree modifiers (§3.2, (61)) -/

/-- The A_pos row of table (61) says whether a maximizer or minimizer is acceptable with the
positive member of an antonym pair, by the pair's scale type. -/
def table61Pos : Boundedness → EndpointModifier → Bool
  | .open_, _ => false
  | .lowerClosed, .maximizer => false
  | .lowerClosed, .minimizer => true
  | .upperClosed, .maximizer => true
  | .upperClosed, .minimizer => false
  | .closed, _ => true

/-- The A_neg row of table (61) says the same for the negative member. -/
def table61Neg : Boundedness → EndpointModifier → Bool
  | .open_, _ => false
  | .lowerClosed, .maximizer => true
  | .lowerClosed, .minimizer => false
  | .upperClosed, .maximizer => false
  | .upperClosed, .minimizer => true
  | .closed, _ => true

/-- `table61` is table (61) as printed, indexed by the member of the pair. -/
def table61 (p : Polarity) (b : Boundedness) (m : EndpointModifier) : Bool :=
  if p = .positive then table61Pos b m else table61Neg b m

/-- Every cell of (61) is the endpoint structure of the adjective's own scale. -/
theorem table61_iff_licenses (p : Polarity) (b : Boundedness) (m : EndpointModifier) :
    table61 p b m = true ↔ (p • b).Licenses m := by
  cases p <;> cases b <;> cases m <;> decide

open English.Adjectives in
-- (61)
theorem fragment_pairs_table61 :
    full.boundedness.Licenses .maximizer ∧ empty.boundedness.Licenses .maximizer ∧
    wet.boundedness.Licenses .minimizer ∧ ¬ wet.boundedness.Licenses .maximizer ∧
    dry.boundedness.Licenses .maximizer ∧ ¬ dry.boundedness.Licenses .minimizer ∧
    bent.boundedness.Licenses .minimizer ∧ ¬ bent.boundedness.Licenses .maximizer ∧
    straight.boundedness.Licenses .maximizer ∧
    ¬ tall.boundedness.Licenses .maximizer ∧ ¬ short.boundedness.Licenses .minimizer := by
  decide

/-! ### Interpretive Economy (§4.2–§4.3) -/

theorem open_requires_comparison_class :
    Boundedness.IsRelative .open_ := by
  decide

open English.Adjectives in
/-- *Bent* and *straight* could take a relative standard, but their scale fixes the transition
from zero to positive bend, and Interpretive Economy selects the standard it fixes (p. 37). -/
theorem bent_straight_absolute :
    bent.boundedness.Admits .minEndpoint ∧ ¬ bent.boundedness.Admits .contextual ∧
      straight.boundedness.Admits .maxEndpoint ∧ ¬ straight.boundedness.Admits .contextual := by
  decide

/-- A totally closed scale is interpretively variable, admitting both endpoint standards
((67)–(68), *opaque/transparent*, *open/exposed*); the maximum is only the default. -/
theorem closed_admits_both_endpoints :
    Boundedness.closed.Admits .minEndpoint ∧ Boundedness.closed.Admits .maxEndpoint := by
  decide

end Kennedy2007
