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
checks the diagnostics of Section 3.2 that separate the three positive forms,
`Degree.RelativePos`, `Degree.MinStandardPos` and `Degree.MaxStandardPos`.

## Main results

* `exists_relativePos_of_lt`, `maxStandardPos_and_not_iff`: definite descriptions, (53)–(54).
* `not_maxStandardPos_of_lt_top`, `not_minStandardPos_iff`: the Sorites second premise,
  (57)–(58).
* `isCompl_minStandardPos_maxStandardPos_dual`: the denial of a minimum-standard adjective
  asserts its maximum-standard antonym, (47).
* `minStandardPos_of_comparative`, `not_maxStandardPos_of_comparative`,
  `relativePos_undetermined_of_comparative`: comparatives, (49)–(51).
* `table61_iff_licenses`: maximizers and minimizers follow the endpoints of the scale, (61).
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

theorem exists_relativePos_of_lt (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    ∃ θ, RelativePos μ θ a ∧ ¬ RelativePos μ θ b :=
  ⟨μ b, h, lt_irrefl _⟩

/-- In *the full one* (54), a maximum-standard adjective tells two objects apart only when one
is at the maximum and the other is not, so two partially full jars leave nothing to pick out. -/
theorem maxStandardPos_and_not_iff [OrderTop D] (μ : Entity → D) (a b : Entity) :
    MaxStandardPos μ a ∧ ¬ MaxStandardPos μ b ↔ μ a = ⊤ ∧ μ b ≠ ⊤ :=
  Iff.rfl

/-! ### The Sorites second premise (§3.2, (57)–(58)) -/

/-- A theater with one fewer occupied seat than a full one is not full (57), since any degree
below the maximum fails a maximum standard. -/
theorem not_maxStandardPos_of_lt_top [OrderTop D] {μ : Entity → D} {x : Entity}
    (h : μ x < ⊤) : ¬ MaxStandardPos μ x :=
  h.ne

/-- A rod with no bend is not bent (58), since exactly the minimum fails a minimum standard. -/
theorem not_minStandardPos_iff [OrderBot D] (μ : Entity → D) (x : Entity) :
    ¬ MinStandardPos μ x ↔ μ x = ⊥ :=
  not_lt.trans le_bot_iff

/-- *The door is not open* entails *the door is closed* (47). A minimum standard and the maximum
standard of the antonym, which measures on the dual scale, split the domain between them, since
the minimum of the one is the maximum of the other. -/
theorem isCompl_minStandardPos_maxStandardPos_dual [OrderBot D] (μ : Entity → D) :
    IsCompl {x | MinStandardPos μ x} {x | MaxStandardPos (OrderDual.toDual ∘ μ) x} := by
  have : {x | MaxStandardPos (OrderDual.toDual ∘ μ) x} = {x | MinStandardPos μ x}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_minStandardPos_iff, MaxStandardPos,
      Function.comp]
    exact OrderDual.toDual.injective.eq_iff
  rw [this]
  exact isCompl_compl

/-! ### Comparatives (§3.2, (49)–(52)) -/

/-- *The floor is wetter than the countertop* entails *the floor is wet* (49). -/
theorem minStandardPos_of_comparative [OrderBot D] {μ : Entity → D} {a b : Entity}
    (h : μ b < μ a) : MinStandardPos μ a :=
  bot_le.trans_lt h

/-- *The floor is drier than the countertop* entails *the countertop is not dry* (50). -/
theorem not_maxStandardPos_of_comparative [OrderTop D] {μ : Entity → D} {a b : Entity}
    (h : μ b < μ a) : ¬ MaxStandardPos μ b :=
  not_maxStandardPos_of_lt_top (h.trans_le le_top)

/-- *Rod A is longer than rod B* entails neither that A is long nor that it is not (51). -/
theorem relativePos_undetermined_of_comparative (μ : Entity → D) {a b : Entity}
    (h : μ b < μ a) :
    (∃ θ, RelativePos μ θ a) ∧ ∃ θ, ¬ RelativePos μ θ a :=
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
/-- The Fragment's antonym pairs fill table (61) with *completely full/empty*, *slightly wet* but
*??completely wet*, *completely dry* but *??slightly dry*, *slightly bent* but *??fully bent*,
*fully straight*, and nothing on the open height scale. -/
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
    Boundedness.IsRelative .open_ :=
  trivial

/-- A totally closed scale is interpretively variable, admitting both endpoint standards
((67)–(68), *opaque/transparent*, *open/exposed*); the maximum is only the default. -/
theorem closed_admits_both_endpoints :
    Boundedness.closed.Admits .minEndpoint ∧ Boundedness.closed.Admits .maxEndpoint :=
  ⟨trivial, trivial⟩

end Kennedy2007
