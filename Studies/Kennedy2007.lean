module

public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Languages.English.Adjectives
public import Linglib.Data.Examples.Kennedy2007

/-!
# Kennedy (2007): Vagueness and Grammar

A relative gradable adjective such as *tall* compares with a standard the context supplies, and
an absolute one with an endpoint of its scale: the minimum for *wet* and *bent*, the maximum for
*full* and *dry*. The positive form of a measure `μ` at these standards is the preimage of
`Set.Ioi θ`, of `Set.Ioi ⊥` and of `Set.Ici ⊤`. The file derives from them the contrasts between
relative and absolute adjectives in definite descriptions, the Sorites argument, comparatives and
antonym pairs, checks the judgments on *perfectly* and *slightly* against the scales of the
English adjectives, and states what Interpretive Economy admits on those scales.

## Implementation notes

The rows are the thirty adjectives of the modifier paradigm with each of the two modifiers.
Nineteen of the adjectives have an entry in the English adjectives file and are marked with it;
the prediction is read off the scale of the entry. The paper measures *bent* and *dirty* towards
the positive pole of a lower-closed scale, and the language file measures *straight* and *clean*
towards the positive pole of the dual scale, which gives each adjective the same endpoints.

## References

* [kennedy-2007]
* [kennedy-mcnally-2005]
* [rotstein-winter-2004]
-/

@[expose] public section

namespace Kennedy2007


variable {Entity D : Type*} [LinearOrder D]

/-! ### Definite descriptions (§3.2, (53)–(54)) -/

-- (53)
theorem definite_relative (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    ∃ θ, a ∈ μ ⁻¹' Set.Ioi θ ∧ b ∉ μ ⁻¹' Set.Ioi θ :=
  ⟨μ b, h, lt_irrefl _⟩

/-- A maximum-standard adjective distinguishes two objects only when exactly one is at the maximum,
as in *the full one* (54). -/
theorem definite_maximum [OrderTop D] (μ : Entity → D) (a b : Entity) :
    a ∈ μ ⁻¹' Set.Ici ⊤ ∧ b ∉ μ ⁻¹' Set.Ici ⊤ ↔ μ a = ⊤ ∧ μ b ≠ ⊤ := by
  simp

/-! ### The Sorites second premise (§3.2, (57)–(58)) -/

-- (57)
theorem sorites_maximum [OrderTop D] {μ : Entity → D} {x : Entity} (h : μ x < ⊤) :
    x ∉ μ ⁻¹' Set.Ici ⊤ :=
  h.not_ge

-- (58)
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

-- (49)
theorem wet_of_wetter [OrderBot D] (μ : Entity → D) (b : Entity) :
    μ ⁻¹' Set.Ioi (μ b) ⊆ μ ⁻¹' Set.Ioi ⊥ :=
  Set.preimage_mono (Set.Ioi_subset_Ioi bot_le)

-- (50)
theorem not_dry_of_drier [OrderTop D] {μ : Entity → D} {a b : Entity} (h : μ b < μ a) :
    b ∉ μ ⁻¹' Set.Ici ⊤ :=
  sorites_maximum (h.trans_le le_top)

-- (51)
theorem long_undetermined_of_longer (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    (∃ θ, a ∈ μ ⁻¹' Set.Ioi θ) ∧ ∃ θ, a ∉ μ ⁻¹' Set.Ioi θ :=
  ⟨⟨μ b, h⟩, μ a, lt_irrefl _⟩

/-! ### Degree modifiers (§4.2, (62)–(65)) -/

/-- The adjective of the English adjectives file that a lexeme of the rows is. -/
def Examples.Lexeme.entry : Examples.Lexeme → Adjective
  | .tall => English.Adjectives.tall
  | .deep => English.Adjectives.deep
  | .expensive => English.Adjectives.expensive
  | .short => English.Adjectives.short
  | .shallow => English.Adjectives.shallow
  | .bent => English.Adjectives.bent
  | .dirty => English.Adjectives.dirty
  | .straight => English.Adjectives.straight
  | .flat => English.Adjectives.flat
  | .clean => English.Adjectives.clean
  | .certain => English.Adjectives.certain
  | .safe => English.Adjectives.safe
  | .pure => English.Adjectives.pure_
  | .uncertain => English.Adjectives.uncertain
  | .dangerous => English.Adjectives.dangerous
  | .full => English.Adjectives.full
  | .openAdj => English.Adjectives.open_
  | .empty => English.Adjectives.empty
  | .closed => English.Adjectives.closed_

/-- *Perfectly* picks out a maximal degree and *slightly* a minimal one. -/
def Examples.Modifier.endpoint : Examples.Modifier → EndpointModifier
  | .perfectly => .maximizer
  | .slightly => .minimizer

/-- The adjective entry and the endpoint modifier a row tests. -/
def test? (e : Datum) : Option (Adjective × EndpointModifier) := do
  let p ← e.spans.find? (Examples.label? · = some .adjective)
  let l ← Examples.lexeme? p
  let m ← Examples.modifier e
  pure (l.entry, m.endpoint)

/-- A modifier is predicted acceptable with an adjective whose scale has the endpoint it picks
out. -/
def predicted (t : Adjective × EndpointModifier) : Judgment.Band :=
  .ofProp (∃ b ∈ t.1.boundedness, b.Licenses t.2)

-- every lexeme of the rows is an entry of the English adjectives file
theorem entry_mem_allEntries :
    ∀ l : Examples.Lexeme, ∃ a ∈ English.Adjectives.allEntries, a = l.entry := by
  decide

-- every span that names a lexeme is printed as its entry is written
theorem printed :
    ∀ e ∈ Examples.all, ∀ p ∈ e.spans, ∀ l ∈ Examples.lexeme? p,
      (p.words e).map (·.word) = [l.entry.form.toList] := by
  decide

/-- The judgments on *perfectly* and *slightly* with the nineteen adjectives that have an entry are
those the scales of the entries predict. -/
theorem modifiers_check : Datum.Checks test? predicted Examples.all 38 := by
  decide

/-! ### Interpretive Economy (§4.2–§4.3) -/

-- §4.2
theorem open_requires_comparison_class : Boundedness.IsRelative .open_ :=
  Boundedness.isRelative_iff.2 rfl

open English.Adjectives in
/-- *Bent* and *straight* could take a relative standard, but their scale fixes the transition
from zero to positive bend, and Interpretive Economy selects the standard it fixes (p. 37). -/
theorem bent_straight_absolute :
    (∃ b ∈ bent.boundedness, b.Admits .minEndpoint ∧ ¬ b.Admits .contextual) ∧
      ∃ b ∈ straight.boundedness, b.Admits .maxEndpoint ∧ ¬ b.Admits .contextual := by
  decide

/-- A totally closed scale is interpretively variable, admitting both endpoint standards
((67)–(68), *opaque/transparent*, *open/exposed*); the maximum is only the default. -/
theorem closed_admits_both_endpoints :
    Boundedness.closed.Admits .minEndpoint ∧ Boundedness.closed.Admits .maxEndpoint := by
  decide

end Kennedy2007
