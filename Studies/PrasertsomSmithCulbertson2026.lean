module

public import Linglib.Core.InformationTheory.Entropy
public import Studies.Aikhenvald2000

/-!
# Prasertsom, Smith and Culbertson (2026): Domain-General Categorisation Explains Constrained Cross-Linguistic Variation in Noun Classification

This file formalizes the two formal claims of Prasertsom, Smith and Culbertson. The paper asks
why animacy, but never colour, serves as a basis for noun classification although both are
perceptually salient, and answers with a domain-general principle: a good category is one whose
defining feature predicts the other features of its members, and animacy predicts more than
colour. The typological premise is read off Aikhenvald's sample of noun categorization
devices, where animacy is a basic semantic parameter and colour is none of any device's
(`animacy_not_colour`). The predictive-power manipulation of Experiments 3a and 3b rests on two
sixteen-stimulus sets, Tables 4 and 5 (`predictiveAnimacy`, `predictiveColour`), built so that
the conditional entropy of horn type, body shape, and appendage shape is lower given the
predictive dimension than given the other, and so that exchanging the animacy and colour columns
of one set gives the other (`mirror_images`). The six entropy orderings of Table 6 that the
design promises are proved from the tables under the uniform measure over the stimuli
(`predictiveAnimacy_horn`, `predictiveColour_horn`, and their shape and appendage siblings).

## Implementation notes

Each stimulus set has exactly one stimulus per animacy–colour pair, so a set is a function from
the pair to the three remaining dimensions and its stimuli are the sixteen cells of the grid.
Conditional entropy is the substrate's `H[X | Y ; μ]` under the uniform measure on the grid,
reduced to counts by `condEntropy_uniformOn_univ`; each ordering then comes to a positive multiple
of `negMulLog (1/2)`, the entropy of the evenly split fibres that only the non-predictive
dimension has. The learning and sorting results of Experiments 1a to 3b and the corpus measures
of §4.1, which are means over participants and word embeddings, are not formalized.

## TODO

The paper's reason for the mirror design, that animacy in one set has exactly the predictive
power of colour in the other, is the invariance of conditional entropy under a relabelling of
the population and of the conditioning variable; the substrate has no such lemma yet, so the
predictive-colour orderings are computed directly rather than transferred from the
predictive-animacy ones through `mirror_images`.

## References

* [prasertsom-smith-culbertson-2026]
* [aikhenvald-2000]
-/

@[expose] public section

open InformationTheory MeasureTheory ProbabilityTheory Real
open scoped ProbabilityTheory

namespace PrasertsomSmithCulbertson2026

/-! ### The typological premise (§1) -/

/-- Every noun class or numeral classifier device of the sample has animacy, humanness, or sex
among its basic semantic parameters, and none has colour. -/
theorem animacy_not_colour (l : Aikhenvald2000.Language)
    (hk : l.device = some .nounClass ∨ l.device = some .numeralClassifier) :
    (∃ p ∈ l.semantics, p = .animacy ∨ p = .humanness ∨ p = .sex) ∧ .colour ∉ l.semantics :=
  ⟨Aikhenvald2000.animacy_basic l hk, Aikhenvald2000.colour_never l⟩

/-! ### The stimulus dimensions (§4.2.2, Fig. 10) -/

/-- The animacy dimension has two kinds of animate, with crescent or round eyes, and two of
inanimate, dots forming a line or a triangle. -/
inductive Animacy where
  | crescentEyed
  | roundEyed
  | line
  | triangle
  deriving DecidableEq, Repr, Fintype

/-- The colour dimension has two warm and two cool colours. -/
inductive Colour where
  | red
  | orange
  | blue
  | teal
  deriving DecidableEq, Repr, Fintype

/-- Horn type. -/
inductive Horn where
  | crescent
  | jagged
  deriving DecidableEq, Repr, Fintype

/-- Body shape. -/
inductive Shape where
  | circle
  | inkblot
  deriving DecidableEq, Repr, Fintype

/-- Appendage shape. -/
inductive Appendages where
  | wavy
  | round
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Animacy := ⊤
instance : MeasurableSpace Colour := ⊤
instance : MeasurableSpace Horn := ⊤
instance : MeasurableSpace Shape := ⊤
instance : MeasurableSpace Appendages := ⊤

section sums

variable {M : Type*} [AddCommMonoid M]

theorem Animacy.sum_univ (f : Animacy → M) :
    ∑ v, f v = f .crescentEyed + f .roundEyed + f .line + f .triangle := by
  rw [show (Finset.univ : Finset Animacy) = {.crescentEyed, .roundEyed, .line, .triangle} by decide]
  simp [Finset.sum_insert, add_assoc]

theorem Colour.sum_univ (f : Colour → M) : ∑ v, f v = f .red + f .orange + f .blue + f .teal := by
  rw [show (Finset.univ : Finset Colour) = {.red, .orange, .blue, .teal} by decide]
  simp [Finset.sum_insert, add_assoc]

theorem Horn.sum_univ (f : Horn → M) : ∑ v, f v = f .crescent + f .jagged := by
  rw [show (Finset.univ : Finset Horn) = {.crescent, .jagged} by decide]
  simp [Finset.sum_insert]

theorem Shape.sum_univ (f : Shape → M) : ∑ v, f v = f .circle + f .inkblot := by
  rw [show (Finset.univ : Finset Shape) = {.circle, .inkblot} by decide]
  simp [Finset.sum_insert]

theorem Appendages.sum_univ (f : Appendages → M) : ∑ v, f v = f .wavy + f .round := by
  rw [show (Finset.univ : Finset Appendages) = {.wavy, .round} by decide]
  simp [Finset.sum_insert]

end sums

/-- The three dimensions of a stimulus that its animacy and colour may predict. -/
structure Body where
  horn : Horn
  shape : Shape
  appendages : Appendages
  deriving DecidableEq, Repr

/-! ### The stimulus sets (Tables 4 and 5) -/

/-- The predictive-animacy set (Table 4) gives the body of the stimulus in each animacy–colour
cell. The eight animates are alike; among the inanimates each body dimension departs once per
kind of inanimate from its inanimate value. -/
def predictiveAnimacy : Animacy × Colour → Body
  | (.crescentEyed, _) | (.roundEyed, _) => ⟨.crescent, .circle, .wavy⟩
  | (.line, .red) => ⟨.crescent, .inkblot, .round⟩
  | (.line, .orange) => ⟨.jagged, .circle, .round⟩
  | (.line, .blue) => ⟨.jagged, .inkblot, .wavy⟩
  | (.line, .teal) => ⟨.jagged, .inkblot, .round⟩
  | (.triangle, .red) => ⟨.jagged, .inkblot, .wavy⟩
  | (.triangle, .orange) => ⟨.jagged, .inkblot, .round⟩
  | (.triangle, .blue) => ⟨.jagged, .circle, .round⟩
  | (.triangle, .teal) => ⟨.crescent, .inkblot, .round⟩

/-- The predictive-colour set (Table 5). -/
def predictiveColour : Animacy × Colour → Body
  | (_, .red) | (_, .orange) => ⟨.crescent, .circle, .wavy⟩
  | (.crescentEyed, .blue) => ⟨.crescent, .inkblot, .round⟩
  | (.crescentEyed, .teal) => ⟨.jagged, .inkblot, .wavy⟩
  | (.roundEyed, .blue) => ⟨.jagged, .circle, .round⟩
  | (.roundEyed, .teal) => ⟨.jagged, .inkblot, .round⟩
  | (.line, .blue) => ⟨.jagged, .inkblot, .wavy⟩
  | (.line, .teal) => ⟨.jagged, .circle, .round⟩
  | (.triangle, .blue) => ⟨.jagged, .inkblot, .round⟩
  | (.triangle, .teal) => ⟨.crescent, .inkblot, .round⟩

/-- The colour that stands in for a kind of animacy when the two columns are exchanged, the warm
colours for the animates and the cool ones for the inanimates. -/
def Animacy.toColour : Animacy → Colour
  | .crescentEyed => .red
  | .roundEyed => .orange
  | .line => .blue
  | .triangle => .teal

/-- The kind of animacy that stands in for a colour. -/
def Colour.toAnimacy : Colour → Animacy
  | .red => .crescentEyed
  | .orange => .roundEyed
  | .blue => .line
  | .teal => .triangle

/-- The exchange of the animacy and colour columns. -/
def mirror : Animacy × Colour → Animacy × Colour
  | (a, c) => (c.toAnimacy, a.toColour)

/-- The two sets are mirror images of each other, each being the other with the animacy and
colour columns exchanged. -/
theorem mirror_images :
    ∀ p, predictiveColour (mirror p) = predictiveAnimacy p
      ∧ predictiveAnimacy (mirror p) = predictiveColour p := by
  decide

/-! ### Predictive power (Table 6) -/

private theorem card_grid : Fintype.card (Animacy × Colour) = 16 := rfl

private theorem negMulLog_half_pos : 0 < negMulLog (1 / 2 : ℝ) := by
  rw [negMulLog, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- In the predictive-animacy set, animacy predicts horn type better than colour does. -/
theorem predictiveAnimacy_horn :
    H[Body.horn ∘ predictiveAnimacy | Prod.fst ; uniformOn Set.univ]
      < H[Body.horn ∘ predictiveAnimacy | Prod.snd ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Horn.sum_univ, Function.comp_apply, predictiveAnimacy]
  norm_num
  linarith [negMulLog_half_pos]

/-- In the predictive-animacy set, animacy predicts body shape better than colour does. -/
theorem predictiveAnimacy_shape :
    H[Body.shape ∘ predictiveAnimacy | Prod.fst ; uniformOn Set.univ]
      < H[Body.shape ∘ predictiveAnimacy | Prod.snd ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Shape.sum_univ, Function.comp_apply, predictiveAnimacy]
  norm_num
  linarith [negMulLog_half_pos]

/-- In the predictive-animacy set, animacy predicts appendage shape better than colour does. -/
theorem predictiveAnimacy_appendages :
    H[Body.appendages ∘ predictiveAnimacy | Prod.fst ; uniformOn Set.univ]
      < H[Body.appendages ∘ predictiveAnimacy | Prod.snd ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Appendages.sum_univ, Function.comp_apply, predictiveAnimacy]
  norm_num
  linarith [negMulLog_half_pos]

/-- In the predictive-colour set, colour predicts horn type better than animacy does. -/
theorem predictiveColour_horn :
    H[Body.horn ∘ predictiveColour | Prod.snd ; uniformOn Set.univ]
      < H[Body.horn ∘ predictiveColour | Prod.fst ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Horn.sum_univ, Function.comp_apply, predictiveColour]
  norm_num
  linarith [negMulLog_half_pos]

/-- In the predictive-colour set, colour predicts body shape better than animacy does. -/
theorem predictiveColour_shape :
    H[Body.shape ∘ predictiveColour | Prod.snd ; uniformOn Set.univ]
      < H[Body.shape ∘ predictiveColour | Prod.fst ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Shape.sum_univ, Function.comp_apply, predictiveColour]
  norm_num
  linarith [negMulLog_half_pos]

/-- In the predictive-colour set, colour predicts appendage shape better than animacy does. -/
theorem predictiveColour_appendages :
    H[Body.appendages ∘ predictiveColour | Prod.snd ; uniformOn Set.univ]
      < H[Body.appendages ∘ predictiveColour | Prod.fst ; uniformOn Set.univ] := by
  rw [condEntropy_uniformOn_univ, condEntropy_uniformOn_univ, card_grid]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Animacy.sum_univ, Colour.sum_univ,
    Appendages.sum_univ, Function.comp_apply, predictiveColour]
  norm_num
  linarith [negMulLog_half_pos]

end PrasertsomSmithCulbertson2026
