module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Order.SetNotation

/-!
# Erotetic reasoning with alternatives

The erotetic theory of reasoning of Koralus and Mascarenhas treats the premises of a deductive
task asymmetrically: a disjunction-like first premise raises a set of alternatives, a question;
the second premise is a hint toward an answer; the reasoner selects the alternative the hint
bears on and reads conclusions off the selected alternative, a mental-models analog of
conjunction elimination. A `Problem` is the alternative set with its hint; a conclusion is
`Illusory` under a selection rule when some selected alternative yields it although it does not
follow from the premises' classical content. The selection rule is a parameter: `Matches` is
the exact content overlap of the mental-models and erotetic literature, the alternative
carrying the hint's content, and `Overlaps` is bare consistency with the hint; probabilistic
rules such as selection by confirmation are study-specific refinements. The schema `indirect`
covers the classical illusory inference from disjunction as the special case where the hint is
the first conjunct itself (`disjunction_eq_indirect`), and matching provably undergenerates
the indirect case while certifying the classical one.

The generators formalized with the schema are the three the literature has established:
disjunction, indefinites (one alternative per witness), and the epistemic modal *might*, whose
attentive content is the alternative pair of the prejacent with the tautology.

## Implementation notes

* Alternatives are bare `Set W` propositions; `Matches p := p ⊆ hint` renders exact content
  overlap semantically, with no syntactic conjunct structure.
* Under the weak `Overlaps` rule the symmetric conclusion of the classical schema is also
  certified (`disjunction_illusory_overlaps_right`): the rule records attention, not the
  asymmetry, which comes from the selection theory.

## References

* [koralus-mascarenhas-2013]
* [koralus-mascarenhas-2018]
* [walsh-johnson-laird-2004]
* [mascarenhas-koralus-2017]
* [mascarenhas-picat-2019]
* [sable-meyer-mascarenhas-2022]
* [bade-picat-chung-mascarenhas-2022]
-/

@[expose] public section

namespace Erotetic

open Set

variable {W : Type*}

/-- A reasoning problem whose first premise raises alternatives and whose second premise is a
hint. -/
structure Problem (W : Type*) where
  /-- The Hamblin alternatives raised by the first premise. -/
  alts : Set (Set W)
  /-- The second premise. -/
  hint : Set W

namespace Problem

variable (P : Problem W)

/-- The classical content of the two premises together. -/
def premises : Set W := ⋃₀ P.alts ∩ P.hint

/-- A conclusion follows classically from the premises. -/
def Entails (q : Set W) : Prop := P.premises ⊆ q

/-- The erotetic selection of the alternative `p` as the answer: the alternative with the
hint. -/
def selected (p : Set W) : Set W := p ∩ P.hint

/-- Bare overlap: the hint is consistent with the alternative. -/
def Overlaps (p : Set W) : Prop := (P.selected p).Nonempty

/-- Exact matching: the alternative carries the hint's content, the selection procedure of the
mental-models account and the erotetic theory. -/
def Matches (p : Set W) : Prop := p ⊆ P.hint

/-- A conclusion is illusory under the selection rule `sel` when some selected alternative the
hint partially overlaps yields it by conjunction elimination, though it does not follow
classically. -/
def Illusory (sel : Set W → Prop) (q : Set W) : Prop :=
  (∃ p ∈ P.alts, sel p ∧ (P.selected p).Nonempty ∧ P.selected p ⊆ q) ∧ ¬ P.Entails q

theorem Illusory.mono {sel sel' : Set W → Prop} (h : ∀ p, sel p → sel' p) {q : Set W}
    (hq : P.Illusory sel q) : P.Illusory sel' q :=
  ⟨hq.1.imp fun p ⟨hp, hs, hne, hsub⟩ ↦ ⟨hp, h p hs, hne, hsub⟩, hq.2⟩

end Problem

/-- The classical schema: the premise `(a ∧ b) ∨ c` raising `{a ∧ b, c}`, with hint `a`. -/
def disjunction (a b c : Set W) : Problem W := ⟨{a ∩ b, c}, a⟩

/-- The indirect schema: the same disjunctive premise with an arbitrary hint `d`. -/
def indirect (a b c d : Set W) : Problem W := ⟨{a ∩ b, c}, d⟩

/-- *might φ* raises the alternatives `{φ, ⊤}`, its attentive content. -/
def might (p : Set W) : Set (Set W) := {p, univ}

/-- The *might* schema: `might (a ∧ b)` with hint `a`. -/
def mightProblem (a b : Set W) : Problem W := ⟨might (a ∩ b), a⟩

/-- An indefinite raises one alternative per member of its domain. -/
def indefinite {E : Type*} (P : E → Set W) (D : Set E) (hint : Set W) : Problem W :=
  ⟨P '' D, hint⟩

variable {a b c d : Set W}

theorem disjunction_eq_indirect : disjunction a b c = indirect a b c a := rfl

@[simp] theorem premises_indirect : (indirect a b c d).premises = ((a ∩ b) ∪ c) ∩ d := by
  simp [indirect, Problem.premises]

@[simp] theorem premises_disjunction : (disjunction a b c).premises = ((a ∩ b) ∪ c) ∩ a :=
  premises_indirect

theorem indirect_invalid (h : ((c ∩ d) \ b).Nonempty) : ¬ (indirect a b c d).Entails b := by
  obtain ⟨w, ⟨hwc, hwd⟩, hwb⟩ := h
  exact fun hent ↦ hwb (hent (by simpa using ⟨Or.inr hwc, hwd⟩))

theorem indirect_illusory {sel : Set W → Prop} (hsel : sel (a ∩ b)) (hab : (a ∩ b ∩ d).Nonempty)
    (h : ((c ∩ d) \ b).Nonempty) : (indirect a b c d).Illusory sel b :=
  ⟨⟨a ∩ b, by simp [indirect], hsel, hab, fun _ hw ↦ hw.1.2⟩, indirect_invalid h⟩

theorem matches_disjunction_iff (hc : (c \ a).Nonempty) {p : Set W}
    (hp : p ∈ ({a ∩ b, c} : Set (Set W))) : (disjunction a b c).Matches p ↔ p = a ∩ b := by
  obtain ⟨w, hwc, hwa⟩ := hc
  rcases hp with rfl | rfl
  · simp [Problem.Matches, disjunction]
  · exact ⟨fun h ↦ (hwa (h hwc)).elim, fun h ↦ (hwa (h ▸ hwc).1).elim⟩

theorem disjunction_illusory_matches (hab : (a ∩ b).Nonempty) (h : ((c ∩ a) \ b).Nonempty) :
    (disjunction a b c).Illusory (disjunction a b c).Matches b :=
  indirect_illusory (fun _ hw ↦ hw.1) (hab.elim fun w ⟨hwa, hwb⟩ ↦ ⟨w, ⟨hwa, hwb⟩, hwa⟩) h

theorem disjunction_illusory_overlaps_right (hca : (c ∩ a).Nonempty)
    (h : ((a ∩ b) \ c).Nonempty) :
    (disjunction a b c).Illusory (disjunction a b c).Overlaps c := by
  refine ⟨⟨c, by simp [disjunction], hca, hca, fun _ hw ↦ hw.1⟩, ?_⟩
  obtain ⟨w, ⟨hwa, hwb⟩, hwc⟩ := h
  exact fun hent ↦ hwc (hent (by simpa using ⟨Or.inl ⟨hwa, hwb⟩, hwa⟩))

theorem not_matches_right (hc : (c \ a).Nonempty) : ¬ (disjunction a b c).Matches c :=
  fun h ↦ hc.elim fun _ hw ↦ hw.2 (h hw.1)

theorem indirect_not_illusory_matches (h₁ : ((a ∩ b) \ d).Nonempty) (h₂ : (c \ d).Nonempty)
    (q : Set W) : ¬ (indirect a b c d).Illusory (indirect a b c d).Matches q := by
  rintro ⟨⟨p, hp, hm, -, -⟩, -⟩
  simp only [indirect, mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact h₁.elim fun _ hw ↦ hw.2 (hm hw.1)
  · exact h₂.elim fun _ hw ↦ hw.2 (hm hw.1)

theorem mightProblem_eq_disjunction : mightProblem a b = disjunction a b univ := rfl

@[simp] theorem sUnion_might (p : Set W) : ⋃₀ might p = univ := by simp [might]

theorem might_ne_of_ne_univ {p : Set W} (hp : p ≠ univ) : might p ≠ might univ := by
  simp [might, hp]

theorem might_illusory (hab : (a ∩ b).Nonempty) (h : (a \ b).Nonempty) :
    (mightProblem a b).Illusory (mightProblem a b).Matches b :=
  disjunction_illusory_matches hab (by simpa using h)

theorem indefinite_illusory {E : Type*} {P : E → Set W} {D : Set E} {hint : Set W} {john : E}
    (hj : john ∈ D) (hw : (P john ∩ hint).Nonempty)
    (hcm : ∃ x ∈ D, ((P x ∩ hint) \ P john).Nonempty) :
    (indefinite P D hint).Illusory (indefinite P D hint).Overlaps (P john) := by
  refine ⟨⟨P john, ⟨john, hj, rfl⟩, hw, hw, fun _ hw ↦ hw.1⟩, ?_⟩
  obtain ⟨x, hx, w, ⟨hwx, hwh⟩, hwj⟩ := hcm
  exact fun hent ↦ hwj (hent ⟨⟨P x, ⟨x, hx, rfl⟩, hwx⟩, hwh⟩)

/-! ### Posteriors over the schema

Conditioning a measure on the schema's premises cannot separate the attractive conclusion from
the symmetric one: the premises distribute, and the two posteriors agree exactly when the
priors of the two conjunctions do. -/

section Posterior

open MeasureTheory ProbabilityTheory

variable {A B C : Set W}

theorem premises_eq_distrib (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A = (A ∩ B) ∪ (A ∩ C) := by
  ext; simp; tauto

theorem premises_inter_left (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A ∩ B = A ∩ B := by
  ext; simp; tauto

theorem premises_inter_right (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A ∩ C = A ∩ C := by
  ext; simp; tauto

theorem posterior_eq_iff [MeasurableSpace W] (μ : Measure W) [IsFiniteMeasure μ]
    (hE : MeasurableSet (((A ∩ B) ∪ C) ∩ A)) (h0 : μ (((A ∩ B) ∪ C) ∩ A) ≠ 0) :
    μ[B | ((A ∩ B) ∪ C) ∩ A] = μ[C | ((A ∩ B) ∪ C) ∩ A] ↔ μ (A ∩ B) = μ (A ∩ C) := by
  rw [cond_apply hE, cond_apply hE, premises_inter_left, premises_inter_right]
  exact ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    (ENNReal.inv_ne_top.2 h0)

end Posterior

end Erotetic
