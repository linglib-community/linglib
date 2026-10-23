module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Denotation

/-!
# Frank and Goodman (2012): Predicting Pragmatic Reasoning in Language Games

Frank and Goodman's rational speech act model of reference games. A context is a model `M` whose
objects vary on two dimensions, colour and shape, and a word names a colour or a shape. The
extension `⟦w⟧ᴹ` of a word is the set of objects with the colour or the shape it names, so a word
is true of the objects in its extension. The literal listener hears a word as the uniform
distribution over its extension. A speaker who wants to refer to an object chooses a word in
proportion to the literal listener's probability of the object, the reciprocal of the size of the
word's extension, and the listener inverts the speaker against a prior, the salience of the
objects. The paper reports the fit of speaker and listener bets to the model.

## Main statements

* `size_principle`: of two words true of an object the speaker prefers the one with the smaller
  extension.
* `speaker_real_singleton_lt_iff`, `listener_real_singleton_lt_iff`: of two objects a word is
  true of, the speaker uses the word more for the one whose other feature more objects share,
  and a listener with no prior preference between the two infers that one.
* `prefers_informative`, `narrowing_blue`, `listener_narrows_blue`: in the context of the paper's
  figure the speaker prefers *circle* to *blue* for the blue circle and uses *blue* less for it
  than for the blue square, so a listener who hears *blue* favours the blue square.

## Implementation notes

* A context gives each object a value on each dimension, and a word is the pair of a dimension
  and the value it names, so the lexical entries are one clause and no table of words against
  objects is given.
* The speaker and the literal listener are the uniform-prior pipeline of `RSA/Uniform.lean` at
  the extensions. The paper's speaker has rationality one and costless words, and the findings
  are stated at every positive rationality.

## References

* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Semantics
open scoped ENNReal Topology Semantics.Superscript

namespace FrankGoodman2012

/-! ### Contexts and words -/

/-- The two dimensions on which the objects of a context vary. -/
inductive Attribute
  | colour | shape
  deriving DecidableEq, Fintype, Repr

/-- The values of a dimension, for colours `C` and shapes `S`. -/
abbrev Attribute.Value (C S : Type) : Attribute → Type
  | .colour => C
  | .shape => S

/-- A word is a one-place predicate that names a colour or a shape. -/
abbrev Word (C S : Type) := Σ a : Attribute, a.Value C S

variable {E C S : Type}

instance [DecidableEq C] [DecidableEq S] (a : Attribute) : DecidableEq (a.Value C S) := by
  cases a <;> exact inferInstance

instance [Fintype C] [Fintype S] (a : Attribute) : Fintype (a.Value C S) := by
  cases a <;> exact inferInstance

instance : MeasurableSpace (Word C S) := ⊤
instance : DiscreteMeasurableSpace (Word C S) := ⟨fun _ ↦ trivial⟩

section Model

variable [DecidableEq C] [DecidableEq S] [Fintype E]

/-- The lexical entries. The extension of a word in a context is the set of objects whose colour
or shape is the one the word names, so `⟦blue⟧ᴹ` is the set of objects that are blue in `M`. -/
instance : Denotes (Word C S)
    ({E : Type} → [Fintype E] → (E → (a : Attribute) → a.Value C S) → Finset E) where
  denote w _ _ M := Finset.univ.filter fun x ↦ M x w.1 = w.2

variable (M : E → (a : Attribute) → a.Value C S)

@[simp] theorem mem_denote {w : Word C S} {x : E} : x ∈ ⟦w⟧ᴹ ↔ M x w.1 = w.2 := by
  simp [Denotes.denote]

variable [Fintype C] [Fintype S]

section Profile

variable [DecidableEq E]

theorem filter_mem_denote (r : E) :
    (Finset.univ.filter fun w : Word C S ↦ r ∈ ⟦w⟧ᴹ) =
      {⟨.colour, M r .colour⟩, ⟨.shape, M r .shape⟩} := by
  ext ⟨a, v⟩
  cases a <;> simp [eq_comm]

theorem profile_eq (r : E) :
    RSA.profile (fun w : Word C S ↦ ⟦w⟧ᴹ) Finset.univ r =
      {⟦(⟨.colour, M r .colour⟩ : Word C S)⟧ᴹ.card, ⟦(⟨.shape, M r .shape⟩ : Word C S)⟧ᴹ.card} := by
  rw [RSA.profile, filter_mem_denote, Finset.insert_val_of_notMem (by simp), Finset.singleton_val]
  rfl

end Profile

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- On hearing a word, the literal listener conditions the uniform prior on its extension. -/
noncomputable def literal : Kernel (Word C S) E :=
  RSA.listener (uniformOn Set.univ) (RSA.truthful fun w : Word C S ↦ (⟦w⟧ᴹ : Set E))

/-- The speaker at rationality `α` is `S(w | r) ∝ L₀(r | w) ^ α`, the paper's second equation at
`α = 1`. -/
noncomputable def speaker (α : ℝ) : Kernel E (Word C S) :=
  RSA.speaker α 0 (literal M) Measure.dirac

/-- The listener of the paper's first equation inverts the speaker against a prior, the salience
of the objects. -/
noncomputable def listener (P : Measure E) (α : ℝ) : Kernel (Word C S) E :=
  RSA.listener P (speaker M α)

instance : IsFiniteKernel (literal M) := inferInstanceAs (IsFiniteKernel (RSA.listener _ _))

instance (α : ℝ) : IsFiniteKernel (speaker M α) :=
  inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _ _))

variable {α : ℝ} {w w₁ w₂ : Word C S} {r r' : E}

theorem speaker_real_singleton_eq_zero (hα : 0 < α) (h : r ∉ ⟦w⟧ᴹ) :
    (speaker M α r).real {w} = 0 :=
  RSA.speaker_listener_truthful_dirac_real_singleton_eq_zero hα _ _ _ h

theorem speaker_real_singleton_pos (hα : 0 ≤ α) (h : r ∈ ⟦w⟧ᴹ) : 0 < (speaker M α r).real {w} :=
  ENNReal.toReal_pos (RSA.speaker_dirac_apply_singleton_ne_zero hα
    ((RSA.listener_truthful_apply_singleton_ne_zero_iff _ _ _ _).2
      ⟨h, uniformOn_univ_singleton_ne_zero _⟩)) (measure_ne_top _ _)

variable [DecidableEq E]

theorem literal_apply_singleton (w : Word C S) (r : E) :
    literal M w {r} = if r ∈ ⟦w⟧ᴹ then (⟦w⟧ᴹ.card : ℝ≥0∞)⁻¹ else 0 :=
  RSA.listener_uniformOn_truthful_apply_singleton _ w r

/-- By the size principle, of two words true of an object the speaker prefers the one with the
smaller extension. -/
theorem size_principle (hα : 0 < α) (h₁ : r ∈ ⟦w₁⟧ᴹ) (h₂ : r ∈ ⟦w₂⟧ᴹ)
    (h : ⟦w₂⟧ᴹ.card < ⟦w₁⟧ᴹ.card) : (speaker M α r).real {w₁} < (speaker M α r).real {w₂} :=
  RSA.speaker_uniformOn_dirac_real_singleton_lt_of_card_lt _ hα h₁ h₂ h

/-- Of two objects a word is true of, the speaker uses the word more for the one whose other
feature more objects share, the object whose alternative word is the less informative. -/
theorem speaker_real_singleton_lt_iff (hα : 0 < α) (h : r ∈ ⟦w⟧ᴹ) (h' : r' ∈ ⟦w⟧ᴹ)
    {b : Attribute} (hb : b ≠ w.1) :
    (speaker M α r').real {w} < (speaker M α r).real {w} ↔
      ⟦(⟨b, M r' b⟩ : Word C S)⟧ᴹ.card < ⟦(⟨b, M r b⟩ : Word C S)⟧ᴹ.card := by
  have hpos (x : E) (a : Attribute) : 0 < ⟦(⟨a, M x a⟩ : Word C S)⟧ᴹ.card :=
    Finset.card_pos.2 ⟨x, (mem_denote M).2 rfl⟩
  have hlt (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      ((m : ℝ≥0∞)⁻¹ ^ α < (n : ℝ≥0∞)⁻¹ ^ α) ↔ n < m := by
    rw [ENNReal.rpow_lt_rpow_iff hα, ENNReal.inv_lt_inv, Nat.cast_lt]
  have htop (n : ℕ) (hn : 0 < n) : (n : ℝ≥0∞)⁻¹ ^ α ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hα.le
      (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn.ne'))
  have hw : 0 < ⟦w⟧ᴹ.card := Finset.card_pos.2 ⟨r, h⟩
  rw [speaker, literal, RSA.speaker_uniformOn_dirac_real_singleton_lt_iff_invPowSum
    (fun w : Word C S ↦ ⟦w⟧ᴹ) hα h h', profile_eq, profile_eq]
  obtain ⟨a, v⟩ := w
  rw [mem_denote] at h h'
  simp only at h h' hb
  cases a <;> cases b <;> try exact absurd rfl hb
  · simp only [h, h', Multiset.insert_eq_cons, Multiset.invPowSum_cons,
      Multiset.invPowSum_singleton]
    rw [ENNReal.add_lt_add_iff_left (htop _ hw), hlt _ _ (hpos r .shape) (hpos r' .shape)]
  · simp only [h, h', Multiset.insert_eq_cons, Multiset.invPowSum_cons,
      Multiset.invPowSum_singleton]
    rw [ENNReal.add_lt_add_iff_right (htop _ hw), hlt _ _ (hpos r .colour) (hpos r' .colour)]

/-- A listener with no prior preference between two objects a word is true of infers the one
whose other feature more objects share, since for the other object the speaker had a more
informative word. -/
theorem listener_real_singleton_lt_iff (hα : 0 < α) (P : Measure E) [IsFiniteMeasure P]
    (h : r ∈ ⟦w⟧ᴹ) (h' : r' ∈ ⟦w⟧ᴹ) (hP : P {r'} = P {r}) (hP0 : P {r} ≠ 0) {b : Attribute}
    (hb : b ≠ w.1) :
    (listener M P α w).real {r'} < (listener M P α w).real {r} ↔
      ⟦(⟨b, M r' b⟩ : Word C S)⟧ᴹ.card < ⟦(⟨b, M r b⟩ : Word C S)⟧ᴹ.card := by
  rw [listener, RSA.listener_real_singleton_lt_iff, measureReal_def, measureReal_def P, hP,
    mul_lt_mul_iff_right₀ (ENNReal.toReal_pos hP0 (measure_ne_top _ _)),
    speaker_real_singleton_lt_iff M hα h h' hb]

end Model

/-! ### The context of the figure (Figure 1A) -/

/-- The colours. -/
inductive Colour
  | blue | green
  deriving DecidableEq, Fintype, Repr

/-- The shapes. -/
inductive Shape
  | square | circle
  deriving DecidableEq, Fintype, Repr

/-- The three objects of the context, the domain of the model. -/
inductive Object
  | blueSquare | blueCircle | greenSquare
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Object := ⊤
instance : DiscreteMeasurableSpace Object := ⟨fun _ ↦ trivial⟩

/-- The model `M` gives each object of its domain its colour and its shape. -/
def M : Object → (a : Attribute) → a.Value Colour Shape
  | .blueSquare, .colour => Colour.blue
  | .blueSquare, .shape => Shape.square
  | .blueCircle, .colour => Colour.blue
  | .blueCircle, .shape => Shape.circle
  | .greenSquare, .colour => Colour.green
  | .greenSquare, .shape => Shape.square

namespace Word

/-- The word *blue*. -/
abbrev blue : Word Colour Shape := ⟨.colour, Colour.blue⟩

/-- The word *green*. -/
abbrev green : Word Colour Shape := ⟨.colour, Colour.green⟩

/-- The word *square*. -/
abbrev square : Word Colour Shape := ⟨.shape, Shape.square⟩

/-- The word *circle*. -/
abbrev circle : Word Colour Shape := ⟨.shape, Shape.circle⟩

end Word

variable {α : ℝ}

/-- For the blue circle the speaker prefers *circle*, which identifies it, to the ambiguous
*blue*. -/
theorem prefers_informative (hα : 0 < α) :
    (speaker M α .blueCircle).real {.blue} < (speaker M α .blueCircle).real {.circle} :=
  size_principle M hα (by decide) (by decide) (by decide)

/-- *Blue* is used less for the blue circle, where *circle* competes, than for the blue square,
where the only competitor is as ambiguous. -/
theorem narrowing_blue (hα : 0 < α) :
    (speaker M α .blueCircle).real {.blue} < (speaker M α .blueSquare).real {.blue} :=
  (speaker_real_singleton_lt_iff M hα (by decide) (by decide) (b := .shape) (by decide)).2
    (by decide)

theorem narrowing_square (hα : 0 < α) :
    (speaker M α .greenSquare).real {.square} < (speaker M α .blueSquare).real {.square} :=
  (speaker_real_singleton_lt_iff M hα (by decide) (by decide) (b := .colour) (by decide)).2
    (by decide)

/-- A listener with a uniform prior who hears *blue* favours the blue square over the blue
circle. -/
theorem listener_narrows_blue (hα : 0 < α) :
    (listener M Measure.count α .blue).real {.blueCircle} <
      (listener M Measure.count α .blue).real {.blueSquare} :=
  (listener_real_singleton_lt_iff M hα Measure.count (by decide) (by decide) (by simp) (by simp)
    (b := .shape) (by decide)).2 (by decide)

theorem unique_green (hα : 0 < α) :
    (speaker M α .blueSquare).real {.green} < (speaker M α .greenSquare).real {.green} := by
  rw [speaker_real_singleton_eq_zero M hα (by decide)]
  exact speaker_real_singleton_pos M hα.le (by decide)

theorem unique_circle (hα : 0 < α) :
    (speaker M α .blueSquare).real {.circle} < (speaker M α .blueCircle).real {.circle} := by
  rw [speaker_real_singleton_eq_zero M hα (by decide)]
  exact speaker_real_singleton_pos M hα.le (by decide)

theorem fully_rational_picks_circle :
    Filter.Tendsto (fun α ↦ (speaker M α .blueCircle).real {.circle}) Filter.atTop (𝓝 1) := by
  refine RSA.tendsto_speaker_dirac_real_singleton_atTop ?_ fun u hu ↦ ?_
  · exact (RSA.listener_truthful_apply_singleton_ne_zero_iff _ _ _ _).2
      ⟨by decide, uniformOn_univ_singleton_ne_zero _⟩
  · simp only [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one]
    rw [← measureReal_def, ← measureReal_def, literal,
      RSA.listener_uniformOn_truthful_real_singleton,
      RSA.listener_uniformOn_truthful_real_singleton]
    have h1 : ⟦Word.circle⟧ᴹ.card = 1 := by decide
    have h2 : ⟦Word.blue⟧ᴹ.card = 2 := by decide
    obtain ⟨a, v⟩ := u
    cases a <;> cases v <;> first | exact absurd rfl hu | simp +decide [h1, h2]
    all_goals norm_num

end FrankGoodman2012
