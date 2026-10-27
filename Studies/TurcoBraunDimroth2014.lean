module

public import Linglib.Semantics.Focus.Marking
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Fragments.Dutch.Particles
public import Linglib.Fragments.German.Particles
public import Linglib.Data.Examples.TurcoBraunDimroth2014

/-!
# Turco, Braun and Dimroth (2014): When Contrasting Polarity, the Dutch Use Particles, Germans Intonation

Turco, Braun and Dimroth study how Dutch and German speakers mark a switch from a negative to a
positive claim in two discourse contexts. In a polarity contrast, (1), the positive claim is about
a different topic situation, in Klein's sense, than the negative one, so the two claims are
compatible; in a polarity correction, (2), it is about the same topic situation, so they exclude
each other. These are Umbach's contrast and correction. German speakers produced Höhle's Verum
focus, a high-falling pitch accent on the finite verb, and never a sentence-internal affirmative
particle, whereas Dutch speakers mostly produced the accented affirmative particle *wel*
(`Dutch.Particles.wel`). The paper's claim is that the two devices are functionally equivalent
but operate on different levels. A sentence contains a polarity operator and, above it, an
assertion operator carried by the finite verb; *wel* is the overt affirmative value of the
polarity operator, the counterpart of *niet*, as Sudhoff has it, whereas Verum focus marks the
assertion operator. An overt polarity value fixes the polarity of its sentence, so *wel* cannot
occur in a negated sentence while Verum focus can, which is why the assertion operator takes
effect above polarity, as in Blühdorn. The paper sets this against Sudhoff, for whom focus on
*wel* is itself an instance of Verum focus: that the two devices do the same work does not put
them on the same level.

## Main definitions

* `Sentence`: a property of a topic situation, asserted through a polarity operator
  (`Sentence.polarityOp`) and an assertion operator that Verum focus marks
  (`Sentence.verumFocus`).
* `Switch`, `IsContrast`, `IsCorrection`: a negative claim followed by a positive one, about a
  different or the same topic situation.

## Implementation notes

The polarity operator is a single slot of the sentence holding its overt value, if any, with
unmarked affirmation as the default, so a sentence with the affirmative particle is positive by
construction and *Het kind heeft wel niet gehuild* is not a `Sentence`.
The production results are not formalized. Dutch speakers used *wel* in most utterances of both
contexts, fewer in correction, an effect the paper leaves unexplained, and Verum focus never in
contrast and rarely in correction; German speakers used Verum focus in more than 70% of the
utterances of both contexts and never a sentence-internal particle. In correction only, some
German speakers produced the polarity particle *doch*, `German.PolarityParticles.doch`, as a
separate utterance before a Verum focus utterance; the paper codes the combination as another
realization, not an affirmative particle, since *doch* never carried the correction by
itself. *Wel* was mostly accented, as a downstepped fall in
contrast and as a fall in correction, and the pitch range of German Verum focus was larger in
correction than in contrast; the paper attributes the greater prominence of correction either to
the strength of undoing a denial, as Hogeweg has it, or to the absence of a contrastive topic accent
before the comment. The examples are the rows of `Data.Examples.TurcoBraunDimroth2014`.

## References

* [turco-braun-dimroth-2014]
* [umbach-2004]
* [klein-2008]
* [hohle-1992]
* [sudhoff-2012]
* [bluhdorn-2012]
* [hogeweg-2009]
* [hogeweg-2009]
* [dimroth-etal-2010]
-/

@[expose] public section

namespace TurcoBraunDimroth2014

/-! ### The polarity operator and the assertion operator -/

/-- A sentence predicates a descriptive property, given per topic situation as the set of worlds
where it holds there, of a topic situation, through a polarity operator and, above it, the
assertion operator carried by the finite verb, which Verum focus accents. -/
structure Sentence (S W : Type*) where
  property : S → Set W
  situation : S
  /-- The overt value of the polarity operator: negation, or an affirmative particle such as
  Dutch *wel*; `none` when affirmation is unmarked. -/
  polarityOp : Option Polarity
  /-- The mark on the assertion operator, F-marked under Verum focus. -/
  verumFocus : Focus.Mark

variable {S W : Type*}

namespace Sentence

/-- The polarity of a sentence, the value of its polarity operator, positive by default. -/
def pol (s : Sentence S W) : Polarity := s.polarityOp.getD .positive

/-- The proposition a sentence asserts. -/
def denotation (s : Sentence S W) : Set W := s.pol • s.property s.situation

/-- Accenting the assertion operator leaves the truth conditions unchanged. -/
theorem denotation_verumFocus (s : Sentence S W) (m : Focus.Mark) :
    { s with verumFocus := m }.denotation = s.denotation := rfl

/-- An overt affirmative particle leaves the truth conditions of the unmarked affirmative
sentence unchanged: *wel* and Verum focus are functionally equivalent on a positive sentence. -/
theorem denotation_affirmation (s : Sentence S W) :
    { s with polarityOp := some .positive }.denotation =
      { s with polarityOp := none }.denotation := rfl

/-- An overt value of the polarity operator is the polarity of the sentence: a sentence with
the affirmative particle is positive, so the particle cannot occur in a negated sentence. -/
theorem pol_of_polarityOp_eq_some {s : Sentence S W} {p : Polarity} (h : s.polarityOp = some p) :
    s.pol = p := by
  simp only [pol, h, Option.getD_some]

/-- Verum focus can occur in a negated sentence, *Das Kind HAT nicht geweint*. -/
theorem exists_verumFocus_negative [Nonempty S] :
    ∃ s : Sentence S W, s.verumFocus = .focused ∧ s.pol = .negative :=
  ⟨⟨fun _ ↦ ∅, Classical.arbitrary S, some .negative, .focused⟩, rfl, rfl⟩

end Sentence

/-! ### Polarity contrast and polarity correction -/

/-- A polarity switch from `a` to `b` is a negative claim followed by a positive claim of the
same descriptive property. -/
def Switch (a b : Sentence S W) : Prop :=
  a.property = b.property ∧ a.pol = .negative ∧ b.pol = .positive

/-- A polarity contrast is a switch between claims about different topic situations. -/
def IsContrast (a b : Sentence S W) : Prop := Switch a b ∧ a.situation ≠ b.situation

/-- A polarity correction is a switch between claims about the same topic situation. -/
def IsCorrection (a b : Sentence S W) : Prop := Switch a b ∧ a.situation = b.situation

/-- The claims of a switch exclude each other exactly when the property's holding of the second
topic situation entails its holding of the first. -/
theorem Switch.disjoint_iff {a b : Sentence S W} (h : Switch a b) :
    Disjoint a.denotation b.denotation ↔ b.property b.situation ⊆ a.property a.situation := by
  obtain ⟨hP, ha, hb⟩ := h
  simp only [Sentence.denotation, ha, hb, hP, Polarity.negative_smul_set, Polarity.positive_smul,
    Set.disjoint_compl_left_iff_subset]

/-- The claims of a correction exclude each other. -/
theorem IsCorrection.disjoint {a b : Sentence S W} (h : IsCorrection a b) :
    Disjoint a.denotation b.denotation :=
  h.1.disjoint_iff.2 (by rw [h.1.1, h.2])

/-- The claims of a contrast need not exclude each other: any two topic situations carry a
contrast whose claims are jointly true. -/
theorem exists_isContrast_not_disjoint [Nonempty W] {s₁ s₂ : S} (h : s₁ ≠ s₂) :
    ∃ a b : Sentence S W, IsContrast a b ∧ ¬ Disjoint a.denotation b.denotation := by
  refine ⟨⟨fun s ↦ {_w | s = s₂}, s₁, some .negative, .unfeatured⟩,
    ⟨fun s ↦ {_w | s = s₂}, s₂, none, .unfeatured⟩, ⟨⟨rfl, rfl, rfl⟩, h⟩, ?_⟩
  exact Set.not_disjoint_iff.2 ⟨Classical.arbitrary W, h, rfl⟩

end TurcoBraunDimroth2014
