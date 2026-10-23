module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Logic.Natural.ImplicationSignature

/-!
# Implicative verbs

Karttunen analyzes an implicative sentence as a presupposition–proposition pair: it asserts the
proposition `v(S)` and presupposes that `v(S)` is a condition for the complement, so that what it
implies about the complement follows from the assertion or from its denial. The condition is read
off the implication signature (`NaturalLogic.ImplicationSignature`): a verb implying a complement in
a positive context presupposes `v(S)` sufficient for it, and one implying a complement in a negative
context presupposes `v(S)` necessary for the complement's negation. Here the conditions are read
through any relations of sufficiency and necessity that are sound for truth at a world
(`Implicative.Interpretation`), Karttunen's own interpretation being the material conditional at the
world (`Implicative.Interpretation.material`), and under every interpretation an implicative
sentence implies what its signature says.

## Main definitions

* `Implicative.Interpretation`: relations of sufficiency and necessity between facts, sound at
  worlds
* `Implicative.sentence`: the trivalent proposition of a verb with a given implication
  signature, undefined where its presupposition fails

## Main results

* `Implicative.holds_signed_of_implied_eq`: an affirmed or denied claim implies the polarity of
  the complement that its signature records for that context
* `Implicative.antitone_support`: a signature that implies more presupposes more

## References

* [karttunen-1971]
-/

@[expose] public section

open Presupposition NaturalLogic

namespace Implicative

/-- An interpretation of sufficiency and necessity between facts `F` that is sound for truth at the
worlds `W`. A fact sufficient for another at a world makes it true there when it is true, and a fact
necessary for another is true there when the other is. -/
structure Interpretation (F W : Type*) where
  /-- The fact holds at the world. -/
  Holds : F → W → Prop
  /-- The negation of a fact. -/
  neg : F → F
  holds_neg (a : F) (w : W) : Holds (neg a) w ↔ ¬ Holds a w
  /-- The first fact is sufficient for the second at the world. -/
  Sufficient : F → F → W → Prop
  /-- The first fact is necessary for the second at the world. -/
  Necessary : F → F → W → Prop
  holds_of_sufficient {a b : F} {w : W} : Sufficient a b w → Holds a w → Holds b w
  holds_of_necessary {a b : F} {w : W} : Necessary a b w → Holds b w → Holds a w

namespace Interpretation

/-- Karttunen's interpretation takes facts to be propositions and a condition to be the material
conditional at the world. -/
def material (W : Type*) : Interpretation (W → Prop) W where
  Holds a w := a w
  neg a w := ¬ a w
  holds_neg _ _ := Iff.rfl
  Sufficient a b w := a w → b w
  Necessary a b w := b w → a w
  holds_of_sufficient h := h
  holds_of_necessary h := h

variable {F W : Type*} (R : Interpretation F W)

/-- A fact or its negation, by polarity. -/
def signed : Polarity → F → F
  | .positive, a => a
  | .negative, a => R.neg a

variable {R}

theorem holds_signed_negative_mul {q : Polarity} {a : F} {w : W} :
    R.Holds (R.signed (.negative * q) a) w ↔ ¬ R.Holds (R.signed q a) w := by
  cases q
  · exact R.holds_neg a w
  · show R.Holds a w ↔ ¬ R.Holds (R.neg a) w
    rw [R.holds_neg]; exact not_not.symm

end Interpretation

variable {F W : Type*} (R : Interpretation F W)

open Classical in
/-- The sentence of a verb with implication signature `s`, asserted proposition `v` and embedded
fact `S`. It presupposes that `v` is sufficient for the complement `s` implies in a positive
context and necessary for the negation of the complement it implies in a negative context, and it
asserts `v`. -/
noncomputable def sentence (s : ImplicationSignature) (v S : F) : W → SignType :=
  {w | (∀ q : Polarity, s.positive = q → R.Sufficient v (R.signed q S) w) ∧
    ∀ q : Polarity, s.negative = q → R.Necessary v (R.signed (.negative * q) S) w}.indicator
    fun w ↦ SignType.ofProp (R.Holds v w)

variable {R} {s : ImplicationSignature} {v S : F} {w : W}

theorem holds_signed_of_implied_eq {m q : Polarity} (hq : s.implied m = q)
    (hs : (m • sentence R s v S) w = 1) : R.Holds (R.signed q S) w := by
  cases m
  · simp only [Pi.smul_apply, Polarity.positive_smul, sentence,
      Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq, SignType.ofProp_eq_one_iff] at hs
    exact R.holds_of_sufficient (hs.1.1 q hq) hs.2
  · simp only [Pi.smul_apply, Polarity.negative_smul_signType, SignType.neg_eq_one_iff, sentence,
      Trivalent.indicator_apply_eq_neg_one_iff, Set.mem_ofPred_eq,
      SignType.ofProp_eq_neg_one_iff] at hs
    by_contra h
    exact hs.2 (R.holds_of_necessary (hs.1.2 q hq) (Interpretation.holds_signed_negative_mul.2 h))

variable (R v S) in
theorem antitone_support : Antitone fun s ↦ Function.support (sentence R s v S) := by
  intro s t h w hw
  simp only [sentence, Function.mem_support, ne_eq, Set.indicator_apply_eq_zero,
    SignType.ofProp_ne_zero, imp_false, not_not, Set.mem_ofPred_eq] at hw ⊢
  obtain ⟨hp, hn⟩ := hw
  have hst := ImplicationSignature.le_iff.1 h
  exact ⟨fun q hq ↦ hp q (Flat.coe_le_iff.1 (hq ▸ hst.1)),
    fun q hq ↦ hn q (Flat.coe_le_iff.1 (hq ▸ hst.2))⟩

end Implicative
