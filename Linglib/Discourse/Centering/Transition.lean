module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WithBot

/-!
# Centering theory: transitions

This file defines the transitions of centering theory. The transition from one utterance to the
next is classified by two tests on the backward-looking center of the second: whether it is the
backward-looking center of the first, or the first has none, and whether it is the preferred
center of the second. Kibble calls the tests *cohesion* and *salience*. Brennan, Friedman, and
Pollard's four transitions, named continue, retain, smooth shift, and rough shift by Walker, Iida,
and Cote, are the four outcomes of the two tests; Grosz, Joshi, and Weinstein's three,
continuation, retaining, and shifting, merge the two shifts, and the merging map
`ExtendedTransition.toTransition` is monotone (`ExtendedTransition.toTransition_mono`). Rule 2
orders the transitions by the first test and then by the second
(`ExtendedTransition.toLexIso`).

## Implementation notes

Grosz, Joshi, and Weinstein state Rule 2 on sequences of transitions; the orders here are its
restriction to single transitions, as Brennan, Friedman, and Pollard state it, and a study
compares sequences pointwise.

The first test passes when there is no prior center: Walker, Iida, and Cote treat the center of a
segment's first utterance as a variable bound to the center of the second, so the second continues
or retains. An utterance with no backward-looking center has no extended transition, as Poesio
and colleagues note of the four-way table; `Transition.ofCenters` counts it as shifting.

## References

* [grosz-joshi-weinstein-1995]
* [brennan-friedman-pollard-1987]
* [walker-iida-cote-1994]
* [kibble-2001]
* [poesio-stevenson-eugenio-hitzeman-2004]
-/

@[expose] public section

namespace Discourse.Centering

/-! ### Transitions and Rule 2 -/

/-- The transitions of Grosz, Joshi, and Weinstein. -/
inductive Transition where
  | continuation
  | retaining
  | shifting
  deriving DecidableEq, Repr

namespace Transition

/-- A transition as the outcome of the second test where the center is kept, and `⊥` on a
shift. -/
def salienceEquiv : Transition ≃ WithBot Bool where
  toFun
    | continuation => (true : Bool)
    | retaining => (false : Bool)
    | shifting => ⊥
  invFun
    | some true => continuation
    | some false => retaining
    | none => shifting
  left_inv t := by cases t <;> rfl
  right_inv b := by rcases b with _ | _ | _ <;> rfl

/-- Rule 2: continuation, then retaining, then shifting. -/
instance : LinearOrder Transition := LinearOrder.lift' salienceEquiv salienceEquiv.injective

/-- The transitions in the order of Rule 2 are `WithBot Bool`. -/
def salienceIso : Transition ≃o WithBot Bool := ⟨salienceEquiv, Iff.rfl⟩

@[simp] theorem salienceIso_continuation : salienceIso continuation = (true : Bool) := rfl

@[simp] theorem salienceIso_retaining : salienceIso retaining = (false : Bool) := rfl

@[simp] theorem salienceIso_shifting : salienceIso shifting = ⊥ := rfl

end Transition

/-- The transitions of Brennan, Friedman, and Pollard's extended table. -/
inductive ExtendedTransition where
  | continue
  | retain
  | smoothShift
  | roughShift
  deriving DecidableEq, Repr

namespace ExtendedTransition

/-- Whether the center of a transition is kept: the first test. -/
def cohesion : ExtendedTransition → Bool
  | .continue | .retain => true
  | .smoothShift | .roughShift => false

/-- Whether the center of a transition is the preferred center: the second test. -/
def salience : ExtendedTransition → Bool
  | .continue | .smoothShift => true
  | .retain | .roughShift => false

@[ext] theorem ext {t t' : ExtendedTransition} (hc : t.cohesion = t'.cohesion)
    (hs : t.salience = t'.salience) : t = t' := by
  cases t <;> cases t' <;> simp_all [cohesion, salience]

/-- The transition on which the first test comes out `c` and the second `s`. -/
def ofTests (c s : Prop) [Decidable c] [Decidable s] : ExtendedTransition :=
  if c then if s then .continue else .retain else if s then .smoothShift else .roughShift

section ofTests

variable (c s : Prop) [Decidable c] [Decidable s]

@[simp] theorem cohesion_ofTests : (ofTests c s).cohesion = decide c := by
  unfold ofTests; split_ifs <;> simp_all [cohesion]

@[simp] theorem salience_ofTests : (ofTests c s).salience = decide s := by
  unfold ofTests; split_ifs <;> simp_all [salience]

end ofTests

/-- A transition as the outcomes of the two tests. -/
def testsEquiv : ExtendedTransition ≃ Bool × Bool where
  toFun t := (t.cohesion, t.salience)
  invFun p := ofTests (p.1 = true) (p.2 = true)
  left_inv t := by cases t <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> rfl

/-- Rule 2: the order by the first test and then by the second. -/
instance : LinearOrder ExtendedTransition :=
  LinearOrder.lift' (toLex ∘ testsEquiv) (toLex.injective.comp testsEquiv.injective)

/-- The transitions in the order of Rule 2 are the pairs of outcomes of the two tests in
lexicographic order. -/
def toLexIso : ExtendedTransition ≃o Bool ×ₗ Bool := ⟨testsEquiv.trans toLex, Iff.rfl⟩

@[simp] theorem toLexIso_apply (t : ExtendedTransition) :
    toLexIso t = toLex (t.cohesion, t.salience) := rfl

/-- The transition of Grosz, Joshi, and Weinstein that a transition refines. -/
def toTransition : ExtendedTransition → Transition
  | .continue => .continuation
  | .retain => .retaining
  | .smoothShift | .roughShift => .shifting

theorem toTransition_mono : Monotone toTransition := by
  intro a b; cases a <;> cases b <;> decide

/-- `toTransition` as an order homomorphism. -/
def toTransitionHom : ExtendedTransition →o Transition := ⟨toTransition, toTransition_mono⟩

@[simp] theorem coe_toTransitionHom : ⇑toTransitionHom = toTransition := rfl

/-- Through the two order isomorphisms, `toTransition` keeps the outcome of the second test
where the first passes and forgets it where the first fails. -/
theorem salienceIso_toTransition (t : ExtendedTransition) :
    Transition.salienceIso t.toTransition =
      if t.cohesion then (t.salience : WithBot Bool) else ⊥ := by
  cases t <;> rfl

end ExtendedTransition

/-! ### Transitions from centers -/

variable {E : Type*} [DecidableEq E]

/-- The transition into an utterance with backward-looking center `c` and preferred center `cp`,
after one with backward-looking center `prevCb`. -/
def ExtendedTransition.ofCenters (prevCb : Option E) (c : E) (cp : Option E) :
    ExtendedTransition :=
  ofTests (∀ p ∈ prevCb, p = c) (cp = some c)

/-- The transition into an utterance with backward-looking center `cb` and preferred center `cp`,
after one with backward-looking center `prevCb`, shifting if `cb` is undefined. -/
def Transition.ofCenters (prevCb : Option E) : Option E → Option E → Transition
  | none, _ => .shifting
  | some c, cp => (ExtendedTransition.ofCenters prevCb c cp).toTransition

namespace Transition

@[simp] theorem ofCenters_none (prevCb cp : Option E) : ofCenters prevCb none cp = .shifting :=
  rfl

/-- The transitions of [grosz-joshi-weinstein-1995]: the center is kept, and is the preferred
center or not, or it changes. -/
theorem ofCenters_some (prevCb cp : Option E) (c : E) : ofCenters prevCb (some c) cp =
    if ∀ p ∈ prevCb, p = c then if cp = some c then continuation else retaining
    else shifting := by
  simp only [ofCenters, ExtendedTransition.ofCenters, ExtendedTransition.ofTests]
  split_ifs <;> rfl

end Transition

end Discourse.Centering
