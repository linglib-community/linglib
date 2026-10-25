module

public import Linglib.Discourse.Centering.Basic
public import Mathlib.Data.List.Zip
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WithBot

/-!
# Centering theory: transitions

The transition from one utterance to the next is classified by two tests on the backward-looking
center of the second: whether it is the backward-looking center of the first, or the first has
none, and whether it is the preferred center of the second. Kibble calls the tests *cohesion* and
*salience*. Brennan, Friedman, and Pollard's four transitions, named continue, retain, smooth
shift, and rough shift by Walker, Iida, and Cote, are the four outcomes of the two tests; Grosz,
Joshi, and Weinstein's three, continuation, retaining, and shifting, do not apply the second test
to a shift. Rule 2 orders the transitions by the first test and then by the second.

## Main declarations

* `Discourse.Centering.ExtendedTransition`: the four transitions, ordered lexicographically by
  their outcomes on the two tests, `cohesion` and `salience`.
* `Discourse.Centering.Transition`: the three transitions; `ExtendedTransition.toTransition`
  merges the two shifts and is monotone.
* `ExtendedTransition.ofCenters`, `Transition.ofCenters`: the transition determined by the prior
  backward-looking center, the current one, and the current preferred center.
* `Discourse.Centering.cbs`, `transitions`: the centers and transitions along a discourse.

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

/-- The outcome of the second test on a transition whose center is kept, `⊥` on a shift. -/
def salience : Transition → WithBot Bool
  | continuation => (true : Bool)
  | retaining => (false : Bool)
  | shifting => ⊥

/-- Rule 2: continuation, then retaining, then shifting. -/
instance : LinearOrder Transition :=
  LinearOrder.lift' salience fun a b h ↦ by cases a <;> cases b <;> cases h <;> rfl

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

/-- Rule 2: the order by the first test and then by the second. -/
instance : LinearOrder ExtendedTransition :=
  LinearOrder.lift' (fun t ↦ toLex (t.cohesion, t.salience)) fun _ _ h ↦
    have h := Prod.ext_iff.mp (toLex.injective h); ext h.1 h.2

theorem lt_iff_toLex_lt {t t' : ExtendedTransition} :
    t < t' ↔ toLex (t.cohesion, t.salience) < toLex (t'.cohesion, t'.salience) := Iff.rfl

/-- The transition of Grosz, Joshi, and Weinstein that a transition refines. -/
def toTransition : ExtendedTransition → Transition
  | .continue => .continuation
  | .retain => .retaining
  | .smoothShift | .roughShift => .shifting

theorem toTransition_mono : Monotone toTransition := by
  intro a b; cases a <;> cases b <;> decide

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

/-! ### Scanning a discourse -/

variable {R : Type*} [LinearOrder R]

/-- The transition into `cur` from `prev`, given the backward-looking center of `prev`. -/
def transition (prevCb : Option E) (prev cur : Utterance E R) : Transition :=
  .ofCenters prevCb (cb prev cur) cur.cp

/-- The backward-looking center of each utterance of `d` after the first. -/
def cbs (d : List (Utterance E R)) : List (Option E) := List.zipWith cb d d.tail

/-- The transition into each utterance of `d` after the first, the first of them with no prior
center. -/
def transitions (d : List (Utterance E R)) : List Transition :=
  List.zipWith3 transition (none :: cbs d) d d.tail

@[simp] theorem cbs_nil : cbs ([] : List (Utterance E R)) = [] := rfl

@[simp] theorem cbs_singleton (u : Utterance E R) : cbs [u] = [] := rfl

@[simp] theorem cbs_cons_cons (u₁ u₂ : Utterance E R) (d : List (Utterance E R)) :
    cbs (u₁ :: u₂ :: d) = cb u₁ u₂ :: cbs (u₂ :: d) := rfl

@[simp] theorem length_cbs (d : List (Utterance E R)) : (cbs d).length = d.length - 1 := by
  simp [cbs, List.length_zipWith]

@[simp] theorem transitions_nil : transitions ([] : List (Utterance E R)) = [] := rfl

@[simp] theorem transitions_singleton (u : Utterance E R) : transitions [u] = [] := rfl

@[simp] theorem length_transitions (d : List (Utterance E R)) :
    (transitions d).length = d.length - 1 := by
  rw [transitions, ← List.zipWith_zipWith_left (fun (f : Utterance E R → Transition) ↦ f)
    transition]
  simp [List.length_zipWith]

end Discourse.Centering
