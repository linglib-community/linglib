module

public import Studies.Cohen1999

/-!
# Cohen (2013): No quantification without reinterpretation

A generic or habitual sentence contains no audible quantifier, so the hearer must
introduce one by reinterpreting the quantifierless input, and the introducing device —
not a phonologically null determiner — fixes the quantifier's scope. Generics arise by
Nunberg's Predicate Transfer: when predicating a property of a kind makes no pragmatic
sense, the predicate is transferred to one true of a kind whose instances generically
bear it. Pragmatic triggering leaves the transfer free to apply at any level of
composition, after Nunberg and Recanati, so "Storks have a favorite nesting area" is
scopally ambiguous — transfer of the verb leaves the generic under the existential,
transfer of the whole phrase puts it above (§13.4.1) — though never out of an opaque
context, since transfer needs the property's intension. Habituals arise by a type-shift:
an eventive verb is evaluated at intervals while the present tense supplies a moment
(after Taylor and Dowty), and the shift γ resolves the mismatch at the verb, before the
object composes, so "Mary smokes a cigarette" keeps the generic under the existential and
is odd, while the brand variant is fine (§13.4.2). That a type-shift applies only at its
trigger site is argued from Partee and Rooth's SHIFT: negating a shifted verb differs
from shifting a negated one, and only the first order is attested (§13.3.1, after the
conjunction *needed but didn't buy*).
Scope alone also does not exhaust the generic–negation interaction: focus fixes the
alternative set of Cohen's earlier generic quantifier, so "Cows do not eat [nettles]"
generalizes with exceptions while "Cows do [not] eat nettles" denies that any cow eats
them (§13.2.1).

We state the two devices with the generic quantifier of `Studies/Cohen1999.lean` in the
transferred and shifted predicates, derive both scopes of the storks sentence from the
transfer's freedom of level and the infelicity of the cigarette sentence from the shift's
locality, and check the focus readings of the nettles sentence against the two
alternative sets.

## Implementation notes

The generic quantifier inside the reinterpretation operators is the absolute reading
with trivial alternatives, per the chapter's own pointer to Cohen's earlier work for its
content. Kinds are `Unit`, individuals and intervals `Fin n`; a felicity judgment is
derived as the absence of a true reading among the available ones.

## TODO

* Bare plurals under habituals ((18): gen above the existential only) follow from bare
  plurals introducing no discourse referent, a duplex condition under an existential
  being no well-formed DRS (after Cohen and Erteschik-Shir); this needs the DRT box
  substrate.
* Predicate Transfer's ban on scoping out of opaque contexts (§13.4.1) rests on its need
  for the property's intension, which these extensional models cannot state.
* The wide-scope generic objects of (19)–(20), which refute a syntactic account
  (§13.2.3), presuppose a subject–object asymmetry not encoded here.

## References

* [A. Cohen, *No Quantification without Reinterpretation* (2013)][cohen-2013]
* [G. Nunberg, *Transfers of Meaning* (1995)][nunberg-1995]
* [B. Partee and M. Rooth, *Generalized Conjunction and Type Ambiguity*
  (1983)][partee-rooth-1983]
* [A. Cohen, *Think Generic! The Meaning and Use of Generic Sentences*
  (1999)][cohen-1999a]
* [G. N. Carlson, *Reference to Kinds in English* (1977)][carlson-1977a]
* [M. Krifka, F. J. Pelletier, G. N. Carlson, A. ter Meulen, G. Chierchia and G. Link,
  *Genericity: An Introduction* (1995)][krifka-etal-1995]
* [A. Cohen and N. Erteschik-Shir, *Topic, Focus, and the Interpretation of Bare
  Plurals* (2002)][cohen-erteschik-shir-2002]
* [F. Recanati, *Embedded Implicatures* (2003)][recanati-2003]
* [B. Taylor, *Tense and Continuity* (1977)][taylor-1977]
* [D. R. Dowty, *Word Meaning and Montague Grammar* (1979)][dowty-1979]
-/

@[expose] public section

namespace Cohen2013

open Quantifier Quantifier.GQ

/-! ### The two reinterpretation devices (§13.3) -/

/-- Partee and Rooth's SHIFT, lifting an extensional transitive verb to take a
quantifier object. -/
def SHIFT {E : Type*} (V : E → E → Prop) : ((E → Prop) → Prop) → E → Prop :=
  fun Q x ↦ Q (fun y ↦ V x y)

/-- Negating a shifted verb differs from shifting the negated verb, and only the first order is
attested (25). -/
theorem not_shift_ne_shift_not :
    ∃ (V : Bool → Bool → Prop) (Q : (Bool → Prop) → Prop) (x : Bool),
      ¬ (¬ SHIFT V Q x ↔ SHIFT (fun a b ↦ ¬ V a b) Q x) :=
  ⟨fun _ y ↦ y = true, fun P ↦ P true ∨ P false, true, by unfold SHIFT; decide⟩

/-- Predicate Transfer for generics (§13.4.1): a property of individuals becomes the
property of a kind whose instances generically bear it. -/
def transfer {Kind Ind : Type*} [MeasurableSpace Ind] [MeasurableSingletonClass Ind]
    [Fintype Ind] (instanceOf : Ind → Kind → Prop)
    [∀ k, DecidablePred (fun y ↦ instanceOf y k)] (P : Ind → Prop) [DecidablePred P] :
    Kind → Prop :=
  fun k ↦ Cohen1999.gen Finset.univ (fun y ↦ instanceOf y k) (fun _ ↦ True) P

instance {Kind Ind : Type*} [MeasurableSpace Ind] [MeasurableSingletonClass Ind]
    [Fintype Ind] (instanceOf : Ind → Kind → Prop)
    [∀ k, DecidablePred (fun y ↦ instanceOf y k)] (P : Ind → Prop) [DecidablePred P]
    (k : Kind) : Decidable (transfer instanceOf P k) := by
  unfold transfer; infer_instance

/-- The habitual type-shift γ (§13.4.2): a property of intervals becomes the property of
a moment in whose surrounding interval it generically holds. -/
def gamma {Interval Moment : Type*} [MeasurableSpace Interval]
    [MeasurableSingletonClass Interval] [Fintype Interval]
    (containedIn : Interval → Moment → Prop)
    [∀ t, DecidablePred (fun e ↦ containedIn e t)] (P : Interval → Prop)
    [DecidablePred P] : Moment → Prop :=
  fun t ↦ Cohen1999.gen Finset.univ (fun e ↦ containedIn e t) (fun _ ↦ True) P

instance {Interval Moment : Type*} [MeasurableSpace Interval]
    [MeasurableSingletonClass Interval] [Fintype Interval]
    (containedIn : Interval → Moment → Prop)
    [∀ t, DecidablePred (fun e ↦ containedIn e t)] (P : Interval → Prop)
    [DecidablePred P] (t : Moment) : Decidable (gamma containedIn P t) := by
  unfold gamma; infer_instance

/-- A reinterpretation device applies at the mismatching word itself or at the containing
phrase. -/
inductive Level
  | word
  | phrase
  deriving DecidableEq

/-- The two devices that introduce covert quantifiers (§13.3). -/
inductive Device
  | predicateTransfer
  | typeShift
  deriving DecidableEq

/-- Where a device may apply (§13.3): Predicate Transfer is pragmatically triggered and
free to apply at any level; a type-shift fires at the type-mismatch site only. -/
def Device.AppliesAt : Device → Level → Prop
  | .predicateTransfer, _ => True
  | .typeShift, l => l = .word

/-! ### Storks have a favorite nesting area (§13.4.1)

Two storks, each nesting in its own area. Transfer at the verb quantifies each area's
candidate nesters, transfer at the phrase quantifies the storks' own areas: the readings
differ in truth value, and both are available to Predicate Transfer, so the sentence is
scopally ambiguous and true on one reading. -/

/-- Each of two storks nests in its own area. -/
abbrev nestsIn : Fin 2 → Fin 2 → Prop := (· = ·)

/-- Every individual stork instantiates the kind. -/
abbrev storkOf : Fin 2 → Unit → Prop := fun _ _ ↦ True

/-- The two logical forms of the storks sentence, by level of transfer. -/
def storksReading : Level → Prop
  | .word => ∃ a : Fin 2, transfer storkOf (fun s ↦ nestsIn s a) ()
  | .phrase => transfer storkOf (fun s ↦ ∃ a, nestsIn s a) ()

instance : ∀ l, Decidable (storksReading l) := fun l ↦ by
  cases l <;> (unfold storksReading; infer_instance)

theorem storksReading_word_ne_phrase :
    ¬ storksReading .word ∧ storksReading .phrase := by
  constructor <;> decide +kernel

theorem storks_true_reading_available :
    ∃ l, Device.predicateTransfer.AppliesAt l ∧ storksReading l :=
  ⟨.phrase, trivial, storksReading_word_ne_phrase.2⟩

/-! ### Mary smokes a cigarette (§13.4.2)

Three occasions in the interval around the speech moment, a different cigarette each
time. The type mismatch sits at the eventive verb, so γ may apply only there, leaving
the existential above the generic; that sole available reading is false, which is the
oddness of (17a)/(45). The brand variant (17b) is the same shift with a constant
witness, so its narrow reading is true and the sentence is fine. -/

/-- Mary smokes a different cigarette at each of three occasions. -/
abbrev smokes : Fin 3 → Fin 3 → Prop := (· = ·)

/-- Every occasion falls in the interval around the speech moment. -/
abbrev inSpeechInterval : Fin 3 → Unit → Prop := fun _ _ ↦ True

/-- The two logical forms of the cigarette sentence, by level of the shift. -/
def cigaretteReading : Level → Prop
  | .word => ∃ c : Fin 3, gamma inSpeechInterval (fun e ↦ smokes c e) ()
  | .phrase => gamma inSpeechInterval (fun e ↦ ∃ c, smokes c e) ()

instance : ∀ l, Decidable (cigaretteReading l) := fun l ↦ by
  cases l <;> (unfold cigaretteReading; infer_instance)

theorem cigaretteReading_word_ne_phrase :
    ¬ cigaretteReading .word ∧ cigaretteReading .phrase := by
  constructor <;> decide +kernel

theorem cigarette_no_true_reading_available :
    ∀ l, Device.typeShift.AppliesAt l → ¬ cigaretteReading l := by
  intro l hl
  have h : l = .word := hl
  subst h
  exact cigaretteReading_word_ne_phrase.1

/-- One brand, smoked at every occasion. -/
abbrev smokesBrand : Fin 1 → Fin 3 → Prop := fun _ _ ↦ True

/-- With a constant witness the same local shift yields a true reading: the brand
variant (17b) is fine. -/
theorem brand_true_reading_available :
    ∃ l, Device.typeShift.AppliesAt l ∧
      ∃ b : Fin 1, gamma inSpeechInterval (fun e ↦ smokesBrand b e) () :=
  ⟨.word, rfl, ⟨0, by decide +kernel⟩⟩

/-! ### Cows do not eat nettles (§13.2.1)

Five cows, one a nettle-eater. With focus on the object, the alternatives are the ways
of eating and the generic scopes over negation: cows in general eat something other than
nettles, exceptions tolerated ((9a)). With focus on the auxiliary, the scope is its own
sole alternative, the generic is the trivially true refutation reading, and the negated
sentence denies that any cow eats nettles — false here ((9b)). -/

/-- The one nettle-eating cow among five. -/
abbrev eatsNettles : Fin 5 → Prop := (·.val = 4)

/-- Every cow eats something, the disjunction of the alternatives under object focus. -/
abbrev eatsSomething : Fin 5 → Prop := fun _ ↦ True

/-- With object focus the generic scopes over negation, and most eating cows avoid nettles
((9a)). -/
theorem cows_gen_over_neg :
    Cohen1999.gen Finset.univ (fun _ ↦ True) eatsSomething (fun x ↦ ¬ eatsNettles x) := by
  decide

/-- With auxiliary focus, negation scopes over the generic, so the sentence is false (9b). -/
theorem cows_neg_over_gen_false :
    Cohen1999.gen Finset.univ (fun _ ↦ True) eatsNettles eatsNettles :=
  Cohen1999.gen_self (by decide)

end Cohen2013
