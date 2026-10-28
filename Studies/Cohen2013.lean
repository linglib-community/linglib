module

public import Linglib.Data.Examples.Cohen2013
public import Studies.Cohen1999

/-!
# Cohen (2013): No quantification without reinterpretation

Generic and habitual sentences have no audible quantifier: the hearer introduces the generic
quantifier $\mathbf{gen}$ of `Studies/Cohen1999.lean` by reinterpreting the quantifierless input,
and the device that introduces it fixes its scope. Predicate Transfer, which makes generics, is
pragmatically triggered and may apply to the verb or to the verb phrase; a type-shift, which makes
habituals and lifts a verb conjoined with an intensional one, applies only where the types
mismatch. [The readings each sentence allows are those its device allows](##readings_available).
[Reinterpreting the verb gives the stronger reading](##reading_word_le_phrase), so *Mary smokes a
cigarette* [has only its implausible reading](##cigarette_no_true_reading_available), and
[negation scopes over a lifted verb](##needed_but_didnt_buy). Focus fixes the alternatives of
$\mathbf{gen}$, so *Cows do not eat nettles* with focus on the auxiliary [denies that any cow eats
nettles](##nettles_aux_focus_iff).

## Implementation notes

* Both operators use the absolute reading of $\mathbf{gen}$ with trivial alternatives, the chapter
  deferring the quantifier's content to Cohen's earlier work.
* Kinds are `Unit`, and individuals, cigarettes and intervals are `Fin n`; the relation
  $e \le \mathrm{int}(t)$ of the habitual shift is a parameter.
* An oddness judgment is derived as the falsity of every available reading in a model where the
  plausible reading is true; plausibility itself is not modelled.
* The rows name a reading by the scope of the reinterpreted element: `narrow` for the device
  applied to the verb, `wide` for the device applied to the phrase.

## Errata

* Below (25) the chapter says that (25a) can only mean (25b) "but not (25b)"; the excluded
  reading is (25c).
* The derivation of the bamboo-shoots generic applies $T_G$ to "(39b)"; the logical form is
  (35b).

## TODO

* Bare plurals under habituals ((18): $\mathbf{gen}$ above the existential only) follow from bare
  plurals introducing no discourse referent, a duplex condition under an existential being no
  well-formed DRS (after Cohen and Erteschik-Shir); this needs the DRT box substrate.
* Predicate Transfer's ban on scoping out of opaque contexts rests on its need for the property's
  intension, which these extensional models cannot state.
* The wide-scope generic objects of (19)–(20), which refute a syntactic account, presuppose a
  subject–object asymmetry not encoded here.

## References

* [cohen-2013]
* [nunberg-1995]
* [recanati-2003]
* [partee-rooth-1983]
* [cohen-1999a]
* [carlson-1977a]
* [krifka-etal-1995]
* [cohen-erteschik-shir-2002]
* [taylor-1977]
* [dowty-1979]
-/

@[expose] public section

namespace Cohen2013

/-! ### The reinterpretation devices -/

/-- Partee and Rooth's SHIFT lifts an extensional transitive verb to take a quantifier object,
$\mathrm{SHIFT}(V) = \lambda Q\,\lambda x.\,Q(\lambda y.\,V(x, y))$. -/
def shift {E : Type*} (V : E → E → Prop) : ((E → Prop) → Prop) → E → Prop :=
  fun Q x ↦ Q fun y ↦ V x y

section Operators

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  (R : α → β → Prop) [∀ b, DecidablePred (R · b)]

/-- Predicate Transfer for generics, $T_G(P) = \lambda x.\,\mathbf{gen}_y[C(y, x)][P(y)]$, turns
a property of individuals into the property of a kind whose instances generically bear it. -/
def transfer (P : α → Prop) (x : β) : Prop :=
  Cohen1999.gen Finset.univ (R · x) (fun _ ↦ True) P

instance (P : α → Prop) [DecidablePred P] (x : β) : Decidable (transfer R P x) := by
  unfold transfer; infer_instance

theorem monotone_transfer : Monotone (transfer R) := fun _ _ h x ↦ by
  classical exact Cohen1999.gen_mono h

/-- The habitual type-shift $\gamma P = \lambda t.\,\mathbf{gen}_e[e \le \mathrm{int}(t)][P(e)]$
turns a property of intervals into the property of a moment in whose surrounding interval it
generically holds. -/
def gamma (P : α → Prop) (t : β) : Prop :=
  Cohen1999.gen Finset.univ (R · t) (fun _ ↦ True) P

instance (P : α → Prop) [DecidablePred P] (t : β) : Decidable (gamma R P t) := by
  unfold gamma; infer_instance

theorem monotone_gamma : Monotone (gamma R) := fun _ _ h t ↦ by
  classical exact Cohen1999.gen_mono h

end Operators

/-- A reinterpretation device applies to the mismatching word itself or to the containing
phrase. -/
inductive Level
  | word
  | phrase
  deriving DecidableEq, Fintype

/-- The two devices that introduce covert quantifiers. -/
inductive Device
  | predicateTransfer
  | typeShift
  deriving DecidableEq

/-- Predicate Transfer is pragmatically triggered and may apply at any level; a type-shift is
triggered by the type mismatch and applies at its site only. -/
def Device.AppliesAt : Device → Level → Prop
  | .predicateTransfer, _ => True
  | .typeShift, l => l = .word

instance : ∀ d l, Decidable (Device.AppliesAt d l)
  | .predicateTransfer, _ => .isTrue trivial
  | .typeShift, l => inferInstanceAs (Decidable (l = .word))

/-- A verb `V` with an existential object restricted to `N`, reinterpreted by `op`: applied to
the verb, the reinterpretation leaves the object above it; applied to the verb phrase, it takes
the object in its scope. -/
def reading {α β γ : Type*} (op : (α → Prop) → β → Prop) (N : γ → Prop) (V : γ → α → Prop) :
    Level → β → Prop
  | .word => fun b ↦ ∃ y, N y ∧ op (V y) b
  | .phrase => op fun x ↦ ∃ y, N y ∧ V y x

/-- Reinterpreting the verb entails reinterpreting the verb phrase, for any reinterpretation
monotone in the property it reinterprets. -/
theorem reading_word_le_phrase {α β γ : Type*} {op : (α → Prop) → β → Prop} (hop : Monotone op)
    (N : γ → Prop) (V : γ → α → Prop) : reading op N V .word ≤ reading op N V .phrase :=
  fun b ⟨y, hy, h⟩ ↦ hop (fun _ hx ↦ ⟨y, hy, hx⟩) b h

/-! ### The readings the devices allow -/

/-- The device of a construction: Predicate Transfer for a generic, a type-shift for a habitual
and for an extensional verb conjoined with an intensional one. -/
def device? (e : Datum) : Option Device :=
  e.parse? "construction"
    [("generic", .predicateTransfer), ("habitual", .typeShift), ("verb conjunction", .typeShift)]

/-- A row's name for the reading a level yields. -/
def Level.key : Level → String
  | .word => "narrow"
  | .phrase => "wide"

/-- A sentence has a reading exactly when its device may apply at the reading's level. -/
theorem readings_available :
    ∀ e ∈ Examples.all, ∀ d ∈ device? e, ∀ l,
      (e.readings.lookup l.key = some .acceptable ↔ d.AppliesAt l) := by
  decide

theorem readCount_device : Datum.ReadCount device? Examples.all 4 := by
  decide

/-! ### Storks have a favorite nesting area

Two storks, each nesting in its own area: transferring the verb quantifies over each area's
nesters, transferring the verb phrase over the storks' own areas. -/

/-- Each of two storks nests in its own area. -/
abbrev nestsIn : Fin 2 → Fin 2 → Prop := (· = ·)

/-- Every individual stork instantiates the kind. -/
abbrev storkOf : Fin 2 → Unit → Prop := fun _ _ ↦ True

/-- The storks sentence, by the level of transfer. -/
def storks : Level → Unit → Prop :=
  reading (transfer storkOf) (fun _ ↦ True) fun a s ↦ nestsIn s a

-- (12b)
theorem storks_word_ne_phrase : ¬ storks .word () ∧ storks .phrase () := by
  simp only [storks, reading]
  constructor <;> decide +kernel

/-! ### Mary smokes a cigarette

Three occasions in the interval around the speech moment, a different cigarette each time. -/

/-- Mary smokes a different cigarette at each of three occasions. -/
abbrev smokes : Fin 3 → Fin 3 → Prop := (· = ·)

/-- Every occasion falls in the interval around the speech moment. -/
abbrev inSpeechInterval : Fin 3 → Unit → Prop := fun _ _ ↦ True

/-- The cigarette sentence, by the level of the shift. -/
def cigarette : Level → Unit → Prop :=
  reading (gamma inSpeechInterval) (fun _ ↦ True) smokes

-- (45)
theorem cigarette_word_ne_phrase : ¬ cigarette .word () ∧ cigarette .phrase () := by
  simp only [cigarette, reading]
  constructor <;> decide +kernel

/-- A type-shift gives *Mary smokes a cigarette* only the reading on which one cigarette is
smoked habitually, false when she smokes a different one each time. -/
theorem cigarette_no_true_reading_available :
    ∀ l, Device.typeShift.AppliesAt l → ¬ cigarette l () := by
  intro l hl
  have h : l = .word := hl
  subst h
  exact cigarette_word_ne_phrase.1

/-- The brand variant, one brand smoked at every occasion. -/
def brand : Level → Unit → Prop :=
  reading (gamma inSpeechInterval) (fun _ : Fin 1 ↦ True) fun _ _ ↦ True

-- (17b)
theorem brand_true_reading_available : ∃ l, Device.typeShift.AppliesAt l ∧ brand l () :=
  ⟨.word, rfl, by simp only [brand, reading]; decide +kernel⟩

/-! ### John needed but didn't buy a new coat -/

/-- The second conjunct of *John needed but didn't buy a new coat*, with SHIFT applied to the
verb or to the negated verb. -/
def didntBuy {E : Type*} (V : E → E → Prop) (Q : (E → Prop) → Prop) (x : E) : Level → Prop
  | .word => ¬ shift V Q x
  | .phrase => shift (fun a b ↦ ¬ V a b) Q x

/-- A type-shift gives *John needed but didn't buy a new coat* only the reading on which he
bought no new coat. -/
theorem needed_but_didnt_buy {E : Type*} (V : E → E → Prop) (N : E → Prop) (x : E) :
    ∀ l, Device.typeShift.AppliesAt l →
      (didntBuy V (fun P ↦ ∃ y, N y ∧ P y) x l ↔ ¬ ∃ y, N y ∧ V x y) := by
  intro l hl
  have h : l = .word := hl
  subst h
  exact Iff.rfl

-- (25)
theorem didntBuy_word_ne_phrase :
    ¬ (didntBuy (fun _ y ↦ y = true) (fun P ↦ ∃ y, True ∧ P y) true .word ↔
      didntBuy (fun _ y ↦ y = true) (fun P ↦ ∃ y, True ∧ P y) true .phrase) := by
  unfold didntBuy shift
  decide

/-! ### Cows do not eat nettles

With focus on the object, the alternatives are the ways of eating and $\mathbf{gen}$ scopes over
negation. With focus on the auxiliary, the scope is its own sole alternative, and the generic
under negation is the existential one. -/

/-- The one nettle-eating cow among five. -/
abbrev eatsNettles : Fin 5 → Prop := (·.val = 4)

/-- Every cow eats something, the disjunction of the alternatives under object focus. -/
abbrev eatsSomething : Fin 5 → Prop := fun _ ↦ True

-- (7a), (9a)
theorem nettles_object_focus :
    Cohen1999.gen Finset.univ (fun _ ↦ True) eatsSomething (fun x ↦ ¬ eatsNettles x) ∧
      ∃ x, eatsNettles x :=
  ⟨by decide, 4, rfl⟩

/-- With focus on the auxiliary, *Cows do not eat nettles* denies that any cow eats nettles. -/
theorem nettles_aux_focus_iff {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (cow eats : α → Prop) [DecidablePred cow] [DecidablePred eats] :
    ¬ Cohen1999.gen Finset.univ cow eats eats ↔ ∀ x, cow x → ¬ eats x := by
  simp [Cohen1999.gen_self_iff, Finset.filter_nonempty_iff]

end Cohen2013
