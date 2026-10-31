module

public import Linglib.Data.Examples.Cohen2013
public import Linglib.Fragments.English.Coordination
public import Linglib.Semantics.Composition.Coordination
public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Quantification.Basic
public import Studies.Cohen1999
public import Linglib.Data.Examples.Readers

/-!
# Cohen (2013): No quantification without reinterpretation

Generic and habitual sentences have no audible quantifier: the hearer introduces the generic
quantifier $\mathbf{gen}$ of `Studies/Cohen1999.lean` by reinterpreting the quantifierless input,
and the device that introduces it fixes its scope. Predicate Transfer, which makes generics, is
pragmatically triggered and may apply to the verb or to the verb phrase; a type-shift, which makes
habituals and lifts a verb conjoined with an intensional one, applies only where the types
mismatch. [The readings each sentence allows are those its device allows](##readings_available).
[Reinterpreting the verb under an indefinite object gives the stronger
reading](##reading_word_le_phrase), so *Mary smokes a cigarette* [has only its implausible
reading](##cigarette_no_true_reading_available). On the composition engine, where a coordinator
and negation are words of every conjoinable type and SHIFT gives a verb a second type, *John
needed but didn't buy a new coat* [has only the reading with negation over the lifted
verb](##readings_neededButDidntBuy), since a lexical shift cannot apply to a phrase. Focus fixes
the alternatives of
$\mathbf{gen}$, so *Cows do not eat nettles* with focus on the auxiliary [denies that any cow eats
nettles](##nettles_aux_focus_iff).

## Implementation notes

* Both devices apply one operator, $\lambda x.\,\mathbf{gen}_y[R(y, x)][P(y)]$, and differ only in
  where they apply. It uses the absolute reading of $\mathbf{gen}$ with trivial alternatives, the
  chapter deferring the quantifier's content to Cohen's earlier work.
* Kinds are `Unit`, and individuals, cigarettes and intervals are `Fin n`; the relation
  $e \le \mathrm{int}(t)$ of the habitual shift is a parameter.
* An oddness judgment is derived as the falsity of every available reading in a model where the
  plausible reading is true; plausibility itself is not modelled.
* The rows name a reading by the scope of the reinterpreted element: `narrow` for the device
  applied to the verb, `wide` for the device applied to the phrase.
* The locality of SHIFT is derived on the composition engine, which interprets SHIFT as a second
  lexical reading of the verb; the locality of the habitual shift is the postulate
  `Device.AppliesAt`, since the engine's types have no sorts for intervals and moments.

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
* Deriving the habitual shift's locality on the engine needs sorts for intervals and moments.

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

open Quantifier

/-! ### The reinterpretation devices -/

/-- Partee and Rooth's SHIFT lifts an extensional transitive verb to take a quantifier object,
$\mathrm{SHIFT}(V) = \lambda Q\,\lambda x.\,Q(\lambda y.\,V(x, y))$. -/
def shift {E : Type*} (V : E → E → Prop) : (Set E → Prop) → E → Prop :=
  fun Q x ↦ Q {y | V x y}

section Reinterpret

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  (R : α → β → Prop) [∀ b, DecidablePred (R · b)]

/-- The reinterpretation both devices perform,
$\lambda x.\,\mathbf{gen}_y[R(y, x)][P(y)]$: with $R$ instantiation it is Predicate Transfer's
$T_G$, turning a property of individuals into the property of a kind whose instances generically
bear it; with $R$ inclusion in the interval around a moment it is the habitual shift $\gamma$,
turning a property of intervals into the property of a moment. -/
def reinterpret (P : α → Prop) (x : β) : Prop :=
  Cohen1999.gen Finset.univ (R · x) (fun _ ↦ True) P

instance (P : α → Prop) [DecidablePred P] (x : β) : Decidable (reinterpret R P x) := by
  unfold reinterpret; infer_instance

theorem monotone_reinterpret : Monotone (reinterpret R) := fun _ _ h _ ↦
  Cohen1999.monotone_gen h

end Reinterpret

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

/-- A verb `V` with a quantified object `Q`, reinterpreted by `op`: applied to the verb, the
reinterpretation leaves the object above it; applied to the verb phrase, it takes the object in
its scope. -/
def reading {α β γ : Type*} (op : (α → Prop) → β → Prop) (Q : Set γ → Prop)
    (V : γ → α → Prop) : Level → β → Prop
  | .word => fun b ↦ Q {y | op (V y) b}
  | .phrase => op fun x ↦ Q {y | V y x}

/-- Under an indefinite object, reinterpreting the verb entails reinterpreting the verb phrase,
for any reinterpretation monotone in the property it reinterprets. -/
theorem reading_word_le_phrase {α β γ : Type*} {op : (α → Prop) → β → Prop} (hop : Monotone op)
    (N : γ → Prop) (V : γ → α → Prop) :
    reading op (Det.some N) V .word ≤ reading op (Det.some N) V .phrase :=
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
  reading (reinterpret storkOf) (Det.some Set.univ) fun a s ↦ nestsIn s a

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
  reading (reinterpret inSpeechInterval) (Det.some Set.univ) smokes

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
  reading (reinterpret inSpeechInterval) (Det.some (Set.univ : Set (Fin 1))) fun _ _ ↦ True

-- (17b)
theorem brand_true_reading_available : ∃ l, Device.typeShift.AppliesAt l ∧ brand l () :=
  ⟨.word, rfl, by simp only [brand, reading]; decide +kernel⟩

/-! ### John needed but didn't buy a new coat

On the composition engine a coordinator and negation are words of every conjoinable type, and
SHIFT is a second reading of *buy*. Coordinating *need* with *buy* is a type mismatch that only
the lifted reading repairs, and a shift applies to a word, never to the phrase *didn't buy*. -/

section Engine

open Montague PhraseStructure

variable {E : Type} (j : E) (need : ((E → Prop) → Prop) → E → Prop) (buy : E → E → Prop)
  (newCoat : E → Prop)

/-- Negation at every conjoinable type, the complement in its Boolean algebra. -/
def negation : Set (Denotation E Unit) :=
  Set.range fun τ : {τ : Ty // τ.Conjoinable} ↦
    ⟨τ.1 ⇒ τ.1, fun p ↦ letI := Ty.Domain.completeBooleanAlgebra E Unit τ.1 τ.2; pᶜ⟩

/-- *Buy* at its own type and lifted by SHIFT. -/
def buyReadings : Set (Denotation E Unit) :=
  {⟨Ty.eet, fun y x ↦ buy x y⟩, ⟨Ty.ett ⇒ Ty.et, shift buy⟩}

/-- The words of (23) and (25a). -/
inductive Word
  | john
  | needed
  | and
  | but
  | didnt
  | buy
  | aNewCoat

/-- The lexicon, with `B` the readings of *buy* and *need* a relation to a quantifier. -/
def lexicon (B : Set (Denotation E Unit)) : Word → Set (Denotation E Unit)
  | .john => {⟨.e, j⟩}
  | .needed => {⟨Ty.ett ⇒ Ty.et, need⟩}
  | .and => English.Coordination.and_.readings
  | .but => English.Coordination.but_.readings
  | .didnt => negation
  | .buy => B
  | .aNewCoat => {⟨Ty.ett, Det.some newCoat⟩}

/-- (23), `John [[needed [and buy]] [a new coat]]`. -/
def neededAndBought : Tree Unit Word :=
  .bin (.leaf .john) (.bin (.bin (.leaf .needed) (.bin (.leaf .and) (.leaf .buy)))
    (.leaf .aNewCoat))

/-- (25a), `John [[needed [but [didn't buy]]] [a new coat]]`. -/
def neededButDidntBuy : Tree Unit Word :=
  .bin (.leaf .john) (.bin (.bin (.leaf .needed) (.bin (.leaf .but) (.bin (.leaf .didnt)
    (.leaf .buy)))) (.leaf .aNewCoat))

-- (23)
theorem readings_neededAndBought_unlifted (g : Assignment E) :
    Tree.readings (lexicon j need newCoat {⟨Ty.eet, fun y x ↦ buy x y⟩}) g neededAndBought =
      ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun d ↦ ?_
  simp only [neededAndBought, Tree.mem_readings_phrase_binary, Tree.readings_terminal, lexicon,
    Set.mem_singleton_iff, Mode.combine?, Option.map_eq_some_iff]
  rintro ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, ⟨⟨τ, h⟩, rfl⟩, _, rfl, ⟨ρ₁, m₁⟩, hm₁, rfl⟩,
    ⟨ρ₂, m₂⟩, hm₂, rfl⟩, _, rfl, ⟨ρ₃, m₃⟩, -, rfl⟩, ⟨ρ₄, m₄⟩, -, rfl⟩
  have b₁ := Ty.isBasic_of_mode?_eq_some hm₁
  have b₂ := Ty.isBasic_of_mode?_eq_some hm₂
  clear hm₁ hm₂
  cases m₁
  all_goals try simp only [Mode.IsBasic] at b₁
  all_goals cases m₂
  all_goals simp only [Mode.IsBasic] at b₂

-- (23)
theorem readings_neededAndBought (g : Assignment E) :
    Tree.readings (lexicon j need newCoat (buyReadings buy)) g neededAndBought =
      {⟨.t, need (Det.some newCoat) j ∧ shift buy (Det.some newCoat) j⟩} := by
  ext d
  simp only [neededAndBought, Tree.mem_readings_phrase_binary, Tree.readings_terminal, lexicon,
    buyReadings, Set.mem_singleton_iff, Set.mem_insert_iff, Mode.combine?,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, ⟨⟨τ, h⟩, rfl⟩, _, hb, ⟨ρ₁, m₁⟩, hm₁, rfl⟩,
      ⟨ρ₂, m₂⟩, hm₂, rfl⟩, _, rfl, ⟨ρ₃, m₃⟩, hm₃, rfl⟩, ⟨ρ₄, m₄⟩, hm₄, rfl⟩
    have b₁ := Ty.isBasic_of_mode?_eq_some hm₁
    have b₂ := Ty.isBasic_of_mode?_eq_some hm₂
    have b₃ := Ty.isBasic_of_mode?_eq_some hm₃
    have b₄ := Ty.isBasic_of_mode?_eq_some hm₄
    clear hm₁ hm₂ hm₃ hm₄
    rcases hb with rfl | rfl <;> cases m₁
    all_goals try simp only [Mode.IsBasic] at b₁
    all_goals cases m₂
    all_goals try simp only [Mode.IsBasic] at b₂
    all_goals cases m₃
    all_goals try simp only [Mode.IsBasic] at b₃
    all_goals cases m₄
    all_goals try simp only [Mode.IsBasic] at b₄
    simp [Coordinator.reading, Coordinator.denote_of_conjunctive (c := English.Coordination.and_)
      rfl]
  · rintro rfl
    refine ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, ⟨⟨Ty.ett ⇒ Ty.et, trivial⟩, rfl⟩, _, .inr rfl,
      _, Mode.mode?_fn_left _ _, rfl⟩, _, Mode.mode?_fn_right _ _, rfl⟩, _, rfl, _,
      Mode.mode?_fn_left _ _, rfl⟩, _, Mode.mode?_fn_right _ _, ?_⟩
    simp [Coordinator.reading, Coordinator.denote_of_conjunctive (c := English.Coordination.and_)
      rfl]

/-- On the composition engine, *John needed but didn't buy a new coat* has only the reading with
negation over the lifted verb. -/
theorem readings_neededButDidntBuy (g : Assignment E) :
    Tree.readings (lexicon j need newCoat (buyReadings buy)) g neededButDidntBuy =
      {⟨.t, need (Det.some newCoat) j ∧ ¬ shift buy (Det.some newCoat) j⟩} := by
  ext d
  simp only [neededButDidntBuy, Tree.mem_readings_phrase_binary, Tree.readings_terminal, lexicon,
    buyReadings, Set.mem_singleton_iff, Set.mem_insert_iff, Mode.combine?,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, ⟨⟨τ₂, h₂⟩, rfl⟩, _, ⟨_, ⟨⟨τ₁, h₁⟩, rfl⟩, _, hb,
      ⟨ρ₁, m₁⟩, hm₁, rfl⟩, ⟨ρ₂, m₂⟩, hm₂, rfl⟩, ⟨ρ₃, m₃⟩, hm₃, rfl⟩, _, rfl, ⟨ρ₄, m₄⟩, hm₄, rfl⟩,
      ⟨ρ₅, m₅⟩, hm₅, rfl⟩
    have b₁ := Ty.isBasic_of_mode?_eq_some hm₁
    have b₂ := Ty.isBasic_of_mode?_eq_some hm₂
    have b₃ := Ty.isBasic_of_mode?_eq_some hm₃
    have b₄ := Ty.isBasic_of_mode?_eq_some hm₄
    have b₅ := Ty.isBasic_of_mode?_eq_some hm₅
    clear hm₁ hm₂ hm₃ hm₄ hm₅
    rcases hb with rfl | rfl <;> cases m₁
    all_goals try simp only [Mode.IsBasic] at b₁
    all_goals cases m₂
    all_goals try simp only [Mode.IsBasic] at b₂
    all_goals cases m₃
    all_goals try simp only [Mode.IsBasic] at b₃
    all_goals cases m₄
    all_goals try simp only [Mode.IsBasic] at b₄
    all_goals cases m₅
    all_goals try simp only [Mode.IsBasic] at b₅
    simp [Coordinator.reading, Coordinator.denote_of_adversative (c := English.Coordination.but_)
      rfl]
  · rintro rfl
    refine ⟨_, rfl, _, ⟨_, ⟨_, rfl, _, ⟨_, ⟨⟨Ty.ett ⇒ Ty.et, trivial⟩, rfl⟩, _,
      ⟨_, ⟨⟨Ty.ett ⇒ Ty.et, trivial⟩, rfl⟩, _, .inr rfl, _, Mode.mode?_fn_left _ _, rfl⟩, _,
      Mode.mode?_fn_left _ _, rfl⟩, _, Mode.mode?_fn_right _ _, rfl⟩, _, rfl, _,
      Mode.mode?_fn_left _ _, rfl⟩, _, Mode.mode?_fn_right _ _, ?_⟩
    simp [Coordinator.reading, Coordinator.denote_of_adversative (c := English.Coordination.but_)
      rfl]

-- (25)
theorem not_shift_ne_shift_not :
    ¬ ((¬ shift (fun _ y ↦ y = true) (Det.some Set.univ) true) ↔
      shift (fun _ b ↦ ¬ (b = true)) (Det.some Set.univ) true) := by
  unfold shift
  decide

end Engine

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
