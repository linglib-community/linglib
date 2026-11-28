module

public import Mathlib.Data.Set.Card
public import Linglib.Data.Examples.Bhadra2024
public import Linglib.Semantics.Presupposition.Again
public import Studies.Beavers2011

/-!
# Bhadra (2024): Verb roots encode outcomes

This file formalizes Bhadra's entries for the reversative prefix *un-* and the restitutive prefix
*re-*. An object `x` is in a state `k x t` at each time `t`, so an event `e` finds it in the state
`pre τ k x e` at its left boundary and leaves it in the state `res τ k x e` at its right boundary. A
dynamic transitive root denotes a predicate `P` of objects and events and carries a set `O` of
outcomes, the states its action may leave its object in. An event `e` reverses an event `e'` when
each ends in the state the other starts from, `res τ k x e' = pre τ k x e` and
`res τ k x e = pre τ k x e'`.

For a root `P` with outcomes `O`, *un-* is the partial proposition `un τ k P O x` of events. It is
defined of `e` when `1 < O.encard` and some earlier `P`-event left `x` in the state `e` starts
from, and it is true when `e` reverses such an event. *Re-* is `re τ k P T x`, for a contextual set
`T` of thresholds, the states the object may be in when the action begins. It is defined of `e`
when some earlier `P`-event `e'` has the result of `e`, `res τ k x e = res τ k x e'`, and that
result is a threshold, and it is true when moreover `P x e`.

*Un-* is undefined of a root with at most one outcome. *Re-* makes no demand on the number of
outcomes, and is undefined of a root none of whose outcomes is a threshold. *Re-* is repetitive
*again* along a smaller relation of an event to the earlier ones, so *again* is defined wherever
*re-* is and has its value there.

A root that effects a quantized change in Beavers's sense has one result, so *un-* is undefined of
it. Where the states are ordered and the object's state never decreases, an event reverses only
an event that left the object as it found it, so no event reverses an event of a root whose events
each raise the object on one of Beavers's scales.

The outcomes of *coil* and of *build* are read from the paper's lexical causation test, as the
states whose row of the test is judged acceptable. *Coil* has seven and *build* one, so *un-* is
undefined of *build*, whose *un-* form the paper judges ungrammatical.

## Implementation notes

* The entries are conditional events (`Trivalent.condEvent`), with the conditions the paper writes
  before the dot as the presupposition. The earlier event is bound across the presupposition and
  the assertion of *un-*: the assertion here is that `e` reverses some earlier event of the root.
  The assertion's conjunct that some predicate holds of `e` and `x` is true of every event and is
  omitted.
* The last presupposition of *re-* is formalized as the paper's statement of the prefix's
  distribution, that the base event leave the object in a state from which its result can be
  restored: the result of the base event is a threshold of the *re-* event. The base predicate is
  total.
* The paper's states are functions from times to lifespan points, and those of an outcome set or a
  threshold set are defined at one boundary of one event. An outcome or a threshold is here the
  lifespan point such a state takes there.
* The outcome set is a parameter, given for a root and an object. Its relation to the results of
  the root's events is a hypothesis of the theorems that need it, in the direction each needs.

## TODO

* The paper judges *unbreak a page* acceptable, and *un-* is undefined of every object of *break*
  with its one outcome.
* The judgments on *re-* with the impingement verbs and with *break a sewer* depend on threshold
  sets the paper does not give.
* The paper judges that *repaint the barn blue* does not entail that the barn was blue before.
  Here a property of the result of a *re-* event is a property of the base event's result, so the
  judgment holds only of a property the object's state does not record.
* The verbs of the rows are not yet tied to entries of the English language file, which has none
  for *coil*, and the paper's other judgments on the prefixes are not yet rows.

## References

* [D. Bhadra, *Verb roots encode outcomes: argument structure and lexical semantics of reversal
  and restitution* (2024)][bhadra-2024]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [A. von Stechow, *The Different Readings of Wieder ‘Again’: A Structural Account*
  (1996)][von-stechow-1996]
-/

@[expose] public section

namespace Bhadra2024

open Event (Precedes)

open ArgumentStructure ModalLogic Presupposition

open scoped SetRel

variable {Entity State I E : Type*} [LinearOrder I] {τ : E → NonemptyInterval I}

/-! ### States at the boundaries of an event -/

/-- (64): `res τ k x e` is the state of `x` at the right boundary of `e`. -/
def res (τ : E → NonemptyInterval I) (k : Entity → I → State) (x : Entity) (e : E) : State :=
  k x (τ e).snd

/-- (65): `pre τ k x e` is the state of `x` at the left boundary of `e`. -/
def pre (τ : E → NonemptyInterval I) (k : Entity → I → State) (x : Entity) (e : E) : State :=
  k x (τ e).fst

/-- (82a): `e` reverses `e'` when `e'` leaves `x` in the state `e` starts from and `e` leaves `x`
in the state `e'` started from. -/
def reversal (τ : E → NonemptyInterval I) (k : Entity → I → State) (x : Entity) : SetRel E E :=
  {(e, e') | res τ k x e' = pre τ k x e ∧ res τ k x e = pre τ k x e'}

variable {k : Entity → I → State} {P : Entity → E → Prop} {O T : Set State} {x : Entity}
  {e e' : E}

theorem reversal_comm : e ~[reversal τ k x] e' ↔ e' ~[reversal τ k x] e := and_comm

theorem pre_eq_res_of_reversal [PartialOrder State] (hk : Monotone (k x))
    (h : e ~[reversal τ k x] e') : pre τ k x e' = res τ k x e' :=
  (hk (τ e').fst_le_snd).antisymm <| h.1.trans_le <| (hk (τ e).fst_le_snd).trans h.2.le

/-! ### Reversative *un-* -/

open Classical in
/-- (66): *un-* of a root `P` with outcomes `O` is defined of `e` when `O` has several members and
an earlier `P`-event left `x` in the state `e` starts from, and is true when `e` reverses such an
event. -/
noncomputable def un (τ : E → NonemptyInterval I) (k : Entity → I → State)
    (P : Entity → E → Prop) (O : Set State) (x : Entity) : E → Trivalent :=
  Trivalent.condEvent
    (fun e ↦ 1 < O.encard ∧ ∃ e', P x e' ∧ Precedes τ e' e ∧ res τ k x e' = pre τ k x e)
    (fun e ↦ ∃ e', P x e' ∧ Precedes τ e' e ∧ e ~[reversal τ k x] e')

theorem un_ne_undefined_iff : un τ k P O x e ≠ .undefined ↔
    1 < O.encard ∧ ∃ e', P x e' ∧ Precedes τ e' e ∧ res τ k x e' = pre τ k x e := by
  simp [un]

@[simp] theorem un_eq_true_iff : un τ k P O x e = .true ↔
    1 < O.encard ∧ ∃ e', P x e' ∧ Precedes τ e' e ∧ e ~[reversal τ k x] e' := by
  simp only [un, Trivalent.condEvent_eq_true_iff, and_assoc]
  exact and_congr_right fun _ ↦ and_iff_right_of_imp fun ⟨e', h₁, h₂, h₃⟩ ↦ ⟨e', h₁, h₂, h₃.1⟩

/-- (67): *un-* is undefined of a root with at most one outcome. -/
theorem un_eq_undefined_of_subsingleton (hO : O.Subsingleton) : un τ k P O x e = .undefined :=
  of_not_not fun h ↦
    not_lt.2 (Set.encard_le_one_iff_subsingleton.2 hO) (un_ne_undefined_iff.1 h).1

-- (61a)–(61g): a lexically specified result
@[simp] theorem un_singleton (s : State) : un τ k P {s} x e = .undefined :=
  un_eq_undefined_of_subsingleton Set.subsingleton_singleton

-- (61h): no change specified
@[simp] theorem un_empty : un τ k P ∅ x e = .undefined :=
  un_eq_undefined_of_subsingleton Set.subsingleton_empty

/-! ### Restitutive *re-* -/

/-- (68): *re-* of a root `P` is *again* along the relation of an event to the earlier events that
have its result, that result being among the thresholds `T`. -/
noncomputable def re (τ : E → NonemptyInterval I) (k : Entity → I → State)
    (P : Entity → E → Prop) (T : Set State) (x : Entity) : E → Trivalent :=
  again {(e, e') | Precedes τ e' e ∧ res τ k x e = res τ k x e' ∧ res τ k x e' ∈ T} (P x)

theorem re_ne_undefined_iff : re τ k P T x e ≠ .undefined ↔
    ∃ e', P x e' ∧ Precedes τ e' e ∧ res τ k x e = res τ k x e' ∧ res τ k x e' ∈ T := by
  rw [re, again_ne_undefined_iff, diamond_iff]
  exact exists_congr fun _ ↦ and_comm

@[simp] theorem re_eq_true_iff : re τ k P T x e = .true ↔
    (∃ e', P x e' ∧ Precedes τ e' e ∧ res τ k x e = res τ k x e' ∧ res τ k x e' ∈ T) ∧ P x e := by
  rw [← re_ne_undefined_iff, re, again_eq_true_iff, again_ne_undefined_iff]

/-- (72): *re-* is undefined of a root none of whose outcomes is a threshold. -/
theorem re_eq_undefined_of_disjoint (hO : res τ k x '' {e | P x e} ⊆ O) (h : Disjoint O T) :
    re τ k P T x e = .undefined :=
  of_not_not fun hne ↦
    let ⟨e', hP, _, _, hT⟩ := re_ne_undefined_iff.1 hne
    Set.disjoint_left.1 h (hO ⟨e', hP, rfl⟩) hT

/-- Where *re-* is defined, repetitive *again* is defined of the same predicate along precedence
and has the value of *re-*. -/
theorem re_eq_again_of_ne_undefined (h : re τ k P T x e ≠ .undefined) :
    re τ k P T x e = again ({(e, e') | Precedes τ e' e} : SetRel E E) (P x) e := by
  have h' : ◇[({(e, e') | Precedes τ e' e} : SetRel E E)] (P x) e :=
    let ⟨e', hP, he', _⟩ := re_ne_undefined_iff.1 h
    ⟨e', he', hP⟩
  rw [re, again_ne_undefined_iff] at h
  simp [re, again, Trivalent.condEvent_apply, h, h']

-- (80): a property of the result of a *re-* event is a property of the base event's result
theorem exists_res_mem_of_re_ne_undefined {Q : Set State} (h : re τ k P T x e ≠ .undefined)
    (hQ : res τ k x e ∈ Q) : ∃ e', P x e' ∧ Precedes τ e' e ∧ res τ k x e' ∈ Q :=
  let ⟨e', hP, hp, hr, _⟩ := re_ne_undefined_iff.1 h
  ⟨e', hP, hp, hr ▸ hQ⟩

/-! ### Scalar change -/

section ScalarChange

variable {S : Type*} {θ : Entity → S → E → Prop} {R : Entity → S → State → E → Prop} {g : State}

theorem subsingleton_res_image_of_quantizedChange
    (hR : ∀ x s e, θ x s e → R x s g e → res τ k x e = g) (h : QuantizedChange θ R P g) :
    (res τ k x '' {e | P x e}).Subsingleton := by
  rintro _ ⟨e₁, h₁, rfl⟩ _ ⟨e₂, h₂, rfl⟩
  rw [h.eq_of_result hR h₁, h.eq_of_result hR h₂]

-- a root that effects a quantized change has one result
theorem un_eq_undefined_of_quantizedChange
    (hR : ∀ x s e, θ x s e → R x s g e → res τ k x e = g) (h : QuantizedChange θ R P g)
    (hO : O ⊆ res τ k x '' {e | P x e}) : un τ k P O x e = .undefined :=
  un_eq_undefined_of_subsingleton ((subsingleton_res_image_of_quantizedChange hR h).anti hO)

-- [beavers-2011] (48)
theorem un_eq_undefined_of_quantizedChange_result [LinearOrder State] {b : State}
    (h : QuantizedChange θ (Beavers2011.Result τ (fun _ ↦ k) b) P g)
    (hO : O ⊆ res τ k x '' {e | P x e}) : un τ k P O x e = .undefined :=
  un_eq_undefined_of_quantizedChange (fun _ _ _ _ h ↦ h.2.2) h hO

/-- (81a): along a trajectory that never decreases, no event reverses an event of a root whose
events each raise the object on one of Beavers's scales. -/
theorem not_diamond_reversal_of_nonQuantizedChange [LinearOrder State] {b : State}
    (hk : Monotone (k x)) (h : NonQuantizedChange θ (Beavers2011.Result τ (fun _ ↦ k) b) P) :
    ¬ ◇[reversal τ k x] (P x) e :=
  fun ⟨_, hr, hP⟩ ↦
    let ⟨_, _, hlt⟩ := Beavers2011.exists_lt_of_nonQuantizedChange h hP
    hlt.ne (pre_eq_res_of_reversal hk hr)

-- [beavers-2011] (59)
theorem un_ne_true_of_nonQuantizedChange [LinearOrder State] {b : State} (hk : Monotone (k x))
    (h : NonQuantizedChange θ (Beavers2011.Result τ (fun _ ↦ k) b) P) : un τ k P O x e ≠ .true :=
  fun hu ↦
    let ⟨_, e', hP, _, hr⟩ := un_eq_true_iff.1 hu
    not_diamond_reversal_of_nonQuantizedChange hk h ⟨e', hr, hP⟩

end ScalarChange

/-! ### A base event and a prefixed event -/

section Scenario

variable {a b : State}

/-- The base event of the scenario, over `[0, 5]`. -/
def ev₁ : NonemptyInterval ℤ := ⟨⟨0, 5⟩, by omega⟩

/-- The prefixed event of the scenario, over `[10, 15]`. -/
def ev₂ : NonemptyInterval ℤ := ⟨⟨10, 15⟩, by omega⟩

private theorem precedes_ev₁_ev₂ : Precedes id ev₁ ev₂ := by
  show (5 : ℤ) < 10; omega

private theorem not_precedes_ev₂ : ¬ Precedes id ev₂ ev₂ := by
  show ¬ (15 : ℤ) < 10; omega

/-- A root whose action occurs at the base event alone. -/
def once : Unit → NonemptyInterval ℤ → Prop := fun _ e ↦ e = ev₁

/-- A root whose action occurs at the base event and at the prefixed event. -/
def twice : Unit → NonemptyInterval ℤ → Prop := fun _ e ↦ e = ev₁ ∨ e = ev₂

/-- The object goes from `a` to `b` at the base event and back to `a` at the prefixed event. -/
def andBack (a b : State) : Unit → ℤ → State :=
  fun _ t ↦ if t ≤ 0 then a else if t ≤ 10 then b else a

/-- The object goes from `a` to `b` at the base event and is in `b` after the prefixed event. -/
def andStays (a b : State) : Unit → ℤ → State := fun _ t ↦ if t ≤ 0 then a else b

-- (67): where the prefixed event reverses the base event, the number of outcomes decides
theorem un_andBack_eq_true_iff :
    un id (andBack a b) once O () ev₂ = .true ↔ 1 < O.encard :=
  un_eq_true_iff.trans <| and_iff_left ⟨ev₁, rfl, precedes_ev₁_ev₂, rfl, rfl⟩

-- *un-* is defined of some event in some course of events exactly for a root with several outcomes
theorem exists_un_ne_undefined_iff :
    (∃ (k : Unit → ℤ → State) (P : Unit → NonemptyInterval ℤ → Prop) (e : NonemptyInterval ℤ),
      un id k P O () e ≠ .undefined) ↔ 1 < O.encard := by
  refine ⟨fun ⟨_, _, _, h⟩ ↦ (un_ne_undefined_iff.1 h).1, fun h ↦ ?_⟩
  obtain ⟨s, -⟩ := Set.encard_pos.1 (zero_lt_one.trans h)
  exact ⟨andBack s s, once, ev₂, by simp [un_andBack_eq_true_iff.2 h]⟩

-- (69): *reload the truck* and *reshatter the mirror*
theorem re_andStays_eq_true_iff : re id (andStays a b) twice T () ev₂ = .true ↔ b ∈ T := by
  rw [re_eq_true_iff, and_iff_left (.inr rfl)]
  refine ⟨?_, fun h ↦ ⟨ev₁, .inl rfl, precedes_ev₁_ev₂, rfl, h⟩⟩
  rintro ⟨e', rfl | rfl, hp, -, hT⟩
  exacts [hT, absurd hp not_precedes_ev₂]

end Scenario

/-! ### The outcomes of *coil* and *build* -/

section Data

/-- The verb a row tests, the lexeme of its span. -/
def verb? (d : Datum) : Option Examples.Lexeme := d.spans.head?.bind Examples.lexeme?

/-- (23), (63): the outcomes of a verb are the states that its rows of the lexical causation test
admit. -/
def outcomes (v : Examples.Lexeme) : Finset Examples.Outcome :=
  ((Examples.all.filter fun d ↦ verb? d = some v ∧ d.judgment = .acceptable).filterMap
    Examples.outcome).toFinset

-- (23)
theorem card_outcomes_coil : (outcomes .coil).card = 7 := by decide

-- (63)
theorem outcomes_build : outcomes .build = {.comeIntoBeing} := by decide

/-- (12e), (63): the *un-* form of a verb is judged acceptable exactly when its rows of the
lexical causation test admit several outcomes. -/
theorem un_rows : ∀ d ∈ Examples.all, Examples.affix d = some .un → ∀ v ∈ verb? d,
    (d.judgment = .acceptable ↔ 1 < (outcomes v).card) := by
  decide

-- every row names its verb, and two of the rows judge a prefixed form
theorem readCount_rows :
    Datum.ReadCount verb? Examples.all 14 ∧ Datum.ReadCount Examples.affix Examples.all 2 := by
  decide

theorem one_lt_encard_outcomes_coil : 1 < (outcomes .coil : Set Examples.Outcome).encard := by
  rw [Set.encard_coe_eq_coe_finsetCard, card_outcomes_coil]
  exact_mod_cast (by decide : 1 < 7)

-- *uncoil*: the rope is knotted up by the coiling and undamaged again after the uncoiling
theorem un_coil :
    un id (andBack Examples.Outcome.undamaged .knottedUp) once (outcomes .coil) () ev₂ = .true :=
  un_andBack_eq_true_iff.2 one_lt_encard_outcomes_coil

-- (12e)
theorem un_build (k : Entity → I → Examples.Outcome) (P : Entity → E → Prop) (x : Entity)
    (e : E) : un τ k P (outcomes .build) x e = .undefined := by
  rw [outcomes_build, Finset.coe_singleton]
  exact un_singleton _

end Data

end Bhadra2024
