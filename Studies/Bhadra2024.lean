module

public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Presupposition.Again
public import Studies.Beavers2011

/-!
# Bhadra (2024): Verb roots encode outcomes

This file formalizes Bhadra's entries for the reversative prefix *un-* and the restitutive prefix
*re-*. An object `x` is in a state `k x t` at each time `t`, so an event `e` finds it in the state
`pre k x e` at its left boundary and leaves it in the state `res k x e` at its right boundary. A
dynamic transitive root denotes a predicate `P` of objects and events and carries a set `O` of
outcomes, the states its action may leave its object in.

For a root `P` with outcomes `O`, *un-* is the partial proposition `un k P O x` of events. It is
defined of `e` when `1 < O.encard` and some earlier `P`-event `e'` left `x` in the state `e` starts
from, `res k x e' = pre k x e`, and it is true when moreover `e` returns `x` to the state `e'`
started from, `res k x e = pre k x e'`. *Re-* is `re k P T x`, for a contextual set `T` of
thresholds, the states the object may be in when the action begins. It is defined of `e` when some
earlier `P`-event `e'` has the result of `e`, `res k x e = res k x e'`, and that result is a
threshold, and it is true when moreover `P x e`.

*Un-* is undefined of a root with at most one outcome. *Re-* makes no demand on the number of
outcomes, and is undefined of a root none of whose outcomes is a threshold. *Re-* is repetitive
*again* along a smaller relation of an event to the earlier ones, so *again* is defined wherever
*re-* is and has its value there. A root that effects a quantized change in Beavers's sense has one
result, so *un-* is undefined of it.

## Implementation notes

* The entries are conditional events (`Trivalent.condEvent`), with the conditions the paper writes
  before the dot as the presupposition. The earlier event is bound across the presupposition and
  the assertion of *un-*: the assertion here is that some event satisfying the presupposition is
  one whose starting state `e` restores. The assertion's conjunct that some predicate holds of `e`
  and `x` is true of every event and is omitted.
* The last presupposition of *re-* is formalized as the paper's statement of the prefix's
  distribution, that the base event leave the object in a state from which its result can be
  restored: the result of the base event is a threshold of the *re-* event. The base predicate is
  total.
* The paper's states are functions from times to lifespan points, and those of an outcome set or a
  threshold set are defined at one boundary of one event. An outcome or a threshold is here the
  lifespan point such a state takes there.
* The outcome set is a parameter, given for a root and an object. That the result of each of the
  root's events is among its outcomes is a hypothesis of the theorems that need it.

## TODO

* The paper judges *unbreak a page* acceptable, and *un-* is undefined of every object of *break*
  with its one outcome.
* The judgments on *re-* with the impingement verbs and with *break a sewer* depend on threshold
  sets the paper does not give.
* The paper's judgments are not yet rows of `Data/Examples`.

## References

* [D. Bhadra, *Verb roots encode outcomes: argument structure and lexical semantics of reversal
  and restitution* (2024)][bhadra-2024]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
* [A. von Stechow, *The Different Readings of Wieder ‘Again’: A Structural Account*
  (1996)][von-stechow-1996]
-/

@[expose] public section

namespace Bhadra2024

open Event (τ Precedes)

open ArgumentStructure ModalLogic Presupposition

variable {Entity State I E : Type*} [LinearOrder I] [TemporalTrace E I]

/-! ### States at the boundaries of an event -/

/-- (64): `res k x e` is the state of `x` at the right boundary of `e`. -/
def res (k : Entity → I → State) (x : Entity) (e : E) : State := k x (τ e).snd

/-- (65): `pre k x e` is the state of `x` at the left boundary of `e`. -/
def pre (k : Entity → I → State) (x : Entity) (e : E) : State := k x (τ e).fst

/-! ### Reversative *un-* -/

open Classical in
/-- (66): *un-* of a root `P` with outcomes `O` is defined of `e` when `O` has several members and
an earlier `P`-event left `x` in the state `e` starts from, and is true when `e` returns `x` to the
state that event started from. -/
noncomputable def un (k : Entity → I → State) (P : Entity → E → Prop) (O : Set State)
    (x : Entity) : E → Trivalent :=
  Trivalent.condEvent
    (fun e ↦ 1 < O.encard ∧ ∃ e', P x e' ∧ Precedes e' e ∧ res k x e' = pre k x e)
    (fun e ↦ ∃ e', P x e' ∧ Precedes e' e ∧ res k x e' = pre k x e ∧ res k x e = pre k x e')

variable {k : Entity → I → State} {P : Entity → E → Prop} {O T : Set State} {x : Entity} {e : E}

theorem un_ne_undefined_iff : un k P O x e ≠ .undefined ↔
    1 < O.encard ∧ ∃ e', P x e' ∧ Precedes e' e ∧ res k x e' = pre k x e := by
  simp [un]

@[simp] theorem un_eq_true_iff : un k P O x e = .true ↔ 1 < O.encard ∧
    ∃ e', P x e' ∧ Precedes e' e ∧ res k x e' = pre k x e ∧ res k x e = pre k x e' := by
  simp only [un, Trivalent.condEvent_eq_true_iff, and_assoc]
  exact and_congr_right fun _ ↦ and_iff_right_of_imp fun ⟨e', h₁, h₂, h₃, _⟩ ↦ ⟨e', h₁, h₂, h₃⟩

/-- (67): *un-* is undefined of a root with at most one outcome. -/
theorem un_eq_undefined_of_subsingleton (hO : O.Subsingleton) : un k P O x e = .undefined :=
  of_not_not fun h ↦
    not_lt.2 (Set.encard_le_one_iff_subsingleton.2 hO) (un_ne_undefined_iff.1 h).1

-- (61a)–(61g): a lexically specified result
@[simp] theorem un_singleton (s : State) : un k P {s} x e = .undefined :=
  un_eq_undefined_of_subsingleton Set.subsingleton_singleton

-- (61h): no change specified
@[simp] theorem un_empty : un k P ∅ x e = .undefined :=
  un_eq_undefined_of_subsingleton Set.subsingleton_empty

/-! ### Restitutive *re-* -/

/-- (68): *re-* of a root `P` is *again* along the relation of an event to the earlier events that
have its result, that result being among the thresholds `T`. -/
noncomputable def re (k : Entity → I → State) (P : Entity → E → Prop) (T : Set State)
    (x : Entity) : E → Trivalent :=
  again {(e, e') | Precedes e' e ∧ res k x e = res k x e' ∧ res k x e' ∈ T} (P x)

theorem re_ne_undefined_iff : re k P T x e ≠ .undefined ↔
    ∃ e', P x e' ∧ Precedes e' e ∧ res k x e = res k x e' ∧ res k x e' ∈ T := by
  rw [re, again_ne_undefined_iff, diamond_iff]
  exact exists_congr fun _ ↦ and_comm

@[simp] theorem re_eq_true_iff : re k P T x e = .true ↔
    (∃ e', P x e' ∧ Precedes e' e ∧ res k x e = res k x e' ∧ res k x e' ∈ T) ∧ P x e := by
  rw [← re_ne_undefined_iff, re, again_eq_true_iff, again_ne_undefined_iff]

/-- (72): *re-* is undefined of a root none of whose outcomes is a threshold. -/
theorem re_eq_undefined_of_disjoint (hO : ∀ e, P x e → res k x e ∈ O) (h : Disjoint O T) :
    re k P T x e = .undefined :=
  of_not_not fun hne ↦
    let ⟨e', hP, _, _, hT⟩ := re_ne_undefined_iff.1 hne
    Set.disjoint_left.1 h (hO e' hP) hT

/-- Where *re-* is defined, repetitive *again* is defined of the same predicate along precedence
and has the value of *re-*. -/
theorem re_eq_again_of_ne_undefined (h : re k P T x e ≠ .undefined) :
    re k P T x e = again ({(e, e') | Precedes e' e} : SetRel E E) (P x) e := by
  have h' : ◇[({(e, e') | Precedes e' e} : SetRel E E)] (P x) e :=
    let ⟨e', hP, he', _⟩ := re_ne_undefined_iff.1 h
    ⟨e', he', hP⟩
  rw [re, again_ne_undefined_iff] at h
  simp [re, again, Trivalent.condEvent_apply, h, h']

/-! ### Quantized change -/

section QuantizedChange

variable {S : Type*} {θ : Entity → S → E → Prop} {R : Entity → S → State → E → Prop} {g : State}

/-- A root that effects a quantized change in Beavers's sense has one result, so *un-* is
undefined of it when each of its outcomes is the result of one of its events. -/
theorem un_eq_undefined_of_quantizedChange (hR : ∀ x s g e, R x s g e → res k x e = g)
    (h : QuantizedChange θ R P g) (hO : ∀ s ∈ O, ∃ e, P x e ∧ res k x e = s) :
    un k P O x e = .undefined := by
  refine un_eq_undefined_of_subsingleton fun s₁ h₁ s₂ h₂ ↦ ?_
  obtain ⟨e₁, hP₁, rfl⟩ := hO s₁ h₁
  obtain ⟨e₂, hP₂, rfl⟩ := hO s₂ h₂
  obtain ⟨_, -, hg₁⟩ := h x e₁ hP₁
  obtain ⟨_, -, hg₂⟩ := h x e₂ hP₂
  rw [hR _ _ _ _ hg₁, hR _ _ _ _ hg₂]

-- [beavers-2011] (48)
theorem un_eq_undefined_of_quantizedChange_result [LinearOrder State] {b : State}
    (h : QuantizedChange θ (Beavers2011.Result (fun _ ↦ k) b) P g)
    (hO : ∀ s ∈ O, ∃ e, P x e ∧ res k x e = s) : un k P O x e = .undefined :=
  un_eq_undefined_of_quantizedChange (fun _ _ _ _ h ↦ h.2.2) h hO

end QuantizedChange

/-! ### A base event and a prefixed event -/

section Examples

variable {a b : State}

/-- The base event of the scenario, over `[0, 5]`. -/
def ev₁ : NonemptyInterval ℤ := ⟨⟨0, 5⟩, by omega⟩

/-- The prefixed event of the scenario, over `[10, 15]`. -/
def ev₂ : NonemptyInterval ℤ := ⟨⟨10, 15⟩, by omega⟩

private theorem precedes_ev₁_ev₂ : Precedes ev₁ ev₂ := by
  show (5 : ℤ) < 10; omega

private theorem not_precedes_ev₂ : ¬ Precedes ev₂ ev₂ := by
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

/-- Where the prefixed event undoes the base event, *un-* is true of it for a root with several
outcomes, and undefined otherwise. -/
theorem un_andBack_eq_true_iff :
    un (andBack a b) once O () ev₂ = .true ↔ 1 < O.encard :=
  un_eq_true_iff.trans <| and_iff_left ⟨ev₁, rfl, precedes_ev₁_ev₂, rfl, rfl⟩

-- (69): *reload the truck* and *reshatter the mirror*
theorem re_andStays_eq_true_iff : re (andStays a b) twice T () ev₂ = .true ↔ b ∈ T := by
  rw [re_eq_true_iff, and_iff_left (.inr rfl)]
  refine ⟨?_, fun h ↦ ⟨ev₁, .inl rfl, precedes_ev₁_ev₂, rfl, h⟩⟩
  rintro ⟨e', rfl | rfl, hp, -, hT⟩
  exacts [hT, absurd hp not_precedes_ev₂]

/-- (54): the outcomes of folding a piece of wire. -/
inductive FoldOutcome where
  | noImpingement
  | slightlyBent
  | halfwayBent
  | greatlyBent
  | damagedBeyondRepair
  deriving DecidableEq

-- (60b)
theorem one_lt_encard_univ_foldOutcome : 1 < (Set.univ : Set FoldOutcome).encard :=
  Set.one_lt_encard_iff_nontrivial.2
    ⟨.noImpingement, trivial, .halfwayBent, trivial, by decide⟩

-- (74): *unfold*
theorem un_fold :
    un (andBack FoldOutcome.noImpingement .halfwayBent) once Set.univ () ev₂ = .true :=
  un_andBack_eq_true_iff.2 one_lt_encard_univ_foldOutcome

end Examples

end Bhadra2024
