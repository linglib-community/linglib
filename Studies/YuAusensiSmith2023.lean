module

public import Studies.BeaversEtAl2021
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Events.Closure
public import Linglib.Semantics.Mereology.Relation
public import Linglib.Data.Examples.YuAusensiSmith2023

/-!
# Yu, Ausensi & Smith (2023): States and Changes-of-State in the Semantics of Result Roots

This file formalizes the account of result roots by Yu, Ausensi and Smith. Beavers and
Koontz-Garboden's two classes of result roots, property concept roots and the roots that entail
change, here called change-of-state roots, differ in semantic type. A property concept root, such
as that of *open*, relates an individual to a state (20); a change-of-state root, such as that of
*break*, relates an individual to an event of change into the state it names (19)
(`Analysis.denote`). Events and states are sorts of one domain of eventualities (`Model`), and the
sorts restrict the variables of the denotations, not the relations of becoming and causing.

Every argument of the paper is that a predicate of states and a predicate of events are disjoint.
*Again* on a change-of-state root presupposes an earlier event wherever it attaches
(`again_changeOfState`), a *for*-phrase finds no state of the root to measure, and a root that
holds of states cannot modify a causative verb phrase by Event Identification
(`eventIdentification_causative_eq_bot`). So the sort of the root decides each reading
(`available_iff`), the causative verb phrase over any root being realized, *Lucy broke the vase*
(21) among them. No reading the account cannot derive is accepted in the examples
(`rows_unavailable`), and every derivable one they reject is a resultative on a change-of-state
root (`rows_available`), whose deviance the paper puts down to direct causation and world
knowledge.

On Beavers and Koontz-Garboden's analysis a change-of-state root is a stative description that
entails change (`BeaversEtAl2021.resultStative`). *Again* cannot tell the analyses apart
(`again_beaversKoontzGarboden`), but theirs predicts the internal reading of a *for*-phrase that
the examples reject (`rows_beaversKoontzGarboden`). Its resultative conjoins the root with the
result phrase by Event Identification (55), which makes one state a state of both; once each
state has one holder, the Unique Role Requirement (56), the individual in the root's state is the
holder of the result (`holder_eq_of_up`). In their own two-sorted interpretations, read as one
domain, the restitutive reading of a root is their change-denial diagnostic and the internal
reading a state of their deverbal stative (`not_realized_restitutive_relativize`,
`realized_internal_relativize_iff`). On this analysis the holder of the root's state is
existentially closed in a state of its own, so in *a couple of monks broke the corpse loose from
the deck* it is the deck that breaks (`Monks.sentence`).

## Implementation notes

* The causative head vCAUSE is `EventStructure.Interpretation.vCause` restricted to events
  (`Model.causative`). It introduces no individual and quantifies over a caused eventuality of
  either sort (footnote 7).
* In two-sorted interpretations `cause` relates events, so the causative head cannot take a stative
  complement as in (22), Harley's structure without vBECOME (footnote 8); the readings at the verb
  phrase are compared in one-domain models.
* The existential closure of the holder at the verb phrase is `Event.closure` of the flipped
  relation, and the agent of (33) is the effector of the change (footnote 17).
* Beavers and Koontz-Garboden's first objection to (55), that one state cannot carry two
  unrelated descriptions, is an intuition the paper does not make precise; only the second, the
  Unique Role Requirement, is formalized.

## TODO

* Direct causation (pp. 1609–1610) is not represented, since `cause` is uninterpreted.
* The part-whole construals of (40)–(41) and the state-specifying result phrases of (47)–(48) are
  not represented.
* Footnote 11 records a reviewer who accepts internal readings in context, the only diagnostic
  that tells the two analyses apart.

## References

* [yu-ausensi-smith-2023]
* [beavers-koontz-garboden-2020]
* [kratzer-1996]
* [landman-2000]
-/

@[expose] public section

namespace YuAusensiSmith2023

open ArgumentStructure ArgumentStructure.EventStructure ModalLogic Presupposition
open scoped SetRel

/-- An interpretation of the event-structure primitives over one domain of eventualities, with
the states among them (footnote 6). -/
structure Model (Entity Ev : Type*) extends Interpretation Entity Ev Ev where
  /-- The eventuality is a state. -/
  IsState : Ev → Prop

/-- The two classes of result roots (footnotes 1 and 4). -/
inductive RootClass
  /-- Roots that do not entail change, such as that of *open*. -/
  | propertyConcept
  /-- Roots that entail change, Beavers and Koontz-Garboden's result roots, such as that of
  *break*. -/
  | changeOfState
  deriving DecidableEq

/-- The two analyses of change-of-state roots. -/
inductive Analysis
  | yuAusensiSmith
  | beaversKoontzGarboden
  deriving DecidableEq

/-! ### Roots and their sorts -/

section Roots

variable {Entity Ev : Type*} (M : Model Entity Ev)

/-- The causative head vCAUSE (21), (22): the events that cause an eventuality of `P`. -/
def Model.causative (P : Ev → Prop) : Ev → Prop := M.vCause P ⊓ M.IsStateᶜ

/-- The root of a class with state description `B`. A property concept root relates an
individual to a state of `B` (20). A change-of-state root relates an individual to an event of
change into a state of `B` (19) on this paper's analysis, and to a state of `B` that a change gave
rise to (54a) on Beavers and Koontz-Garboden's. -/
def Analysis.denote : Analysis → RootClass → (Entity → Ev → Prop) → Entity → Ev → Prop
  | _, .propertyConcept, B, x => B x ⊓ M.IsState
  | .yuAusensiSmith, .changeOfState, B, x => M.vBecome B x ⊓ M.IsStateᶜ
  | .beaversKoontzGarboden, .changeOfState, B, x =>
    BeaversEtAl2021.resultStative M.toInterpretation B x ⊓ M.IsState

/-- The root describes states: always on Beavers and Koontz-Garboden's analysis, and on this one
when it is a property concept root. -/
def Analysis.DescribesStates : Analysis → RootClass → Prop
  | .yuAusensiSmith, c => c = .propertyConcept
  | .beaversKoontzGarboden, _ => True

instance : ∀ a c, Decidable (Analysis.DescribesStates a c)
  | .yuAusensiSmith, c => inferInstanceAs (Decidable (c = _))
  | .beaversKoontzGarboden, _ => inferInstanceAs (Decidable True)

variable {M} {a : Analysis} {c : RootClass}

theorem Analysis.denote_le_isState (h : a.DescribesStates c) (B : Entity → Ev → Prop)
    (x : Entity) : a.denote M c B x ≤ M.IsState := by
  cases a <;> cases c
  · exact inf_le_right
  · cases h
  all_goals exact inf_le_right

theorem Analysis.denote_le_compl (h : ¬ a.DescribesStates c) (B : Entity → Ev → Prop)
    (x : Entity) : a.denote M c B x ≤ M.IsStateᶜ := by
  cases a <;> cases c
  · exact absurd rfl h
  · exact inf_le_right
  all_goals exact absurd trivial h

theorem Model.causative_le_compl (P : Ev → Prop) : M.causative P ≤ M.IsStateᶜ := inf_le_right

/-- A root that holds of states, a property concept root among them, cannot modify a causative
verb phrase by Event Identification (30), (31). -/
theorem eventIdentification_causative_eq_bot {ρ : Entity → Ev → Prop} (hρ : ∀ x, ρ x ≤ M.IsState)
    (L : Ev → Prop) : eventIdentification ρ (M.causative L) = ⊥ :=
  eventIdentification_eq_bot_iff.2 fun x ↦ disjoint_compl_right.mono (hρ x) inf_le_right

end Roots

/-! ### *Again* -/

section Again

variable {Entity Ev : Type*} {M : Model Entity Ev} {R : SetRel Ev Ev} {P : Ev → Prop} {v : Ev}

theorem diamond_compl_of_again_ne_zero (hP : P ≤ M.IsStateᶜ) (h : again R P v ≠ 0) :
    ◇[R] M.IsStateᶜ v :=
  diamond_mono R hP v (again_ne_zero_iff.1 h)

variable (B : Entity → Ev → Prop) (x : Entity)

/-- *Again* on a change-of-state root presupposes an earlier event wherever it attaches, so the root
has no restitutive reading (25). -/
theorem again_changeOfState :
    (again R (Analysis.yuAusensiSmith.denote M .changeOfState B x) v ≠ 0 →
        ◇[R] M.IsStateᶜ v) ∧
      (again R (M.causative (Analysis.yuAusensiSmith.denote M .changeOfState B x)) v ≠ 0 →
        ◇[R] M.IsStateᶜ v) :=
  ⟨diamond_compl_of_again_ne_zero (Analysis.denote_le_compl (by decide) B x),
    diamond_compl_of_again_ne_zero (Model.causative_le_compl _)⟩

/-- On Beavers and Koontz-Garboden's analysis, *again* on a change-of-state root presupposes an
earlier state resulting from a change (p. 1616). -/
theorem again_beaversKoontzGarboden
    (h : again R (Analysis.beaversKoontzGarboden.denote M .changeOfState B x) v ≠ 0) :
    ◇[R] (◇[M.become] ⊤) v :=
  diamond_mono R (fun _ hw ↦ hw.1.2) v (again_ne_zero_iff.1 h)

end Again

/-! ### Readings -/

/-- The readings the examples test. -/
inductive Reading
  /-- *Again* presupposes an earlier state that no change gave rise to. -/
  | restitutive
  /-- *Again* presupposes an earlier event of the verb phrase. -/
  | repetitive
  /-- A *for*-phrase measures an event of the verb phrase. -/
  | durative
  /-- A *for*-phrase measures a state of the root. -/
  | internal
  /-- The root modifies a causative verb phrase. -/
  | modifier
  deriving DecidableEq

section Realized

variable {Entity Ev : Type*} (M : Model Entity Ev) (L : Ev → Prop) (ρ : Entity → Ev → Prop)
  (x : Entity)

/-- The root `ρ`, applied to `x`, realizes the reading: the root holds of a state that no change
gave rise to, the causative verb phrase over it holds of an event, the root holds of a state, or
the root conjoined with a causative verb phrase over the result phrase `L` holds of an event. -/
def Reading.Realized : Reading → Prop
  | .restitutive => ∃ w, ρ x w ∧ M.IsState w ∧ ¬ ◇[M.become] ⊤ w
  | .repetitive | .durative => ∃ v, M.causative (ρ x) v
  | .internal => ∃ w, (ρ x ⊓ M.IsState) w
  | .modifier => ∃ v, eventIdentification ρ (M.causative L) x v

variable {M L ρ x}

theorem not_realized_restitutive_of_le_compl (h : ρ x ≤ M.IsStateᶜ) :
    ¬ Reading.restitutive.Realized M L ρ x :=
  fun ⟨w, hw, hs, _⟩ ↦ h w hw hs

theorem not_realized_restitutive_of_become (h : ρ x ≤ ◇[M.become] ⊤) :
    ¬ Reading.restitutive.Realized M L ρ x :=
  fun ⟨w, hw, _, hb⟩ ↦ hb (h w hw)

theorem not_realized_internal (h : ρ x ≤ M.IsStateᶜ) : ¬ Reading.internal.Realized M L ρ x :=
  fun ⟨w, hw, hs⟩ ↦ h w hw hs

theorem not_realized_modifier (h : ∀ y, ρ y ≤ M.IsState) : ¬ Reading.modifier.Realized M L ρ x :=
  fun ⟨v, hv⟩ ↦ (congrFun₂ (eventIdentification_causative_eq_bot h L) x v).mp hv

end Realized

/-- The reading `r` is available for a root of class `c` on the analysis `a` when some model
realizes it. -/
def Available (a : Analysis) (c : RootClass) (r : Reading) : Prop :=
  ∃ (Ev : Type) (M : Model Unit Ev) (B : Unit → Ev → Prop) (L : Ev → Prop),
    r.Realized M L (a.denote M c B) ()

/-- What the sort of the root predicts: the readings at the verb phrase always, the restitutive
reading for a root that entails no change, the internal reading for a root that describes states,
and the modifier for one that describes events. -/
def Analysis.Predicts (a : Analysis) (c : RootClass) : Reading → Prop
  | .restitutive => c = .propertyConcept
  | .repetitive | .durative => True
  | .internal => a.DescribesStates c
  | .modifier => ¬ a.DescribesStates c

instance (a : Analysis) (c : RootClass) : DecidablePred (a.Predicts c) := fun r ↦ by
  cases r <;> unfold Analysis.Predicts <;> infer_instance

/-! ### A scene for every available reading -/

/-- The eventualities of a scene: a causing event, the change it causes, the state the change
gives rise to, and an earlier state that no change gave rise to. -/
inductive Scene
  | causing
  | change
  | result
  | prior
  deriving DecidableEq

/-- The causing event causes the change and its state, and the change causes its state. -/
def scene : Model Unit Scene where
  become := {p | p.1 = .result ∧ p.2 = .change}
  cause := {p | p.1 = .causing ∧ (p.2 = .change ∨ p.2 = .result) ∨ p.1 = .change ∧ p.2 = .result}
  effector _ e := e = .causing
  IsState v := v = .result ∨ v = .prior

/-! ### Predictions -/

variable {a : Analysis} {c : RootClass}

private theorem available_of {r : Reading}
    (h : r.Realized scene (· = .result) (a.denote scene c fun _ ↦ scene.IsState) ()) :
    Available a c r :=
  ⟨Scene, scene, fun _ ↦ scene.IsState, (· = .result), h⟩

theorem available_restitutive_iff : Available a c .restitutive ↔ c = .propertyConcept := by
  refine ⟨fun ⟨_, M, B, L, h⟩ ↦ ?_, fun hc ↦ available_of ?_⟩
  · cases c
    · rfl
    · cases a
      · exact absurd h (not_realized_restitutive_of_le_compl
          (Analysis.denote_le_compl (by decide) B ()))
      · exact absurd h (not_realized_restitutive_of_become fun _ hw ↦ hw.1.2)
  · subst hc
    exact ⟨.prior, by cases a <;> simp [Analysis.denote, diamond_iff, scene]⟩

theorem available_internal_iff : Available a c .internal ↔ a.DescribesStates c := by
  refine ⟨fun ⟨_, M, B, L, h⟩ ↦ by_contra fun hd ↦
    not_realized_internal (Analysis.denote_le_compl hd B ()) h, fun h ↦ available_of ⟨.result, ?_⟩⟩
  cases a <;> cases c <;>
    simp_all [Analysis.DescribesStates, Analysis.denote, BeaversEtAl2021.resultStative, diamond_iff,
      scene]

theorem available_modifier_iff : Available a c .modifier ↔ ¬ a.DescribesStates c := by
  refine ⟨fun ⟨_, M, B, L, h⟩ hd ↦ not_realized_modifier (Analysis.denote_le_isState hd B) h,
    fun hd ↦ available_of ?_⟩
  cases a <;> cases c <;> simp only [Analysis.DescribesStates, not_true_eq_false] at hd
  exact ⟨.change, ⟨⟨.result, ⟨rfl, rfl⟩, .inl rfl⟩, by simp [scene]⟩,
    ⟨.result, .inr ⟨rfl, rfl⟩, rfl⟩, by simp [scene]⟩

-- (21), (22)
theorem available_durative : Available a c .durative := by
  refine available_of ⟨.causing, ?_, by simp [scene]⟩
  cases c
  · exact ⟨.result, .inl ⟨rfl, .inr rfl⟩, by cases a <;> simp [Analysis.denote, scene]⟩
  · cases a
    · exact ⟨.change, .inl ⟨rfl, .inl rfl⟩, ⟨.result, ⟨rfl, rfl⟩, .inl rfl⟩, by simp [scene]⟩
    · exact ⟨.result, .inl ⟨rfl, .inr rfl⟩, ⟨.inl rfl, .change, ⟨rfl, rfl⟩, trivial⟩, .inl rfl⟩

theorem available_iff : ∀ r, Available a c r ↔ a.Predicts c r
  | .restitutive => available_restitutive_iff
  | .repetitive => iff_of_true available_durative trivial
  | .durative => iff_of_true available_durative trivial
  | .internal => available_internal_iff
  | .modifier => available_modifier_iff

/-! ### Two sorts as one domain

Beavers and Koontz-Garboden's interpretations keep states and events as separate types. Such an
interpretation is a one-domain model over the sum of its sorts, the states on the left
(`relativize`), and a state predicate is a predicate on the left (`liftState`). Read through it,
their change-of-state root is their own deverbal stative and this paper's is their own
change-of-state head, on the event side (`denote_relativize_beaversKoontzGarboden`,
`denote_relativize_yuAusensiSmith`). The readings of the root are then
their own notions: a restitutive reading is a state that survives the denial of change, so their
change-of-state root has none (`not_realized_restitutive_relativize`), and an internal reading is a
state of the deverbal stative. -/

section Relativize

universe u

variable {Entity : Type*} {State Event : Type u} (N : Interpretation Entity State Event)

/-- The one-domain model of a two-sorted interpretation, on the sum of its sorts with the states
on the left. -/
def relativize : Model Entity (State ⊕ Event) where
  become := Prod.map Sum.inl Sum.inr '' N.become
  cause := Prod.map Sum.inr Sum.inr '' N.cause
  effector x := Sum.elim ⊥ (N.effector x)
  IsState v := v.isLeft

/-- A state predicate as a predicate of the sum of the sorts. -/
def liftState (P : Entity → State → Prop) (x : Entity) : State ⊕ Event → Prop := Sum.elim (P x) ⊥

variable {N} {P : Entity → State → Prop} {x : Entity}

theorem diamond_relativize_become_inl {q : State ⊕ Event → Prop} {s : State} :
    ◇[(relativize N).become] q (.inl s) ↔ ◇[N.become] (q ∘ .inr) s := by
  simp [diamond_iff, relativize]

theorem not_diamond_relativize_become_inr {q : State ⊕ Event → Prop} {e : Event} :
    ¬ ◇[(relativize N).become] q (.inr e) := by
  simp [diamond_iff, relativize]

theorem vBecome_relativize_inr {e : Event} :
    (relativize N).vBecome (liftState P) x (.inr e) ↔ N.vBecome P x e := by
  simp [Interpretation.vBecome_iff, relativize, liftState]

theorem not_vBecome_relativize_inl {s : State} :
    ¬ (relativize N).vBecome (liftState P) x (.inl s) := by
  simp [Interpretation.vBecome_iff, relativize, liftState]

theorem denote_relativize_propertyConcept (a : Analysis) :
    a.denote (relativize N) .propertyConcept (liftState P) = liftState P := by
  funext x v
  rcases v with s | e <;> cases a <;> simp [Analysis.denote, liftState, relativize]

theorem denote_relativize_beaversKoontzGarboden :
    Analysis.beaversKoontzGarboden.denote (relativize N) .changeOfState (liftState P) =
      liftState (BeaversEtAl2021.resultStative N P) := by
  funext x v
  rcases v with s | e
  · exact propext ⟨fun ⟨⟨hp, hd⟩, _⟩ ↦ ⟨hp, diamond_relativize_become_inl.1 hd⟩,
      fun ⟨hp, hd⟩ ↦ ⟨⟨hp, diamond_relativize_become_inl.2 hd⟩, rfl⟩⟩
  · exact propext ⟨fun h ↦ h.1.1, False.elim⟩

theorem denote_relativize_yuAusensiSmith :
    Analysis.yuAusensiSmith.denote (relativize N) .changeOfState (liftState P) =
      fun x ↦ Sum.elim ⊥ (N.vBecome P x) := by
  funext x v
  rcases v with s | e
  · exact propext ⟨fun h ↦ h.2 rfl, False.elim⟩
  · exact propext ⟨fun h ↦ vBecome_relativize_inr.1 h.1,
      fun h ↦ ⟨vBecome_relativize_inr.2 h, Bool.false_ne_true⟩⟩

variable {L : State ⊕ Event → Prop} {Q : Entity → State → Prop}

theorem realized_restitutive_liftState_iff :
    Reading.restitutive.Realized (relativize N) L (liftState Q) x ↔
      ∃ s, BeaversEtAl2021.DeniesChange N Q x s := by
  constructor
  · rintro ⟨s | e, hq, -, hn⟩
    · exact ⟨s, hq, fun h ↦ hn (diamond_relativize_become_inl.2 h)⟩
    · exact hq.elim
  · rintro ⟨s, hq, hn⟩
    exact ⟨.inl s, hq, rfl, fun h ↦ hn (diamond_relativize_become_inl.1 h)⟩

theorem realized_internal_liftState_iff :
    Reading.internal.Realized (relativize N) L (liftState Q) x ↔ ∃ s, Q x s :=
  ⟨fun ⟨v, hq, _⟩ ↦ match v, hq with | .inl s, hq => ⟨s, hq⟩,
    fun ⟨s, hq⟩ ↦ ⟨.inl s, hq, rfl⟩⟩

theorem not_realized_restitutive_relativize :
    ¬ Reading.restitutive.Realized (relativize N) L
      (Analysis.beaversKoontzGarboden.denote (relativize N) .changeOfState (liftState P)) x := by
  rw [denote_relativize_beaversKoontzGarboden, realized_restitutive_liftState_iff]
  exact fun ⟨_, h⟩ ↦ BeaversEtAl2021.not_deniesChange_resultStative N h

theorem realized_internal_relativize_iff :
    Reading.internal.Realized (relativize N) L
        (Analysis.beaversKoontzGarboden.denote (relativize N) .changeOfState (liftState P)) x ↔
      ∃ s, BeaversEtAl2021.resultStative N P x s := by
  rw [denote_relativize_beaversKoontzGarboden, realized_internal_liftState_iff]

-- (27), (29)
theorem changing_internal :
    Reading.internal.Realized (relativize BeaversKoontzGarboden2020.changing) ⊥
      (Analysis.beaversKoontzGarboden.denote (relativize BeaversKoontzGarboden2020.changing)
        .changeOfState (liftState fun _ _ ↦ True)) () :=
  realized_internal_relativize_iff.2 ⟨(), trivial, (), trivial, trivial⟩

end Relativize

/-! ### Resultatives -/

section Resultative

variable {Entity Ev : Type*} {M : Model Entity Ev} {ρ : Entity → Ev → Prop} {L : Ev → Prop}

-- (36), (37)
theorem exists_of_resultative {e : Ev}
    (h : Event.closure (flip (eventIdentification ρ (M.causative L))) e) : ∃ y, ρ y e :=
  let ⟨y, hρ, _⟩ := h
  ⟨y, hρ⟩

variable {B : Entity → Ev → Prop} {holder : Entity → Ev → Prop} {c x : Entity} {s : Ev}

/-- Under Event Identification (55) with unique holders (56), the individual in the change-of-state
root's state is the holder of the result. -/
theorem holder_eq_of_up (hU : Mereology.UP holder) (hB : B ≤ holder) (hL : L ≤ holder c)
    (h : eventIdentification (Analysis.beaversKoontzGarboden.denote M .changeOfState B) L x s) :
    x = c :=
  hU (hB x s h.1.1.1) (hL s h.2)

end Resultative

/-! ### Breaking the corpse loose -/

namespace Monks

/-- The participants of *a couple of monks broke the corpse loose from the deck*. -/
inductive Participant
  | monks
  | corpse
  | deck
  deriving DecidableEq

/-- The eventualities of the sentence: the breaking, the broken state of the deck, and the
corpse's state of being loose from it. -/
inductive Eventuality
  | breaking
  | broken
  | loose
  deriving DecidableEq

/-- The breaking gives rise to the broken state and causes the loose one, and the monks are its
effector. -/
def model : Model Participant Eventuality where
  become := {p | p.1 = .broken ∧ p.2 = .breaking}
  cause := {p | p.1 = .breaking ∧ p.2 = .loose}
  effector x e := x = .monks ∧ e = .breaking
  IsState v := v ≠ .breaking

/-- The deck holds the broken state and the corpse the loose one. -/
def holder (x : Participant) (v : Eventuality) : Prop :=
  x = .deck ∧ v = .broken ∨ x = .corpse ∧ v = .loose

/-- *Broken*. -/
def broken (x : Participant) (s : Eventuality) : Prop := holder x s ∧ s = .broken

/-- *The corpse loose from the deck*. -/
def looseFromDeck (s : Eventuality) : Prop := holder .corpse s ∧ s = .loose

theorem up_holder : Mereology.UP holder := by
  rintro x y v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, hv⟩ | ⟨rfl, hv⟩) <;> first | rfl | cases hv

/-- Sentence (34) makes the monks the agent of the deck's becoming broken, which causes the corpse
to be loose from the deck. -/
theorem sentence :
    eventIdentification model.effector
        (Event.closure (flip (eventIdentification
          (Analysis.yuAusensiSmith.denote model .changeOfState broken)
          (model.causative looseFromDeck)))) .monks .breaking ∧
      ∀ x, Analysis.yuAusensiSmith.denote model .changeOfState broken x .breaking ↔
        x = .deck := by
  refine ⟨⟨⟨rfl, rfl⟩, .deck, ⟨⟨.broken, ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, rfl⟩, ?_⟩,
    ⟨⟨.loose, ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, rfl⟩, ?_⟩⟩, fun x ↦ ?_⟩
  · simp [model]
  · simp [model]
  · cases x <;> simp [Analysis.denote, Interpretation.vBecome_iff, model, broken, holder]

end Monks

/-! ### The examples -/

/-- The class of a row's root. -/
def rootClass? (d : Datum) : Option RootClass :=
  d.parse? "root class"
    [("property concept", .propertyConcept), ("change of state", .changeOfState)]

/-- The readings a row tests, with their judgments: a resultative tests the modifier, judged as
the sentence, and the other rows the readings they name. -/
def tests (d : Datum) : List (Reading × Judgment) :=
  if d.feature? "diagnostic" = some "resultative modifier" then [(.modifier, d.judgment)]
  else d.readings.filterMap fun r ↦
    ([("restitutive", Reading.restitutive), ("repetitive", .repetitive),
      ("durative", .durative), ("internal", .internal)].lookup r.1).map (·, r.2)

theorem rows_unavailable : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    ¬ Available .yuAusensiSmith c t.1 → t.2 ≠ .acceptable := by
  simp only [available_iff]
  decide

/-- Every derivable reading the examples reject is a resultative on a change-of-state root, judged
so by a source the paper cites or, for (44), questionable. -/
theorem rows_available : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    Available .yuAusensiSmith c t.1 → t.2 ≠ .acceptable →
      t.1 = .modifier ∧ c = .changeOfState ∧
        (d.feature? "judgedBy" ≠ none ∨ t.2 = .questionable) := by
  simp only [available_iff]
  decide

/-- On Beavers and Koontz-Garboden's analysis, a non-modifier reading is accepted exactly when
available, except the internal reading of a change-of-state root (§4.1). -/
theorem rows_beaversKoontzGarboden : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    t.1 ≠ .modifier → ((t.2 = .acceptable ↔ Available .beaversKoontzGarboden c t.1) ↔
      ¬ (c = .changeOfState ∧ t.1 = .internal)) := by
  simp only [available_iff]
  decide

end YuAusensiSmith2023
