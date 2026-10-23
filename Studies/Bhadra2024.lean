module

public import Mathlib.Data.Set.Subsingleton
public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Events.Basic

/-!
# Bhadra (2024): Verb roots encode outcomes

This file formalizes Bhadra's account of the reversative prefix *un-* and the restitutive prefix
*re-*. Every dynamic transitive root lexically carries a set of outcomes, the states its object can
be in at the right boundary of the event, while a contextual set of thresholds collects the states
an object can be in at the left boundary. Potential-for-change roots such as *fold*, *wrap* and
*coil* have several outcomes, change-of-state and impingement-effecting roots such as *break*,
*shatter* and *hit* have a single lexically specified outcome, and roots unspecified for change have
none. *Un-* presupposes a prior base event whose result the object is still in and several
outcomes, and asserts that the object returns to the base event's initial state. *Re-* presupposes
a prior base event with the same result and requires that the base action not leave the object
where that result cannot be restored. Cardinality thus governs *un-* alone and threshold structure
governs *re-*, so the two prefixes overlap exactly on the potential-for-change class.

The hierarchy of outcome sets cross-classifies Beavers's affectedness hierarchy. Beavers places the
impingement-effecting verbs with the potential-for-change verbs, while their single outcome puts
them with the change-of-state verbs, whose single outcome may be a quantized or a non-quantized
change.

## Implementation notes

* Each `VerbOutcomes` fixes its outcome and threshold sets once per root and object, so the
  object-dependence the paper locates at the minimal verb phrase is modelled by distinct records
  for distinct objects.
* The degrees of affectedness are those the paper reports for its classes of verbs, and it reports
  none for the transformation, movement and creation classes. Its critique of Beavers's definition
  of potential for change (§6.1) is not formalized.

## References

* [D. Bhadra, *Verb roots encode outcomes: argument structure and lexical semantics of reversal
  and restitution* (2024)][bhadra-2024]
* [J. Beavers, *On Affectedness* (2011)][beavers-2011]
-/

@[expose] public section

namespace Bhadra2024

open Event (τ)

open ArgumentStructure

/-! ### Outcome cardinality -/

/-- An outcome cardinality is the tier of an outcome set, ordered `empty < singleton < multi`
(62). -/
inductive OutcomeCardinality where
  | empty
  | singleton
  | multi
  deriving Repr, DecidableEq

namespace OutcomeCardinality

/-- `c.rank` is the rank of the tier `c` as a natural number. -/
def toNat : OutcomeCardinality → ℕ
  | .empty => 0
  | .singleton => 1
  | .multi => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder OutcomeCardinality := LinearOrder.lift' toNat toNat_injective

theorem empty_lt_singleton : empty < singleton := by decide
theorem singleton_lt_multi : singleton < multi := by decide

/-- The tier of an outcome set is `multi` when it is nontrivial, `empty` when it is empty, and
`singleton` otherwise. -/
noncomputable def ofSet {State : Type*} (O : Set State) : OutcomeCardinality :=
  open Classical in
  if O.Nontrivial then .multi else if O.Nonempty then .singleton else .empty

variable {State : Type*} {O : Set State}

theorem ofSet_eq_multi (h : O.Nontrivial) : ofSet O = .multi := by
  rw [ofSet, ite_eq_left h]

theorem ofSet_eq_singleton (hne : O.Nonempty) (hnt : ¬ O.Nontrivial) :
    ofSet O = .singleton := by
  rw [ofSet, ite_eq_right hnt, ite_eq_left hne]

theorem ofSet_eq_empty (h : ¬ O.Nonempty) : ofSet O = .empty := by
  rw [ofSet, ite_eq_right (fun hnt ↦ h hnt.nonempty), ite_eq_right h]

@[simp] theorem ofSet_singleton (s : State) : ofSet ({s} : Set State) = .singleton :=
  ofSet_eq_singleton ⟨s, rfl⟩ (by rw [Set.not_nontrivial_iff]; exact Set.subsingleton_singleton)

@[simp] theorem ofSet_empty : ofSet (∅ : Set State) = .empty :=
  ofSet_eq_empty (by simp)

end OutcomeCardinality

/-- An outcome class classifies dynamic transitive roots by what their outcome sets encode, the
potential-for-change class (60) and the classes with a lexically specified result or none
(61a–h). -/
inductive OutcomeClass where
  | potentialForChange
  | physicalProperty
  | transformation
  | movement
  | consumption
  | creation
  | degreeAchievement
  | impingement
  | noChange
  deriving DecidableEq, Repr

/-- The outcome tier of a class is multi-membered for potential-for-change roots, singleton for
every root with a lexically specified result, and empty for roots unspecified for change (62). -/
def OutcomeClass.tier : OutcomeClass → OutcomeCardinality
  | .potentialForChange => .multi
  | .noChange => .empty
  | _ => .singleton

theorem tier_eq_multi_iff (c : OutcomeClass) :
    c.tier = .multi ↔ c = .potentialForChange := by
  cases c <;> decide

/-! ### States, boundaries, and roots -/

/-- A state function gives an object's state at each time, a lifespan point (53). -/
abbrev StateFunction (Entity State T : Type*) := T → Entity → State

variable {Entity State T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-- `res(e)(x)` is the object's state at the right boundary of `e` (64). -/
def resState (k : StateFunction Entity State T) (e : E) (x : Entity) : State :=
  k (τ e).snd x

/-- `pre(e)(x)` is the object's state at the left boundary of `e` (65). -/
def preState (k : StateFunction Entity State T) (e : E) (x : Entity) : State :=
  k (τ e).fst x

/-- A verb root, as the prefixes see it, is its base predicate together with the lexical outcome
set of states at the right boundary and the contextual threshold set of states at the left boundary
((56), (60)). -/
structure VerbOutcomes (E Entity State : Type*) where
  /-- The base predicate `P(e)(x)`. -/
  verb : E → Entity → Prop
  /-- The outcome set `O`. -/
  outcomes : Set State
  /-- The threshold set `T`. -/
  thresholds : Set State

/-- The cardinality of a root is the tier of its outcome set. -/
noncomputable def VerbOutcomes.cardinality (vro : VerbOutcomes E Entity State) :
    OutcomeCardinality :=
  OutcomeCardinality.ofSet vro.outcomes

/-! ### The prefixes as result-state modifiers -/

/-- Reversative *un-* (66) requires a prior base event `e'` whose result is the state the *un-*
event starts from and a multi-membered outcome set, and returns the object to the base event's
initial state. The vacuous `∃ Q. Q(e)(x)` of the assertion is dropped. -/
def unSem (k : StateFunction Entity State T) (vro : VerbOutcomes E Entity State)
    (e : E) (x : Entity) : Prop :=
  ∃ e' : E,
    vro.verb e' x ∧
    (τ e').Precedes (τ e) ∧
    resState k e' x = preState k e x ∧
    vro.outcomes.Nontrivial ∧
    resState k e x = preState k e' x

/-- Restitutive *re-* ((68), (72)) requires a prior base event `e'` with the same result, whose
result state is an admissible start state, so that the base action does not leave the object where
its result cannot be restored, and requires the base predicate to hold of the *re-* event. It
places no demand on the cardinality of the outcome set. -/
def reSem (k : StateFunction Entity State T) (vro : VerbOutcomes E Entity State)
    (e : E) (x : Entity) : Prop :=
  (∃ e' : E,
    vro.verb e' x ∧
    (τ e').Precedes (τ e) ∧
    resState k e x = resState k e' x ∧
    resState k e' x ∈ vro.thresholds) ∧
  vro.verb e x

/-- A root whose outcome set is not multi-membered cannot host *un-* (67). -/
theorem subsingleton_blocks_un (k : StateFunction Entity State T)
    (vro : VerbOutcomes E Entity State) (h : ¬ vro.outcomes.Nontrivial)
    (e : E) (x : Entity) : ¬ unSem k vro e x :=
  fun ⟨_, _, _, _, hnt, _⟩ ↦ h hnt

theorem singleton_blocks_un (k : StateFunction Entity State T)
    (vro : VerbOutcomes E Entity State) (s : State) (hs : vro.outcomes = {s})
    (e : E) (x : Entity) : ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_singleton) e x

theorem empty_blocks_un (k : StateFunction Entity State T)
    (vro : VerbOutcomes E Entity State) (hs : vro.outcomes = ∅)
    (e : E) (x : Entity) : ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_empty) e x

theorem un_requires_multi (k : StateFunction Entity State T)
    (vro : VerbOutcomes E Entity State) (e : E) (x : Entity)
    (h : unSem k vro e x) : vro.cardinality = .multi :=
  let ⟨_, _, _, _, hnt, _⟩ := h
  OutcomeCardinality.ofSet_eq_multi hnt

/-- A base action whose result is never an admissible start state blocks *re-* (72). -/
theorem not_reSem_of_outcome_not_threshold (k : StateFunction Entity State T)
    (vro : VerbOutcomes E Entity State) (x : Entity)
    (h : ∀ e', vro.verb e' x → resState k e' x ∉ vro.thresholds) (e : E) :
    ¬ reSem k vro e x :=
  fun ⟨⟨e', hv, _, _, hT⟩, _⟩ ↦ h e' hv hT

/-! ### Worked roots -/

section Examples

/-- `ev₁` is the base event of the scenario, over `[0, 5]`. -/
def ev₁ : NonemptyInterval ℤ := ⟨⟨0, 5⟩, by omega⟩

/-- `ev₂` is the prefixed event of the scenario, over `[10, 15]`. -/
def ev₂ : NonemptyInterval ℤ := ⟨⟨10, 15⟩, by omega⟩

private theorem ev₁_precedes_ev₂ : (τ ev₁).Precedes (τ ev₂) := by
  show (5 : ℤ) < 10; omega

/-- The base predicate of every worked root holds of the scenario's two events. -/
def acts : NonemptyInterval ℤ → Unit → Prop := fun e _ ↦ e = ev₁ ∨ e = ev₂

private theorem acts_ev₁ : acts ev₁ () := Or.inl rfl
private theorem acts_ev₂ : acts ev₂ () := Or.inr rfl

/-- A root whose action carries the object from `start` to `result` at the base event and
again at the prefixed event, both acting on the same object. -/
def twice {State : Type*} (start result : State) : StateFunction Unit State ℤ :=
  fun t _ ↦ if t ≤ 0 then start else result

/-- A root whose action carries the object from `start` to `result` at the base event and
back to `start` at the prefixed event. -/
def andBack {State : Type*} (start result : State) : StateFunction Unit State ℤ :=
  fun t _ ↦ if t ≤ 0 then start else if t ≤ 10 then result else start

/-- A parchment under folding is flat, slightly creased, folded or tightly folded (54). -/
inductive ParchmentState where
  | flat | slightlyCreased | folded | tightlyFolded
  deriving DecidableEq, Repr

/-- *Fold* is a potential-for-change root (60), with a multi-membered outcome set, and a folded
parchment can be folded again. -/
def foldVRO : VerbOutcomes (NonemptyInterval ℤ) Unit ParchmentState where
  verb := acts
  outcomes := {.slightlyCreased, .folded, .tightlyFolded}
  thresholds := {.flat, .slightlyCreased, .folded}

theorem fold_outcomes_multi : foldVRO.outcomes.Nontrivial :=
  ⟨.slightlyCreased, by simp [foldVRO], .folded, by simp [foldVRO], by decide⟩

/-- *Veena unfolded the parchment* is true in the scenario, the worked derivation of (66). -/
theorem fold_un : unSem (andBack .flat .folded) foldVRO ev₂ () :=
  ⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl, fold_outcomes_multi, rfl⟩

theorem fold_re : reSem (twice .flat .folded) foldVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [foldVRO, resState, twice, ev₁]⟩, acts_ev₂⟩

inductive LimbState where
  | intact | broken
  deriving DecidableEq, Repr

/-- *Break* applied to a limb (61a) has a single result, and a broken limb admits another breaking
(73a). -/
def breakLimbVRO : VerbOutcomes (NonemptyInterval ℤ) Unit LimbState where
  verb := acts
  outcomes := {.broken}
  thresholds := {.intact, .broken}

/-- *Break* applied to a sewer has the same single result, which a sewer cannot informatively reach
again (73a). -/
def breakSewerVRO : VerbOutcomes (NonemptyInterval ℤ) Unit LimbState where
  verb := acts
  outcomes := {.broken}
  thresholds := {.intact}

/-- *#Unbreak a limb* fails, the outcome set being a singleton (67). -/
theorem breakLimb_not_un (k : StateFunction Unit LimbState ℤ) (e : NonemptyInterval ℤ) :
    ¬ unSem k breakLimbVRO e () :=
  singleton_blocks_un k breakLimbVRO .broken rfl e ()

/-- *Rebreak a limb* is true in the scenario (73a). -/
theorem breakLimb_re : reSem (twice .intact .broken) breakLimbVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [breakLimbVRO, resState, twice, ev₁]⟩, acts_ev₂⟩

/-- *#Rebreak a sewer* fails, since a broken sewer is not an admissible start state (73a). -/
theorem breakSewer_not_re (e : NonemptyInterval ℤ) :
    ¬ reSem (twice .intact .broken) breakSewerVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' ↦ by
    rcases he' with rfl | rfl <;> simp [breakSewerVRO, resState, twice, ev₁, ev₂]) e

inductive SurfaceState where
  | unaltered | surfaceAltered
  deriving DecidableEq, Repr

/-- *Hit* is an impingement-effecting root (61g), with a single, irreversible surface alteration.
-/
def hitVRO : VerbOutcomes (NonemptyInterval ℤ) Unit SurfaceState where
  verb := acts
  outcomes := {.surfaceAltered}
  thresholds := {.unaltered}

/-- *\*Unhit* fails (25). -/
theorem hit_not_un (k : StateFunction Unit SurfaceState ℤ) (e : NonemptyInterval ℤ) :
    ¬ unSem k hitVRO e () :=
  singleton_blocks_un k hitVRO .surfaceAltered rfl e ()

/-- *\*Rehit* fails, since impingement leaves the surface altered and never again unaltered (48).
-/
theorem hit_not_re (e : NonemptyInterval ℤ) :
    ¬ reSem (twice .unaltered .surfaceAltered) hitVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' ↦ by
    rcases he' with rfl | rfl <;> simp [hitVRO, resState, twice, ev₁, ev₂]) e

inductive TruckState where
  | empty | full
  deriving DecidableEq, Repr

/-- *Load* is a degree achievement (70), with a single contextually salient result that does not
prevent loading again. -/
def loadVRO : VerbOutcomes (NonemptyInterval ℤ) Unit TruckState where
  verb := acts
  outcomes := {.full}
  thresholds := {.empty, .full}

/-- *Raj reloaded the truck* is true in the scenario (69a). -/
theorem load_re : reSem (twice .empty .full) loadVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [loadVRO, resState, twice, ev₁]⟩, acts_ev₂⟩

inductive MirrorState where
  | intact | shattered
  deriving DecidableEq, Repr

/-- *Shatter* (71) has a single result that leaves the object outside every threshold. -/
def shatterVRO : VerbOutcomes (NonemptyInterval ℤ) Unit MirrorState where
  verb := acts
  outcomes := {.shattered}
  thresholds := {.intact}

/-- *#The children reshattered the mirror* fails (69b). -/
theorem shatter_not_re (e : NonemptyInterval ℤ) :
    ¬ reSem (twice .intact .shattered) shatterVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' ↦ by
    rcases he' with rfl | rfl <;> simp [shatterVRO, resState, twice, ev₁, ev₂]) e

theorem re_on_singleton :
    loadVRO.cardinality = .singleton ∧ reSem (twice .empty .full) loadVRO ev₂ () :=
  ⟨by simp [VerbOutcomes.cardinality, loadVRO], load_re⟩

end Examples

/-! ### The affectedness hierarchy (§2.4, (20), (62)) -/

/-- `BeaversDegree c d` holds when the paper places verbs of the class `c` at the degree `d` of
Beavers's affectedness hierarchy ((20), §2.4.2). -/
inductive BeaversDegree : OutcomeClass → AffectednessDegree → Prop
  /-- *Break* undergoes a quantized change ((20a)). -/
  | physicalProperty : BeaversDegree .physicalProperty .quantized
  /-- *Destroy* and *devour* effect a quantized change ((20a)). -/
  | consumption : BeaversDegree .consumption .quantized
  /-- Degree achievements effect a non-quantized change ((20b)). -/
  | degreeAchievement : BeaversDegree .degreeAchievement .nonquantized
  /-- *Wrap* and *furl* give their object potential for change ((20d)). -/
  | potentialForChange : BeaversDegree .potentialForChange .potential
  /-- Beavers places surface-contact verbs such as *hit* and *wipe* under potential for change, a
  placement the paper rejects in separating them as impingement-effecting (§2.4.2). -/
  | impingement : BeaversDegree .impingement .potential
  /-- *See* and *laugh at* are unspecified for change ((20c)). -/
  | noChange : BeaversDegree .noChange .unspecified

/-- Potential-for-change and impingement-effecting verbs share a degree of affectedness but not an
outcome tier, which is why the paper separates them (§2.4.2, (62)). -/
theorem potentialForChange_impingement :
    (∃ d, BeaversDegree .potentialForChange d ∧ BeaversDegree .impingement d) ∧
      OutcomeClass.potentialForChange.tier ≠ OutcomeClass.impingement.tier :=
  ⟨⟨.potential, .potentialForChange, .impingement⟩, by decide⟩

/-- Consumption verbs and degree achievements share the singleton tier but not a degree of
affectedness, the tier of lexically specified change including quantized and non-quantized change
((62)). -/
theorem consumption_degreeAchievement :
    OutcomeClass.consumption.tier = OutcomeClass.degreeAchievement.tier ∧
      ∃ d d', d ≠ d' ∧ BeaversDegree .consumption d ∧ BeaversDegree .degreeAchievement d' :=
  ⟨rfl, .quantized, .nonquantized, by decide, .consumption, .degreeAchievement⟩

end Bhadra2024
