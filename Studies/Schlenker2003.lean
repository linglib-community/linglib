module

public import Linglib.Semantics.Reference.Context.Tower
public import Linglib.Semantics.Reference.Context.Shifts
public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Semantics.Reference.Kaplan

/-!
# Schlenker (2003): A Plea for Monsters

Schlenker treats attitude verbs as quantifiers over contexts. Kaplan's Fixity Thesis holds that
an indexical's value is fixed by the context of the actual speech act, so that no operator shifts
contexts (`SatisfiesFixity`); Amharic, where the first person under *say* denotes the reported
speaker, is the counterexample. An attitude verb therefore quantifies over contexts of the
reported speech act or thought (`ContextBox`), with the holder as agent and the accessible world
as world (`reportedContext`), and Hintikka's quantification over worlds is the case where the
embedded meaning reads only the world (`contextBox_world_only`, `doxastic_holdsAt_iff_contextBox`).
English *I* resolves to the origin agent under any shift and Amharic *I* to the innermost agent
(`english_I_invariant`, `amharicI_ne_I`), so *Bob said that I am happy* is false read as English
and true read as Amharic in a two-person model (`english_amharic_differ`). A logophoric pronoun
is the author of an embedded context who is not the actual speaker (`Logophoric`).

## Implementation notes

The paper's context variables and its syntactic filtering of shiftable from non-shiftable
indexicals are not modelled; shiftability is the choice between the origin and the innermost
access pattern of `Semantics/Reference/Context/Tower`. Quantification over the accessible worlds
is the relational box of `Logic/Modal/Defs`, decidable over finitely many worlds. A monstrous
operator whose embedded meaning consumes the whole shifted tower, needed for mixed origin and
local readings, is not defined.

## References

* [schlenker-2003]
* [kaplan-1989]
* [hintikka-1962]
-/

@[expose] public section

namespace Schlenker2003

open ModalLogic Kaplan ContextTower
open scoped SetRel

variable {W E P T : Type*}

/-! ### The context of the reported speech act -/

/-- The context of the reported speech act ([schlenker-2003] (4)): push
    the attitude shift onto the tower and read the innermost context:
    the holder becomes the agent, the accessible world the world, and
    the remaining coordinates are inherited. -/
def reportedContext (t : ContextTower (Context W E P T)) (holder : E)
    (w' : W) : Context W E P T :=
  (t.push (attitudeShift holder w')).innermost

@[simp] theorem reportedContext_world
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').world = w' := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_agent
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').agent = holder := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_time
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').time = t.innermost.time := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_position
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').position = t.innermost.position := by
  simp [reportedContext, attitudeShift]

@[simp] theorem reportedContext_addressee
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    (reportedContext t holder w').addressee = t.innermost.addressee := by
  simp [reportedContext, attitudeShift]

/-! ### Context quantification -/

/-- `ContextBox R holder φ t w` iff at every world `R holder`-accessible from `w` the embedded
    meaning `φ` holds of the context of the reported speech act: [schlenker-2003]'s attitude
    verb quantifying over contexts, the box over the reported contexts. -/
def ContextBox (R : E → SetRel W W) (holder : E) (φ : Context W E P T → Prop)
    (t : ContextTower (Context W E P T)) : W → Prop :=
  □[R holder] fun w' ↦ φ (reportedContext t holder w')

instance [Fintype W] (R : E → SetRel W W) (holder : E) (φ : Context W E P T → Prop)
    [DecidablePred φ] (t : ContextTower (Context W E P T)) (w : W)
    [∀ v, Decidable (w ~[R holder] v)] : Decidable (ContextBox R holder φ t w) :=
  inferInstanceAs (Decidable (□[R holder] (fun w' ↦ φ (reportedContext t holder w')) w))

/-- With a world-only meaning, context quantification is Hintikka world
    quantification, the sense in which [hintikka-1962]'s semantics is
    a special case of [schlenker-2003]'s. -/
theorem contextBox_world_only (R : E → SetRel W W) (holder : E) (p : W → Prop)
    (t : ContextTower (Context W E P T)) :
    ContextBox R holder (fun c ↦ p c.world) t = □[R holder] p := by
  simp only [ContextBox, reportedContext_world]

/-- `DoxasticPredicate.HoldsAt` is a factivity and a veridicality requirement plus context
    quantification over a world-only meaning, so every doxastic predicate of `Doxastic.lean` is
    a special case of [schlenker-2003]'s context quantification. -/
theorem doxastic_holdsAt_iff_contextBox (V : Doxastic.DoxasticPredicate W E) (agent : E)
    (p : W → Prop) (w : W) (t : ContextTower (Context W E P T)) :
    V.HoldsAt agent p w ↔
      (∀ _ ∈ V.factivity, p w) ∧ Doxastic.VeridicalityHolds V.veridicality p w ∧
        ContextBox V.access agent (fun c ↦ p c.world) t w := by
  rw [contextBox_world_only]
  exact V.holdsAt_iff agent p w

/-! ### The Fixity Thesis -/

/-- The Fixity Thesis, [schlenker-2003] (1): "the semantic value of an
    indexical is fixed solely by the context of the actual speech act,
    and cannot be affected by any logical operators." Rendered on
    tower-parameterized meanings: the truth value is independent of the
    tower configuration. It holds of every meaning of a monster-free
    language and fails for the shift-reading meanings of the paper's
    monster-friendly logics (Appendix B). -/
def SatisfiesFixity (φ : ContextTower (Context W E P T) → W → Prop) : Prop :=
  ∀ (t₁ t₂ : ContextTower (Context W E P T)) (w : W), φ t₁ w ↔ φ t₂ w

/-- World-only meanings satisfy the Fixity Thesis. -/
theorem fixity_world_only (p : W → Prop) :
    SatisfiesFixity (W := W) (E := E) (P := P) (T := T)
      (fun _ w ↦ p w) :=
  fun _ _ _ ↦ Iff.rfl

/-! ### Shifted indexicals -/

/-- English *I* is invariant under the attitude shift used by
    `ContextBox`: it resolves to the origin agent (the actual
    speaker), not the attitude holder. -/
theorem english_I_invariant
    (t : ContextTower (Context W E P T)) (holder : E) (w' : W) :
    Kaplan.I.resolve (t.push (attitudeShift holder w')) = Kaplan.I.resolve t :=
  AccessPattern.stable_origin _ _ t

/-- Amharic *I* ([schlenker-2003] §3): the agent of the innermost context, so under an
    attitude shift the attitude holder. -/
def amharicI : AccessPattern (Context W E P T) E := .innermost Context.agent

/-- The paper's counterexample to Kaplan's thesis is that under an attitude shift to a holder
    other than the speaker, Amharic *I* and English *I* resolve differently. -/
theorem amharicI_ne_I (c : Context W E P T) (holder : E) (w' : W) (h : c.agent ≠ holder) :
    amharicI.resolve ((ContextTower.root c).push (attitudeShift holder w')) ≠
      Kaplan.I.resolve ((ContextTower.root c).push (attitudeShift holder w')) := by
  simpa [amharicI, Kaplan.I] using h.symm

/-! ### Person features as presuppositions -/

/-- The paper's `+author(x, cᵢ)` says that `x` is the agent of the context at depth `d`, and
    `+author*(x)` is the case `d = .origin`. -/
def AuthorAt (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) : Prop :=
  x = (AccessPattern.mk d Context.agent).resolve t

/-- A logophoric pronoun (§6) is `+author(x, cᵢ) ∧ −author*(x)`, the agent of the embedded
    context who is not the actual speaker. -/
def Logophoric (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) : Prop :=
  AuthorAt d x t ∧ ¬ AuthorAt .origin x t

instance [DecidableEq E] (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) :
    Decidable (AuthorAt d x t) := by
  unfold AuthorAt; infer_instance

instance [DecidableEq E] (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) :
    Decidable (Logophoric d x t) := by
  unfold Logophoric; infer_instance

/-- Under an attitude shift, a holder other than the speaker is logophoric at the local
    depth. -/
theorem logophoric_local_of_ne (t : ContextTower (Context W E P T)) (holder : E) (w' : W)
    (h : holder ≠ t.origin.agent) : Logophoric .local holder (t.push (attitudeShift holder w')) :=
  ⟨by simp [AuthorAt, AccessPattern.resolve], by simpa [AuthorAt, AccessPattern.resolve] using h⟩

/-- The actual speaker is never logophoric. -/
theorem not_logophoric_origin_agent (t : ContextTower (Context W E P T)) (d : DepthSpec) :
    ¬ Logophoric d t.origin.agent t :=
  fun h ↦ h.2 rfl

/-! ### A two-person, two-world model -/

/-- The speaker Alice and the attitude holder Bob. -/
inductive Person where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- The actual world and one alternative. -/
inductive World where
  | w0
  | w1
  deriving DecidableEq, Fintype, Repr

abbrev Ctx := Context World Person Unit Unit

/-- The context of the actual speech act: Alice speaking to Bob at the actual world. -/
def speechCtx : Ctx :=
  { agent := .alice, addressee := .bob, world := .w0, time := (), position := () }

/-- Bob's doxastic accessibility: both worlds are compatible with what he believes. -/
def bobBel : Person → SetRel World World
  | .bob => .univ
  | .alice => {p | p.2 = .w0}

instance : ∀ a w w', Decidable (w ~[bobBel a] w')
  | .bob, _, _ => inferInstanceAs (Decidable True)
  | .alice, _, w' => inferInstanceAs (Decidable (w' = .w0))

/-- Alice is happy only in the actual world; Bob is happy in both. -/
def isHappy : Person → World → Prop
  | .alice, .w0 => True
  | .alice, .w1 => False
  | .bob, _ => True

instance : ∀ p w, Decidable (isHappy p w) := by
  intro p w; cases p <;> cases w <;> simp [isHappy] <;> infer_instance

/-- *Bob said that I am happy* is false read as English, where *I* is Alice and the meaning
is world-only, and true read as Amharic, where *I* is the agent of the reported context:
context quantification is strictly more expressive than world quantification. -/
theorem english_amharic_differ :
    ¬ ContextBox bobBel .bob (fun c ↦ isHappy .alice c.world) (.root speechCtx) .w0 ∧
      ContextBox bobBel .bob (fun c ↦ isHappy c.agent c.world) (.root speechCtx) .w0 := by
  decide

end Schlenker2003
