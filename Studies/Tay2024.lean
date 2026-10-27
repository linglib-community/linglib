module

public import Linglib.Data.Examples.Tay2024
public import Linglib.Fragments.Mandarin.Resultatives
public import Studies.Kim2024
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

/-!
# Tay (2024): Resultative Expressions in Mandarin Chinese

This file formalizes Tay's account of why Mandarin V-V resultatives realize their arguments
more freely than V-*de* resultatives and English resultatives. A V-V resultative is a
synthetic compound built in morphology, V1-∅-V2, so its components are inaccessible to
syntactic operations, chapter 2: a locative can modify V1 of a V-*de* resultative but not of
the compound, (45)–(46), and *repeatedly* has only the whole-event reading on the compound,
(41)–(44). The null affix ∅ introduces a macroevent containing a causing event described by V1
and a caused event described by V2, inherits every argument of V2, and existentially closes
every argument of V1 (110), `nullAffix`; the variant ∅+C also names the crucial contributory
factor of the macroevent (111), `nullAffixC`. The factor is a function of the macroevent, so a
change has one, `ccf_unique`, and V1's arguments are closed, so nothing relates the arguments
of the compound to those of V1, `nullAffix_of`: the external argument can be V1's agent
(131)–(132) or its theme (133)–(134), the internal argument need not be V1's agent
(202)–(206), and the sole argument of an unaccusative compound can be V1's agent (219),
which is why Mandarin has subject-oriented resultatives without a reflexive.

What does constrain the external argument is the Onset Condition of [kim-2024], (141): an event
integrated into the macroevent of a simplex causative is the initial event of its causal chain,
`Model.Onset`. The factor is a participant in that initial event, `Model.CcfInitial`, and
V1's event is integrated, so the factor is a participant in V1's event,
`participant_of_nullAffixC`: no pure causers (146)–(149), while subject matters are
participants (150)–(151). On the causal chain of *chén* 'sink' (136), *jī-chén* 'strike-sink'
names the onset and *\*chōng-chén* 'rush-sink' an event downstream of it, (137)–(140),
`onsetCondition_strike` and `not_onsetCondition_rush`: on a model of (136) the first meets the
Onset Condition and puts the Russian forces in V1's event, `ji_chen_participant`, and the second
violates it, `not_sinkingModel_rush_onset`. The rows carry the paper's reading of the
external argument, and a transitive compound is ungrammatical exactly where that reading is a
pure causer, `ungrammatical_iff_pureCauser`. The macroevent must contain the two subevents
rather than identify or nest them: in *shè-sǐ* 'shoot dead' (107) the shooting and the dying
overlap at the moment of contact only, so their traces are neither equal nor nested,
`shooting_trieventive`.
Chapter 8's typology varies whether the null head merges in morphology, whether the result X
can be a verb, and whether a transitive resultative takes an intransitive X; the third follows
from whether the language's change-of-state verbs alternate, since an intransitive one that
does not carries no factor and the null head supplies it, `ResultativeType.intransitiveX`,
with Mandarin's *pò* (684)–(686) the witness, `po_not_alternating`.

## Implementation notes

Predicates take their arguments as tuples `Fin n → D`, so a family of null affixes indexed by the
arities of V1 and V2 is one definition. The causal relation, the factor, the participant relation
and the causal chain of each macroevent, (136), are the primitives of a `Model`; the thesis takes
the causal relation to be Lewis's counterfactual causation and leaves its characterization open.
Events are partially ordered by causal precedence, the initial event of a chain is its least event,
and the Onset Condition is [kim-2024]'s, `Kim2024.OnsetCondition`. The model of (136) draws the
chain as a relation of immediate causation (`SinkingEvent.Causes`), ordered by its reflexive
transitive closure, so the macroevent, no link in the chain, is unordered with respect to its
subevents. Temporal traces are rational intervals. The compounds are entries of
`Fragments/Mandarin/Resultatives.lean`, which record no orientation: the apparent subject-oriented
transitives *chī-bǎo* (3) and *qí-lèi* (330) are the hybrid resultatives of chapter 4, whose
postverbal phrase is an argument of V2, and that chapter, the V-*de* construction's syntax (chapter
6), the case against the No Argument Theory (chapter 5) and the null head ∅+C+B for adjectival X
(693) are not formalized.

## References

* [tay-2024]
* [kim-2024]
-/

@[expose] public section

namespace Tay2024

open Mandarin Morphology

/-! ### The null affix (chapter 2, section 3.3) -/

section NullAffix

variable {E D : Type*} {m n : ℕ}

/-- The causal vocabulary of the null affix. `cause e e₁ e₂` says the macroevent `e` contains
the causing event `e₁` and the caused event `e₂`; `ccf e` is the crucial contributory factor
of `e`, the essential factor in bringing about its result, if `e` is a change with one,
`CCF(e) = c` in (111); `participant e x` says `x` is a participant in `e`; and `chain e` is the
causal chain of events that the macroevent `e` comprises (136). -/
structure Model (E D : Type*) where
  cause : E → E → E → Prop
  ccf : E → Option D
  participant : E → D → Prop
  chain : E → Set E

variable (M : Model E D)

/-- The null affix (110) introduces a macroevent `e` containing a causing event `e₁` described by
V1, whose arguments are existentially closed, and a caused event `e₂` described by V2, whose
arguments the compound inherits. -/
def nullAffix (R2 : E → (Fin n → D) → Prop) (R1 : E → (Fin m → D) → Prop) (e : E)
    (ys : Fin n → D) : Prop :=
  ∃ e₁ e₂ xs, M.cause e e₁ e₂ ∧ R2 e₂ ys ∧ R1 e₁ xs

/-- The null affix ∅+C (111) also names the crucial contributory factor of the macroevent,
which is an argument of the macroevent alone and enters no relation with the arguments of
V1. -/
def nullAffixC (R2 : E → (Fin n → D) → Prop) (R1 : E → (Fin m → D) → Prop) (e : E) (c : D)
    (ys : Fin n → D) : Prop :=
  M.ccf e = some c ∧ nullAffix M R2 R1 e ys

variable {M} {R2 : E → (Fin n → D) → Prop} {R1 : E → (Fin m → D) → Prop} {e e₁ e₂ : E}
  {c c' : D} {ys : Fin n → D} {xs : Fin m → D}

/-- Any arguments of V1 witness the compound, so the compound's arguments may but need not be V1's
((131)–(134), (202)–(206)). -/
theorem nullAffix_of (hc : M.cause e e₁ e₂) (h2 : R2 e₂ ys) (h1 : R1 e₁ xs) :
    nullAffix M R2 R1 e ys :=
  ⟨e₁, e₂, xs, hc, h2, h1⟩

-- (219)
theorem nullAffix_of_agent {R2 R1 : E → (Fin 1 → D) → Prop} {y : D} (hc : M.cause e e₁ e₂)
    (h2 : R2 e₂ ![y]) (h1 : R1 e₁ ![y]) : nullAffix M R2 R1 e ![y] :=
  nullAffix_of hc h2 h1

theorem ccf_unique {n' m' : ℕ} {R2' : E → (Fin n' → D) → Prop} {R1' : E → (Fin m' → D) → Prop}
    {ys' : Fin n' → D} (h : nullAffixC M R2 R1 e c ys) (h' : nullAffixC M R2' R1' e c' ys') :
    c = c' :=
  Option.some_injective D (h.1.symm.trans h'.1)

/-! ### The Onset Condition (chapter 3, section 2.2) -/

variable [PartialOrder E]

/-- The Onset Condition of [kim-2024], (141): the causing event integrated into the macroevent of
a simplex causative is the initial event of the macroevent's causal chain. -/
def Model.Onset : Prop := ∀ e e₁ e₂, M.cause e e₁ e₂ → Kim2024.OnsetCondition (M.chain e) e₁

/-- The crucial contributory factor is essential in bringing about the result, so it is a
participant in the initial event of the causal chain (145). -/
def Model.CcfInitial : Prop :=
  ∀ e c e₀, M.ccf e = some c → IsLeast (M.chain e) e₀ → M.participant e₀ c

/-- The external argument of a transitive compound participates in the event V1 describes, so there
are no pure causers ((146)–(149), (150)–(151)). -/
theorem participant_of_nullAffixC (hO : M.Onset) (hI : M.CcfInitial)
    (h : nullAffixC M R2 R1 e c ys) : ∃ e₁ xs, R1 e₁ xs ∧ M.participant e₁ c :=
  let ⟨hc, e₁, e₂, xs, hcause, _, h1⟩ := h
  ⟨e₁, xs, h1, hI e c e₁ hc (hO e e₁ e₂ hcause)⟩

end NullAffix

/-! ### The causal chain of *chén* 'sink', (136)–(140) -/

/-- The events of (136): the Russians strike the cruiser with a missile, seawater rushes into it,
it descends into the water, and it is below the surface of the sea; and the macroevent of
sinking that comprises them, which *chén* 'sink' denotes. -/
inductive SinkingEvent
  | strike
  | rush
  | descend
  | below
  | sink
  deriving DecidableEq, Fintype

namespace SinkingEvent

/-- The arrows of (136). The macroevent is no link in the chain, so it neither precedes nor
follows its subevents. -/
def Causes (a b : SinkingEvent) : Prop :=
  a = strike ∧ b = rush ∨ a = rush ∧ b = descend ∨ a = descend ∧ b = below

instance : DecidableRel Causes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The events in order of causal precedence. -/
instance : PartialOrder SinkingEvent :=
  partialOrderOfCovers Causes (OrderDual.toDual ∘ SinkingEvent.ctorIdx) (by decide)

instance : DecidableLE SinkingEvent := fun a b ↦
  inferInstanceAs (Decidable (Relation.ReflTransGen Causes a b))

/-- The causal chain the sinking comprises. -/
def chain : Set SinkingEvent := {strike, rush, descend, below}

end SinkingEvent

open SinkingEvent

/-- (137)–(138): in *jī-chén* 'strike-sink' V1 names the striking, the onset of the chain, so the
Onset Condition is met. -/
theorem onsetCondition_strike : Kim2024.OnsetCondition chain strike :=
  ⟨by simp [chain], fun e he ↦ by rcases he with rfl | rfl | rfl | rfl <;> decide⟩

/-- (139)–(140): in *\*chōng-chén* 'rush-sink' V1 would name the seawater rushing in, downstream of
the striking, so it cannot be the integrated event. -/
theorem not_onsetCondition_rush : ¬ Kim2024.OnsetCondition chain rush :=
  Kim2024.not_onsetCondition_of_lt onsetCondition_strike (lt_of_le_of_ne (by decide) (by decide))

/-- The participants of (135)–(140). -/
inductive Participant
  | russians
  | seawater
  | cruiser
  deriving DecidableEq

/-- The model of (136) on which V1 names the event `v1`: the sinking contains `v1` as its causing
event and the cruiser's being below the surface as its caused event, and its crucial
contributory factor is the Russian forces, who take part in the striking. -/
def sinkingModel (v1 : SinkingEvent) : Model SinkingEvent Participant where
  cause e e₁ e₂ := e = sink ∧ e₁ = v1 ∧ e₂ = below
  ccf e := if e = sink then some .russians else none
  participant e p := (e, p) ∈ [(strike, .russians), (strike, .cruiser), (rush, .seawater),
    (rush, .cruiser), (descend, .cruiser), (below, .cruiser)]
  chain e := if e = sink then chain else ∅

theorem sinkingModel_ccfInitial (v1 : SinkingEvent) : (sinkingModel v1).CcfInitial := by
  intro e c e₀ hc h₀
  obtain rfl : e = sink := by by_contra he; simp [sinkingModel, he] at hc
  obtain rfl : c = .russians := by simpa [sinkingModel] using hc.symm
  obtain rfl := h₀.unique onsetCondition_strike
  simp [sinkingModel]

theorem sinkingModel_strike_onset : (sinkingModel strike).Onset := by
  rintro e e₁ e₂ ⟨rfl, rfl, rfl⟩
  simpa [sinkingModel] using onsetCondition_strike

theorem not_sinkingModel_rush_onset : ¬ (sinkingModel rush).Onset := fun h ↦
  not_onsetCondition_rush (by simpa [sinkingModel] using h sink rush below ⟨rfl, rfl, rfl⟩)

/-- *jī* 'strike' and *chén* 'sink' on the events of (136). -/
def ji (e : SinkingEvent) (xs : Fin 2 → Participant) : Prop :=
  e = strike ∧ xs = ![.russians, .cruiser]

@[inherit_doc ji]
def chen (e : SinkingEvent) (ys : Fin 1 → Participant) : Prop := e = below ∧ ys = ![.cruiser]

/-- In (137) *Éjūn jī-chén-le yī sōu xúnyángjiàn* places the Russian forces in the event V1
describes. -/
theorem ji_chen_participant :
    ∃ e₁ xs, ji e₁ xs ∧ (sinkingModel strike).participant e₁ .russians :=
  participant_of_nullAffixC sinkingModel_strike_onset (sinkingModel_ccfInitial strike)
    (⟨rfl, strike, below, _, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩ :
      nullAffixC (sinkingModel strike) chen ji sink .russians ![.cruiser])

/-! ### The external argument in the data (chapter 3, sections 2.1–2.2) -/

/-- The paper's reading of the external argument of a transitive compound relative to V1. -/
inductive ExternalArgument
  | agent
  | theme
  | subjectMatter
  | pureCauser
  deriving DecidableEq

/-- The reading of the external argument a row records. -/
def externalArgument? (ex : Datum) : Option ExternalArgument :=
  ex.parse? "externalArgument"
    [("agent", .agent), ("theme", .theme), ("subjectMatter", .subjectMatter),
     ("pureCauser", .pureCauser)]

example : externalArgument? Examples.ex_146 = some .pureCauser := rfl

example : externalArgument? Examples.ex_150 = some .subjectMatter := rfl

theorem ungrammatical_iff_pureCauser :
    ∀ ex ∈ Examples.all, ∀ a ∈ externalArgument? ex,
      ex.judgment = .ungrammatical ↔ a = .pureCauser := by
  decide

/-! ### Trieventive structure (chapter 2, section 3.3) -/

section Traces

variable {E : Type*} (trace : E → Set ℚ)

/-- The temporal signature of the monoeventive analysis (104): V1 and V2 describe one event, so
one trace. -/
def Monoeventive (e₁ e₂ : E) : Prop := trace e₁ = trace e₂

/-- The temporal signature of the bieventive analyses (105)–(106): one event is a part of the
other, so one trace contains the other. -/
def Bieventive (e₁ e₂ : E) : Prop := trace e₂ ⊆ trace e₁ ∨ trace e₁ ⊆ trace e₂

/-- The events of *shè-sǐ* 'shoot dead' (107). -/
inductive Ev
  | shoot
  | die

/-- In the traces of (108) the shooting ends as the bullet makes contact, when the dying begins. -/
def shooting : Ev → Set ℚ
  | .shoot => Set.Icc 0 1
  | .die => Set.Icc 1 3

/-- The shooting and the dying of (107) are neither one event nor nested, so only a trieventive
macroevent fits. -/
theorem shooting_trieventive :
    ¬ Monoeventive shooting .shoot .die ∧ ¬ Bieventive shooting .shoot .die ∧
      (shooting .shoot ∩ shooting .die).Nonempty := by
  refine ⟨fun h ↦ ?_, ?_, ?_⟩
  · have := Set.ext_iff.1 h 0
    norm_num [shooting] at this
  · norm_num [Bieventive, shooting, Set.Icc_subset_Icc_iff]
  · norm_num [shooting, Set.Icc_inter_Icc, Set.nonempty_Icc]

end Traces

/-! ### The compound in morphology (chapter 2, section 2) -/

/-- The null affix as a morph is a phonologically empty prefix on V2. -/
def nullMorph : Morph := .pref ""

/-- The word V1-∅-V2 (130): ∅ affixed to V2, the result compounded with V1. -/
def vvTree (v1 v2 : Morph) : Word.Tree Morph :=
  .compound (.root v1) (.prefixed nullMorph (.root v2))

@[simp] theorem toList_vvTree (v1 v2 : Morph) : (vvTree v1 v2).toList = [v1, nullMorph, v2] :=
  rfl

/-- The word V1-∅-V2 of a compound of the fragment. -/
def word (c : Resultative) : Word.Tree Morph := vvTree (.root c.v1.form) (.root c.v2.form)

theorem toList_word_erase (c : Resultative) :
    (word c).toList.erase nullMorph = c.tree.toList.map (Morph.root ·.form) := by
  simp [word, nullMorph, Morph.root, Morph.pref]

/-! ### Typology (chapter 8) -/

/-- The parameters of the typology: whether the null head merges in morphology and whether the
result X can be a verb (section 2), and whether the language's deadjectival change-of-state
verbs have transitive counterparts (section 3.1), in which case its intransitive
change-of-state verbs are reflexivizations carrying their own crucial contributory factor
(692), and otherwise denote a becoming with none (686). -/
structure ResultativeType where
  compound : Bool
  verbalX : Bool
  alternating : Bool

namespace ResultativeType

/-- A transitive resultative takes an intransitive X iff X can be a verb that carries no
factor, so that the null head ∅+C supplies one (694), (697); an X carrying its own leaves none
for the head to introduce, since a change has one (section 3.3). -/
def intransitiveX (t : ResultativeType) : Bool := t.verbalX && !t.alternating

theorem verbalX_of_intransitiveX {t : ResultativeType} (h : t.intransitiveX) : t.verbalX :=
  (Bool.and_eq_true _ _ ▸ h).1

end ResultativeType

/-- Mandarin V-V resultatives are compounds with a verbal X, and its deadjectival
change-of-state verbs lack transitive counterparts (681)–(683), so a transitive resultative
takes an intransitive X, *dǎ-pò* (673). -/
def mandarin : ResultativeType := ⟨true, true, false⟩

/-- English resultatives are not compounds, X is never a verb (669), and *break* alternates
(676)–(677). -/
def english : ResultativeType := ⟨false, false, true⟩

/-- Japanese V-V resultatives are compounds with a verbal X, and its change-of-state verbs come
in transitive and unaccusative pairs (687)–(690), so a transitive resultative takes no
intransitive X (674)–(675). -/
def japanese : ResultativeType := ⟨true, true, true⟩

example : mandarin.intransitiveX = true := rfl

example : japanese.intransitiveX = false := rfl

/-- *pò* 'break' has no transitive frame (684)–(685), the datum behind Mandarin's parameter. -/
theorem po_not_alternating : ∀ fr ∈ po.valency.frames, ¬ fr.IsTransitive := by decide

end Tay2024
