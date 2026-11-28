module

public import Linglib.Logic.Modal.Index
public import Linglib.Semantics.Aspect.Progressive
public import Linglib.Semantics.Events.Closure
public import Linglib.Semantics.Modality.Basic
public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Syntax.Cartography.Clause
public import Linglib.Data.Examples.RamchandSvenonius2014
public import Mathlib.Data.Part

/-!
# Ramchand and Svenonius (2014): Deriving the functional hierarchy

A clause is built from descriptions of three sorts. An event description is a predicate of events
at a world. A situation has a world and a time, and a situation description is a predicate of
situations. A proposition is a predicate of contexts of utterance. A head of the clausal spine
takes a description of one sort to a description of the same sort or of the next: the heads of
the V-domain take event descriptions to event descriptions, Asp* closes the event existentially
and yields a situation description, the heads of the T-domain take situation descriptions to
situation descriptions, and Fin* closes the situation and anchors it to the context. A spine has a
denotation over an event description when each head takes the sort of the description below it.

No head lowers the sort, so no spine with a denotation has a head that takes a lower sort above
one that yields a higher sort. The perfect auxiliary, a situation head, is above the progressive,
an event head; an epistemic modal, a head of the propositional zone, is above a root modal and
above the perfect; and an adverb is above every adverb of a lower sort. Heads of one sort are not
ordered by sort: a root modal and the perfect compose in either order, and so do *once* and
*probably*, whose two orders differ in meaning unless the worlds accessible at the earlier time
are accessible at the later.

A verbal word spells out a stretch of the spine: the heads of its stem, then those of its
inflection. The dummy *be* has no head of its own, the participle in *-en* is an Asp* over an event
description and a head of the T-domain over a situation description, and an infinitive or finite
form of an event stem includes a null Asp*. A finite form includes Fin*, so no finite form is below
the perfect auxiliary; English modals, which have only finite forms, are therefore above the
perfect, while a Norwegian root modal has a participle and composes below it.

With *intentionally* a modifier of events and *already* a modifier of situations, an assignment of
sorts to the heads of Cinque's hierarchy is not monotone, since the hierarchy has the volitional
head above anterior tense.

## Implementation notes

* A situation is an index of a world and an interval, and the utterance situation a context. The
  relations that the denotations leave open, the transitions of the participle, the consequence
  relation of the perfect auxiliary, the accessibility relations and the content of the adverbs,
  are the fields of a model. The null imperfect Asp* is fully specified: the reference time lies
  within the run time of the event.
* The description of the verb phrase is the argument of a spine, not a head: the process and
  result heads are not functions of a description. The passive participle denotes the identity,
  without its presupposition of an external argument, and the holders that the progressive and the
  perfect auxiliary introduce are left out.
* Selection beyond sort is not modelled: the progressive's dynamic complement, the passive's
  argument structure and the order of the heads of the event zone. The doubled progressive and the
  doubled perfect, which sorts do not exclude, are not rows.
* A finite form anchors by the tense of its form, the modals included. In the tree of the full
  auxiliary sequence *could* spells out Fin* and one head of the T-domain, which is the modal's
  here. Where no Asp* is named for a form, the simple past and the infinitive, a spine has an
  unnamed Asp* with a transition relation of its own.
* The reading and the force of a modal in a row without judged readings are those of its
  translation.
* The rows with adverbs are paired with spines and not with words, since word order does not fix
  where an adverb before a finite verb is adjoined. *Probably* modifies situations, so the starred
  order *once probably* has a denotation; its star is pragmatic.
* The library's progressive and modal imperfective yield interval properties. Here the
  progressive is the null imperfect Asp* at the exact run time over the in-progress description,
  and the modal imperfective a necessity of the situation zone over the null imperfect Asp*.

## References

* [ramchand-svenonius-2014]
* [cinque-1999]
-/

@[expose] public section

namespace RamchandSvenonius2014

open ModalLogic Aspect Event
open scoped SetRel

universe u

/-! ### Sorts and descriptions, §3 -/

/-- The sorts of description, events below situations below propositions. -/
inductive Zone
  | event
  | situation
  | proposition
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Zone := LinearOrder.lift' Zone.ctorIdx (by decide)

/-- A situation has a world and a time. -/
abbrev Sit (W T : Type*) [LE T] : Type _ := Index W (NonemptyInterval T)

/-- The utterance situation is a context of utterance. -/
abbrev Ctx (W T X L : Type*) : Type _ := SpeechAct.Context W X L T

/-- The descriptions of a sort: predicates of events at a world, of situations, and of contexts. -/
abbrev Desc (E W T X L : Type u) [LinearOrder T] : Zone → Type u
  | .event => W → E → Prop
  | .situation => Sit W T → Prop
  | .proposition => Ctx W T X L → Prop

/-! ### Heads, §4 and §5 -/

/-- The adverbs of the rows, each with the sort of description it modifies. -/
inductive Adverb : Zone → Type
  | quietly : Adverb .event
  | intentionally : Adverb .event
  | twice : Adverb .event
  | already : Adverb .situation
  | once : Adverb .situation
  | probably : Adverb .situation
  | fortunately : Adverb .proposition
  deriving DecidableEq

/-- The ways Fin* anchors a situation to the context, by its time (48) or its world (49). -/
inductive Anchor
  | present
  | past
  | realis
  | irrealis
  deriving DecidableEq

/-- The heads, each with the sort of description it takes and the sort it yields. -/
inductive Head : Zone → Zone → Type
  /-- Initiation (38). -/
  | vInit : Head .event .event
  /-- The passive participle (40). -/
  | vPass : Head .event .event
  /-- The progressive *-ing* (41). -/
  | vEvt : Head .event .event
  /-- An Asp* whose form and relation are not given. -/
  | asp : Head .event .situation
  /-- The perfect participle as Asp* (43). -/
  | aspEn : Head .event .situation
  /-- The null imperfect Asp* (44). -/
  | aspImp : Head .event .situation
  /-- The perfect auxiliary (45). -/
  | tPerf : Head .situation .situation
  /-- The participle in the T-domain (46). -/
  | tEn : Head .situation .situation
  /-- A modal in the T-domain, root modality (47). -/
  | tModal (f : Modality.QuantificationalForce) : Head .situation .situation
  /-- The transition to propositions (48), (49). -/
  | fin (a : Anchor) : Head .situation .proposition
  /-- A modal in the propositional zone, epistemic modality (§4.4). -/
  | epistemic (f : Modality.QuantificationalForce) : Head .proposition .proposition
  /-- An adverb, modifying descriptions of its sort (§5.1). -/
  | adverb {z : Zone} (a : Adverb z) : Head z z
  deriving DecidableEq

-- (29): no head lowers the sort
theorem Head.le {a b : Zone} (h : Head a b) : a ≤ b := by
  cases h <;> first | decide | exact le_rfl

/-- The relations that the denotations of the heads leave open. -/
structure Model (E W T X L : Type u) [LinearOrder T] where
  /-- The caused-process relation of initiation (38). -/
  cause : SetRel E E
  /-- The in-progress description of an event description (41). -/
  inProgress : (W → E → Prop) → W → E → Prop
  /-- The relation of an unnamed Asp* between a reference time and an event, at a world. -/
  transition₀ : W → SetRel (NonemptyInterval T) E
  /-- The transition of the perfect participle between a reference time and an event (43). -/
  transition₁ : W → SetRel (NonemptyInterval T) E
  /-- A situation begins as a consequence of another (45). -/
  consequence : SetRel (Sit W T) (Sit W T)
  /-- The transition of the participle between two situations (46). -/
  transition₂ : SetRel (Sit W T) (Sit W T)
  /-- The situations accessible from a situation (47). -/
  acc : SetRel (Sit W T) (Sit W T)
  /-- The contexts epistemically accessible from a context. -/
  epistemic : SetRel (Ctx W T X L) (Ctx W T X L)
  /-- The property of events that an event adverb adds. -/
  manner : Adverb .event → E → Prop
  /-- How the time that *once* binds stands to the reference time. -/
  once : SetRel (NonemptyInterval T) (NonemptyInterval T)
  /-- The worlds over which *probably* quantifies at a time. -/
  likely : NonemptyInterval T → SetRel W W
  /-- The content of *already*. -/
  already : (Sit W T → Prop) → Sit W T → Prop
  /-- The content of *fortunately*. -/
  fortunately : (Ctx W T X L → Prop) → Ctx W T X L → Prop

section Denote

variable {E W T X L : Type u} [LinearOrder T] (τ : E → NonemptyInterval T) [PartialOrder E]
  (M : Model E W T X L)

/-- Possibility or necessity along a relation, by the force. -/
def modalOp {α : Type*} (f : Modality.QuantificationalForce) (R : SetRel α α) (p : α → Prop) :
    α → Prop :=
  match f with
  | .existential => ◇[R] p
  | .universal => □[R] p

/-- The denotation of a head, a map from descriptions of the sort it takes to descriptions of the
sort it yields. -/
def Head.denote : {a b : Zone} → Head a b → Desc E W T X L a → Desc E W T X L b
  | _, _, .vInit, P => fun w e' ↦ ◇[M.cause] (P w) e'
  | _, _, .vPass, P => P
  | _, _, .vEvt, P => M.inProgress P
  | _, _, .asp, P => fun s ↦ ◇[M.transition₀ s.world] (P s.world) s.time
  | _, _, .aspEn, P => fun s ↦ ◇[M.transition₁ s.world] (P s.world) s.time
  | _, _, .aspImp, P => fun s ↦ unbounded τ (P s.world) s.time
  | _, _, .tPerf, Q => ◇[M.consequence] Q
  | _, _, .tEn, Q => ◇[M.transition₂] Q
  | _, _, .tModal f, Q => modalOp f M.acc Q
  | _, _, .fin .present, R => fun c ↦ ∃ s, R s ∧ s.time = .pure c.time
  | _, _, .fin .past, R => fun c ↦ ∃ s, R s ∧ s.time ≠ .pure c.time
  | _, _, .fin .realis, R => fun c ↦ ∃ s, R s ∧ s.world = c.world
  | _, _, .fin .irrealis, R => fun c ↦ ∃ s, R s ∧ s.world ≠ c.world
  | _, _, .epistemic f, p => modalOp f M.epistemic p
  | .event, _, .adverb a, P => fun w e' ↦ M.manner a e' ∧ ∃ e ≤ e', P w e
  | .situation, _, .adverb .once, Q => ◇[Index.temporal M.once] Q
  | .situation, _, .adverb .probably, Q => □[Index.modal M.likely] Q
  | .situation, _, .adverb .already, Q => M.already Q
  | .proposition, _, .adverb .fortunately, p => M.fortunately p

/-! ### Spines -/

/-- A head with its sorts. -/
abbrev AnyHead : Type := (a : Zone) × (b : Zone) × Head a b

/-- The sort of description a head takes. -/
def AnyHead.dom (h : AnyHead) : Zone := h.1

/-- The sort of description a head yields. -/
def AnyHead.cod (h : AnyHead) : Zone := h.2.1

/-- The denotation of a list of heads over a description, undefined where a head does not take
the sort of the description below it. -/
def denoteFrom :
    List AnyHead → (z : Zone) → Desc E W T X L z → Part ((z : Zone) × Desc E W T X L z)
  | [], _, P => Part.some ⟨_, P⟩
  | ⟨a, b, h⟩ :: l, z, P => Part.assert (a = z) fun e ↦ denoteFrom l b (h.denote τ M (e ▸ P))

/-- The denotation of a spine over the event description of its verb phrase. -/
def denote (s : Spine AnyHead) (P : W → E → Prop) : Part ((z : Zone) × Desc E W T X L z) :=
  denoteFrom τ M s.heads .event P

/-- A list of heads composes over a sort when each head takes the sort yielded below it. -/
def ComposesFrom : List AnyHead → Zone → Prop
  | [], _ => True
  | h :: l, z => h.dom = z ∧ ComposesFrom l h.cod

instance : ∀ (l : List AnyHead) (z : Zone), Decidable (ComposesFrom l z)
  | [], _ => instDecidableTrue
  | h :: l, _ => @instDecidableAnd _ _ _ (instDecidableComposesFrom l h.cod)

/-- A spine composes when its heads compose over an event description. -/
def Composes (s : Spine AnyHead) : Prop := ComposesFrom s.heads .event

instance (s : Spine AnyHead) : Decidable (Composes s) :=
  inferInstanceAs (Decidable (ComposesFrom _ _))

theorem dom_denoteFrom_iff (l : List AnyHead) (z : Zone) (P : Desc E W T X L z) :
    (denoteFrom τ M l z P).Dom ↔ ComposesFrom l z := by
  induction l generalizing z with
  | nil => simp [denoteFrom, ComposesFrom]
  | cons h l ih =>
    obtain ⟨a, b, h⟩ := h
    simp only [denoteFrom, Part.assert, ComposesFrom, AnyHead.dom, AnyHead.cod]
    exact ⟨fun ⟨e, hd⟩ ↦ ⟨e, (ih _ _).1 hd⟩, fun ⟨e, hc⟩ ↦ ⟨e, (ih _ _).2 hc⟩⟩

/-- A spine has a denotation exactly when it composes. -/
theorem dom_denote_iff (s : Spine AnyHead) (P : W → E → Prop) :
    (denote τ M s P).Dom ↔ Composes s :=
  dom_denoteFrom_iff τ M _ _ _

end Denote

theorem ComposesFrom.isChain : ∀ {l : List AnyHead} {z : Zone}, ComposesFrom l z →
    l.IsChain fun h h' ↦ h.cod = h'.dom
  | [], _, _ => .nil
  | [_], _, _ => .singleton _
  | _ :: _ :: _, _, ⟨_, h, hl⟩ => .cons_cons h.symm (ComposesFrom.isChain (z := _) ⟨h, hl⟩)

variable {s : Spine AnyHead}

theorem pairwise_cod_le (hs : Composes s) : s.heads.Pairwise fun h h' ↦ h.cod ≤ h'.dom :=
  have : IsTrans AnyHead fun h h' ↦ h.cod ≤ h'.dom :=
    ⟨fun _ b _ hab hbc ↦ hab.trans (b.2.2.le.trans hbc)⟩
  List.isChain_iff_pairwise.1 (hs.isChain.imp fun _ _ e ↦ e.le)

theorem not_composes_of_sublist {a b : AnyHead} (h : List.Sublist [a, b] s.heads)
    (hab : b.dom < a.cod) : ¬ Composes s := fun hs ↦
  not_lt_of_ge (List.pairwise_pair (R := fun h h' : AnyHead ↦ h.cod ≤ h'.dom) |>.1
    ((pairwise_cod_le hs).sublist h)) hab

open Head

-- (3): the progressive is not above the perfect auxiliary
theorem not_composes_of_tPerf_vEvt (h : List.Sublist [⟨_, _, tPerf⟩, ⟨_, _, vEvt⟩] s.heads) :
    ¬ Composes s :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_fin_tPerf {a : Anchor}
    (h : List.Sublist [⟨_, _, fin a⟩, ⟨_, _, tPerf⟩] s.heads) : ¬ Composes s :=
  not_composes_of_sublist h (show Zone.situation < .proposition by decide)

theorem not_composes_of_epistemic_tEn {f : Modality.QuantificationalForce}
    (h : List.Sublist [⟨_, _, epistemic f⟩, ⟨_, _, tEn⟩] s.heads) : ¬ Composes s :=
  not_composes_of_sublist h (show Zone.situation < .proposition by decide)

theorem not_composes_of_epistemic_tModal {f g : Modality.QuantificationalForce}
    (h : List.Sublist [⟨_, _, epistemic f⟩, ⟨_, _, tModal g⟩] s.heads) : ¬ Composes s :=
  not_composes_of_sublist h (show Zone.situation < .proposition by decide)

theorem not_composes_of_adverb {z z' : Zone} {a : Adverb z} {b : Adverb z'}
    (h : List.Sublist [⟨_, _, adverb a⟩, ⟨_, _, adverb b⟩] s.heads) (hz : z' < z) :
    ¬ Composes s :=
  not_composes_of_sublist h hz

/-! ### Elaboration, §3 -/

section Elaboration

variable {E W T X L : Type u} [LinearOrder T] (τ : E → NonemptyInterval T) [PartialOrder E]
  (M : Model E W T X L)

/-- A description is realized when it holds of something. -/
def Realized : {z : Zone} → Desc E W T X L z → Prop
  | .event, P => ∃ w, Event.closure P w
  | .situation, Q => ∃ s, Q s
  | .proposition, p => ∃ c, p c

/-- A model is coherent when its in-progress descriptions, its necessities and its adverbs are
realized only over realized descriptions. -/
structure Model.Coherent : Prop where
  inProgress : ∀ P w e, M.inProgress P w e → ∃ w', Event.closure P w'
  acc : ∀ s, ∃ s', s ~[M.acc] s'
  epistemic : ∀ c, ∃ c', c ~[M.epistemic] c'
  likely : ∀ t w, ∃ v, w ~[M.likely t] v
  already : ∀ Q s, M.already Q s → ∃ s', Q s'
  fortunately : ∀ p c, M.fortunately p c → ∃ c', p c'

variable {τ M}

theorem Head.realized (hM : M.Coherent) : ∀ {a b : Zone} (h : Head a b) {P : Desc E W T X L a},
    Realized (h.denote τ M P) → Realized P
  | _, _, .vInit, _, ⟨w, _, e, _, he⟩ => ⟨w, e, he⟩
  | _, _, .vPass, _, h => h
  | _, _, .vEvt, _, ⟨w, e, he⟩ => hM.inProgress _ w e he
  | _, _, .asp, _, ⟨s, e, _, he⟩ => ⟨s.world, e, he⟩
  | _, _, .aspEn, _, ⟨s, e, _, he⟩ => ⟨s.world, e, he⟩
  | _, _, .aspImp, _, ⟨s, hs⟩ => let ⟨e, _, he⟩ := unbounded_iff.1 hs; ⟨s.world, e, he⟩
  | _, _, .tPerf, _, ⟨_, s, _, hs⟩ => ⟨s, hs⟩
  | _, _, .tEn, _, ⟨_, s, _, hs⟩ => ⟨s, hs⟩
  | _, _, .tModal .existential, _, ⟨_, s, _, hs⟩ => ⟨s, hs⟩
  | _, _, .tModal .universal, _, ⟨s, hs⟩ => let ⟨s', h⟩ := hM.acc s; ⟨s', hs s' h⟩
  | _, _, .fin .present, _, ⟨_, s, hs, _⟩ => ⟨s, hs⟩
  | _, _, .fin .past, _, ⟨_, s, hs, _⟩ => ⟨s, hs⟩
  | _, _, .fin .realis, _, ⟨_, s, hs, _⟩ => ⟨s, hs⟩
  | _, _, .fin .irrealis, _, ⟨_, s, hs, _⟩ => ⟨s, hs⟩
  | _, _, .epistemic .existential, _, ⟨_, c, _, hc⟩ => ⟨c, hc⟩
  | _, _, .epistemic .universal, _, ⟨c, hc⟩ => let ⟨c', h⟩ := hM.epistemic c; ⟨c', hc c' h⟩
  | .event, _, .adverb a, _, h => by
    cases a <;> (obtain ⟨w, _, _, e, _, he⟩ := h; exact ⟨w, e, he⟩)
  | .situation, _, .adverb .once, _, ⟨_, s, _, hs⟩ => ⟨s, hs⟩
  | .situation, _, .adverb .probably, _, ⟨s, hs⟩ =>
    let ⟨v, h⟩ := hM.likely s.time s.world; ⟨⟨v, s.time⟩, hs ⟨v, s.time⟩ ⟨rfl, h⟩⟩
  | .situation, _, .adverb .already, _, ⟨s, hs⟩ => hM.already _ s hs
  | .proposition, _, .adverb .fortunately, _, ⟨c, hc⟩ => hM.fortunately _ c hc

theorem realized_of_mem_denoteFrom (hM : M.Coherent) : ∀ (l : List AnyHead) (z : Zone)
    (P : Desc E W T X L z) {d : (z : Zone) × Desc E W T X L z}, d ∈ denoteFrom τ M l z P →
    Realized d.2 → Realized P
  | [], _, _, _, hd, hr => by
    obtain rfl := Part.mem_some_iff.1 hd
    exact hr
  | ⟨_, _, h⟩ :: l, _, _, _, hd, hr => by
    obtain ⟨rfl, hd⟩ := Part.mem_assert_iff.1 hd
    exact h.realized hM (realized_of_mem_denoteFrom hM l _ _ hd hr)

/-- In a coherent model, a description of any sort that a spine yields is realized only if the
event description of its verb phrase holds of some event. -/
theorem closure_of_mem_denote (hM : M.Coherent) {s : Spine AnyHead} {P : W → E → Prop}
    {d : (z : Zone) × Desc E W T X L z} (hd : d ∈ denote τ M s P) (hr : Realized d.2) :
    ∃ w, Event.closure P w :=
  realized_of_mem_denoteFrom hM _ _ _ hd hr

/-! ### The progressive, the imperfective, and *once probably* -/

-- the modal imperfective is a necessity of the situation zone over the null imperfect Asp*
theorem imperfective_iff_box_aspImp (M : Model E W T X L) (acc : NonemptyInterval T → SetRel W W)
    (P : W → E → Prop) (w : W) (t : NonemptyInterval T) :
    imperfective τ acc P w t ↔ □[Index.modal acc] (aspImp.denote τ M P) ⟨w, t⟩ :=
  (Index.box_modal (R := acc) (P := aspImp.denote τ M P) (i := ⟨w, t⟩)).symm

/-- The progressive holds at a time only if the null imperfect Asp* over the in-progress
description holds there. -/
theorem aspImp_vEvt_of_progressive (M : Model E W T X L)
    (circ : E → (W → E → Prop) → Modality.Background W) (ni : E → Modality.Background W)
    (hM : M.inProgress = fun P w e ↦ InProgress τ circ ni e P w) (P : W → E → Prop) (w : W)
    (t : NonemptyInterval T) (h : progressive τ circ ni P w t) :
    aspImp.denote τ M (vEvt.denote τ M P) ⟨w, t⟩ := by
  obtain ⟨e, rfl, he⟩ := progressive_iff.1 h
  exact unbounded_iff.2 ⟨e, le_rfl, by simpa [Head.denote, hM] using he⟩

-- (60), (61): possibility at an earlier time entails an earlier time in an accessible world,
-- when the worlds accessible at the earlier time are accessible at the reference time
theorem once_probably_le {R : NonemptyInterval T → SetRel W W}
    {S : SetRel (NonemptyInterval T) (NonemptyInterval T)}
    (h : ∀ ⦃t u⦄, t ~[S] u → R u ⊆ R t) (Q : Sit W T → Prop) :
    ◇[Index.temporal S] (◇[Index.modal R] Q) ≤ ◇[Index.modal R] (◇[Index.temporal S] Q) := by
  rw [← diamond_comp, ← diamond_comp]
  exact diamond_le_diamond_iff.2 (Index.temporal_comp_modal_subset h) Q

end Elaboration

/-! ### Words -/

/-- The stems of the verbal words. -/
inductive Stem
  /-- A lexical verb. -/
  | lexical
  /-- The dummy *be*, inserted to carry an inflection (§4). -/
  | be
  /-- The perfect auxiliary. -/
  | have
  /-- A modal on a reading, with its force. -/
  | modal (r : Examples.Reading) (f : Modality.QuantificationalForce)

namespace Stem

/-- The heads a stem spells out: none for a lexical verb, whose description the spine is over, a
head of the T-domain for a root modal and a head of the propositional zone for an epistemic one
(§4.4). -/
def heads : Stem → List AnyHead
  | .lexical => []
  | .be => []
  | .have => [⟨_, _, tPerf⟩]
  | .modal .root f => [⟨_, _, tModal f⟩]
  | .modal .epistemic f => [⟨_, _, epistemic f⟩]

/-- The sort of the description a stem yields, an event description if it has no head. -/
def sort (s : Stem) : Zone := s.heads.getLast?.elim .event AnyHead.cod

end Stem

/-- The inflections of the verbal words. -/
inductive Inflection
  /-- The passive participle. -/
  | passive
  /-- The progressive participle in *-ing*. -/
  | ing
  /-- The participle in *-en* of the perfect. -/
  | en
  | infinitive
  /-- A finite form, with its anchor. -/
  | finite (a : Anchor)

/-- The null heads that take a description of a sort to a situation description: an Asp* over an
event description (§4.2). -/
def toSituation : Zone → List AnyHead
  | .event => [⟨_, _, asp⟩]
  | _ => []

/-- The heads an inflection spells out over a stem of a sort. The participle in *-en* is Asp* over
an event description and a head of the T-domain otherwise. -/
def Inflection.heads : Inflection → Zone → List AnyHead
  | .passive, _ => [⟨_, _, vPass⟩]
  | .ing, _ => [⟨_, _, vEvt⟩]
  | .en, .event => [⟨_, _, aspEn⟩]
  | .en, _ => [⟨_, _, tEn⟩]
  | .infinitive, z => toSituation z
  | .finite a, z => toSituation z ++ [⟨_, _, fin a⟩]

/-- A verbal word, a stem with an inflection. -/
structure Word where
  stem : Stem
  inflection : Inflection

/-- The heads a word spells out, those of its stem below those of its inflection; the Fin* of a
finite epistemic modal is below the modal. -/
def Word.heads : Word → List AnyHead
  | ⟨.modal .epistemic f, .finite a⟩ => [⟨_, _, fin a⟩, ⟨_, _, epistemic f⟩]
  | ⟨s, i⟩ => s.heads ++ i.heads s.sort

/-- The spine of a sequence of verbal words in their surface order, the first word highest. -/
def spine (ws : List Word) : Spine AnyHead := ⟨ws.reverse.flatMap Word.heads⟩

theorem fin_mem_heads {w : Word} {a : Anchor} (h : w.inflection = .finite a) :
    (⟨_, _, fin a⟩ : AnyHead) ∈ w.heads := by
  rcases w with ⟨_ | _ | _ | ⟨_ | _, _⟩, _⟩ <;> cases h <;>
    simp [Word.heads, Stem.heads, Stem.sort, Inflection.heads, toSituation]

/-- No finite word is below the perfect auxiliary on a composing spine. -/
theorem not_composes_of_finite_of_have {l₁ l₂ : List Word} {i : Inflection} {w : Word}
    {a : Anchor} (hw : w ∈ l₂) (hf : w.inflection = .finite a) :
    ¬ Composes (spine (l₁ ++ ⟨.have, i⟩ :: l₂)) := by
  have h₁ : [(⟨_, _, fin a⟩ : AnyHead)].Sublist (l₂.reverse.flatMap Word.heads) :=
    List.singleton_sublist.2 (List.mem_flatMap.2 ⟨w, List.mem_reverse.2 hw, fin_mem_heads hf⟩)
  have h₂ : [(⟨_, _, tPerf⟩ : AnyHead)].Sublist (Word.heads ⟨.have, i⟩) :=
    List.singleton_sublist.2 (List.mem_append_left _ List.mem_cons_self)
  refine not_composes_of_fin_tPerf (a := a) ?_
  simpa [spine] using (h₁.append h₂).trans (List.sublist_append_left _ (l₁.reverse.flatMap _))

-- a root modal and the perfect auxiliary compose in either order
theorem composes_modal_have (f : Modality.QuantificationalForce) (a : Anchor) :
    Composes (spine [⟨.have, .finite a⟩, ⟨.modal .root f, .en⟩, ⟨.lexical, .infinitive⟩]) ∧
      Composes (spine [⟨.modal .root f, .finite a⟩, ⟨.have, .infinitive⟩, ⟨.lexical, .en⟩]) := by
  cases f <;> cases a <;> decide

/-! ### The rows -/

/-- The rows of the auxiliary sequences with their verbal words. -/
def analyses : List (Datum × List Word) :=
  [(Examples.ex_3a, [⟨.modal .root .existential, .finite .past⟩, ⟨.have, .infinitive⟩,
      ⟨.be, .en⟩, ⟨.be, .ing⟩, ⟨.lexical, .passive⟩]),
    (Examples.ex_3b, [⟨.be, .finite .present⟩, ⟨.have, .ing⟩, ⟨.lexical, .en⟩]),
    (Examples.ex_20a, [⟨.modal .epistemic .existential, .finite .present⟩, ⟨.have, .infinitive⟩,
      ⟨.lexical, .en⟩]),
    (Examples.ex_20b, [⟨.modal .epistemic .universal, .finite .present⟩, ⟨.have, .infinitive⟩,
      ⟨.lexical, .en⟩]),
    (Examples.ex_21a, [⟨.have, .finite .present⟩, ⟨.modal .root .existential, .en⟩,
      ⟨.lexical, .infinitive⟩]),
    (Examples.ex_21b, [⟨.have, .finite .present⟩, ⟨.modal .root .universal, .en⟩,
      ⟨.lexical, .infinitive⟩]),
    (Examples.ex_24a, [⟨.modal .root .universal, .finite .present⟩,
      ⟨.modal .root .existential, .infinitive⟩, ⟨.lexical, .infinitive⟩]),
    (Examples.ex_24b, [⟨.modal .epistemic .existential, .finite .present⟩,
      ⟨.modal .root .universal, .infinitive⟩, ⟨.lexical, .infinitive⟩])]

/-- A row is acceptable exactly when the spine of its words composes. -/
theorem analyses_judgment :
    ∀ p ∈ analyses, p.1.judgment = .acceptable ↔ Composes (spine p.2) := by
  decide

-- (23): a participial modal under the perfect auxiliary has its root reading alone
theorem modal_judgment : ∀ p ∈ [(Examples.ex_23a, Modality.QuantificationalForce.existential),
      (Examples.ex_23b, .universal)], ∀ r,
    Examples.reading p.1 r = some .acceptable ↔
      Composes (spine [⟨.have, .finite .present⟩, ⟨.modal r p.2, .en⟩,
        ⟨.lexical, .infinitive⟩]) := by
  decide

/-- The rows with adverbs, with their spines. -/
def adverbAnalyses : List (Datum × Spine AnyHead) :=
  [(Examples.ex_51a, ⟨[⟨_, _, asp⟩, ⟨_, _, adverb .already⟩, ⟨_, _, fin .present⟩,
      ⟨_, _, adverb .fortunately⟩]⟩),
    (Examples.ex_51b, ⟨[⟨_, _, asp⟩, ⟨_, _, adverb .fortunately⟩, ⟨_, _, adverb .already⟩,
      ⟨_, _, fin .present⟩]⟩),
    (Examples.ex_51c, ⟨[⟨_, _, adverb .quietly⟩, ⟨_, _, asp⟩, ⟨_, _, adverb .already⟩,
      ⟨_, _, fin .past⟩]⟩),
    (Examples.ex_51d, ⟨[⟨_, _, asp⟩, ⟨_, _, adverb .already⟩, ⟨_, _, adverb .quietly⟩,
      ⟨_, _, fin .past⟩]⟩),
    (Examples.ex_54a, ⟨[⟨_, _, vPass⟩, ⟨_, _, adverb .intentionally⟩, ⟨_, _, adverb .twice⟩,
      ⟨_, _, aspEn⟩, ⟨_, _, tPerf⟩, ⟨_, _, fin .present⟩]⟩),
    (Examples.ex_60a, ⟨[⟨_, _, asp⟩, ⟨_, _, adverb .once⟩, ⟨_, _, adverb .probably⟩,
      ⟨_, _, fin .past⟩]⟩)]

theorem adverbAnalyses_judgment :
    ∀ p ∈ adverbAnalyses, p.1.judgment = .acceptable ↔ Composes p.2 := by
  decide

-- (60b), (61): the order *once probably* composes as *probably once* does
theorem composes_once_probably :
    Composes ⟨[⟨_, _, asp⟩, ⟨_, _, adverb .probably⟩, ⟨_, _, adverb .once⟩,
      ⟨_, _, fin .past⟩]⟩ := by
  decide

-- (54): adverbs under passive *been* modify events
theorem composes_54a_iff {z z' : Zone} (a : Adverb z) (b : Adverb z') :
    Composes ⟨[⟨_, _, vPass⟩, ⟨_, _, adverb a⟩, ⟨_, _, adverb b⟩, ⟨_, _, aspEn⟩,
      ⟨_, _, tPerf⟩, ⟨_, _, fin .present⟩]⟩ ↔ z = .event ∧ z' = .event := by
  cases a <;> cases b <;> decide

/-! ### Cinque's hierarchy, §5 -/

theorem not_monotone_of_modVolitional {z : Cartography.Head → Zone}
    (hv : z .modVolitional = .event) (ha : z .tAnterior = .situation) : ¬ Monotone z :=
  fun hz ↦ absurd (hz (show Cartography.Head.tAnterior ≤ .modVolitional by decide))
    (by rw [hv, ha]; decide)

end RamchandSvenonius2014
