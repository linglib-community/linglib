module

public import Linglib.Semantics.ArgumentStructure.Root.Basic
public import Linglib.Semantics.ArgumentStructure.EventStructure.Postulates
public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Presupposition.Again
public import Linglib.Data.Examples.BeaversKoontzGarboden2020
public import Linglib.Data.Examples.Readers

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

A root carries entailments of four kinds, manner, cause, result and state, and the book's
diagnostics refute two theses that restrict them. Result roots allow no truly restitutive *again*,
so [no lexicon of states and manners fits the judgments](##bifurcation_thesis_false), against the
Bifurcation Thesis; the causer of *drown* cannot be denied to have acted, so
[no lexicon without a root of manner and result fits them](##manner_result_complementarity_false),
against Manner/Result Complementarity. The book's own classes [fit them](##rows). Its typology
fills [the cells that markedness and naturalness allow](##mem_attestedCells_iff), which are
[the signatures of the basic templates](##attestedRows_eq_kinds_templates).

## Implementation notes

* The state entailments of a result root, and the result entailed by a cause, come from the
  collocational closure of the signature (`Root.close`). The refutation of Manner/Result
  Complementarity rests on the second: read on the signatures as given, the thesis
  [is consistent with the judgments](##exists_fits_not_mannerResult).
* A root is its signature, so √hand and √drown coincide as values, and the position of each
  root is recorded beside it in `sample`.
* The third clause of `mem_attestedCells_iff` is the book's naturalness argument for the row
  with a manner and a state alone; for the row that adds a change without a cause the book leaves
  open whether a change and a manner can combine without causation.
* The signatures of the Levin classes are this study's (`rootEntailments`), and the book's
  hypothesis about which roots alternate is compared with the class pages of [levin-1993]
  (`rootHypothesis_matches_profile`, `rootHypothesisResidue_disagrees`).
* A diagnostic is a property of a root's state description in an interpretation, passed when some
  interpretation that respects the signature lets the denial go through (`passes_iff`). The
  denial of action is modelled as the book applies it to the manner of killing verbs, on a
  causative, whose causing event it denies to be of the root's manner; with a pure manner verb
  it denies the verb's own event and is not modelled.
* The postulate of a root such as √guillotine constrains the causes of a change that its state
  arises from, and the causative introduces a change of its own. The two are the same change
  when a state arises from at most one, which `Passes` assumes of the interpretations it ranges
  over; `not_diamond_cause_diamond_become_le_twoChanges` is an interpretation without the
  assumption in which the postulate holds and the causing event lacks the manner. The mirror
  postulate of √hand, on which an action of the manner causes the result, is independent of it
  (`twoChanges_not_entailsCausedResult`, `jointCause_not_entailsMannerOfCause`).
* A ditransitive is the head `v◊cause` (29) with the root adjoined (36). The possibility operator
  of the head is a relation `prospect` between a causing event and the states it may bring
  about, which contains the composite of `cause` and `become` since an actual result is a
  possible one. A ditransitive root class is the result its root entails as a function of the
  template's (`Examples.RootClass.result?`), and the result-denial rows of chapter 3 are read by
  `resultDenial_rows`. In the causative of chapter 4 the template entails the result whatever
  the root (`causative_denote_le`). The object-deletion row is not read; the rows of the three
  attachments of *again* are read by `attachment_rows`.

## References

* [beavers-koontz-garboden-2020]
* [levin-1993]
* [embick-2009]
* [arad-2005]
* [rappaport-hovav-levin-2010]
* [von-stechow-1996]
-/

@[expose] public section

namespace BeaversKoontzGarboden2020

open ArgumentStructure ArgumentStructure.Root
open scoped SetRel ModalLogic

/-! ### The ontological kinds -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root := {.state, .manner}

/-! ### The typology -/

/-- The seven rows of the typology (12). -/
def typology : Finset Root :=
  {propertyConcept, pureResult, causativeResult, pureManner, {.state, .manner},
   {.state, .manner, .result}, fullSpec}

-- (12), p. 227
theorem wellFormed_iff_mem_typology :
    ∀ s : Root, s.WellFormed ↔ s = ∅ ∨ s ∈ typology := by decide

/-- The filled cells of (12), pairs of a closed signature and a position. -/
def attestedCells : Finset (Root × Root.Position) :=
  {(propertyConcept, .complement), (pureResult, .complement), (causativeResult, .complement),
   (pureManner, .adjoined), (fullSpec, .adjoined), (fullSpec, .complement)}

/-- The filled cells of (12) are those where an adjoined root is a manner, a complement root a
state, and manner with state entails cause (pp. 229–230). -/
theorem mem_attestedCells_iff : ∀ (s : Root) (p : Root.Position),
    (s, p) ∈ attestedCells ↔ s ∈ typology ∧ (p = .adjoined → .manner ∈ s) ∧
      (p = .complement → .state ∈ s) ∧ (.manner ∈ s → .state ∈ s → .cause ∈ s) := by
  decide

section Again

open Presupposition ModalLogic EventStructure Template

/-! ### Sublexical *again* and the hierarchy of its readings

*Again* is a presupposition trigger that can attach at three points in the change-of-state
structure, the root, `vbecome` and `vcause` (27), which yields the three readings of *Mary
flattened the rug again* (25): the restitutive one, that the rug had been flat, the repetitive
one over the change, that it had flattened, and the repetitive one over the causation, that
Mary had flattened it. The three points are the subterms `state` and `achievement` of the
causative template (18c), `[y CAUSE [x BECOME P]]`, and the template itself, `causative`, whose
causing subevent is an eventuality with the causer as its actor
(`Template.denote_cause_effector`), and the entry for *again* is `Presupposition.again`. The
hierarchy of the readings is the subterm order: attached at a template, *again* presupposes
that each of its subterms was realized. -/

universe u

variable {Entity : Type*} {State Event : Type u} (M : Model State Event)
  (θ : Entity → Event → Prop) {σ τ : Eventuality} {P : Entity → State → Prop} {y x : Entity}

/-- The causative change-of-state template (18c), `[y CAUSE [x BECOME P]]`. -/
def causative : Template .event := .cause .effector .achievement

/-- *Again* attached at the subterm `t` of the causative template of a root with state predicate
`P`, with `θ` the relation of a causer to the causing event and `R` relating an eventuality of
the sort of `t` to the earlier ones. The attachment at `state` gives the restitutive reading, at
`achievement` the repetitive reading over the change, and at `causative` the repetitive reading
over the causation. -/
noncomputable def againAt (t : Template σ)
    (R : SetRel (σ.Carrier State Event) (σ.Carrier State Event)) (P : Entity → State → Prop)
    (y x : Entity) : σ.Carrier State Event → Trivalent :=
  again R (t.denote M θ P ⊤ y x)

variable {M θ}

theorem exists_denote_of_againAt_ne_undefined {t : Template σ} {u : Template τ} (hu : u.IsSubterm t)
    {R : SetRel (σ.Carrier State Event) (σ.Carrier State Event)} {w : σ.Carrier State Event}
    (h : againAt M θ t R P y x w ≠ .undefined) :
    ∃ w', w ~[R] w' ∧ ∃ y' v, u.denote M θ P ⊤ y' x v :=
  diamond_mono R (fun _ ↦ exists_denote_of_isSubterm hu) w (again_ne_undefined_iff.1 h)

theorem diamond_cause_of_againAt_causative_ne_undefined {R : SetRel Event Event} {w : Event}
    (h : againAt M θ causative R P y x w ≠ .undefined) :
    ◇[R] (◇[M.cause] (◇[M.become] (P x))) w :=
  diamond_mono R (fun _ h ↦ h.2) w (again_ne_undefined_iff.1 h)

-- chapter 4, (25a): the template entails the result whatever the root
theorem causative_denote_le {Q : Event → Prop} :
    causative.denote M θ P Q y x ≤ ◇[M.cause] (◇[M.become] (P x)) :=
  fun _ h ↦ h.2

theorem diamond_become_of_againAt_state_ne_undefined {R : SetRel State State} {s : State}
    (hres : M.EntailsChange (P x)) (h : againAt M θ .state R P y x s ≠ .undefined) :
    ◇[R] (◇[M.become.inv] ⊤) s :=
  diamond_mono R hres s (again_ne_undefined_iff.1 h)

/-- The subterm of the causative template at an attachment site of *again* (27). -/
def Examples.Attachment.template : Examples.Attachment → Σ σ, Template σ
  | .root => ⟨_, .state⟩
  | .vBecome => ⟨_, .achievement⟩
  | .vCause => ⟨_, causative⟩

theorem Examples.Attachment.isSubterm (s : Examples.Attachment) :
    s.template.2.IsSubterm causative := by
  cases s
  · exact .caused (.become (.refl _))
  · exact .caused (.refl _)
  · exact .refl _

end Again

/-! ### The typology and the templates -/

section Templates

open EventStructure Template

variable {σ : Eventuality}

-- (13), p. 231: the attested rows are the signatures of the basic templates
theorem attestedRows_eq_kinds_templates :
    attestedCells.image Prod.fst =
      {state.kinds, act.kinds, achievement.kinds, causative.kinds, accomplishment.kinds} := by
  decide

theorem kinds_ne_of_cause_not_mem {t : Template σ} {s : Root} (hm : .manner ∈ s)
    (hs : .state ∈ s) (hc : .cause ∉ s) : t.kinds ≠ s := by
  rintro rfl; exact hc (cause_mem_kinds_of_manner_of_state hm hs)

-- (12), p. 230
theorem kinds_ne_emptyRows (t : Template σ) :
    t.kinds ≠ {.state, .manner} ∧ t.kinds ≠ {.state, .manner, .result} :=
  ⟨kinds_ne_of_cause_not_mem (by decide) (by decide) (by decide),
    kinds_ne_of_cause_not_mem (by decide) (by decide) (by decide)⟩

end Templates

/-! ### The six representative roots -/

/-- √flat is a pure state root. -/
def flat : Root := {.state}

/-- √jog is a pure manner-of-motion root, its manner the jogging gait. -/
def jog : Root := {.manner}

/-- √blossom is a result root with no specified manner or cause, an internally caused change
into flowering. -/
def blossom : Root := {.result}

/-- √crack is a caused-result root without a specified manner, a caused change into a fissured
state. -/
def crack : Root := {.result, .cause}

/-- √hand carries manner, cause and result, a transfer by hand into the recipient's possession.
The possession result is not cancelable (*Mary handed John the book, #but it never came to be
on his person*), so it is entailed by the root rather than implicated. -/
def hand : Root := {.manner, .result, .cause}

/-- √drown is a manner-of-killing root, death by submersion in liquid, carrying manner, cause
and result. -/
def drown : Root := {.manner, .result, .cause}

/-- The six roots with the position each occupies in (12), √hand adjoined and √drown a
complement. -/
def sample : List (Root × Root.Position) :=
  [(flat, .complement), (jog, .adjoined), (blossom, .complement), (crack, .complement),
   (hand, .adjoined), (drown, .complement)]

/-! ### Closed signatures

The closed signatures of the roots are the rows of the typology they fill. -/

theorem close_flat : close flat = propertyConcept := by decide

theorem close_jog : close jog = pureManner := by decide

theorem close_blossom : close blossom = pureResult := by decide

theorem close_crack : close crack = causativeResult := by decide

theorem close_hand : close hand = fullSpec := by decide

theorem close_drown : close drown = fullSpec := by decide

-- (12)
theorem attestedCells_eq_sample :
    attestedCells = (sample.map fun c ↦ (close c.1, c.2)).toFinset := by decide

theorem hand_drown_differ_in_position :
    close hand = close drown ∧ (hand, .adjoined) ∈ sample ∧
      (drown, .complement) ∈ sample := by decide

/-! ### The entailments of the roots in a model

The kinds of a root are meaning postulates on its state and manner predicates
(`EventStructure.Model.Respects`). In an interpretation that respects the signature of
√crack, a cracked state arises from a caused change whatever template the root occurs in, while
one that respects the signature of √flat may have a flat state that no change gave rise to. -/

section Model

variable {Entity State Event : Type*} {M : EventStructure.Model State Event}
  {P : Entity → State → Prop} {Q : Event → Prop} {x : Entity} {s : State}

theorem crack_entails_cause (h : M.Respects (P x) Q crack) (hs : P x s) :
    ◇[M.become.inv] (◇[M.cause.inv] ⊤) s :=
  h.cause (by decide) s hs

-- (74), p. 201
theorem drown_entails_manner (h : M.Respects (P x) Q drown) (hs : P x s) :
    ◇[M.become.inv] (◇[M.cause.inv] Q) s :=
  (h.mannerOfCause (by decide) (by decide)).le_diamond_inv_diamond_inv s hs

-- p. 201: the root constrains the causing event that `vcause` introduces
theorem drown_diamond_cause_diamond_become_le (h : M.Respects (P x) Q drown)
    (hM : ∀ s ⦃e⦄, e ~[M.become] s → ∀ ⦃e'⦄, e' ~[M.become] s → e = e') :
    ◇[M.cause] (◇[M.become] (P x)) ≤ Q :=
  (h.mannerOfCause (by decide) (by decide)).diamond_cause_diamond_become_le hM

end Model

/-- A model without changes. -/
def unchanging : EventStructure.Model Unit Unit where
  become := ⊥
  cause := ⊥

/-- A model in which every state arises from a caused change. -/
def changing : EventStructure.Model Unit Unit where
  become := ⊤
  cause := ⊤

theorem flat_not_entailsChange :
    unchanging.Respects (fun _ ↦ True) (fun _ ↦ True) flat ∧
      ¬ unchanging.EntailsChange (fun _ ↦ True) :=
  ⟨by constructor <;> intro h <;> exact absurd h (by decide),
    fun h ↦ let ⟨_, he, _⟩ := h () trivial; he⟩

private theorem changing_respects {ks : Root}
    (h : ¬ (Root.Kind.manner ∈ ks ∧ Root.Kind.cause ∈ ks)) :
    changing.Respects (fun _ ↦ True) ⊥ ks :=
  ⟨fun _ _ _ ↦ ⟨(), trivial, trivial⟩, fun _ _ _ ↦ ⟨(), trivial, (), trivial, trivial⟩,
    fun hm hc ↦ absurd ⟨hm, hc⟩ h⟩

theorem crack_respects :
    changing.Respects (fun _ ↦ True) ⊥ crack ∧
      ¬ unchanging.Respects (fun _ ↦ True) ⊥ crack :=
  ⟨changing_respects (by decide),
    fun h ↦
      let ⟨_, he, _⟩ := crack_entails_cause (P := fun _ _ ↦ True) (x := ()) (s := ()) h trivial
      he⟩

/-- The changes `change i` that the one state arises from and the actions `action i` that cause
them. -/
inductive Subevent
  | change (i : Bool)
  | action (i : Bool)

/-- A model in which the one state arises from two changes, each caused by one action. -/
def twoChanges : EventStructure.Model Unit Subevent where
  become := {(e, _) | ∃ i, e = .change i}
  cause := {(v, e) | ∃ i, v = .action i ∧ e = .change i}

theorem not_diamond_cause_diamond_become_le_twoChanges :
    twoChanges.EntailsMannerOfCause (fun _ ↦ True) (· = .action true) ∧
      ¬ ◇[twoChanges.cause] (◇[twoChanges.become] fun _ ↦ True) ≤ (· = .action true) :=
  ⟨fun _ _ ↦ ⟨.change true, ⟨_, rfl⟩, ⟨.action true, ⟨_, rfl, rfl⟩, trivial⟩,
      fun _ ⟨_, hv, hi⟩ ↦ Subevent.change.inj hi ▸ hv⟩,
    fun h ↦ Bool.false_ne_true <| Subevent.action.inj <|
      h (.action false) ⟨.change false, ⟨_, rfl, rfl⟩, (), ⟨_, rfl⟩, trivial⟩⟩

/-! ### The two postulates of a manner with a cause

The roots √drown and √hand carry the same kinds and differ in position: the state predicate of
√drown requires its cause to be of the manner (74), and the manner of √hand requires an action
of it to cause the result (2b). Neither postulate entails the other. -/

-- every eventuality has the manner, and a change causes nothing
theorem twoChanges_not_entailsCausedResult :
    twoChanges.EntailsMannerOfCause ⊤ ⊤ ∧ ¬ twoChanges.EntailsCausedResult ⊤ ⊤ :=
  ⟨fun _ _ ↦ ⟨.change true, ⟨_, rfl⟩, ⟨.action true, ⟨_, rfl, rfl⟩, trivial⟩, fun _ _ ↦ trivial⟩,
    fun h ↦ let ⟨_, ⟨_, hv, _⟩, _⟩ := h (.change true) trivial; nomatch hv⟩

/-- A model in which the one state arises from one change, which both actions cause. -/
def jointCause : EventStructure.Model Unit Subevent where
  become := {(e, _) | e = .change true}
  cause := {(v, e) | (∃ i, v = .action i) ∧ e = .change true}

-- the manner's action brings about the state, and so does an action that lacks the manner
theorem jointCause_not_entailsMannerOfCause :
    jointCause.EntailsCausedResult (· = .action true) ⊤ ∧
      ¬ jointCause.EntailsMannerOfCause ⊤ (· = .action true) :=
  ⟨fun _ hv ↦ ⟨.change true, ⟨⟨_, hv⟩, rfl⟩, (), rfl, trivial⟩,
    fun h ↦ let ⟨_, he, _, hQ⟩ := h () trivial
      Bool.false_ne_true <| Subevent.action.inj <| hQ (.action false) ⟨⟨_, rfl⟩, he⟩⟩

/-! ### Ditransitives and the denial of the result

The ditransitive head `v◊cause` (29) says that its subject is the effector of an event that may
cause a change into the result state, and a root adjoined to it (36) adds its manner. The result
is then prospective: *Mary sent John a letter, but he never got it*. A root may entail an actual
caused result of its own, and the result of the template cannot be denied when the root's
entails it, as with √give (39) and √hand (49), while the root of *send* entails only that the
theme leaves the causer (52). -/

section Ditransitive

variable {Entity State Event : Type*} {M : EventStructure.Model State Event}
  {prospect : SetRel Event State} {θ : Entity → Event → Prop} {p r : State → Prop}
  {Q : Event → Prop} {x : Entity}

/-- (36): the ditransitive head with a root of manner `Q` adjoined holds of an event of the
manner whose actor is `x` and that may bring about a state of `p`. -/
def ditransitive (prospect : SetRel Event State) (θ : Entity → Event → Prop) (p : State → Prop)
    (Q : Event → Prop) (x : Entity) : Event → Prop :=
  θ x ⊓ ◇[prospect] p ⊓ Q

-- (43), (44): a result that obtains is prospective
theorem diamond_prospect_inf_eq (h : M.cause ○ M.become ⊆ prospect) (p : State → Prop) :
    ◇[prospect] p ⊓ ◇[M.cause] (◇[M.become] p) = ◇[M.cause] (◇[M.become] p) :=
  inf_eq_right.2 fun _ ⟨e, hve, s, hes, hs⟩ ↦ ⟨s, h ⟨e, hve, hes⟩, hs⟩

-- (38), (48)
theorem ditransitive_le_of_entailsCausedResult (h : M.EntailsCausedResult Q r) (hr : r ≤ p) :
    ditransitive prospect θ p Q x ≤ ◇[M.cause] (◇[M.become] p) :=
  fun v hv ↦ ModalLogic.diamond_mono _ (ModalLogic.diamond_mono _ hr) v (h v hv.2)

end Ditransitive

/-- The result a ditransitive root of the class entails, with `p` the result of the template and
`q` a further description of a state: the template's result (39), that result reached by motion
(49), or the theme's leaving the causer (52). -/
def Examples.RootClass.result? {State : Type*} (p q : State → Prop) :
    Examples.RootClass → Option (State → Prop)
  | .truePossession => some p
  | .transferByMotion => some (p ⊓ q)
  | .release => some q
  | .propertyConcept | .result => none

/-- A ditransitive with a root of the class survives the denial of the template's result when
in some interpretation the root's manner entails its caused result and an event of the
ditransitive brings about no state of the template's result. -/
def Examples.RootClass.Deniable (c : Examples.RootClass) : Prop :=
  ∃ (State Event : Type) (M : ArgumentStructure.EventStructure.Model State Event)
    (prospect : SetRel Event State) (θ : Unit → Event → Prop) (p q : State → Prop)
    (Q : Event → Prop),
    M.cause ○ M.become ⊆ prospect ∧ (∃ r ∈ c.result? p q, M.EntailsCausedResult Q r) ∧
      ∃ v, ditransitive prospect θ p Q () v ∧ ¬ ◇[M.cause] (◇[M.become] p) v

/-- (52): a throwing `false` causes a change `true` into the state `false`, in which the theme
has left the causer; the state `true`, in which the recipient has it, does not come about. -/
def thrown : ArgumentStructure.EventStructure.Model Bool Bool where
  become := {(e, s) | e = true ∧ s = false}
  cause := {(v, e) | v = false ∧ e = true}

theorem Examples.RootClass.deniable_iff (c : Examples.RootClass) :
    c.Deniable ↔ c = .release := by
  refine ⟨fun ⟨_, _, M, _, _, _, _, _, _, ⟨r, hr, h⟩, v, hv, hn⟩ ↦ ?_, ?_⟩
  · cases c
    · cases hr
    · cases hr
    · cases Option.mem_some_iff.1 hr
      exact absurd (ditransitive_le_of_entailsCausedResult h le_rfl v hv) hn
    · cases Option.mem_some_iff.1 hr
      exact absurd (ditransitive_le_of_entailsCausedResult h inf_le_left v hv) hn
    · rfl
  · rintro rfl
    exact ⟨Bool, Bool, thrown, ⊤, ⊤, (· = true), (· = false), (· = false), fun _ _ ↦ trivial,
      ⟨_, rfl, fun _ hv ↦ ⟨true, ⟨hv, rfl⟩, false, ⟨rfl, rfl⟩, rfl⟩⟩, false,
      ⟨⟨trivial, true, trivial, rfl⟩, rfl⟩,
      fun ⟨_, _, _, ⟨_, hs⟩, hp⟩ ↦ Bool.false_ne_true (hs.symm.trans hp)⟩

/-! ### The diagnostics

Each diagnostic asks whether a sentence can deny something of a root's state description: that a
change gave rise to the state, that the state held before without a change, under restitutive
*again*, or that the causer of the change acted. A root passes a diagnostic when some
interpretation that respects its signature lets the denial go through, and fails it exactly when
it carries the kinds the diagnostic detects (`passes_iff`). -/

section Diagnostics

open Presupposition

universe u

variable {Entity : Type*} {State Event : Type u}
  (M : ArgumentStructure.EventStructure.Model State Event) (θ : Entity → Event → Prop)

/-- The stative description `P` holds of `x` in the state `s`, and no change gave rise to `s`. -/
def DeniesChange (P : Entity → State → Prop) (x : Entity) : State → Prop :=
  P x ⊓ (◇[M.become.inv] ⊤)ᶜ

theorem entailsChange_iff_forall_not_deniesChange {P : Entity → State → Prop} {x : Entity} :
    M.EntailsChange (P x) ↔ ∀ s, ¬ DeniesChange M P x s :=
  forall_congr' fun _ ↦ not_and_not_right.symm

/-- The three diagnostics of a root's entailments. -/
inductive Diagnostic
  /-- The stative survives a denial that a change gave rise to its state. -/
  | changeDenial
  /-- *Again* at the state presupposes an earlier state, and no earlier change. -/
  | restitutive
  /-- The causative survives a denial that its causing event was an action of the manner. -/
  | actionDenial
  deriving DecidableEq

/-- The kinds a root carries when it fails the diagnostic: a result for the two diagnostics of
change, and a manner with a cause for the denial of action. -/
def Diagnostic.detects : Diagnostic → Finset Root.Kind
  | .changeDenial | .restitutive => {.result}
  | .actionDenial => {.manner, .cause}

/-- The state description `P` of a root with the manner `Q`, applied to `x`, passes the
diagnostic, with `R` relating a state to the earlier ones and `θ` a causer to its action. -/
def Diagnostic.Passes (R : SetRel State State) (P : Entity → State → Prop) (Q : Event → Prop)
    (x : Entity) : Diagnostic → Prop
  | .changeDenial => ∃ s, DeniesChange M P x s
  | .restitutive =>
    ∃ s, againAt M θ .state R P x x s ≠ .undefined ∧ ¬ ◇[R] (◇[M.become.inv] ⊤) s
  | .actionDenial => ∃ v, causative.denote M θ P Q x x v ∧ ¬ Q v

end Diagnostics

/-- (46a): a knife forged sharp is sharp in its first state `false`, and in its later state
`true`, which a sharpening gave rise to. -/
def forged : ArgumentStructure.EventStructure.Model Bool Unit where
  become := {(_, s) | s = true}
  cause := ⊥

/-- The knife is sharp in both of its states. -/
def sharp (_ : Unit) (_ : Bool) : Prop := True

theorem forged_deniesChange : DeniesChange forged sharp () false :=
  ⟨trivial, fun ⟨_, h, _⟩ ↦ Bool.false_ne_true h⟩

theorem not_entailsChange_sharp : ¬ forged.EntailsChange (sharp ()) :=
  fun h ↦ (entailsChange_iff_forall_not_deniesChange forged).1 h false forged_deniesChange

theorem forged_restitutive :
    againAt forged ⊤ .state {p | p.2 < p.1} sharp () () true ≠ .undefined ∧
      ¬ ◇[{p | p.2 < p.1}] (◇[forged.become.inv] ⊤) true :=
  ⟨Presupposition.again_ne_undefined_iff.2 ⟨false, Bool.false_lt_true, trivial⟩,
    fun ⟨_, hlt, _, h, _⟩ ↦ by cases (h : _ = true); exact lt_irrefl true hlt⟩

private theorem forged_respects {ks : Root} (hr : Root.Kind.result ∉ close ks) :
    forged.Respects (sharp ()) ⊥ ks :=
  have hcause : Root.Kind.cause ∉ ks := fun hk ↦ hr (mem_close.2 ⟨_, hk, .result_cause⟩)
  ⟨fun hk ↦ absurd (mem_close.2 ⟨_, hk, le_rfl⟩) hr, fun hk ↦ absurd hk hcause,
    fun _ hk ↦ absurd hk hcause⟩

/-- A root of signature `ks` passes the diagnostic when its state description passes it in some
model that respects the signature, with some manner, and in which a state arises from at most
one change. -/
def Passes (ks : Root) (g : Diagnostic) : Prop :=
  ∃ (State Event : Type) (M : ArgumentStructure.EventStructure.Model State Event)
    (θ : Unit → Event → Prop) (P : Unit → State → Prop) (Q : Event → Prop)
    (R : SetRel State State),
    (∀ s ⦃e⦄, e ~[M.become] s → ∀ ⦃e'⦄, e' ~[M.become] s → e = e') ∧
      M.Respects (P ()) Q ks ∧ g.Passes M θ R P Q ()

/-- A root passes a diagnostic exactly when its collocational closure lacks the kinds the
diagnostic detects. -/
theorem passes_iff {ks : Root} (g : Diagnostic) :
    Passes ks g ↔ ¬ g.detects ⊆ close ks := by
  cases g with
  | changeDenial =>
    simp only [Diagnostic.detects, Finset.singleton_subset_iff]
    exact ⟨fun ⟨_, _, M, _, _, _, _, _, hR, s, hs⟩ hr ↦
      (entailsChange_iff_forall_not_deniesChange M).1 (hR.entailsChange hr) s hs,
      fun hr ↦ ⟨Bool, Unit, forged, ⊤, sharp, ⊥, ⊥, fun _ _ _ _ _ ↦ rfl, forged_respects hr,
        false, forged_deniesChange⟩⟩
  | restitutive =>
    simp only [Diagnostic.detects, Finset.singleton_subset_iff]
    exact ⟨fun ⟨_, _, _, _, _, _, _, _, hR, _, ha, hn⟩ hr ↦
      hn (diamond_become_of_againAt_state_ne_undefined (hR.entailsChange hr) ha),
      fun hr ↦ ⟨Bool, Unit, forged, ⊤, sharp, ⊥, {p | p.2 < p.1}, fun _ _ _ _ _ ↦ rfl,
        forged_respects hr, true, forged_restitutive⟩⟩
  | actionDenial =>
    simp only [Diagnostic.detects, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      mem_close_iff_of_isMax Root.Kind.isMax_manner, mem_close_iff_of_isMax Root.Kind.isMax_cause]
    exact ⟨fun ⟨_, _, _, _, _, _, _, hM, hR, v, hv, hn⟩ ⟨hm, hc⟩ ↦
      hn ((hR.mannerOfCause hm hc).diamond_cause_diamond_become_le hM v hv.2),
      fun h ↦ ⟨Unit, Unit, changing, ⊤, fun _ _ ↦ True, ⊥, ⊥, fun _ _ _ _ _ ↦ rfl,
        changing_respects h, (), ⟨trivial, (), trivial, (), trivial, trivial⟩, fun h ↦ h⟩⟩

/-- The signature of a root class of chapter 2, the least the book assigns it. -/
def Examples.RootClass.kinds? : Examples.RootClass → Option Root
  | .propertyConcept => some Root.propertyConcept
  | .result => some Root.pureResult
  | .truePossession | .transferByMotion | .release => none

/-- The signature of a row's root, from its root class or its verb class. -/
def kinds? (d : Datum) : Option Root :=
  (Examples.rootClass d).bind (·.kinds?) <|>
    (Examples.verbClass d).map fun | .mannerOfKilling => fullSpec

/-- The diagnostic of a root's entailments that a row's test is. -/
def Examples.Diagnostic.toDiagnostic? :
    Examples.Diagnostic → Option BeaversKoontzGarboden2020.Diagnostic
  | .restitutiveAgain => some .restitutive
  | .actionDenial => some .actionDenial
  | .sublexicalAgain | .resultDenial | .objectDeletion => none

/-- The diagnostic a row tests. -/
def diagnostic? (d : Datum) : Option Diagnostic :=
  (Examples.diagnostic d).bind (·.toDiagnostic?)

/-- A lexicon, an assignment of a signature to the root of each row, fits the judgments when each
row that tests a diagnostic is acceptable exactly when its root passes it. -/
def Fits (σ : Datum → Root) : Prop :=
  ∀ d ∈ Examples.all, ∀ g ∈ diagnostic? d, (d.judgment = .acceptable ↔ Passes (σ d) g)

/-- The book's root classes fit the judgments of (46)–(48) and (32). -/
theorem rows : Fits fun d ↦ (kinds? d).getD ∅ := by
  simp only [Fits, passes_iff]
  decide

-- chapter 3, (10a), (11a), (48a)
theorem resultDenial_rows : ∀ d ∈ Examples.all, Examples.diagnostic d = some .resultDenial →
    ∀ c ∈ Examples.rootClass d, (d.judgment = .acceptable ↔ c.Deniable) := by
  simp only [Examples.RootClass.deniable_iff]
  decide

/-- No lexicon whose roots carry only states and manners fits the judgments: the Bifurcation
Thesis lets every root pass restitutive *again*, and the result root of *return* in (47a) does
not. -/
theorem bifurcation_thesis_false :
    ¬ ∃ σ : Datum → Root, (∀ d, close (σ d) ≤ ontological) ∧ Fits σ := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root, close s ≤ ontological →
      ¬ Diagnostic.restitutive.detects ⊆ close s := by
    decide
  exact absurd ((h Examples.bkg2020_ch2_47a (by simp [Examples.all]) .restitutive (by decide)).2
    ((passes_iff _).2 (key _ (hσ Examples.bkg2020_ch2_47a)))) (by decide)

/-- No lexicon in which no root entails both a manner and a result fits the judgments: the denial
of action fails in (32b) only for a root whose manner is that of its cause, and a cause entails a
result. -/
theorem manner_result_complementarity_false :
    ¬ ∃ σ : Datum → Root,
      (∀ d, ¬ ({.manner, .result} : Root) ≤ close (σ d)) ∧ Fits σ := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root, Diagnostic.actionDenial.detects ⊆ close s →
      ({.manner, .result} : Root) ≤ close s := by
    decide
  refine hσ Examples.bkg2020_ch4_32b (key _ ?_)
  by_contra hn
  exact absurd ((h Examples.bkg2020_ch4_32b (by simp [Examples.all]) .actionDenial (by decide)).2
    ((passes_iff _).2 hn)) (by decide)

private theorem not_subset_erase_result (s : Root) :
    ¬ ({.manner, .result} : Root) ⊆ if .manner ∈ s then s.erase .result else s := by
  intro h
  have hm := h (Finset.mem_insert_self _ _)
  have hr := h (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  split_ifs at hm hr with hk
  · exact (Finset.mem_erase.1 hr).1 rfl
  · exact hk hm

-- Read on the signatures as given rather than on their closures, Manner/Result Complementarity
-- fits the judgments: dropping the result from each root with a manner keeps its closure.
theorem exists_fits_not_mannerResult :
    ∃ σ : Datum → Root, (∀ d, ¬ ({.manner, .result} : Root) ≤ σ d) ∧ Fits σ := by
  refine ⟨fun d ↦ if .manner ∈ (kinds? d).getD ∅ then ((kinds? d).getD ∅).erase .result
    else (kinds? d).getD ∅, fun d ↦ not_subset_erase_result _, ?_⟩
  simp only [Fits, passes_iff]
  decide

/-! ### The attachment of *again* -/

-- (25), (27): each reading of *Mary flattened the rug again* is available, *again* attaching
-- at a subterm of the causative template (see `exists_denote_of_againAt_ne_undefined`)
theorem attachment_rows : ∀ d ∈ Examples.all, ∀ s ∈ Examples.attachment d,
    d.judgment = .acceptable ∧ s.template.2.IsSubterm causative := by
  have h : ∀ d ∈ Examples.all, ∀ s ∈ Examples.attachment d, d.judgment = .acceptable := by
    decide
  exact fun d hd s hs ↦ ⟨h d hd s hs, s.isSubterm⟩

/-! ### The root hypothesis against Levin's class profiles -/

/-- The root signature a class realizes, where one has been established: manner roots for the
activity classes, causative-result roots for the externally caused changes of state, pure
result roots for the internally caused ones, property concepts for the statives, the empty
signature for roots with no structural entailment. -/
def rootEntailments : LevinClass → Option Root
  -- §9 Putting: template provides CAUSE+BECOME; root content varies
  | .put => none
  | .putDirection => none
  | .funnel => some pureManner          -- manner of channeling
  | .pour => some pureManner            -- manner of pouring
  | .coil => some pureManner            -- manner of arranging
  | .sprayLoad => none
  -- §10 Removing
  | .remove => none
  | .clear => some causativeResult      -- externally caused cleared state
  | .wipeManner | .wipeInstrument => some pureManner            -- manner of surface action
  | .steal => none
  -- §11 Sending and Carrying
  | .send => none
  | .carry => some pureManner           -- manner of transport
  | .drive => some pureManner           -- manner via vehicle
  -- §12 Exerting Force
  | .pushPull => some pureManner        -- manner of force application
  -- §13 Change of Possession
  | .give => some fullSpec              -- (B&KG Ch.3) √HAND: manner + caused possession change
  | .contribute => none
  | .get | .obtain => none
  | .exchange => none
  -- §14–16
  | .learn => none
  | .hold => some propertyConcept       -- state of holding
  | .conceal => some causativeResult    -- externally caused hidden state
  -- §17 Throwing
  | .throw => some fullSpec             -- manner of propulsion + caused arrival
  -- §18 Contact by Impact
  | .hit => some pureManner             -- (B&KG Ch.4) impact manner, no state entailed
  | .swat => some pureManner            -- like hit
  | .spank => some pureManner           -- like hit
  -- §19 Poking
  | .poke => some pureManner            -- manner of contact
  -- §20 Contact: Touch
  | .touch => some ∅              -- (B&KG) no structural entailments
  -- §21 Cutting
  | .cut => some fullSpec               -- (B&KG Ch.4) cutting manner + caused separation
  | .carve => some fullSpec             -- like cut
  -- §22 Combining and Attaching
  | .mix => some causativeResult        -- externally caused combined state
  | .amalgamate => some causativeResult
  -- §23 Separating
  | .separate => some causativeResult   -- externally caused separated state
  | .split => some fullSpec             -- instrument manner + caused separation
  -- §24 Coloring
  | .color => some causativeResult      -- externally caused colored state
  -- §25 Image Creation
  | .imageImpression | .scribble | .illustrate | .transcribe =>
    some fullSpec
  -- §26 Creation and Transformation
  | .build => some causativeResult      -- externally caused creation
  | .grow => some pureResult            -- internally caused growth
  | .create => some causativeResult     -- externally caused creation
  | .knead => some fullSpec             -- kneading manner + caused shape change
  | .turn => some causativeResult       -- externally caused transformation
  | .performance => some pureManner     -- performance manner
  -- §27–28
  | .engender => some causativeResult   -- root entails causation
  | .calve => some pureResult           -- internally caused biological process
  -- §29 Predicative Complements
  | .appoint => some causativeResult    -- externally caused status change
  | .characterize => none
  | .declare => some causativeResult    -- externally caused status change
  -- §30 Perception
  | .see => none
  | .sight => none
  -- §31 Psych-Verbs
  | .amuse => some causativeResult      -- stimulus causes psychological CoS
  | .admire => some propertyConcept     -- psychological state
  | .marvel => some propertyConcept     -- psychological state
  -- §32–34
  | .want => some propertyConcept       -- desiderative state
  | .long => some propertyConcept       -- desiderative state
  | .judgment => none
  | .assessment => none
  -- §35 Searching
  | .hunt | .search | .stalk | .investigate | .rummage | .ferret =>
    some pureManner
  -- §36 Social Interaction
  | .correspond | .marry | .meet => none
  -- §37 Communication
  | .say => none
  | .tell => none
  | .mannerOfSpeaking => some pureManner -- manner of speaking
  | .talk => none
  -- §38 Animal Sounds
  | .animalSound => some pureManner     -- specific sound manner
  -- §39 Ingesting
  | .eat => some causativeResult        -- caused consumption, no specific manner
  | .devour => some fullSpec            -- vigorous manner + caused consumption
  | .dine => some pureManner            -- social activity manner
  -- §40 Body
  | .hiccup | .breathe | .exhale => none
  | .nonverbalExpression => none
  | .flinch => none
  | .hurt => some causativeResult       -- externally caused injury
  -- §41 Grooming
  | .dress => some causativeResult      -- externally caused dressed state
  -- §42 Killing
  | .murder => some causativeResult     -- (B&KG) root entails caused death
  | .poison => some fullSpec            -- (B&KG) poisoning manner + caused death (√DROWN-type)
  -- §43 Emission
  | .lightEmission => some propertyConcept  -- emitting state
  | .soundEmission => some propertyConcept
  | .substanceEmission => some propertyConcept
  -- §44 Destroy
  | .destroy => some causativeResult    -- (B&KG) root entails caused total destruction
  -- §45 Change of State
  | .break_ => some causativeResult     -- (B&KG Ch.2,5) √CRACK: externally caused CoS
  | .bend => some causativeResult       -- externally caused shape change
  | .cooking => some causativeResult    -- externally caused CoS; √cook has no manner (B&KG (41))
  | .otherChangeOfState => some causativeResult   -- √MELT/√FREEZE: externally caused CoS
  | .entitySpecificChangeOfState => some pureResult -- √BLOSSOM/√RUST: internally caused
  | .calibratableChangeOfState => some pureResult -- internally driven scalar change
  -- §46 Lodge
  | .lodge => none
  -- §47 Existence
  | .exist => some ∅              -- (B&KG) pure stative, no root content
  -- §48 Appearance, Disappearance
  | .appear | .reflexiveAppearance => some pureResult          -- internally caused appearance
  | .disappearance => some pureResult   -- internally caused going out of existence
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => some pureManner -- fidgeting manner
  -- §50 Assuming a Position
  | .assumePosition => some pureResult  -- internally caused position change
  -- §51 Motion
  | .inherentlyDirectedMotion => some pureResult -- internally caused directed motion
  | .leave => some pureResult           -- internally caused departure
  | .roll | .run => some pureManner  -- (B&KG) √JOG: motion manner
  | .vehicleName | .nonVehicleName => some pureManner   -- vehicle manner
  | .chase => some pureManner           -- chasing manner
  -- §52 Avoid
  | .avoid => none
  -- §53 Lingering and Rushing
  | .linger => some pureManner          -- temporal manner
  | .rush => some pureManner            -- temporal manner
  -- §54 Measure
  | .register | .cost | .fit | .price | .bill => some propertyConcept    -- measurement state
  -- §55 Aspectual
  | .begin | .complete => none
  -- §57 Weather
  | .weather => none
  | _ => none

theorem rootEntailments_wellFormed (c : LevinClass) (s : Root)
    (h : rootEntailments c = some s) : s.WellFormed := by
  cases c <;> cases h <;> decide

/-- The classes whose root entails a caused change without a manner and that still lack an
inchoative variant, for the two reasons the book gives (p. 63): *murder* restricts its causer to
an agent, and *destroy* lacks one "for purely idiosyncratic reasons". -/
def causativeExceptions : Finset LevinClass := {.destroy, .murder}

/-- The root hypothesis: a class alternates between causative and inchoative when its root
entails a caused change and no manner, outside the classes that lack an inchoative for other
reasons. -/
def RootPredictsCausative (c : LevinClass) : Prop :=
  (∃ s ∈ rootEntailments c, Root.Kind.cause ∈ s ∧ Root.Kind.manner ∉ s) ∧
    c ∉ causativeExceptions

instance : DecidablePred RootPredictsCausative := fun _ ↦
  inferInstanceAs (Decidable ((∃ s ∈ _, _ ∧ _) ∧ _))

/-- A class Part II of [levin-1993] tests for the causative alternation and whose root
signature is recorded. -/
def TestedForCausative (c : LevinClass) : Prop :=
  rootEntailments c ≠ none ∧ c.Tests .causativeInchoative

instance : DecidablePred TestedForCausative := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The tested classes on which the root hypothesis and the class pages disagree. The verbs of
creation and the psych causatives have causative-result roots that the hypothesis predicts to
alternate although the pages star the alternation. The other classes have pages that attest it
without a manner-free causative root, namely the manner-and-result roots, the internally caused
result of the grow verbs, and the pure-manner roots of the coil and roll verbs. -/
def rootHypothesisResidue : Finset LevinClass :=
  {LevinClass.build, .create, .engender, .amuse, .split, .knead, .grow, .coil, .roll}

theorem rootHypothesis_matches_profile :
    ∀ c : LevinClass, TestedForCausative c → c ∉ rootHypothesisResidue →
      (RootPredictsCausative c ↔ c.Participates .causativeInchoative) := by
  decide +kernel

theorem rootHypothesisResidue_disagrees :
    ∀ c ∈ rootHypothesisResidue, TestedForCausative c ∧
      ¬ (RootPredictsCausative c ↔ c.Participates .causativeInchoative) := by
  decide +kernel

end BeaversKoontzGarboden2020
