module

public import Linglib.Semantics.Root.Defs
public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.RootEntailment
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Presupposition.Again
public import Linglib.Data.Examples.BeaversKoontzGarboden2020

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

This file formalizes the root typology of Beavers and Koontz-Garboden's book and the two theses
it refutes. A root carries entailments of four kinds, manner, cause, result and state. The
Bifurcation Thesis holds that a root carries only a state or a manner, all eventive content
belonging to the verbal template, and Manner/Result Complementarity holds that no root entails
both a manner and a result. The book's diagnostics refute both. Result roots allow no truly
restitutive reading of *again*, so no lexicon that obeys the first fits the judgments
(`bifurcation_thesis_false`); the causer of *drown* cannot be denied to have acted, so none that
obeys the second fits them either (`manner_result_complementarity_false`). The book's own root
classes fit every judgment its diagnostics read (`rows`).

The typology (12) crosses the well-formed signatures with the two positions of a root. The book
accounts for its empty cells by markedness, an adjoined root describing a manner and a
complement root a state, and by naturalness, a root that describes a manner and a state also
entailing the causation that would relate them; together these carve out exactly the filled
cells (`mem_attestedCells_iff`). No event template relates a manner and a state other than by
causation (`Template.hasCause_of_mem_kinds`), and the attested rows are exactly the signatures
of the templates of the basic inventory, as (13) shows (`attestedRows_eq_kinds_templates`).

The modifier *again* attaches to the root, to `vbecome` or to `vcause`, the three subterms of
the causative template, and the entailments among its three readings follow from the subterm
order (`Template.exists_denote_of_isSubterm`). The book's hypothesis about which roots alternate
between a causative and an inchoative is compared with the class pages of Levin's *English Verb
Classes and Alternations* (`rootHypothesis_matches_profile`).

## Implementation notes

* The state entailments of the result roots are derived by the collocational closure of the
  kind signature (`Root.closedKinds`).
* A root is its meaning; the six roots carry their signatures and leave their content
  unannotated, so √hand and √drown coincide as values, and the position of each root is
  recorded beside it in `sample`.
* The third clause of `mem_attestedCells_iff` is the book's naturalness argument for the row
  with a manner and a state alone. For the row that adds a change without a cause, the book
  leaves open whether a change and a manner can combine without causation (p. 230).
* The thesis predicates are the apparatus of this study alone.
* A diagnostic is a property of a root's state description in an interpretation, and a lexicon,
  an assignment of signatures to the rows' roots, fits the judgments when each row is acceptable
  exactly when its root passes the row's diagnostic. The denial of action is modelled as the
  book applies it to the manner of killing verbs, on a causative, where it denies that the cause
  of the change is an action of the root's manner; the denial of action with a pure manner verb
  denies the verb's own event and is not modelled.
* The result-denial rows test whether a verb entails its result state, which in the ditransitive
  rows depends on the template as well as the root (§3.3.1), and are not read; the attachment
  rows of *again* are read by `againAt`.

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

open ArgumentStructure ArgumentStructure.Root.Kinds
open scoped SetRel ModalLogic

/-! ### The two theses, at signature level -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root.Kinds := {.state, .manner}

/-- A signature violates the Bifurcation Thesis when it carries templatic, eventive content,
that is, when it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Root.Kinds) : Prop := ¬ s ≤ ontological

instance : DecidablePred ViolatesBifurcation := fun _ ↦ inferInstanceAs (Decidable (¬ _ ≤ _))

theorem violatesBifurcation_iff :
    ∀ s, ViolatesBifurcation s ↔ .result ∈ s ∨ .cause ∈ s := by decide

theorem violatesBifurcation_monotone : Monotone ViolatesBifurcation :=
  fun _ _ hst hs ht ↦ hs (hst.trans ht)

/-- A signature has both manner and result, the configuration that Manner/Result
Complementarity claims no root realizes. -/
def HasMannerAndResult (s : Root.Kinds) : Prop := ({.manner, .result} : Root.Kinds) ≤ s

instance : DecidablePred HasMannerAndResult := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

theorem hasMannerAndResult_monotone : Monotone HasMannerAndResult :=
  fun _ _ hst h ↦ h.trans hst

theorem violatesBifurcation_close_iff :
    ∀ s, ViolatesBifurcation (close s) ↔ ViolatesBifurcation s := by decide

theorem hasMannerAndResult_close_iff :
    ∀ s, HasMannerAndResult (close s) ↔ HasMannerAndResult s ∨ (.manner ∈ s ∧ .cause ∈ s) := by
  decide

/-! ### The typology -/

/-- The seven rows of the typology (12). -/
def typology : Finset Root.Kinds :=
  {propertyConcept, pureResult, causativeResult, pureManner, {.state, .manner},
   {.state, .manner, .result}, fullSpec}

-- (12), p. 227
theorem wellFormed_iff_mem_typology :
    ∀ s : Root.Kinds, s.WellFormed ↔ s = ∅ ∨ s ∈ typology := by decide

/-- The filled cells of (12), pairs of a closed signature and a position. -/
def attestedCells : Finset (Root.Kinds × Root.Position) :=
  {(propertyConcept, .complement), (pureResult, .complement), (causativeResult, .complement),
   (pureManner, .adjoined), (fullSpec, .adjoined), (fullSpec, .complement)}

/-- The filled cells of (12) are those where an adjoined root is a manner, a complement root a
state, and manner with state entails cause (pp. 229–230). -/
theorem mem_attestedCells_iff : ∀ (s : Root.Kinds) (p : Root.Position),
    (s, p) ∈ attestedCells ↔ s ∈ typology ∧ (p = .adjoined → .manner ∈ s) ∧
      (p = .complement → .state ∈ s) ∧ (.manner ∈ s → .state ∈ s → .cause ∈ s) := by
  decide

section Again

open Presupposition ModalLogic ArgumentStructure EventStructure Template
open scoped SetRel

/-! ### Sublexical *again* and the hierarchy of its readings

*Again* is a presupposition trigger that can attach at three points in the change-of-state
structure, the root, `vbecome` and `vcause` (27), which yields the three readings of *Mary
flattened the rug again* (25): the restitutive one, that the rug had been flat, the repetitive
one over the change, that it had flattened, and the repetitive one over the causation, that
Mary had flattened it. The three points are the subterms `state` and `achievement` of the
causative template (18c), `[y CAUSE [x BECOME P]]`, and the template itself, `causative`, whose
causing subevent is an eventuality with the causer as effector
(`Template.denote_cause_effector`), and the entry for *again* is `Presupposition.again`. The
hierarchy of the readings is the subterm order: attached at a template, *again* presupposes
that each of its subterms was realized. -/

universe u

variable {Entity : Type*} {State Event : Type u} (M : Interpretation Entity State Event)
  {σ τ : Eventuality} {P : Entity → State → Prop} {y x : Entity}

/-- The causative change-of-state template (18c), `[y CAUSE [x BECOME P]]`. -/
def causative : Template .event := .cause .effector .achievement

/-- *Again* attached at the subterm `t` of the causative template of a root with state predicate
`P`, with `R` relating an eventuality of the sort of `t` to the earlier ones. The attachment at
`state` gives the restitutive reading, at `achievement` the repetitive reading over the change,
and at `causative` the repetitive reading over the causation. -/
noncomputable def againAt (t : Template σ)
    (R : SetRel (σ.Carrier State Event) (σ.Carrier State Event)) (P : Entity → State → Prop)
    (y x : Entity) : σ.Carrier State Event → SignType :=
  again R (t.denote M P ⊤ y x)

variable {M}

theorem exists_denote_of_againAt_ne_zero {t : Template σ} {u : Template τ} (hu : u.IsSubterm t)
    {R : SetRel (σ.Carrier State Event) (σ.Carrier State Event)} {w : σ.Carrier State Event}
    (h : againAt M t R P y x w ≠ 0) : ∃ w', w ~[R] w' ∧ ∃ y' v, u.denote M P ⊤ y' x v :=
  diamond_mono R (fun _ ↦ exists_denote_of_isSubterm hu) w (again_ne_zero_iff.1 h)

theorem diamond_vCause_of_againAt_causative_ne_zero {R : SetRel Event Event} {w : Event}
    (h : againAt M causative R P y x w ≠ 0) : ◇[R] (M.vCause (M.vBecome P x)) w :=
  diamond_mono R (fun _ h ↦ h.2) w (again_ne_zero_iff.1 h)

theorem diamond_become_of_againAt_state_ne_zero {R : SetRel State State} {s : State}
    (hres : M.EntailsChange P) (h : againAt M .state R P y x s ≠ 0) :
    ◇[R] (◇[M.become] ⊤) s :=
  diamond_mono R (hres x) s (again_ne_zero_iff.1 h)

end Again

/-! ### The typology and the templates -/

section Templates

open ArgumentStructure EventStructure Template

variable {σ : Eventuality}

/-- The attested rows of (12) are the signatures of the state, activity, achievement and two
accomplishment templates ((13), p. 231). -/
theorem attestedRows_eq_kinds_templates :
    attestedCells.image Prod.fst =
      {state.kinds, act.kinds, achievement.kinds, causative.kinds, accomplishment.kinds} := by
  decide

theorem kinds_ne_of_cause_not_mem {t : Template σ} {s : Root.Kinds} (hm : .manner ∈ s)
    (hs : .state ∈ s) (hc : .cause ∉ s) : t.kinds ≠ s := by
  rintro rfl; exact hc (hasCause_of_mem_kinds hm hs)

-- (12), p. 230
theorem kinds_ne_emptyRows (t : Template σ) :
    t.kinds ≠ {.state, .manner} ∧ t.kinds ≠ {.state, .manner, .result} :=
  ⟨kinds_ne_of_cause_not_mem (by decide) (by decide) (by decide),
    kinds_ne_of_cause_not_mem (by decide) (by decide) (by decide)⟩

end Templates

/-! ### The six representative roots -/

/-- √flat is a pure state root. -/
def flat : Root := { kinds := {.state} }

/-- √jog is a pure manner-of-motion root, its manner the jogging gait. -/
def jog : Root := { kinds := {.manner} }

/-- √blossom is a result root with no specified manner or cause, an internally caused change
into flowering. -/
def blossom : Root := { kinds := {.result} }

/-- √crack is a caused-result root without a specified manner, a caused change into a fissured
state. -/
def crack : Root := { kinds := {.result, .cause} }

/-- √hand carries manner, cause and result, a transfer by hand into the recipient's possession.
The possession result is not cancelable (*Mary handed John the book, #but it never came to be
on his person*), so it is entailed by the root rather than implicated. -/
def hand : Root := { kinds := {.manner, .result, .cause} }

/-- √drown is a manner-of-killing root, death by submersion in liquid, carrying manner, cause
and result. -/
def drown : Root := { kinds := {.manner, .result, .cause} }

/-- The six roots with the position each occupies in (12), √hand adjoined and √drown a
complement. -/
def sample : List (Root × Root.Position) :=
  [(flat, .complement), (jog, .adjoined), (blossom, .complement), (crack, .complement),
   (hand, .adjoined), (drown, .complement)]

/-! ### Closed signatures

The closed signatures of the roots are the rows of the typology they fill. -/

theorem flat_closedKinds : flat.closedKinds = propertyConcept := by decide

theorem jog_closedKinds : jog.closedKinds = pureManner := by decide

theorem blossom_closedKinds : blossom.closedKinds = pureResult := by decide

theorem crack_closedKinds : crack.closedKinds = causativeResult := by decide

theorem hand_closedKinds : hand.closedKinds = fullSpec := by decide

theorem drown_closedKinds : drown.closedKinds = fullSpec := by decide

-- (12)
theorem attestedCells_eq_sample :
    attestedCells = (sample.map fun c ↦ (c.1.closedKinds, c.2)).toFinset := by decide

theorem hand_drown_differ_in_position :
    hand.closedKinds = drown.closedKinds ∧ (hand, .adjoined) ∈ sample ∧
      (drown, .complement) ∈ sample := by decide

/-! ### The entailments of the roots in a model

The kinds of a root are meaning postulates on its state and manner predicates
(`EventStructure.Interpretation.Respects`). In an interpretation that respects the signature of
√crack, a cracked state arises from a caused change whatever template the root occurs in, while
one that respects the signature of √flat may have a flat state that no change gave rise to. -/

section Model

open ArgumentStructure

variable {Entity State Event : Type*} {M : EventStructure.Interpretation Entity State Event}
  {P : Entity → State → Prop} {Q : Event → Prop} {x : Entity} {s : State}

theorem crack_entails_cause (h : M.Respects P Q crack.kinds) (hs : P x s) :
    ◇[M.become] (◇[M.cause.inv] ⊤) s :=
  h .cause (by decide) x s hs

theorem drown_entails_manner (h : M.Respects P Q drown.kinds) (hs : P x s) :
    ◇[M.become] (□[M.cause.inv] Q) s :=
  h .mannerOfCause (by decide) x s hs

end Model

/-- A model without changes. -/
def unchanging : ArgumentStructure.EventStructure.Interpretation Unit Unit Unit where
  become := ⊥
  cause := ⊥
  effector := ⊥

/-- A model in which every state arises from a caused change. -/
def changing : ArgumentStructure.EventStructure.Interpretation Unit Unit Unit where
  become := ⊤
  cause := ⊤
  effector := ⊤

theorem flat_not_entailsChange :
    unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) flat.kinds ∧
      ¬ unchanging.EntailsChange (fun _ _ ↦ True) :=
  ⟨fun p hp ↦ absurd hp (by cases p <;> decide), fun h ↦ let ⟨_, he, _⟩ := h () () trivial; he⟩

theorem crack_respects :
    changing.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds ∧
      ¬ unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds :=
  ⟨fun p hp ↦ by
      cases p
      · exact fun _ _ _ ↦ ⟨(), trivial, trivial⟩
      · exact fun _ _ _ ↦ ⟨(), trivial, (), trivial, trivial⟩
      all_goals exact absurd hp (by decide),
    fun h ↦ let ⟨_, he, _⟩ := crack_entails_cause h (x := ()) (s := ()) trivial; he⟩

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
  (M : ArgumentStructure.EventStructure.Interpretation Entity State Event)

/-- The stative description `P` holds of `x` in the state `s`, and no change gave rise to `s`. -/
def DeniesChange (P : Entity → State → Prop) (x : Entity) : State → Prop :=
  P x ⊓ (◇[M.become] ⊤)ᶜ

theorem entailsChange_iff_forall_not_deniesChange {P : Entity → State → Prop} :
    M.EntailsChange P ↔ ∀ x s, ¬ DeniesChange M P x s :=
  forall₂_congr fun _ _ ↦ not_and_not_right.symm

/-- The three diagnostics of a root's entailments. -/
inductive Diagnostic
  /-- The stative survives a denial that a change gave rise to its state. -/
  | changeDenial
  /-- *Again* at the state presupposes an earlier state, and no earlier change. -/
  | restitutive
  /-- The causative survives a denial that its causer acted. -/
  | actionDenial
  deriving DecidableEq

/-- The kinds a root carries when it fails the diagnostic: a result for the two diagnostics of
change, and a manner with a cause for the denial of action. -/
def Diagnostic.detects : Diagnostic → Root.Kinds
  | .changeDenial | .restitutive => {.result}
  | .actionDenial => {.manner, .cause}

/-- The state description `P` of a root with the manner `Q`, applied to `x`, passes the
diagnostic, with `R` relating a state to the earlier ones. -/
def Diagnostic.Passes (R : SetRel State State) (P : Entity → State → Prop) (Q : Event → Prop)
    (x : Entity) : Diagnostic → Prop
  | .changeDenial => ∃ s, DeniesChange M P x s
  | .restitutive => ∃ s, againAt M .state R P x x s ≠ 0 ∧ ¬ ◇[R] (◇[M.become] ⊤) s
  | .actionDenial => ∃ s, P x s ∧ ¬ ◇[M.become] (□[M.cause.inv] Q) s

end Diagnostics

/-- (46a): a knife forged sharp is sharp in its first state `false`, and in its later state
`true`, which a sharpening gave rise to. -/
def forged : ArgumentStructure.EventStructure.Interpretation Unit Bool Unit where
  become := {p | p.1 = true}
  cause := ⊥
  effector := ⊥

/-- The knife is sharp in both of its states. -/
def sharp (_ : Unit) (_ : Bool) : Prop := True

theorem forged_deniesChange : DeniesChange forged sharp () false :=
  ⟨trivial, fun ⟨_, h, _⟩ ↦ Bool.false_ne_true h⟩

theorem not_entailsChange_sharp : ¬ forged.EntailsChange sharp :=
  fun h ↦ (entailsChange_iff_forall_not_deniesChange forged).1 h () false forged_deniesChange

theorem forged_restitutive :
    againAt forged .state {p | p.2 < p.1} sharp () () true ≠ 0 ∧
      ¬ ◇[{p | p.2 < p.1}] (◇[forged.become] ⊤) true :=
  ⟨Presupposition.again_ne_zero_iff.2 ⟨false, Bool.false_lt_true, trivial⟩,
    fun ⟨_, hlt, _, h, _⟩ ↦ by cases (h : _ = true); exact lt_irrefl true hlt⟩

/-- A root of signature `ks` passes the diagnostic when its state description passes it in some
model that respects the signature, with some manner. -/
def Passes (ks : Root.Kinds) (g : Diagnostic) : Prop :=
  ∃ (State Event : Type) (M : ArgumentStructure.EventStructure.Interpretation Unit State Event)
    (P : Unit → State → Prop) (Q : Event → Prop) (R : SetRel State State),
    M.Respects P Q ks ∧ g.Passes M R P Q ()

private theorem passes_iff_of_ne {ks : Root.Kinds} {g : Diagnostic} (hg : g ≠ .actionDenial) :
    Passes ks g ↔ Root.Kind.result ∉ close ks := by
  refine ⟨fun ⟨_, _, M, P, Q, R, hR, hp⟩ hr ↦ ?_, fun hr ↦ ⟨Bool, Unit, forged, sharp, ⊥,
    {p | p.2 < p.1}, fun p hp ↦ ?_, ?_⟩⟩
  · have hc := hR.entailsChange hr
    cases g with
    | changeDenial =>
      obtain ⟨s, hs⟩ := hp
      exact (entailsChange_iff_forall_not_deniesChange M).1 hc () s hs
    | restitutive =>
      obtain ⟨s, ha, hn⟩ := hp
      exact hn (diamond_become_of_againAt_state_ne_zero hc ha)
    | actionDenial => exact hg rfl
  · have hcause : Root.Kind.cause ∉ ks := fun hk ↦ hr (mem_close.2 ⟨_, hk, .result_cause⟩)
    cases p with
    | change => exact absurd (mem_close.2 ⟨_, Finset.singleton_subset_iff.1 hp, le_rfl⟩) hr
    | cause => exact absurd (Finset.singleton_subset_iff.1 hp) hcause
    | manner => exact fun _ h ↦ h.elim
    | mannerOfCause => exact absurd (Finset.insert_subset_iff.1 hp).2 (by simpa using hcause)
  · cases g with
    | changeDenial => exact ⟨false, forged_deniesChange⟩
    | restitutive => exact ⟨true, forged_restitutive⟩
    | actionDenial => exact absurd rfl hg

private theorem passes_actionDenial_iff {ks : Root.Kinds} :
    Passes ks .actionDenial ↔ ¬ (Root.Kind.manner ∈ ks ∧ Root.Kind.cause ∈ ks) := by
  refine ⟨fun ⟨_, _, M, P, Q, R, hR, s, hs, hn⟩ ⟨hm, hc⟩ ↦ hn ?_,
    fun h ↦ ⟨Unit, Unit, changing, fun _ _ ↦ True, ⊥, ⊥, fun p hp ↦ ?_, (), trivial, ?_⟩⟩
  · exact hR .mannerOfCause (Finset.insert_subset_iff.2 ⟨hm, Finset.singleton_subset_iff.2 hc⟩)
      () s hs
  · cases p with
    | change => exact fun _ _ _ ↦ ⟨(), trivial, trivial⟩
    | cause => exact fun _ _ _ ↦ ⟨(), trivial, (), trivial, trivial⟩
    | manner => exact fun _ h ↦ h.elim
    | mannerOfCause =>
      exact absurd ⟨(Finset.insert_subset_iff.1 hp).1,
        Finset.singleton_subset_iff.1 (Finset.insert_subset_iff.1 hp).2⟩ h
  · exact fun ⟨_, _, hbox⟩ ↦ hbox () trivial

/-- A root passes a diagnostic exactly when its collocational closure lacks the kinds the
diagnostic detects. -/
theorem passes_iff {ks : Root.Kinds} (g : Diagnostic) :
    Passes ks g ↔ ¬ g.detects ⊆ close ks := by
  cases g with
  | changeDenial =>
    simpa only [Diagnostic.detects, Finset.singleton_subset_iff] using
      passes_iff_of_ne (ks := ks) (g := .changeDenial) (by decide)
  | restitutive =>
    simpa only [Diagnostic.detects, Finset.singleton_subset_iff] using
      passes_iff_of_ne (ks := ks) (g := .restitutive) (by decide)
  | actionDenial =>
    simpa only [Diagnostic.detects, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      mem_close_iff_of_isMax Root.Kind.isMax_manner, mem_close_iff_of_isMax Root.Kind.isMax_cause]
      using passes_actionDenial_iff (ks := ks)

/-- The signature of a row's root, the least of the class the book assigns it. -/
def kinds? (d : Datum) : Option Root.Kinds :=
  d.parse? "root class" [("property concept", propertyConcept), ("result", pureResult)] <|>
    d.parse? "verb class" [("manner of killing", fullSpec)]

/-- The diagnostic a row tests. -/
def diagnostic? (d : Datum) : Option Diagnostic :=
  d.parse? "diagnostic" [("restitutive again", .restitutive), ("action denial", .actionDenial)]

-- (46)–(48), (32)
theorem rows : ∀ d ∈ Examples.all, ∀ ks ∈ kinds? d, ∀ g ∈ diagnostic? d,
    (d.judgment = .acceptable ↔ Passes ks g) := by
  simp only [passes_iff]
  decide

/-- No lexicon whose roots carry only states and manners fits the judgments: the Bifurcation
Thesis lets every root pass restitutive *again*, and the result root of *return* in (47a) does
not. -/
theorem bifurcation_thesis_false :
    ¬ ∃ σ : Datum → Root.Kinds, (∀ d, σ d ≤ ontological) ∧
      ∀ d ∈ Examples.all, ∀ g ∈ diagnostic? d, (d.judgment = .acceptable ↔ Passes (σ d) g) := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root.Kinds, s ≤ ontological → ¬ Diagnostic.restitutive.detects ⊆ close s := by
    decide
  exact absurd ((h Examples.bkg2020_ch2_47a (by simp [Examples.all]) .restitutive (by decide)).2
    ((passes_iff _).2 (key _ (hσ Examples.bkg2020_ch2_47a)))) (by decide)

/-- No lexicon in which no root carries both a manner and a result fits the judgments: the
denial of action fails in (32b) only for a root whose manner is that of its cause, which with
the cause carries a result. -/
theorem manner_result_complementarity_false :
    ¬ ∃ σ : Datum → Root.Kinds, (∀ d, ¬ HasMannerAndResult (close (σ d))) ∧
      ∀ d ∈ Examples.all, ∀ g ∈ diagnostic? d, (d.judgment = .acceptable ↔ Passes (σ d) g) := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root.Kinds, Diagnostic.actionDenial.detects ⊆ close s →
      HasMannerAndResult (close s) := by
    decide
  refine hσ Examples.bkg2020_ch4_32b (key _ (not_not.1 fun hn ↦ ?_))
  exact absurd ((h Examples.bkg2020_ch4_32b (by simp [Examples.all]) .actionDenial (by decide)).2
    ((passes_iff _).2 hn)) (by decide)

/-! ### The root hypothesis against Levin's class profiles -/

open ArgumentStructure

/-- A class Part II of [levin-1993] tests for the causative alternation and whose root
signature is recorded. -/
def TestedForCausative (c : LevinClass) : Prop :=
  c.rootEntailments.isSome ∧ c.Tests .causativeInchoative

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
      (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

theorem rootHypothesisResidue_disagrees :
    ∀ c ∈ rootHypothesisResidue, TestedForCausative c ∧
      ¬ (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

end BeaversKoontzGarboden2020
