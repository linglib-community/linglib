module

public import Linglib.Semantics.Root.Defs
public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Semantics.Root.Kinds
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Presupposition.Again
public import Linglib.Data.Examples.BeaversKoontzGarboden2020

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
  collocational closure of the signature (`Root.closedKinds`). The refutation of Manner/Result
  Complementarity rests on the second: read on the signatures as given, the thesis
  [is consistent with the judgments](##exists_fits_not_mannerResult).
* A root is its meaning; the six roots carry their signatures and leave their content
  unannotated, so √hand and √drown coincide as values, and the position of each root is
  recorded beside it in `sample`.
* The third clause of `mem_attestedCells_iff` is the book's naturalness argument for the row
  with a manner and a state alone; for the row that adds a change without a cause the book leaves
  open whether a change and a manner can combine without causation.
* The signatures of the Levin classes are this study's (`rootEntailments`), and the book's
  hypothesis about which roots alternate is compared with the class pages of [levin-1993]
  (`rootHypothesis_matches_profile`, `rootHypothesisResidue_disagrees`).
* A diagnostic is a property of a root's state description in an interpretation, passed when some
  interpretation that respects the signature lets the denial go through (`passes_iff`). The
  denial of action is modelled as the book applies it to the manner of killing verbs, on a
  causative; with a pure manner verb it denies the verb's own event and is not modelled.
* The result-denial rows, which in the ditransitives depend on the template as well as the root,
  and the object-deletion row are not read; the rows of the three attachments of *again* are read
  by `attachment_rows`.

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

/-! ### The ontological kinds -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root.Kinds := {.state, .manner}

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

open Presupposition ModalLogic EventStructure Template

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

/-- The three attachment sites of *again* (27). -/
inductive Site
  /-- The root, for the restitutive reading. -/
  | root
  /-- `vbecome`, for the repetitive reading over the change. -/
  | vBecome
  /-- `vcause`, for the repetitive reading over the causation. -/
  | vCause
  deriving DecidableEq

/-- The subterm of the causative template at a site. -/
def Site.template : Site → Σ σ, Template σ
  | .root => ⟨_, .state⟩
  | .vBecome => ⟨_, .achievement⟩
  | .vCause => ⟨_, causative⟩

theorem Site.isSubterm (s : Site) : s.template.2.IsSubterm causative := by
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

private theorem changing_respects {ks : Root.Kinds}
    (h : ¬ (Root.Kind.manner ∈ ks ∧ Root.Kind.cause ∈ ks)) :
    changing.Respects (fun _ _ ↦ True) ⊥ ks := fun p hp ↦ by
  cases p with
  | change => exact fun _ _ _ ↦ ⟨(), trivial, trivial⟩
  | cause => exact fun _ _ _ ↦ ⟨(), trivial, (), trivial, trivial⟩
  | manner => exact fun _ h ↦ h.elim
  | mannerOfCause =>
    exact absurd ⟨(Finset.insert_subset_iff.1 hp).1,
      Finset.singleton_subset_iff.1 (Finset.insert_subset_iff.1 hp).2⟩ h

theorem crack_respects :
    changing.Respects (fun _ _ ↦ True) ⊥ crack.kinds ∧
      ¬ unchanging.Respects (fun _ _ ↦ True) ⊥ crack.kinds :=
  ⟨changing_respects (by decide),
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

private theorem forged_respects {ks : Root.Kinds} (hr : Root.Kind.result ∉ close ks) :
    forged.Respects sharp ⊥ ks := fun p hp ↦ by
  have hcause : Root.Kind.cause ∉ ks := fun hk ↦ hr (mem_close.2 ⟨_, hk, .result_cause⟩)
  cases p with
  | change => exact absurd (mem_close.2 ⟨_, Finset.singleton_subset_iff.1 hp, le_rfl⟩) hr
  | cause => exact absurd (Finset.singleton_subset_iff.1 hp) hcause
  | manner => exact fun _ h ↦ h.elim
  | mannerOfCause => exact absurd (Finset.insert_subset_iff.1 hp).2 (by simpa using hcause)

/-- A root of signature `ks` passes the diagnostic when its state description passes it in some
model that respects the signature, with some manner. -/
def Passes (ks : Root.Kinds) (g : Diagnostic) : Prop :=
  ∃ (State Event : Type) (M : ArgumentStructure.EventStructure.Interpretation Unit State Event)
    (P : Unit → State → Prop) (Q : Event → Prop) (R : SetRel State State),
    M.Respects P Q ks ∧ g.Passes M R P Q ()

/-- A root passes a diagnostic exactly when its collocational closure lacks the kinds the
diagnostic detects. -/
theorem passes_iff {ks : Root.Kinds} (g : Diagnostic) :
    Passes ks g ↔ ¬ g.detects ⊆ close ks := by
  cases g with
  | changeDenial =>
    simp only [Diagnostic.detects, Finset.singleton_subset_iff]
    exact ⟨fun ⟨_, _, M, _, _, _, hR, s, hs⟩ hr ↦
      (entailsChange_iff_forall_not_deniesChange M).1 (hR.entailsChange hr) () s hs,
      fun hr ↦ ⟨Bool, Unit, forged, sharp, ⊥, ⊥, forged_respects hr, false, forged_deniesChange⟩⟩
  | restitutive =>
    simp only [Diagnostic.detects, Finset.singleton_subset_iff]
    exact ⟨fun ⟨_, _, _, _, _, _, hR, _, ha, hn⟩ hr ↦
      hn (diamond_become_of_againAt_state_ne_zero (hR.entailsChange hr) ha),
      fun hr ↦ ⟨Bool, Unit, forged, sharp, ⊥, {p | p.2 < p.1}, forged_respects hr, true,
        forged_restitutive⟩⟩
  | actionDenial =>
    simp only [Diagnostic.detects, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      mem_close_iff_of_isMax Root.Kind.isMax_manner, mem_close_iff_of_isMax Root.Kind.isMax_cause]
    exact ⟨fun ⟨_, _, _, _, _, _, hR, s, hs, hn⟩ ⟨hm, hc⟩ ↦
      hn (hR .mannerOfCause (Finset.insert_subset_iff.2 ⟨hm, Finset.singleton_subset_iff.2 hc⟩)
        () s hs),
      fun h ↦ ⟨Unit, Unit, changing, fun _ _ ↦ True, ⊥, ⊥, changing_respects h, (), trivial,
        fun ⟨_, _, hbox⟩ ↦ hbox () trivial⟩⟩

/-- The signature of a row's root, the least of the class the book assigns it. -/
def kinds? (d : Datum) : Option Root.Kinds :=
  d.parse? "root class" [("property concept", propertyConcept), ("result", pureResult)] <|>
    d.parse? "verb class" [("manner of killing", fullSpec)]

/-- The diagnostic a row tests. -/
def diagnostic? (d : Datum) : Option Diagnostic :=
  d.parse? "diagnostic" [("change denial", .changeDenial), ("restitutive again", .restitutive),
    ("action denial", .actionDenial)]

/-- A lexicon, an assignment of a signature to the root of each row, fits the judgments when each
row that tests a diagnostic is acceptable exactly when its root passes it. -/
def Fits (σ : Datum → Root.Kinds) : Prop :=
  ∀ d ∈ Examples.all, ∀ g ∈ diagnostic? d, (d.judgment = .acceptable ↔ Passes (σ d) g)

/-- The book's root classes fit the judgments of (46)–(48) and (32). -/
theorem rows : Fits fun d ↦ (kinds? d).getD ∅ := by
  simp only [Fits, passes_iff]
  decide

/-- No lexicon whose roots carry only states and manners fits the judgments: the Bifurcation
Thesis lets every root pass restitutive *again*, and the result root of *return* in (47a) does
not. -/
theorem bifurcation_thesis_false :
    ¬ ∃ σ : Datum → Root.Kinds, (∀ d, close (σ d) ≤ ontological) ∧ Fits σ := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root.Kinds, close s ≤ ontological →
      ¬ Diagnostic.restitutive.detects ⊆ close s := by
    decide
  exact absurd ((h Examples.bkg2020_ch2_47a (by simp [Examples.all]) .restitutive (by decide)).2
    ((passes_iff _).2 (key _ (hσ Examples.bkg2020_ch2_47a)))) (by decide)

/-- No lexicon in which no root entails both a manner and a result fits the judgments: the denial
of action fails in (32b) only for a root whose manner is that of its cause, and a cause entails a
result. -/
theorem manner_result_complementarity_false :
    ¬ ∃ σ : Datum → Root.Kinds,
      (∀ d, ¬ ({.manner, .result} : Root.Kinds) ≤ close (σ d)) ∧ Fits σ := by
  rintro ⟨σ, hσ, h⟩
  have key : ∀ s : Root.Kinds, Diagnostic.actionDenial.detects ⊆ close s →
      ({.manner, .result} : Root.Kinds) ≤ close s := by
    decide
  refine hσ Examples.bkg2020_ch4_32b (key _ ?_)
  by_contra hn
  exact absurd ((h Examples.bkg2020_ch4_32b (by simp [Examples.all]) .actionDenial (by decide)).2
    ((passes_iff _).2 hn)) (by decide)

private theorem not_subset_erase_result (s : Root.Kinds) :
    ¬ ({.manner, .result} : Root.Kinds) ⊆ if .manner ∈ s then s.erase .result else s := by
  intro h
  have hm := h (Finset.mem_insert_self _ _)
  have hr := h (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  split_ifs at hm hr with hk
  · exact (Finset.mem_erase.1 hr).1 rfl
  · exact hk hm

-- Read on the signatures as given rather than on their closures, Manner/Result Complementarity
-- fits the judgments: dropping the result from each root with a manner keeps its closure.
theorem exists_fits_not_mannerResult :
    ∃ σ : Datum → Root.Kinds, (∀ d, ¬ ({.manner, .result} : Root.Kinds) ≤ σ d) ∧ Fits σ := by
  refine ⟨fun d ↦ if .manner ∈ (kinds? d).getD ∅ then ((kinds? d).getD ∅).erase .result
    else (kinds? d).getD ∅, fun d ↦ not_subset_erase_result _, ?_⟩
  simp only [Fits, passes_iff]
  decide

/-! ### The attachment of *again* -/

/-- The site at which a row attaches *again*. -/
def site? (d : Datum) : Option Site :=
  d.parse? "attachment" [("root", .root), ("v_become", .vBecome), ("v_cause", .vCause)]

-- (25), (27): each reading of *Mary flattened the rug again* is available, *again* attaching
-- at a subterm of the causative template (see `exists_denote_of_againAt_ne_zero`)
theorem attachment_rows : ∀ d ∈ Examples.all, ∀ s ∈ site? d,
    d.judgment = .acceptable ∧ s.template.2.IsSubterm causative := by
  have h : ∀ d ∈ Examples.all, ∀ s ∈ site? d, d.judgment = .acceptable := by decide
  exact fun d hd s hs ↦ ⟨h d hd s hs, s.isSubterm⟩

/-! ### The root hypothesis against Levin's class profiles -/

/-- The root signature a class realizes, where one has been established: manner roots for the
activity classes, causative-result roots for the externally caused changes of state, pure
result roots for the internally caused ones, property concepts for the statives, the empty
signature for roots with no structural entailment. -/
def rootEntailments : LevinClass → Option Root.Kinds
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

theorem rootEntailments_wellFormed (c : LevinClass) (s : Root.Kinds)
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
