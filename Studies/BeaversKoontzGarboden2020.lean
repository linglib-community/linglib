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
both a manner and a result. The root of *blossom* entails a change and so falsifies the first
(`bifurcation_thesis_false`); the roots of *hand* and *drown* entail both a manner and a result
and so falsify the second (`manner_result_complementarity_false`).

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

open Semantics Semantics.Root.Kinds

/-! ### The two theses, at signature level -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root.Kinds := {.state, .manner}

/-- A signature violates the Bifurcation Thesis when it carries templatic, eventive content,
that is, when it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Root.Kinds) : Prop := ¬ s ≤ ontological

instance : DecidablePred ViolatesBifurcation := fun _ ↦ inferInstanceAs (Decidable (¬ _ ≤ _))

/-- Violation is carrying a `result` or `cause` kind. -/
theorem violatesBifurcation_iff :
    ∀ s, ViolatesBifurcation s ↔ .result ∈ s ∨ .cause ∈ s := by decide

/-- Adding entailments cannot repair a violation. -/
theorem violatesBifurcation_monotone : Monotone ViolatesBifurcation :=
  fun _ _ hst hs ht ↦ hs (hst.trans ht)

/-- A signature has both manner and result, the configuration that Manner/Result
Complementarity claims no root realizes. -/
def HasMannerAndResult (s : Root.Kinds) : Prop := ({.manner, .result} : Root.Kinds) ≤ s

instance : DecidablePred HasMannerAndResult := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

theorem hasMannerAndResult_monotone : Monotone HasMannerAndResult :=
  fun _ _ hst h ↦ h.trans hst

/-- Bifurcation is invariant under collocational closure, since `close` only adds the `state`
and `result` kinds forced by `cause`, never `manner`. -/
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

/-- The typology (12) is exhaustive, since the signatures respecting the collocational
restrictions are its seven rows and `∅`, the roots positively specified for no feature that the
book sets aside (p. 227). -/
theorem wellFormed_iff_mem_typology :
    ∀ s : Root.Kinds, s.WellFormed ↔ s = ∅ ∨ s ∈ typology := by decide

/-- The filled cells of (12), pairs of a closed signature and a position. -/
def attestedCells : Finset (Root.Kinds × Root.Position) :=
  {(propertyConcept, .complement), (pureResult, .complement), (causativeResult, .complement),
   (pureManner, .adjoined), (fullSpec, .adjoined), (fullSpec, .complement)}

/-- The book's account of the empty cells of (12) (pp. 229–230): on markedness grounds an
adjoined root describes a manner and a complement root a state, and on naturalness grounds a
root describing a manner and a state also entails the causation that relates them. These
carve out exactly the filled cells. -/
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

/-- *Again* attached at a template presupposes an earlier eventuality of the template, and so the
realization of each of its subterms, with the same undergoer, which is the hierarchy of the
readings. -/
theorem exists_denote_of_againAt_ne_zero {t : Template σ} {u : Template τ} (hu : u.IsSubterm t)
    {R : SetRel (σ.Carrier State Event) (σ.Carrier State Event)} {w : σ.Carrier State Event}
    (h : againAt M t R P y x w ≠ 0) : ∃ w', w ~[R] w' ∧ ∃ y' v, u.denote M P ⊤ y' x v :=
  diamond_mono R (fun _ ↦ exists_denote_of_isSubterm hu) w (again_eq_zero_iff.not_left.1 h)

/-- End to end, the repetitive reading over the causation presupposes an earlier causing
eventuality and a change to the root's state. -/
theorem exists_become_of_againAt_causative_ne_zero {R : SetRel Event Event} {w : Event}
    (h : againAt M causative R P y x w ≠ 0) :
    ∃ w', w ~[R] w' ∧ ∃ e s, M.become s e ∧ P x s :=
  let ⟨w', hw, _, e, s, hb, hs⟩ := exists_denote_of_againAt_ne_zero (.caused (.refl _)) h
  ⟨w', hw, e, s, hb, hs⟩

/-- For a state predicate that entails change, even the restitutive attachment of *again*
presupposes a change, so result roots never admit a truly restitutive reading. -/
theorem exists_become_of_againAt_state_ne_zero {R : SetRel State State} {s : State}
    (hres : M.EntailsChange P) (h : againAt M .state R P y x s ≠ 0) :
    ∃ s', s ~[R] s' ∧ ∃ e, M.become s' e :=
  diamond_mono R (hres x) s (again_eq_zero_iff.not_left.1 h)

end Again

/-! ### The typology and the templates -/

section Templates

open ArgumentStructure EventStructure Template

variable {σ : Eventuality}

/-- The attested rows of (12) are the signatures of the templates of the basic inventory, the
state, the activity, the achievement and the two accomplishments: as (13) and the text after it
show (p. 231), √blossom has the templatic meaning of the inchoative, √crack of the causative and
√drown of the resultative. -/
theorem attestedRows_eq_kinds_templates :
    attestedCells.image Prod.fst =
      {state.kinds, act.kinds, achievement.kinds, causative.kinds, accomplishment.kinds} := by
  decide

/-- A signature with a manner and a state but no cause is the signature of no template. -/
theorem kinds_ne_of_cause_not_mem {t : Template σ} {s : Root.Kinds} (hm : .manner ∈ s)
    (hs : .state ∈ s) (hc : .cause ∉ s) : t.kinds ≠ s := by
  rintro rfl; exact hc (hasCause_of_mem_kinds hm hs)

/-- The two rows of (12) that describe a manner and a state without a cause are the signature
of no template, as the book finds no event template that would relate the two (p. 230). -/
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

/-- The filled cells of (12) are the cells of its six roots. -/
theorem attestedCells_eq_sample :
    attestedCells = (sample.map fun c ↦ (c.1.closedKinds, c.2)).toFinset := by decide

/-- √hand and √drown share a signature and differ in position. -/
theorem hand_drown_differ_in_position :
    hand.closedKinds = drown.closedKinds ∧ (hand, .adjoined) ∈ sample ∧
      (drown, .complement) ∈ sample := by decide

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails a change of state, the templatic content of `v_become`, in the root, and so
falsifies Bifurcation without any manner or cause entailment. -/
theorem blossom_violatesBifurcation : ViolatesBifurcation blossom.kinds := by decide

theorem crack_violatesBifurcation : ViolatesBifurcation crack.kinds := by decide

theorem hand_violatesBifurcation : ViolatesBifurcation hand.kinds := by decide

/-- √flat and √jog respect Bifurcation, their signatures being bounded by the ontological
kinds. -/
theorem flat_jog_le_ontological : flat.kinds ≤ ontological ∧ jog.kinds ≤ ontological := by
  decide

/-- The Bifurcation Thesis, that every root carries only ontological kinds, is false. -/
theorem bifurcation_thesis_false : ¬ ∀ r : Root, r.kinds ≤ ontological :=
  fun h ↦ blossom_violatesBifurcation (h blossom)

/-! ### Falsifying Manner/Result Complementarity -/

/-- √hand entails both a manner (by-hand transfer) and a result (recipient possession). -/
theorem hand_hasMannerAndResult : HasMannerAndResult hand.kinds := by decide

/-- √drown entails both a manner (submersion) and a result (death). -/
theorem drown_hasMannerAndResult : HasMannerAndResult drown.kinds := by decide

/-- √crack, a caused result without a manner, respects Manner/Result Complementarity. -/
theorem crack_not_hasMannerAndResult : ¬ HasMannerAndResult crack.kinds := by decide

/-- Manner/Result Complementarity, that no root entails both a manner and a result, is
false. -/
theorem manner_result_complementarity_false : ¬ ∀ r : Root, ¬ HasMannerAndResult r.kinds :=
  fun h ↦ h hand hand_hasMannerAndResult

/-! ### The entailments of the roots in a model

The kinds of a root are meaning postulates on its state and manner predicates
(`EventStructure.Interpretation.Respects`). In an interpretation that respects the signature of
√crack, a cracked state arises from a caused change whatever template the root occurs in, while
one that respects the signature of √flat may have a flat state that no change gave rise to. -/

section Model

open ArgumentStructure

variable {Entity State Event : Type*} {M : EventStructure.Interpretation Entity State Event}
  {P : Entity → State → Prop} {Q : Event → Prop} {x : Entity} {s : State}

/-- In a model that respects the signature of √crack, a cracked state arises from a change
that some event causes. -/
theorem crack_entails_cause (h : M.Respects P Q crack.kinds) (hs : P x s) :
    ∃ e v, M.become s e ∧ M.cause v e :=
  h.1 .cause (by decide) x s hs

/-- In a model that respects the signature of √drown, a drowned state arises from a change
whose every cause is an event of the root's manner. -/
theorem drown_entails_manner (h : M.Respects P Q drown.kinds) (hs : P x s) :
    ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v :=
  h.2 (by decide) (by decide) x s hs

end Model

/-- A model without changes. -/
def unchanging : ArgumentStructure.EventStructure.Interpretation Unit Unit Unit where
  become _ _ := False
  cause _ _ := False
  effector _ _ := False

/-- A model in which every state arises from a caused change. -/
def changing : ArgumentStructure.EventStructure.Interpretation Unit Unit Unit where
  become _ _ := True
  cause _ _ := True
  effector _ _ := True

/-- The signature of √flat does not entail change, since the model without changes respects it
for a state predicate that holds. -/
theorem flat_not_entailsChange :
    unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) flat.kinds ∧
      ¬ unchanging.EntailsChange (fun _ _ ↦ True) :=
  ⟨⟨fun k hk ↦ by
      obtain rfl : k = .state := by revert k; decide
      trivial, fun hm ↦ absurd hm (by decide)⟩,
    fun h ↦ let ⟨_, he⟩ := h () () trivial; he⟩

/-- The signature of √crack is respected for a state predicate that holds, in the model where
every state arises from a caused change, and is not respected in the model without changes. -/
theorem crack_respects :
    changing.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds ∧
      ¬ unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds :=
  ⟨⟨fun k hk ↦ by
      have : k = .result ∨ k = .cause := by revert k; decide
      rcases this with rfl | rfl
      · exact fun _ _ _ ↦ ⟨(), trivial⟩
      · exact fun _ _ _ ↦ ⟨(), (), trivial, trivial⟩, fun hm ↦ absurd hm (by decide)⟩,
    fun h ↦ let ⟨_, _, he, _⟩ := crack_entails_cause h (x := ()) (s := ()) trivial; he⟩

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
  {LevinClass.build, .create, .engender, .amuse, .split, .knead, .cooking, .grow, .coil, .roll}

/-- Outside the residue, the root hypothesis agrees with every tested class page. -/
theorem rootHypothesis_matches_profile :
    ∀ c : LevinClass, TestedForCausative c → c ∉ rootHypothesisResidue →
      (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

/-- The residue is exactly the tested classes on which they disagree. -/
theorem rootHypothesisResidue_disagrees :
    ∀ c ∈ rootHypothesisResidue, TestedForCausative c ∧
      ¬ (c.RootPredictsCausative ↔ c.Participates .causativeInchoative) := by
  decide +kernel

end BeaversKoontzGarboden2020
