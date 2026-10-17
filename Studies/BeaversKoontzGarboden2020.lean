module

public import Linglib.Semantics.Root.Defs
public import Linglib.Syntax.Category.Verb.Basic
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

The modifier *again* attaches to the root, to `vbecome` or to `vcause`, the three subterms of
the causative template, and the entailments among its three readings follow from the subterm
order (`Template.exists_denote_of_isSubterm`). The book's hypothesis about which roots alternate
between a causative and an inchoative is compared with the class pages of Levin's *English Verb
Classes and Alternations* (`rootHypothesis_matches_profile`).

## Implementation notes

* The state entailments of the result roots are derived by the collocational closure of the
  kind signature (`Root.closedKinds`).
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

namespace Semantics.Root.Kinds

/-! ### The two theses, at signature level -/

/-- The ontological kinds are all that the Bifurcation Thesis allows a root to carry. -/
def ontological : Root.Kinds := {.state, .manner}

/-- A signature violates the Bifurcation Thesis when it carries templatic, eventive content,
that is, when it is not bounded by `ontological`. -/
def ViolatesBifurcation (s : Root.Kinds) : Prop := ¬ s ≤ ontological

instance (s : Root.Kinds) : Decidable s.ViolatesBifurcation :=
  inferInstanceAs (Decidable (¬ _ ≤ _))

/-- Violation is carrying a `result` or `cause` kind. -/
theorem violatesBifurcation_iff :
    ∀ s : Root.Kinds,
      s.ViolatesBifurcation ↔ .result ∈ s ∨ .cause ∈ s := by decide

/-- Bifurcation violation is monotone, so adding entailments cannot repair a violation. -/
theorem violatesBifurcation_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.ViolatesBifurcation → t.ViolatesBifurcation := by decide

/-- A signature has both manner and result, the configuration that Manner/Result
Complementarity claims no root realizes. -/
def HasMannerAndResult (s : Root.Kinds) : Prop :=
  {Root.Kind.manner, Root.Kind.result} ≤ s

instance (s : Root.Kinds) : Decidable s.HasMannerAndResult :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- MRC violation is monotone in the signature order. -/
theorem hasMannerAndResult_mono :
    ∀ {s t : Root.Kinds}, s ≤ t →
      s.HasMannerAndResult → t.HasMannerAndResult := by decide

/-- Bifurcation is invariant under collocational closure, since `close` only adds the `state`
and `result` kinds forced by `cause`, never `manner`. -/
theorem violatesBifurcation_close_iff :
    ∀ s : Root.Kinds,
      (close s).ViolatesBifurcation ↔ s.ViolatesBifurcation := by decide

theorem hasMannerAndResult_close_iff :
    ∀ s : Root.Kinds,
      (close s).HasMannerAndResult ↔
        s.HasMannerAndResult ∨ (.manner ∈ s ∧ .cause ∈ s) := by decide

/-! ### The typology -/

/-- The seven rows of the typology (12). -/
def typology : Finset Root.Kinds :=
  {propertyConcept, pureResult, causativeResult, pureManner, {.state, .manner},
   {.state, .manner, .result}, fullSpec}

/-- The typology (12) is exhaustive, since the signatures respecting the collocational
    restrictions are its seven rows and `∅`. -/
theorem wellFormed_iff_mem_typology :
    ∀ s : Root.Kinds, s.WellFormed ↔ s = ∅ ∨ s ∈ typology := by decide

/-- The filled cells of (12), pairs of a closed signature and a position. -/
def attestedCells : Finset (Root.Kinds × Root.Position) :=
  {(propertyConcept, .complement), (pureResult, .complement), (causativeResult, .complement),
   (pureManner, .adjoined), (fullSpec, .adjoined), (fullSpec, .complement)}

end Semantics.Root.Kinds

namespace Semantics.Root

/-! ### The two theses, at root level -/

/-- A root violates Bifurcation when it itself carries templatic, eventive meaning, a change of
state or a cause. -/
def ViolatesBifurcation (r : Root) : Prop :=
  r.kinds.ViolatesBifurcation

instance (r : Root) : Decidable r.ViolatesBifurcation :=
  inferInstanceAs (Decidable (Root.Kinds.ViolatesBifurcation _))

/-- A root respects Bifurcation when it carries only the ontological entailments, state and
manner. -/
def RespectsBifurcation (r : Root) : Prop :=
  ¬ r.ViolatesBifurcation

instance (r : Root) : Decidable r.RespectsBifurcation :=
  inferInstanceAs (Decidable (¬ _))

/-- A root respects Bifurcation iff its signature is bounded by the ontological kinds. -/
theorem respectsBifurcation_iff_le {r : Root} :
    r.RespectsBifurcation ↔
      r.kinds ≤ Root.Kinds.ontological :=
  not_not

/-- A root has both manner and result entailments, which Manner/Result Complementarity claims
no root does. -/
def HasMannerAndResult (r : Root) : Prop :=
  r.kinds.HasMannerAndResult

instance (r : Root) : Decidable r.HasMannerAndResult :=
  inferInstanceAs (Decidable (Root.Kinds.HasMannerAndResult _))

/-- Negation of `HasMannerAndResult`. -/
def RespectsMannerResultComplementarity (r : Root) : Prop :=
  ¬ r.HasMannerAndResult

instance (r : Root) : Decidable r.RespectsMannerResultComplementarity :=
  inferInstanceAs (Decidable (¬ _))

end Semantics.Root

namespace BeaversKoontzGarboden2020

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

end BeaversKoontzGarboden2020


namespace BeaversKoontzGarboden2020

open Verb
open Semantics

/-! ### The six representative roots -/

/-- √flat is a pure state root. -/
def flat : Root := { name := "flat", entailments := {.state "flat"}, position := some .complement }

/-- √jog is a pure manner-of-motion root. -/
def jog : Root :=
  { name := "jog", entailments := {.manner "jogging-gait"}, position := some .adjoined }

/-- √blossom is a result root with no specified manner or cause, an internally caused change
of state. -/
def blossom : Root :=
  { name := "blossom", entailments := {.result "flowering"}, position := some .complement }

/-- √crack is a caused-result root without a specified manner. -/
def crack : Root :=
  { name := "crack", entailments := {.result "fissured", .cause}, position := some .complement }

/-- √hand carries manner, cause and result in the adjoined position. The possession result is
not cancelable (*Mary handed John the book, #but it never came to be on his person*), so it is
entailed by the root rather than implicated. -/
def hand : Root :=
  { name := "hand",
    entailments := {.manner "by-hand-transfer", .result "in-recipient-possession", .cause},
    position := some .adjoined }

/-- √drown is a manner-of-killing root, carrying manner, cause and result in the complement
position. -/
def drown : Root :=
  { name := "drown",
    entailments := {.manner "submersion-in-liquid", .result "dead", .cause},
    position := some .complement }

/-! ### Kind signatures

Base signatures record the atom kinds; closed signatures are their
collocational closures, and coincide with the canonical rows of the
book's typology. -/

theorem flat_kinds : flat.kinds = {.state} := by
  decide

theorem jog_kinds : jog.kinds = {.manner} := by
  decide

theorem blossom_kinds :
    blossom.kinds = {.result} := by decide

theorem crack_kinds :
    crack.kinds = {.result, .cause} := by decide

theorem hand_kinds :
    hand.kinds = {.manner, .result, .cause} := by decide

theorem drown_kinds :
    drown.kinds = {.manner, .result, .cause} := by decide

theorem flat_closedKinds :
    flat.closedKinds = Root.Kinds.propertyConcept := by
  decide

theorem jog_closedKinds :
    jog.closedKinds = Root.Kinds.pureManner := by decide

theorem blossom_closedKinds :
    blossom.closedKinds = Root.Kinds.pureResult := by
  decide

theorem crack_closedKinds :
    crack.closedKinds = Root.Kinds.causativeResult := by
  decide

theorem hand_closedKinds :
    hand.closedKinds = Root.Kinds.fullSpec := by decide

theorem drown_closedKinds :
    drown.closedKinds = Root.Kinds.fullSpec := by decide

/-- Each of the six roots fills a cell of (12). -/
theorem cells_attested :
    ∀ r ∈ [flat, jog, blossom, crack, hand, drown],
      ∃ p, r.position = some p ∧ (r.closedKinds, p) ∈ Root.Kinds.attestedCells := by decide

/-- √hand and √drown share a signature and differ only in position. -/
theorem hand_drown_differ_in_position :
    hand.closedKinds = drown.closedKinds ∧ hand.position ≠ drown.position := by decide

/-! ### Falsifying the Bifurcation Thesis -/

/-- √blossom entails a change of state, the templatic content of `v_become`, in the root, and so
falsifies Bifurcation without any manner or cause entailment. -/
theorem blossom_violatesBifurcation : blossom.ViolatesBifurcation := by
  decide

theorem crack_violatesBifurcation : crack.ViolatesBifurcation := by
  decide

theorem hand_violatesBifurcation : hand.ViolatesBifurcation := by decide

theorem drown_violatesBifurcation : drown.ViolatesBifurcation := by
  decide

/-- Some root carries templatic content. -/
theorem exists_violatesBifurcation : ∃ r : Root, r.ViolatesBifurcation :=
  ⟨blossom, blossom_violatesBifurcation⟩

/-- The universal closure of the Bifurcation Thesis is false. -/
theorem bifurcation_thesis_false :
    ¬ ∀ r : Root, r.RespectsBifurcation := fun h =>
  h blossom blossom_violatesBifurcation

/-! ### Falsifying Manner/Result Complementarity -/

/-- √hand entails both a manner (by-hand transfer) and a result
    (recipient possession). -/
theorem hand_hasMannerAndResult : hand.HasMannerAndResult := by decide

/-- √drown entails both a manner (submersion) and a result (death);
    it differs from √hand in root position. -/
theorem drown_hasMannerAndResult : drown.HasMannerAndResult := by decide

/-- Some root entails both a manner and a result. -/
theorem exists_hasMannerAndResult : ∃ r : Root, r.HasMannerAndResult :=
  ⟨hand, hand_hasMannerAndResult⟩

/-- The universal closure of Manner/Result Complementarity is false. -/
theorem manner_result_complementarity_false :
    ¬ ∀ r : Root, r.RespectsMannerResultComplementarity := fun h =>
  h hand hand_hasMannerAndResult

/-! ### Roots respecting each constraint -/

/-- √flat, a pure state root, respects Bifurcation, its signature being bounded by the
ontological kinds. -/
theorem flat_respectsBifurcation : flat.RespectsBifurcation := by decide

/-- √jog (pure manner) respects Bifurcation. -/
theorem jog_respectsBifurcation : jog.RespectsBifurcation := by decide

/-- √crack (cause + result, no manner) respects Manner/Result
    Complementarity. -/
theorem crack_respectsMannerResultComplementarity :
    crack.RespectsMannerResultComplementarity := by decide

/-! ### The entailments of the roots in a model

The kinds of a root are meaning postulates on its state predicate
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
  h .cause (by decide) x s hs

/-- In a model that respects the signature of √drown, a drowned state arises from a change
whose every cause is an event of the root's manner. -/
theorem drown_entails_manner (h : M.Respects P Q drown.kinds) (hs : P x s) :
    ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v :=
  h .manner (by decide) x s hs

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
  ⟨fun k hk ↦ by
      obtain rfl : k = .state := by revert k; decide
      trivial,
    fun h ↦ let ⟨_, he⟩ := h () () trivial; he⟩

/-- The signature of √crack is respected for a state predicate that holds, in the model where
every state arises from a caused change, and is not respected in the model without changes. -/
theorem crack_respects :
    changing.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds ∧
      ¬ unchanging.Respects (fun _ _ ↦ True) (fun _ ↦ True) crack.kinds :=
  ⟨fun k hk ↦ by
      have : k = .result ∨ k = .cause := by revert k; decide
      rcases this with rfl | rfl
      · exact fun _ _ _ ↦ ⟨(), trivial⟩
      · exact fun _ _ _ ↦ ⟨(), (), trivial, trivial⟩,
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
