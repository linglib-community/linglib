module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Preorder.Chain
public import Linglib.Core.Data.Tree.Cells
public import Linglib.Data.Statistics.Hafeez2025
public import Linglib.Syntax.Voice.Causativization

/-!
# Hafeez (2025): Agentivity and causation in Urdu

A *scene* is a causal chain classified by three variables: its causer, an intentional human
(IHCr), an accidental human (AHCr) or a natural force (NFCr); its second participant, a
controlling human causee (ContrHCEAF), a physically or a psychologically impacted human
(PhysImpHCEAF, PsychImpHCEAF) or an inanimate affectee (InanCEAF); and whether a third participant
mediates the chain (Mediation). A *scene type* is a conjunction of signed predictors such as
[+IHCr, -Mediation, +InanCEAF], denoting the scenes that have each of them (`denote`). The
scenes the clip design stages are those whose mediated chains pass through a human (`design`).

[hafeez-2025] has twelve raters judge a description of each of the 43 clips of the Causality
Across Languages project in each of seven Urdu response types, and fits one conditional inference
tree per response type: a binary tree whose inner nodes test a signed predictor, so that its
leaves are pairwise disjoint and cover the scenes (`pairwise_disjoint_leaves`,
`foldr_sup_leaves`). The *prototype* of a response type is the set of scenes of the leaf with the
highest share of ceiling ratings, when that share exceeds 50%, and empty otherwise (`prototype`).
The trees of `tree` have the leaves the dissertation tabulates (`cells_tree`), and the prototypes
derived from them are the ones it states (`prototype_inter_design`); the lexical dative has none
(`prototype_eq_empty_iff`).

The response types are the lexical ergative LEX-ERG (ergative causer, transitive verb), the
lexical instrumental LEX-INST (instrumental causer, intransitive verb), the lexical dative
LEX-DAT (dative causee or affectee, infinitive and light verb), the morphological causative verb
MCV (the indirect causative *-va*), the adverbial ADV (two clauses joined by *keyoonkeh*
'because'), the non-sentential cause adjunct NCA (a cause NP with *=par*, *wajhan=se* or *=se*)
and the non-sentential causer adjunct NCrA (a causer NP with *wajhan=se*).

Agentivity has three degrees, from intentionality and control (`Degree.of`): full for an
intentional actor in control, induced for a causee in control of an action it was induced to
perform, and marginal for a human involved without intention or control. The prototypes fix the
degrees of the participants: the LEX-ERG causer is fully agentive (`lexErg_full`), the MCV
prototype pairs a fully agentive causer with an induced causee (`mcv_full_induced`), and the NCrA
causer is not agentive (`ncrA_nonagentive`).

The leaves a majority of whose ratings are at ceiling cover, for the lexical ergative, exactly
the unmediated scenes with an intentional causer, and for the morphological causative exactly the
mediated ones (`mem_majorityCeiling_lexErg_iff`, `mem_majorityCeiling_mcv_iff`).

In the production study a response type's preferred scene types refine its prototype
(`individual_le_prototype`), and the preference of the model of all response types is comparable
with one of the response type's own model (`combined_comparable_individual`). The LEX-ERG
prototype is unmediated and the MCV prototype mediated (`lexErg_mcv_mediation`), the order
[comrie-1989]'s compactness generalization requires of a lexical and a morphological causative
(`lexErg_mcv_isChain`).

## Implementation notes

* The second participant is one variable with four values, so a scene type such as
  [-ContrHCEAF, +InanCEAF] and its shorter form [+InanCEAF] denote the same scenes.
* The scene's mediation is the substrate's `Causativization.Mediation`: [+Mediation] is a
  third participant between causer and result, the narrow sense of directness the dissertation
  distinguishes from the broad one.
* A clip's scene is read from the clip coding of the Causality Across Languages project
  (`Clip.scene`): an intentional human causer is a human who acts intentionally, a physically
  impacted second participant a human without control whom the causer impacts, and so on.
* The InanCEAF literal of an ADV scene type is read with the sign of the prose on the ADV tree,
  whose peak scene type has a human second participant (`sceneType`).
* A printed prototype may be shorter than the scene type of its leaf: LEX-ERG's omits
  [-Mediation]. The two denote the same scenes of the design, and
  `denote_lexErg_not_subset_prototype` is a scene outside the design that separates them.
* The source gives no degree to an intentional actor without control; `Degree.of` counts it as
  marginal, and no participant of the design is one.
* A tree is a mathlib `BinaryTree` of signed predictors, and its leaves are the
  `BinaryTree.cells` of the tree of the sets they denote, the scenes that pass a node's test
  going left.

## References

* [hafeez-2025]
* [bohnemeyer-2004]
* [comrie-1989]
-/

@[expose] public section

namespace Hafeez2025

open Causativization Data.Statistics

/-! ### Scenes -/

/-- The causer of a scene. -/
inductive Causer where
  /-- IHCr: acts intentionally and in control. -/
  | intentionalHuman
  /-- AHCr: acts accidentally, without intention or control. -/
  | accidentalHuman
  /-- NFCr: a natural force. -/
  | naturalForce
  deriving DecidableEq, Repr, Fintype

/-- The second participant of the causal chain: a causee when it is an induced agent, an
affectee when it is a patient. -/
inductive CauseeAffectee where
  /-- ContrHCEAF: a human who controls the induced action. -/
  | controlling
  /-- PhysImpHCEAF: a human impacted physically. -/
  | physicallyImpacted
  /-- PsychImpHCEAF: a human impacted psychologically. -/
  | psychologicallyImpacted
  /-- InanCEAF: an inanimate affectee. -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- A causal scene: its causer, its second participant, and whether a third participant
mediates the chain. -/
structure Scene where
  causer : Causer
  causeeAffectee : CauseeAffectee
  mediation : Mediation
  deriving DecidableEq, Repr, Fintype

/-- The scenes the design can stage: a mediated chain's second participant is a human causee,
never an inanimate affectee. -/
def design : Finset Scene := {s | s.mediation = .indirect → s.causeeAffectee ≠ .inanimate}

/-! ### Scene types -/

/-- The scenes a predictor is true of. -/
def scenes : Predictor → Finset Scene
  | .ihcr => {s | s.causer = .intentionalHuman}
  | .ahcr => {s | s.causer = .accidentalHuman}
  | .nfcr => {s | s.causer = .naturalForce}
  | .contrHCEAF => {s | s.causeeAffectee = .controlling}
  | .physImpHCEAF => {s | s.causeeAffectee = .physicallyImpacted}
  | .psychImpHCEAF => {s | s.causeeAffectee = .psychologicallyImpacted}
  | .inanCEAF => {s | s.causeeAffectee = .inanimate}
  | .mediation => {s | s.mediation = .indirect}

/-- The scenes a signed predictor, [+F] or [-F], is true of. -/
def literal : Predictor × Sign → Finset Scene
  | (p, .plus) => scenes p
  | (p, .minus) => (scenes p)ᶜ

/-- The scenes of a scene type, a conjunction of signed predictors. -/
def denote (t : List (Predictor × Sign)) : Finset Scene := t.foldr (literal · ∩ ·) Finset.univ

@[simp] theorem denote_nil : denote [] = Finset.univ := rfl

@[simp] theorem denote_cons (l : Predictor × Sign) (t : List (Predictor × Sign)) :
    denote (l :: t) = literal l ∩ denote t := rfl

/-! ### The clips -/

/-- A clip's scene, by the definitions of the predictors: a human causer is intentional or
accidental, a human second participant controls its action, is physically impacted by the causer
or is neither, and the chain is mediated when a participant stands between the two ends. -/
def Clip.scene (c : Clip) : Scene where
  causer :=
    if !c.humanCauser then .naturalForce
    else if c.intentionalCauser then .intentionalHuman else .accidentalHuman
  causeeAffectee :=
    if !c.humanSecond then .inanimate
    else if c.controllingSecond then .controlling
    else if c.impactedSecond then .physicallyImpacted else .psychologicallyImpacted
  mediation := if c.intermediate then .indirect else .direct

theorem scene_mem_design : ∀ c ∈ clips, c.scene ∈ design := by decide

/-! ### Conditional inference trees -/

/-- The node numbers of the leaves of a tree whose root is node `n`, numbered in preorder as the
dissertation's tree plots number them. -/
def leafNumbers {α : Type*} : BinaryTree α → ℕ → List ℕ
  | .nil, n => [n]
  | .node _ l r, n => leafNumbers l (n + 1) ++ leafNumbers r (n + 1 + (l.numNodes + l.numLeaves))

/-- The opposite sign. -/
def opposite : Sign → Sign
  | .plus => .minus
  | .minus => .plus

/-- The scene type a printed conjunction of signed predictors denotes for a response type: the
conjunction itself, with the InanCEAF literal of an ADV scene type read with the opposite sign. -/
def sceneType (r : ResponseType) (t : List (Predictor × Sign)) : List (Predictor × Sign) :=
  if r = .adv then t.map fun q ↦ if q.1 = .inanCEAF then (q.1, opposite q.2) else q else t

/-- The scenes of a leaf. -/
def Leaf.scenes (l : Leaf) : Finset Scene := denote (sceneType l.responseType l.path)

/-- The leaves of a response type's tree. -/
def leavesOf (r : ResponseType) : List Leaf := leaves.filter (·.responseType = r)

open BinaryTree in
/-- The tree of a response type of the acceptability study. -/
def tree : ResponseType → Option (BinaryTree (Predictor × Sign))
  | .lexErg => some <|
      node (.ihcr, .minus) nil (node (.mediation, .plus) nil (node (.inanCEAF, .plus) nil nil))
  | .lexInst => some <|
      node (.ihcr, .plus) (node (.psychImpHCEAF, .plus) nil nil)
        (node (.contrHCEAF, .minus) (node (.inanCEAF, .plus) nil nil) nil)
  | .lexDat => some <| node (.contrHCEAF, .plus) nil (node (.nfcr, .plus) nil nil)
  | .mcv => some <|
      node (.mediation, .plus) (node (.ihcr, .minus) nil (node (.contrHCEAF, .plus) nil nil))
        (node (.contrHCEAF, .plus) nil nil)
  | .adv => some <| node (.inanCEAF, .plus) (node (.ihcr, .plus) nil nil) nil
  | .nca => some <| node (.inanCEAF, .minus) (node (.nfcr, .minus) nil nil) nil
  | .ncrA => some <|
      node (.inanCEAF, .plus) (node (.ihcr, .minus) nil nil) (node (.nfcr, .plus) nil nil)
  | _ => none

variable {r : ResponseType} {t : BinaryTree (Predictor × Sign)}

-- Table 18
theorem leafNumbers_tree (h : tree r = some t) :
    leafNumbers t 1 = (leavesOf r).map (·.node) := by
  cases r <;> cases h <;> decide

/-- The leaves the dissertation tabulates for a response type are the cells of its tree. -/
theorem cells_tree (h : tree r = some t) :
    (t.map literal).cells Finset.univ = (leavesOf r).map (·.scenes) := by
  cases r <;> cases h <;> decide +kernel

theorem pairwise_disjoint_leaves (h : tree r = some t) :
    ((leavesOf r).map (·.scenes)).Pairwise Disjoint :=
  cells_tree h ▸ BinaryTree.pairwise_disjoint_cells _ _

theorem foldr_sup_leaves (h : tree r = some t) :
    ((leavesOf r).map (·.scenes)).foldr (· ⊔ ·) ⊥ = Finset.univ :=
  cells_tree h ▸ BinaryTree.foldr_sup_cells _ _

/-! ### Response counts -/

/-- The number of clips whose scene is among the given ones. -/
def clipCount (S : Finset Scene) : ℕ := clips.countP (·.scene ∈ S)

theorem responses_le : ∀ l ∈ leaves, l.responses ≤ raters * clipCount l.scenes := by
  decide +kernel

theorem responses_eq : ∀ l ∈ leaves,
    (l.responseType, l.node) ∉ [(ResponseType.lexInst, 8), (.lexDat, 5), (.ncrA, 7)] →
      l.responses = raters * clipCount l.scenes := by
  decide +kernel

/-! ### Prototypes -/

/-- The leaf with the peak share of ceiling ratings. -/
def peakLeaf (r : ResponseType) : Option Leaf := (leavesOf r).argmax (·.ceilingPercent.toRat)

/-- The prototype of a response type: the scenes of the peak leaf, when its share of ceiling
ratings exceeds 50%, and no scene otherwise. -/
def prototype (r : ResponseType) : Finset Scene :=
  ((peakLeaf r).filter fun l ↦ 50 < l.ceilingPercent.toRat).elim ∅ (·.scenes)

/-- The scenes of a printed prototype of a response type. -/
def printed (r : ResponseType) (o : Option (List (Predictor × Sign))) : Finset Scene :=
  o.elim ∅ fun t ↦ denote (sceneType r t)

-- the lexical dative, whose peak is below 50%, and the three response types that were not rated
theorem prototype_eq_empty_iff (r : ResponseType) :
    prototype r = ∅ ↔ r ∈ [.lexNom, .lexDat, .acc, .impCausRel] := by
  cases r <;> decide +kernel

theorem exists_clip_mem_prototype (r : ResponseType) (hr : prototype r ≠ ∅) :
    ∃ c ∈ clips, c.scene ∈ prototype r := by
  cases r <;> first | decide +kernel | exact absurd (by decide +kernel) hr

/-- The prototypes the dissertation states are the derived prototypes, among the scenes of the
design. -/
theorem prototype_inter_design :
    ∀ row ∈ comparison,
      printed row.responseType row.prototype ∩ design = prototype row.responseType ∩ design := by
  decide +kernel

theorem denote_lexErg_not_subset_prototype :
    ¬denote [(.ihcr, .plus), (.inanCEAF, .plus)] ⊆ prototype .lexErg := by
  decide +kernel

/-! ### Agentivity -/

/-- The degrees of agentivity. -/
inductive Degree where
  /-- An intentional actor in control. -/
  | full
  /-- A causee in control of an action it was induced to perform. -/
  | induced
  /-- A human involved without intention or control. -/
  | marginal
  deriving DecidableEq, Repr

/-- The degree of agentivity of a participant, from whether it is human, acts intentionally and
has control, the ability to initiate or terminate an action in [bohnemeyer-2004]'s sense. Only a
human has a degree. -/
def Degree.of (human intentional control : Prop) [Decidable human] [Decidable intentional]
    [Decidable control] : Option Degree :=
  if ¬human then none
  else if ¬control then some .marginal
  else if intentional then some .full else some .induced

/-- The causer is a human. -/
def Causer.Human (c : Causer) : Prop := c ≠ .naturalForce

/-- The causer acts intentionally, and so in control. -/
def Causer.Intentional (c : Causer) : Prop := c = .intentionalHuman

/-- The second participant is a human. -/
def CauseeAffectee.Human (p : CauseeAffectee) : Prop := p ≠ .inanimate

/-- The second participant controls the caused event. -/
def CauseeAffectee.Control (p : CauseeAffectee) : Prop := p = .controlling

instance : DecidablePred Causer.Human := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred Causer.Intentional := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred CauseeAffectee.Human := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred CauseeAffectee.Control := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- A causer's agentivity: an intentional human is in control, an accidental one is not. -/
def Causer.degree (c : Causer) : Option Degree := Degree.of c.Human c.Intentional c.Intentional

/-- A second participant's agentivity: it acts, when it does, because it was induced to. -/
def CauseeAffectee.degree (p : CauseeAffectee) : Option Degree := Degree.of p.Human False p.Control

theorem lexErg_full : ∀ s ∈ prototype .lexErg, s.causer.degree = some .full := by
  decide +kernel

theorem lexInst_marginal : ∀ s ∈ prototype .lexInst,
    s.causer.degree ≠ some .full ∧ s.causeeAffectee.degree = none := by
  decide +kernel

/-- The prototype of the morphological causative pairs a fully agentive causer with a causee of
induced agentivity. -/
theorem mcv_full_induced : ∀ s ∈ prototype .mcv,
    s.causer.degree = some .full ∧ s.causeeAffectee.degree = some .induced := by
  decide +kernel

theorem adv_agentive : ∀ s ∈ prototype .adv, s.causeeAffectee.degree ≠ none := by
  decide +kernel

theorem nca_agentive : ∀ s ∈ prototype .nca,
    s.causer.degree ≠ none ∧ s.causeeAffectee.degree ≠ none := by
  decide +kernel

theorem ncrA_nonagentive : ∀ s ∈ prototype .ncrA,
    s.causer.degree = none ∧ s.causeeAffectee.degree ≠ none := by
  decide +kernel

/-! ### Majority leaves -/

/-- The scenes of the leaves a majority of whose ratings are at ceiling. -/
def majorityCeiling (r : ResponseType) : Finset Scene :=
  ((leavesOf r).filter fun l ↦ 50 < l.ceilingPercent.toRat).foldr (·.scenes ∪ ·) ∅

private theorem subset_foldr_union {l : Leaf} {ls : List Leaf} (h : l ∈ ls) :
    l.scenes ⊆ ls.foldr (·.scenes ∪ ·) ∅ := by
  induction ls with
  | nil => simp at h
  | cons a ls ih =>
    rcases List.mem_cons.1 h with rfl | h
    exacts [Finset.subset_union_left, (ih h).trans Finset.subset_union_right]

theorem prototype_subset_majorityCeiling (r : ResponseType) :
    prototype r ⊆ majorityCeiling r := by
  unfold prototype majorityCeiling
  cases hp : peakLeaf r with
  | none => simp
  | some l =>
    by_cases hl : 50 < l.ceilingPercent.toRat
    · simpa [Option.filter, hl] using
        subset_foldr_union (List.mem_filter.2 ⟨List.argmax_mem hp, by simpa using hl⟩)
    · simp [Option.filter, hl]

-- Table 18
theorem mem_majorityCeiling_lexErg_iff (s : Scene) :
    s ∈ majorityCeiling .lexErg ↔ s.causer = .intentionalHuman ∧ s.mediation = .direct := by
  revert s; decide +kernel

-- Table 18; the lower of the two leaves holds 58.3% of 48 responses
theorem mem_majorityCeiling_mcv_iff (s : Scene) :
    s ∈ majorityCeiling .mcv ↔ s.causer = .intentionalHuman ∧ s.mediation = .indirect := by
  revert s; decide +kernel

/-! ### Production -/

/-- The production study's preferences refine the acceptability prototypes: the scenes of the
design a rated response type's own model prefers it for are in its prototype. -/
theorem individual_le_prototype :
    ∀ row ∈ comparison, row.rated = .yes → ∀ t ∈ row.individualPreferences,
      denote t ∩ design ⊆ prototype row.responseType := by
  decide +kernel

theorem combinedPreference_isSome_iff :
    ∀ row ∈ comparison, row.combinedPreference.isSome ↔ row.individualPreferences ≠ [] := by
  decide

-- Table 25
theorem combined_comparable_individual :
    ∀ row ∈ comparison, ∀ t ∈ row.combinedPreference, ∃ t' ∈ row.individualPreferences,
      denote t ∩ design ⊆ denote t' ∨ denote t' ∩ design ⊆ denote t := by
  decide +kernel

-- Table 25
theorem nca_combined_not_subset_prototype :
    ∀ row ∈ comparison, row.responseType = .nca → ∃ t ∈ row.combinedPreference,
      ∃ c ∈ clips, c.scene ∈ denote t ∧ c.scene ∉ prototype .nca := by
  decide +kernel

/-! ### Compactness and directness -/

theorem lexErg_mcv_mediation :
    ∀ s₁ ∈ prototype .lexErg, ∀ s₂ ∈ prototype .mcv, s₁.mediation < s₂.mediation := by
  decide +kernel

/-- The prototypes of the lexical ergative and of the morphological causative form a chain of
complexity and mediation, as [comrie-1989]'s generalization requires of a lexical and a
morphological causative: the more compact construction has the more direct prototype. -/
theorem lexErg_mcv_isChain {s₁ s₂ : Scene} (h₁ : s₁ ∈ prototype .lexErg)
    (h₂ : s₂ ∈ prototype .mcv) :
    IsChain (· ≤ ·)
      ({(.lexical, s₁.mediation), (.morphological, s₂.mediation)} :
        Set (CausativeComplexity × Mediation)) :=
  IsChain.pair ⟨(by decide : CausativeComplexity.lexical ≤ .morphological),
    (lexErg_mcv_mediation s₁ h₁ s₂ h₂).le⟩

end Hafeez2025
