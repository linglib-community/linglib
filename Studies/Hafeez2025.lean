module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Tree.Basic
public import Linglib.Data.Statistics.Hafeez2025
public import Linglib.Semantics.Causation.Morphological

/-!
# Hafeez (2025): Agentivity and causation in Urdu

A *scene* is a causal chain classified by three variables: its causer, an intentional human
(IHCr), an accidental human (AHCr) or a natural force (NFCr); its second participant, a
controlling human causee (ContrHCEAF), a physically or a psychologically impacted human
(PhysImpHCEAF, PsychImpHCEAF) or an inanimate affectee (InanCEAF); and whether a third participant
mediates the chain (Mediation). A *scene type* is a conjunction of signed predictors such as
[+IHCr, -Mediation, +InanCEAF], and a scene falls under it when it has each of them
(`Scene.Fits`).

[hafeez-2025] has twelve raters judge a description of each of the 43 clips of the Causality
Across Languages project in each of seven Urdu response types, and fits one conditional inference
tree per response type: a binary tree whose inner nodes test a signed predictor, so that the
scene types of its leaves partition the scenes (`leaves_partition`). The *prototype* of a
response type is the scene type of the leaf with the highest share of ceiling ratings, when that
share exceeds 50% (`prototype`). The trees of `tree` have the leaves the dissertation tabulates
(`tree_leaves`), and the prototypes derived from them are the ones it states
(`prototype_iff_printed`); the lexical dative has none (`prototype_eq_none_iff`).

The response types are the lexical ergative LEX-ERG (ergative causer, transitive verb), the
lexical instrumental LEX-INST (instrumental causer, intransitive verb), the lexical dative
LEX-DAT (dative causee or affectee, infinitive and light verb), the morphological causative verb
MCV (the indirect causative *-va*), the adverbial ADV (two clauses joined by *keyoonkeh*
'because'), the non-sentential cause adjunct NCA (a cause NP with *=par*, *wajhan=se* or *=se*)
and the non-sentential causer adjunct NCrA (a causer NP with *wajhan=se*).

Agentivity has three degrees, from intentionality and control: full for an intentional actor in
control, induced for a causee in control of an action it was induced to perform, and marginal for
a human involved without intention or control. The prototypes fix the degrees of the participants:
the LEX-ERG causer is fully agentive (`lexErg_full`), the MCV prototype pairs a fully agentive
causer with an induced causee (`mcv_full_induced`), and the NCrA causer is not agentive
(`ncrA_nonagentive`).

In the production study a response type's preferred scene types refine its prototype
(`individual_le_prototype`), and the preference of the model of all response types is comparable
with one of the response type's own model (`combined_comparable_individual`). The LEX-ERG
prototype is unmediated and the MCV prototype mediated (`lexErg_mcv_mediation`), the order
[comrie-1989]'s compactness generalization requires of a lexical and a morphological causative
(`lexErg_mcv_comrieMonotone`).

## Implementation notes

* The second participant is one variable with four values, so a scene type such as
  [-ContrHCEAF, +InanCEAF] and its shorter form [+InanCEAF] hold of the same scenes.
* The scene's mediation is the substrate's `Causation.Morphological.Mediation`: [+Mediation] is a
  third participant between causer and result, the narrow sense of directness the dissertation
  distinguishes from the broad one.
* A clip's scene is read from its name (`Clip.scene`), as the clip coding of the Causality Across
  Languages project does.
* The InanCEAF literal of an ADV scene type is read with the sign of the prose on the ADV tree,
  whose peak scene type has a human second participant (`sceneType`).
* A printed prototype may be shorter than the scene type of its leaf: LEX-ERG's omits
  [-Mediation]. The two hold of the same scenes among those the design can stage
  (`Scene.Stageable`), and `not_stageable_fits_not_prototypical` is a scene outside the design
  that separates them.
* A tree is a mathlib `BinaryTree` of signed predictors, the scenes that pass a node's test going
  left.

## References

* [hafeez-2025]
* [bohnemeyer-2004]
* [comrie-1989]
-/

@[expose] public section

namespace Hafeez2025

open Causation.Morphological Data.Statistics

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

/-- A scene the design can stage: a mediated chain's second participant is a human causee, never
an inanimate affectee. -/
def Scene.Stageable (s : Scene) : Prop :=
  s.mediation = .indirect → s.causeeAffectee ≠ .inanimate

instance : DecidablePred Scene.Stageable := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-! ### Predictors and scene types -/

/-- The scenes a predictor is true of. -/
def Scene.Is (s : Scene) : Predictor → Prop
  | .ihcr => s.causer = .intentionalHuman
  | .ahcr => s.causer = .accidentalHuman
  | .nfcr => s.causer = .naturalForce
  | .contrHCEAF => s.causeeAffectee = .controlling
  | .physImpHCEAF => s.causeeAffectee = .physicallyImpacted
  | .psychImpHCEAF => s.causeeAffectee = .psychologicallyImpacted
  | .inanCEAF => s.causeeAffectee = .inanimate
  | .mediation => s.mediation = .indirect

instance (s : Scene) : DecidablePred s.Is := fun p ↦ by
  cases p <;> unfold Scene.Is <;> infer_instance

/-- The scenes a signed predictor, [+F] or [-F], is true of. -/
def Scene.Has (s : Scene) : Predictor × Sign → Prop
  | (p, .plus) => s.Is p
  | (p, .minus) => ¬s.Is p

instance (s : Scene) : DecidablePred s.Has := fun
  | (_, .plus) => inferInstanceAs (Decidable (s.Is _))
  | (_, .minus) => inferInstanceAs (Decidable ¬_)

/-- The signed predictor with the opposite sign. -/
def negate : Predictor × Sign → Predictor × Sign
  | (p, .plus) => (p, .minus)
  | (p, .minus) => (p, .plus)

@[simp] theorem Scene.has_negate (s : Scene) (l : Predictor × Sign) :
    s.Has (negate l) ↔ ¬s.Has l := by
  obtain ⟨p, _ | _⟩ := l <;> simp [negate, Has]

/-- A scene falls under a scene type, a conjunction of signed predictors, when it has each. -/
def Scene.Fits (s : Scene) (t : List (Predictor × Sign)) : Prop := ∀ l ∈ t, s.Has l

instance (s : Scene) : DecidablePred s.Fits := fun _ ↦ List.decidableBAll _ _

@[simp] theorem Scene.fits_nil (s : Scene) : s.Fits [] := by simp [Fits]

@[simp] theorem Scene.fits_cons (s : Scene) (l : Predictor × Sign) (t : List (Predictor × Sign)) :
    s.Fits (l :: t) ↔ s.Has l ∧ s.Fits t := by simp [Fits]

/-! ### The clips -/

/-- A clip's scene, read off its name by the code of Appendix L: the first letter is the causer,
the second the second participant, and a third letter O an inanimate affectee behind a mediating
causee. The M of clip 22 names an umbrella, an inanimate affectee. -/
def Clip.scene (c : Clip) : Scene where
  causer := match c.causer with
    | .h => .intentionalHuman
    | .u => .accidentalHuman
    | .n => .naturalForce
  causeeAffectee := if c.number = 22 then .inanimate else match c.second with
    | .c => .controlling
    | .u => .psychologicallyImpacted
    | .m => .physicallyImpacted
    | .o => .inanimate
  mediation := if c.third.isSome then .indirect else .direct

theorem clips_stageable : ∀ c ∈ clips, c.scene.Stageable := by decide

/-! ### Conditional inference trees -/

/-- The leaves of a tree whose root is node `n`, numbered in preorder as the dissertation's tree
plots number them, each with the scene type of its path. -/
def leafPaths : BinaryTree (Predictor × Sign) → ℕ → List (ℕ × List (Predictor × Sign))
  | .nil, n => [(n, [])]
  | .node l p f, n =>
      (leafPaths p (n + 1)).map (Prod.map id (l :: ·)) ++
        (leafPaths f (n + 1 + (p.numNodes + p.numLeaves))).map (Prod.map id (negate l :: ·))

theorem countP_leafPaths (t : BinaryTree (Predictor × Sign)) (n : ℕ) (s : Scene) :
    (leafPaths t n).countP (fun p ↦ s.Fits p.2) = 1 := by
  induction t generalizing n with
  | nil => simp [leafPaths]
  | node l p f ihp ihf =>
    by_cases h : s.Has l <;>
      simp [leafPaths, List.countP_append, List.countP_map, Function.comp_def, h, ihp, ihf]

/-- The scene type a printed conjunction of signed predictors denotes for a response type: the
conjunction itself, with the InanCEAF literal of an ADV scene type read with the opposite sign. -/
def sceneType (r : ResponseType) (t : List (Predictor × Sign)) : List (Predictor × Sign) :=
  if r = .adv then t.map fun q ↦ if q.1 = .inanCEAF then negate q else q else t

/-- The scene type of a leaf. -/
def Leaf.sceneType (l : Leaf) : List (Predictor × Sign) :=
  Hafeez2025.sceneType l.responseType l.path

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

-- Table 18
theorem tree_leaves (r : ResponseType) (t : BinaryTree (Predictor × Sign)) (h : tree r = some t) :
    leafPaths t 1 = (leavesOf r).map fun l ↦ (l.node, l.sceneType) := by
  cases r <;> cases h <;> decide

/-- The scene types of the leaves of a response type's tree partition the scenes. -/
theorem leaves_partition (r : ResponseType) (t : BinaryTree (Predictor × Sign))
    (h : tree r = some t) (s : Scene) :
    (leavesOf r).countP (fun l ↦ s.Fits l.sceneType) = 1 := by
  simpa [tree_leaves r t h, List.countP_map, Function.comp_def] using countP_leafPaths t 1 s

/-! ### Response counts -/

/-- The number of clips whose scene falls under a scene type. -/
def clipCount (t : List (Predictor × Sign)) : ℕ := clips.countP fun c ↦ c.scene.Fits t

theorem responses_le : ∀ l ∈ leaves, l.responses ≤ raters * clipCount l.sceneType := by
  decide

theorem responses_eq : ∀ l ∈ leaves,
    (l.responseType, l.node) ∉ [(ResponseType.lexInst, 8), (.lexDat, 5), (.ncrA, 7)] →
      l.responses = raters * clipCount l.sceneType := by
  decide

/-! ### Prototypes -/

/-- The leaf with the peak share of ceiling ratings. -/
def peakLeaf (r : ResponseType) : Option Leaf := (leavesOf r).argmax (·.ceilingPercent.toRat)

/-- The prototype of a response type: the scene type of the peak leaf, when its share of ceiling
ratings exceeds 50%. -/
def prototype (r : ResponseType) : Option (List (Predictor × Sign)) :=
  ((peakLeaf r).filter fun l ↦ 50 < l.ceilingPercent.toRat).map (·.sceneType)

/-- The scenes of the response type's prototype. -/
def Prototypical (r : ResponseType) (s : Scene) : Prop := ∃ t ∈ prototype r, s.Fits t

instance (r : ResponseType) : DecidablePred (Prototypical r) := fun s ↦
  decidable_of_iff (∃ t ∈ (prototype r).toList, s.Fits t) (by simp [Prototypical])

theorem prototype_eq_none_iff (r : ResponseType) :
    prototype r = none ↔ r ∈ [.lexNom, .lexDat, .acc, .impCausRel] := by
  cases r <;> decide +kernel

theorem exists_clip_prototypical (r : ResponseType) (hr : prototype r ≠ none) :
    ∃ c ∈ clips, Prototypical r c.scene := by
  cases r <;> first | decide +kernel | exact absurd (by decide +kernel) hr

/-- The prototypes the dissertation states hold of the scenes of the derived prototypes, among
the scenes the design can stage. -/
theorem prototype_iff_printed :
    ∀ row ∈ comparison, ∀ s : Scene, s.Stageable →
      ((∃ t ∈ row.prototype, s.Fits (sceneType row.responseType t)) ↔
        Prototypical row.responseType s) := by
  decide +kernel

theorem not_stageable_fits_not_prototypical :
    ∃ s : Scene, ¬s.Stageable ∧ s.Fits [(.ihcr, .plus), (.inanCEAF, .plus)] ∧
      ¬Prototypical .lexErg s :=
  ⟨⟨.intentionalHuman, .inanimate, .indirect⟩, by decide +kernel⟩

/-! ### Agentivity -/

/-- The degrees of agentivity, from intentionality and control, the ability to initiate or
terminate an action in [bohnemeyer-2004]'s sense: full for an intentional actor in control,
marginal for an actor involved accidentally, without intention or control, and induced for a
causee in control of an action it was induced to perform. -/
inductive Degree where
  | full | induced | marginal
  deriving DecidableEq, Repr

/-- A causer's agentivity; a natural force has none. -/
def Causer.degree : Causer → Option Degree
  | .intentionalHuman => some .full
  | .accidentalHuman => some .marginal
  | .naturalForce => none

/-- A second participant's agentivity; an inanimate affectee has none. -/
def CauseeAffectee.degree : CauseeAffectee → Option Degree
  | .controlling => some .induced
  | .physicallyImpacted | .psychologicallyImpacted => some .marginal
  | .inanimate => none

theorem lexErg_full : ∀ s, Prototypical .lexErg s → s.causer.degree = some .full := by
  decide +kernel

theorem lexInst_marginal : ∀ s, Prototypical .lexInst s →
    s.causer.degree ≠ some .full ∧ s.causeeAffectee.degree = none := by
  decide +kernel

/-- The prototype of the morphological causative pairs a fully agentive causer with a causee of
induced agentivity. -/
theorem mcv_full_induced : ∀ s, Prototypical .mcv s →
    s.causer.degree = some .full ∧ s.causeeAffectee.degree = some .induced := by
  decide +kernel

theorem adv_agentive : ∀ s, Prototypical .adv s → s.causeeAffectee.degree ≠ none := by
  decide +kernel

theorem nca_agentive : ∀ s, Prototypical .nca s →
    s.causer.degree ≠ none ∧ s.causeeAffectee.degree ≠ none := by
  decide +kernel

theorem ncrA_nonagentive : ∀ s, Prototypical .ncrA s →
    s.causer.degree = none ∧ s.causeeAffectee.degree ≠ none := by
  decide +kernel

/-! ### Production -/

/-- The production study's preferences refine the acceptability prototypes: every stageable
scene a rated response type's own model prefers it for is prototypical for it. -/
theorem individual_le_prototype :
    ∀ row ∈ comparison, row.rated = .yes → ∀ t ∈ row.individualPreferences, ∀ s : Scene,
      s.Stageable → s.Fits t → Prototypical row.responseType s := by
  decide +kernel

theorem combinedPreference_isSome_iff :
    ∀ row ∈ comparison, row.combinedPreference.isSome ↔ row.individualPreferences ≠ [] := by
  decide

-- Table 25
theorem combined_comparable_individual :
    ∀ row ∈ comparison, ∀ t ∈ row.combinedPreference, ∃ t' ∈ row.individualPreferences,
      (∀ s : Scene, s.Stageable → s.Fits t → s.Fits t') ∨
        (∀ s : Scene, s.Stageable → s.Fits t' → s.Fits t) := by
  decide +kernel

-- Table 25
theorem nca_combined_not_le_prototype :
    ∀ row ∈ comparison, row.responseType = .nca → ∃ t ∈ row.combinedPreference,
      ∃ c ∈ clips, c.scene.Fits t ∧ ¬Prototypical .nca c.scene := by
  decide +kernel

/-! ### Compactness and directness -/

theorem lexErg_mcv_mediation :
    ∀ s₁ s₂, Prototypical .lexErg s₁ → Prototypical .mcv s₂ → s₁.mediation < s₂.mediation := by
  decide +kernel

/-- The prototypes of the lexical ergative and of the morphological causative are ordered as
[comrie-1989] orders a lexical and a morphological causative: the more compact construction has
the more direct prototype. -/
theorem lexErg_mcv_comrieMonotone (s₁ s₂ : Scene) (h₁ : Prototypical .lexErg s₁)
    (h₂ : Prototypical .mcv s₂) :
    CausativeConstruction.ComrieMonotone ⟨.lexical, s₁.mediation⟩ ⟨.morphological, s₂.mediation⟩ :=
  fun _ ↦ (lexErg_mcv_mediation s₁ s₂ h₁ h₂).le

end Hafeez2025
