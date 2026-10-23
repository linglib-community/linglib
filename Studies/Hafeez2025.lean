module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.List.MinMax
public import Linglib.Data.Experiments.Hafeez2025
public import Linglib.Semantics.Causation.Morphological

/-!
# Hafeez (2025): Agentivity and causation in Urdu

[hafeez-2025] asks which Urdu causal constructions speakers accept for which causal scenes. The
scenes are the 43 video clips of the Causality Across Languages project, and they vary along three
variables: the causer is an intentional human (IHCr), an accidental human (AHCr) or a natural
force (NFCr); the second participant of the chain is a controlling human causee (ContrHCEAF), a
physically or a psychologically impacted human (PhysImpHCEAF, PsychImpHCEAF) or an inanimate
affectee (InanCEAF); and a third participant does or does not mediate the chain (Mediation).

The acceptability study (chapter 5) had twelve raters judge a description of every clip in each of
seven response types, and fits one conditional inference tree per response type. Each leaf of a
tree is a conjunction of signed predictors such as [+IHCr, -Mediation, +InanCEAF], and the leaf
with the highest share of ceiling ratings is the response type's hypothesized semantic prototype
when that share exceeds 50% (Table 18). The response types are the lexical ergative LEX-ERG
(ergative causer, transitive verb), the lexical instrumental LEX-INST (instrumental causer,
intransitive verb), the lexical dative LEX-DAT (dative causee or affectee, infinitive and light
verb), the morphological causative verb MCV (the indirect causative *-va*; verbs with the direct
causative *-aa* count as lexical), the adverbial ADV (two clauses joined by *keyoonkeh*
'because'), the non-sentential cause adjunct NCA (a cause NP with *=par*, *wajhan=se* or *=se*)
and the non-sentential causer adjunct NCrA (a causer NP with *wajhan=se*). The printed tables are
`Data/Experiments/Hafeez2025`.

* **The coding.** A clip's scene is read off its name by the code of Appendix L
  (`Clip.scene`), and every clip is a scene the design can stage (`clips_stageable`). The
  predictor table as printed (Table 4) codes five clips otherwise (`table4_disagreements`), and
  it cannot be the coding the trees were fit on: three leaves hold more responses than twelve
  raters give their clips under it (`table4_exceeded`), while under the clip names no leaf does
  (`responses_le`) and all but three hold exactly that many (`responses_shortfall`).
* **The trees.** The trees reproduce Table 18's leaves with their node numbers (`tree_leaves`)
  and partition the scenes (`leaves_partition`, from `Tree.countP_leaves`). Table 18 prints the
  InanCEAF split of the ADV tree with reversed signs: section 5.3.5 puts the 90.8% peak on
  [-InanCEAF], and with the printed signs no ADV leaf holds its clips' responses
  (`adv_printed_misfit`). Every printed percentage is a count out of its responses except the
  0.08 of the LEX-INST tree (`attainablePercent_iff`).
* **The prototypes** are derived as the highest leaf above 50% (`prototype`); LEX-DAT has none
  (`prototype_eq_none_iff`). Table 19 prints the peaks of NCA and NCrA swapped
  (`summary_percent_swapped`). The printed prototypes of Tables 19 and 25 denote the derived
  ones (`summary_iff_prototype`), LEX-ERG's only on stageable scenes, since it drops the leaf's
  [-Mediation] (`lexErg_summary_not_prototype`), and ADV's is the complement of the derived one
  (`adv_summary_iff_not_prototype`).
* **Agentivity.** The agentivity reading of the prototypes in the chapter's conclusion
  (`lexErg_full`, `ncrA_nonagentive`, …) follows from the prototypes and the agentivity degrees of
  the participants.
* **Production.** The production study's preferences (chapter 6, Table 25) refine the
  prototypes, the dovetailing the abstract reports (`individual_le_prototype`). The combined
  model's NCA preference reaches the clip of a woman startled by thunder, outside the NCA
  prototype (`nca_combined_not_le_prototype`).
* **Comrie.** The LEX-ERG prototype is unmediated and the MCV prototype mediated
  (`lexErg_mcv_mediation`), the order [comrie-1989]'s compactness generalization demands of a
  lexical and a morphological causative (`lexErg_mcv_comrieMonotone`).

## Implementation notes

The second participant is one variable with four values, so a scene type such as
[-ContrHCEAF, +InanCEAF] and its shorter form [+InanCEAF] are equivalent, which is how Table 18's
LEX-INST leaf and the LEX-INST prototype of Tables 19 and 25 agree. The scene's mediation is the
substrate's `Causation.Morphological.Mediation`: [+Mediation] is a third participant between
causer and result, the narrow sense of directness the dissertation distinguishes from the broad
one.

## References

* [hafeez-2025]
* [bohnemeyer-2004]
* [comrie-1989]
-/

@[expose] public section

namespace Hafeez2025

open Causation.Morphological Data.Experiments

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
causee. The code's one exception is clip 22, whose M marks an umbrella. -/
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

/-- The predictor table as printed (Table 4) disagrees with the clip names on five clips: it
codes clips 11 and 21, where a pushed or bumped man knocks down a cup tower, with an inanimate
second participant, the umbrella of clip 22 without one, and adds a human impact to the paper
of clips 1 and 23. -/
theorem table4_disagreements :
    (clips.filter fun c ↦ ¬∀ p, p ∈ c.present ↔ c.scene.Is p).map (·.number) =
      [1, 11, 21, 22, 23] := by
  decide

/-! ### Conditional inference trees -/

/-- A binary conditional inference tree: an inner node tests a signed predictor, sending the
scenes that pass it left. -/
inductive Tree where
  | leaf
  | node (test : Predictor × Sign) (pass fail : Tree)

/-- The number of nodes. -/
def Tree.size : Tree → ℕ
  | .leaf => 1
  | .node _ p f => p.size + f.size + 1

/-- The leaves of a tree whose root is node `n`, numbered in preorder as the dissertation's tree
plots number them, each with the scene type of its path. -/
def Tree.leaves : Tree → ℕ → List (ℕ × List (Predictor × Sign))
  | .leaf, n => [(n, [])]
  | .node l p f, n =>
      (p.leaves (n + 1)).map (Prod.map id (l :: ·)) ++
        (f.leaves (n + 1 + p.size)).map (Prod.map id (negate l :: ·))

theorem Tree.countP_leaves (t : Tree) (n : ℕ) (s : Scene) :
    (t.leaves n).countP (fun p ↦ s.Fits p.2) = 1 := by
  induction t generalizing n with
  | leaf => simp [leaves]
  | node l p f ihp ihf =>
    by_cases h : s.Has l <;>
      simp [leaves, List.countP_append, List.countP_map, Function.comp_def, h, ihp, ihf]

/-- The scene type of a leaf of Table 18, with the InanCEAF signs of the ADV tree as section
5.3.5 states them. -/
def leafPath (l : Leaf) : List (Predictor × Sign) :=
  if l.responseType = .adv then
    l.path.map fun q ↦ if q.1 = .inanCEAF then negate q else q
  else l.path

/-- The leaves of a response type's tree in Table 18. -/
def leavesOf (r : ResponseType) : List Leaf := leaves.filter (·.responseType = r)

open Tree in
/-- The tree of a response type of the acceptability study. -/
def tree : ResponseType → Option Tree
  | .lexErg => some <|
      node (.ihcr, .minus) leaf (node (.mediation, .plus) leaf (node (.inanCEAF, .plus) leaf leaf))
  | .lexInst => some <|
      node (.ihcr, .plus) (node (.psychImpHCEAF, .plus) leaf leaf)
        (node (.contrHCEAF, .minus) (node (.inanCEAF, .plus) leaf leaf) leaf)
  | .lexDat => some <| node (.contrHCEAF, .plus) leaf (node (.nfcr, .plus) leaf leaf)
  | .mcv => some <|
      node (.mediation, .plus) (node (.ihcr, .minus) leaf (node (.contrHCEAF, .plus) leaf leaf))
        (node (.contrHCEAF, .plus) leaf leaf)
  | .adv => some <| node (.inanCEAF, .plus) (node (.ihcr, .plus) leaf leaf) leaf
  | .nca => some <| node (.inanCEAF, .minus) (node (.nfcr, .minus) leaf leaf) leaf
  | .ncrA => some <|
      node (.inanCEAF, .plus) (node (.ihcr, .minus) leaf leaf) (node (.nfcr, .plus) leaf leaf)
  | _ => none

/-- The trees reproduce Table 18: their leaves, numbered in preorder, are the printed leaves. -/
theorem tree_leaves (r : ResponseType) (t : Tree) (h : tree r = some t) :
    t.leaves 1 = (leavesOf r).map fun l ↦ (l.node, leafPath l) := by
  cases r <;> cases h <;> decide

/-- Each tree's leaves in Table 18 partition the scenes. -/
theorem leaves_partition (r : ResponseType) (t : Tree) (h : tree r = some t) (s : Scene) :
    (leavesOf r).countP (fun l ↦ s.Fits (leafPath l)) = 1 := by
  simpa [tree_leaves r t h, List.countP_map, Function.comp_def] using t.countP_leaves 1 s

/-! ### Response counts -/

/-- The number of clips whose scene falls under a scene type. -/
def clipCount (t : List (Predictor × Sign)) : ℕ := clips.countP fun c ↦ c.scene.Fits t

theorem responses_le : ∀ l ∈ leaves, l.responses ≤ raters * clipCount (leafPath l) := by
  decide

theorem responses_shortfall :
    ((leaves.filter fun l ↦ l.responses ≠ raters * clipCount (leafPath l)).map
      fun l ↦ (l.responseType, l.node)) = [(.lexInst, 8), (.lexDat, 5), (.ncrA, 7)] := by
  decide

/-- With the InanCEAF signs Table 18 prints, no ADV leaf holds the responses of its clips. -/
theorem adv_printed_misfit :
    ∀ l ∈ leavesOf .adv, l.responses ≠ raters * clipCount l.path := by
  decide

/-- Whether Table 4 marks a clip with a signed predictor. -/
def table4Has (c : Clip) : Predictor × Sign → Prop
  | (p, .plus) => p ∈ c.present
  | (p, .minus) => p ∉ c.present

instance (c : Clip) : DecidablePred (table4Has c) := fun
  | (_, .plus) => inferInstanceAs (Decidable (_ ∈ _))
  | (_, .minus) => inferInstanceAs (Decidable ¬_)

/-- Under the coding of Table 4 as printed, three leaves hold more responses than the twelve
raters could give their clips, so Table 4 is not the coding the trees were fit on. -/
theorem table4_exceeded :
    ((leaves.filter fun l ↦
        raters * (clips.countP fun c ↦ ∀ q ∈ leafPath l, table4Has c q) < l.responses).map
      fun l ↦ (l.responseType, l.node)) = [(.lexInst, 4), (.adv, 5), (.nca, 3)] := by
  decide

theorem attainablePercent_iff :
    ∀ l ∈ leaves, l.ceilingPercent.AttainablePercent l.responses ↔
      ¬(l.responseType = .lexInst ∧ l.node = 4) := by
  decide +kernel

/-! ### Prototypes -/

/-- The leaf with the peak share of ceiling ratings. -/
def peakLeaf (r : ResponseType) : Option Leaf := (leavesOf r).argmax (·.ceilingPercent.toRat)

/-- The hypothesized semantic prototype: the scene type of the peak leaf, when its share of
ceiling ratings exceeds 50%. -/
def prototype (r : ResponseType) : Option (List (Predictor × Sign)) :=
  ((peakLeaf r).filter fun l ↦ 50 < l.ceilingPercent.toRat).map leafPath

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

/-- Table 19 prints each response type's peak, except that it swaps those of NCA and NCrA. -/
theorem summary_percent :
    ∀ row ∈ summary, row.responseType ≠ .nca → row.responseType ≠ .ncrA →
      some row.percent = (peakLeaf row.responseType).map (·.ceilingPercent) := by
  decide +kernel

theorem summary_percent_swapped :
    ∀ row ∈ summary,
      (row.responseType = .nca → some row.percent = (peakLeaf .ncrA).map (·.ceilingPercent)) ∧
      (row.responseType = .ncrA → some row.percent = (peakLeaf .nca).map (·.ceilingPercent)) := by
  decide +kernel

/-- Tables 19 and 25 print the same prototypes. -/
theorem summary_prototype_eq : ∀ row ∈ summary,
    ∃ c ∈ comparison, c.responseType = row.responseType ∧ c.prototype = row.prototype := by
  decide +kernel

theorem summary_iff_prototype :
    ∀ row ∈ comparison, row.responseType ≠ .adv → ∀ s : Scene, s.Stageable →
      ((∃ t ∈ row.prototype, s.Fits t) ↔ Prototypical row.responseType s) := by
  decide +kernel

theorem summary_iff_prototype_of_ne :
    ∀ row ∈ comparison, row.responseType ≠ .adv → row.responseType ≠ .lexErg → ∀ s : Scene,
      ((∃ t ∈ row.prototype, s.Fits t) ↔ Prototypical row.responseType s) := by
  decide +kernel

theorem lexErg_summary_not_prototype :
    ∃ s : Scene, ¬s.Stageable ∧ s.Fits [(.ihcr, .plus), (.inanCEAF, .plus)] ∧
      ¬Prototypical .lexErg s :=
  ⟨⟨.intentionalHuman, .inanimate, .indirect⟩, by decide +kernel⟩

theorem adv_summary_iff_not_prototype :
    ∀ row ∈ comparison, row.responseType = .adv → ∀ s : Scene,
      ((∃ t ∈ row.prototype, s.Fits t) ↔ ¬Prototypical .adv s) := by
  decide +kernel

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

/-- The model of all response types prefers NCA for a psychologically impacted second
participant, and the clip of a woman startled by thunder is such a scene outside the NCA
prototype. -/
theorem nca_combined_not_le_prototype :
    ∀ row ∈ comparison, row.responseType = .nca → ∃ t ∈ row.combinedPreference,
      ∃ c ∈ clips, c.scene.Fits t ∧ ¬Prototypical .nca c.scene := by
  decide +kernel

/-! ### Compactness and directness -/

theorem lexErg_mcv_mediation :
    ∀ s₁ s₂, Prototypical .lexErg s₁ → Prototypical .mcv s₂ → s₁.mediation < s₂.mediation := by
  decide +kernel

theorem lexErg_mcv_comrieMonotone (s₁ s₂ : Scene) (h₁ : Prototypical .lexErg s₁)
    (h₂ : Prototypical .mcv s₂) :
    CausativeConstruction.ComrieMonotone ⟨.lexical, s₁.mediation⟩ ⟨.morphological, s₂.mediation⟩ :=
  fun _ ↦ (lexErg_mcv_mediation s₁ s₂ h₁ h₂).le

end Hafeez2025
