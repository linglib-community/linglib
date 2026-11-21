module

public import Mathlib.Data.List.Chain
public import Mathlib.Order.Cover
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Reference.Character
public import Linglib.Data.Examples.Traugott2010
public import Studies.Eckardt2006

/-!
# Traugott (2010): (Inter)subjectivity and (Inter)subjectification: A Reassessment

A meaning is *subjective* when it codes the speaker's attitude or viewpoint, and *intersubjective*
when it codes the speaker's attention to the addressee's self-image. The cline of
(inter)subjectivity orders coded meanings as nonsubjective < subjective < intersubjective
(`SubjectivityLevel`). The history of an expression is the list of the levels of the meanings it
came to code, in the order they arose. We say that a history `h` follows the cline,
`FollowsCline h`, when the position at which a level first occurs, `h.idxOf a`, is monotone in the
level `a`. Equivalently, the levels coded by any given time form a lower set of the cline
(`followsCline_iff_forall_prefix`). In such a history a level first arises after every level
below it (`FollowsCline.idxOf_lt_idxOf`), so an intersubjective meaning is preceded by a
subjective one.

The uses of *be going to* are given characters, functions from contexts to interval properties
(`Examples.Use.denote`): motion with intent is the progressive of movement *go* with an infinitive,
and the later uses are the reanalysed entry of Eckardt with the event made imminent by the
subject's intention or by the speaker's assessment. Each use is included in the later ones
(`monotone_denote`), and a use has the nonsubjective level exactly when its character is constant
in the context (`level_eq_nonSubjective_iff`).

The binominals *a piece of*, *a bit of* and *a shred of* pass through the stages Partitive,
Extended Partitive and Quantifier, and *a bit of* goes on to Degree Modifier and Adjunct. The
level coded at a stage, `Examples.Stage.level`, is subjective from the Quantifier on, and the
stages at which the paper attests each item, in their order, follow the cline
(`followsCline_stages`). The Quantifier is also the least stage by which host-class, syntactic and
semantic-pragmatic expansion have all occurred, so the stages that meet these three criteria of
grammaticalization are the subjective ones (`forall_stage_le_iff`).

## Implementation notes

* A history records coded meanings only. *A bit of* is used intersubjectively as a hedge, but
  that use is pragmatic, and no stage has the intersubjective level.
* `FollowsCline` constrains the first occurrence of each level and not every later meaning. A
  history may return to a lower level, as when an emphatic becomes a plain marker of negation; a
  definition asking each new meaning to weakly cover the previous one would exclude this.
* Earlier and later meanings of an item coexist, which is why a history is a list and not a
  single current level.

## References

* [traugott-2010]
* [traugott-dasher-2002]
* [himmelmann-2004]
* [eckardt-2006]
-/

@[expose] public section

namespace Traugott2010

open Examples (Example Item Stage Use Honorific)

/-! ### The cline -/

/-- (2): The levels of the cline of (inter)subjectivity, from least to most subjective. -/
inductive SubjectivityLevel where
  /-- The meaning describes the world or an event. Traugott labels this level as non-subjective
  or less subjective. -/
  | nonSubjective
  /-- The meaning codes the speaker's attitude, belief or evaluation. -/
  | subjective
  /-- The meaning codes the speaker's attention to the addressee's face or self-image. -/
  | intersubjective
  deriving DecidableEq, Fintype, Repr

/-- The levels are ordered as they are listed. -/
instance : LinearOrder SubjectivityLevel := LinearOrder.lift' SubjectivityLevel.ctorIdx (by decide)

variable {h : List SubjectivityLevel} {a b : SubjectivityLevel}

/-- (4): A history follows the cline when its levels first arise in the order of the cline. -/
def FollowsCline (h : List SubjectivityLevel) : Prop := Monotone fun a ↦ h.idxOf a

instance : DecidablePred FollowsCline := fun h ↦
  inferInstanceAs (Decidable (Monotone fun a ↦ h.idxOf a))

theorem FollowsCline.mem_of_le (hc : FollowsCline h) (hab : a ≤ b) (hb : b ∈ h) : a ∈ h :=
  List.idxOf_lt_length_iff.1 ((hc hab).trans_lt (List.idxOf_lt_length_iff.2 hb))

/-- In a history that follows the cline, a level first arises after every level below it. -/
theorem FollowsCline.idxOf_lt_idxOf (hc : FollowsCline h) (hab : a < b) (hb : b ∈ h) :
    h.idxOf a < h.idxOf b :=
  (hc hab.le).lt_of_ne fun he ↦ hab.ne ((List.idxOf_inj (hc.mem_of_le hab.le hb)).1 he)

/-- A history follows the cline exactly when the levels coded by each time form a lower set. -/
theorem followsCline_iff_forall_prefix :
    FollowsCline h ↔ ∀ p, p <+: h → IsLowerSet {a | a ∈ p} := by
  refine ⟨fun hc p hp b a hab hb ↦ ?_, fun H a b hab ↦ ?_⟩
  · exact (hp.mem_iff_idxOf_lt_length a).2
      ((hc hab).trans_lt ((hp.mem_iff_idxOf_lt_length b).1 hb))
  · change h.idxOf a ≤ h.idxOf b
    by_cases hb : b ∈ h
    · have hlt := List.idxOf_lt_length_iff.2 hb
      have hp := List.take_prefix (h.idxOf b + 1) h
      have hlen : (h.take (h.idxOf b + 1)).length = h.idxOf b + 1 := by
        rw [List.length_take]; omega
      have ha := H _ hp hab ((hp.mem_iff_idxOf_lt_length b).2 (by omega))
      have := (hp.mem_iff_idxOf_lt_length a).1 ha
      omega
    · exact List.idxOf_le_length.trans_eq (List.idxOf_eq_length_iff.2 hb).symm

-- A coded intersubjective meaning does not arise from an ideational one (p. 37).
theorem not_followsCline_skip : ¬ FollowsCline [.nonSubjective, .intersubjective] := by decide

-- A subjectified emphatic may be bleached into a plain marker of negation (section 4.4).
theorem followsCline_bleached : FollowsCline [.nonSubjective, .subjective, .nonSubjective] := by
  decide

/-! ### *Be going to* and *saburahu* -/

/-- (5): The coded level of each use of *be going to*. Only the raising use expresses the
speaker's assessment of the future. -/
def Examples.Use.level : Use → SubjectivityLevel
  | .motion | .intention => .nonSubjective
  | .raising => .subjective

/-- (6): The coded level of each honorific value. A referent honorific construes the relation of
the subject referent to the speaker, and an addressee honorific attends to the addressee. -/
def Examples.Honorific.level : Honorific → SubjectivityLevel
  | .nonHonorific => .nonSubjective
  | .referent => .subjective
  | .addressee => .intersubjective

theorem followsCline_use : FollowsCline ((Example.all.filterMap Example.use).map Use.level) := by
  decide

theorem followsCline_honorific :
    FollowsCline (Example.ex_6.honorific.map Honorific.level) ∧
      .intersubjective ∈ Example.ex_6.honorific.map Honorific.level := by
  decide

/-! ### The uses of *be going to* -/

section GoingTo

open Aspect
open Event (τ)
open Eckardt2006 (goTo beGoingTo)

variable {C W X E T : Type*} [LinearOrder T] [TemporalTrace E T]
  (go : X → W → E → Prop) (prepare : E → E → Prop)
  (intends : X → NonemptyInterval T → E → Prop) (assess : C → NonemptyInterval T → E → Prop)
  (P : X → W → E → Prop) (x : X) {w : W} {c c' : C}

/-- The uses are ordered as they arose. -/
instance : LinearOrder Use := LinearOrder.lift' Use.ctorIdx (by decide)

/-- (5): The character of each use of *be going to*. The motion use is the progressive of
movement *go* with an infinitive. The other two are the reanalysed entry of [eckardt-2006], and
differ in what makes the event imminent: the intention of the subject, or the assessment of the
speaker of the context. -/
def Examples.Use.denote : Use → Character C W (Set (NonemptyInterval T))
  | .motion => fun _ ↦ UNBOUNDED (goTo go prepare P x)
  | .intention => fun _ ↦ beGoingTo (intends x) P x
  | .raising => fun c ↦ beGoingTo (assess c) P x

variable {go prepare intends assess P x}

/-- Each use of *be going to* is included in the uses that arose after it, where a going in
progress shows the intention of what it prepares and the speaker takes as imminent what the
subject intends. -/
theorem monotone_denote (hprep : ∀ e e', prepare e e' → Event.Precedes e e')
    (hint : ∀ w t e e', go x w e → prepare e e' → t ≤ τ e → intends x t e')
    (hass : ∀ t e, intends x t e → assess c t e) :
    Monotone fun u ↦ Use.denote go prepare intends assess P x u c w := by
  have h₁ : UNBOUNDED (goTo go prepare P x) w ⊆ beGoingTo (intends x) P x w :=
    Eckardt2006.unbounded_goTo_subset_beGoingTo hprep hint
  have h₂ : beGoingTo (intends x) P x w ⊆ beGoingTo (assess c) P x w :=
    Eckardt2006.beGoingTo_mono hass
  intro u v huv
  cases u <;> cases v <;>
    first | exact le_rfl | exact h₁ | exact h₂ | exact h₁.trans h₂ | exact absurd huv (by decide)

-- The raising use says different things where the speakers assess imminence differently.
theorem denote_raising_ne {t : NonemptyInterval T} {e : E} (ht : t.Precedes (τ e))
    (hP : P x w e) (hc : assess c t e) (hc' : ∀ e', P x w e' → ¬ assess c' t e') :
    Use.denote go prepare intends assess P x .raising c ≠
      Use.denote go prepare intends assess P x .raising c' := fun h ↦
  let ⟨e', _, hi, hP'⟩ := (congrFun h w).subset ⟨e, ht, hc, hP⟩
  hc' e' hP' hi

/-- A use of *be going to* is nonsubjective exactly when it says the same in every context. -/
theorem level_eq_nonSubjective_iff
    (hne : ∃ c c' : C, Use.denote go prepare intends assess P x .raising c ≠
      Use.denote go prepare intends assess P x .raising c') (u : Use) :
    u.level = .nonSubjective ↔
      ∀ c c' : C, Use.denote go prepare intends assess P x u c =
        Use.denote go prepare intends assess P x u c' := by
  obtain ⟨c, c', h⟩ := hne
  cases u
  · exact iff_of_true rfl fun _ _ ↦ rfl
  · exact iff_of_true rfl fun _ _ ↦ rfl
  · exact iff_of_false (by decide) fun h' ↦ h (h' c c')

end GoingTo

/-! ### Partitive to Quantifier -/

/-- The stages are ordered as they are listed. -/
instance : LinearOrder Stage := LinearOrder.lift' Stage.ctorIdx (by decide)

/-- The coded level at each stage. The Extended Partitive's implication that the unit is small
is an invited inference and not yet coded, while the Quantifier's scalar meaning is coded and
subjective. -/
def Examples.Stage.level : Stage → SubjectivityLevel
  | .prePartitive | .partitive | .extendedPartitive => .nonSubjective
  | .quantifier | .degreeModifier | .adjunct => .subjective

theorem level_monotone : Monotone Stage.level := by decide

/-- The stages at which the paper attests an item. -/
def stages (i : Item) : Finset Stage := {s | ∃ x : Example, x.item = some i ∧ x.stage = some s}

-- The three case studies share the stages from the Partitive to the Quantifier.
theorem forall_mem_stages_iff {s : Stage} :
    (∀ i ∈ [Item.aPieceOf, .aBitOf, .aShredOf], s ∈ stages i) ↔
      s ∈ Set.Icc Stage.partitive .quantifier := by
  cases s <;> decide

theorem stages_aBitOf : stages .aBitOf = Finset.univ := by decide

/-- The stages, from the first to the last. -/
def Examples.Stage.path : List Stage :=
  [.prePartitive, .partitive, .extendedPartitive, .quantifier, .degreeModifier, .adjunct]

theorem path_isChain : Stage.path.IsChain (· ⋖ ·) := by decide

theorem followsCline_stages (i : Item) :
    FollowsCline ((Stage.path.filter (· ∈ stages i)).map Stage.level) := by
  cases i <;> decide

/-- The three expansions of [himmelmann-2004]. -/
inductive Expansion where
  | hostClass
  | syntactic
  | semanticPragmatic
  deriving DecidableEq, Fintype, Repr

/-- The stage at which each expansion first occurs. The complement generalizes at the Extended
Partitive. At the Quantifier the string gains a second syntactic analysis, and its first
noun loses partitive meaning and is enriched as a quantifier. -/
def Expansion.stage : Expansion → Stage
  | .hostClass => .extendedPartitive
  | .syntactic => .quantifier
  | .semanticPragmatic => .quantifier

theorem isLUB_range_stage : IsLUB (Set.range Expansion.stage) .quantifier :=
  ⟨by rintro _ ⟨e, rfl⟩; cases e <;> decide, fun _ hs ↦ hs ⟨.syntactic, rfl⟩⟩

-- Semantic-pragmatic expansion alone, which [himmelmann-2004] takes as defining, gives the same.
theorem stage_semanticPragmatic_le_iff {s : Stage} :
    Expansion.semanticPragmatic.stage ≤ s ↔ .subjective ≤ s.level := by
  cases s <;> decide

/-- The stages by which all three expansions have occurred are those whose coded level is
subjective. -/
theorem forall_stage_le_iff {s : Stage} :
    (∀ e : Expansion, e.stage ≤ s) ↔ .subjective ≤ s.level := by
  cases s <;> decide

end Traugott2010
