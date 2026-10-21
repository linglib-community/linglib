module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Semantics.Tense.Embedding
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Schlenker (2004b): Sequence Phenomena and Double Access Readings Generalized

This file formalizes the chapter's two remarks. The first is that sequence of tense is one
instance of an agreement mechanism shared by person, tense and mood. An attitude verb quantifies
over the contexts compatible with the attitude, an embedded argument read de se is a coordinate
of the bound context variable, and the features it is pronounced with are copied from the
arguments of the embedding verb by the formation rule (22) (`Features.ofArgs`) without being
interpreted. The fragment of Appendix A is given as terms carrying features (`Term`,
`TimeTerm`), formulas with the attitude construction (`Formula`), and their value and
definedness at an assignment and an utterance context. A de se report then has the truth
conditions of (13b) and inherits no presupposition from its embedded features, whereas
interpreting a person, tense or mood feature on a coordinate makes its presupposition project
universally over the attitude's contexts, which the examples (16), (19) and (21) refute
(`past_coord_weird`, `ind_coord_not_weird_iff`). Features are transmitted unchanged down a chain
of attitudes, also through a future auxiliary, which (22) keeps out of agreement
(`Features.ofArgs_coord_fut`), as the example (24) of [kamp-rohrer-1983] requires.

The second remark generalizes the upper limit constraint of [abusch-1997] from tense to mood.
After the de re transformation a tense or mood denotes a description of times or worlds relative
to the local context, and the coordinate of that context is an upper limit for it: a time
description may not lie entirely after the context's time, and a world description must contain
its world, one constraint for both (`ULC`). Double access for tense follows as in Abusch, and the
same argument yields its modal counterpart, the reading on which the agent's thought is about the
actual world as well as the world of the thought act (`doubleAccess_of_ulc`,
`worldDoubleAccess_of_ulc`): in both the description contains the coordinate of the thought and
the actual one.

## Implementation notes

* Failure of denotation is a definedness predicate beside a total value rather than a partial
  denotation, and the diacritic of a context variable is read off the enclosing attitude's
  arguments by (22) rather than stored on its coordinates, so the feature a term is pronounced
  with is the feature appearing in it. Disjunction is omitted. Vividness of descriptions is left
  to the hypotheses of the double access theorems.
* The chapter states the upper limit constraint for present and past time terms and indicative
  world terms only; the constraint here is on descriptions, and which terms it applies to is
  left to its application.

## References

* [schlenker-2004b]
* [abusch-1997]
* [heim-1994]
* [kamp-rohrer-1983]
-/

@[expose] public section

namespace Schlenker2004b

open Tense Kaplan

variable {W E P T : Type*}

/-! ### The fragment (Appendix A) -/

/-- The person features. -/
inductive PersonFeature
  | he
  | she
  deriving DecidableEq

/-- The tense features. -/
inductive TenseFeature
  | pres
  | past
  deriving DecidableEq

/-- The mood features. -/
inductive MoodFeature
  | ind
  | subj
  deriving DecidableEq

/-- The feature triple a complementizer carries, each coordinate possibly absent. -/
structure Features where
  person : Option PersonFeature
  tense : Option TenseFeature
  mood : Option MoodFeature
  deriving DecidableEq

/-- A term of one of the fragment's sorts: a bare variable, the corresponding coordinate of the
context variable `c_i`, or a term carrying a feature. -/
inductive Term (φ : Type)
  | var (k : ℕ)
  | coord (i : ℕ)
  | feat (f : φ) (t : Term φ)

/-- A time term: a term, or a future built on a time term with a variable of its own. -/
inductive TimeTerm
  | base (t : Term TenseFeature)
  | fut (k : ℕ) (t : TimeTerm)

/-- The feature appearing in a term, which is also the feature it is pronounced with; the
diacritic of a context variable is supplied by the environment `env` (Appendix A, Note A). -/
def Term.feature {φ : Type} (proj : Features → Option φ) (env : ℕ → Features) :
    Term φ → Option φ
  | .var _ => none
  | .coord i => proj (env i)
  | .feat f _ => some f

/-- The tense feature appearing in a time term; a future auxiliary contributes none. -/
def TimeTerm.feature (env : ℕ → Features) : TimeTerm → Option TenseFeature
  | .base t => t.feature Features.tense env
  | .fut _ t => t.feature env

/-- (22): the diacritic of the complementizer of an attitude verb with arguments `i`, `t` and
`w`, the person, tense and mood features appearing in them. -/
def Features.ofArgs (env : ℕ → Features) (i : Term PersonFeature) (t : TimeTerm)
    (w : Term MoodFeature) : Features :=
  ⟨i.feature Features.person env, t.feature env, w.feature Features.mood env⟩

/-- An attitude verb whose arguments are the coordinates of the context variable `c_k` passes
that variable's diacritic on unchanged. -/
theorem Features.ofArgs_coord (env : ℕ → Features) (k : ℕ) :
    Features.ofArgs env (.coord k) (.base (.coord k)) (.coord k) = env k := rfl

/-- (24): the diacritic passes through a future auxiliary on the time argument, so *would*,
the future of a past coordinate, transmits past. -/
theorem Features.ofArgs_coord_fut (env : ℕ → Features) (k j : ℕ) :
    Features.ofArgs env (.coord k) (.fut j (.base (.coord k))) (.coord k) = env k := rfl

/-- A model of the fragment: the genders behind *he* and *she*, the simple predicates, and
the contexts compatible with each attitude verb at an individual, time and world, when there
is such an attitude. -/
structure Model (W E P T : Type*) where
  /-- Being male at a time in a world. -/
  male : E → T → W → Prop
  /-- Being female at a time in a world. -/
  female : E → T → W → Prop
  /-- The simple predicates, indexed. -/
  pred : ℕ → E → T → W → Prop
  /-- The contexts compatible with attitude verb `V` held by an individual at a time in a
  world, if there is such an attitude. -/
  att : ℕ → E → T → W → Option (Set (Context W E P T))

/-- An assignment of values to the individual, time, world and context variables. -/
structure Assignment (W E P T : Type*) where
  /-- Values of the individual variables. -/
  ind : ℕ → E
  /-- Values of the time variables. -/
  time : ℕ → T
  /-- Values of the world variables. -/
  world : ℕ → W
  /-- Values of the context variables. -/
  ctx : ℕ → Context W E P T

/-- The assignment with the context variable `k` set to `c`. -/
def Assignment.updateCtx (s : Assignment W E P T) (k : ℕ) (c : Context W E P T) :
    Assignment W E P T :=
  { s with ctx := Function.update s.ctx k c }

variable (M : Model W E P T) (c₀ : Context W E P T) (s : Assignment W E P T)

/-- The presupposition of a person feature at the utterance context `c₀`. -/
def PersonFeature.Presup : PersonFeature → E → Prop
  | .he, x => M.male x c₀.time c₀.world
  | .she, x => M.female x c₀.time c₀.world

/-- The presupposition of a tense feature at the utterance context `c₀`. -/
def TenseFeature.Presup [Preorder T] : TenseFeature → T → Prop
  | .pres, t => t = c₀.time
  | .past, t => t < c₀.time

/-- The presupposition of a mood feature at the utterance context `c₀`; the subjunctive
carries none. -/
def MoodFeature.Presup : MoodFeature → W → Prop
  | .ind, w => w = c₀.world
  | .subj, _ => True

/-- The value of a term: a variable's value, the coordinate of the context variable's value, or
the value of the term a feature is attached to. -/
def Term.value {φ : Type} {α : Type*} (val : ℕ → α) (coordOf : Context W E P T → α) :
    Term φ → α
  | .var k => val k
  | .coord i => coordOf (s.ctx i)
  | .feat _ t => Term.value val coordOf t

/-- A term is weird when a feature on it has its presupposition violated by the value of the
term it is attached to. -/
def Term.Weird {φ : Type} {α : Type*} (val : ℕ → α) (coordOf : Context W E P T → α)
    (presup : φ → α → Prop) : Term φ → Prop
  | .var _ => False
  | .coord _ => False
  | .feat f t => Term.Weird val coordOf presup t ∨ ¬ presup f (t.value s val coordOf)

/-- The value of a time term; a future denotes its own variable. -/
def TimeTerm.value : TimeTerm → T
  | .base t => t.value s s.time Context.time
  | .fut k _ => s.time k

/-- A future is weird unless its variable is after the term it is built on. -/
def TimeTerm.Weird [Preorder T] : TimeTerm → Prop
  | .base t => t.Weird s s.time Context.time (TenseFeature.Presup c₀)
  | .fut k t => TimeTerm.Weird t ∨ ¬ t.value s < s.time k

/-- Weirdness of the three arguments of a predicate or attitude verb. -/
def ArgsWeird [Preorder T] (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature) :
    Prop :=
  i.Weird s s.ind Context.agent (PersonFeature.Presup M c₀) ∨ t.Weird c₀ s ∨
    w.Weird s s.world Context.world (MoodFeature.Presup c₀)

/-- The formulas: atomic predications, negation, conjunction, and the attitude construction
`i V-t-w that_{c_k} φ`, whose complementizer binds the context variable `k`. -/
inductive Formula
  | atom (P : ℕ) (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature)
  | neg (φ : Formula)
  | conj (φ ψ : Formula)
  | att (V : ℕ) (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature) (k : ℕ)
      (φ : Formula)

/-- The individual, time and world arguments of a predicate or attitude verb. -/
def args (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature) : E × T × W :=
  (i.value s s.ind Context.agent, t.value s, w.value s s.world Context.world)

/-- The contexts compatible with the attitude `V` at the arguments, if there is one. -/
def attAt (V : ℕ) (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature) :
    Option (Set (Context W E P T)) :=
  M.att V (i.value s s.ind Context.agent) (t.value s) (w.value s s.world Context.world)

/-- Presupposition failure of a formula: an argument is weird, or some context compatible with
the attitude makes the complement weird. -/
def Formula.Weird [Preorder T] : Assignment W E P T → Formula → Prop
  | s, .atom _ i t w => ArgsWeird M c₀ s i t w
  | s, .neg φ => Formula.Weird s φ
  | s, .conj φ ψ => Formula.Weird s φ ∨ Formula.Weird s ψ
  | s, .att V i t w k φ => ArgsWeird M c₀ s i t w ∨
      ∃ A ∈ attAt M s V i t w, ∃ c ∈ A, Formula.Weird (s.updateCtx k c) φ

/-- Truth of a formula: an attitude report holds when there is such an attitude and its
complement holds at every compatible context. -/
def Formula.Holds : Assignment W E P T → Formula → Prop
  | s, .atom P i t w => M.pred P (i.value s s.ind Context.agent) (t.value s)
      (w.value s s.world Context.world)
  | s, .neg φ => ¬ Formula.Holds s φ
  | s, .conj φ ψ => Formula.Holds s φ ∧ Formula.Holds s ψ
  | s, .att V i t w k φ => ∃ A ∈ attAt M s V i t w, ∀ c ∈ A, Formula.Holds (s.updateCtx k c) φ

/-! ### De se readings and agreement (§1) -/

variable (V Pr : ℕ) (i : Term PersonFeature) (t : TimeTerm) (w : Term MoodFeature) (k : ℕ)

/-- (13b), (23b): the report whose embedded arguments are all read de se, the coordinates of
the bound context variable, pronounced with the features of the diacritic. -/
def deSe : Formula := .att V i t w k (.atom Pr (.coord k) (.base (.coord k)) (.coord k))

/-- (13b): a de se report holds iff there is such an attitude and at every compatible context
its agent satisfies the predicate at its time in its world. -/
theorem deSe_holds_iff :
    (deSe V Pr i t w k).Holds M s ↔
      ∃ A ∈ attAt M s V i t w, ∀ c ∈ A, M.pred Pr c.agent c.time c.world := by
  simp [deSe, Formula.Holds, Term.value, TimeTerm.value, Assignment.updateCtx]

/-- The embedded features of a de se report, being uninterpreted, add no presupposition: the
report is weird only through its matrix arguments. -/
theorem deSe_weird_iff [Preorder T] :
    (deSe V Pr i t w k).Weird M c₀ s ↔ ArgsWeird M c₀ s i t w := by
  simp [deSe, Formula.Weird, ArgsWeird, Term.Weird, TimeTerm.Weird]

/-- (17b), (18): interpreting the past feature on the de se time coordinate presupposes, at
every context compatible with the attitude, that its time precedes the utterance time. -/
theorem past_coord_weird_iff [Preorder T] :
    (Formula.att V i t w k (.atom Pr (.coord k) (.base (.feat .past (.coord k)))
        (.coord k))).Weird M c₀ s ↔
      ArgsWeird M c₀ s i t w ∨ ∃ A ∈ attAt M s V i t w, ∃ c ∈ A, ¬ c.time < c₀.time := by
  simp [Formula.Weird, ArgsWeird, Term.Weird, TimeTerm.Weird, Term.value, TenseFeature.Presup,
    Assignment.updateCtx]

/-- (19): when the attitude holder takes the time of her thought to be after the utterance
time, an interpreted embedded past is weird, although the sentence is fine. -/
theorem past_coord_weird [Preorder T]
    (h : ∃ A ∈ attAt M s V i t w, A.Nonempty ∧ ∀ c ∈ A, c₀.time < c.time) :
    (Formula.att V i t w k (.atom Pr (.coord k) (.base (.feat .past (.coord k)))
      (.coord k))).Weird M c₀ s := by
  obtain ⟨A, hA, ⟨c, hc⟩, hlt⟩ := h
  exact (past_coord_weird_iff M c₀ s V Pr i t w k).2 (Or.inr ⟨A, hA, c, hc, (hlt c hc).not_gt⟩)

/-- (16): interpreting a masculine feature on the de se subject presupposes that the agent of
every compatible context is male, which the report of a hope to become a woman refutes. -/
theorem he_coord_weird [Preorder T]
    (hex : ∀ x, M.female x c₀.time c₀.world → ¬ M.male x c₀.time c₀.world)
    (h : ∃ A ∈ attAt M s V i t w, A.Nonempty ∧ ∀ c ∈ A, M.female c.agent c₀.time c₀.world) :
    (Formula.att V i t w k (.atom Pr (.feat .he (.coord k)) (.base (.coord k))
      (.coord k))).Weird M c₀ s := by
  obtain ⟨A, hA, ⟨c, hc⟩, hf⟩ := h
  refine Or.inr ⟨A, hA, c, hc, Or.inl (Or.inr ?_)⟩
  simpa [Term.value, PersonFeature.Presup, Assignment.updateCtx] using hex _ (hf c hc)

/-- (21): interpreting the indicative on the de se world coordinate presupposes that the world
of every compatible context is the actual world, that is, that the agent is omniscient. -/
theorem ind_coord_not_weird_iff [Preorder T] (hargs : ¬ ArgsWeird M c₀ s i t w) :
    ¬ (Formula.att V i t w k (.atom Pr (.coord k) (.base (.coord k))
        (.feat .ind (.coord k)))).Weird M c₀ s ↔
      ∀ A ∈ attAt M s V i t w, ∀ c ∈ A, c.world = c₀.world := by
  simp only [ArgsWeird, not_or] at hargs
  obtain ⟨h₁, h₂, h₃⟩ := hargs
  simp [Formula.Weird, ArgsWeird, Term.Weird, TimeTerm.Weird, Term.value, MoodFeature.Presup,
    Assignment.updateCtx, h₁, h₂, h₃]

/-! ### The generalized upper limit constraint (§2) -/

section ULC

variable {C α : Type*}

/-- (38), (40): the coordinate `κ c` of the local context `c` is an upper limit for the
description `d` in its scope, which may not lie entirely beyond it. For times, beyond is
strictly after; for worlds, distinct. -/
def ULC (beyond : α → α → Prop) (κ : C → α) (d : C → Set α) (c : C) : Prop :=
  ¬ ∀ x ∈ d c, beyond (κ c) x

/-- (38): a time description satisfies the constraint iff it reaches the local time. -/
theorem ulc_time_iff [LinearOrder T] (d : Context W E P T → Set T) (c : Context W E P T) :
    ULC (· < ·) Context.time d c ↔ ∃ t ∈ d c, t ≤ c.time := by
  simp [ULC, not_lt]

/-- (40): a world description satisfies the constraint iff it contains the local world. -/
theorem ulc_world_iff (e : Context W E P T → Set W) (c : Context W E P T) :
    ULC (· ≠ ·) Context.world e c ↔ c.world ∈ e c := by
  simp [ULC]

/-- On a description denoting a single time the constraint is the upper limit constraint on
reference times of `Semantics/Tense/Embedding`. -/
theorem ulc_singleton_iff [LinearOrder T] (r : T) (c : Context W E P T) :
    ULC (· < ·) Context.time (λ _ => {r}) c ↔ compare r c.time ∈ upperLimitConstraint := by
  simp [ULC, not_lt]

/-- (39): a present tense under a past attitude denotes the utterance time (i'), the
description contains it at the actual context of the thought (ii'), and the constraint holds
at every compatible context (iii'); when the agent is not mistaken about the time, so that the
actual context is compatible with the thought, the description is about both the time of the
thought and the utterance time. -/
theorem doubleAccess_of_ulc [LinearOrder T] {A : Set (Context W E P T)} {c : Context W E P T}
    (hc : c ∈ A) (d : Context W E P T → Set T) (hd : (d c).OrdConnected) (hle : c.time ≤ c₀.time)
    (hii : c₀.time ∈ d c) (hiii : ∀ c' ∈ A, ULC (· < ·) Context.time d c') :
    {c.time, c₀.time} ⊆ d c := by
  obtain ⟨t, ht, htc⟩ := (ulc_time_iff d c).1 (hiii c hc)
  exact Set.pair_subset (hd.out ht hii ⟨htc, hle⟩) hii

/-- (41): the modal counterpart. An indicative under a subjunctive attitude denotes the actual
world (i'), the description contains it at the actual context of the thought (ii'), and the
constraint holds at every compatible context (iii'); when the actual context is compatible with
the thought, the description is about both the world of the thought and the actual world. -/
theorem worldDoubleAccess_of_ulc {A : Set (Context W E P T)} {c : Context W E P T} (hc : c ∈ A)
    (e : Context W E P T → Set W) (hii : c₀.world ∈ e c)
    (hiii : ∀ c' ∈ A, ULC (· ≠ ·) Context.world e c') :
    {c.world, c₀.world} ⊆ e c :=
  Set.pair_subset ((ulc_world_iff e c).1 (hiii c hc)) hii

end ULC

end Schlenker2004b
