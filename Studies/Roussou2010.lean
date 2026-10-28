module

public import Linglib.Fragments.Greek.StandardModern.Complementizers
public import Linglib.Fragments.Greek.StandardModern.Verbs
public import Linglib.Semantics.Questions.Polar
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Composition.Tree
public import Linglib.Data.Examples.Roussou2010

/-!
# Roussou (2010): Selecting complementizers

This file formalizes the paper's account of the Modern Greek complementizers as nominal
elements, each with a lexical specification that fixes what it can embed and what can embed it
(`profile`). *oti*, *an*, and *pu* merge outside the clause, as the internal argument of the
matrix verb, and take a proposition: *oti* is an indefinite over propositions, *an* an
indefinite that is a polarity item, and *pu* a definite, which is why a *pu*-clause is factive,
its content presupposed and projecting through negation (`puClause_ne_zero_iff`,
`pu_projects_through_negation`), while the *oti*-clause of the same verb carries only the weak,
deniable presupposition the verb supplies. *na* merges inside the clause and reopens the
subject position, so a *na*-clause is a property rather than a proposition and cannot be
embedded under the outside mergers (`comp_over_na_type_clash`). The distribution follows from
the specifications and the lexical semantics of the selecting predicate: *an* needs a binder,
an interrogative predicate or a matrix negation or question over a proposition-taking one
(`polar_needs_binder`); *pu* needs an emotive factive, a recollection reading, or a focused
predicate; *na* is taken freely by volitionals and verbs of knowing, with control, and by
epistemic predicates only in the present tense (`epistemic_na_present`). The paper's examples
are rows, read by `rows` as the analysis predicts.

## Implementation notes

The matrix predicates are entries of the Greek fragment, classified for selection as the paper
classifies them; the classification is the paper's, with the recollection sense of *thimáme*
the fragment's stative entry, and *nomízo*'s need of an operator for its *na*-complement a
lexical mark. The type-level incompatibility of the outside mergers with *na* is stated on the
composition substrate's types, propositions as `t` and properties as `⟨e,t⟩`. Control, the
dynamic modal reading of *kséro* with *na*, the Romance and English parallels, and the paper's
argument against uninterpretable features are not formalized.

## References

* [roussou-2010]
* [christidis-1986]
* [kiparsky-kiparsky-1970]
* [adger-quer-2001]
* [hamblin-1973b]
-/

@[expose] public section

namespace Roussou2010

open Greek.StandardModern.Complementizers Greek.StandardModern.Verbs
open PhraseStructure.Tree

/-! ### The lexical specification -/

/-- An outside-merging complementizer contributes a quantification over propositions — an
indefinite ranging over a set of propositions, a polar indefinite requiring a binder, or a
definite binding a single proposition. -/
inductive Quantification
  | indefinite
  | polar
  | definite
  deriving DecidableEq, Repr

/-- A clause-typing element is lexically specified as merging outside the clause, as the matrix
verb's argument, with a quantification over propositions, or inside its lower C domain, binding
no propositional variable. -/
inductive Spec
  | outside (q : Quantification)
  | inside
  deriving DecidableEq, Repr

/-- Among the Modern Greek complementizers, *oti* is indefinite, *an* polar and *pu* definite,
all merging outside, and *na* merges inside. -/
def profile (c : Complementizer) : Option Spec :=
  if c = oti then some (.outside .indefinite)
  else if c = an then some (.outside .polar)
  else if c = pu then some (.outside .definite)
  else if c = na then some .inside
  else none

theorem factive_iff_definite :
    ∀ c ∈ complementizers,
      (c.factive = true ↔ profile c = some (.outside .definite)) := by
  decide

/-! ### The denotations -/

variable {W : Type*}

open Classical in
/-- The *oti*-clause is an indefinite over propositions, asserting its content without
presupposition. -/
noncomputable def otiClause (p : Set W) : W → SignType := fun w ↦ SignType.ofProp (w ∈ p)

/-- The *pu*-clause is a definite over propositions, presupposing the proposition it locates and
so true wherever it is defined. -/
noncomputable def puClause (p : Set W) : W → SignType := p.indicator 1

/-- The *an*-clause is the polar set of the proposition and its negation. -/
def anClause (p : Set W) : Question W := Question.polar p

theorem puClause_ne_zero_iff (p : Set W) (w : W) : puClause p w ≠ 0 ↔ w ∈ p := by
  simp [puClause]

theorem pu_projects_through_negation (p : Set W) (w : W) :
    ((-puClause p) w ≠ 0 ↔ w ∈ p) ∧ (-otiClause p) w ≠ 0 := by
  simp [puClause, otiClause]

theorem posSupport_puClause_subset (p : Set W) :
    posSupport (puClause p) ⊆ posSupport (otiClause p) := fun w hw ↦ by
  simp_all [puClause, otiClause]

theorem anClause_not_informative (p : Set W) : ¬ (anClause p).IsInformative :=
  Question.not_isInformative_polar p

theorem comp_over_na_type_clash (b : Montague.Ty) :
    Montague.Ty.combine? (.fn .t b) (.fn .e .t) = none := by
  simp [Montague.Ty.combine?, Montague.Ty.mode?, Montague.Mode.functionalLeft?,
    Montague.Mode.functionalRight?, Montague.Mode.predicateModification?,
    Montague.Mode.eventIdentification?]

/-! ### Selection -/

/-- The paper distinguishes these classes of selecting predicate — interrogatives, which bind the
polar complementizer themselves; verbs of knowing, which take any complement; epistemic verbs,
which take *na* only in the present tense, some of them only under an operator; volitionals,
which take *na* alone; emotive factives, which take *pu* alone; emotives that take *pu* on a
factive and *oti* on a non-factive reading; factive non-emotives, which take *oti* and not
*pu*; verbs of saying; and the recollection sense of *remember*, which takes *pu*. -/
inductive Class
  | interrogative
  | knowing
  | epistemic (needsOperator : Bool)
  | volitional
  | emotiveFactive
  | emotive
  | factive
  | saying
  | recollection
  deriving DecidableEq, Repr

/-- The paper's classification of the fragment's predicates. -/
def classOf (v : Verb) : Option Class :=
  if v == anarotjeme then some .interrogative
  else if v == ksero then some .knowing
  else if v == thimame then some .knowing
  else if v == thimameStat then some .recollection
  else if v == pistevo then some (.epistemic false)
  else if v == nomizo then some (.epistemic true)
  else if v == thelo then some .volitional
  else if v == xerome then some .emotiveFactive
  else if v == anisixo then some .emotive
  else if v == paradhexome then some .factive
  else if v == antilamvanome then some .factive
  else if v == leo then some .saying
  else none

/-- A selection configuration records the predicate's class, the complementizer, and the matrix
operators and tenses the paper finds relevant. -/
structure Config where
  cls : Class
  comp : Complementizer
  negated : Bool
  question : Bool
  focused : Bool
  past : Bool
  embeddedPast : Bool
  deriving DecidableEq, Repr

/-- The class takes a propositional complement, so an indefinite complementizer. -/
def Class.TakesProposition : Class → Prop
  | .knowing | .epistemic _ | .emotive | .factive | .saying | .recollection => True
  | .interrogative | .volitional | .emotiveFactive => False

instance : DecidablePred Class.TakesProposition
  | .knowing | .epistemic _ | .emotive | .factive | .saying | .recollection => isTrue trivial
  | .interrogative | .volitional | .emotiveFactive => isFalse id

/-- The class takes a set of propositions under an operator — the proposition-taking classes
other than the epistemic ones. -/
def Class.TakesSet : Class → Prop
  | .knowing | .factive | .saying => True
  | _ => False

instance : DecidablePred Class.TakesSet
  | .knowing | .factive | .saying => isTrue trivial
  | .interrogative | .epistemic _ | .volitional | .emotiveFactive | .emotive | .recollection =>
    isFalse id

/-- The complementizer is licensed in the configuration — *oti* by a proposition-taking
predicate; *an* by an interrogative predicate, or by a matrix negation or question over a
predicate taking a set of propositions; *pu* by an emotive factive, an emotive, a recollection
reading, or a focused predicate; *na* by a volitional, by a verb of knowing with a present-tense
complement, or by a present-tense epistemic, with an operator when the verb demands one. -/
def Licensed (k : Config) : Prop :=
  (k.comp = oti ∧ k.cls.TakesProposition) ∨
  (k.comp = an ∧ (k.cls = .interrogative ∨ (k.cls.TakesSet ∧ (k.negated ∨ k.question)))) ∨
  (k.comp = pu ∧ (k.cls = .emotiveFactive ∨ k.cls = .emotive ∨ k.cls = .recollection ∨
    k.focused)) ∨
  (k.comp = na ∧ (k.cls = .volitional ∨ (k.cls = .knowing ∧ ¬ k.embeddedPast) ∨
    ∃ b, k.cls = .epistemic b ∧ ¬ k.past ∧ (¬ b ∨ k.negated ∨ k.question)))

instance (k : Config) : Decidable (Licensed k) := by unfold Licensed; infer_instance

theorem polar_needs_binder (k : Config) (hc : k.comp = an) (h : Licensed k) :
    k.cls = .interrogative ∨ k.negated ∨ k.question := by
  have hne : ∀ c ∈ [oti, pu, na], an ≠ c := by decide
  rcases h with ⟨h₁, _⟩ | ⟨_, h₂ | ⟨_, h₃⟩⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩
  · exact absurd (hc ▸ h₁) (hne oti (by simp))
  · exact .inl h₂
  · exact .inr h₃
  · exact absurd (hc ▸ h₁) (hne pu (by simp))
  · exact absurd (hc ▸ h₁) (hne na (by simp))

theorem epistemic_na_present (k : Config) (b : Bool) (hc : k.comp = na)
    (hk : k.cls = .epistemic b) (h : Licensed k) : ¬ k.past := by
  have hne : ∀ c ∈ [oti, an, pu], na ≠ c := by decide
  rcases h with ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨h₁, _⟩ | ⟨_, h₂ | ⟨h₂, _⟩ | ⟨_, _, h₃, _⟩⟩
  · exact absurd (hc ▸ h₁) (hne oti (by simp))
  · exact absurd (hc ▸ h₁) (hne an (by simp))
  · exact absurd (hc ▸ h₁) (hne pu (by simp))
  · exact absurd (hk ▸ h₂) (by simp)
  · exact absurd (hk ▸ h₂) (by simp)
  · exact h₃

/-! ### The rows -/

/-- The fragment entry named by a row. -/
def verbOf : String → Option Verb
  | "ksero" => some ksero
  | "anarotjeme" => some anarotjeme
  | "xerome" => some xerome
  | "thelo" => some thelo
  | "pistevo" => some pistevo
  | "nomizo" => some nomizo
  | "thimame" => some thimame
  | "thimameStat" => some thimameStat
  | "paradhexome" => some paradhexome
  | "anisixo" => some anisixo
  | "leo" => some leo
  | _ => none

/-- A row's configuration and judgment. -/
def datum (r : Datum) : Option (Config × Judgment) := do
  let v ← (r.feature? "verb").bind verbOf
  let cls ← classOf v
  let comp ← r.parse? "complementizer" [("oti", oti), ("an", an), ("pu", pu), ("na", na)]
  let flag (key : String) : Bool := r.feature? key = some "yes"
  pure (⟨cls, comp, flag "negation", flag "question", flag "focus",
    r.feature? "tense" = some "past", r.feature? "embeddedTense" = some "past"⟩, r.judgment)

/-- The paper's examples. -/
def data : List (Config × Judgment) := Examples.all.filterMap datum

theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- The examples are acceptable exactly when their complementizer is licensed. -/
theorem rows : ∀ d ∈ data, d.2 = .acceptable ↔ Licensed d.1 := by
  decide +kernel

end Roussou2010
