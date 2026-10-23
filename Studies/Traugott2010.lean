module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.Cover
public import Linglib.Data.Examples.Traugott2010

/-!
# Traugott (2010): (Inter)subjectivity and (Inter)subjectification: A Reassessment

This file formalizes Traugott's cline of (inter)subjectivity and its diachronic reading. An
expression is *subjective* when it codes the speaker's attitude or viewpoint, and
*intersubjective* when it codes the speaker's attention to the addressee's self-image. The cline
orders coded meanings from nonsubjective through subjective to intersubjective
(`SubjectivityLevel`). The diachronic claim is that the meanings an item newly codes move up the
cline one level at a time, so that an intersubjective meaning arises from a subjectified one
(`Unidirectional`). It follows that an item with an intersubjective meaning has a subjective one
(`subjective_mem_of_intersubjective_mem`).

The case studies *a piece of*, *a bit of* and *a shred of* run from Partitive through Extended
Partitive to Quantifier (`Stage`), the last stage they share. The Quantifier is the subjectified
stage, and it alone shows all three of the expansions that Himmelmann makes criterial for
grammaticalization (`isGrammaticalized_iff`).

## Implementation notes

* A history records coded meanings only. *A bit of* is used intersubjectively as a hedge but
  codes only the subjective downtoner, so its history stops at the subjective level.
* Earlier and later meanings of an item coexist, which is why a history is a list and not a
  single current level.

## References

* [traugott-2010]
* [traugott-dasher-2002]
* [himmelmann-2004]
-/

@[expose] public section

namespace Traugott2010

/-! ### The cline -/

/-- The levels of the cline of (inter)subjectivity, from least to most subjective. -/
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
instance : LinearOrder SubjectivityLevel :=
  LinearOrder.lift' SubjectivityLevel.ctorIdx fun a b h ↦ by
    cases a <;> cases b <;> first | rfl | cases h

/-- The levels of an item's coded meanings in the order they arose. -/
abbrev History := List SubjectivityLevel

/-- A history follows the cline when each newly coded meaning is at the level of the previous
one or at the next level up. -/
def Unidirectional (h : History) : Prop := h.IsChain (· ⩿ ·)

instance : DecidablePred Unidirectional := fun h ↦
  inferInstanceAs (Decidable (h.IsChain (· ⩿ ·)))

theorem subjective_mem_of_intersubjective_mem {a : SubjectivityLevel} {h : History}
    (hc : Unidirectional (a :: h)) (ha : a ≤ .subjective) (hi : .intersubjective ∈ a :: h) :
    .subjective ∈ a :: h :=
  hc.mem_of_le_of_le ha hi (by decide)

/-! ### Partitive to Quantifier (section 4) -/

/-- The stages the three case studies share are the Partitive, the Extended Partitive with
non-food and abstract complements, and the Quantifier, Stage III; the Degree Modifier is a later
stage. -/
inductive Stage where
  | partitive
  | extendedPartitive
  | quantifier
  deriving DecidableEq, Fintype, Repr

/-- The stages are ordered as they are listed. -/
instance : LinearOrder Stage := LinearOrder.lift' Stage.ctorIdx (by decide)

/-- The coded level at each stage. The Extended Partitive's implication that the unit is small
is an invited inference and not yet coded, while the Quantifier's scalar meaning is coded and
subjective. -/
def Stage.level : Stage → SubjectivityLevel
  | .partitive => .nonSubjective
  | .extendedPartitive => .nonSubjective
  | .quantifier => .subjective

theorem stages_unidirectional :
    Unidirectional ([.partitive, .extendedPartitive, .quantifier].map Stage.level) := by
  decide

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

/-- A stage is grammaticalized, by [himmelmann-2004]'s criteria, once every expansion has
occurred. -/
def Stage.IsGrammaticalized (s : Stage) : Prop := ∀ e : Expansion, e.stage ≤ s

instance (s : Stage) : Decidable s.IsGrammaticalized := inferInstanceAs (Decidable (∀ _, _))

theorem isGrammaticalized_iff {s : Stage} : s.IsGrammaticalized ↔ s = .quantifier := by
  cases s <;> decide

end Traugott2010
