module

public import Linglib.Core.Order.Antisymmetrization
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Defs.Unbundled

/-!
# Qualitative probability

Comparative probability reads a relation `r a b` on a Boolean algebra `α` as "`a` is at
least as likely as `b`". This file states the axioms of the subject as unbundled mixin
classes on such a relation, in the style of `IsTrans`, and collects de Finetti's system, the
standard base of comparative probability that Kraft, Pratt and Seidenberg and Scott build
on, as the class `IsQualitativeProbability`: `⊥` is not at least as likely as `⊤`, every
event is at least as likely as `⊥`, and the relation is total, transitive and qualitatively
additive (`a ≿ b ↔ a \ b ≿ b \ a`). Monotonicity follows from these axioms.

A likelihood order also defines *probably*: `△a` holds when `a` is strictly more likely than
its complement, as in the logics of comparative probability that Holliday and Icard compare.
Over a monotone order the contradiction is never probable and, when the order is non-trivial,
the tautology always is; over a monotone transitive order *probably* is upward closed.
`RightUnion` is Halpern's union property `J`, and `DeterminedBySingletons` his property that
comparisons with a single world reduce to comparisons of single worlds.

## Main definitions

* `IsLikelihoodMono`, `IsQualitativeAdditive`, `IsNontrivial`, `IsComplementReversing`: the
  axiom mixins on a relation. Its asymmetric part `a ≻ b` is Core's `AsymmRel r`.
* `IsQualitativeProbability`: de Finetti's axioms on a relation.
* `Probably`, `RightUnion`, `DeterminedBySingletons`: *probably* and Halpern's two properties of
  Lewis's comparative possibility.

## Main statements

* `instComplementReversingOfQualitativeAdditive`: qualitative additivity implies complement
  reversal, via `bᶜ \ aᶜ = a \ b` (`compl_sdiff_compl`).
* `IsQualitativeProbability.isLikelihoodMono`: a qualitative probability is monotone.

## References

* [kraft-pratt-seidenberg-1959]
* [scott-1964]
* [holliday-icard-2013]
* [halpern-2003]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α]

/-! ### The axioms as mixins -/

/-- A relation is monotone when every event is at least as likely as its subevents. -/
class IsLikelihoodMono (r : α → α → Prop) : Prop where
  mono : ∀ a b : α, a ≤ b → r b a

/-- A relation reverses complements when `a ≽ b` gives `bᶜ ≽ aᶜ`. -/
class IsComplementReversing (r : α → α → Prop) : Prop where
  complRev : ∀ a b : α, r a b → r bᶜ aᶜ

/-- A relation is qualitatively additive when `a ≽ b` holds exactly when `a \ b ≽ b \ a`. This
is de Finetti's additivity axiom with the common part `a ⊓ b` cancelled from both sides;
`isQualitativeAdditive_iff` recovers the axiom as printed. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- A relation is non-trivial when `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- Qualitative additivity implies complement reversal, since `bᶜ \ aᶜ = a \ b` and
`aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

/-! ### Qualitative probabilities -/

/-- A **qualitative probability** on a Boolean algebra `α` is a relation `r`, read "`a` is at
least as likely as `b`", satisfying de Finetti's axioms as [scott-1964] lists them (p. 246):
`⊥` is not at least as likely as `⊤`, every event is at least as likely as `⊥`, any two events
compare, `r` is transitive, and `r` is qualitatively additive, which is axiom (v) with the
common part of the two sides cancelled (`isQualitativeAdditive_iff`). Every qualitative
probability on a finite carrier is represented by a qualitatively additive measure
(`exists_qualAddMeasure_repr`), but by a probability measure only below five atoms
(`Completeness.lean`). -/
class IsQualitativeProbability (r : α → α → Prop) : Prop
    extends IsNontrivial r, Std.Total r, IsTrans α r, IsQualitativeAdditive r where
  /-- Every event is at least as likely as `⊥`. Use the lemma `rel_bot`. -/
  rel_bot' : ∀ a, r a ⊥

/-- A qualitative probability is monotone: for `a ≤ b`, qualitative additivity reduces `b ≽ a`
to `b \ a ≽ ⊥`. -/
instance (priority := 100) IsQualitativeProbability.isLikelihoodMono {r : α → α → Prop}
    [IsQualitativeProbability r] : IsLikelihoodMono r where
  mono a b h := by
    rw [qadd (r := r), sdiff_eq_bot_iff.mpr h]; exact IsQualitativeProbability.rel_bot' _

instance (priority := 100) IsQualitativeProbability.isPreorder {r : α → α → Prop}
    [IsQualitativeProbability r] : IsPreorder α r where

/-! ### *Probably* -/

/-- `Probably r a` ("`△a`") says that `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := AsymmRel r a aᶜ

/-- A relation is right-union closed, Halpern's axiom `J`, when `a ≽ b` and `a ≽ c` give
`a ≽ (b ⊔ c)`. This union property separates the l-lifting from the additive semantics. -/
def RightUnion {β : Type*} [SemilatticeSup β] (r : β → β → Prop) : Prop :=
  ∀ a b c, r a b → r a c → r a (b ⊔ c)

/-- A relation on propositions is determined by singletons when `r A {b}` gives some `a ∈ A`
with `r {a} {b}`. With `RightUnion` it characterizes Lewis's comparative possibility. -/
def DeterminedBySingletons {β : Type*} (r : Set β → Set β → Prop) : Prop :=
  ∀ (A : Set β) (b : β), r A {b} → ∃ a ∈ A, r {a} {b}

variable {r : α → α → Prop} {a b : α}

theorem rel_bot [IsLikelihoodMono r] (a : α) : r a ⊥ := mono _ _ bot_le

theorem top_rel [IsLikelihoodMono r] (a : α) : r ⊤ a := mono _ _ le_top

theorem Probably.mono [IsLikelihoodMono r] [IsTrans α r] (hab : a ≤ b) (ha : Probably r a) :
    Probably r b :=
  AsymmRel.trans_le (asymmRel_of_rel_of_asymmRel (IsLikelihoodMono.mono _ _ hab) ha)
    (IsLikelihoodMono.mono _ _ (compl_le_compl hab))

theorem probably_top [IsLikelihoodMono r] [IsNontrivial r] : Probably r ⊤ := by
  rw [Probably, compl_top]
  exact ⟨rel_bot _, IsNontrivial.bot_not_ge_top⟩

theorem not_probably_bot [IsLikelihoodMono r] : ¬ Probably r ⊥ := fun h ↦
  h.2 (by rw [compl_bot]; exact top_rel _)

end ComparativeProbability
