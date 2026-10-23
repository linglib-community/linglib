module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Defs.Unbundled

/-!
# Qualitative probability

Comparative probability reads a relation `r a b` on a Boolean algebra `α` as "`a` is at
least as likely as `b`". This file states the axioms of the subject as unbundled mixin
classes on such a relation, in the style of `IsTrans`, and collects de Finetti's system, the
standard base of comparative probability that Kraft, Pratt and Seidenberg and Scott build
on, as the class `IsQualitativeProbability`: a monotone, non-trivial and qualitatively
additive (`a ≿ b ↔ a \ b ≿ b \ a`) total preorder.

A likelihood order also defines *probably*: `△a` holds when `a` is strictly more likely than
its complement, as in the logics of comparative probability that Holliday and Icard compare.
Over a monotone order the contradiction is never probable and, when the order is non-trivial,
the tautology always is; over a monotone transitive order *probably* is upward closed.
`RightUnion` is Halpern's union property `J`.

## Main definitions

* `IsLikelihoodMono`, `IsQualitativeAdditive`, `IsNontrivial`, `IsComplementReversing`: the
  axiom mixins on a relation; `Strict r` is its asymmetric part `a ≻ b`, which a transitive
  `r` absorbs on either side (`strict_of_strict_of_rel`, `strict_of_rel_of_strict`).
* `IsQualitativeProbability`: de Finetti's axioms on a relation.
* `Probably`, `RightUnion`: *probably* and Halpern's union property.

## Main statements

* `instComplementReversingOfQualitativeAdditive`: qualitative additivity implies complement
  reversal, via `bᶜ \ aᶜ = a \ b` (`compl_sdiff_compl`).

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

/-- A relation is qualitatively additive, de Finetti's axiom, when `a ≽ b` holds exactly when
`a \ b ≽ b \ a`. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- A relation is non-trivial when `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- `Strict r a b` ("`a ≻ b`") is the asymmetric part of `r`. -/
def Strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ r b a

instance {r : α → α → Prop} [DecidableRel r] : DecidableRel (Strict r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

section Strict

omit [BooleanAlgebra α]

variable {r : α → α → Prop} [IsTrans α r] {a b c : α}

theorem strict_of_strict_of_rel (hab : Strict r a b) (hbc : r b c) : Strict r a c :=
  ⟨_root_.trans hab.1 hbc, fun hca ↦ hab.2 (_root_.trans hbc hca)⟩

theorem strict_of_rel_of_strict (hab : r a b) (hbc : Strict r b c) : Strict r a c :=
  ⟨_root_.trans hab hbc.1, fun hca ↦ hbc.2 (_root_.trans hca hab)⟩

end Strict

/-- Qualitative additivity implies complement reversal, since `bᶜ \ aᶜ = a \ b` and
`aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

/-! ### Qualitative probabilities -/

/-- A **qualitative probability** on a Boolean algebra `α` is a relation `r`, read "`a` is at
least as likely as `b`", that is a monotone, non-trivial and qualitatively additive total
preorder: de Finetti's axioms, the base system of comparative probability. Every qualitative
probability on a finite carrier is represented by a qualitatively additive measure
(`exists_qualAddMeasure_repr`), but by a probability measure only below five atoms (Kraft,
Pratt and Seidenberg; `Completeness.lean`). -/
class IsQualitativeProbability (r : α → α → Prop) : Prop
    extends IsPreorder α r, Std.Total r, IsLikelihoodMono r, IsQualitativeAdditive r,
      IsNontrivial r

/-! ### *Probably* -/

/-- `Probably r a` ("`△a`") says that `a` is strictly more likely than its complement. -/
def Probably (r : α → α → Prop) (a : α) : Prop := Strict r a aᶜ

/-- A relation is right-union closed, Halpern's axiom `J`, when `a ≽ b` and `a ≽ c` give
`a ≽ (b ⊔ c)`. This union property separates the l-lifting from the additive semantics. -/
def RightUnion {β : Type*} [SemilatticeSup β] (r : β → β → Prop) : Prop :=
  ∀ a b c, r a b → r a c → r a (b ⊔ c)

variable {r : α → α → Prop} {a b : α}

theorem rel_bot [IsLikelihoodMono r] (a : α) : r a ⊥ := mono _ _ bot_le

theorem top_rel [IsLikelihoodMono r] (a : α) : r ⊤ a := mono _ _ le_top

theorem Probably.mono [IsLikelihoodMono r] [IsTrans α r] (hab : a ≤ b) (ha : Probably r a) :
    Probably r b :=
  strict_of_strict_of_rel (strict_of_rel_of_strict (IsLikelihoodMono.mono _ _ hab) ha)
    (IsLikelihoodMono.mono _ _ (compl_le_compl hab))

theorem probably_top [IsLikelihoodMono r] [IsNontrivial r] : Probably r ⊤ := by
  rw [Probably, compl_top]
  exact ⟨rel_bot _, IsNontrivial.bot_not_ge_top⟩

theorem not_probably_bot [IsLikelihoodMono r] : ¬ Probably r ⊥ := fun h ↦
  h.2 (by rw [compl_bot]; exact top_rel _)

end ComparativeProbability
