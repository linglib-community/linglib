module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.PropInstances
public import Linglib.Core.Control.Monad.Writer

/-!
# Conventional implicature

A two-dimensional meaning pairs an at-issue value of type `α` with not-at-issue content of type
`ω`, which the speaker contributes without putting it at issue: a proposition, a truth value, or
a set of propositions. Not-at-issue content only accumulates, so such a meaning is a computation
of the writer monad whose log is the not-at-issue content, combined by meet; `TwoDim ω α` is
`Writer ω α` under the names `atIssue` and `notAtIssue` for its value and its log. Potts's rule
of [CI application](##ConventionalImplicature.TwoDim.ciApply) is a bind that hands its at-issue
argument on unmodified, and the connectives combine at-issue content applicatively, so that CIs
project from under each of them.

## Implementation notes

* Potts interprets a parsetree as its root's at-issue term with the set of CI propositions on its
  nodes. The studies take one proposition for the log, the meet of that set, so a repeated
  CI adds nothing. That suits content whose repetition is redundant, but not the strengthening
  Potts reports for repeated expressives, which needs graded expressive content.
* The dimension also carries not-at-issue content that is not a CI in Potts's sense, such as
  presuppositions (`Semantics/Presupposition/TwoDimensional.lean`), the appositive impositions of
  AnderBois, Brasoveanu and Henderson, and evidential content. How an utterance updates the
  context with each kind is not modelled here.

## References

* [potts-2005]
* [potts-2007b]
* [giorgolo-asudeh-2012]
* [anderbois-brasoveanu-henderson-2015]
-/

@[expose] public section

namespace ConventionalImplicature

universe u

/-- A two-dimensional meaning pairs an at-issue value with the not-at-issue proposition it
carries ([potts-2005]). *That bastard John is late* has at-issue content "John is late" and
not-at-issue content "the speaker disdains John". -/
abbrev TwoDim (ω : Type u) (α : Type u) := Writer ω α

namespace TwoDim

variable {ω α β : Type u}

/-- The meaning with the given at-issue value and not-at-issue content. -/
protected abbrev mk (atIssue : α) (notAtIssue : ω) : TwoDim ω α := Writer.mk atIssue notAtIssue

/-- The at-issue value. -/
abbrev atIssue (m : TwoDim ω α) : α := Writer.val m

/-- The not-at-issue content. -/
abbrev notAtIssue (m : TwoDim ω α) : ω := Writer.log m

section Monad

variable [SemilatticeInf ω] [OrderTop ω]

/-! ### CI application -/

/-- CI application ([potts-2005]) applies a CI functor `f` to an at-issue argument, hands the
argument on unmodified and adds the result to the not-at-issue content. -/
def ciApply (f : α → ω) (p : TwoDim ω α) : TwoDim ω α := p >>= fun a ↦ .mk a (f a)

@[simp] theorem ciApply_atIssue (f : α → ω) (p : TwoDim ω α) :
    (p.ciApply f).atIssue = p.atIssue := rfl

@[simp] theorem ciApply_notAtIssue (f : α → ω) (p : TwoDim ω α) :
    (p.ciApply f).notAtIssue = p.notAtIssue ⊓ f p.atIssue := rfl

/-! ### Connectives -/

section Connectives

variable [BooleanAlgebra α] (p q : TwoDim ω α)

/-- Negation complements the at-issue proposition and passes the not-at-issue content up. -/
def neg : TwoDim ω α := compl <$> p

/-- Conjunction conjoins the at-issue propositions. -/
def and : TwoDim ω α := (· ⊓ ·) <$> p <*> q

/-- Disjunction disjoins the at-issue propositions. -/
def or : TwoDim ω α := (· ⊔ ·) <$> p <*> q

/-- Implication takes the conditional of the at-issue propositions. -/
def imp : TwoDim ω α := (· ⇨ ·) <$> p <*> q

@[simp] theorem neg_atIssue : p.neg.atIssue = p.atIssueᶜ := rfl

@[simp] theorem neg_notAtIssue : p.neg.notAtIssue = p.notAtIssue := rfl

@[simp] theorem neg_neg : p.neg.neg = p := Writer.ext (compl_compl _) rfl

@[simp] theorem and_atIssue : (p.and q).atIssue = p.atIssue ⊓ q.atIssue := rfl

@[simp] theorem and_notAtIssue : (p.and q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem or_atIssue : (p.or q).atIssue = p.atIssue ⊔ q.atIssue := rfl

@[simp] theorem or_notAtIssue : (p.or q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem imp_atIssue : (p.imp q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem imp_notAtIssue : (p.imp q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

end Connectives

end Monad

end TwoDim

end ConventionalImplicature
