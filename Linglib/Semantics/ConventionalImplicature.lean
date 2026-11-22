module

public import Linglib.Core.Control.Monad.Writer
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Conventional implicature

A two-dimensional meaning `TwoDim W α` pairs an at-issue value of type `α` with not-at-issue
content, a proposition over worlds `W` that the speaker contributes without putting it at issue.
Not-at-issue content only accumulates, so `TwoDim W` is the writer monad over propositions under
meet. Potts's rule of [CI application](##ConventionalImplicature.TwoDim.ciApply) is a bind that
hands its at-issue argument on unmodified, and the connectives combine at-issue content
applicatively, so that CIs project from under each of them.

## Implementation notes

* Propositions under meet are the multiplicative monoid of mathlib's `AsBoolRing (W → Prop)`,
  and `TwoDim W` is `Writer` over it; `TwoDim.mk`, `TwoDim.atIssue` and `TwoDim.notAtIssue` hide
  the synonym.
* Potts interprets a parsetree as its root's at-issue term with the set of CI propositions on its
  nodes. The not-at-issue dimension here is one proposition, the meet of that set, so a repeated
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
carries ([potts-2005]): a computation of the writer monad over propositions under meet, the monad
[giorgolo-asudeh-2012] give for conventional implicature. *That bastard John is late* has
at-issue content "John is late" and not-at-issue content "the speaker disdains John". -/
def TwoDim (W : Type u) (α : Type u) : Type u := Writer (AsBoolRing (W → Prop)) α

namespace TwoDim

variable {W α β : Type u}

instance : Monad (TwoDim W) := inferInstanceAs (Monad (Writer (AsBoolRing (W → Prop))))

instance : LawfulMonad (TwoDim W) :=
  inferInstanceAs (LawfulMonad (Writer (AsBoolRing (W → Prop))))

/-- The meaning with at-issue value `a` and not-at-issue content `n`. -/
protected def mk (a : α) (n : W → Prop) : TwoDim W α := Writer.mk a (toBoolRing n)

/-- The at-issue value. -/
def atIssue (p : TwoDim W α) : α := Writer.val p

/-- The not-at-issue content. -/
def notAtIssue (p : TwoDim W α) : W → Prop := ofBoolRing (Writer.log p)

@[ext]
protected theorem ext {p q : TwoDim W α} (ha : p.atIssue = q.atIssue)
    (hn : p.notAtIssue = q.notAtIssue) : p = q :=
  Writer.ext ha (ofBoolRing_inj.mp hn)

@[simp] theorem mk_atIssue (a : α) (n : W → Prop) : (TwoDim.mk a n).atIssue = a := rfl

@[simp] theorem mk_notAtIssue (a : α) (n : W → Prop) : (TwoDim.mk a n).notAtIssue = n := rfl

@[simp] theorem mk_inj {a b : α} {m n : W → Prop} :
    TwoDim.mk a m = TwoDim.mk b n ↔ a = b ∧ m = n :=
  ⟨fun h ↦ ⟨congrArg atIssue h, congrArg notAtIssue h⟩, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩

@[simp] theorem mk_eta (p : TwoDim W α) : TwoDim.mk p.atIssue p.notAtIssue = p := rfl

/-! ### The monad

A `pure` value contributes no not-at-issue content, and composition meets the not-at-issue
content of its parts. -/

@[simp] theorem pure_atIssue (a : α) : (pure a : TwoDim W α).atIssue = a := rfl

@[simp] theorem pure_notAtIssue (a : α) : (pure a : TwoDim W α).notAtIssue = ⊤ := rfl

@[simp] theorem map_atIssue (f : α → β) (p : TwoDim W α) : (f <$> p).atIssue = f p.atIssue :=
  rfl

@[simp] theorem map_notAtIssue (f : α → β) (p : TwoDim W α) :
    (f <$> p).notAtIssue = p.notAtIssue := rfl

@[simp] theorem seq_atIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).atIssue = f.atIssue p.atIssue := rfl

@[simp] theorem seq_notAtIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).notAtIssue = f.notAtIssue ⊓ p.notAtIssue := rfl

@[simp] theorem bind_atIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).atIssue = (f p.atIssue).atIssue := rfl

@[simp] theorem bind_notAtIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).notAtIssue = p.notAtIssue ⊓ (f p.atIssue).notAtIssue := rfl

/-! ### Sets of implicatures -/

/-- The meet of a set of propositions, as a monoid homomorphism from sets under union. -/
def sInfHom : Writer.SetLog (W → Prop) →* AsBoolRing (W → Prop) where
  toFun s := toBoolRing (sInf s.toAdd.toSet)
  map_one' := by simp
  map_mul' s t := by simp [sInf_union]

/-- A computation that logs a set of not-at-issue propositions denotes the two-dimensional
meaning whose not-at-issue content is their meet. -/
def ofSetLog (m : Writer (Writer.SetLog (W → Prop)) α) : TwoDim W α :=
  WriterT.adapt sInfHom m

@[simp] theorem ofSetLog_atIssue (m : Writer (Writer.SetLog (W → Prop)) α) :
    (ofSetLog m).atIssue = m.val := rfl

@[simp] theorem ofSetLog_notAtIssue (m : Writer (Writer.SetLog (W → Prop)) α) :
    (ofSetLog m).notAtIssue = sInf m.logSet := rfl

@[simp] theorem ofSetLog_pure (a : α) : ofSetLog (pure a : Writer _ α) = (pure a : TwoDim W α) :=
  Writer.adapt_pure sInfHom a

theorem ofSetLog_bind (m : Writer (Writer.SetLog (W → Prop)) α)
    (f : α → Writer (Writer.SetLog (W → Prop)) β) :
    ofSetLog (m >>= f) = ofSetLog m >>= fun a ↦ ofSetLog (f a) :=
  Writer.adapt_bind sInfHom m f

/-! ### CI application -/

/-- CI application ([potts-2005]) applies a CI functor `f` to an at-issue argument, hands the
argument on unmodified and adds the result to the not-at-issue content. -/
def ciApply (f : α → W → Prop) (p : TwoDim W α) : TwoDim W α := p >>= fun a ↦ .mk a (f a)

@[simp] theorem ciApply_atIssue (f : α → W → Prop) (p : TwoDim W α) :
    (p.ciApply f).atIssue = p.atIssue := rfl

@[simp] theorem ciApply_notAtIssue (f : α → W → Prop) (p : TwoDim W α) :
    (p.ciApply f).notAtIssue = p.notAtIssue ⊓ f p.atIssue := rfl

/-! ### Connectives -/

section Connectives

variable (p q : TwoDim W (W → Prop))

/-- Negation complements the at-issue proposition and passes the not-at-issue content up. -/
def neg : TwoDim W (W → Prop) := compl <$> p

/-- Conjunction conjoins the at-issue propositions. -/
def and : TwoDim W (W → Prop) := (· ⊓ ·) <$> p <*> q

/-- Disjunction disjoins the at-issue propositions. -/
def or : TwoDim W (W → Prop) := (· ⊔ ·) <$> p <*> q

/-- Implication takes the conditional of the at-issue propositions. -/
def imp : TwoDim W (W → Prop) := (· ⇨ ·) <$> p <*> q

@[simp] theorem neg_atIssue : p.neg.atIssue = p.atIssueᶜ := rfl

@[simp] theorem neg_notAtIssue : p.neg.notAtIssue = p.notAtIssue := rfl

@[simp] theorem neg_neg : p.neg.neg = p := TwoDim.ext (compl_compl _) rfl

@[simp] theorem and_atIssue : (p.and q).atIssue = p.atIssue ⊓ q.atIssue := rfl

@[simp] theorem and_notAtIssue : (p.and q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem or_atIssue : (p.or q).atIssue = p.atIssue ⊔ q.atIssue := rfl

@[simp] theorem or_notAtIssue : (p.or q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem imp_atIssue : (p.imp q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem imp_notAtIssue : (p.imp q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

end Connectives

end TwoDim

end ConventionalImplicature
