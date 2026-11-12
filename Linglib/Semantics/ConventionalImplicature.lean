module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.PropInstances
public import Mathlib.Order.Hom.BoundedLattice
public import Linglib.Core.Control.Monad.Writer

/-!
# Conventional implicature

A two-dimensional meaning `TwoDim ω α` pairs an at-issue value of type `α` with not-at-issue
content of type `ω`, which the speaker contributes without putting it at issue: a proposition,
a truth value, or a set of propositions. Not-at-issue content only accumulates, so `TwoDim ω` is
mathlib's writer monad over a meet-semilattice with a top, its value the at-issue dimension and
its log the not-at-issue one, and a map of logs that preserves meets and the top is
[a morphism of the monads](##ConventionalImplicature.TwoDim.mapLog). Potts's rule of
[CI application](##ConventionalImplicature.TwoDim.ciApply) is a bind that hands its at-issue
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
def TwoDim (ω : Type u) (α : Type u) := Writer ω α

namespace TwoDim

variable {ω ω' α β : Type u}

/-- The meaning with the given at-issue value and not-at-issue content. -/
protected def mk (atIssue : α) (notAtIssue : ω) : TwoDim ω α :=
  Writer.mk atIssue notAtIssue

/-- The at-issue value. -/
def atIssue (m : TwoDim ω α) : α := Writer.val m

/-- The not-at-issue content. -/
def notAtIssue (m : TwoDim ω α) : ω := Writer.log m

@[ext] protected theorem ext {m n : TwoDim ω α} (ha : m.atIssue = n.atIssue)
    (hn : m.notAtIssue = n.notAtIssue) : m = n :=
  Writer.ext ha hn

@[simp] theorem atIssue_mk (a : α) (p : ω) : (TwoDim.mk a p).atIssue = a := rfl

@[simp] theorem notAtIssue_mk (a : α) (p : ω) : (TwoDim.mk a p).notAtIssue = p := rfl

@[simp] theorem mk_inj {a b : α} {p q : ω} :
    TwoDim.mk a p = TwoDim.mk b q ↔ a = b ∧ p = q :=
  ⟨fun h ↦ ⟨congrArg atIssue h, congrArg notAtIssue h⟩, fun ⟨ha, hp⟩ ↦ ha ▸ hp ▸ rfl⟩

/-! ### The monad -/

section Monad

variable [SemilatticeInf ω] [OrderTop ω]

/-- Two-dimensional meanings form the writer monad over propositions under meet, the monad
[giorgolo-asudeh-2012] give for conventional implicature: mathlib's `WriterT.monad` with `⊤` for
the empty log and meet for appending. A `pure` value contributes no not-at-issue content, and
composition meets the not-at-issue content of its parts. -/
instance : Monad (TwoDim ω) := WriterT.monad (M := Id) ⊤ (· ⊓ ·)

@[simp] theorem pure_atIssue (a : α) : (pure a : TwoDim ω α).atIssue = a := rfl

@[simp] theorem pure_notAtIssue (a : α) : (pure a : TwoDim ω α).notAtIssue = ⊤ := rfl

@[simp] theorem map_atIssue (f : α → β) (p : TwoDim ω α) : (f <$> p).atIssue = f p.atIssue :=
  rfl

@[simp] theorem map_notAtIssue (f : α → β) (p : TwoDim ω α) :
    (f <$> p).notAtIssue = p.notAtIssue := rfl

@[simp] theorem seq_atIssue (f : TwoDim ω (α → β)) (p : TwoDim ω α) :
    (f <*> p).atIssue = f.atIssue p.atIssue := rfl

@[simp] theorem seq_notAtIssue (f : TwoDim ω (α → β)) (p : TwoDim ω α) :
    (f <*> p).notAtIssue = f.notAtIssue ⊓ p.notAtIssue := rfl

@[simp] theorem bind_atIssue (p : TwoDim ω α) (f : α → TwoDim ω β) :
    (p >>= f).atIssue = (f p.atIssue).atIssue := rfl

@[simp] theorem bind_notAtIssue (p : TwoDim ω α) (f : α → TwoDim ω β) :
    (p >>= f).notAtIssue = p.notAtIssue ⊓ (f p.atIssue).notAtIssue := rfl

instance : LawfulMonad (TwoDim ω) := LawfulMonad.mk' (TwoDim ω)
  (id_map := fun _ ↦ rfl)
  (pure_bind := fun _ _ ↦ TwoDim.ext rfl (top_inf_eq _))
  (bind_assoc := fun _ _ _ ↦ TwoDim.ext rfl (inf_assoc ..))
  (bind_pure_comp := fun _ _ ↦ TwoDim.ext rfl (inf_top_eq _))
  (bind_map := fun _ _ ↦ rfl)

/-! ### CI application -/

/-- CI application ([potts-2005]) applies a CI functor `f` to an at-issue argument, hands the
argument on unmodified and adds the result to the not-at-issue content. -/
def ciApply (f : α → ω) (p : TwoDim ω α) : TwoDim ω α := p >>= fun a ↦ .mk a (f a)

@[simp] theorem ciApply_atIssue (f : α → ω) (p : TwoDim ω α) :
    (p.ciApply f).atIssue = p.atIssue := rfl

@[simp] theorem ciApply_notAtIssue (f : α → ω) (p : TwoDim ω α) :
    (p.ciApply f).notAtIssue = p.notAtIssue ⊓ f p.atIssue := rfl

/-! ### Changing the log -/

/-- Changing the log along a map that preserves meets and the top. It is a morphism of the
monads: it commutes with [`pure`](##ConventionalImplicature.TwoDim.mapLog_pure) and with
[`bind`](##ConventionalImplicature.TwoDim.mapLog_bind). -/
def mapLog [SemilatticeInf ω'] [OrderTop ω'] (f : InfTopHom ω ω') (p : TwoDim ω α) : TwoDim ω' α :=
  .mk p.atIssue (f p.notAtIssue)

section MapLog

variable [SemilatticeInf ω'] [OrderTop ω'] (f : InfTopHom ω ω')

@[simp] theorem mapLog_atIssue (p : TwoDim ω α) : (p.mapLog f).atIssue = p.atIssue := rfl

@[simp] theorem mapLog_notAtIssue (p : TwoDim ω α) :
    (p.mapLog f).notAtIssue = f p.notAtIssue := rfl

theorem mapLog_pure (a : α) : (pure a : TwoDim ω α).mapLog f = pure a :=
  TwoDim.ext rfl (map_top f)

theorem mapLog_bind (p : TwoDim ω α) (k : α → TwoDim ω β) :
    (p >>= k).mapLog f = p.mapLog f >>= fun a ↦ (k a).mapLog f :=
  TwoDim.ext rfl (map_inf f _ _)

end MapLog

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

@[simp] theorem neg_neg : p.neg.neg = p := TwoDim.ext (compl_compl _) rfl

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
