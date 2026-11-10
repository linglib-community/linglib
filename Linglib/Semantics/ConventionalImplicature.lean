module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.PropInstances

/-!
# Conventional implicature

A two-dimensional meaning `TwoDim W α` pairs an at-issue value of type `α` with not-at-issue
content, a proposition over worlds `W` that the speaker contributes without putting it at issue.
Not-at-issue content only accumulates, so `TwoDim W` is the writer monad over propositions under
meet. Potts's rule of [CI application](##ConventionalImplicature.TwoDim.ciApply) is a bind that
hands its at-issue argument on unmodified, and the connectives combine at-issue content
applicatively, so that CIs project from under each of them.

## Implementation notes

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
carries ([potts-2005]). *That bastard John is late* has at-issue content "John is late" and
not-at-issue content "the speaker disdains John". -/
@[ext]
structure TwoDim (W : Type u) (α : Type u) where
  /-- The at-issue value. -/
  atIssue : α
  /-- The not-at-issue content. -/
  notAtIssue : W → Prop

namespace TwoDim

variable {W α β : Type u}

/-! ### The monad -/

/-- Two-dimensional meanings form the writer monad over propositions under meet, the monad
[giorgolo-asudeh-2012] give for conventional implicature. A `pure` value contributes no
not-at-issue content, and composition meets the not-at-issue content of its parts. -/
instance : Monad (TwoDim W) where
  pure a := ⟨a, ⊤⟩
  map f p := ⟨f p.atIssue, p.notAtIssue⟩
  seq f p := ⟨f.atIssue (p ()).atIssue, f.notAtIssue ⊓ (p ()).notAtIssue⟩
  bind p f := ⟨(f p.atIssue).atIssue, p.notAtIssue ⊓ (f p.atIssue).notAtIssue⟩

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

instance : LawfulMonad (TwoDim W) := LawfulMonad.mk' (TwoDim W)
  (id_map := fun _ ↦ rfl)
  (pure_bind := fun _ _ ↦ TwoDim.ext rfl (top_inf_eq _))
  (bind_assoc := fun _ _ _ ↦ TwoDim.ext rfl (inf_assoc ..))
  (bind_pure_comp := fun _ _ ↦ TwoDim.ext rfl (inf_top_eq _))
  (bind_map := fun _ _ ↦ rfl)

/-! ### CI application -/

/-- CI application ([potts-2005]) applies a CI functor `f` to an at-issue argument, hands the
argument on unmodified and adds the result to the not-at-issue content. -/
def ciApply (f : α → W → Prop) (p : TwoDim W α) : TwoDim W α := p >>= fun a ↦ ⟨a, f a⟩

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
