module

public import Eval.Basic
public import Studies.Schlenker2009
public import Studies.Kalomoiros2023

/-!
# Accounts of presupposition projection

A theory of projection says when a context accepts a sentence of the fragment that the theories
share, under an interpretation of its atoms (`Eval.Projection.Theory`): a formula of the
propositional fragment, and a quantified clause if the theory covers them. A theory silent on
quantified clauses is not thereby wrong about them. A theory predicts an inference from a formula
when every context that accepts the formula entails it (`Theory.Predicts`). This is the linking
hypothesis by which a theory's acceptance conditions meet the judgments of an inference task,
stated once and shared by every task that uses it.

The accounts linglib formalizes are registered as theories by their own acceptability predicates,
from `Semantics/Presupposition` or the paper's study (`Account.Accepts`): Heim's context change
potentials with Beaver's disjunction, Peters's filtering connectives, Schlenker's Transparency,
local satisfaction, Strong Kleene and supervaluationist theories, each checked incrementally and
symmetrically, and Kalomoiros's Limited Symmetry. Schlenker's accounts also cover quantified
clauses (`Account.AcceptsClause`); dynamic semantics, filtering and Limited Symmetry are stated for
the propositional fragment and are silent on them. A theory under development in `Lab` is
scored the same way. A theory is stronger than another when every context that accepts a formula by
the first accepts it by the second, so that it predicts presuppositions at least as strong
(`Theory.Stronger`).

## References

* [heim-1983]
* [beaver-2001]
* [peters-1979]
* [schlenker-2009]
* [schlenker-2008b]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Projection

open Presupposition

/-- When a context accepts a quantified clause, under an interpretation of its atoms as sets of
world–individual pairs. -/
abbrev ClauseAcceptance : Type 1 :=
  ∀ (Atom W E : Type), (Atom → Set (W × E)) → Set W → QuantifiedClause Atom → Prop

/-- A theory of projection says when a context accepts a formula, under an interpretation of its
atoms, and, if it covers them, when a context accepts a quantified clause. -/
structure Theory where
  /-- Whether the theory accepts a formula in a context. -/
  accepts : ∀ {Atom W : Type}, (Atom → Set W) → Set W → Formula Atom → Prop
  /-- Whether the theory accepts a quantified clause in a context, if it covers them. -/
  acceptsClause : Option ClauseAcceptance

namespace Theory

/-- `T` predicts presuppositions at least as strong as `T'` when every context that accepts a
formula by `T` accepts it by `T'`. -/
def Stronger (T T' : Theory) : Prop :=
  ∀ (Atom W : Type) (I : Atom → Set W) (C : Set W) (F : Formula Atom),
    T.accepts I C F → T'.accepts I C F

theorem Stronger.refl (T : Theory) : T.Stronger T := fun _ _ _ _ _ h ↦ h

theorem Stronger.trans {T T' T'' : Theory} (h : T.Stronger T') (h' : T'.Stronger T'') :
    T.Stronger T'' :=
  fun Atom W I C F hT ↦ h' Atom W I C F (h Atom W I C F hT)

/-- The linking hypothesis of inference tasks. A theory predicts the inference `φ` from `F` when,
under every interpretation of the atoms, every context that accepts `F` entails `φ`, so that a
hearer who accommodates what the sentence needs draws the inference. -/
def Predicts (T : Theory) {Atom : Type} (F : Formula Atom)
    (φ : ∀ {W : Type}, (Atom → Set W) → Set W) : Prop :=
  ∀ (W : Type) (I : Atom → Set W) (C : Set W), T.accepts I C F → C ⊆ φ I

/-- A stronger theory predicts every inference that a weaker one predicts. -/
theorem Predicts.of_stronger {T T' : Theory} (h : T.Stronger T') {Atom : Type}
    {F : Formula Atom} {φ : ∀ {W : Type}, (Atom → Set W) → Set W} (hT' : T'.Predicts F φ) :
    T.Predicts F φ :=
  fun W I C hC ↦ hT' W I C (h Atom W I C F hC)

end Theory

/-- The accounts of projection in the propositional fragment. -/
inductive Account where
  /-- [heim-1983]'s context change potentials, with [beaver-2001]'s disjunction. -/
  | dynamic
  /-- [peters-1979]'s filtering connectives. -/
  | filtering
  /-- [schlenker-2009]'s Transparency, over every good final. -/
  | transparencyIncremental
  /-- [schlenker-2009]'s Transparency, over the actual sentence. -/
  | transparencySymmetric
  /-- [schlenker-2009]'s local satisfaction, over every good final. -/
  | satisfactionIncremental
  /-- [schlenker-2009]'s local satisfaction, over the actual sentence. -/
  | satisfactionSymmetric
  /-- Strong Kleene definedness after each trigger with every good final ([schlenker-2008b]). -/
  | kleeneIncremental
  /-- Strong Kleene definedness of the sentence ([schlenker-2008b]). -/
  | kleeneSymmetric
  /-- Supervaluationist definedness after each trigger with every good final
  ([schlenker-2008b]). -/
  | supervaluationIncremental
  /-- Supervaluationist definedness of the sentence ([schlenker-2008b]). -/
  | supervaluationSymmetric
  /-- [kalomoiros-2023]'s Limited Symmetry. -/
  | limitedSymmetry
  deriving DecidableEq, Repr

namespace Account

variable {Atom W : Type*}

/-- Whether an account accepts a formula in a context, under an interpretation of the atoms, is
given by the theory's own predicate. -/
noncomputable def Accepts : Account → (Atom → Set W) → Set W → Formula Atom → Prop
  | dynamic => fun I C F ↦ (F.ccp I).Admits C
  | filtering => fun I C F ↦ C ⊆ Function.support (F.middleKleene I)
  | transparencyIncremental => fun I C F ↦
    Schlenker2009.Transparency .incremental C (Formula.occurrences I F)
  | transparencySymmetric => fun I C F ↦
    Schlenker2009.Transparency .symmetric C (Formula.occurrences I F)
  | satisfactionIncremental => fun I C F ↦
    Schlenker2009.Satisfaction .incremental C (Formula.occurrences I F)
  | satisfactionSymmetric => fun I C F ↦
    Schlenker2009.Satisfaction .symmetric C (Formula.occurrences I F)
  | kleeneIncremental => fun I ↦ Schlenker2009.StrongKleeneAcceptable I .incremental
  | kleeneSymmetric => fun I ↦ Schlenker2009.StrongKleeneAcceptable I .symmetric
  | supervaluationIncremental => fun I ↦ Schlenker2009.SupervaluationAcceptable I .incremental
  | supervaluationSymmetric => fun I ↦ Schlenker2009.SupervaluationAcceptable I .symmetric
  | limitedSymmetry => fun I C F ↦ Kalomoiros2023.LimitedSymmetry C (Formula.occurrences I F)

open Schlenker2009.QuantifiedClause in
/-- Whether an account accepts a quantified clause, for the accounts defined on them. -/
def AcceptsClause : Account → Option ClauseAcceptance
  | transparencyIncremental => some fun _ _ _ J C c ↦
    Schlenker2009.Transparency .incremental C (QuantifiedClause.occurrences J c)
  | transparencySymmetric => some fun _ _ _ J C c ↦
    Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences J c)
  | satisfactionIncremental => some fun _ _ _ J C c ↦
    Schlenker2009.Satisfaction .incremental C (QuantifiedClause.occurrences J c)
  | satisfactionSymmetric => some fun _ _ _ J C c ↦
    Schlenker2009.Satisfaction .symmetric C (QuantifiedClause.occurrences J c)
  | kleeneIncremental => some fun _ _ _ J ↦ StrongKleeneAcceptable J .incremental
  | kleeneSymmetric => some fun _ _ _ J ↦ StrongKleeneAcceptable J .symmetric
  | supervaluationIncremental => some fun _ _ _ J ↦ SupervaluationAcceptable J .incremental
  | supervaluationSymmetric => some fun _ _ _ J ↦ SupervaluationAcceptable J .symmetric
  | _ => none

/-- The theory an account registers. -/
def theory (a : Account) : Theory := ⟨a.Accepts, a.AcceptsClause⟩

/-- `a` predicts presuppositions at least as strong as `b`. -/
def Stronger (a b : Account) : Prop := a.theory.Stronger b.theory

theorem Stronger.refl (a : Account) : a.Stronger a := Theory.Stronger.refl _

theorem Stronger.trans {a b c : Account} (hab : a.Stronger b) (hbc : b.Stronger c) :
    a.Stronger c :=
  Theory.Stronger.trans hab hbc

end Account

end Eval.Projection
