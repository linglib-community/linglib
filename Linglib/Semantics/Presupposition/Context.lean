module

public import Linglib.Semantics.Presupposition.Basic
public import Mathlib.Basic.Rel
public import Linglib.Discourse.CommonGround

/-!
# Presuppositions in context

A context set admits a sentence with a presupposition when it entails the presupposition, in the
tradition of Stalnaker, Karttunen and Heim: for a trivalent proposition `p`, when
`C ⊆ Function.support p`. An embedded clause is checked in its local context. Karttunen's table
gives the local contexts of the connectives (`Connective.localContext`): a first argument and the
argument of negation are evaluated in the context itself, the second argument of a conjunction or
a conditional in the context updated with the first argument, and a second disjunct in the context
updated with the first disjunct's negation. The complement of an attitude verb is evaluated in the
image of the context under the subject's doxastic accessibility, which admits a sentence iff the
context entails the core of its presupposition along the relation (`SetRel.image_subset_iff`), so
the report presupposes that the subject believes what the complement presupposes.

Theories of projection agree on the table and differ in why it holds. Karttunen's filtering
connectives, Peters' Middle Kleene connectives, are admittance in it
(`subset_support_meetMiddle_iff`), Heim's context change potentials evaluate their second argument
in it (`Semantics/Dynamic/Partial.lean`), and Schlenker derives it from transparency. They part at
disjunction, where the table is asymmetric and symmetric filtering is `TwoDim.orKPSymmetric`.

Accommodating a presupposition restricts the context to where the sentence is defined, and
Doron and Wehbe require that the sentence then still be informative, which holds exactly when it
is false somewhere in the context.

## Main declarations

* `Connective.localContext`: the local context of the second argument of a connective.
* `subset_support_meetMiddle_iff`, `subset_support_neg_joinMiddle_iff`,
  `subset_support_joinMiddle_iff`: the filtering connectives are admittance in the local contexts.
* `PostAccommodationInformative`, `postAccommodationInformative_iff`: informativity after
  accommodation is falsity somewhere in the context.

## References

* [stalnaker-1974]
* [heim-1983]
* [heim-1992]
* [karttunen-1973]
* [karttunen-1974-presupposition]
* [peters-1979]
* [schlenker-2009]
* [doron-wehbe-2022]
* [spector-2025]
-/

@[expose] public section

namespace Presupposition

open Trivalent

variable {W : Type*}

/-- The binary connectives of [karttunen-1974-presupposition]'s table of local contexts. -/
inductive Connective
  | conj
  | cond
  | disj
  deriving DecidableEq, Fintype

/-- The local context of a connective's second argument in the context `C`, where `A` is the
first argument's content. It is `C` updated with `A` for a conjunction or a conditional, and with
the negation of `A` for a disjunction. -/
def Connective.localContext (C A : Set W) : Connective → Set W
  | conj => C ∩ A
  | cond => C ∩ A
  | disj => C ∩ Aᶜ

open Connective

variable {C : Set W} {p q : W → SignType}

/-- A context admits Karttunen's filtering conjunction when it admits the first conjunct and the
second conjunct's local context admits the second. -/
theorem subset_support_meetMiddle_iff :
    C ⊆ Function.support (fun w ↦ (p w).meetMiddle (q w)) ↔
      C ⊆ Function.support p ∧ conj.localContext C (posSupport p) ⊆ Function.support q := by
  simp only [Set.subset_def, Function.mem_support, ne_eq, SignType.meetMiddle_eq_zero_iff,
    not_or, not_and, localContext, Set.mem_inter_iff, mem_posSupport, and_imp]
  exact ⟨fun h ↦ ⟨fun w hw ↦ (h w hw).1, fun w hw ↦ (h w hw).2⟩,
    fun h w hw ↦ ⟨h.1 w hw, h.2 w hw⟩⟩

/-- A context admits Karttunen's filtering conditional when it admits the antecedent and the
consequent's local context admits the consequent. -/
theorem subset_support_neg_joinMiddle_iff :
    C ⊆ Function.support (fun w ↦ (-p w).joinMiddle (q w)) ↔
      C ⊆ Function.support p ∧ cond.localContext C (posSupport p) ⊆ Function.support q := by
  simp only [Set.subset_def, Function.mem_support, ne_eq, SignType.joinMiddle_eq_zero_iff,
    SignType.neg_eq_zero_iff, SignType.neg_eq_neg_one_iff, not_or, not_and, localContext,
    Set.mem_inter_iff, mem_posSupport, and_imp]
  exact ⟨fun h ↦ ⟨fun w hw ↦ (h w hw).1, fun w hw ↦ (h w hw).2⟩,
    fun h w hw ↦ ⟨h.1 w hw, h.2 w hw⟩⟩

/-- A context admits Karttunen's filtering disjunction when it admits the first disjunct and the
second disjunct's local context admits the second. -/
theorem subset_support_joinMiddle_iff :
    C ⊆ Function.support (fun w ↦ (p w).joinMiddle (q w)) ↔
      C ⊆ Function.support p ∧ disj.localContext C (posSupport p) ⊆ Function.support q := by
  simp only [Set.subset_def, Function.mem_support, ne_eq, SignType.joinMiddle_eq_zero_iff,
    not_or, not_and, localContext, Set.mem_inter_iff, Set.mem_compl_iff, mem_posSupport, and_imp]
  refine ⟨fun h ↦ ⟨fun w hw ↦ (h w hw).1, fun w hw h1 ↦ ?_⟩, fun h w hw ↦ ⟨h.1 w hw, ?_⟩⟩
  · exact (h w hw).2 (by have := (h w hw).1; cases hp : p w <;> simp_all)
  · exact fun _ ↦ h.2 w hw (by intro h1; simp_all)

/-! ### Informativity after accommodation

Accommodating the presupposition of a sentence restricts the context to where the sentence is
defined. Doron and Wehbe's constraint asks that the sentence still be informative there. -/

/-- A sentence is informative after accommodation in `C`, [doron-wehbe-2022]'s
Post-Accommodation Informativity, when the context with its presupposition accommodated does not
entail it. -/
def PostAccommodationInformative (C : Set W) (p : W → SignType) : Prop :=
  ¬ C ∩ Function.support p ⊆ posSupport p

/-- A sentence is informative after accommodation exactly when it is false somewhere in the
context ([spector-2025], (3) and (4)). -/
theorem postAccommodationInformative_iff :
    PostAccommodationInformative C p ↔ ∃ w ∈ C, p w = -1 := by
  simp only [PostAccommodationInformative, Set.subset_def, Set.mem_inter_iff,
    Function.mem_support, mem_posSupport, not_forall, exists_prop, and_assoc]
  exact exists_congr fun w ↦ and_congr_right fun _ ↦ by cases p w <;> decide

theorem PostAccommodationInformative.mono {C' : Set W} (h : PostAccommodationInformative C p)
    (hC : C ⊆ C') : PostAccommodationInformative C' p :=
  let ⟨w, hw, hp⟩ := postAccommodationInformative_iff.1 h
  postAccommodationInformative_iff.2 ⟨w, hC hw, hp⟩

end Presupposition
