/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Composition.WithAlternatives

/-!
# Focus antecedents

[rooth-1992] reduces the effects of focus to one operator. Adjoined to a phrase $\phi$, the
squiggle $\phi \sim v$ presupposes that its free variable $v$ resolves to an antecedent the focus
semantic value of $\phi$ accommodates. In the set case the antecedent is a subset of
$[\phi]^f$ containing $[\phi]^o$ and [some other element](##squiggleSet_iff_nontrivial); in the
individual case it is an element of $[\phi]^f$ other than $[\phi]^o$, which is
[the set case at the pair](##squiggleSet_pair_iff) $\{[\phi]^o, \gamma\}$. A phrase with no
focus has the unit set of its ordinary value as focus semantic value, so
[no antecedent resolves a squiggle on it](##Antecedent.not_resolves_unfeatured).

The discourse supplies the antecedent, and its shape sets the pragmatic use of the focus
([hartmann-zimmermann-2007], on [uhmann-1991]'s notion of a context controlling a focus): a
question makes it new information, a prior assertion it corrects makes it corrective, offered
alternatives make it selective, and a phrase in contrast makes it contrastive. Questions and
offers supply a set, assertions and contrasting phrases an individual. Whether an antecedent
admits a focus depends only on the set it supplies, and
[the use cannot be read off that set](##Antecedent.use_not_factorsThrough_contrastSet): the four
uses are one semantic focus.

## Implementation notes

`Antecedent.Admits` is the first version of the focus interpretation principle, containment in
the focus semantic value, and `Antecedent.Resolves` the revised presupposition, which entails it.
The squiggle also resets the focus semantic value of its phrase to the unit set of the ordinary
value, so the node it closes is `WithAlternatives.unfeatured` and is not a definition here.

## References

* [rooth-1992]
* [hartmann-zimmermann-2007]
* [uhmann-1991]
-/

@[expose] public section

namespace Focus

variable {α : Type*}

/-! ### The squiggle presupposition -/

section Squiggle

variable {o γ : α} {fv Γ : Set α}

/-- The set case of the ~ presupposition: the antecedent `Γ` is a subset of the focus semantic
value `fv` containing the ordinary value `o` and an element distinct from it ([rooth-1992] (40)).
-/
def SquiggleSet (o : α) (fv Γ : Set α) : Prop :=
  Γ ⊆ fv ∧ o ∈ Γ ∧ ∃ x ∈ Γ, x ≠ o

/-- The individual case of the ~ presupposition: the antecedent `γ` is an element of the focus
semantic value `fv` distinct from the ordinary value `o` ([rooth-1992] (40)). -/
def SquiggleInd (o : α) (fv : Set α) (γ : α) : Prop :=
  γ ∈ fv ∧ γ ≠ o

theorem squiggleSet_iff_nontrivial : SquiggleSet o fv Γ ↔ Γ ⊆ fv ∧ o ∈ Γ ∧ Γ.Nontrivial :=
  and_congr_right' <| and_congr_right fun ho ↦ (Set.nontrivial_iff_exists_ne ho).symm

theorem squiggleInd_iff_mem_diff : SquiggleInd o fv γ ↔ γ ∈ fv \ {o} := Iff.rfl

theorem SquiggleSet.subset (h : SquiggleSet o fv Γ) : Γ ⊆ fv := h.1

theorem SquiggleSet.nontrivial (h : SquiggleSet o fv Γ) : Γ.Nontrivial :=
  (squiggleSet_iff_nontrivial.1 h).2.2

/-- A member of a set antecedent other than the ordinary value is an individual antecedent
([rooth-1992] fn. 9). -/
theorem SquiggleSet.squiggleInd (h : SquiggleSet o fv Γ) (hγ : γ ∈ Γ) (hne : γ ≠ o) :
    SquiggleInd o fv γ :=
  ⟨h.1 hγ, hne⟩

/-- The individual case is the set case at the pair of the ordinary value and the antecedent,
when the focus semantic value contains the ordinary value ([rooth-1992] p. 90). -/
theorem squiggleSet_pair_iff : SquiggleSet o fv {o, γ} ↔ o ∈ fv ∧ SquiggleInd o fv γ := by
  simp [SquiggleSet, SquiggleInd, Set.pair_subset_iff, and_assoc]

theorem not_squiggleSet_of_subsingleton (h : fv.Subsingleton) : ¬ SquiggleSet o fv Γ :=
  fun hs ↦ Set.not_nontrivial_iff.2 (h.anti hs.subset) hs.nontrivial

theorem not_squiggleInd_of_subsingleton (h : fv.Subsingleton) (ho : o ∈ fv) :
    ¬ SquiggleInd o fv γ :=
  fun hs ↦ hs.2 (h hs.1 ho)

end Squiggle

/-! ### Antecedents and their uses -/

/-- The pragmatic uses of a focus, by the context that controls it
([hartmann-zimmermann-2007] §1.2). -/
inductive Use where
  /-- Answering a question. -/
  | newInfo
  /-- Correcting a prior assertion. -/
  | corrective
  /-- Selecting from explicitly offered alternatives. -/
  | selective
  /-- Contrasting with a phrase of the same category and word field. -/
  | contrastive
  deriving DecidableEq, Repr, Inhabited

/-- The discourse object to which the variable of ~ resolves, by the shape of the context that
supplies it. -/
inductive Antecedent (α : Type*) where
  /-- A question, whose ordinary semantic value `q` is the set of its answers. -/
  | question (q : Set α)
  /-- Explicitly offered alternatives, as in 'coffee or tea?'. -/
  | offer (alts : Set α)
  /-- A prior assertion `p` that the focus corrects. -/
  | assertion (p : α)
  /-- The ordinary value `γ` of a phrase the focus contrasts with ([rooth-1992] (14)). -/
  | phrase (γ : α)

namespace Antecedent

variable {c : Antecedent α} {o : α} {fv fv' : Set α}

/-- The set an antecedent requires to lie inside the focus semantic value: a set antecedent
itself, or the unit set of an individual one ([rooth-1992] (27)). -/
def contrastSet : Antecedent α → Set α
  | question q => q
  | offer alts => alts
  | assertion p => {p}
  | phrase γ => {γ}

/-- The pragmatic use of a focus that an antecedent controls. -/
def use : Antecedent α → Use
  | question _ => .newInfo
  | offer _ => .selective
  | assertion _ => .corrective
  | phrase _ => .contrastive

@[simp] theorem contrastSet_question (q : Set α) : (question q).contrastSet = q := rfl
@[simp] theorem contrastSet_offer (alts : Set α) : (offer alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_assertion (p : α) : (assertion p).contrastSet = {p} := rfl
@[simp] theorem contrastSet_phrase (γ : α) : (phrase γ).contrastSet = {γ} := rfl

@[simp] theorem use_question (q : Set α) : (question q).use = .newInfo := rfl
@[simp] theorem use_offer (alts : Set α) : (offer alts).use = .selective := rfl
@[simp] theorem use_assertion (p : α) : (assertion p).use = .corrective := rfl
@[simp] theorem use_phrase (γ : α) : (phrase γ).use = .contrastive := rfl

/-- An antecedent admits a focus semantic value containing its contrast set, the first version of
the focus interpretation principle ([rooth-1992] (27)). -/
def Admits (c : Antecedent α) (fv : Set α) : Prop :=
  c.contrastSet ⊆ fv

theorem Admits.mono (hc : c.Admits fv) (h : fv ⊆ fv') : c.Admits fv' := hc.trans h

theorem admits_inter_iff : c.Admits (fv ∩ fv') ↔ c.Admits fv ∧ c.Admits fv' :=
  Set.subset_inter_iff

/-- An antecedent resolves the squiggle on a phrase with ordinary value `o` and focus semantic
value `fv` when it meets the case of the presupposition its shape takes: the set case for a
question or an offer, the individual case for an assertion or a contrasting phrase
([rooth-1992] (40)). -/
def Resolves : Antecedent α → α → Set α → Prop
  | question q, o, fv => SquiggleSet o fv q
  | offer alts, o, fv => SquiggleSet o fv alts
  | assertion p, o, fv => SquiggleInd o fv p
  | phrase γ, o, fv => SquiggleInd o fv γ

theorem Resolves.admits (h : c.Resolves o fv) : c.Admits fv := by
  cases c with
  | question _ | offer _ => exact h.1
  | assertion _ | phrase _ => exact Set.singleton_subset_iff.2 h.1

/-- The argument of ~ must contain a focus, since the focus semantic value of a focus-free phrase
is the unit set of its ordinary value ([rooth-1992] pp. 111–112). -/
theorem not_resolves_unfeatured (c : Antecedent α) (x : α) :
    ¬ c.Resolves (WithAlternatives.unfeatured x).ordinary
      (WithAlternatives.unfeatured x).alternatives := by
  cases c with
  | question _ | offer _ => exact not_squiggleSet_of_subsingleton Set.subsingleton_singleton
  | assertion _ | phrase _ => exact not_squiggleInd_of_subsingleton Set.subsingleton_singleton rfl

theorem admits_factorsThrough_contrastSet (fv : Set α) :
    Function.FactorsThrough (Admits · fv) (contrastSet (α := α)) :=
  fun _ _ h ↦ congrArg (· ⊆ fv) h

/-- The four foci "do not instantiate different semantic types of focus, but only different
pragmatic uses of focus" ([hartmann-zimmermann-2007] §1.2). -/
theorem use_not_factorsThrough_contrastSet :
    ¬ Function.FactorsThrough (use (α := α)) contrastSet :=
  fun h ↦ absurd (h (a := question ∅) (b := offer ∅) rfl) nofun

end Antecedent

end Focus
