module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Truthmaker.Bilateral

/-!
# Bilateral state-based modal logic

This file defines Aloni's bilateral state-based modal logic (BSML). A formula is evaluated at
teams, finite sets of worlds of a Kripke model, and is both supported (`⊨`) and anti-supported
(`⫤`) by teams, so its meaning in a model is a bilateral proposition, the pair of its supporting
and its anti-supporting teams. Negation swaps the two. The non-emptiness atom `NE`, supported
exactly by the non-empty teams, is the source of the free-choice effects.

## Main definitions

* `BSML.Formula`: atoms, `NE`, `¬`, `∧`, split `∨` and `◇`; `□` is the abbreviation `Formula.nec`.
* `BSML.Formula.den`: the meaning of a formula in a model.
* `BSML.support`, `BSML.antiSupport`: support and anti-support.
* `BSML.Formula.NEFree`, `BSML.Formula.Positive`: the `NE`-free and the negation-free fragments.
* `BSML.Consequence` (`Γ ⊨ φ`), `BSML.Equivalent`, `BSML.StronglyEquivalent`: consequence and
  equivalence over pointed team models.

## Implementation notes

A meaning is a `Truthmaker.BilProp` of teams and negation is its involution `-`, so double
negation and the dualities of `∧` with `∨` and of `◇` with `□` hold by `rfl`, and two formulas
are strongly equivalent exactly when their meanings are equal (`stronglyEquivalent_iff`). Each
clause applies an operation of `Team/Operations.lean`, so the closure properties in
`Properties.lean` follow from the closure lemmas of each connective.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
-/

@[expose] public section

open scoped SetFamily

namespace BSML

open ModalLogic (KripkeModel PointedTeam)
open Truthmaker (BilProp)

/-! ### Formulas -/

/-- The formulas of BSML over an atom type are built from atoms and `NE` by `¬`, `∧`, split `∨`
and `◇` ([aloni-2022] Definition 1). -/
inductive Formula (Atom : Type*) where
  /-- An atomic proposition. -/
  | atom : Atom → Formula Atom
  /-- The non-emptiness atom, supported by the non-empty teams. -/
  | ne : Formula Atom
  /-- Negation, which swaps support and anti-support. -/
  | neg : Formula Atom → Formula Atom
  /-- Conjunction. -/
  | conj : Formula Atom → Formula Atom → Formula Atom
  /-- Split disjunction. -/
  | disj : Formula Atom → Formula Atom → Formula Atom
  /-- The possibility modality. -/
  | poss : Formula Atom → Formula Atom
  deriving Repr

variable {Atom : Type*}

/-- Necessity `□φ` abbreviates `¬◇¬φ`. A team supports it when the successors of each of its
worlds support `φ`, and anti-supports it when each world has a non-empty set of successors
anti-supporting `φ`. -/
def Formula.nec (φ : Formula Atom) : Formula Atom :=
  .neg (.poss (.neg φ))

/-! ### Syntactic fragments -/

/-- `Formula.NEFree φ` holds when `φ` contains no `NE` atom. On this fragment, support at a
singleton team is classical modal truth (`BSML/Classical.lean`). -/
def Formula.NEFree : Formula Atom → Prop
  | .atom _ => True
  | .ne => False
  | .neg φ => φ.NEFree
  | .conj φ ψ => φ.NEFree ∧ ψ.NEFree
  | .disj φ ψ => φ.NEFree ∧ ψ.NEFree
  | .poss φ => φ.NEFree

instance instDecidableNEFree : (φ : Formula Atom) → Decidable φ.NEFree
  | .atom _ => .isTrue trivial
  | .ne => .isFalse id
  | .neg φ => instDecidableNEFree φ
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)
  | .disj φ ψ => @instDecidableAnd _ _ (instDecidableNEFree φ) (instDecidableNEFree ψ)
  | .poss φ => instDecidableNEFree φ

/-- `Formula.Positive φ` holds when `φ` contains no negation, and so no `□`. -/
def Formula.Positive : Formula Atom → Prop
  | .atom _ => True
  | .ne => True
  | .neg _ => False
  | .conj φ ψ => φ.Positive ∧ ψ.Positive
  | .disj φ ψ => φ.Positive ∧ ψ.Positive
  | .poss φ => φ.Positive

instance instDecidablePositive : (φ : Formula Atom) → Decidable φ.Positive
  | .atom _ => .isTrue trivial
  | .ne => .isTrue trivial
  | .neg _ => .isFalse id
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidablePositive φ) (instDecidablePositive ψ)
  | .disj φ ψ => @instDecidableAnd _ _ (instDecidablePositive φ) (instDecidablePositive ψ)
  | .poss φ => instDecidablePositive φ

/-- The modal depth of a formula is the greatest number of nested `◇`s in it. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .ne => 0
  | .neg φ => φ.modalDepth
  | .conj φ ψ | .disj φ ψ => max φ.modalDepth ψ.modalDepth
  | .poss φ => φ.modalDepth + 1

/-! ### Contradictions -/

/-- The weak contradiction `⊥ := p ∧ ¬p` for a fixed atom `p`, the default one. Its meaning is
that of the primitive `⊥` of [aloni-anttila-yang-2024] (`Formula.den_falsum`). -/
def Formula.falsum [Inhabited Atom] : Formula Atom :=
  .conj (.atom default) (.neg (.atom default))

/-- The strong contradiction `⊥⊥ := ⊥ ∧ NE` of [aloni-anttila-yang-2024]. -/
def Formula.strongFalsum [Inhabited Atom] : Formula Atom :=
  .conj .falsum .ne

@[simp] theorem Formula.neFree_falsum [Inhabited Atom] : (Formula.falsum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-! ### Meaning, support and anti-support -/

variable {W : Type*} [DecidableEq W]

/-- The meaning of a formula in a model is the bilateral proposition whose verifiers are the
teams that support it and whose falsifiers are the teams that anti-support it
([aloni-2022] Definition 2). The split clauses are the pointwise sups `⊻` of teams. -/
def Formula.den (M : KripkeModel W Atom) : Formula Atom → BilProp (Finset W)
  | .atom p => ⟨Team.flat (M.val p), Team.flat fun w ↦ ¬ M.val p w⟩
  | .ne => ⟨Team.ne, {∅}⟩
  | .neg φ => -φ.den M
  | .conj φ ψ => ⟨(φ.den M).ver ∩ (ψ.den M).ver, (φ.den M).fal ⊻ (ψ.den M).fal⟩
  | .disj φ ψ => ⟨(φ.den M).ver ⊻ (ψ.den M).ver, (φ.den M).fal ∩ (ψ.den M).fal⟩
  | .poss φ => ⟨Team.poss M.access (φ.den M).ver, Team.nec M.access (φ.den M).fal⟩

/-- A team supports `φ`, `M, t ⊨ φ`, when it is a verifier of the meaning of `φ`. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).ver

/-- A team anti-supports `φ`, `M, t ⫤ φ`, when it is a falsifier of the meaning of `φ`. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).fal

variable (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W)

@[simp] theorem Formula.den_neg : φ.neg.den M = -φ.den M := rfl

@[simp] lemma support_neg : support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg : antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_conj : support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_disj :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

lemma empty_supports_atom (p : Atom) : support M (.atom p) ∅ :=
  Team.empty_mem_flat _

/-- The weak contradiction is supported only by the empty team and anti-supported by every
team, the meaning of the primitive `⊥` of [aloni-anttila-yang-2024]. -/
theorem Formula.den_falsum [Inhabited Atom] :
    (Formula.falsum : Formula Atom).den M = ⟨{∅}, .univ⟩ := by
  refine BilProp.ext (Set.ext fun t ↦ ⟨fun ⟨h₁, h₂⟩ ↦ ?_, ?_⟩) ?_
  · exact Finset.eq_empty_iff_forall_notMem.mpr fun w hw ↦ h₂ w hw (h₁ w hw)
  · rintro rfl; exact ⟨Team.empty_mem_flat _, Team.empty_mem_flat _⟩
  · exact Set.eq_univ_of_forall fun t ↦ Team.mem_flat_sups_flat.mpr fun w _ ↦ (em' _)

/-- The strong contradiction is supported by no team and anti-supported by every team. -/
theorem Formula.den_strongFalsum [Inhabited Atom] :
    (Formula.strongFalsum : Formula Atom).den M = ⟨∅, .univ⟩ := by
  refine BilProp.ext (Set.eq_empty_of_forall_notMem fun t ⟨h, hne⟩ ↦ ?_) ?_
  · rw [Formula.den_falsum] at h
    exact hne.ne_empty h
  · refine Set.eq_univ_of_forall fun t ↦ ⟨t, ?_, ∅, rfl, Finset.union_empty t⟩
    rw [Formula.den_falsum]; trivial

@[simp] theorem support_falsum [Inhabited Atom] : support M .falsum t ↔ t = ∅ := by
  rw [support, Formula.den_falsum]; rfl

theorem not_support_strongFalsum [Inhabited Atom] : ¬ support M .strongFalsum t := by
  rw [support, Formula.den_strongFalsum]; exact id

/-! ### Consequence and equivalence -/

/-- `Γ ⊨ φ`: every pointed team model whose team supports each formula of `Γ` supports `φ`
([aloni-2022] Definition 3, with sets of premises as in [aloni-anttila-yang-2024]). The
models range over `Type`; by soundness and completeness the universe does not matter for finite
premise sets (`BSML.support_of_consequence`). -/
def Consequence (Γ : Set (Formula Atom)) (φ : Formula Atom) : Prop :=
  ∀ p : PointedTeam.{0} Atom, (∀ γ ∈ Γ, support p.model γ p.team) → support p.model φ p.team

@[inherit_doc] scoped infix:50 " ⊨ " => Consequence

variable {φ ψ}

@[simp] theorem consequence_singleton_iff :
    {φ} ⊨ ψ ↔ ∀ p : PointedTeam.{0} Atom, support p.model φ p.team → support p.model ψ p.team :=
  forall_congr' fun _ ↦ by simp

/-- Two formulas are equivalent, `φ ≡ ψ`, when each is a consequence of the other, that is, when
they have the same support. -/
def Equivalent (φ ψ : Formula Atom) : Prop :=
  ∀ p : PointedTeam.{0} Atom, support p.model φ p.team ↔ support p.model ψ p.team

theorem equivalent_iff : Equivalent φ ψ ↔ {φ} ⊨ ψ ∧ {ψ} ⊨ φ := by
  rw [consequence_singleton_iff, consequence_singleton_iff]
  exact ⟨fun h ↦ ⟨fun p ↦ (h p).1, fun p ↦ (h p).2⟩, fun h p ↦ ⟨h.1 p, h.2 p⟩⟩

/-- Two formulas are strongly equivalent, `φ ⊜ ψ`, when they and their negations are equivalent
[aloni-anttila-yang-2024], that is, when they have the same support and the same
anti-support. -/
def StronglyEquivalent (φ ψ : Formula Atom) : Prop :=
  Equivalent φ ψ ∧ Equivalent (.neg φ) (.neg ψ)

/-- Two formulas are strongly equivalent exactly when they have the same meaning in every
model. -/
theorem stronglyEquivalent_iff : StronglyEquivalent φ ψ ↔
    ∀ (W : Type) [DecidableEq W] (M : KripkeModel W Atom), φ.den M = ψ.den M where
  mp h W _ M := BilProp.ext (Set.ext fun t ↦ h.1 ⟨W, M, t⟩) (Set.ext fun t ↦ h.2 ⟨W, M, t⟩)
  mpr h := ⟨fun p ↦ .of_eq (congrArg (p.team ∈ ·.ver) (h p.World p.model)),
    fun p ↦ .of_eq (congrArg (p.team ∈ ·.fal) (h p.World p.model))⟩

/-! ### Decidability -/

/-- Support and anti-support are decidable on a finite model, by recursion on the formula. -/
def Formula.decidableMemDen [Fintype W] [DecidableRel M.val] :
    (φ : Formula Atom) → DecidablePred (· ∈ (φ.den M).ver) × DecidablePred (· ∈ (φ.den M).fal)
  | .atom p => (fun t ↦ inferInstanceAs (Decidable (t ∈ Team.flat (M.val p))),
      fun t ↦ inferInstanceAs (Decidable (t ∈ Team.flat fun w ↦ ¬ M.val p w)))
  | .ne => (fun t ↦ inferInstanceAs (Decidable t.Nonempty),
      fun t ↦ inferInstanceAs (Decidable (t = ∅)))
  | .neg φ => (φ.decidableMemDen).swap
  | .conj φ ψ =>
    letI := (φ.decidableMemDen).1; letI := (ψ.decidableMemDen).1
    letI := (φ.decidableMemDen).2; letI := (ψ.decidableMemDen).2
    (fun t ↦ inferInstanceAs (Decidable (t ∈ (φ.den M).ver ∩ (ψ.den M).ver)),
      fun t ↦ inferInstanceAs (Decidable (t ∈ (φ.den M).fal ⊻ (ψ.den M).fal)))
  | .disj φ ψ =>
    letI := (φ.decidableMemDen).1; letI := (ψ.decidableMemDen).1
    letI := (φ.decidableMemDen).2; letI := (ψ.decidableMemDen).2
    (fun t ↦ inferInstanceAs (Decidable (t ∈ (φ.den M).ver ⊻ (ψ.den M).ver)),
      fun t ↦ inferInstanceAs (Decidable (t ∈ (φ.den M).fal ∩ (ψ.den M).fal)))
  | .poss φ =>
    letI := (φ.decidableMemDen).1; letI := (φ.decidableMemDen).2
    (fun t ↦ inferInstanceAs (Decidable (t ∈ Team.poss M.access (φ.den M).ver)),
      fun t ↦ inferInstanceAs (Decidable (t ∈ Team.nec M.access (φ.den M).fal)))

instance [Fintype W] [DecidableRel M.val] : DecidablePred (· ∈ (φ.den M).ver) :=
  (φ.decidableMemDen M).1

instance [Fintype W] [DecidableRel M.val] : DecidablePred (· ∈ (φ.den M).fal) :=
  (φ.decidableMemDen M).2

end BSML
