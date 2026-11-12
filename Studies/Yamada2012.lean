/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.Commitment.Proposition

/-!
# Yamada (2012): Dynamic Logic of Propositional Commitments

Yamada's logic has, for each agent, a commitment incurred by asserting and a weaker one incurred
by conceding, and modalities for the acts of asserting and conceding, which cut the accessibility
arrows of the agent that lead to worlds where the content fails. The act of asserting is the
performative update `Commitment.perform` on both of the agent's relations. After an assertion [the
asserter is committed to what the content implied](##Yamada2012.realize_afterAssert_cmt_self),
so every formula has [an equivalent without act modalities](##Yamada2012.realize_translate). An
assertion [commits its author to its content](##Yamada2012.realize_afterAssert_cmt_of_iFree) when
the content does not mention the author's own commitments, and
[need not otherwise](##Yamada2012.exists_not_mem_realize_afterAssert_cmt), while
[incompatible assertions by two agents](##Yamada2012.realize_afterAssert_afterAssert_neg) leave
each committed to their own.

## Implementation notes

A model's worlds are not required to be nonempty. The translation is defined by recursion on the
formula under the act modality, which the chapter's clause for nested acts unfolds to. The model
in which an assertion fails to commit its author is constructed here; the chapter states the
restriction and cites the phenomenon.

## TODO

* The proof systems and the two completeness theorems.
* Acts of withdrawing, whose truth definition is relative to the history of acts, and the
  initial-stage model for scorekeeping.

## References

* [yamada-2012]
-/

@[expose] public section

namespace Yamada2012

open Commitment

/-- A commitment is incurred by asserting or by conceding. -/
inductive Kind
  | asserted
  | conceded
  deriving DecidableEq

/-- The formulas of the dynamified logic, with atoms `P` and agents `I`: the commitment
modalities `[a-cmt]ᵢ` and `[c-cmt]ᵢ` and the act modalities `[assertᵢ χ]` and `[concedeᵢ χ]`. -/
inductive Formula (P I : Type*)
  | top
  | atom (p : P)
  | neg (φ : Formula P I)
  | and (φ ψ : Formula P I)
  | cmt (k : Kind) (i : I) (φ : Formula P I)
  | afterAssert (i : I) (χ φ : Formula P I)
  | afterConcede (i : I) (χ φ : Formula P I)

/-- A model has an accessibility for each agent and kind of commitment, the one for conceding
inside the one for asserting, so that an asserted commitment is a conceded one. -/
structure Model (W P I : Type*) where
  /-- The accessibility of `i`'s commitments of each kind. -/
  acc : I × Kind → SetRel W W
  conceded_subset : ∀ i, acc (i, .conceded) ⊆ acc (i, .asserted)
  /-- The worlds where an atom holds. -/
  val : P → Set W

variable {W P I : Type*}

namespace Model

variable (M : Model W P I) (i j : I) (k : Kind) (X Y : Set W)

/-- The model after `i` asserts a content true at `X`: both of `i`'s relations lose the arrows
that leave `X`. -/
def assert : Model W P I where
  acc := perform (perform M.acc (i, .asserted) X) (i, .conceded) X
  conceded_subset j _ hp :=
    ⟨⟨M.conceded_subset j hp.1.1, fun e ↦ hp.2 (congrArg (fun q ↦ (q.1, Kind.conceded)) e)⟩,
      fun e ↦ nomatch (Prod.ext_iff.1 e).2⟩
  val := M.val

/-- The model after `i` concedes a content true at `X`: the relation of `i`'s conceded
commitments loses the arrows that leave `X`. -/
def concede : Model W P I where
  acc := perform M.acc (i, .conceded) X
  conceded_subset j _ hp := ⟨M.conceded_subset j hp.1, fun e ↦ nomatch (Prod.ext_iff.1 e).2⟩
  val := M.val

variable {M i j k X Y}

theorem committed_assert_self :
    committed (M.assert i X).acc (i, k) Y = committed M.acc (i, k) (Xᶜ ∪ Y) := by
  cases k
  · rw [assert, committed_perform_of_ne (by simp), committed_perform]
  · rw [assert, committed_perform, committed_perform_of_ne (by simp)]

theorem committed_assert_of_ne (h : j ≠ i) :
    committed (M.assert i X).acc (j, k) Y = committed M.acc (j, k) Y := by
  rw [assert, committed_perform_of_ne (by simp [h]), committed_perform_of_ne (by simp [h])]

theorem committed_concede_self :
    committed (M.concede i X).acc (i, .conceded) Y = committed M.acc (i, .conceded) (Xᶜ ∪ Y) :=
  committed_perform

theorem committed_concede_of_ne (h : (j, k) ≠ (i, Kind.conceded)) :
    committed (M.concede i X).acc (j, k) Y = committed M.acc (j, k) Y :=
  committed_perform_of_ne h

end Model

namespace Formula

/-- The worlds of a model where a formula holds. A commitment holds where every accessible world
satisfies its content, and an act modality evaluates its scope in the updated model. -/
def realize : Formula P I → Model W P I → Set W
  | top, _ => Set.univ
  | atom p, M => M.val p
  | neg φ, M => (φ.realize M)ᶜ
  | and φ ψ, M => φ.realize M ∩ ψ.realize M
  | cmt k i φ, M => committed M.acc (i, k) (φ.realize M)
  | afterAssert i χ φ, M => φ.realize (M.assert i (χ.realize M))
  | afterConcede i χ φ, M => φ.realize (M.concede i (χ.realize M))

/-- Material implication. -/
def imp (φ ψ : Formula P I) : Formula P I := neg (and φ (neg ψ))

/-- A formula without act modalities, a formula of the static logic. -/
def Static : Formula P I → Prop
  | top | atom _ => True
  | neg φ => φ.Static
  | and φ ψ => φ.Static ∧ ψ.Static
  | cmt _ _ φ => φ.Static
  | afterAssert .. | afterConcede .. => False

/-- A static formula is `i`-free when neither of `i`'s commitment modalities occurs in it. -/
def IFree (i : I) : Formula P I → Prop
  | top | atom _ => True
  | neg φ => φ.IFree i
  | and φ ψ => φ.IFree i ∧ ψ.IFree i
  | cmt _ j φ => j ≠ i ∧ φ.IFree i
  | afterAssert .. | afterConcede .. => False

end Formula

open Formula Model

variable {M : Model W P I} {i j : I} {k : Kind} {χ φ ψ : Formula P I}

@[simp] theorem realize_imp : (φ.imp ψ).realize M = (φ.realize M)ᶜ ∪ ψ.realize M := by
  simp [imp, realize, Set.compl_inter]

/-! ### The reduction axioms -/

/-- After `i` asserts `χ`, `i` is committed to `ψ` where `i` was committed to `χ` implying that
`ψ` holds after the assertion, for either kind of commitment: axioms (A6) and (A8). -/
theorem realize_afterAssert_cmt_self :
    (afterAssert i χ (cmt k i ψ)).realize M =
      (cmt k i (χ.imp (afterAssert i χ ψ))).realize M := by
  simp only [realize, realize_imp, committed_assert_self]

-- (A5), (A7)
theorem realize_afterAssert_cmt_of_ne (h : j ≠ i) :
    (afterAssert i χ (cmt k j ψ)).realize M = (cmt k j (afterAssert i χ ψ)).realize M := by
  simp only [realize, committed_assert_of_ne h]

-- (C7)
theorem realize_afterConcede_cmt_self :
    (afterConcede i χ (cmt .conceded i ψ)).realize M =
      (cmt .conceded i (χ.imp (afterConcede i χ ψ))).realize M := by
  simp only [realize, realize_imp, committed_concede_self]

-- (C5), (C6)
theorem realize_afterConcede_cmt_of_ne (h : (j, k) ≠ (i, Kind.conceded)) :
    (afterConcede i χ (cmt k j ψ)).realize M = (cmt k j (afterConcede i χ ψ)).realize M := by
  simp only [realize, committed_concede_of_ne h]

/-! ### Formulas free of the agent's commitments -/

variable {X : Set W}

-- Corollary 2
theorem realize_assert_of_iFree (h : φ.IFree i) : φ.realize (M.assert i X) = φ.realize M := by
  induction φ with
  | top | atom => rfl
  | neg φ ih => simp only [realize, ih h]
  | and φ ψ ihφ ihψ => simp only [realize, ihφ h.1, ihψ h.2]
  | cmt k j φ ih => simp only [realize, ih h.2, committed_assert_of_ne h.1]
  | afterAssert | afterConcede => exact h.elim

-- Corollary 2
theorem realize_concede_of_iFree (h : φ.IFree i) : φ.realize (M.concede i X) = φ.realize M := by
  induction φ with
  | top | atom => rfl
  | neg φ ih => simp only [realize, ih h]
  | and φ ψ ihφ ihψ => simp only [realize, ihφ h.1, ihψ h.2]
  | cmt k j φ ih =>
    simp only [realize, ih h.2, committed_concede_of_ne fun e ↦ h.1 (Prod.ext_iff.1 e).1]
  | afterAssert | afterConcede => exact h.elim

/-- Asserting a formula that does not mention one's own commitments commits one to it, in both
kinds (Proposition 2). -/
theorem realize_afterAssert_cmt_of_iFree (h : φ.IFree i) :
    (afterAssert i φ (cmt k i φ)).realize M = Set.univ := by
  simp only [realize, committed_assert_self, realize_assert_of_iFree h, Set.compl_union_self,
    committed_univ]

-- Proposition 2
theorem realize_afterConcede_cmt_of_iFree (h : φ.IFree i) :
    (afterConcede i φ (cmt .conceded i φ)).realize M = Set.univ := by
  simp only [realize, committed_concede_self, realize_concede_of_iFree h, Set.compl_union_self,
    committed_univ]

/-- When `i` asserts `φ` and then another agent `j` asserts its negation, `i` is committed to
`φ` and `j` to its negation, with no contradiction. -/
theorem realize_afterAssert_afterAssert_neg (hij : i ≠ j) (hi : φ.IFree i) (hj : φ.IFree j) :
    (afterAssert i φ (afterAssert j (neg φ)
      (and (cmt .asserted i φ) (cmt .asserted j (neg φ))))).realize M = Set.univ := by
  simp only [realize, committed_assert_self, committed_assert_of_ne hij,
    realize_assert_of_iFree hi, realize_assert_of_iFree hj, compl_compl, Set.compl_union_self,
    Set.union_compl_self, committed_univ, Set.inter_self]

/-- An assertion need not commit its author to its content: asserting "`p`, and I am not
committed to `p`" leaves the author uncommitted to it. -/
theorem exists_not_mem_realize_afterAssert_cmt :
    ∃ (M : Model Bool Unit Unit) (φ : Formula Unit Unit),
      true ∉ (afterAssert () φ (cmt .asserted () φ)).realize M := by
  let M : Model Bool Unit Unit := ⟨fun _ ↦ Set.univ, fun _ ↦ subset_rfl, fun _ ↦ {true}⟩
  let φ : Formula Unit Unit := and (atom ()) (neg (cmt .asserted () (atom ())))
  have hX : φ.realize M = {true} :=
    Set.ext fun w ↦ ⟨And.left, fun hw ↦ ⟨hw, fun hc ↦ Bool.false_ne_true (@hc false trivial)⟩⟩
  refine ⟨M, φ, fun h ↦ ?_⟩
  have h₁ : true ∈ committed M.acc ((), .asserted)
      ((φ.realize M)ᶜ ∪ φ.realize (M.assert () (φ.realize M))) := committed_assert_self ▸ h
  rw [hX] at h₁
  have h₂ : true ∈ φ.realize (M.assert () {true}) :=
    (@h₁ true trivial).resolve_left fun hn ↦ hn rfl
  have h₃ : true ∈ committed (M.assert () {true}).acc ((), .asserted) {true} := by
    rw [committed_assert_self, Set.compl_union_self, committed_univ]
    trivial
  exact h₂.2 h₃

/-! ### The translation into the static logic -/

variable [DecidableEq I]

/-- The static equivalent of `[assertᵢ χ]ψ` for a static `ψ`, pushing the act through `ψ` by
the reduction axioms. -/
def reduceAssert (i : I) (χ : Formula P I) : Formula P I → Formula P I
  | .neg ψ => .neg (reduceAssert i χ ψ)
  | .and ψ ψ' => .and (reduceAssert i χ ψ) (reduceAssert i χ ψ')
  | .cmt k j ψ =>
    if j = i then .cmt k j (χ.imp (reduceAssert i χ ψ)) else .cmt k j (reduceAssert i χ ψ)
  | ψ => ψ

/-- The static equivalent of `[concedeᵢ χ]ψ` for a static `ψ`. -/
def reduceConcede (i : I) (χ : Formula P I) : Formula P I → Formula P I
  | .neg ψ => .neg (reduceConcede i χ ψ)
  | .and ψ ψ' => .and (reduceConcede i χ ψ) (reduceConcede i χ ψ')
  | .cmt k j ψ =>
    if (j, k) = (i, Kind.conceded) then .cmt k j (χ.imp (reduceConcede i χ ψ))
    else .cmt k j (reduceConcede i χ ψ)
  | ψ => ψ

/-- The translation of a formula into the static logic (Definition 8). -/
def translate : Formula P I → Formula P I
  | .top => .top
  | .atom p => .atom p
  | .neg φ => .neg (translate φ)
  | .and φ ψ => .and (translate φ) (translate ψ)
  | .cmt k i φ => .cmt k i (translate φ)
  | .afterAssert i χ φ => reduceAssert i (translate χ) (translate φ)
  | .afterConcede i χ φ => reduceConcede i (translate χ) (translate φ)

theorem realize_reduceAssert (hψ : ψ.Static) :
    (reduceAssert i χ ψ).realize M = ψ.realize (M.assert i (χ.realize M)) := by
  induction ψ with
  | top | atom => rfl
  | neg ψ ih => simp only [reduceAssert, realize, ih hψ]
  | and ψ ψ' ih ih' => simp only [reduceAssert, realize, ih hψ.1, ih' hψ.2]
  | cmt k j ψ ih =>
    rw [reduceAssert]
    split_ifs with h
    · subst h
      simp only [realize, realize_imp, ih hψ, committed_assert_self]
    · simp only [realize, ih hψ, committed_assert_of_ne h]
  | afterAssert | afterConcede => exact hψ.elim

theorem realize_reduceConcede (hψ : ψ.Static) :
    (reduceConcede i χ ψ).realize M = ψ.realize (M.concede i (χ.realize M)) := by
  induction ψ with
  | top | atom => rfl
  | neg ψ ih => simp only [reduceConcede, realize, ih hψ]
  | and ψ ψ' ih ih' => simp only [reduceConcede, realize, ih hψ.1, ih' hψ.2]
  | cmt k j ψ ih =>
    rw [reduceConcede]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp only [realize, realize_imp, ih hψ, committed_concede_self]
    · simp only [realize, ih hψ, committed_concede_of_ne h]
  | afterAssert | afterConcede => exact hψ.elim

theorem static_reduceAssert (hχ : χ.Static) (hψ : ψ.Static) : (reduceAssert i χ ψ).Static := by
  induction ψ with
  | top | atom => trivial
  | neg ψ ih => exact ih hψ
  | and ψ ψ' ih ih' => exact ⟨ih hψ.1, ih' hψ.2⟩
  | cmt k j ψ ih =>
    rw [reduceAssert]
    split_ifs
    exacts [⟨hχ, ih hψ⟩, ih hψ]
  | afterAssert | afterConcede => exact hψ.elim

theorem static_reduceConcede (hχ : χ.Static) (hψ : ψ.Static) : (reduceConcede i χ ψ).Static := by
  induction ψ with
  | top | atom => trivial
  | neg ψ ih => exact ih hψ
  | and ψ ψ' ih ih' => exact ⟨ih hψ.1, ih' hψ.2⟩
  | cmt k j ψ ih =>
    rw [reduceConcede]
    split_ifs
    exacts [⟨hχ, ih hψ⟩, ih hψ]
  | afterAssert | afterConcede => exact hψ.elim

theorem static_translate (φ : Formula P I) : (translate φ).Static := by
  induction φ with
  | top | atom => trivial
  | neg φ ih => exact ih
  | and φ ψ ih ih' => exact ⟨ih, ih'⟩
  | cmt k i φ ih => exact ih
  | afterAssert i χ φ ihχ ihφ => exact static_reduceAssert ihχ ihφ
  | afterConcede i χ φ ihχ ihφ => exact static_reduceConcede ihχ ihφ

/-- Every formula holds at the same worlds as its translation, which has no act modalities: the
dynamified logic is no more expressive than the static one. -/
theorem realize_translate (φ : Formula P I) (M : Model W P I) :
    (translate φ).realize M = φ.realize M := by
  induction φ generalizing M with
  | top | atom => rfl
  | neg φ ih => simp only [translate, realize, ih]
  | and φ ψ ih ih' => simp only [translate, realize, ih, ih']
  | cmt k i φ ih => simp only [translate, realize, ih]
  | afterAssert i χ φ ihχ ihφ =>
    rw [translate, realize_reduceAssert (static_translate φ), ihχ, ihφ, realize]
  | afterConcede i χ φ ihχ ihφ =>
    rw [translate, realize_reduceConcede (static_translate φ), ihχ, ihφ, realize]

end Yamada2012
