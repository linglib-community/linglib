module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Order.Interval.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.Morph
public import Linglib.Discourse.Commitment.Table
public import Linglib.Logic.Natural.Soundness
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Readings of a conditional

This file defines the two readings of a conditional. A conditional is read as *hypothetical* when
its antecedent is supposed and left open, and as a *premise* conditional when the antecedent
echoes prior discourse and is treated as established, the distinction of Iatridou and Haegeman.
On the hypothetical reading *if p, q* denotes the conditional proposition of whatever operator
the theory supplies, and on the premise reading it asserts *q* with *p* presupposed, the *given
that* paraphrase. The two readings give the antecedent opposite entailment directions, the
source of their opposite polarity-item profiles: for a conditional over a domain that grows with
the antecedent, such as the material or the strict conditional, the hypothetical antecedent is
downward entailing and every other clause upward entailing, while over the closest
antecedent-worlds the antecedent is neither. Languages may lexicalize the split, as Japanese
*-ra* and German *falls* mark only hypothetical conditionals.

## Main definitions

* `Conditional.Reading`: the hypothetical and premise readings.
* `Conditional.Reading.denote`: the denotation of *if p, q* under a reading, a trivalent
  proposition.
* `Conditional.Reading.Felicitous`: the discourse condition of each reading on its antecedent.
* `Conditional.Reading.clauseSignature`: the projectivity signature of each clause under a
  reading, whose sign is `Conditional.Reading.clausePolarity`.
* `Conditional.Marker`: a conditional marker, its exponent with the readings it can mark.

## Main results

* `Conditional.Reading.soundFor_clauseSignature`: over a monotone domain the signatures are
  sound.
* `Conditional.Reading.exists_not_antitone_hypothetical_closestImp`: over the closest
  antecedent-worlds the hypothetical antecedent is not downward entailing.

## Implementation notes

The sources often attest a marker with one reading and say nothing about the other, so a
marker's readings are recorded as an interval of sets of readings: the readings it is attested
marking below, the readings it is not known to exclude above. A marker the sources describe
fully has a one-point interval.

## References

* [S. Iatridou, *Topics in Conditionals* (1991)][iatridou-1991]
* [L. Haegeman, *Conditional clauses: External and internal syntax* (2003)][haegeman-2003]
* [D. Lassiter, *Sorting Out Left-Nested Conditionals* (2025)][lassiter-2025]
-/

@[expose] public section

namespace Conditional

open NaturalLogic

/-- The readings of a conditional, on which the antecedent is supposed and left open or echoes
prior discourse and is treated as established. -/
inductive Reading
  | hypothetical
  | premise
  deriving DecidableEq, Fintype, Repr

/-- The two clauses of a conditional. -/
inductive Clause
  | antecedent
  | consequent
  deriving DecidableEq, Fintype, Repr

namespace Reading

@[simp] theorem «forall» {P : Reading → Prop} : (∀ ct, P ct) ↔ P .hypothetical ∧ P .premise :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ ct ↦ by cases ct <;> assumption⟩

@[simp] theorem «exists» {P : Reading → Prop} : (∃ ct, P ct) ↔ P .hypothetical ∨ P .premise :=
  ⟨fun ⟨ct, h⟩ ↦ by cases ct; exacts [.inl h, .inr h], fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩

section Denotation

variable {W : Type*} (cond : Set W → Set W → Set W) (p q : Set W)

open Classical in
/-- The denotation of *if p, q* under a reading, for a conditional operator `cond` on total
propositions. The hypothetical reading is `cond p q`, and the premise reading asserts `q` with
`p` presupposed. -/
noncomputable def denote : Reading → W → SignType
  | .hypothetical => fun w ↦ SignType.ofProp (w ∈ cond p q)
  | .premise => p.indicator fun w ↦ SignType.ofProp (w ∈ q)

variable {cond p q} {w : W}

@[simp] theorem denote_hypothetical_eq_one_iff :
    hypothetical.denote cond p q w = 1 ↔ w ∈ cond p q := by
  simp [denote]

@[simp] theorem denote_premise_eq_one_iff : premise.denote cond p q w = 1 ↔ w ∈ p ∧ w ∈ q := by
  simp [denote]

theorem denote_hypothetical_materialImp_eq_premise (hw : w ∈ p) :
    hypothetical.denote materialImp p q w = premise.denote materialImp p q w := by
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_ <;> simp [denote, hw, mem_materialImp]

end Denotation

/-! ### Discourse conditions

A hypothetical conditional leaves its antecedent open, and a premise conditional echoes it: some
participant is committed to the antecedent, or it is already common ground. -/

section Felicity

variable {A W : Type*} {K : Commitment.Table A W} {p : Set W}

/-- A reading is felicitous for the antecedent `p` in the commitment table `K` when `p` meets its
discourse condition ([iatridou-1991], [haegeman-2003]). A hypothetical conditional leaves `p`
undecided in the common ground, and a premise conditional needs `p` committed to by some
participant or already in the common ground. -/
def Felicitous (K : Commitment.Table A W) (p : Set W) : Reading → Prop
  | .hypothetical => ¬ (Question.polar p).DecidedBy K.commonGround
  | .premise => (∃ a, p ∈ K.discourseCommitments a) ∨ p ∈ K.commonGround

theorem felicitous_iff_of_mem_commonGround (h : p ∈ K.commonGround) {ct : Reading} :
    ct.Felicitous K p ↔ ct = .premise := by
  cases ct
  · exact iff_of_false (fun h' ↦ h' (Question.decidedBy_polar.2 (.inl h))) (by decide)
  · exact iff_of_true (.inr h) rfl

theorem felicitous_iff_of_not_decidedBy (h₁ : ∀ a, p ∉ K.discourseCommitments a)
    (h₂ : ¬ (Question.polar p).DecidedBy K.commonGround) {ct : Reading} :
    ct.Felicitous K p ↔ ct = .hypothetical := by
  cases ct
  · exact iff_of_true h₂ rfl
  · exact iff_of_false (fun h ↦ h.elim (fun ⟨a, ha⟩ ↦ h₁ a ha)
      fun hp ↦ h₂ (Question.decidedBy_polar.2 (.inl hp))) (by decide)

end Felicity

/-! ### Entailment directions

The clauses of a conditional over a domain of antecedent-worlds have the projectivity
signatures of natural logic: the hypothetical antecedent is antitone when the domain grows with
the antecedent, and every other clause is monotone. The material and the strict conditional
have such domains; the conditional of the closest antecedent-worlds does not, since antecedent
strengthening fails for it. -/

section Signature

variable {W : Type*} {D : W → Set W → Set W} (cond : Set W → Set W → Set W) (p q : Set W)

/-- The projectivity signature of a clause under a reading is antitone for the hypothetical
antecedent and monotone for every other clause. -/
def clauseSignature : Reading → Clause → Signature
  | .hypothetical, .antecedent => .anti
  | _, _ => .mono

/-- The entailment direction of a clause under a reading, the sign of its signature. -/
def clausePolarity (ct : Reading) (c : Clause) : SignType := (clauseSignature ct c).sign

/-- The function of a clause under a reading, the other clause held fixed, on truth sets. -/
def clauseMap (ct : Reading) : Clause → Set W → Set W
  | .antecedent => fun p' ↦ Trivalent.posExt (ct.denote cond p' q)
  | .consequent => fun q' ↦ Trivalent.posExt (ct.denote cond p q')

variable {cond p q}

theorem antitone_posExt_hypothetical (hD : ∀ w, Monotone (D w)) (q : Set W) :
    Antitone fun p ↦ Trivalent.posExt (hypothetical.denote (ofDomain D) p q) :=
  fun _ _ h _ hw ↦ denote_hypothetical_eq_one_iff.2
    (ofDomain_anti_left (fun i ↦ hD i h) (denote_hypothetical_eq_one_iff.1 hw))

theorem monotone_posExt_premise (cond : Set W → Set W → Set W) (q : Set W) :
    Monotone fun p ↦ Trivalent.posExt (premise.denote cond p q) :=
  fun _ _ h _ hw ↦ denote_premise_eq_one_iff.2 ((denote_premise_eq_one_iff.1 hw).imp_left (h ·))

theorem monotone_posExt_consequent (ct : Reading) (p : Set W) :
    Monotone fun q ↦ Trivalent.posExt (ct.denote (ofDomain D) p q) := by
  cases ct
  · exact fun _ _ h _ hw ↦
      denote_hypothetical_eq_one_iff.2 (ofDomain_mono_right h (denote_hypothetical_eq_one_iff.1 hw))
  · exact fun _ _ h _ hw ↦
      denote_premise_eq_one_iff.2 ((denote_premise_eq_one_iff.1 hw).imp_right (h ·))

/-- Over a domain that grows with the antecedent, each clause's signature is sound for the
clause's function. -/
theorem soundFor_clauseSignature (hD : ∀ w, Monotone (D w)) (p q : Set W) (ct : Reading)
    (c : Clause) : (clauseSignature ct c).SoundFor (clauseMap (ofDomain D) p q ct c) := by
  cases ct <;> cases c
  · exact soundFor_anti_iff.2 (antitone_posExt_hypothetical hD q)
  · exact soundFor_mono_iff.2 (monotone_posExt_consequent .hypothetical p)
  · exact soundFor_mono_iff.2 (monotone_posExt_premise _ q)
  · exact soundFor_mono_iff.2 (monotone_posExt_consequent .premise p)

/-- Over the closest antecedent-worlds the hypothetical antecedent is not antitone — with three
worlds ranked `0 < 1 < 2` from `0`, *if 1 or 2, then 1* holds at `0` while *if 2, then 1* does
not. -/
theorem exists_not_antitone_hypothetical_closestImp :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (q : Set (Fin 3)),
      ¬ Antitone fun p ↦ Trivalent.posExt (hypothetical.denote (closestImp ord) p q) := by
  let ord : Fin 3 → Preorder (Fin 3) := fun _ ↦ Preorder.lift fun v : Fin 3 ↦ (v : ℕ)
  refine ⟨ord, {1}, fun h ↦ ?_⟩
  have h1 : (0 : Fin 3) ∈ Trivalent.posExt (hypothetical.denote (closestImp ord) {1, 2} {1}) := by
    simp only [Trivalent.mem_posExt, denote_hypothetical_eq_one_iff]
    decide
  have h2 := h (show ({2} : Set (Fin 3)) ⊆ {1, 2} by simp) h1
  simp only [Trivalent.mem_posExt, denote_hypothetical_eq_one_iff] at h2
  revert h2; decide

end Signature

end Reading

/-- A conditional marker is an exponent together with the readings it can mark. Japanese *-ra* and
German *falls* mark only hypothetical conditionals, and *nara*, *wenn* and English *if* mark either
([lassiter-2025]). -/
structure Marker where
  /-- The exponent, in surface order. -/
  morphs : List Morphology.Morph
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The set of readings the marker can mark lies in this interval: it contains the readings the
  sources attest, and is contained in the readings they do not exclude. -/
  readings : NonemptyInterval (Finset Reading)
  deriving DecidableEq

/-- The surface form is the morphs' forms with their boundary notation. -/
def Marker.form (m : Marker) : String := Morphology.Morph.surface m.morphs

end Conditional
