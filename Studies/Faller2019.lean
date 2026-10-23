module

public import Linglib.Discourse.Commitment.Table

/-!
# Faller (2019): The Discourse Commitments of Illocutionary Reportatives

This file formalizes [faller-2019a]'s account of declaratives with the Cuzco Quechua reportative
*=si* in a modified discourse structure of [farkas-bruce-2010]. The puzzle is that the speaker
of a reportative declarative need not be committed to the reported proposition `φ` and may deny
it, yet `φ` is at issue and, unless it is denied, is taken to be proposed for the common ground.
The account splits Goffman's animator from the principal ([goffman-1979]): the operator PRESENT
of the declarative puts `φ` on the Table, commits the principal to its truth and the animator to
adequate evidence, with animator and principal identified by default (her (34)); the reportative
is an illocutionary modifier that adds `φ` to the animator's reportative commitments instead and
requires the principal to be distinct (her (35)). The structure `DS` is the Table of
`Discourse/Commitment/Table.lean` with a set of evidential commitments per participant for
each evidence type (her (24) and (25)), and `present` carries the evidence type of its
evidential as a parameter, so the plain declarative, the reportative and the best-possible-grounds
evidential differ only there and in the distinctness requirement, which is the paper's uniform
semantics of evidentials. `accept` is assertion acceptance (§4.3, Figure 2): the addressee
commits on the strength of the assertion, so with reportative evidence, `φ` leaves the Table
and enters the common ground.

The theorems are the paper's tableaux. Default assertion is Figure 1 (`assert_discourseCommitments`,
`assert_evid`) and its acceptance Figure 2 (`accept_discourseCommitments`, `accept_evid_addressee`,
  `mem_commonGround_accept`,
`accept_stack`). A reportative presentation is Figure 4: the principal is committed and the
animator has reportative evidence (`reportative_discourseCommitments_principal`,
  `reportative_evid`), and
Absence of Commitment is `reportative_discourseCommitments_animator`,
  the animator's truth commitments being
untouched, with `reportative_evid_adequate` the override of the adequate-evidence default. The
animator's denial (37) is Figure 5 (`denial_discourseCommitments`, `denial_evid`),
  and her acceptance under the
Collaborative Principle ([walker-1996]) Figure 6 (`figure6_discourseCommitments`,
  `figure6_discourseCommitments_eq_assert`). §6.3
draws the upshot with [gunlogson-2008]'s distinction: a truth commitment is `Dependent` when
backed by reportative evidence and `IsSource` when backed by adequate evidence or best possible
grounds, so the animator of Figure 6 is committed as after an assertion but only dependently
(`figure6_dependent`, `figure6_not_isSource`), where the asserter and the denier commit as
sources (`assert_isSource`, `denial_isSource`) and the English hearsay parenthetical commits
dependently (`present_reportative_dependent`).

## Implementation notes

* Goffman's author plays no part in the operators, which take the animator and the principal
  as participants; the paper treats the principal as a free variable that need not be a
  participant, and the acceptance of Figure 2 is the addressee's `Table.commit`, with the
  Gunlogson distinction carried by the evidential commitments rather than by the Table.
* The Collaborative Principle is pragmatic, so Figure 6 is the animator performing `accept` on
  her own reportative presentation rather than an operator of its own.
* The denial is the animator's best-possible-grounds presentation of `φᶜ`; the Table then
  carries `φᶜ` above `φ` where the paper's tableau shows `φ` replaced.
* Acceptance keeps `φ` in the truth commitments when it enters the common ground, as the
  paper's tableaux do, rather than stripping it as `Table.settle` does.

## References

* [faller-2019a]
* [farkas-bruce-2010]
* [goffman-1979]
* [gunlogson-2008]
* [walker-1996]
-/

@[expose] public section

namespace Faller2019

open Commitment Filter

/-- The evidence types whose commitments are tracked in distinct sets: adequate evidence in
Grice's sense, the default of assertion (24b); reportative evidence, which the reportative *=si*
contributes (25a); best possible grounds, which *=mi* contributes (25b). -/
inductive EvidenceType
  | adequate
  | reportative
  | bpg
  deriving DecidableEq, Repr

/-- A discourse structure: the Table, with its truth commitments and common ground, and the
evidential commitment sets `AeC`, `RepC` and `BpgC` of each participant. -/
structure DS (A W : Type*) extends Table A W where
  /-- The propositions `a` is committed to having evidence of type `e` for. -/
  evid : EvidenceType → A → Set (Set W)

namespace DS

variable {A W : Type*} [DecidableEq A] (K : DS A W) (φ : Set W) (a b p : A) (e : EvidenceType)

/-- The initial structure: the empty Table and no evidential commitments. -/
def empty : DS A W := { Table.empty with evid := λ _ _ => ∅ }

/-- Add `φ` to `a`'s evidential commitments of type `e`. -/
def addEvid : DS A W :=
  { K with evid := Function.update K.evid e (Function.update (K.evid e) a (insert φ (K.evid e a))) }

/-- (34) with an evidential: `φ` goes on the Table, the principal `p` commits to its truth and
the animator `a` to evidence of type `e`. -/
def present : DS A W := { K.addEvid φ a e with toTable := K.toTable.assert p φ }

/-- Default assertion: the animator is the principal and the evidence is adequate. -/
def assert : DS A W := K.present φ a a .adequate

/-- (35): the reportative presents with reportative evidence; that animator and principal are
distinct is its requirement, a hypothesis of the theorems below. -/
def reportative : DS A W := K.present φ a p .reportative

/-- Acceptance of `φ` by `b` (§4.3): `b` commits to `φ` on the strength of the assertion, so
with reportative evidence, `φ` leaves the Table and enters the common ground. -/
def accept : DS A W :=
  { K.addEvid φ b .reportative with
    toTable := { (K.toTable.commit b φ).pop with commonGround := K.commonGround ⊓ 𝓟 φ } }

/-- A dependent truth commitment ([gunlogson-2008]): `φ` in `TC_a ∩ RepC_a` (§6.3). -/
def Dependent : Prop := φ ∈ K.discourseCommitments a ∧ φ ∈ K.evid .reportative a

/-- A source commitment: `φ` in `TC_a ∩ AeC_a` or in `TC_a ∩ BpgC_a` (§6.3). -/
def IsSource : Prop := φ ∈ K.discourseCommitments a ∧ (φ ∈ K.evid .adequate a ∨ φ ∈ K.evid .bpg a)

@[simp] theorem addEvid_toTable : (K.addEvid φ a e).toTable = K.toTable := rfl

@[simp] theorem addEvid_evid_self : (K.addEvid φ a e).evid e a = insert φ (K.evid e a) := by
  simp [addEvid]

theorem addEvid_evid_of_ne {b : A} (h : b ≠ a) : (K.addEvid φ a e).evid e b = K.evid e b := by
  simp [addEvid, Function.update_of_ne h]

theorem addEvid_evid_of_ne_type {e' : EvidenceType} (h : e' ≠ e) :
    (K.addEvid φ a e).evid e' = K.evid e' := by
  simp [addEvid, Function.update_of_ne h]

@[simp] theorem present_toTable : (K.present φ a p e).toTable = K.toTable.assert p φ := rfl
@[simp] theorem present_evid : (K.present φ a p e).evid = (K.addEvid φ a e).evid := rfl
@[simp] theorem accept_toTable :
    (K.accept φ b).toTable =
      { (K.toTable.commit b φ).pop with commonGround := K.commonGround ⊓ 𝓟 φ } := rfl
@[simp] theorem accept_evid : (K.accept φ b).evid = (K.addEvid φ b .reportative).evid := rfl

/-! ### Figures 1 and 2: default assertion and its acceptance -/

theorem assert_discourseCommitments :
    φ ∈ (K.assert φ a).discourseCommitments a := Table.mem_discourseCommitments_assert _ _ _

theorem assert_evid : φ ∈ (K.assert φ a).evid .adequate a := by simp [assert]

theorem assert_stack : (K.assert φ a).stack = Question.ofSet φ :: K.stack := rfl

theorem assert_commonGround : (K.assert φ a).commonGround = K.commonGround := rfl

theorem accept_discourseCommitments :
    φ ∈ ((K.assert φ a).accept φ b).discourseCommitments b :=
  Table.mem_discourseCommitments_commit_self _ _ _

theorem accept_discourseCommitments_speaker :
    φ ∈ ((K.assert φ a).accept φ b).discourseCommitments a := by
  rcases eq_or_ne a b with rfl | h
  · exact accept_discourseCommitments K φ a a
  · rw [show ((K.assert φ a).accept φ b).discourseCommitments a =
      ((K.assert φ a).toTable.commit b φ).discourseCommitments a from rfl,
      Table.discourseCommitments_commit_of_ne h]
    exact assert_discourseCommitments K φ a

theorem accept_evid_addressee : φ ∈ ((K.assert φ a).accept φ b).evid .reportative b := by
  simp [accept]

theorem mem_commonGround_accept : φ ∈ ((K.assert φ a).accept φ b).commonGround :=
  mem_inf_of_right (mem_principal_self φ)

/-- Acceptance resolves the issue: the Table is as before the assertion. -/
theorem accept_stack : ((K.assert φ a).accept φ b).stack = K.stack := rfl

/-! ### Figure 4: reportative presentation and Absence of Commitment -/

theorem reportative_discourseCommitments_principal :
    φ ∈ (K.reportative φ a p).discourseCommitments p := Table.mem_discourseCommitments_assert _ _ _

theorem reportative_evid : φ ∈ (K.reportative φ a p).evid .reportative a := by simp [reportative]

theorem reportative_discourseCommitments_animator (h : a ≠ p) :
    (K.reportative φ a p).discourseCommitments a = K.discourseCommitments a :=
  Table.discourseCommitments_commit_of_ne h

/-- (35i) overrides (34iii): no adequate-evidence commitment is added. -/
theorem reportative_evid_adequate : (K.reportative φ a p).evid .adequate = K.evid .adequate :=
  K.addEvid_evid_of_ne_type φ a .reportative (e' := .adequate) (by decide)

theorem reportative_stack : (K.reportative φ a p).stack = Question.ofSet φ :: K.stack := rfl

theorem not_discourseCommitments_reportative_empty (h : a ≠ p) :
    φ ∉ ((empty : DS A W).reportative φ a p).discourseCommitments a := by
  rw [reportative_discourseCommitments_animator _ _ _ _ h]; simp [empty]

/-! ### Figure 5: the animator's denial -/

/-- The denial (37): the animator presents `φᶜ` on best possible grounds. -/
def denial : DS A W := (K.reportative φ a p).present φᶜ a a .bpg

theorem denial_discourseCommitments (h : a ≠ p) :
    φ ∈ (K.denial φ a p).discourseCommitments p ∧ φᶜ ∈ (K.denial φ a p).discourseCommitments a :=
  ⟨by
    rw [show (K.denial φ a p).discourseCommitments p =
      ((K.reportative φ a p).toTable.assert a φᶜ).discourseCommitments p from rfl,
      Table.assert, Table.discourseCommitments_push, Table.discourseCommitments_commit_of_ne h.symm]
    exact reportative_discourseCommitments_principal K φ a p,
   Table.mem_discourseCommitments_assert _ _ _⟩

theorem denial_discourseCommitments_animator (h : a ≠ p) :
    (K.denial φ a p).discourseCommitments a = insert φᶜ (K.discourseCommitments a) := by
  rw [show (K.denial φ a p).discourseCommitments a =
    ((K.reportative φ a p).toTable.assert a φᶜ).discourseCommitments a from rfl,
    Table.discourseCommitments_assert, reportative_discourseCommitments_animator _ _ _ _ h]

theorem denial_stack :
    (K.denial φ a p).stack = Question.ofSet φᶜ :: Question.ofSet φ :: K.stack := rfl

theorem denial_evid : φ ∈ (K.denial φ a p).evid .reportative a ∧
    φᶜ ∈ (K.denial φ a p).evid .bpg a := by
  refine ⟨?_, by simp [denial, present]⟩
  rw [show (K.denial φ a p).evid .reportative = (K.reportative φ a p).evid .reportative from
    addEvid_evid_of_ne_type (K.reportative φ a p) φᶜ a .bpg (e' := .reportative) (by decide)]
  exact reportative_evid K φ a p

theorem denial_isSource : (K.denial φ a p).IsSource φᶜ a :=
  ⟨Table.mem_discourseCommitments_assert _ _ _, Or.inr (by simp [denial, present])⟩

/-! ### Figure 6: the animator's acceptance under the Collaborative Principle -/

theorem figure6_discourseCommitments (h : a ≠ p) :
    φ ∈ ((K.reportative φ a p).accept φ a).discourseCommitments a ∧
    φ ∈ ((K.reportative φ a p).accept φ a).discourseCommitments p :=
  ⟨Table.mem_discourseCommitments_commit_self _ _ _, by
    rw [show ((K.reportative φ a p).accept φ a).discourseCommitments p =
      ((K.reportative φ a p).toTable.commit a φ).discourseCommitments p from rfl,
      Table.discourseCommitments_commit_of_ne h.symm]
    exact reportative_discourseCommitments_principal K φ a p⟩

theorem figure6_discourseCommitments_eq_assert (h : a ≠ p) :
    ((K.reportative φ a p).accept φ a).discourseCommitments a =
      (K.assert φ a).discourseCommitments a := by
  rw [show ((K.reportative φ a p).accept φ a).discourseCommitments a =
    ((K.reportative φ a p).toTable.commit a φ).discourseCommitments a from rfl,
    Table.discourseCommitments_commit_self, reportative_discourseCommitments_animator _ _ _ _ h]
  exact (Table.discourseCommitments_assert _ _ _).symm

theorem figure6_dependent : ((K.reportative φ a p).accept φ a).Dependent φ a :=
  ⟨Table.mem_discourseCommitments_commit_self _ _ _, by simp [accept]⟩

/-- Weaker than an assertion: the animator is not committed as a source unless she already had
adequate evidence or best possible grounds for `φ`. -/
theorem figure6_not_isSource (h1 : φ ∉ K.evid .adequate a) (h2 : φ ∉ K.evid .bpg a) :
    ¬ ((K.reportative φ a p).accept φ a).IsSource φ a := by
  rintro ⟨-, h | h⟩
  · exact h1 (by simpa [accept, reportative, present, addEvid_evid_of_ne_type] using h)
  · exact h2 (by simpa [accept, reportative, present, addEvid_evid_of_ne_type] using h)

theorem assert_isSource : (K.assert φ a).IsSource φ a :=
  ⟨assert_discourseCommitments K φ a, Or.inl (assert_evid K φ a)⟩

theorem present_reportative_dependent : (K.present φ a a .reportative).Dependent φ a :=
  ⟨Table.mem_discourseCommitments_assert _ _ _, by simp [present]⟩

end DS

end Faller2019
