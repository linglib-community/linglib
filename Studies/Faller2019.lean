module

public import Linglib.Discourse.Commitment.Table

/-!
# Faller (2019): The Discourse Commitments of Illocutionary Reportatives

Faller accounts for declaratives with the Cuzco Quechua reportative *=si* in a modified version
of Farkas and Bruce's discourse structure. The speaker of a reportative declarative need not be
committed to the reported proposition `φ` and may deny it, yet `φ` is at issue and, unless it is
denied, is taken to be proposed for the common ground. The account splits Goffman's animator from
the principal. The operator PRESENT of the declarative puts `φ` on the Table and commits the
principal to its truth and the animator to adequate evidence, with animator and principal
identified by default (her (34)). The reportative is an illocutionary modifier that adds `φ` to
the animator's reportative commitments instead and requires the principal to be distinct (her
(35)). The structure `DS` is the Table of `Discourse/Commitment/Table.lean` with a set of
evidential commitments per participant for each evidence type (her (24) and (25)), and `present`
carries the evidence type of its evidential as a parameter, so the plain declarative, the
reportative and the best-possible-grounds evidential differ only there and in the distinctness
requirement, which is the paper's uniform semantics of evidentials. In assertion acceptance,
`accept` (§4.3, Figure 2), the addressee commits on the strength of the assertion, so that with
reportative evidence `φ` leaves the Table and enters the common ground.

The theorems are the paper's tableaux. Default assertion is Figure 1 (`assert_discourseCommitments`,
`assert_evid`) and its acceptance Figure 2 (`accept_discourseCommitments`, `accept_evid_addressee`,
`mem_commonGround_accept`, `accept_stack`). In a reportative presentation, Figure 4, the principal
is committed and the animator has reportative evidence
(`reportative_discourseCommitments_principal`, `reportative_evid`), and Absence of Commitment is
`reportative_discourseCommitments_animator`, the animator's truth commitments being untouched, with
`reportative_evid_adequate` the override of the adequate-evidence default. The animator's denial
(37), which replaces `φ` by `φᶜ` on the Table, is Figure 5 (`denial_discourseCommitments`,
`denial_evid`, `denial_stack`). Under Walker's Collaborative Principle an animator who does not deny
the reported `φ` becomes committed to it, Figure 6 (`collaborate`, `figure6_discourseCommitments`,
`figure6_discourseCommitments_eq_assert`), while `φ` stays on the Table and enters the common ground
only when the addressee accepts it (`figure6_stack`, `figure6_accept`). §6.3 draws the upshot with
Gunlogson's distinction, by which a truth commitment is `Dependent` when backed by reportative
evidence and `IsSource` when backed by adequate evidence or best possible grounds. The animator of
Figure 6 is thus committed as after an assertion but only dependently (`figure6_dependent`,
`figure6_not_isSource`), where the asserter and the denier commit as sources (`assert_isSource`,
`denial_isSource`) and the English hearsay parenthetical commits dependently
(`present_reportative_dependent`).

## Implementation notes

* Goffman's author plays no part in the operators, which take the animator and the principal
  as participants; the paper treats the principal as a free variable that need not be a
  participant, and the acceptance of Figure 2 is the addressee's `Table.commit`, with the
  Gunlogson distinction carried by the evidential commitments rather than by the Table.
* The Collaborative Principle is pragmatic, and the commitment it brings an animator is
  `collaborate`, the animator's truth commitment alone. It is not the acceptance of Figure 2,
  which resolves the issue and grows the common ground.
* The evidential commitments are one commitment state keyed by evidence type and participant,
  `Commitment.State (EvidenceType × A) W`.
* Acceptance keeps `φ` in the truth commitments when it enters the common ground, as the
  paper's tableaux do, rather than stripping it as `Table.settle` does.

## Errata

* After (35) the prose has (35ii) override the default in (34iii) and (35i) the default in
  (34ii). Against the final (34), whose defaults are (ii) the principal's truth commitment, (iii)
  the animator's adequate evidence and (iv) the identification of animator and principal, the
  overridden defaults are (34iv) and (34iii), as the distinctness hypothesis of the reportative
  theorems and `reportative_evid_adequate` take them.

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

/-- The evidence types whose commitments are tracked in distinct sets are adequate evidence in
Grice's sense, the default of assertion (24b), reportative evidence, which the reportative *=si*
contributes (25a), and best possible grounds, which *=mi* contributes (25b). -/
inductive EvidenceType
  | adequate
  | reportative
  | bpg
  deriving DecidableEq, Repr

/-- A discourse structure is the Table, with its truth commitments and common ground, together
with the evidential commitments `AeC`, `RepC` and `BpgC` of each participant, a commitment state
keyed by evidence type and participant. -/
structure DS (A W : Type*) extends Table A W where
  /-- `((e, a), φ) ∈ evid` when `a` is committed to having evidence of type `e` for `φ`. -/
  evid : State (EvidenceType × A) W

namespace DS

variable {A W : Type*} (K : DS A W) (φ : Set W) (a b p : A) (e : EvidenceType)

/-- The initial structure has the empty Table and no evidential commitments. -/
def empty : DS A W := { Table.empty with evid := ∅ }

/-- Add `φ` to `a`'s evidential commitments of type `e`. -/
def addEvid : DS A W := { K with evid := insert ((e, a), φ) K.evid }

/-- In the presentation (34) with an evidential, `φ` goes on the Table, the principal `p` commits
to its truth, and the animator `a` commits to evidence of type `e`. -/
def present : DS A W := { K.addEvid φ a e with toTable := K.toTable.assert p φ }

/-- In default assertion the animator is the principal and the evidence is adequate. -/
def assert : DS A W := K.present φ a a .adequate

/-- The reportative presents with reportative evidence; that animator and principal are distinct is
its requirement, a hypothesis of the theorems below (35). -/
def reportative : DS A W := K.present φ a p .reportative

/-- In the acceptance of `φ` by `b` (§4.3), `b` commits to `φ` on the strength of the assertion, so
that with reportative evidence `φ` leaves the Table and enters the common ground. -/
def accept : DS A W :=
  { K.addEvid φ b .reportative with
    toTable := { (K.toTable.commit b φ).pop with commonGround := K.commonGround ⊓ 𝓟 φ } }

/-- Under the Collaborative Principle (29), an animator who does not deny the `φ` she presented is
understood as accepting it and becomes committed to its truth, while `φ` stays on the Table
(Figure 6). -/
def collaborate : DS A W := { K with toTable := K.toTable.commit a φ }

/-- A truth commitment of `a` to `φ` is dependent when `φ` is in `TC_a ∩ RepC_a`
([gunlogson-2008], §6.3). -/
def Dependent : Prop := φ ∈ K.discourseCommitments a ∧ ((.reportative, a), φ) ∈ K.evid

/-- A truth commitment of `a` to `φ` is a source commitment when `φ` is in `TC_a ∩ AeC_a` or in
`TC_a ∩ BpgC_a` (§6.3). -/
def IsSource : Prop :=
  φ ∈ K.discourseCommitments a ∧ (((.adequate, a), φ) ∈ K.evid ∨ ((.bpg, a), φ) ∈ K.evid)

@[simp] theorem addEvid_toTable : (K.addEvid φ a e).toTable = K.toTable := rfl
@[simp] theorem addEvid_evid : (K.addEvid φ a e).evid = insert ((e, a), φ) K.evid := rfl
@[simp] theorem present_toTable : (K.present φ a p e).toTable = K.toTable.assert p φ := rfl
@[simp] theorem present_evid : (K.present φ a p e).evid = insert ((e, a), φ) K.evid := rfl
@[simp] theorem accept_toTable :
    (K.accept φ b).toTable =
      { (K.toTable.commit b φ).pop with commonGround := K.commonGround ⊓ 𝓟 φ } := rfl
@[simp] theorem accept_evid : (K.accept φ b).evid = insert ((.reportative, b), φ) K.evid := rfl
@[simp] theorem collaborate_toTable : (K.collaborate φ a).toTable = K.toTable.commit a φ := rfl
@[simp] theorem collaborate_evid : (K.collaborate φ a).evid = K.evid := rfl

/-! ### Default assertion and its acceptance, Figures 1 and 2 -/

theorem assert_discourseCommitments :
    φ ∈ (K.assert φ a).discourseCommitments a := Table.mem_discourseCommitments_assert _ _ _

theorem assert_evid : ((.adequate, a), φ) ∈ (K.assert φ a).evid := Set.mem_insert _ _

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

theorem accept_evid_addressee : ((.reportative, b), φ) ∈ ((K.assert φ a).accept φ b).evid :=
  Set.mem_insert _ _

theorem mem_commonGround_accept : φ ∈ ((K.assert φ a).accept φ b).commonGround :=
  mem_inf_of_right (mem_principal_self φ)

/-- Acceptance resolves the issue, leaving the Table as it was before the assertion. -/
theorem accept_stack : ((K.assert φ a).accept φ b).stack = K.stack := rfl

/-! ### Reportative presentation and Absence of Commitment, Figure 4 -/

theorem reportative_discourseCommitments_principal :
    φ ∈ (K.reportative φ a p).discourseCommitments p := Table.mem_discourseCommitments_assert _ _ _

theorem reportative_evid : ((.reportative, a), φ) ∈ (K.reportative φ a p).evid :=
  Set.mem_insert _ _

theorem reportative_discourseCommitments_animator (h : a ≠ p) :
    (K.reportative φ a p).discourseCommitments a = K.discourseCommitments a :=
  Table.discourseCommitments_commit_of_ne h

/-- No adequate-evidence commitment is added, as (35i) overrides (34iii). -/
theorem reportative_evid_adequate (c : A) :
    (K.reportative φ a p).evid.contents (.adequate, c) = K.evid.contents (.adequate, c) :=
  State.contents_insert_of_ne (by simp)

theorem reportative_stack : (K.reportative φ a p).stack = Question.ofSet φ :: K.stack := rfl

theorem not_discourseCommitments_reportative_empty (h : a ≠ p) :
    φ ∉ ((empty : DS A W).reportative φ a p).discourseCommitments a := by
  rw [reportative_discourseCommitments_animator _ _ _ _ h]; simp [empty]

/-! ### The animator's denial, Figure 5 -/

/-- In the denial (37) the animator replaces the reported `φ` on the Table by `φᶜ`, presented on
best possible grounds. -/
def denial : DS A W :=
  ({ K.reportative φ a p with toTable := (K.reportative φ a p).toTable.pop } : DS A W).present
    φᶜ a a .bpg

theorem denial_discourseCommitments (h : a ≠ p) :
    φ ∈ (K.denial φ a p).discourseCommitments p ∧ φᶜ ∈ (K.denial φ a p).discourseCommitments a :=
  ⟨by
    rw [show (K.denial φ a p).discourseCommitments p =
      ((K.reportative φ a p).toTable.pop.assert a φᶜ).discourseCommitments p from rfl,
      Table.discourseCommitments_assert_of_ne h.symm, Table.discourseCommitments_pop]
    exact reportative_discourseCommitments_principal K φ a p,
   Table.mem_discourseCommitments_assert _ _ _⟩

theorem denial_discourseCommitments_animator (h : a ≠ p) :
    (K.denial φ a p).discourseCommitments a = insert φᶜ (K.discourseCommitments a) := by
  rw [show (K.denial φ a p).discourseCommitments a =
    ((K.reportative φ a p).toTable.pop.assert a φᶜ).discourseCommitments a from rfl,
    Table.discourseCommitments_assert, Table.discourseCommitments_pop,
    reportative_discourseCommitments_animator _ _ _ _ h]

/-- The denial replaces `φ` on the Table by `φᶜ` (37). -/
theorem denial_stack : (K.denial φ a p).stack = Question.ofSet φᶜ :: K.stack := rfl

theorem denial_evid : ((.reportative, a), φ) ∈ (K.denial φ a p).evid ∧
    ((.bpg, a), φᶜ) ∈ (K.denial φ a p).evid :=
  ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), Set.mem_insert _ _⟩

theorem denial_isSource : (K.denial φ a p).IsSource φᶜ a :=
  ⟨Table.mem_discourseCommitments_assert _ _ _, Or.inr (Set.mem_insert _ _)⟩

/-! ### The animator's acceptance under the Collaborative Principle, Figure 6 -/

theorem figure6_discourseCommitments (h : a ≠ p) :
    φ ∈ ((K.reportative φ a p).collaborate φ a).discourseCommitments a ∧
    φ ∈ ((K.reportative φ a p).collaborate φ a).discourseCommitments p :=
  ⟨Table.mem_discourseCommitments_commit_self _ _ _, by
    rw [show ((K.reportative φ a p).collaborate φ a).discourseCommitments p =
      ((K.reportative φ a p).toTable.commit a φ).discourseCommitments p from rfl,
      Table.discourseCommitments_commit_of_ne h.symm]
    exact reportative_discourseCommitments_principal K φ a p⟩

theorem figure6_discourseCommitments_eq_assert (h : a ≠ p) :
    ((K.reportative φ a p).collaborate φ a).discourseCommitments a =
      (K.assert φ a).discourseCommitments a := by
  rw [show ((K.reportative φ a p).collaborate φ a).discourseCommitments a =
    ((K.reportative φ a p).toTable.commit a φ).discourseCommitments a from rfl,
    Table.discourseCommitments_commit_self, reportative_discourseCommitments_animator _ _ _ _ h]
  exact (Table.discourseCommitments_assert _ _ _).symm

/-- After the animator's commitment, `φ` is still on the Table and the common ground is unchanged,
since `φ` is now only proposed for it (Figure 6). -/
theorem figure6_stack :
    ((K.reportative φ a p).collaborate φ a).stack = Question.ofSet φ :: K.stack ∧
      ((K.reportative φ a p).collaborate φ a).commonGround = K.commonGround :=
  ⟨rfl, rfl⟩

/-- If the addressee accepts `φ` too, it enters the common ground as a regularly asserted
proposition and resolves the issue (§6.2). -/
theorem figure6_accept :
    φ ∈ (((K.reportative φ a p).collaborate φ a).accept φ b).commonGround ∧
      (((K.reportative φ a p).collaborate φ a).accept φ b).stack = K.stack :=
  ⟨mem_inf_of_right (mem_principal_self φ), rfl⟩

theorem figure6_dependent : ((K.reportative φ a p).collaborate φ a).Dependent φ a :=
  ⟨Table.mem_discourseCommitments_commit_self _ _ _, Set.mem_insert _ _⟩

/-- The acceptance is weaker than an assertion, since the animator is not committed as a source
unless she already had adequate evidence or best possible grounds for `φ`. -/
theorem figure6_not_isSource (h1 : ((.adequate, a), φ) ∉ K.evid) (h2 : ((.bpg, a), φ) ∉ K.evid) :
    ¬ ((K.reportative φ a p).collaborate φ a).IsSource φ a := by
  rintro ⟨-, h | h⟩ <;> simp_all [reportative, present]

theorem assert_isSource : (K.assert φ a).IsSource φ a :=
  ⟨assert_discourseCommitments K φ a, Or.inl (assert_evid K φ a)⟩

theorem present_reportative_dependent : (K.present φ a a .reportative).Dependent φ a :=
  ⟨Table.mem_discourseCommitments_assert _ _ _, Set.mem_insert _ _⟩

end DS

end Faller2019
