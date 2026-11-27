module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Questions.Inquisitive.Answerhood
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.DropRight
public import Mathlib.Data.Set.Sups

/-!
# The Table

The context structure of Farkas and Bruce records the participants' discourse commitments, the
common ground, and the Table, a stack of the issues under discussion with the most recent on top.
A declarative with content `p` raises the issue whose only complete answer is `p`, and a polar
interrogative raises the issue whose complete answers are `p` and `pᶜ`, following Karttunen in
taking an interrogative to denote the set of its complete answers.

An issue `P` projects, from a set `ps` of common grounds, the consistent common grounds `f ⊓ 𝓟 q`
with `f ∈ ps` and `q` a complete answer of `P`. The projected set of a context is obtained from its
common ground by projecting each issue on the Table in turn. It consists of the common grounds
that settle everything at issue, and it does not depend on the order of the stack. An assertion
is a proposal: it commits its author and changes the projected set, and leaves the common ground
alone. Once a proposition is a joint commitment, it enters the common ground by Stalnaker's
update `f ⊓ 𝓟 p`, and the issues the new common ground decides leave the Table. When the new
common ground is one of the projected ones, the Table is left empty.

## Main definitions

* `Commitment.Table A W`: the context structure, with participants `A` and worlds `W`.
* `Commitment.Table.project`: the projection of an issue from a set of common grounds.
* `Commitment.Table.projectedSet`: the projected set of a context.
* `Commitment.Table.totalCommitment`, `Commitment.Table.IsCoherent`: the body of information a
  participant's discourse commitments generate with the common ground, and its consistency.
* `Commitment.Table.IsStable`: the Table is empty.
* `Commitment.Table.InCrisis`: the common ground is inconsistent or no projected common ground is
  consistent.
* `Commitment.Table.assert`, `Commitment.Table.polarQuestion`: the default assertion, which commits
  its author as in Gunlogson, and the default polar question.
* `Commitment.Table.settle`: the operation that turns a joint commitment into common ground.
* `Commitment.Table.agreeToDisagree`: the removal of a denied assertion and its denial.

## Main results

* `Commitment.Table.project_right_comm`, `Commitment.Table.projectedSet_congr_perm`: projection
  does not depend on the order of the issues.
* `Commitment.Table.le_commonGround_of_mem_projectedSet`,
  `Commitment.Table.decidedBy_of_mem_projectedSet_of_mem_stack`: a projected common ground refines
  the current one and decides every issue on the Table.
* `Commitment.Table.exists_le_mem_projectedSet_iff`: the consistent common grounds that refine the
  current one and decide every issue on the Table are those that refine a projected one.
* `Commitment.Table.isStable_settle_of_mem_projectedSet`: reaching a projected common ground
  empties the Table.
* `Commitment.Table.commonGround_settle_mem_projectedSet_assert`: in a stable context, settling an
  assertion reaches the common ground it projected.
* `Commitment.Table.inCrisis_iff`, `Commitment.Table.inCrisis_iff_projectedSet_eq_empty`: a
  conversation is in crisis exactly when no projected common ground is consistent, and with an
  issue on the Table exactly when nothing is projected.
* `Commitment.Table.inCrisis_assert_assert_compl`: a denied assertion leaves the conversation in
  crisis.
* `Commitment.Table.agreeToDisagree_assert_assert`,
  `Commitment.Table.generate_discourseCommitments_inf_eq_bot_agreeToDisagree`: agreeing to
  disagree keeps both commitments and restores the Table, and the commitments of the two parties
  are jointly inconsistent while the common ground is unchanged.
* `Commitment.Table.totalCommitment_settle_of_mem`: settling a proposition leaves the total
  commitment of a participant committed to it as it was.

## Implementation notes

* The projected set can always be rebuilt from the common ground and the Table, so it is derived
  rather than stored. The projection is the pointwise infimum `ps ⊼ 𝓟 '' alt P` of two families of
  filters with `⊥` removed, so that its commutativity is that of `⊼`.
* A discourse commitment list is a set of propositions, from which a proposition can be removed,
  and a common ground is a filter. The filter a list generates relates the two, and its kernel is
  the commitment set.
* A common ground is a filter of propositions, so a proposition follows from it when it belongs
  to the filter. Every necessary proposition then follows from every common ground, and the
  trivial issue is always decided; a finer consequence relation is not represented.
* An item on the Table is the denotation of a sentence, without the sentence. A polar
  interrogative and its negative counterpart then place the same item on the Table, and the
  effects that depend on the form of the item are not represented.
* The common-ground increasing operation applies once the proposition is on every commitment
  list; `Commitment.Table.settle` is the operation itself, and that the proposition is a joint
  commitment is a hypothesis on the caller. It pops from the top of the Table while the top issue
  has a complete answer that the new common ground entails. This is narrower than popping every
  issue one of whose answers is decided, positively or negatively: a declarative whose negation
  the new common ground entails stays on the Table. Whether a common ground entails a complete
  answer is not decidable, so the operation is classical and noncomputable.
* Agreeing to disagree requires a denial on top of the assertion it denies and removes both;
  `Commitment.Table.agreeToDisagree` pops twice and does not check the precondition.

## References

* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
* [L. Karttunen, *Syntax and Semantics of Questions* (1977)][karttunen-1977]
-/

@[expose] public section

open Filter

namespace Commitment

open Inquisitive Inquisitive.Proposition
open scoped SetFamily SetRel

/-- The context structure `K` of [farkas-bruce-2010] consists of the Table as a stack of issues,
the participants' discourse commitments, and the common ground. -/
@[ext]
structure Table (A W : Type*) where
  /-- The Table: the issues under discussion, the most recent first. -/
  stack : List (Proposition (Set W))
  /-- The discourse commitments of the participants that are not joint commitments. -/
  commitments : State A W
  /-- The common ground: the propositions that are joint commitments. -/
  commonGround : Filter W

initialize_simps_projections Table (as_prefix stack, as_prefix commitments, as_prefix commonGround)

namespace Table

variable {A W : Type*}

/-! ### Projecting an issue -/

/-- The projection of the issue `P` from the common grounds `ps` adds each complete answer of `P`
to each member of `ps` and discards the inconsistent results. -/
def project (ps : Set (Filter W)) (P : Proposition (Set W)) : Set (Filter W) :=
  (ps ⊼ 𝓟 '' alt P) \ {⊥}

section Project

variable {ps ps' : Set (Filter W)} {f : Filter W} {p : Set W} {P Q : Proposition (Set W)}

@[simp] theorem mem_project :
    f ∈ project ps P ↔ (∃ g ∈ ps, ∃ q ∈ alt P, g ⊓ 𝓟 q = f) ∧ f ≠ ⊥ := by
  simp [project]

theorem bot_notMem_project : ⊥ ∉ project ps P := fun h ↦ h.2 rfl

@[gcongr]
theorem project_subset (h : ps ⊆ ps') : project ps P ⊆ project ps' P :=
  Set.sdiff_subset_sdiff_left (Set.infs_subset_right h)

theorem exists_le_of_mem_project (h : f ∈ project ps P) : ∃ g ∈ ps, f ≤ g :=
  let ⟨g, hg, _, _, e⟩ := (mem_project.1 h).1
  ⟨g, hg, e ▸ inf_le_left⟩

theorem decidedBy_of_mem_project (h : f ∈ project ps P) : P.DecidedBy f :=
  let ⟨_, _, q, hq, e⟩ := (mem_project.1 h).1
  ⟨q, hq, e ▸ mem_inf_of_right (mem_principal_self q)⟩

/-- Discarding the inconsistent common grounds before projecting changes nothing. -/
@[simp] theorem project_sdiff_bot : project (ps \ {⊥}) P = project ps P := by
  ext f
  simp only [mem_project, Set.mem_sdiff, Set.mem_singleton_iff]
  refine and_congr_left fun hf ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hg.1, h⟩, fun ⟨g, hg, q, hq, e⟩ ↦
    ⟨g, ⟨hg, ?_⟩, q, hq, e⟩⟩
  rintro rfl
  exact hf (by simpa using e.symm)

/-- Two issues project the same common grounds in either order. -/
theorem project_right_comm : project (project ps P) Q = project (project ps Q) P := by
  have h (P Q : Proposition (Set W)) :
      project (project ps P) Q = (ps ⊼ 𝓟 '' alt P ⊼ 𝓟 '' alt Q) \ {⊥} := project_sdiff_bot
  rw [h, h, Set.infs_right_comm]

instance : LeftCommutative fun (P : Proposition (Set W)) (ps : Set (Filter W)) ↦ project ps P :=
  ⟨fun _ _ _ ↦ project_right_comm⟩

theorem project_singleton_ofSet (h : f ⊓ 𝓟 p ≠ ⊥) : project {f} (ofSet p) = {f ⊓ 𝓟 p} := by
  rw [project, alt_ofSet, Set.image_singleton, Set.singleton_infs_singleton,
    Set.sdiff_singleton_eq_self (Set.notMem_singleton_iff.2 h.symm)]

theorem project_singleton_polar (hp : f ⊓ 𝓟 p ≠ ⊥) (hnp : f ⊓ 𝓟 pᶜ ≠ ⊥) :
    project {f} (polar p) = {f ⊓ 𝓟 p, f ⊓ 𝓟 pᶜ} := by
  rw [project, alt_polar_of_nontrivial (fun e ↦ hp (by simp [e])) (fun e ↦ hnp (by simp [e])),
    Set.image_pair, Set.singleton_infs, Set.image_pair,
    Set.sdiff_singleton_eq_self (by simp [hp.symm, hnp.symm])]

end Project

variable (K : Table A W) (a : A) (p : Set W) (P : Proposition (Set W))

/-! ### The initial context and the stack -/

/-- The initial context has nothing on the Table, no commitments, and the trivial common ground. -/
@[simps] def empty : Table A W := ⟨[], ∅, ⊤⟩

instance : Inhabited (Table A W) := ⟨empty⟩

/-- Place an issue on the Table. -/
@[simps] def push : Table A W := { K with stack := P :: K.stack }

/-- Remove the top issue. -/
@[simps] def pop : Table A W := { K with stack := K.stack.tail }

/-- Commit `a` to `p`. -/
@[simps] def commit : Table A W := { K with commitments := insert (a, p) K.commitments }

/-- The current issue is the top of the Table, the trivial issue when the Table is empty. -/
def issue : Proposition (Set W) := K.stack.headD ⊤

@[simp] theorem issue_empty : (empty : Table A W).issue = ⊤ := rfl

@[simp] theorem issue_push : (K.push P).issue = P := rfl

@[simp] theorem issue_commit : (K.commit a p).issue = K.issue := rfl

/-- A conversation is stable when its Table is empty. -/
def IsStable : Prop := K.stack = []

@[simp] theorem empty_isStable : (empty : Table A W).IsStable := rfl

theorem not_isStable_push : ¬ (K.push P).IsStable := List.cons_ne_nil _ _

variable {K} in
theorem issue_eq_top_of_isStable (h : K.IsStable) : K.issue = ⊤ :=
  congrArg (List.headD · ⊤) h

/-! ### Discourse commitments -/

/-- The discourse commitments `DC_a` are the propositions `a` has publicly committed to. -/
def discourseCommitments : Set (Set W) := K.commitments.contents a

@[simp] theorem discourseCommitments_empty : (empty : Table A W).discourseCommitments a = ∅ :=
  rfl

@[simp] theorem discourseCommitments_push :
    (K.push P).discourseCommitments a = K.discourseCommitments a := rfl

@[simp] theorem discourseCommitments_pop :
    K.pop.discourseCommitments a = K.discourseCommitments a := rfl

@[simp] theorem discourseCommitments_commit_self :
    (K.commit a p).discourseCommitments a = insert p (K.discourseCommitments a) :=
  State.contents_insert_self

variable {K a p} in
theorem discourseCommitments_commit_of_ne {b : A} (h : b ≠ a) :
    (K.commit a p).discourseCommitments b = K.discourseCommitments b :=
  State.contents_insert_of_ne h

theorem mem_discourseCommitments_commit_iff {b : A} {q : Set W} :
    q ∈ (K.commit a p).discourseCommitments b ↔ (b = a ∧ q = p) ∨ q ∈ K.discourseCommitments b := by
  by_cases hb : b = a
  · subst hb; simp
  · simp [discourseCommitments_commit_of_ne hb, hb]

theorem mem_discourseCommitments_commit_self : p ∈ (K.commit a p).discourseCommitments a := by
  simp

/-! ### Total commitments -/

private theorem generate_insert (S : Set (Set W)) (q : Set W) :
    Filter.generate (insert q S) = Filter.generate S ⊓ 𝓟 q := by
  rw [Set.insert_eq, Filter.generate_union, Filter.generate_singleton, inf_comm]

/-- The total discourse commitment of `a` is the body of information that `a`'s discourse
commitments generate together with the common ground. -/
def totalCommitment : Filter W := Filter.generate (K.discourseCommitments a) ⊓ K.commonGround

/-- A participant is coherent when their total discourse commitment is consistent. -/
def IsCoherent : Prop := K.totalCommitment a ≠ ⊥

theorem totalCommitment_le_commonGround : K.totalCommitment a ≤ K.commonGround := inf_le_right

variable {K a} in
theorem mem_totalCommitment_of_mem_discourseCommitments {q : Set W}
    (h : q ∈ K.discourseCommitments a) : q ∈ K.totalCommitment a :=
  mem_inf_of_left (Filter.GenerateSets.basic h)

variable {K a} in
theorem IsCoherent.commonGround_ne_bot (h : K.IsCoherent a) : K.commonGround ≠ ⊥ := fun e ↦
  h (le_bot_iff.1 (e ▸ K.totalCommitment_le_commonGround a))

/-- The kernel of the commitments `a`'s discourse commitments generate is `a`'s commitment set. -/
theorem ker_generate_discourseCommitments :
    (Filter.generate (K.discourseCommitments a)).ker = K.commitments.commitmentSet a := by
  rw [Filter.generate_eq_biInf, State.commitmentSet, Set.sInter_eq_biInter]
  simp [discourseCommitments]

variable {K a p} in
/-- Two participants committed to a proposition and to its negation have jointly inconsistent
discourse commitments. -/
theorem generate_discourseCommitments_inf_eq_bot {b : A} (ha : p ∈ K.discourseCommitments a)
    (hb : pᶜ ∈ K.discourseCommitments b) :
    Filter.generate (K.discourseCommitments a) ⊓ Filter.generate (K.discourseCommitments b) = ⊥ :=
  Filter.empty_mem_iff_bot.1 <| Set.inter_compl_self p ▸
    inter_mem_inf (Filter.GenerateSets.basic ha) (Filter.GenerateSets.basic hb)

@[simp] theorem totalCommitment_empty : (empty : Table A W).totalCommitment a = ⊤ := by
  simp [totalCommitment, Filter.generate_empty]

@[simp] theorem totalCommitment_push : (K.push P).totalCommitment a = K.totalCommitment a := rfl

@[simp] theorem totalCommitment_pop : K.pop.totalCommitment a = K.totalCommitment a := rfl

@[simp] theorem totalCommitment_commit_self :
    (K.commit a p).totalCommitment a = K.totalCommitment a ⊓ 𝓟 p := by
  rw [totalCommitment, discourseCommitments_commit_self, generate_insert, commonGround_commit,
    totalCommitment, inf_right_comm]

variable {K a p} in
theorem totalCommitment_commit_of_ne {b : A} (h : b ≠ a) :
    (K.commit a p).totalCommitment b = K.totalCommitment b := by
  rw [totalCommitment, discourseCommitments_commit_of_ne h]
  rfl

/-! ### The projected set -/

/-- The projected set consists of the common grounds that canonically settle what is at issue,
rebuilt from the common ground by the issues on the Table, oldest first. -/
def projectedSet : Set (Filter W) := K.stack.foldr (fun P ps ↦ project ps P) {K.commonGround}

@[simp] theorem projectedSet_empty : (empty : Table A W).projectedSet = {⊤} := rfl

@[simp] theorem projectedSet_push : (K.push P).projectedSet = project K.projectedSet P := rfl

@[simp] theorem projectedSet_commit : (K.commit a p).projectedSet = K.projectedSet :=
  rfl

section

variable {K a p P} {f : Filter W}

theorem projectedSet_of_isStable (h : K.IsStable) : K.projectedSet = {K.commonGround} := by
  rw [projectedSet, show K.stack = [] from h, List.foldr_nil]

/-- The projected set does not depend on the order of the issues on the Table. -/
theorem projectedSet_congr_perm {L : Table A W} (hs : K.stack.Perm L.stack)
    (hc : K.commonGround = L.commonGround) : K.projectedSet = L.projectedSet := by
  rw [projectedSet, projectedSet, hc]
  exact hs.foldr_eq _

/-- A projected common ground refines the current one. -/
theorem le_commonGround_of_mem_projectedSet (h : f ∈ K.projectedSet) : f ≤ K.commonGround := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact le_of_eq h
  | cons P T ih =>
    obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project h
    exact hfg.trans (ih hg)

/-- Every projected common ground decides every issue on the Table. -/
theorem decidedBy_of_mem_projectedSet_of_mem_stack (hf : f ∈ K.projectedSet) (hP : P ∈ K.stack) :
    P.DecidedBy f := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact (List.not_mem_nil hP).elim
  | cons Q T ih =>
    rcases List.mem_cons.1 hP with rfl | hP
    · exact decidedBy_of_mem_project hf
    · obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project hf
      exact (ih hg hP).mono hfg

theorem ker_mem_issue_of_mem_projectedSet (hf : f ∈ K.projectedSet) : f.ker ∈ K.issue := by
  change f.ker ∈ K.stack.headD ⊤
  cases h : K.stack with
  | nil => exact mem_top
  | cons P T =>
    exact (decidedBy_of_mem_projectedSet_of_mem_stack (P := P) hf (h ▸ List.mem_cons_self)).ker_mem

/-- The consistent common grounds that refine the current one and decide every issue on the Table
are those that refine a projected common ground. -/
theorem exists_le_mem_projectedSet_iff {g : Filter W} (hg : g ≠ ⊥) :
    (∃ f ∈ K.projectedSet, g ≤ f) ↔ g ≤ K.commonGround ∧ ∀ P ∈ K.stack, P.DecidedBy g := by
  refine ⟨fun ⟨f, hf, hgf⟩ ↦ ⟨hgf.trans (le_commonGround_of_mem_projectedSet hf),
    fun P hP ↦ (decidedBy_of_mem_projectedSet_of_mem_stack hf hP).mono hgf⟩, ?_⟩
  obtain ⟨T, C, cg⟩ := K
  induction T with
  | nil => exact fun h ↦ ⟨cg, rfl, h.1⟩
  | cons P T ih =>
    rintro ⟨hcg, hdec⟩
    obtain ⟨f, hf, hgf⟩ := ih ⟨hcg, fun Q hQ ↦ hdec Q (List.mem_cons_of_mem _ hQ)⟩
    obtain ⟨q, hq, hqg⟩ := hdec P List.mem_cons_self
    have hle : g ≤ f ⊓ 𝓟 q := le_inf hgf (le_principal_iff.2 hqg)
    exact ⟨f ⊓ 𝓟 q, mem_project.2 ⟨⟨f, hf, q, hq, rfl⟩, fun h ↦ hg (le_bot_iff.1 (h ▸ hle))⟩, hle⟩

end

/-! ### Assertions and polar questions -/

/-- In the default assertion (9), `a` commits to `p` and places the declarative's issue on the
Table. -/
@[simps!] def assert : Table A W := (K.commit a p).push (ofSet p)

/-- The default polar question (12) places the interrogative's issue on the Table. -/
@[simps!] def polarQuestion : Table A W := K.push (polar p)

@[simp] theorem issue_assert : (K.assert a p).issue = ofSet p := rfl

@[simp] theorem issue_polarQuestion : (K.polarQuestion p).issue = polar p := rfl

@[simp] theorem discourseCommitments_polarQuestion :
    (K.polarQuestion p).discourseCommitments a = K.discourseCommitments a := rfl

@[simp] theorem discourseCommitments_assert :
    (K.assert a p).discourseCommitments a = insert p (K.discourseCommitments a) :=
  discourseCommitments_commit_self K a p

variable {K a p} in
theorem discourseCommitments_assert_of_ne {b : A} (h : b ≠ a) :
    (K.assert a p).discourseCommitments b = K.discourseCommitments b :=
  discourseCommitments_commit_of_ne h

theorem mem_discourseCommitments_assert :
    p ∈ (K.assert a p).discourseCommitments a := mem_discourseCommitments_commit_self K a p

/-- A polar question and its negative counterpart place the same issue on the Table. -/
@[simp] theorem polarQuestion_compl : K.polarQuestion pᶜ = K.polarQuestion p := by
  rw [polarQuestion, polar_compl, polarQuestion]

@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet = project K.projectedSet (ofSet p) := rfl

@[simp] theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet = project K.projectedSet (polar p) := rfl

section

variable {K a p P} {f : Filter W}

theorem mem_of_mem_projectedSet_assert (h : f ∈ (K.assert a p).projectedSet) : p ∈ f :=
  decidedBy_ofSet.1 (decidedBy_of_mem_project h)

theorem mem_or_compl_mem_of_mem_projectedSet_polarQuestion
    (h : f ∈ (K.polarQuestion p).projectedSet) : p ∈ f ∨ pᶜ ∈ f :=
  decidedBy_polar.1 (decidedBy_of_mem_project h)

end

variable {K p} in
/-- An assertion in a stable context projects the common ground with its content (8). -/
theorem projectedSet_assert_of_isStable (hK : K.IsStable) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.assert a p).projectedSet = {K.commonGround ⊓ 𝓟 p} := by
  rw [projectedSet_assert, projectedSet_of_isStable hK, project_singleton_ofSet hp]

variable {K p} in
/-- A polar question in a stable context projects a common ground for each answer (11). -/
theorem projectedSet_polarQuestion_of_isStable (hK : K.IsStable)
    (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) :
    (K.polarQuestion p).projectedSet = {K.commonGround ⊓ 𝓟 p, K.commonGround ⊓ 𝓟 pᶜ} := by
  rw [projectedSet_polarQuestion, projectedSet_of_isStable hK, project_singleton_polar hp hnp]

@[simp] theorem totalCommitment_assert_self :
    (K.assert a p).totalCommitment a = K.totalCommitment a ⊓ 𝓟 p :=
  totalCommitment_commit_self K a p

variable {K a p} in
theorem totalCommitment_assert_of_ne {b : A} (h : b ≠ a) :
    (K.assert a p).totalCommitment b = K.totalCommitment b :=
  totalCommitment_commit_of_ne h

/-! ### Settling a joint commitment -/

open scoped Classical in
/-- In the common-ground increasing operation M' (17), applied once `p` is on every commitment
list, `p` enters the common ground and leaves the individual commitment lists, and the issues the
new common ground decides are popped from the top of the Table. -/
@[simps] noncomputable def settle : Table A W where
  stack := K.stack.dropWhile fun P ↦ decide (P.DecidedBy (K.commonGround ⊓ 𝓟 p))
  commitments := {(a, q) | a ~[K.commitments] q ∧ q ≠ p}
  commonGround := K.commonGround ⊓ 𝓟 p

variable {K} in
theorem isStable_settle_of_isStable (h : K.IsStable) : (K.settle p).IsStable :=
  congrArg (List.dropWhile _) h

/-- M' strips the shared proposition from every commitment list. -/
theorem discourseCommitments_settle :
    (K.settle p).discourseCommitments a = K.discourseCommitments a \ {p} := by
  ext
  simp [discourseCommitments, State.contents]

variable {K p P} in
/-- M' pops a decided issue from the top of the Table and goes on popping. -/
theorem settle_push_of_decidedBy (h : P.DecidedBy (K.commonGround ⊓ 𝓟 p)) :
    (K.push P).settle p = K.settle p :=
  Table.ext (by
    rw [stack_settle, stack_push, List.dropWhile_cons_of_pos (by simpa using h)]
    rfl) rfl rfl

variable {K p P} in
theorem stack_settle_push_of_not_decidedBy (h : ¬ P.DecidedBy (K.commonGround ⊓ 𝓟 p)) :
    ((K.push P).settle p).stack = P :: K.stack := by
  simp [h]

theorem settle_commit_self : (K.commit a p).settle p = K.settle p :=
  Table.ext rfl (Set.insert_inter_of_notMem (t := {q : A × Set W | q.2 ≠ p}) (not_not.2 rfl)) rfl

/-- M' with the asserted proposition pops the assertion and strips its commitment. -/
theorem settle_assert_self : (K.assert a p).settle p = K.settle p :=
  (settle_push_of_decidedBy
    (decidedBy_ofSet.2 (mem_inf_of_right (mem_principal_self p)))).trans
    (settle_commit_self K a p)

theorem settle_settle : (K.settle p).settle p = K.settle p := by
  classical
  refine Table.ext ?_ ?_ ?_
  · simp [List.dropWhile_idempotent]
  · ext ⟨a, q⟩
    simp
  · simp

theorem settle_polarQuestion_self : (K.polarQuestion p).settle p = K.settle p :=
  settle_push_of_decidedBy (decidedBy_polar.2 (.inl (mem_inf_of_right (mem_principal_self p))))

section

variable {K a p P} {f : Filter W}

/-- Reaching a projected common ground empties the Table. -/
theorem isStable_settle_of_mem_projectedSet (h : K.commonGround ⊓ 𝓟 p ∈ K.projectedSet) :
    (K.settle p).IsStable := by
  classical
  rw [IsStable, stack_settle, List.dropWhile_eq_nil_iff]
  exact fun P hP ↦ decide_eq_true (decidedBy_of_mem_projectedSet_of_mem_stack h hP)

end

variable {K p} in
/-- In a stable context, settling an assertion reaches the common ground it projected. -/
theorem commonGround_settle_mem_projectedSet_assert (hK : K.IsStable)
    (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.settle p).commonGround ∈ (K.assert a p).projectedSet :=
  projectedSet_assert_of_isStable a hK hp ▸ rfl

/-- Settling `p` adds `p` to every total commitment. -/
theorem totalCommitment_settle : (K.settle p).totalCommitment a = K.totalCommitment a ⊓ 𝓟 p := by
  have key : Filter.generate (K.discourseCommitments a \ {p}) ⊓ 𝓟 p =
      Filter.generate (K.discourseCommitments a) ⊓ 𝓟 p := by
    rw [← generate_insert, ← generate_insert, Set.insert_sdiff_singleton]
  rw [totalCommitment, discourseCommitments_settle, commonGround_settle, inf_left_comm, key,
    inf_left_comm, totalCommitment, inf_assoc]

variable {K a p} in
/-- Settling a proposition leaves the total commitment of a participant committed to it as it
was. -/
theorem totalCommitment_settle_of_mem (h : p ∈ K.discourseCommitments a) :
    (K.settle p).totalCommitment a = K.totalCommitment a :=
  (totalCommitment_settle K a p).trans <|
    inf_eq_left.2 (le_principal_iff.2 (mem_totalCommitment_of_mem_discourseCommitments h))

/-! ### Crisis -/

/-- A conversation is in crisis when its common ground or every projected common ground is
inconsistent. -/
def InCrisis : Prop := K.commonGround = ⊥ ∨ ∀ f ∈ K.projectedSet, f = ⊥

/-- With the projected set derived, a conversation is in crisis exactly when no projected common
ground is consistent. -/
theorem inCrisis_iff : K.InCrisis ↔ ∀ f ∈ K.projectedSet, f = ⊥ :=
  or_iff_right_of_imp fun hcg _ hf ↦
    le_bot_iff.1 ((le_commonGround_of_mem_projectedSet hf).trans_eq hcg)

variable {K} in
/-- With an issue on the Table, a conversation is in crisis exactly when nothing is projected. -/
theorem inCrisis_iff_projectedSet_eq_empty (h : ¬ K.IsStable) :
    K.InCrisis ↔ K.projectedSet = ∅ := by
  obtain ⟨_ | ⟨P, T⟩, C, cg⟩ := K
  · exact absurd rfl h
  · rw [inCrisis_iff, Set.eq_empty_iff_forall_notMem]
    exact forall_congr' fun f ↦ ⟨fun hf hmem ↦ bot_notMem_project (hf hmem ▸ hmem),
      fun hf hmem ↦ absurd hmem hf⟩

/-- After an assertion has been denied, nothing consistent is projected (21). -/
theorem projectedSet_assert_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).projectedSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun f hf ↦ by
    rw [projectedSet_assert, mem_project, alt_ofSet] at hf
    obtain ⟨⟨g, hg, q, rfl, rfl⟩, hne⟩ := hf
    refine hne (inf_principal_eq_bot.2 ?_)
    rw [compl_compl]
    exact mem_of_mem_projectedSet_assert hg

/-- A denied assertion leaves the conversation in crisis. -/
theorem inCrisis_assert_assert_compl (b : A) : ((K.assert a p).assert b pᶜ).InCrisis :=
  (inCrisis_iff _).2 fun f hf ↦
    absurd (projectedSet_assert_assert_compl K a p b ▸ hf) (Set.notMem_empty f)

/-! ### Agreeing to disagree -/

/-- Agreeing to disagree (23), from a Table with the denial on top of the assertion it denies,
removes the contradictory pair from the Table and keeps the commitments. -/
@[simps!] def agreeToDisagree : Table A W := K.pop.pop

@[simp] theorem discourseCommitments_agreeToDisagree :
    K.agreeToDisagree.discourseCommitments a = K.discourseCommitments a := rfl

/-- Agreeing to disagree after two assertions leaves the Table and common ground unchanged, with
both commitments recorded. -/
theorem agreeToDisagree_assert_assert (b : A) (q : Set W) :
    ((K.assert a p).assert b q).agreeToDisagree = (K.commit a p).commit b q := rfl

/-- Agreeing to disagree restores the crisis status of the context before the assertions. -/
theorem inCrisis_agreeToDisagree_assert_assert (b : A) (q : Set W) :
    ((K.assert a p).assert b q).agreeToDisagree.InCrisis ↔ K.InCrisis := Iff.rfl

@[simp] theorem totalCommitment_agreeToDisagree :
    K.agreeToDisagree.totalCommitment a = K.totalCommitment a := rfl

/-- After agreeing to disagree, the discourse commitments of the two parties are jointly
inconsistent. -/
theorem generate_discourseCommitments_inf_eq_bot_agreeToDisagree (b : A) :
    Filter.generate (((K.assert a p).assert b pᶜ).agreeToDisagree.discourseCommitments a) ⊓
      Filter.generate (((K.assert a p).assert b pᶜ).agreeToDisagree.discourseCommitments b) = ⊥ :=
  generate_discourseCommitments_inf_eq_bot
    ((mem_discourseCommitments_commit_iff ..).2 (.inr (mem_discourseCommitments_commit_self K a p)))
    (mem_discourseCommitments_commit_self _ b pᶜ)

end Table

end Commitment
