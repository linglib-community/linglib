module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Semantics.Questions.Inquisitive.Answerhood
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Set.Sups

/-!
# The Table

The context structure of Farkas and Bruce records the participants' discourse commitments, the
common ground, and the Table, a stack of the issues under discussion with the most recent on top.
A declarative with content `p` raises the issue whose only complete answer is `p`, and a polar
interrogative raises the issue whose complete answers are `p` and `pᶜ`.

An issue `P` projects, from a set `ps` of common grounds, the consistent common grounds `f ⊓ 𝓟 q`
with `f ∈ ps` and `q` a complete answer of `P`. The projected set of a context is obtained from its
common ground by projecting each issue on the Table in turn. Its members are the weakest
consistent bodies of information that refine the common ground and decide every issue, and it
does not depend on the order of the stack. Once a proposition is a joint commitment it enters the
common ground by Stalnaker's update `f ⊓ 𝓟 p`, and the issues the new common ground decides leave
the Table.

## Main definitions

* `Commitment.Table A W`: the context structure, with participants `A` and worlds `W`.
* `Commitment.Table.project`: the projection of an issue from a set of common grounds.
* `Commitment.Table.projectedSet`: the projected set of a context.
* `Commitment.Table.assert`, `Commitment.Table.polarQuestion`: the default assertion, which commits
  its author as in Gunlogson, and the default polar question.
* `Commitment.Table.settle`: the operation that turns a joint commitment into common ground.

## Main results

* `Commitment.Table.exists_le_mem_projectedSet_iff`: the consistent bodies of information that
  refine the common ground and decide every issue on the Table are those that refine a projected
  common ground.
* `Commitment.Table.project_right_comm`, `Commitment.Table.projectedSet_congr_perm`: projection
  does not depend on the order of the issues.
* `Commitment.Table.stack_settle_eq_nil_of_mem_projectedSet`: reaching a projected common ground
  empties the Table.

## Implementation notes

* The projected set can always be rebuilt from the common ground and the Table, so it is derived
  rather than stored. The projection is the pointwise infimum `ps ⊼ 𝓟 '' alt P` of two families of
  filters with `⊥` removed, so that its commutativity is that of `⊼`.
* A common ground is a filter of propositions, so a proposition follows from it when it belongs
  to the filter. Every necessary proposition then follows from every common ground; a finer
  consequence relation is not represented. A discourse commitment list is a set of propositions,
  from which a proposition can be removed.
* An item on the Table is the denotation of a sentence, without the sentence. A polar
  interrogative and its negative counterpart then place the same item on the Table, and the
  effects that depend on the form of the item are not represented.
* The common-ground increasing operation applies once the proposition is on every commitment
  list; `Commitment.Table.settle` is the operation itself, and that the proposition is a joint
  commitment is a hypothesis on the caller. It pops from the top of the Table while the top issue
  has a complete answer that the new common ground entails. Whether a common ground entails a
  complete answer is not decidable, so the operation is classical and noncomputable.

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

variable {ps : Set (Filter W)} {f : Filter W} {p : Set W} {P Q : Proposition (Set W)}

@[simp] theorem mem_project :
    f ∈ project ps P ↔ (∃ g ∈ ps, ∃ q ∈ alt P, g ⊓ 𝓟 q = f) ∧ f ≠ ⊥ := by
  simp [project]

theorem bot_notMem_project : ⊥ ∉ project ps P := fun h ↦ h.2 rfl

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

/-- Projecting the polar issue on `p` from common grounds that all entail `p` only discards the
inconsistent ones. -/
theorem project_polar_of_forall_mem (h : ∀ f ∈ ps, p ∈ f) : project ps (polar p) = ps \ {⊥} := by
  ext f
  simp only [mem_project, Set.mem_sdiff, Set.mem_singleton_iff]
  refine and_congr_left fun hf ↦ ⟨?_, fun hfp ↦ ⟨f, hfp, ?_⟩⟩
  · rintro ⟨g, hg, q, hq, rfl⟩
    have hgq : g ⊓ 𝓟 q = g := by
      by_cases hp : p = ∅ ∨ p = Set.univ
      · rcases hp with rfl | rfl
        · exact absurd (by rw [empty_mem_iff_bot.1 (h g hg), bot_inf_eq]) hf
        · rw [polar_univ, alt_top] at hq
          rw [hq, principal_univ, inf_top_eq]
      · rcases (mem_alt_polar_of_nontrivial (not_or.1 hp).1 (not_or.1 hp).2 q).1 hq with rfl | rfl
        · exact inf_eq_left.2 (le_principal_iff.2 (h g hg))
        · exact absurd (inf_principal_eq_bot.2 (by rw [compl_compl]; exact h g hg)) hf
    rwa [hgq]
  · by_cases hp : p = ∅ ∨ p = Set.univ
    · rcases hp with rfl | rfl
      · exact absurd (empty_mem_iff_bot.1 (h f hfp)) hf
      · exact ⟨Set.univ, by rw [polar_univ, alt_top]; rfl, by rw [principal_univ, inf_top_eq]⟩
    · exact ⟨p, (mem_alt_polar_of_nontrivial (not_or.1 hp).1 (not_or.1 hp).2 p).2 (.inl rfl),
        inf_eq_left.2 (le_principal_iff.2 (h f hfp))⟩

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

/-! ### Contexts -/

/-- The initial context has nothing on the Table, no commitments, and the trivial common ground. -/
@[simps] def empty : Table A W := ⟨[], ∅, ⊤⟩

/-- Place an issue on the Table. -/
@[simps] def push : Table A W := { K with stack := P :: K.stack }

/-- Commit `a` to `p`. -/
@[simps] def commit : Table A W := { K with commitments := insert (a, p) K.commitments }

/-! ### The projected set -/

/-- The projected set consists of the common grounds that canonically settle what is at issue,
rebuilt from the common ground by the issues on the Table, oldest first. -/
def projectedSet : Set (Filter W) := K.stack.foldr (fun P ps ↦ project ps P) {K.commonGround}

@[simp] theorem projectedSet_empty : (empty : Table A W).projectedSet = {⊤} := rfl

@[simp] theorem projectedSet_push : (K.push P).projectedSet = project K.projectedSet P := rfl

@[simp] theorem projectedSet_commit : (K.commit a p).projectedSet = K.projectedSet := rfl

section

variable {K a p P} {f : Filter W}

theorem projectedSet_of_stack_eq_nil (h : K.stack = []) : K.projectedSet = {K.commonGround} := by
  rw [projectedSet, h, List.foldr_nil]

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

/-- A polar question and its negative counterpart place the same issue on the Table. -/
@[simp] theorem polarQuestion_compl : K.polarQuestion pᶜ = K.polarQuestion p := by
  rw [polarQuestion, polar_compl, polarQuestion]

@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet = project K.projectedSet (ofSet p) := rfl

@[simp] theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet = project K.projectedSet (polar p) := rfl

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
theorem stack_settle_of_stack_eq_nil (h : K.stack = []) : (K.settle p).stack = [] :=
  congrArg (List.dropWhile _) h

/-- M' strips the shared proposition from every commitment list. -/
theorem contents_commitments_settle :
    (K.settle p).commitments.contents a = K.commitments.contents a \ {p} := by
  ext
  simp [State.contents]

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

variable {K p} in
/-- Reaching a projected common ground empties the Table. -/
theorem stack_settle_eq_nil_of_mem_projectedSet (h : K.commonGround ⊓ 𝓟 p ∈ K.projectedSet) :
    (K.settle p).stack = [] := by
  classical
  rw [stack_settle, List.dropWhile_eq_nil_iff]
  exact fun P hP ↦ decide_eq_true (decidedBy_of_mem_projectedSet_of_mem_stack h hP)

end Table

end Commitment
