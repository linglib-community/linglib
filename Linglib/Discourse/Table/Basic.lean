module

public import Linglib.Discourse.Commitment.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Set.Sups
public import Mathlib.Order.Filter.Basic

/-!
# The Table

The context structure of Farkas and Bruce records the participants' discourse commitments, the
common ground, and the Table, a stack of the items under discussion with the most recent on top.
What an item is depends on the account: a set of propositions, an inquisitive proposition, or a
sentence with its denotation. The structure takes the type of items as a parameter, and what it
needs of an item is the set of its complete answers, given as a function `ans : I → Set (Set W)`.

A set `H` of answers projects, from a set `ps` of common grounds, the consistent common grounds
`f ⊓ 𝓟 q` with `f ∈ ps` and `q ∈ H`. The projected set of a context is obtained from its common
ground by projecting the answers of each item on the Table in turn. Its members are the weakest
consistent bodies of information that refine the common ground and entail an answer of every
item, and it does not depend on the order of the stack. Once a proposition is a joint commitment
it enters the common ground by Stalnaker's update `f ⊓ 𝓟 p`, and the items one of whose answers
the new common ground entails leave the Table.

## Main definitions

* `Commitment.Table A W I`: the context structure, with participants `A`, worlds `W` and items `I`.
* `Commitment.Table.project`: the projection of a set of answers from a set of common grounds.
* `Commitment.Table.projectedSet`: the projected set of a context.
* `Commitment.Table.settle`: the operation that turns a joint commitment into common ground.
* `Commitment.Table.assert`, `Commitment.Table.polarQuestion`: the default assertion, which commits
  its author as in Gunlogson, and the default polar question, on items that are sets of
  propositions.

## Main results

* `Commitment.Table.exists_le_mem_projectedSet_iff`: the consistent bodies of information that
  refine the common ground and entail an answer of every item on the Table are those that refine
  a projected common ground.
* `Commitment.Table.project_right_comm`, `Commitment.Table.projectedSet_congr_perm`: projection
  does not depend on the order of the items.
* `Commitment.Table.stack_settle_eq_nil_of_mem_projectedSet`: reaching a projected common ground
  empties the Table.

## Implementation notes

* The projected set can always be rebuilt from the common ground and the Table, so it is derived
  rather than stored. The projection is the pointwise infimum `ps ⊼ 𝓟 '' H` of two families of
  filters with `⊥` removed, so that its commutativity is that of `⊼`.
* The answers of an item are an argument of the operations that read them and not a field of the
  structure or an instance on the type of items, so that one type of items can be read in more
  than one way.
* A common ground is a filter of propositions, so a proposition follows from it when it belongs
  to the filter. Every necessary proposition then follows from every common ground; a finer
  consequence relation is not represented. A discourse commitment list is a set of propositions,
  from which a proposition can be removed.
* The common-ground increasing operation applies once the proposition is on every commitment
  list; `Commitment.Table.settle` is the operation itself, and that the proposition is a joint
  commitment is a hypothesis on the caller. It pops from the top of the Table while the new
  common ground entails an answer of the top item. Whether it does is not decidable, so the
  operation is classical and noncomputable.

## References

* [farkas-bruce-2010]
* [gunlogson-2001]
-/

@[expose] public section

open Filter

namespace Commitment

open scoped SetFamily SetRel

/-- The context structure `K` of [farkas-bruce-2010] consists of the Table as a stack of items,
the participants' discourse commitments, and the common ground. -/
@[ext]
structure Table (A W I : Type*) where
  /-- The Table: the items under discussion, the most recent first. -/
  stack : List I
  /-- The discourse commitments of the participants that are not joint commitments. -/
  commitments : State A W
  /-- The common ground: the propositions that are joint commitments. -/
  commonGround : Filter W

initialize_simps_projections Table (as_prefix stack, as_prefix commitments, as_prefix commonGround)

namespace Table

variable {A W I : Type*}

/-! ### Projecting a set of answers -/

/-- The projection of the answers `H` from the common grounds `ps` adds each answer to each member
of `ps` and discards the inconsistent results. -/
def project (ps : Set (Filter W)) (H : Set (Set W)) : Set (Filter W) :=
  (ps ⊼ 𝓟 '' H) \ {⊥}

section Project

variable {ps : Set (Filter W)} {f : Filter W} {p q : Set W} {H H' : Set (Set W)}

@[simp] theorem mem_project :
    f ∈ project ps H ↔ (∃ g ∈ ps, ∃ q ∈ H, g ⊓ 𝓟 q = f) ∧ f ≠ ⊥ := by
  simp [project]

theorem bot_notMem_project : ⊥ ∉ project ps H := fun h ↦ h.2 rfl

theorem exists_le_of_mem_project (h : f ∈ project ps H) : ∃ g ∈ ps, f ≤ g :=
  let ⟨g, hg, _, _, e⟩ := (mem_project.1 h).1
  ⟨g, hg, e ▸ inf_le_left⟩

theorem exists_mem_of_mem_project (h : f ∈ project ps H) : ∃ q ∈ H, q ∈ f :=
  let ⟨_, _, q, hq, e⟩ := (mem_project.1 h).1
  ⟨q, hq, e ▸ mem_inf_of_right (mem_principal_self q)⟩

/-- Discarding the inconsistent common grounds before projecting changes nothing. -/
@[simp] theorem project_sdiff_bot : project (ps \ {⊥}) H = project ps H := by
  ext f
  simp only [mem_project, Set.mem_sdiff, Set.mem_singleton_iff]
  refine and_congr_left fun hf ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hg.1, h⟩, fun ⟨g, hg, q, hq, e⟩ ↦
    ⟨g, ⟨hg, ?_⟩, q, hq, e⟩⟩
  rintro rfl
  exact hf (by simpa using e.symm)

/-- Two sets of answers project the same common grounds in either order. -/
theorem project_right_comm : project (project ps H) H' = project (project ps H') H := by
  have h (H H' : Set (Set W)) :
      project (project ps H) H' = (ps ⊼ 𝓟 '' H ⊼ 𝓟 '' H') \ {⊥} := project_sdiff_bot
  rw [h, h, Set.infs_right_comm]

theorem project_singleton (h : f ⊓ 𝓟 p ≠ ⊥) : project {f} {p} = {f ⊓ 𝓟 p} := by
  rw [project, Set.image_singleton, Set.singleton_infs_singleton,
    Set.sdiff_singleton_eq_self (Set.notMem_singleton_iff.2 h.symm)]

theorem project_pair (hp : f ⊓ 𝓟 p ≠ ⊥) (hq : f ⊓ 𝓟 q ≠ ⊥) :
    project {f} {p, q} = {f ⊓ 𝓟 p, f ⊓ 𝓟 q} := by
  rw [project, Set.image_pair, Set.singleton_infs, Set.image_pair,
    Set.sdiff_singleton_eq_self (by simp [hp.symm, hq.symm])]

/-- Projecting `p` and `pᶜ` from common grounds that all entail `p` only discards the inconsistent
ones. -/
theorem project_pair_compl_of_forall_mem (h : ∀ f ∈ ps, p ∈ f) :
    project ps {p, pᶜ} = ps \ {⊥} := by
  ext f
  simp only [mem_project, Set.mem_sdiff, Set.mem_singleton_iff]
  refine and_congr_left fun hf ↦ ⟨?_, fun hfp ↦
    ⟨f, hfp, p, Set.mem_insert _ _, inf_eq_left.2 (le_principal_iff.2 (h f hfp))⟩⟩
  rintro ⟨g, hg, q, hq, rfl⟩
  rcases Set.mem_insert_iff.1 hq with rfl | hq
  · rwa [inf_eq_left.2 (le_principal_iff.2 (h g hg))]
  · rw [Set.mem_singleton_iff.1 hq] at hf
    exact absurd (inf_principal_eq_bot.2 (by rw [compl_compl]; exact h g hg)) hf

end Project

section

variable (K : Table A W I) (ans : I → Set (Set W)) (a : A) (p : Set W) (i : I)

/-! ### Contexts -/

/-- The initial context has nothing on the Table, no commitments, and the trivial common ground. -/
@[simps] def empty : Table A W I := ⟨[], ∅, ⊤⟩

/-- Place an item on the Table. -/
@[simps] def push : Table A W I := { K with stack := i :: K.stack }

/-- Commit `a` to `p`. -/
@[simps] def commit : Table A W I := { K with commitments := insert (a, p) K.commitments }

/-! ### The projected set -/

/-- The projected set consists of the common grounds that canonically settle what is at issue,
rebuilt from the common ground by the items on the Table, oldest first. -/
def projectedSet : Set (Filter W) :=
  K.stack.foldr (fun i ps ↦ project ps (ans i)) {K.commonGround}

@[simp] theorem projectedSet_empty : (empty : Table A W I).projectedSet ans = {⊤} := rfl

@[simp] theorem projectedSet_push :
    (K.push i).projectedSet ans = project (K.projectedSet ans) (ans i) := rfl

@[simp] theorem projectedSet_commit : (K.commit a p).projectedSet ans = K.projectedSet ans := rfl

section

variable {K ans a p i} {f : Filter W}

theorem projectedSet_of_stack_eq_nil (h : K.stack = []) :
    K.projectedSet ans = {K.commonGround} := by
  rw [projectedSet, h, List.foldr_nil]

/-- The projected set does not depend on the order of the items on the Table. -/
theorem projectedSet_congr_perm {L : Table A W I} (hs : K.stack.Perm L.stack)
    (hc : K.commonGround = L.commonGround) : K.projectedSet ans = L.projectedSet ans := by
  have : LeftCommutative fun (i : I) (ps : Set (Filter W)) ↦ project ps (ans i) :=
    ⟨fun _ _ _ ↦ project_right_comm⟩
  rw [projectedSet, projectedSet, hc]
  exact hs.foldr_eq _

/-- A projected common ground refines the current one. -/
theorem le_commonGround_of_mem_projectedSet (h : f ∈ K.projectedSet ans) :
    f ≤ K.commonGround := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact le_of_eq h
  | cons j T ih =>
    obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project h
    exact hfg.trans (ih hg)

/-- Every projected common ground entails an answer of every item on the Table. -/
theorem exists_mem_of_mem_projectedSet_of_mem_stack (hf : f ∈ K.projectedSet ans)
    (hi : i ∈ K.stack) : ∃ q ∈ ans i, q ∈ f := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j T ih =>
    rcases List.mem_cons.1 hi with rfl | hi
    · exact exists_mem_of_mem_project hf
    · obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project hf
      exact (ih hg hi).imp fun _ h ↦ ⟨h.1, hfg h.2⟩

/-- The consistent bodies of information that refine the common ground and entail an answer of
every item on the Table are those that refine a projected common ground. -/
theorem exists_le_mem_projectedSet_iff {g : Filter W} (hg : g ≠ ⊥) :
    (∃ f ∈ K.projectedSet ans, g ≤ f) ↔
      g ≤ K.commonGround ∧ ∀ i ∈ K.stack, ∃ q ∈ ans i, q ∈ g := by
  refine ⟨fun ⟨f, hf, hgf⟩ ↦ ⟨hgf.trans (le_commonGround_of_mem_projectedSet hf),
    fun i hi ↦ (exists_mem_of_mem_projectedSet_of_mem_stack hf hi).imp
      fun _ h ↦ ⟨h.1, hgf h.2⟩⟩, ?_⟩
  obtain ⟨T, C, cg⟩ := K
  induction T with
  | nil => exact fun h ↦ ⟨cg, rfl, h.1⟩
  | cons j T ih =>
    rintro ⟨hcg, hdec⟩
    obtain ⟨f, hf, hgf⟩ := ih ⟨hcg, fun i hi ↦ hdec i (List.mem_cons_of_mem _ hi)⟩
    obtain ⟨q, hq, hqg⟩ := hdec j List.mem_cons_self
    have hle : g ≤ f ⊓ 𝓟 q := le_inf hgf (le_principal_iff.2 hqg)
    exact ⟨f ⊓ 𝓟 q, mem_project.2 ⟨⟨f, hf, q, hq, rfl⟩, fun h ↦ hg (le_bot_iff.1 (h ▸ hle))⟩, hle⟩

end

/-! ### Settling a joint commitment -/

open scoped Classical in
/-- In the common-ground increasing operation M' (17), applied once `p` is on every commitment
list, `p` enters the common ground and leaves the individual commitment lists, and the items one
of whose answers the new common ground entails are popped from the top of the Table. -/
@[simps] noncomputable def settle : Table A W I where
  stack := K.stack.dropWhile fun i ↦ decide (∃ q ∈ ans i, q ∈ K.commonGround ⊓ 𝓟 p)
  commitments := {(a, q) | a ~[K.commitments] q ∧ q ≠ p}
  commonGround := K.commonGround ⊓ 𝓟 p

variable {K} in
theorem stack_settle_of_stack_eq_nil (h : K.stack = []) : (K.settle ans p).stack = [] :=
  congrArg (List.dropWhile _) h

/-- M' strips the shared proposition from every commitment list. -/
theorem contents_commitments_settle :
    (K.settle ans p).commitments.contents a = K.commitments.contents a \ {p} := by
  ext
  simp [State.contents]

variable {K ans p i} in
/-- M' pops an item one of whose answers is entailed and goes on popping. -/
theorem settle_push_of_exists_mem (h : ∃ q ∈ ans i, q ∈ K.commonGround ⊓ 𝓟 p) :
    (K.push i).settle ans p = K.settle ans p :=
  Table.ext (by
    rw [stack_settle, stack_push, List.dropWhile_cons_of_pos (by simpa using h)]
    rfl) rfl rfl

variable {K ans p i} in
theorem stack_settle_push_of_not_exists_mem (h : ¬ ∃ q ∈ ans i, q ∈ K.commonGround ⊓ 𝓟 p) :
    ((K.push i).settle ans p).stack = i :: K.stack := by
  simpa using h

theorem settle_commit_self : (K.commit a p).settle ans p = K.settle ans p :=
  Table.ext rfl (Set.insert_inter_of_notMem (t := {q : A × Set W | q.2 ≠ p}) (not_not.2 rfl)) rfl

variable {K ans p} in
/-- Reaching a projected common ground empties the Table. -/
theorem stack_settle_eq_nil_of_mem_projectedSet
    (h : K.commonGround ⊓ 𝓟 p ∈ K.projectedSet ans) : (K.settle ans p).stack = [] := by
  classical
  rw [stack_settle, List.dropWhile_eq_nil_iff]
  exact fun i hi ↦ decide_eq_true (exists_mem_of_mem_projectedSet_of_mem_stack h hi)

end

/-! ### Assertions and polar questions -/

section Hamblin

variable (K : Table A W (Set (Set W))) (ans : Set (Set W) → Set (Set W)) (a : A) (p : Set W)

/-- In the default assertion (9), `a` commits to `p` and places `{p}` on the Table. -/
@[simps!] def assert : Table A W (Set (Set W)) := (K.commit a p).push {p}

/-- The default polar question (12) places `{p, pᶜ}` on the Table. -/
@[simps!] def polarQuestion : Table A W (Set (Set W)) := K.push {p, pᶜ}

/-- A polar question and its negative counterpart place the same item on the Table. -/
@[simp] theorem polarQuestion_compl : K.polarQuestion pᶜ = K.polarQuestion p := by
  rw [polarQuestion, compl_compl, Set.pair_comm, polarQuestion]

@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet ans = project (K.projectedSet ans) (ans {p}) := rfl

@[simp] theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet ans = project (K.projectedSet ans) (ans {p, pᶜ}) := rfl

end Hamblin

end Table

end Commitment
