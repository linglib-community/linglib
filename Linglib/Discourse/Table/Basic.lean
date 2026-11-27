module

public import Linglib.Discourse.Commitment.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.Set.Sups
public import Mathlib.Order.Filter.Basic

/-!
# The Table

A *Table* is the state of a conversation in the model of Farkas and Bruce. It has a stack of the
items under discussion, the most recent first, the propositions each participant is publicly
committed to, and the common ground. The common ground is a filter on the set of worlds: the
propositions that follow from what the participants jointly accept.

What an item is depends on the account. It may be a set of propositions, an inquisitive
proposition, or a sentence with its denotation. The type `I` of items is a parameter, and the
operations that read an item take a function `ans : I → Set (Set W)` giving its complete answers.

Each item narrows the futures of the conversation to those in which one of its answers is
accepted. The *projected set* collects these futures. From a common ground `f`, an item with
answers `H` contributes the consistent filters `f ⊓ 𝓟 q` for `q ∈ H`, and the items on the stack
are taken in turn. For example, if the only item has answers `{p, pᶜ}` and both are consistent
with `f`, the projected set is `{f ⊓ 𝓟 p, f ⊓ 𝓟 pᶜ}`.

## Main definitions

* `Table A W I`: a Table with participants `A`, worlds `W` and items `I`.
* `Table.project ps H`: the consistent filters `f ⊓ 𝓟 q` with `f ∈ ps` and `q ∈ H`.
* `Table.projectedSet K ans`: the projected set of `K`.
* `Table.settle K ans p`: `p` enters the common ground and leaves the commitment lists, and the
  items one of whose answers now follows are removed from the top of the stack.
* `Table.assert K a p`: `a` commits to `p`, and the item `{p}` is placed on the stack.
* `Table.polarQuestion K p`: the item `{p, pᶜ}` is placed on the stack.

## Main results

* `Table.exists_le_mem_projectedSet_iff`: a consistent filter refines a member of the projected
  set if and only if it refines the common ground and contains an answer of every item.
* `Table.projectedSet_congr_perm`: the projected set does not depend on the order of the stack.
* `Table.stack_settle_eq_nil_of_mem_projectedSet`: if settling `p` gives a common ground that is
  a member of the projected set, the stack becomes empty.

## Implementation notes

The projected set is determined by the common ground and the stack, so it is computed from them
and is not a field. The projection is the pointwise infimum of two families of filters with `⊥`
removed, which makes it commutative.

The answers of an item are an argument of the operations, not a field of the structure or an
instance on the type of items, so that one type of items can be read in more than one way.

A proposition follows from the common ground when it belongs to the filter, so every necessary
proposition follows from every common ground. A commitment list is a set of propositions and not
a filter, because settling removes a proposition from it.

Settling does not check that every participant is committed to the proposition. Whether the
common ground contains an answer of an item is not decidable, so settling is noncomputable.

## References

* [farkas-bruce-2010]
* [gunlogson-2001]
-/

@[expose] public section

open Filter

namespace Commitment

open scoped SetFamily SetRel

/-- A **Table** is the state of a conversation: a stack of the items under discussion, the discourse
commitments of the participants, and the common ground ([farkas-bruce-2010]). -/
@[ext]
structure Table (A W I : Type*) where
  /-- The items under discussion, the most recent first. -/
  stack : List I
  /-- The propositions each participant is publicly committed to that are not joint commitments. -/
  commitments : State A W
  /-- The common ground, the filter of propositions that follow from the joint commitments. -/
  commonGround : Filter W

initialize_simps_projections Table (as_prefix stack, as_prefix commitments, as_prefix commonGround)

namespace Table

variable {A W I : Type*}

/-! ### Projecting a set of answers -/

/-- The **projection** of the answers `H` from the common grounds `ps` is the set of consistent
filters `f ⊓ 𝓟 q` with `f ∈ ps` and `q ∈ H`. -/
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

/-- Removing `⊥` from the common grounds does not change their projection. -/
@[simp] theorem project_sdiff_bot : project (ps \ {⊥}) H = project ps H := by
  ext f
  simp only [mem_project, Set.mem_sdiff, Set.mem_singleton_iff]
  refine and_congr_left fun hf ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hg.1, h⟩, fun ⟨g, hg, q, hq, e⟩ ↦
    ⟨g, ⟨hg, ?_⟩, q, hq, e⟩⟩
  rintro rfl
  exact hf (by simpa using e.symm)

/-- Projecting two sets of answers in either order gives the same common grounds. -/
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

/-- If every member of `ps` contains `p`, the projection of `{p, pᶜ}` from `ps` is `ps` without `⊥`.
-/
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

/-- The **empty** Table has no items, no commitments, and the common ground `⊤`. -/
@[simps] def empty : Table A W I := ⟨[], ∅, ⊤⟩

/-- `K.push i` is `K` with the item `i` on top of the stack. -/
@[simps] def push : Table A W I := { K with stack := i :: K.stack }

/-- `K.commit a p` is `K` with `p` added to the commitments of `a`. -/
@[simps] def commit : Table A W I := { K with commitments := insert (a, p) K.commitments }

/-! ### The projected set -/

/-- The **projected set** of `K` is obtained from the common ground of `K` by projecting the answers
of each item on the stack, the oldest first. -/
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

/-- Two Tables with the same common ground whose stacks are permutations of each other have the same
projected set. -/
theorem projectedSet_congr_perm {L : Table A W I} (hs : K.stack.Perm L.stack)
    (hc : K.commonGround = L.commonGround) : K.projectedSet ans = L.projectedSet ans := by
  have : LeftCommutative fun (i : I) (ps : Set (Filter W)) ↦ project ps (ans i) :=
    ⟨fun _ _ _ ↦ project_right_comm⟩
  rw [projectedSet, projectedSet, hc]
  exact hs.foldr_eq _

/-- Every member of the projected set refines the common ground. -/
theorem le_commonGround_of_mem_projectedSet (h : f ∈ K.projectedSet ans) :
    f ≤ K.commonGround := by
  obtain ⟨T, C, cg⟩ := K
  induction T generalizing f with
  | nil => exact le_of_eq h
  | cons j T ih =>
    obtain ⟨g, hg, hfg⟩ := exists_le_of_mem_project h
    exact hfg.trans (ih hg)

/-- Every member of the projected set contains an answer of every item on the stack. -/
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

/-- A consistent filter refines a member of the projected set if and only if it refines the common
ground and contains an answer of every item on the stack. -/
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
/-- **Settling** `p` in `K` adds `p` to the common ground, removes `p` from every commitment list,
and removes items from the top of the stack while the new common ground contains one of their
answers ([farkas-bruce-2010] (17)). -/
@[simps] noncomputable def settle : Table A W I where
  stack := K.stack.dropWhile fun i ↦ decide (∃ q ∈ ans i, q ∈ K.commonGround ⊓ 𝓟 p)
  commitments := {(a, q) | a ~[K.commitments] q ∧ q ≠ p}
  commonGround := K.commonGround ⊓ 𝓟 p

variable {K} in
theorem stack_settle_of_stack_eq_nil (h : K.stack = []) : (K.settle ans p).stack = [] :=
  congrArg (List.dropWhile _) h

/-- Settling `p` removes `p` from the commitments of every participant. -/
theorem contents_commitments_settle :
    (K.settle ans p).commitments.contents a = K.commitments.contents a \ {p} := by
  ext
  simp [State.contents]

variable {K ans p i} in
/-- If the common ground after settling `p` contains an answer of `i`, settling `p` in `K.push i`
gives the same Table as settling `p` in `K`. -/
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
/-- If the common ground after settling `p` is a member of the projected set, the stack after
settling `p` is empty. -/
theorem stack_settle_eq_nil_of_mem_projectedSet
    (h : K.commonGround ⊓ 𝓟 p ∈ K.projectedSet ans) : (K.settle ans p).stack = [] := by
  classical
  rw [stack_settle, List.dropWhile_eq_nil_iff]
  exact fun i hi ↦ decide_eq_true (exists_mem_of_mem_projectedSet_of_mem_stack h hi)

end

/-! ### Assertions and polar questions -/

section Hamblin

variable (K : Table A W (Set (Set W))) (ans : Set (Set W) → Set (Set W)) (a : A) (p : Set W)

/-- The **assertion** of `p` by `a` adds `p` to the commitments of `a` and places the item `{p}` on
the stack ([farkas-bruce-2010] (9)). -/
@[simps!] def assert : Table A W (Set (Set W)) := (K.commit a p).push {p}

/-- The **polar question** on `p` places the item `{p, pᶜ}` on the stack ([farkas-bruce-2010] (12)).
-/
@[simps!] def polarQuestion : Table A W (Set (Set W)) := K.push {p, pᶜ}

/-- The polar questions on `p` and on `pᶜ` are equal. -/
@[simp] theorem polarQuestion_compl : K.polarQuestion pᶜ = K.polarQuestion p := by
  rw [polarQuestion, compl_compl, Set.pair_comm, polarQuestion]

@[simp] theorem projectedSet_assert :
    (K.assert a p).projectedSet ans = project (K.projectedSet ans) (ans {p}) := rfl

@[simp] theorem projectedSet_polarQuestion :
    (K.polarQuestion p).projectedSet ans = project (K.projectedSet ans) (ans {p, pᶜ}) := rfl

end Hamblin

end Table

end Commitment
