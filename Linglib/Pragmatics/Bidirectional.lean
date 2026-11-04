module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.Family
public import Linglib.Core.Order.WellFoundedSet

/-!
# Bidirectional Optimality Theory

Bidirectional optimality theory evaluates a form-meaning pair of a generator from the speaker's and
the hearer's side at once: a more harmonic pair blocks it when it shares its meaning (the
Q-principle) or its form (the I-principle). Strong bidirection keeps the pairs no pair of the
generator blocks. Weak bidirection keeps those no surviving pair blocks, as a mutual recursion of
the two principles, `IsWeakSolution`, or as a fixed point, `superoptimalSet`. Well-founded harmonies
make [the first](##IsWeakSolution.unique) and [the second](##eq_superoptimalSet_of_isFixedPt)
unique, and [transitivity makes them coincide](##IsWeakSolution.inter_eq_superoptimalSet). The fixed
point is [built in stages](##iUnion_stage), [finitely many](##stage_eq_superoptimalSet_of_encard_le)
for finitely many harmonies, and on a generator containing the graph of an isomorphism of markedness
orders it [is that graph](##superoptimalSet_eq_graphOn), the division of pragmatic labour.

## Implementation notes

* Harmony is any `LT` reached through `f`, with transitivity and totality assumed only where a
  theorem uses them. An OT system's harmony is `OptimalityTheory.ViolationProfile.ofList`, whose
  order is well-founded on any generator. The principles' "other pair" clause is dropped when
  `f q < f p` forces `q ≠ p`.
* The `Finset` form iterates the squared step from `pairs` with `pairs.card` as fuel and an early
  exit, so it needs no convergence hypothesis and `decide` stays shallow.

## References

* [blutner-2000]
* [jaeger-2002]
* [horn-1984]
* [atlas-levinson-1981]
-/

@[expose] public section

namespace BidirectionalOT

open Function
open OrderHom hiding id

universe u v

variable {F : Type u} {M : Type v} {α : Type*}

/-! ### Blocking -/

section Blocks

variable [LT α] (f : F × M → α) (S : Set (F × M)) (p : F × M)

/-- `QBlocks f S p` holds when a more harmonic pair of `S` expresses `p`'s meaning. -/
def QBlocks : Prop := ∃ q ∈ S, q.2 = p.2 ∧ f q < f p

/-- `IBlocks f S p` holds when a more harmonic pair of `S` interprets `p`'s form. -/
def IBlocks : Prop := ∃ q ∈ S, q.1 = p.1 ∧ f q < f p

/-- `Blocks f S p` holds when a more harmonic pair of `S` shares `p`'s form or meaning. -/
def Blocks : Prop := ∃ q ∈ S, (q.1 = p.1 ∨ q.2 = p.2) ∧ f q < f p

theorem blocks_iff : Blocks f S p ↔ IBlocks f S p ∨ QBlocks f S p := by
  simp only [Blocks, IBlocks, QBlocks, or_and_right, exists_or, and_or_left]

variable {f S p} {T : Set (F × M)}

theorem QBlocks.mono (hST : S ⊆ T) : QBlocks f S p → QBlocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

theorem IBlocks.mono (hST : S ⊆ T) : IBlocks f S p → IBlocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

theorem Blocks.mono (hST : S ⊆ T) : Blocks f S p → Blocks f T p :=
  fun ⟨q, hq, h⟩ ↦ ⟨q, hST hq, h⟩

variable [DecidableLT α] (f) (S : Finset (F × M)) (p)

instance [DecidableEq M] : Decidable (QBlocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, q.2 = p.2 ∧ f q < f p) Iff.rfl

instance [DecidableEq F] : Decidable (IBlocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, q.1 = p.1 ∧ f q < f p) Iff.rfl

instance [DecidableEq F] [DecidableEq M] : Decidable (Blocks f ↑S p) :=
  decidable_of_iff (∃ q ∈ S, (q.1 = p.1 ∨ q.2 = p.2) ∧ f q < f p) Iff.rfl

end Blocks

/-! ### The blocking step and its fixed points -/

section Step

variable [LT α] (pairs : Set (F × M)) (f : F × M → α) {S : Set (F × M)} {p : F × M}

/-- The pairs of `pairs` that `S` does not block. Antitone in `S`. -/
def unblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ Blocks f S p}

@[simp] theorem mem_unblockedSet : p ∈ unblockedSet pairs f S ↔ p ∈ pairs ∧ ¬ Blocks f S p :=
  Iff.rfl

theorem unblockedSet_subset : unblockedSet pairs f S ⊆ pairs := fun _ hp ↦ hp.1

theorem unblockedSet_antitone : Antitone (unblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

/-- Strong bidirection keeps the pairs that no pair of `pairs` blocks. -/
def strongOptimalSet : Set (F × M) := unblockedSet pairs f pairs

/-- The square of the blocking step, monotone as the composite of two antitone maps. -/
def unblockedSq : Set (F × M) →o Set (F × M) :=
  ⟨unblockedSet pairs f ∘ unblockedSet pairs f,
    (unblockedSet_antitone pairs f).comp (unblockedSet_antitone pairs f)⟩

@[simp] theorem unblockedSq_apply (S : Set (F × M)) :
    unblockedSq pairs f S = unblockedSet pairs f (unblockedSet pairs f S) := rfl

/-- The super-optimal pairs, the greatest fixed point of the squared blocking step. When the
harmonies of the generator are well-founded it is the unique fixed point of the step itself
(`isFixedPt_superoptimalSet`, `eq_superoptimalSet_of_isFixedPt`), Jäger's reformulation. -/
noncomputable def superoptimalSet : Set (F × M) := (unblockedSq pairs f).gfp

theorem superoptimalSet_subset : superoptimalSet pairs f ⊆ pairs := by
  rw [superoptimalSet, ← (unblockedSq pairs f).map_gfp]
  exact unblockedSet_subset _ _

/-- Optimal pairs are super-optimal, since `strongOptimalSet` is a post-fixed point of the
squared step, since the step is antitone and lands in `pairs`. -/
theorem strongOptimalSet_subset_superoptimalSet :
    strongOptimalSet pairs f ⊆ superoptimalSet pairs f :=
  le_gfp _ (unblockedSet_antitone pairs f (unblockedSet_subset pairs f))

theorem unblockedSet_superoptimalSet :
    unblockedSet pairs f (superoptimalSet pairs f) = (unblockedSq pairs f).lfp := by
  have hfix : ∀ S, unblockedSq pairs f S = S →
      unblockedSq pairs f (unblockedSet pairs f S) = unblockedSet pairs f S := fun S hS ↦ by
    change unblockedSet pairs f (unblockedSq pairs f S) = _
    rw [hS]
  refine le_antisymm ?_ (lfp_le_fixed _ (hfix _ (unblockedSq pairs f).map_gfp))
  calc unblockedSet pairs f (superoptimalSet pairs f)
      ≤ unblockedSet pairs f (unblockedSet pairs f (unblockedSq pairs f).lfp) :=
        unblockedSet_antitone pairs f (le_gfp _ (hfix _ (unblockedSq pairs f).map_lfp).ge)
    _ = (unblockedSq pairs f).lfp := (unblockedSq pairs f).map_lfp

theorem lfp_eq_superoptimalSet (h : (f '' pairs).IsWF) :
    (unblockedSq pairs f).lfp = superoptimalSet pairs f := by
  set G := superoptimalSet pairs f
  set L := (unblockedSq pairs f).lfp
  have hGL : unblockedSet pairs f G = L := unblockedSet_superoptimalSet pairs f
  have hLG : unblockedSet pairs f L = G := by rw [← hGL]; exact (unblockedSq pairs f).map_gfp
  refine le_antisymm (lfp_le_gfp _) (not_not.1 fun hne ↦ ?_)
  obtain ⟨p, ⟨hpG, hpL⟩, hmin⟩ := (h.mono (Set.image_mono fun x hx ↦
    superoptimalSet_subset pairs f hx.1)).exists_forall_not_lt (s := G \ L)
      (Set.not_subset.1 hne)
  have hp : p ∈ unblockedSet pairs f L := hLG.symm ▸ hpG
  obtain ⟨q, hqG, hadj, hlt⟩ : Blocks f G p :=
    not_not.1 fun hb ↦ hpL (hGL ▸ (⟨hp.1, hb⟩ : p ∈ unblockedSet pairs f G))
  exact hmin q ⟨hqG, fun hqL ↦ hp.2 ⟨q, hqL, hadj, hlt⟩⟩ hlt

theorem isFixedPt_superoptimalSet (h : (f '' pairs).IsWF) :
    IsFixedPt (unblockedSet pairs f) (superoptimalSet pairs f) := by
  rw [IsFixedPt, unblockedSet_superoptimalSet, lfp_eq_superoptimalSet pairs f h]

/-- A pair is super-optimal iff it lies in the generator and no super-optimal pair blocks it,
Jäger's reformulation of super-optimality. -/
theorem mem_superoptimalSet (h : (f '' pairs).IsWF) :
    p ∈ superoptimalSet pairs f ↔ p ∈ pairs ∧ ¬ Blocks f (superoptimalSet pairs f) p := by
  conv_lhs => rw [← (isFixedPt_superoptimalSet pairs f h).eq]
  exact Iff.rfl

theorem eq_superoptimalSet_of_isFixedPt (h : (f '' pairs).IsWF)
    (hS : IsFixedPt (unblockedSet pairs f) S) : S = superoptimalSet pairs f := by
  have hsq : unblockedSq pairs f S = S := by
    change unblockedSet pairs f (unblockedSet pairs f S) = S
    rw [hS.eq, hS.eq]
  exact le_antisymm (le_gfp _ hsq.ge)
    ((lfp_eq_superoptimalSet pairs f h).symm.trans_le (lfp_le_fixed _ hsq))

end Step

/-! ### Blutner's mutual recursion -/

section Weak

variable [LT α] (pairs : Set (F × M)) (f : F × M → α)

/-- The pairs of `pairs` that `S` does not Q-block. -/
def qUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ QBlocks f S p}

/-- The pairs of `pairs` that `S` does not I-block. -/
def iUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ IBlocks f S p}

@[simp] theorem mem_qUnblockedSet {S : Set (F × M)} {p : F × M} :
    p ∈ qUnblockedSet pairs f S ↔ p ∈ pairs ∧ ¬ QBlocks f S p := Iff.rfl

@[simp] theorem mem_iUnblockedSet {S : Set (F × M)} {p : F × M} :
    p ∈ iUnblockedSet pairs f S ↔ p ∈ pairs ∧ ¬ IBlocks f S p := Iff.rfl

theorem qUnblockedSet_antitone : Antitone (qUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

theorem iUnblockedSet_antitone : Antitone (iUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

/-- In the weak version of bidirection `Q` collects the pairs no pair of `I` Q-blocks and `I` the
pairs no pair of `Q` I-blocks. A pair of both is super-optimal when the order is transitive and the
generator's harmonies are well-founded (`inter_eq_superoptimalSet`). -/
def IsWeakSolution (Q I : Set (F × M)) : Prop :=
  qUnblockedSet pairs f I = Q ∧ iUnblockedSet pairs f Q = I

theorem exists_isWeakSolution : ∃ Q I, IsWeakSolution pairs f Q I :=
  let Φ : Set (F × M) →o Set (F × M) :=
    ⟨qUnblockedSet pairs f ∘ iUnblockedSet pairs f,
      (qUnblockedSet_antitone pairs f).comp (iUnblockedSet_antitone pairs f)⟩
  ⟨Φ.gfp, iUnblockedSet pairs f Φ.gfp, Φ.map_gfp, rfl⟩

namespace IsWeakSolution

variable {pairs f} {Q I Q' I' : Set (F × M)} {p : F × M}

theorem mem_left (h : IsWeakSolution pairs f Q I) : p ∈ Q ↔ p ∈ pairs ∧ ¬ QBlocks f I p := by
  rw [← h.1, mem_qUnblockedSet]

theorem mem_right (h : IsWeakSolution pairs f Q I) : p ∈ I ↔ p ∈ pairs ∧ ¬ IBlocks f Q p := by
  rw [← h.2, mem_iUnblockedSet]

theorem left_subset (h : IsWeakSolution pairs f Q I) : Q ⊆ pairs := fun _ hx ↦ (h.mem_left.1 hx).1

theorem right_subset (h : IsWeakSolution pairs f Q I) : I ⊆ pairs := fun _ hx ↦ (h.mem_right.1 hx).1

theorem strongOptimalSet_subset_inter (h : IsWeakSolution pairs f Q I) :
    strongOptimalSet pairs f ⊆ Q ∩ I := fun _ hp ↦
  ⟨h.mem_left.2 ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inr (hb.mono h.right_subset)))⟩,
    h.mem_right.2 ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inl (hb.mono h.left_subset)))⟩⟩

/-- With well-founded generator harmonies, the mutual recursion has at most one solution: a
disagreement minimal in harmony is decided by the agreement below it. -/
theorem unique (hf : (f '' pairs).IsWF) (h : IsWeakSolution pairs f Q I)
    (h' : IsWeakSolution pairs f Q' I') : Q = Q' ∧ I = I' := by
  suffices hall : ∀ p, (p ∈ Q ↔ p ∈ Q') ∧ (p ∈ I ↔ p ∈ I') from
    ⟨Set.ext fun p ↦ (hall p).1, Set.ext fun p ↦ (hall p).2⟩
  by_contra hne
  have hD : {p | ¬ ((p ∈ Q ↔ p ∈ Q') ∧ (p ∈ I ↔ p ∈ I'))}.Nonempty := not_forall.1 hne
  have hDp : {p | ¬ ((p ∈ Q ↔ p ∈ Q') ∧ (p ∈ I ↔ p ∈ I'))} ⊆ pairs := fun p hp ↦
    by_contra fun hpG ↦ hp ⟨by simp [h.mem_left, h'.mem_left, hpG],
      by simp [h.mem_right, h'.mem_right, hpG]⟩
  obtain ⟨p, hp, hmin⟩ := (hf.mono (Set.image_mono hDp)).exists_forall_not_lt hD
  have hbelow : ∀ q, f q < f p → (q ∈ Q ↔ q ∈ Q') ∧ (q ∈ I ↔ q ∈ I') :=
    fun q hq ↦ not_not.1 fun hn ↦ hmin q hn hq
  have hQb : QBlocks f I p ↔ QBlocks f I' p := exists_congr fun q ↦
    ⟨fun ⟨a, b, c⟩ ↦ ⟨(hbelow q c).2.1 a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨(hbelow q c).2.2 a, b, c⟩⟩
  have hIb : IBlocks f Q p ↔ IBlocks f Q' p := exists_congr fun q ↦
    ⟨fun ⟨a, b, c⟩ ↦ ⟨(hbelow q c).1.1 a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨(hbelow q c).1.2 a, b, c⟩⟩
  exact hp ⟨by rw [h.mem_left, h'.mem_left, hQb], by rw [h.mem_right, h'.mem_right, hIb]⟩

variable [IsTrans α (· < ·)]

/-- Along the form axis, `Q` and `Q ∩ I` block the same pairs: a blocker in `Q` minimal in harmony
cannot itself be I-blocked by `Q`, since a blocker of a blocker is, by transitivity, a blocker. -/
theorem iBlocks_inter_iff (hf : (f '' pairs).IsWF) (h : IsWeakSolution pairs f Q I) :
    IBlocks f (Q ∩ I) p ↔ IBlocks f Q p := by
  refine ⟨.mono Set.inter_subset_left, fun hb ↦ ?_⟩
  obtain ⟨q, ⟨hqQ, hq, hqp⟩, hmin⟩ := (hf.mono (Set.image_mono fun _ hx ↦
    h.left_subset hx.1)).exists_forall_not_lt (s := {q ∈ Q | q.1 = p.1 ∧ f q < f p}) hb
  refine ⟨q, ⟨hqQ, h.mem_right.2 ⟨h.left_subset hqQ, ?_⟩⟩, hq, hqp⟩
  rintro ⟨r, hrQ, hr, hrq⟩
  exact hmin r ⟨hrQ, hr.trans hq, _root_.trans hrq hqp⟩ hrq

/-- Along the meaning axis, `I` and `Q ∩ I` block the same pairs. -/
theorem qBlocks_inter_iff (hf : (f '' pairs).IsWF) (h : IsWeakSolution pairs f Q I) :
    QBlocks f (Q ∩ I) p ↔ QBlocks f I p := by
  refine ⟨.mono Set.inter_subset_right, fun hb ↦ ?_⟩
  obtain ⟨q, ⟨hqI, hq, hqp⟩, hmin⟩ := (hf.mono (Set.image_mono fun _ hx ↦
    h.right_subset hx.1)).exists_forall_not_lt (s := {q ∈ I | q.2 = p.2 ∧ f q < f p}) hb
  refine ⟨q, ⟨h.mem_left.2 ⟨h.right_subset hqI, ?_⟩, hqI⟩, hq, hqp⟩
  rintro ⟨r, hrI, hr, hrq⟩
  exact hmin r ⟨hrI, hr.trans hq, _root_.trans hrq hqp⟩ hrq

/-- The pairs satisfying both principles are a fixed point of the blocking step. -/
theorem isFixedPt_inter (hf : (f '' pairs).IsWF) (h : IsWeakSolution pairs f Q I) :
    IsFixedPt (unblockedSet pairs f) (Q ∩ I) := by
  ext p
  simp only [mem_unblockedSet, Set.mem_inter_iff, h.mem_left, h.mem_right, blocks_iff, not_or,
    h.iBlocks_inter_iff hf, h.qBlocks_inter_iff hf]
  tauto

/-- For a transitive order with well-founded generator harmonies, the pairs satisfying both
principles of the mutual recursion are exactly the super-optimal pairs. -/
theorem inter_eq_superoptimalSet (hf : (f '' pairs).IsWF) (h : IsWeakSolution pairs f Q I) :
    Q ∩ I = superoptimalSet pairs f :=
  eq_superoptimalSet_of_isFixedPt pairs f hf (h.isFixedPt_inter hf)

end IsWeakSolution

end Weak

/-! ### Stages

The cumulative construction of the super-optimal pairs, the `transfiniteIterate` of a step adding
the most harmonic of the remaining pairs. The step is not monotone, so `OrdinalApprox` does not
apply to it. -/

section Stages

section Defs

variable (pairs : Set (F × M))

/-- The pairs of `pairs` sharing no component with a pair of `X`. -/
def remaining (X : Set (F × M)) : Set (F × M) := {p ∈ pairs | ∀ q ∈ X, q.1 ≠ p.1 ∧ q.2 ≠ p.2}

theorem remaining_antitone : Antitone (remaining pairs) :=
  fun _ _ hXY _ hp ↦ ⟨hp.1, fun q hq ↦ hp.2 q (hXY hq)⟩

variable {pairs} in
theorem notMem_of_mem_remaining {X : Set (F × M)} {p : F × M} (hp : p ∈ remaining pairs X) :
    p ∉ X := fun hpX ↦ (hp.2 p hpX).1 rfl

variable [LE α] (f : F × M → α)

/-- One stage: add the most harmonic of the remaining pairs. -/
def stageStep (X : Set (F × M)) : Set (F × M) :=
  X ∪ {p | MinimalFor (· ∈ remaining pairs X) f p}

variable {J : Type*} [LinearOrder J] [SuccOrder J] [WellFoundedLT J]

/-- The stages of the construction, indexed by any well-order: empty at the bottom (`stage_bot`),
one step further at a successor (`stage_succ`), the union of the earlier stages at a limit
(`stage_of_isSuccLimit`). -/
noncomputable def stage (j : J) : Set (F × M) := transfiniteIterate (stageStep pairs f) j ∅

@[simp] theorem stage_bot [OrderBot J] : stage pairs f (⊥ : J) = ∅ := transfiniteIterate_bot _ _

theorem stage_succ [NoMaxOrder J] (j : J) :
    stage pairs f (Order.succ j) = stageStep pairs f (stage pairs f j) :=
  transfiniteIterate_succ _ _ j (not_isMax j)

theorem stage_mono [OrderBot J] : Monotone (stage pairs f : J → _) :=
  monotone_transfiniteIterate _ _ fun _ ↦ Set.subset_union_left

theorem stage_of_isSuccLimit {a : J} (ha : Order.IsSuccLimit a) :
    stage pairs f a = ⋃ b < a, stage pairs f b := by
  rw [stage, transfiniteIterate_limit _ _ _ ha]
  ext x
  simp [stage]

end Defs

variable [LinearOrder α] {pairs : Set (F × M)} {f : F × M → α}

/-- The two invariants of the stages against the super-optimal pairs, preserved by one stage. -/
private theorem stageStep_invariant (hf : (f '' pairs).IsWF) {X : Set (F × M)}
    (hX : X ⊆ superoptimalSet pairs f)
    (hr : superoptimalSet pairs f \ X ⊆ remaining pairs X) :
    stageStep pairs f X ⊆ superoptimalSet pairs f ∧
      superoptimalSet pairs f \ stageStep pairs f X ⊆ remaining pairs (stageStep pairs f X) := by
  have hmin : ∀ p, MinimalFor (· ∈ remaining pairs X) f p → p ∈ superoptimalSet pairs f :=
    fun p hp ↦ (mem_superoptimalSet pairs f hf).2 ⟨hp.1.1, fun ⟨e, he, hadj, hlt⟩ ↦ by
      by_cases heX : e ∈ X
      · exact hadj.elim (hp.1.2 e heX).1 (hp.1.2 e heX).2
      · exact hp.not_prop_of_lt hlt (hr ⟨he, heX⟩)⟩
  refine ⟨Set.union_subset hX hmin, fun p ⟨hpO, hpS⟩ ↦ ?_⟩
  have hp0 : p ∈ remaining pairs X := hr ⟨hpO, fun hpX ↦ hpS (.inl hpX)⟩
  refine ⟨hp0.1, fun q hq ↦ ?_⟩
  obtain hq | hq := hq
  · exact hp0.2 q hq
  · by_contra hshare
    have hadj : q.1 = p.1 ∨ q.2 = p.2 := by grind
    have hqO := hmin q hq
    have h1 : ¬ f q < f p := fun hlt ↦
      ((mem_superoptimalSet pairs f hf).1 hpO).2 ⟨q, hqO, hadj, hlt⟩
    have h2 : ¬ f p < f q := fun hlt ↦ ((mem_superoptimalSet pairs f hf).1 hqO).2
      ⟨p, hpO, hadj.imp Eq.symm Eq.symm, hlt⟩
    have heq : f p = f q := (not_lt.1 h1).antisymm (not_lt.1 h2)
    exact hpS (.inr (minimalFor_iff_forall_lt.2 ⟨hp0, fun j hj ↦ hq.not_prop_of_lt (heq ▸ hj)⟩))

section Index

variable {J : Type*} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]

private theorem stage_invariant (hf : (f '' pairs).IsWF) (a : J) :
    stage pairs f a ⊆ superoptimalSet pairs f ∧
      superoptimalSet pairs f \ stage pairs f a ⊆ remaining pairs (stage pairs f a) := by
  induction a using SuccOrder.limitRecOn with
  | isMin a ha =>
    rw [ha.eq_bot, stage_bot]
    exact ⟨Set.empty_subset _, fun p hp ↦ ⟨superoptimalSet_subset pairs f hp.1, by simp⟩⟩
  | succ a _ ih =>
    rw [stage_succ]
    exact stageStep_invariant hf ih.1 ih.2
  | isSuccLimit a ha ih =>
    rw [stage_of_isSuccLimit pairs f ha]
    refine ⟨Set.iUnion₂_subset fun b hb ↦ (ih b hb).1, fun p ⟨hpO, hpS⟩ ↦
      ⟨superoptimalSet_subset pairs f hpO, fun q hq ↦ ?_⟩⟩
    obtain ⟨b, hb, hq⟩ := Set.mem_iUnion₂.1 hq
    exact ((ih b hb).2 ⟨hpO, fun hp ↦ hpS (Set.mem_iUnion₂.2 ⟨b, hb, hp⟩)⟩).2 q hq

/-- Every stage consists of super-optimal pairs. -/
theorem stage_subset_superoptimalSet (hf : (f '' pairs).IsWF) (a : J) :
    stage pairs f a ⊆ superoptimalSet pairs f :=
  (stage_invariant hf a).1

/-- A super-optimal pair outside a stage shares no component with it. -/
theorem superoptimalSet_diff_stage_subset_remaining (hf : (f '' pairs).IsWF) (a : J) :
    superoptimalSet pairs f \ stage pairs f a ⊆ remaining pairs (stage pairs f a) :=
  (stage_invariant hf a).2

/-- A stage leaving no pair remaining is the set of super-optimal pairs. -/
theorem stage_eq_of_remaining_eq_empty (hf : (f '' pairs).IsWF) {a : J}
    (ha : remaining pairs (stage pairs f a) = ∅) : stage pairs f a = superoptimalSet pairs f :=
  (stage_subset_superoptimalSet hf a).antisymm fun p hp ↦ by_contra fun hpS ↦
    Set.notMem_empty p (ha ▸ superoptimalSet_diff_stage_subset_remaining hf a ⟨hp, hpS⟩)

end Index

/-- Some stage leaves no pair remaining: otherwise the stages would be strictly increasing, an
injection of the ordinals into a set. -/
theorem exists_remaining_stage_eq_empty (hf : (f '' pairs).IsWF) :
    ∃ a : Ordinal.{max u v}, remaining pairs (stage pairs f a) = ∅ := by
  by_contra! hne
  refine not_injective_of_ordinal.{max u v} (stage pairs f : Ordinal.{max u v} → Set (F × M))
    (.of_lt_imp_ne fun a b hab heq ↦ ?_)
  obtain ⟨p, hp⟩ := Set.IsPWO.exists_minimalFor f _
    (hf.mono (Set.image_mono fun _ hx ↦ hx.1)).isPWO (hne a)
  refine notMem_of_mem_remaining hp.prop (heq ▸ stage_mono pairs f (Order.succ_le_of_lt hab) ?_)
  rw [stage_succ]
  exact .inr hp

/-- The stages exhaust the super-optimal pairs. -/
theorem iUnion_stage (hf : (f '' pairs).IsWF) :
    ⋃ a : Ordinal.{max u v}, stage pairs f a = superoptimalSet pairs f := by
  obtain ⟨a, ha⟩ := exists_remaining_stage_eq_empty hf
  exact (Set.iUnion_subset fun b ↦ stage_subset_superoptimalSet hf b).antisymm
    ((stage_eq_of_remaining_eq_empty hf ha).symm.subset.trans (Set.subset_iUnion _ a))

/-- A pair remaining after stage `n` has at least `n` harmonies below its own. -/
private theorem le_ncard_lt (hV : (f '' pairs).Finite) (n : ℕ) {p : F × M}
    (hp : p ∈ remaining pairs (stage pairs f n)) :
    n ≤ {v ∈ f '' pairs | v < f p}.ncard := by
  induction n generalizing p with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [← Order.succ_eq_add_one, stage_succ] at hp
    have hp0 := remaining_antitone pairs Set.subset_union_left hp
    obtain ⟨q, hq, hqp⟩ : ∃ q ∈ remaining pairs (stage pairs f n), f q < f p := by
      by_contra! hmin
      exact notMem_of_mem_remaining hp (.inr (minimalFor_iff_forall_lt.2
        ⟨hp0, fun j hj hmem ↦ absurd hj (not_lt.2 (hmin j hmem))⟩))
    calc n + 1 ≤ {v ∈ f '' pairs | v < f q}.ncard + 1 := Nat.succ_le_succ (ih hq)
      _ = (insert (f q) {v ∈ f '' pairs | v < f q}).ncard :=
        (Set.ncard_insert_of_notMem (fun h ↦ lt_irrefl _ h.2) (hV.subset (Set.sep_subset _ _))).symm
      _ ≤ {v ∈ f '' pairs | v < f p}.ncard := Set.ncard_le_ncard
        (Set.insert_subset ⟨⟨q, hq.1, rfl⟩, hqp⟩ fun _ hv ↦ ⟨hv.1, hv.2.trans hqp⟩)
        (hV.subset (Set.sep_subset _ _))

/-- When the generator has at most `n` harmonies, stage `n` is the set of super-optimal pairs. -/
theorem stage_eq_superoptimalSet_of_encard_le {n : ℕ} (hn : (f '' pairs).encard ≤ n) :
    stage pairs f n = superoptimalSet pairs f := by
  obtain ⟨hV, hn⟩ := Set.encard_le_coe_iff_finite_ncard_le.1 hn
  refine stage_eq_of_remaining_eq_empty hV.isWF (Set.eq_empty_of_forall_notMem fun p hp ↦ ?_)
  have hlt : {v ∈ f '' pairs | v < f p}.ncard < (f '' pairs).ncard := Set.ncard_lt_ncard
    ⟨Set.sep_subset _ _, fun h ↦ lt_irrefl _ (h ⟨p, hp.1, rfl⟩).2⟩ hV
  have := le_ncard_lt hV n hp
  omega

end Stages

/-! ### Markedness and the division of labour -/

section Markedness

open Set (univ mem_graphOn)

variable [Preorder α] [LinearOrder F] [LinearOrder M] (pairs : Set (F × M)) {f : F × M → α}
  {S : Set (F × M)} {p : F × M}

theorem blocks_iff_of_strictMono (hf : StrictMono f) : Blocks f S p ↔ Blocks id S p := by
  refine exists_congr fun q ↦ and_congr_right fun _ ↦ and_congr_right fun hqp ↦
    ⟨fun hlt ↦ ?_, @hf _ _⟩
  have hcomp : q ≤ p ∨ p ≤ q := by
    obtain ⟨a, b⟩ := q; obtain ⟨c, d⟩ := p
    rcases hqp with rfl | rfl
    · exact (le_total b d).imp Prod.mk_le_mk_iff_right.2 Prod.mk_le_mk_iff_right.2
    · exact (le_total a c).imp Prod.mk_le_mk_iff_left.2 Prod.mk_le_mk_iff_left.2
  exact hcomp.elim (fun h ↦ h.lt_of_ne (by rintro rfl; exact lt_irrefl _ hlt))
    fun h ↦ absurd (hf.monotone h) hlt.not_ge

theorem unblockedSet_eq_of_strictMono (hf : StrictMono f) :
    unblockedSet pairs f = unblockedSet pairs id := by
  ext S p
  simp only [mem_unblockedSet, blocks_iff_of_strictMono hf]

theorem superoptimalSet_eq_of_strictMono (hf : StrictMono f) :
    superoptimalSet pairs f = superoptimalSet pairs id := by
  have : unblockedSq pairs f = unblockedSq pairs id := OrderHom.ext _ _ <| funext fun S ↦ by
    simp only [unblockedSq_apply, unblockedSet_eq_of_strictMono pairs hf]
  rw [superoptimalSet, superoptimalSet, this]

/-- On a generator well-founded in markedness and containing the graph of an isomorphism `e`
between the markedness orders of forms and of meanings, the super-optimal pairs are exactly that
graph, under every harmony strictly monotone in markedness. This is the division of pragmatic
labour. -/
theorem superoptimalSet_eq_graphOn (e : F ≃o M) (hf : StrictMono f) (h : pairs.IsWF)
    (he : univ.graphOn e ⊆ pairs) : superoptimalSet pairs f = univ.graphOn e := by
  rw [superoptimalSet_eq_of_strictMono pairs hf]
  refine (eq_superoptimalSet_of_isFixedPt pairs id (by rwa [Set.image_id]) ?_).symm
  ext ⟨a, b⟩
  change (a, b) ∈ pairs ∧ ¬ Blocks id (univ.graphOn e) (a, b) ↔ (a, b) ∈ univ.graphOn e
  refine ⟨fun ⟨_, hb⟩ ↦ mem_graphOn.2 ⟨trivial, ?_⟩, fun hab ↦ ⟨he hab, ?_⟩⟩
  · refine not_not.1 fun hne ↦ (lt_or_gt_of_ne hne).elim (fun hlt ↦ ?_) fun hlt ↦ ?_
    · exact hb ⟨(a, e a), ⟨a, trivial, rfl⟩, .inl rfl, Prod.mk_lt_mk_iff_right.2 hlt⟩
    · exact hb ⟨(e.symm b, b), ⟨e.symm b, trivial, by simp⟩, .inr rfl,
        Prod.mk_lt_mk_iff_left.2 (e.symm_apply_lt.2 hlt)⟩
  · obtain ⟨-, rfl⟩ : a ∈ univ ∧ e a = b := mem_graphOn.1 hab
    rintro ⟨_, ⟨c, -, rfl⟩, hc | hc, hlt⟩
    · obtain rfl : c = a := hc
      exact lt_irrefl _ hlt
    · obtain rfl : c = a := e.injective hc
      exact lt_irrefl _ hlt

end Markedness

/-! ### Computable forms -/

section Finset

variable [LT α] [DecidableEq F] [DecidableEq M] [DecidableLT α] (pairs : Finset (F × M))
  (f : F × M → α) {S : Finset (F × M)} {p : F × M}

/-- The pairs of `pairs` that `S` does not block. -/
def unblocked (S : Finset (F × M)) : Finset (F × M) := pairs.filter fun p ↦ ¬ Blocks f ↑S p

variable {pairs f} in
@[simp] theorem mem_unblocked : p ∈ unblocked pairs f S ↔ p ∈ pairs ∧ ¬ Blocks f ↑S p :=
  Finset.mem_filter

@[simp] theorem coe_unblocked : (↑(unblocked pairs f S) : Set (F × M)) = unblockedSet ↑pairs f ↑S :=
  Finset.coe_filter _ _

theorem unblocked_subset : unblocked pairs f S ⊆ pairs := Finset.filter_subset _ _

theorem unblocked_antitone : Antitone (unblocked pairs f) := fun _ _ hST _ hp ↦
  mem_unblocked.2 ⟨(mem_unblocked.1 hp).1,
    fun hb ↦ (mem_unblocked.1 hp).2 (hb.mono (Finset.coe_subset.2 hST))⟩

/-- Strong bidirection, computably. -/
def strongOptimal : Finset (F × M) := unblocked pairs f pairs

variable {pairs f} in
@[simp] theorem mem_strongOptimal : p ∈ strongOptimal pairs f ↔ p ∈ pairs ∧ ¬ Blocks f ↑pairs p :=
  mem_unblocked

theorem coe_strongOptimal : (↑(strongOptimal pairs f) : Set (F × M)) = strongOptimalSet ↑pairs f :=
  coe_unblocked pairs f

/-- The squared blocking step iterated from `S` until it is fixed, at most `n` times; the
computation behind `superoptimal`. -/
def superoptimalAux (S : Finset (F × M)) : ℕ → Finset (F × M)
  | 0 => S
  | n + 1 =>
    if unblocked pairs f (unblocked pairs f S) = S then S
    else superoptimalAux (unblocked pairs f (unblocked pairs f S)) n

private theorem superoptimalAux_spec (S : Finset (F × M)) (n : ℕ) :
    ∃ k ≤ n, superoptimalAux pairs f S n = (unblocked pairs f ∘ unblocked pairs f)^[k] S ∧
      (IsFixedPt (unblocked pairs f ∘ unblocked pairs f) (superoptimalAux pairs f S n) ∨
        k = n) := by
  induction n generalizing S with
  | zero => exact ⟨0, le_rfl, rfl, .inr rfl⟩
  | succ n ih =>
    by_cases h : unblocked pairs f (unblocked pairs f S) = S
    · exact ⟨0, Nat.zero_le _, by simp [superoptimalAux, h],
        .inl (by simp [superoptimalAux, h, IsFixedPt])⟩
    · obtain ⟨k, hk, hT, hfix⟩ := ih (unblocked pairs f (unblocked pairs f S))
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · rw [iterate_succ_apply, comp_apply, ← hT]; simp [superoptimalAux, h]
      · simpa [superoptimalAux, h] using hfix.imp_right fun hk ↦ by omega

/-- The super-optimal pairs, computably: the squared blocking step iterated from `pairs` until
fixed, which happens within `pairs.card` steps. Equality with a literal `Finset` is closed by
`decide`. -/
def superoptimal : Finset (F × M) := superoptimalAux pairs f pairs pairs.card

private theorem isFixedPt_iterate_card {β : Type*} {g : Finset β → Finset β} (hg : Monotone g)
    {s : Finset β} (hs : g s ⊆ s) : IsFixedPt g (g^[s.card] s) := by
  have hdesc : ∀ n, g^[n + 1] s ⊆ g^[n] s := fun n ↦ by
    induction n with
    | zero => exact hs
    | succ n ih =>
      have := hg ih
      rwa [← iterate_succ_apply' g, ← iterate_succ_apply' g] at this
  have key : ∀ n, IsFixedPt g (g^[n] s) ∨ (g^[n] s).card + n ≤ s.card := fun n ↦ by
    induction n with
    | zero => exact .inr (by simp)
    | succ n ih =>
      by_cases hfix : IsFixedPt g (g^[n] s)
      · exact .inl (by rw [iterate_succ_apply', hfix.eq]; exact hfix)
      · have hlt : (g^[n + 1] s).card < (g^[n] s).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hdesc n,
            fun h ↦ hfix (by show g (g^[n] s) = g^[n] s; rw [← iterate_succ_apply' g, h])⟩)
        exact .inr (by have := ih.resolve_left hfix; omega)
  rcases key s.card with h | h
  · exact h
  · have hempty : g^[s.card] s = ∅ := Finset.card_eq_zero.1 (by omega)
    have hsub := hdesc s.card
    rw [iterate_succ_apply', hempty] at hsub
    show g (g^[s.card] s) = g^[s.card] s
    rw [hempty]
    exact Finset.subset_empty.1 hsub

theorem coe_superoptimal : (↑(superoptimal pairs f) : Set (F × M)) = superoptimalSet ↑pairs f := by
  have hcoe : ∀ n, (↑((unblocked pairs f ∘ unblocked pairs f)^[n] pairs) : Set (F × M)) =
      (unblockedSq ↑pairs f)^[n] ↑pairs := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; simp
  have hle : ∀ n, (unblockedSq ↑pairs f).gfp ≤ (unblockedSq ↑pairs f)^[n] ↑pairs := fun n ↦ by
    induction n with
    | zero => exact superoptimalSet_subset _ _
    | succ n ih =>
      rw [iterate_succ_apply']
      exact (unblockedSq ↑pairs f).map_gfp.symm.le.trans ((unblockedSq ↑pairs f).monotone ih)
  obtain ⟨k, -, hT, hfix⟩ := superoptimalAux_spec pairs f pairs pairs.card
  have hfix : IsFixedPt (unblocked pairs f ∘ unblocked pairs f) (superoptimal pairs f) :=
    hfix.elim id fun hk ↦ by
      rw [superoptimal, hT, hk]
      exact isFixedPt_iterate_card ((unblocked_antitone pairs f).comp (unblocked_antitone pairs f))
        (unblocked_subset pairs f (S := unblocked pairs f pairs))
  have hΦ : unblockedSq ↑pairs f ↑(superoptimal pairs f) = ↑(superoptimal pairs f) := by
    simpa using congrArg (fun s : Finset (F × M) ↦ (↑s : Set (F × M))) hfix.eq
  refine le_antisymm (le_gfp _ hΦ.ge) ?_
  rw [superoptimal, hT, hcoe]
  exact hle k

theorem superoptimal_subset : superoptimal pairs f ⊆ pairs := by
  rw [← Finset.coe_subset, coe_superoptimal]
  exact superoptimalSet_subset _ _

theorem strongOptimal_subset_superoptimal : strongOptimal pairs f ⊆ superoptimal pairs f := by
  rw [← Finset.coe_subset, coe_strongOptimal, coe_superoptimal]
  exact strongOptimalSet_subset_superoptimalSet _ _

end Finset

/-- The fixed-point equation, computably. A finite set of harmonies is well-founded once the order
is a preorder. -/
theorem mem_superoptimal [Preorder α] [DecidableEq F] [DecidableEq M] [DecidableLT α]
    (pairs : Finset (F × M)) (f : F × M → α) {p : F × M} :
    p ∈ superoptimal pairs f ↔ p ∈ pairs ∧ ¬ Blocks f ↑(superoptimal pairs f) p := by
  rw [← Finset.mem_coe, coe_superoptimal,
    mem_superoptimalSet _ _ (pairs.finite_toSet.image f).isWF, Finset.mem_coe]

end BidirectionalOT
