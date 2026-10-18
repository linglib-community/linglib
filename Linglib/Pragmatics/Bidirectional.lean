module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.FixedPoints
public import Linglib.Core.Order.WellFoundedSet
public import Linglib.Pragmatics.Competition

/-!
# Bidirectional Optimality Theory

Bidirectional optimality theory evaluates a form-meaning pair of a generator from the speaker's
and the hearer's side at once. Another pair blocks it when it is more harmonic and shares its
meaning (the Q-principle, production) or its form (the I-principle, comprehension). Under strong
bidirection a pair is optimal when no pair of the generator blocks it; under weak bidirection it
is super-optimal when no super-optimal pair blocks it, a fixed point of the blocking step.

## Main definitions

* `profile`: the violation profile of a ranking, compared lexicographically.
* `QBlocks`, `IBlocks`, `Blocks`: a set of pairs blocks a pair along the meaning axis, the form
  axis, or either.
* `unblockedSet pairs f S`: the pairs of `pairs` that `S` does not block, an antitone step;
  `strongOptimalSet` is its value at `pairs`.
* `superoptimalSet`: the greatest fixed point of the square of the step.
* `IsWeakSolution`: a solution of Blutner's mutual recursion of the two principles.
* `unblocked`, `strongOptimal`, `superoptimal`: the computable `Finset` forms.

## Main results

* `mem_superoptimalSet`: when the harmonies of the generator are well-founded, a pair is
  super-optimal iff it lies in the generator and no super-optimal pair blocks it, and
  `superoptimalSet` is the only such set.
* `strongOptimalSet_subset_superoptimalSet`: optimal pairs are super-optimal.
* `superoptimalSet_eq_graphOn`: the division of pragmatic labour. On a generator containing the
  graph of an isomorphism between the markedness orders of forms and of meanings, the
  super-optimal pairs are that graph, under every harmony strictly monotone in markedness.
* `coe_superoptimal`: the `Finset` iteration computes `superoptimalSet`.

## Implementation notes

* The harmony is any preorder reached through `f`, such as `profile` into the lexicographic
  order on `List ℕ`. The principles' "other pair" clause is dropped, since `f q < f p` already
  forces `q ≠ p`.
* The step is antitone, so its square has a greatest fixed point without further hypotheses, and
  the step exchanges it with the least one. The two coincide by descent along a minimal pair of
  their difference when the harmonies of the generator are well-founded, Jäger's hypothesis,
  which every finite generator meets (`Set.Finite.isWF`).
* The `Finset` form iterates the squared step from `pairs` with `pairs.card` as fuel and an early
  exit, so it needs no convergence hypothesis and `decide` stays shallow.
* Jäger's uniqueness of weak solutions and their agreement with `superoptimalSet` are proved in
  `Studies/Jaeger2002.lean`.

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

variable {F M α : Type*} [Preorder α]

/-- The violation profile of a ranking lists a pair's violations from the dominant constraint
down, to be compared lexicographically. -/
def profile (ranking : List (F × M → ℕ)) (p : F × M) : List ℕ := ranking.map (· p)

private theorem map_lt_map {β : Type*} {ranking : List (β → ℕ)} {p q : β}
    (hle : ∀ c ∈ ranking, c p ≤ c q) (hlt : ∃ c ∈ ranking, c p < c q) :
    ranking.map (· p) < ranking.map (· q) := by
  induction ranking with
  | nil => simp at hlt
  | cons d ds ih =>
    rw [List.map_cons, List.map_cons, List.cons_lt_cons_iff]
    refine (hle d List.mem_cons_self).lt_or_eq.imp id fun h ↦
      ⟨h, ih (fun c hc ↦ hle c (List.mem_cons_of_mem _ hc)) ?_⟩
    obtain ⟨c, hc, hlt⟩ := hlt
    rcases List.mem_cons.1 hc with rfl | hc
    · exact absurd h hlt.ne
    · exact ⟨c, hc, hlt⟩

/-- A ranking of constraints that each penalize the more marked pair gives a strictly monotone
profile once every strictly less marked pair does strictly better on some constraint. -/
theorem strictMono_profile [Preorder F] [Preorder M] {ranking : List (F × M → ℕ)}
    (hmono : ∀ c ∈ ranking, Monotone c) (hsep : ∀ ⦃p q⦄, p < q → ∃ c ∈ ranking, c p < c q) :
    StrictMono (profile ranking) :=
  fun _ _ hpq ↦ map_lt_map (fun c hc ↦ hmono c hc hpq.le) (hsep hpq)

/-! ### Blocking -/

section Blocks

variable (f : F × M → α) (S : Set (F × M)) (p : F × M)

/-- `QBlocks f S p` holds when a more harmonic pair of `S` expresses `p`'s meaning. -/
def QBlocks : Prop := ∃ q ∈ S, q.2 = p.2 ∧ f q < f p

/-- `IBlocks f S p` holds when a more harmonic pair of `S` interprets `p`'s form. -/
def IBlocks : Prop := ∃ q ∈ S, q.1 = p.1 ∧ f q < f p

/-- `Blocks f S p` holds when a more harmonic pair of `S` shares `p`'s form or meaning. -/
def Blocks : Prop := ∃ q ∈ S, (q.1 = p.1 ∨ q.2 = p.2) ∧ f q < f p

/-- Bidirectional blocking is competition among the pairs of `S` that share a form or a
meaning. -/
theorem blocks_iff_blocked :
    Blocks f S p ↔ Competition.Blocked (fun p ↦ {q ∈ S | q.1 = p.1 ∨ q.2 = p.2}) f p :=
  ⟨fun ⟨q, hq, h, hlt⟩ ↦ ⟨q, ⟨hq, h⟩, hlt⟩, fun ⟨q, ⟨hq, h⟩, hlt⟩ ↦ ⟨q, hq, h, hlt⟩⟩

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

variable (pairs : Set (F × M)) (f : F × M → α) {S : Set (F × M)} {p : F × M}

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

/-- The step exchanges the greatest and least fixed points of its square. -/
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

/-- When the harmonies of the generator are well-founded, the least and greatest fixed points of
the squared step coincide, since a minimal pair of their difference would be blocked by a still
smaller one. -/
theorem lfp_eq_superoptimalSet (h : (f '' pairs).IsWF) :
    (unblockedSq pairs f).lfp = superoptimalSet pairs f := by
  set G := superoptimalSet pairs f
  set L := (unblockedSq pairs f).lfp
  have hGL : unblockedSet pairs f G = L := unblockedSet_superoptimalSet pairs f
  have hLG : unblockedSet pairs f L = G := by rw [← hGL]; exact (unblockedSq pairs f).map_gfp
  refine le_antisymm (lfp_le_gfp _) (not_not.1 fun hne ↦ ?_)
  obtain ⟨p, ⟨hpG, hpL⟩, hmin⟩ := (h.mono (Set.image_mono fun x hx ↦
    superoptimalSet_subset pairs f hx.1)).exists_minimalFor f (G \ L) (Set.not_subset.1 hne)
  have hp : p ∈ unblockedSet pairs f L := hLG.symm ▸ hpG
  obtain ⟨q, hqG, hadj, hlt⟩ : Blocks f G p :=
    not_not.1 fun hb ↦ hpL (hGL ▸ (⟨hp.1, hb⟩ : p ∈ unblockedSet pairs f G))
  exact hlt.not_ge (hmin ⟨hqG, fun hqL ↦ hp.2 ⟨q, hqL, hadj, hlt⟩⟩ hlt.le)

theorem isFixedPt_superoptimalSet (h : (f '' pairs).IsWF) :
    IsFixedPt (unblockedSet pairs f) (superoptimalSet pairs f) := by
  rw [IsFixedPt, unblockedSet_superoptimalSet, lfp_eq_superoptimalSet pairs f h]

/-- A pair is super-optimal iff it lies in the generator and no super-optimal pair blocks it,
Jäger's reformulation of super-optimality. -/
theorem mem_superoptimalSet (h : (f '' pairs).IsWF) :
    p ∈ superoptimalSet pairs f ↔ p ∈ pairs ∧ ¬ Blocks f (superoptimalSet pairs f) p := by
  conv_lhs => rw [← (isFixedPt_superoptimalSet pairs f h).eq]
  exact Iff.rfl

/-- When the harmonies of the generator are well-founded, the blocking step has no fixed point
but the super-optimal set. -/
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

variable (pairs : Set (F × M)) (f : F × M → α)

/-- The pairs of `pairs` that `S` does not Q-block. -/
def qUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ QBlocks f S p}

/-- The pairs of `pairs` that `S` does not I-block. -/
def iUnblockedSet (S : Set (F × M)) : Set (F × M) := {p ∈ pairs | ¬ IBlocks f S p}

theorem qUnblockedSet_antitone : Antitone (qUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

theorem iUnblockedSet_antitone : Antitone (iUnblockedSet pairs f) :=
  fun _ _ hST _ hp ↦ ⟨hp.1, fun hb ↦ hp.2 (hb.mono hST)⟩

theorem unblockedSet_eq_inter (S : Set (F × M)) :
    unblockedSet pairs f S = qUnblockedSet pairs f S ∩ iUnblockedSet pairs f S := by
  ext p
  simp only [mem_unblockedSet, blocks_iff, qUnblockedSet, iUnblockedSet, Set.mem_inter_iff,
    Set.mem_sep_iff, not_or]
  tauto

/-- In the weak version of bidirection `Q` collects the pairs no pair of `I` Q-blocks and `I`
the pairs no pair of `Q` I-blocks. A pair of both is super-optimal. -/
def IsWeakSolution (Q I : Set (F × M)) : Prop :=
  qUnblockedSet pairs f I = Q ∧ iUnblockedSet pairs f Q = I

/-- The mutual recursion has a solution, the greatest fixed point of the monotone composite
`qUnblockedSet ∘ iUnblockedSet` together with its image under `iUnblockedSet`. -/
theorem exists_isWeakSolution : ∃ Q I, IsWeakSolution pairs f Q I :=
  let Φ : Set (F × M) →o Set (F × M) :=
    ⟨qUnblockedSet pairs f ∘ iUnblockedSet pairs f,
      (qUnblockedSet_antitone pairs f).comp (iUnblockedSet_antitone pairs f)⟩
  ⟨Φ.gfp, iUnblockedSet pairs f Φ.gfp, Φ.map_gfp, rfl⟩

/-- Optimal pairs satisfy both principles of every weak solution, since a pair no pair of
`pairs` blocks is blocked by no pair of `I` or of `Q`, both subsets of `pairs`. -/
theorem strongOptimalSet_subset_inter {Q I : Set (F × M)} (h : IsWeakSolution pairs f Q I) :
    strongOptimalSet pairs f ⊆ Q ∩ I := fun p hp ↦ by
  obtain ⟨hQ, hI⟩ := h
  have hQp : Q ⊆ pairs := hQ ▸ fun _ hx ↦ hx.1
  have hIp : I ⊆ pairs := hI ▸ fun _ hx ↦ hx.1
  have hpQ : p ∈ qUnblockedSet pairs f I :=
    ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inr (hb.mono hIp)))⟩
  have hpI : p ∈ iUnblockedSet pairs f Q :=
    ⟨hp.1, fun hb ↦ hp.2 ((blocks_iff ..).2 (.inl (hb.mono hQp)))⟩
  exact ⟨hQ ▸ hpQ, hI ▸ hpI⟩

end Weak

/-! ### Markedness and the division of labour -/

section Markedness

open Set (univ mem_graphOn)

variable [LinearOrder F] [LinearOrder M] (pairs : Set (F × M)) {f : F × M → α}
  {S : Set (F × M)} {p : F × M}

/-- A harmony strictly monotone in the markedness of forms and of meanings blocks as markedness
itself does: of two pairs sharing a form or a meaning, the less marked one is more harmonic. -/
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

/-- Weak bidirection does not depend on how a strictly monotone harmony weighs the markedness of
forms against that of meanings. -/
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

variable [DecidableEq F] [DecidableEq M] [DecidableLT α] (pairs : Finset (F × M))
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

/-- A monotone self-map of finsets that shrinks `s` is fixed on `s` within `s.card` steps. -/
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

/-- The footnote's recursion, computably. -/
theorem mem_superoptimal :
    p ∈ superoptimal pairs f ↔ p ∈ pairs ∧ ¬ Blocks f ↑(superoptimal pairs f) p := by
  rw [← Finset.mem_coe, coe_superoptimal,
    mem_superoptimalSet _ _ (pairs.finite_toSet.image f).isWF, Finset.mem_coe]

theorem superoptimal_subset : superoptimal pairs f ⊆ pairs :=
  fun _ hp ↦ ((mem_superoptimal pairs f).1 hp).1

theorem strongOptimal_subset_superoptimal : strongOptimal pairs f ⊆ superoptimal pairs f := by
  rw [← Finset.coe_subset, coe_strongOptimal, coe_superoptimal]
  exact strongOptimalSet_subset_superoptimalSet _ _

end Finset

end BidirectionalOT
