/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Syntax.Spine.Label
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Infix
public import Mathlib.Logic.Relation

/-!
# The hierarchy of a set of spines

A spine lists the heads of a phrase from the lowest up, so a spine with a head `b` above a head `a`
shows that `b` is higher than `a`. A second spine with `c` above `b` shows that `c` is higher
still, and so higher than `a`, though neither spine has all three heads. The **hierarchy** of a set
of spines is the order on heads that its spines show in this way.

A **step** goes from a head to the head directly above it on a spine of the set. One head is **no
higher than** another when steps lead from it up to the other, or when the two are the same head,
and it is **lower than** the other when no steps lead back. For the spines `[a, b]` and `[b, c]`,
`a` is lower than `c`. Two heads are **level** when each is no higher than the other, which happens
when spines of the set order them in both ways.

The hierarchy holds exactly what the spines require. Give each head a height, a number, so that
heights never drop going up a spine of the set. One head is no higher than another in the hierarchy
exactly when every such choice of heights gives it a height no greater. A height of this kind is
what Grimshaw calls the functional value of a head.

Adding a spine to the set can only add to the hierarchy. When the set is one spine on which no head
occurs twice, the hierarchy is the order in which the heads stand on that spine.

## Implementation notes

The one definition is `Spine.Step S`, for a set `S` of spines. The hierarchy of `S` has no name of
its own. It is written `Relation.ReflTransGen (Spine.Step S)`, the reflexive and transitive closure
of the steps, so that mathlib's lemmas about closures apply to it, and level heads are those
related by `AntisymmRel`.

`Spine.reflTransGen_step_le_iff` says that the hierarchy is the least reflexive and transitive
relation in which every spine of `S` ascends. The statements about heights are
`Spine.forall_reflTransGen_step_iff` and `Spine.reflTransGen_step_iff_forall_le`, the statement
about adding a spine is `Spine.reflTransGen_step_mono`, and the single spine is
`Spine.reflTransGen_step_singleton_iff`.

For a set given as a list, `Spine.steps` lists the steps as pairs, and
`Spine.decidableReflTransGenStep` decides the hierarchy by searching along them.

An analysis that takes two heads to be one head is entered as two spines, the two heads in each
order, which makes them level.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Spine

variable {H β : Type*} {S T : Set (Spine H)} {r : H → H → Prop} {c d : H} {s : Spine H}

/-!
### Steps

A step goes from a head to the head directly above it on some spine of the set.
-/

/-- `Spine.Step S c d` says that `d` stands directly above `c` on some spine of the set `S`: there
is a **step** from `c` up to `d`. -/
def Step (S : Set (Spine H)) (c d : H) : Prop := ∃ s ∈ S, [c, d] <:+: s.heads

/-- A relation holds along every step of a set of spines exactly when every spine of the set is a
chain for it. -/
theorem step_le_iff : Step S ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r := by
  refine ⟨fun h s hs ↦ List.isChain_iff_forall_rel_of_append_cons_cons.2 fun x y l₁ l₂ e ↦
      h _ _ ⟨s, hs, l₁, l₂, by simp [e]⟩, ?_⟩
  rintro h x y ⟨s, hs, l₁, l₂, e⟩
  exact List.isChain_iff_forall_rel_of_append_cons_cons.1 (h s hs) (by simpa using e.symm)

/-- A larger set of spines has more steps. -/
theorem step_mono (h : S ⊆ T) : Step S ≤ Step T := fun _ _ ⟨s, hs, hi⟩ ↦ ⟨s, h hs, hi⟩

/-!
### The hierarchy

One head is no higher than another in the hierarchy of a set of spines when steps lead from it up
to the other, or the two are the same head.
-/

/-- The hierarchy of a set of spines is the least reflexive and transitive relation in which every
spine of the set ascends. -/
theorem reflTransGen_step_le_iff [Std.Refl r] [IsTrans H r] :
    Relation.ReflTransGen (Step S) ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r :=
  ⟨fun h ↦ step_le_iff.1 fun x y hxy ↦ h x y (.single hxy),
    fun h ↦ Relation.reflTransGen_le_of_le (step_le_iff.2 h)⟩

/-- Every spine of a set ascends in the hierarchy of the set. -/
theorem isChain_reflTransGen_step (hs : s ∈ S) :
    s.heads.IsChain (Relation.ReflTransGen (Step S)) :=
  reflTransGen_step_le_iff.1 le_rfl s hs

/-- On a spine of a set, each head is no higher in the hierarchy of the set than any head above it
on the spine. -/
theorem pairwise_reflTransGen_step (hs : s ∈ S) :
    s.heads.Pairwise (Relation.ReflTransGen (Step S)) :=
  List.isChain_iff_pairwise.1 (isChain_reflTransGen_step hs)

/-- Adding spines to a set can only add to its hierarchy. -/
theorem reflTransGen_step_mono (h : S ⊆ T) :
    Relation.ReflTransGen (Step S) ≤ Relation.ReflTransGen (Step T) :=
  Relation.ReflTransGen.mono (step_mono h)

/-!
### Heights

An assignment of heights respects the hierarchy exactly when the heights never drop going up a
spine of the set, and the hierarchy holds between two heads exactly when every such assignment
agrees.
-/

/-- A map of heads sends the hierarchy of a set of spines into a reflexive and transitive relation
exactly when the image of every spine of the set is a chain for that relation. -/
theorem forall_reflTransGen_step_iff {r : β → β → Prop} [Std.Refl r] [IsTrans β r] {f : H → β} :
    (∀ x y, Relation.ReflTransGen (Step S) x y → r (f x) (f y)) ↔
      ∀ s ∈ S, (s.map f).heads.IsChain r := by
  have : Std.Refl fun x y ↦ r (f x) (f y) := ⟨fun _ ↦ refl _⟩
  have : IsTrans H fun x y ↦ r (f x) (f y) := ⟨fun _ _ _ ↦ _root_.trans⟩
  simp only [heads_map, List.isChain_map]
  exact reflTransGen_step_le_iff (S := S) (r := fun x y ↦ r (f x) (f y))

/-- A head `c` is no higher than a head `d` in the hierarchy of a set of spines exactly when every
assignment of heights that never drops going up a spine of the set gives `c` a height no greater
than that of `d`. -/
theorem reflTransGen_step_iff_forall_le :
    Relation.ReflTransGen (Step S) c d ↔
      ∀ f : H → ℕ, (∀ s ∈ S, (s.map f).heads.IsChain (· ≤ ·)) → f c ≤ f d := by
  classical
  refine ⟨fun h f hf ↦ forall_reflTransGen_step_iff.2 hf c d h, fun h ↦ ?_⟩
  have hc := h (fun x ↦ if Relation.ReflTransGen (Step S) c x then 1 else 0) fun s hs ↦ by
    rw [heads_map, List.isChain_map]
    refine (isChain_reflTransGen_step hs).imp fun x y hxy ↦ ?_
    by_cases hx : Relation.ReflTransGen (Step S) c x
    · simp [hx, hx.trans hxy]
    · simp [hx]
  by_contra hcd
  simp [hcd, Relation.ReflTransGen.refl] at hc

/-!
### One spine

On a spine where no head occurs twice, the hierarchy of the spine alone is the order in which its
heads stand on it.
-/

section Singleton

variable [DecidableEq H]

/-- On a spine where no head occurs twice, a head that is no higher than another in the hierarchy
of that spine stands no higher on the spine. -/
theorem height_le_of_reflTransGen_step (hs : s.heads.Nodup)
    (h : Relation.ReflTransGen (Step {s}) c d) : s.height c ≤ s.height d := by
  refine (forall_reflTransGen_step_iff (f := s.height) (r := (· ≤ ·))).2 (fun t ht ↦ ?_) c d h
  obtain rfl : t = s := ht
  rw [heads_map, List.isChain_map]
  exact List.isChain_iff_getElem.2 fun i _ ↦ by
    simp only [height, hs.idxOf_getElem]
    exact Nat.le_succ i

/-- For two heads `c` and `d` of a spine where no head occurs twice, `c` is no higher than `d` in
the hierarchy of that spine exactly when `c` stands no higher on the spine than `d`. -/
theorem reflTransGen_step_singleton_iff (hs : s.heads.Nodup) (hc : c ∈ s) (hd : d ∈ s) :
    Relation.ReflTransGen (Step {s}) c d ↔ s.height c ≤ s.height d := by
  refine ⟨height_le_of_reflTransGen_step hs, fun h ↦ ?_⟩
  have hc' : s.height c < s.heads.length := List.idxOf_lt_length_iff.2 hc
  have hd' : s.height d < s.heads.length := List.idxOf_lt_length_iff.2 hd
  have ec : s.heads[s.height c] = c := List.getElem_idxOf hc'
  have ed : s.heads[s.height d] = d := List.getElem_idxOf hd'
  obtain hlt | heq := h.lt_or_eq
  · exact ec ▸ ed ▸ List.pairwise_iff_getElem.1
      (pairwise_reflTransGen_step (S := {s}) rfl) _ _ hc' hd' hlt
  · exact (List.idxOf_inj hc).1 heq ▸ .refl

end Singleton

/-!
### Deciding the hierarchy of a list of spines

When the set of spines is given as a list, whether one head is no higher than another can be
computed.
-/

/-- The **steps** of a list of spines, each as the pair of a head and the head directly above
it. -/
def steps (L : List (Spine H)) : List (H × H) := L.flatMap fun s ↦ s.heads.zip s.heads.tail

private theorem pair_infix_iff_mem_zip_tail {x y : H} :
    ∀ {l : List H}, [x, y] <:+: l ↔ (x, y) ∈ l.zip l.tail
  | [] => by simp
  | [_] => by simp [List.infix_cons_iff, List.prefix_cons_iff]
  | z :: w :: l => by
    rw [List.infix_cons_iff, pair_infix_iff_mem_zip_tail (l := w :: l)]
    simp [List.prefix_cons_iff, and_comm]

/-- The steps of a list of spines are the pairs in `Spine.steps`. -/
theorem step_iff_mem_steps {L : List (Spine H)} : Step {s | s ∈ L} c d ↔ (c, d) ∈ steps L := by
  simp [Step, steps, pair_infix_iff_mem_zip_tail]

/-- The hierarchy of a list of spines is decided by searching along its steps. -/
@[instance_reducible]
def decidableReflTransGenStep [DecidableEq H] (L : List (Spine H)) :
    DecidableRel (Relation.ReflTransGen (Step {s | s ∈ L})) := fun c d ↦
  Relation.ReflTransGen.decidable_of_finite_step
    (fun x ↦ ((steps L).filter (·.1 == x)).map (·.2)) ((steps L).map (·.2))
    (fun x y ↦ by simp [step_iff_mem_steps]) (fun _ _ h ↦ by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact List.mem_map_of_mem (List.mem_filter.1 hp).1) c d

end Spine
