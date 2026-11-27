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
# The hierarchy of a family of spines

Syntacticians read the order of heads off the structures they draw. A clause drawn with tense above
the verb says that tense is higher than the verb, and a second clause drawn with the complementizer
above tense adds that the complementizer is higher still. This file makes that reading precise for
any type of heads. Given a family of spines, a head is one **step** below another when some spine
of the family has the second directly above the first. The **hierarchy** of the family relates two
heads when a chain of steps leads from the first up to the second, and the first is then **no
higher than** the second.

Take the two spines `[V, v, T]` and `[T, C]`. Their steps are from `V` to `v`, from `v` to `T` and
from `T` to `C`, so in their hierarchy `V` is lower than `C`, though no one spine has both.

The hierarchy is the least reflexive and transitive relation in which every spine of the family
ascends. So a way of assigning heights to heads respects the hierarchy exactly when the heights
never drop going up a spine of the family, and one head is no higher than another in the hierarchy
exactly when every such assignment gives it a height no greater. A larger family has a larger
hierarchy. When the family is one spine on which no head recurs, the hierarchy is the order of the
positions on that spine.

Two spines that order a pair of heads in opposite ways make the two heads **level**, each no higher
than the other. Nothing is lost by this: the hierarchy records that the family does not agree on
them.



## Implementation notes

`Spine.Step S` is the only definition. The hierarchy of `S` is written
`Relation.ReflTransGen (Spine.Step S)`, so that mathlib's lemmas about the closure apply to it, and
level heads are related by `AntisymmRel`. The statements above are, in order,
`Spine.reflTransGen_step_le_iff`, `Spine.forall_reflTransGen_step_iff`,
`Spine.reflTransGen_step_iff_forall_le`, `Spine.reflTransGen_step_mono` and
`Spine.reflTransGen_step_singleton_iff`.

A family is a set of spines. For a family given as a list, `Spine.steps` lists its steps as pairs,
and `Spine.decidableReflTransGenStep` decides the hierarchy by searching along them.

That two heads are one, as when an analysis identifies the heads of two proposals, is said by
putting the two-head spine in the family in both orders.
-/

@[expose] public section

namespace Spine

variable {H β : Type*} {S T : Set (Spine H)} {r : H → H → Prop} {c d : H} {s : Spine H}

/-!
### Steps
-/

/-- A head is one **step** below another in a family of spines when some spine of the family has
the other directly above it. -/
def Step (S : Set (Spine H)) (c d : H) : Prop := ∃ s ∈ S, [c, d] <:+: s.heads

/-- A relation holds along every step of a family exactly when every spine of the family is a
chain for it. -/
theorem step_le_iff : Step S ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r := by
  refine ⟨fun h s hs ↦ List.isChain_iff_forall_rel_of_append_cons_cons.2 fun x y l₁ l₂ e ↦
      h _ _ ⟨s, hs, l₁, l₂, by simp [e]⟩, ?_⟩
  rintro h x y ⟨s, hs, l₁, l₂, e⟩
  exact List.isChain_iff_forall_rel_of_append_cons_cons.1 (h s hs) (by simpa using e.symm)

/-- A larger family has more steps. -/
theorem step_mono (h : S ⊆ T) : Step S ≤ Step T := fun _ _ ⟨s, hs, hi⟩ ↦ ⟨s, h hs, hi⟩

/-!
### The hierarchy
-/

/-- The hierarchy of a family is the least reflexive and transitive relation in which every spine
of the family ascends. -/
theorem reflTransGen_step_le_iff [Std.Refl r] [IsTrans H r] :
    Relation.ReflTransGen (Step S) ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r :=
  ⟨fun h ↦ step_le_iff.1 fun x y hxy ↦ h x y (.single hxy),
    fun h ↦ Relation.reflTransGen_le_of_le (step_le_iff.2 h)⟩

/-- Every spine of a family ascends in the hierarchy of the family. -/
theorem isChain_reflTransGen_step (hs : s ∈ S) :
    s.heads.IsChain (Relation.ReflTransGen (Step S)) :=
  reflTransGen_step_le_iff.1 le_rfl s hs

/-- On a spine of a family, each head is no higher in the hierarchy of the family than any head
above it on the spine. -/
theorem pairwise_reflTransGen_step (hs : s ∈ S) :
    s.heads.Pairwise (Relation.ReflTransGen (Step S)) :=
  List.isChain_iff_pairwise.1 (isChain_reflTransGen_step hs)

/-- A larger family has a larger hierarchy. -/
theorem reflTransGen_step_mono (h : S ⊆ T) :
    Relation.ReflTransGen (Step S) ≤ Relation.ReflTransGen (Step T) :=
  Relation.ReflTransGen.mono (step_mono h)

/-- A map sends the hierarchy of a family into a reflexive and transitive relation exactly when
the images of the spines of the family are chains for it. -/
theorem forall_reflTransGen_step_iff {r : β → β → Prop} [Std.Refl r] [IsTrans β r] {f : H → β} :
    (∀ x y, Relation.ReflTransGen (Step S) x y → r (f x) (f y)) ↔
      ∀ s ∈ S, (s.map f).heads.IsChain r := by
  have : Std.Refl fun x y ↦ r (f x) (f y) := ⟨fun _ ↦ refl _⟩
  have : IsTrans H fun x y ↦ r (f x) (f y) := ⟨fun _ _ _ ↦ _root_.trans⟩
  simp only [heads_map, List.isChain_map]
  exact reflTransGen_step_le_iff (S := S) (r := fun x y ↦ r (f x) (f y))

/-- One head is no higher than another in the hierarchy of a family exactly when every assignment
of heights that never drops going up a spine of the family gives it a height no greater. -/
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

On a spine where no head recurs, the hierarchy of the spine alone is the order of its positions.
-/

/-- In the hierarchy of a single spine on which no head recurs, one head is no higher than another
exactly when the two are the same head, or both are on the spine and the first is at or below the
second. -/
theorem reflTransGen_step_singleton_iff [DecidableEq H] (hs : s.heads.Nodup) :
    Relation.ReflTransGen (Step {s}) c d ↔ c = d ∨ c ∈ s ∧ d ∈ s ∧ s.height c ≤ s.height d := by
  let R : H → H → Prop := fun x y ↦ x = y ∨ x ∈ s ∧ y ∈ s ∧ s.height x ≤ s.height y
  have : Std.Refl R := ⟨fun _ ↦ .inl rfl⟩
  have : IsTrans H R := ⟨by
    rintro x y z (rfl | ⟨hx, hy, hxy⟩) (rfl | ⟨hy', hz, hyz⟩)
    exacts [.inl rfl, .inr ⟨hy', hz, hyz⟩, .inr ⟨hx, hy, hxy⟩, .inr ⟨hx, hz, hxy.trans hyz⟩]⟩
  refine ⟨fun h ↦ (reflTransGen_step_le_iff (r := R)).2 (fun t ht ↦ ?_) c d h, ?_⟩
  · obtain rfl : t = s := ht
    refine List.isChain_iff_getElem.2 fun i hi ↦
      .inr ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
    simp only [height, hs.idxOf_getElem]
    exact Nat.le_succ i
  · rintro (rfl | ⟨hc, hd, hcd⟩)
    · exact .refl
    · have hc' : s.height c < s.heads.length := List.idxOf_lt_length_iff.2 hc
      have hd' : s.height d < s.heads.length := List.idxOf_lt_length_iff.2 hd
      have ec : s.heads[s.height c] = c := List.getElem_idxOf hc'
      have ed : s.heads[s.height d] = d := List.getElem_idxOf hd'
      obtain hlt | heq := hcd.lt_or_eq
      · exact ec ▸ ed ▸ List.pairwise_iff_getElem.1
          (pairwise_reflTransGen_step (S := {s}) rfl) _ _ hc' hd' hlt
      · have : c = d := by rw [← ec, ← ed]; simp only [heq]
        exact this ▸ .refl

/-!
### Deciding the hierarchy of a list of spines
-/

/-- The **steps** of a list of spines, as pairs of a head and the next head up. -/
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
