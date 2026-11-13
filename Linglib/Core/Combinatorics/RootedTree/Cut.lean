/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.UnorderedTree.Leaves
public import Linglib.Core.Data.Multiset.Bind
public import Linglib.Core.Data.Multiset.Convolution
public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.Data.Multiset.Sections
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Admissible-cut enumeration on rose trees

The combinatorics of admissible cuts, independent of the Hopf-algebra structures built on it in
`Core/Algebra/RootedTree/Coproduct/`. An admissible cut of a tree removes a set of subtrees, no
two on a common path to the root. It splits the tree into a crown, the multiset of removed
subtrees, and a trunk, what is left at the root. The enumeration is parameterized by an
extraction policy `extract : RoseTree α → Option (List (RoseTree α))`, called on each cut subtree:

- `extract t = none` forbids cuts at that subtree;
- `extract t = some []` removes it, leaving nothing in the parent's child slot;
- `extract t = some rs` removes it and leaves the replacement trees `rs` in its slot.

The cut bookkeeping is shared by every policy; only the remainder left at a cut varies. The
policy `leaveNothing`, which always leaves nothing, gives the cuts of the Connes–Kreimer coproduct.

## Main definitions

* `ConnesKreimer.rootCuts extract`: the enumeration of the pairs of a crown and a trunk.
* `ConnesKreimer.ExtractInvariant`: the policies that descend along `RoseTree.Perm`.
* `ConnesKreimer.leaveNothing`, `ConnesKreimer.admissibleCuts`: the policy that leaves nothing and
  its cuts on `UnorderedTree`.
* `ConnesKreimer.emptyCuts`: the enumeration with only the empty cut.
* `ConnesKreimer.CutChoice`, `ConnesKreimer.forestCutChoices cuts F`: a cut chosen for each tree
  of a forest, with its crown, its trunk and the number of trees it takes whole.
* `ConnesKreimer.CutChoice.HasExtractionCost`: each tree the choice cuts measures its crown and its
  trunk and a fixed amount for each tree extracted.
* `ConnesKreimer.countSingleCuts`: the number of single cuts with given crown and trunk.

## Main results

* `ConnesKreimer.childrenCuts_induction`: a relation between a list of children and its cuts
  holds of every cut once it holds of the empty list, of a cut at a child, of a cut inside a
  child, and of adding a child.
* `ConnesKreimer.rootCuts_proj_perm`: the projected enumeration is `Perm`-invariant for an
  invariant policy.
* `ConnesKreimer.rootCuts_filter_empty`: the empty cut is the unique cut with empty crown.
* `ConnesKreimer.admissibleCuts_node`: the admissible cuts of a node are the cut convolution over
  its children.
* `ConnesKreimer.CutChoice.HasExtractionCost.sum_map_add_mul_numWhole`: a choice of cuts keeps
  the measure of the forest up to its extraction cost.

`[UPSTREAM]` candidate.

## Implementation notes

`crown` is this library's word for the forest a cut removes, which none of its sources names. The
book writes it `π_C(T)`, and Connes and Kreimer speak of cut branches and a trunk.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### The enumeration -/

mutual
/-- The cuts of a tree under the policy `extract`, as pairs of a crown and a trunk. -/
def rootCuts (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Multiset (RoseTree α) × RoseTree α)
  | .node a cs => (childrenCuts extract cs).map fun p ↦ (p.1, .node a p.2)
/-- The cuts of a list of children, as pairs of a crown and the list of what remains. A surviving
    child contributes its trunk and a cut child contributes `extract` of it. -/
def childrenCuts (extract : RoseTree α → Option (List (RoseTree α))) :
    List (RoseTree α) → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((childCuts extract t ×ˢ childrenCuts extract ts) : Multiset _).map
        fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2)
/-- The choices at one child `t` are to cut `t` itself, with crown `{t}` and remainder
    `extract t` when the policy allows it, or to cut inside `t`. -/
def childCuts (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | t =>
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Multiset (RoseTree α)), r)})
      + (rootCuts extract t).map fun p ↦ (p.1, [p.2])
end

variable (extract : RoseTree α → Option (List (RoseTree α)))

@[simp] theorem rootCuts_node (a : α) (cs : List (RoseTree α)) :
    rootCuts extract (RoseTree.node a cs) =
      (childrenCuts extract cs).map fun p ↦ (p.1, .node a p.2) := by
  unfold rootCuts; rfl

@[simp] theorem childrenCuts_nil :
    childrenCuts extract ([] : List (RoseTree α)) =
      {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))} := by
  unfold childrenCuts; rfl

@[simp] theorem childrenCuts_cons (t : RoseTree α) (ts : List (RoseTree α)) :
    childrenCuts extract (t :: ts) =
      ((childCuts extract t ×ˢ childrenCuts extract ts) : Multiset _).map
        fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2) := by
  conv_lhs => unfold childrenCuts

@[simp] theorem childCuts_eq (t : RoseTree α) :
    childCuts extract t =
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Multiset (RoseTree α)), r)})
      + (rootCuts extract t).map fun p ↦ (p.1, [p.2]) := by
  conv_lhs => unfold childCuts

theorem childCuts_eq_none (t : RoseTree α) (h : extract t = none) :
    childCuts extract t = (rootCuts extract t).map fun p ↦ (p.1, [p.2]) := by
  rw [childCuts_eq, h]
  simp

theorem childCuts_eq_some (t : RoseTree α) (r : List (RoseTree α)) (h : extract t = some r) :
    childCuts extract t =
      (({t} : Multiset (RoseTree α)), r) ::ₘ
        (rootCuts extract t).map fun p ↦ (p.1, [p.2]) := by
  rw [childCuts_eq, h, Multiset.singleton_add]

example (a : α) : rootCuts extract (RoseTree.leaf a) = {(0, RoseTree.leaf a)} := by
  rw [RoseTree.leaf, rootCuts_node, childrenCuts_nil]
  rfl

@[simp] theorem childrenCuts_singleton (t : RoseTree α) :
    childrenCuts extract [t] = childCuts extract t := by
  rw [childrenCuts_cons, childrenCuts_nil, ← Multiset.cons_zero, Multiset.product_cons,
    Multiset.product_zero, add_zero, Multiset.map_map]
  exact (Multiset.map_congr rfl fun _ _ ↦ by simp).trans (Multiset.map_id _)

theorem childrenCuts_append (l₁ l₂ : List (RoseTree α)) :
    childrenCuts extract (l₁ ++ l₂) =
      ((childrenCuts extract l₁ ×ˢ childrenCuts extract l₂) : Multiset _).map
        fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2) := by
  change _ = Multiset.conv (M := Multiset (RoseTree α) × FreeAddMonoid (RoseTree α)) _ _
  induction l₁ with
  | nil =>
    rw [List.nil_append, childrenCuts_nil]
    exact (Multiset.singleton_zero_conv
      (M := Multiset (RoseTree α) × FreeAddMonoid (RoseTree α)) _).symm
  | cons t ts ih =>
    rw [List.cons_append, childrenCuts_cons, childrenCuts_cons]
    exact (congrArg (Multiset.conv (M := Multiset (RoseTree α) × FreeAddMonoid (RoseTree α)) _)
      ih).trans (Multiset.conv_assoc _ _ _).symm

/-! ### Induction over cuts

A relation `P cs q` between a list of children and its cuts holds of every cut once it holds of
the empty list, of a cut that the policy allows at a child, of a cut inside a child, and of adding
a child in front. The cases see the membership of the cuts they combine. -/

section Induction

variable {P : List (RoseTree α) → Multiset (RoseTree α) × List (RoseTree α) → Prop}

mutual

theorem childrenCuts_induction (nil : P [] (0, []))
    (cut : ∀ t r, extract t = some r → P [t] ({t}, r))
    (node : ∀ a cs q, q ∈ childrenCuts extract cs → P cs q →
      P [.node a cs] (q.1, [.node a q.2]))
    (cons : ∀ t ts a b, a ∈ childCuts extract t → b ∈ childrenCuts extract ts → P [t] a →
      P ts b → P (t :: ts) (a.1 + b.1, a.2 ++ b.2)) :
    ∀ cs, ∀ q ∈ childrenCuts extract cs, P cs q
  | [] => by
    intro q hq
    rw [childrenCuts_nil, Multiset.mem_singleton] at hq
    exact hq ▸ nil
  | t :: ts => by
    intro q hq
    rw [childrenCuts_cons] at hq
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hb⟩ := Multiset.mem_product.mp hab
    exact cons t ts a b ha hb (childCuts_induction nil cut node cons t a ha)
      (childrenCuts_induction nil cut node cons ts b hb)

theorem childCuts_induction (nil : P [] (0, []))
    (cut : ∀ t r, extract t = some r → P [t] ({t}, r))
    (node : ∀ a cs q, q ∈ childrenCuts extract cs → P cs q →
      P [.node a cs] (q.1, [.node a q.2]))
    (cons : ∀ t ts a b, a ∈ childCuts extract t → b ∈ childrenCuts extract ts → P [t] a →
      P ts b → P (t :: ts) (a.1 + b.1, a.2 ++ b.2)) :
    ∀ t, ∀ a ∈ childCuts extract t, P [t] a
  | .node x cs => by
    intro a ha
    rw [childCuts_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hE : extract (.node x cs) with
      | none => rw [hE] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hE, Multiset.mem_singleton] at h
        exact h ▸ cut _ r hE
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      rw [rootCuts_node] at hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
      exact node x cs q hq (childrenCuts_induction nil cut node cons cs q hq)

end

theorem rootCuts_induction (nil : P [] (0, []))
    (cut : ∀ t r, extract t = some r → P [t] ({t}, r))
    (node : ∀ a cs q, q ∈ childrenCuts extract cs → P cs q →
      P [.node a cs] (q.1, [.node a q.2]))
    (cons : ∀ t ts a b, a ∈ childCuts extract t → b ∈ childrenCuts extract ts → P [t] a →
      P ts b → P (t :: ts) (a.1 + b.1, a.2 ++ b.2)) :
    ∀ t, ∀ p ∈ rootCuts extract t, P [t] (p.1, [p.2])
  | .node a cs => by
    intro p hp
    rw [rootCuts_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact node a cs q hq (childrenCuts_induction extract nil cut node cons cs q hq)

end Induction

/-! ### Vertex conservation

When every remainder the policy leaves has `k` vertices in total, a cut conserves vertices up to
`k` per crown component. `leaveNothing` has `k = 0` and a policy leaving one leaf has `k = 1`. -/

theorem rootCuts_numNodes {k : ℕ}
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = k) :
    ∀ (t : RoseTree α), ∀ p ∈ rootCuts extract t,
      (Multiset.map RoseTree.numNodes p.1).sum + RoseTree.numNodes p.2 =
        RoseTree.numNodes t + k * Multiset.card p.1 := fun t p hp ↦ by
  simpa using rootCuts_induction extract
    (P := fun cs q ↦ (q.1.map RoseTree.numNodes).sum + (q.2.map RoseTree.numNodes).sum =
      (cs.map RoseTree.numNodes).sum + k * Multiset.card q.1)
    (by simp) (fun t r h ↦ by simp [hext t r h])
    (fun a cs q _ h ↦ by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RoseTree.numNodes_node]
      omega)
    (fun t ts a b _ _ ha hb ↦ by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Multiset.map_add,
        Multiset.sum_add, List.map_append, List.sum_append, Multiset.card_add] at *
      rw [Nat.mul_add]
      omega) t p hp

/-! ### Projection to unordered trees

A cut of a rose tree projects to `UnorderedTree` componentwise. On children the remainder list
becomes a multiset, and the combination of the cuts of two children becomes their convolution
`Multiset.conv`. -/

/-- Project the crown and the trunk of a cut to unordered trees. -/
def projCut (p : Multiset (RoseTree α) × RoseTree α) :
    Multiset (UnorderedTree α) × UnorderedTree α :=
  (p.1.map UnorderedTree.mk, UnorderedTree.mk p.2)

/-- Project the crown and the remainder list of a cut of a list of children. -/
def projChildrenCut (p : Multiset (RoseTree α) × List (RoseTree α)) :
    Multiset (UnorderedTree α) × Multiset (UnorderedTree α) :=
  (p.1.map UnorderedTree.mk, Multiset.ofList (p.2.map UnorderedTree.mk))

theorem projCut_node (a : α) (p : Multiset (RoseTree α) × List (RoseTree α)) :
    projCut (p.1, .node a p.2) =
      ((projChildrenCut p).1, UnorderedTree.node a (projChildrenCut p).2) :=
  Prod.ext rfl (UnorderedTree.node_mk_tree_list a p.2).symm

private theorem projChildrenCut_combine
    (p q : Multiset (RoseTree α) × List (RoseTree α)) :
    projChildrenCut (p.1 + q.1, p.2 ++ q.2) = projChildrenCut p + projChildrenCut q := by
  simp [projChildrenCut]

private theorem childrenCuts_cons_proj (t : RoseTree α) (ts : List (RoseTree α)) :
    (childrenCuts extract (t :: ts)).map projChildrenCut =
      ((childCuts extract t).map projChildrenCut).conv
        ((childrenCuts extract ts).map projChildrenCut) := by
  rw [childrenCuts_cons]
  exact Multiset.map_map_product_distrib projChildrenCut_combine _ _

/-! ### Policies that descend to unordered trees -/

/-- A policy is invariant when the projection of what it leaves at a cut depends only on the
    unordered tree that is cut. -/
def ExtractInvariant (extract : RoseTree α → Option (List (RoseTree α))) : Prop :=
  ∀ t s : RoseTree α, UnorderedTree.mk t = UnorderedTree.mk s →
    (extract t).map (List.map (UnorderedTree.mk (α := α))) =
      (extract s).map (List.map (UnorderedTree.mk (α := α)))

variable {extract}

private theorem childCuts_proj_congr (hExt : ExtractInvariant extract) {t s : RoseTree α}
    (hmk : UnorderedTree.mk t = UnorderedTree.mk s)
    (h : (rootCuts extract t).map projCut = (rootCuts extract s).map projCut) :
    (childCuts extract t).map projChildrenCut = (childCuts extract s).map projChildrenCut := by
  rw [childCuts_eq, childCuts_eq, Multiset.map_add, Multiset.map_add]
  congr 1
  · have hE := hExt t s hmk
    cases ht : extract t <;> cases hs : extract s <;> simp_all [projChildrenCut]
  · have h' := congrArg (Multiset.map fun q : Multiset (UnorderedTree α) × UnorderedTree α ↦
      (q.1, ({q.2} : Multiset (UnorderedTree α)))) h
    simpa [Multiset.map_map, Function.comp_def, projChildrenCut, projCut] using h'

private theorem childrenCuts_proj_perm (extract : RoseTree α → Option (List (RoseTree α)))
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    (childrenCuts extract cs).map projChildrenCut =
      (childrenCuts extract ds).map projChildrenCut := by
  induction h with
  | nil => rfl
  | cons c _ ih => rw [childrenCuts_cons_proj, childrenCuts_cons_proj, ih]
  | swap c d cs =>
    simp only [childrenCuts_cons_proj]
    exact (Multiset.conv_left_comm _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- For an invariant policy, the projected cuts of a tree depend only on the unordered tree. -/
theorem rootCuts_proj_perm (hExt : ExtractInvariant extract) {t s : RoseTree α}
    (h : RoseTree.Perm t s) : (rootCuts extract t).map projCut = (rootCuts extract s).map projCut := by
  refine h.induction_on fun a cs ds ih ↦ ?_
  have hL : (childrenCuts extract cs).map projChildrenCut =
      (childrenCuts extract ds).map projChildrenCut := by
    induction cs generalizing ds with
    | nil => rw [Multiset.coe_nil, Multiset.rel_zero_left, Multiset.coe_eq_zero] at ih; rw [ih]
    | cons c cs ihcs =>
      rw [← Multiset.cons_coe] at ih
      obtain ⟨d, G, hcd, hG, he⟩ := Multiset.rel_cons_left.1 ih
      induction G using Quotient.inductionOn with
      | h ds' =>
        rw [childrenCuts_proj_perm extract (Multiset.coe_eq_coe.1 he), childrenCuts_cons_proj,
          childrenCuts_cons_proj,
          childCuts_proj_congr hExt (UnorderedTree.mk_eq_mk_iff.mpr hcd.1) hcd.2, ihcs ds' hG]
  have hL' := congrArg (Multiset.map fun pf : Multiset (UnorderedTree α) ×
    Multiset (UnorderedTree α) ↦ (pf.1, UnorderedTree.node a pf.2)) hL
  simpa [Multiset.map_map, Function.comp_def, projCut_node] using hL'

variable (extract)

/-! ### Cut convolution

`treeCuts cuts t` lists the cuts of the tree `t` as a forest, including the cut that takes all
of `t`, and `forestCuts cuts F` combines them over the trees of a forest. Nothing here reads a
tree, so rose trees and unordered trees share these definitions, and
[a map between the enumerations carries the cuts along](##forestCuts_map). The admissible-cut
coproduct is a sum over these (`comulForestOfCuts_eq_sum` in `Coproduct/WithCuts.lean`). -/

section Convolution

variable {γ δ : Type*} (cuts : γ → Multiset (Multiset γ × γ))

/-- All the cuts of a tree with the trunk as a forest. They are the cut taking the whole tree,
    with crown `{t}` and empty trunk, and each cut in `cuts t` with a one-tree trunk. -/
def treeCuts (t : γ) : Multiset (Multiset γ × Multiset γ) :=
  ({t}, 0) ::ₘ (cuts t).map fun p ↦ (p.1, {p.2})

/-- The cuts of a forest combine one choice from `treeCuts cuts t` for each tree `t`. -/
def forestCuts (F : Multiset γ) : Multiset (Multiset γ × Multiset γ) :=
  (F.map (treeCuts cuts)).foldr Multiset.conv {(0, 0)}

theorem forestCuts_zero : forestCuts cuts (0 : Multiset γ) = {(0, 0)} := by
  simp [forestCuts]

theorem forestCuts_cons (t : γ) (F : Multiset γ) :
    forestCuts cuts (t ::ₘ F) = (treeCuts cuts t).conv (forestCuts cuts F) := by
  rw [forestCuts, Multiset.map_cons, Multiset.foldr_cons, forestCuts]

theorem forestCuts_singleton (t : γ) : forestCuts cuts {t} = treeCuts cuts t := by
  rw [← Multiset.cons_zero, forestCuts_cons, forestCuts_zero]
  exact Multiset.conv_singleton_zero _

theorem forestCuts_pair (t t' : γ) :
    forestCuts cuts {t, t'} = (treeCuts cuts t).conv (treeCuts cuts t') := by
  rw [Multiset.insert_eq_cons, forestCuts_cons, forestCuts_singleton]

theorem forestCuts_add (F G : Multiset γ) :
    forestCuts cuts (F + G) = (forestCuts cuts F).conv (forestCuts cuts G) := by
  induction F using Multiset.induction with
  | empty => rw [zero_add, forestCuts_zero]; exact (Multiset.singleton_zero_conv _).symm
  | cons t F ih =>
    rw [Multiset.cons_add, forestCuts_cons, forestCuts_cons, ih]
    exact (Multiset.conv_assoc _ _ _).symm

variable {cuts} {cuts' : δ → Multiset (Multiset δ × δ)} {f : γ → δ}

/-- A map carrying one enumeration to another carries the cuts of a tree along. -/
theorem treeCuts_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f)) (t : γ) :
    treeCuts cuts' (f t) =
      (treeCuts cuts t).map (Prod.map (Multiset.map f) (Multiset.map f)) := by
  simp [treeCuts, h, Multiset.map_map]

/-- A map carrying one enumeration to another carries the cuts of a forest along. -/
theorem forestCuts_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f))
    (F : Multiset γ) :
    forestCuts cuts' (F.map f) =
      (forestCuts cuts F).map (Prod.map (Multiset.map f) (Multiset.map f)) := by
  induction F using Multiset.induction with
  | empty => simp [forestCuts_zero]
  | cons t F ih =>
    rw [Multiset.map_cons, forestCuts_cons, treeCuts_map h, ih, forestCuts_cons]
    exact (Multiset.map_conv _ _ fun _ _ ↦
      Prod.ext (Multiset.map_add ..) (Multiset.map_add ..)).symm

end Convolution

/-! ### Cuts chosen tree by tree

A `CutChoice` records, for each tree of a forest, the crown and trunk of the cut chosen for it
beside the tree, and `forestCutChoices cuts F` lists the choices for `F`. Gathering the crowns and
the trunks of a choice gives a forest cut of `F` (`forestCuts_eq_map_forestCutChoices`), and the
record says where each tree went: into the crown whole, or cut and left as a trunk. -/

/-- A choice of cuts for the trees of a forest, each tree beside the crown and the trunk of the
    cut chosen for it. -/
abbrev CutChoice (α : Type*) :=
  Multiset (UnorderedTree α × (Multiset (UnorderedTree α) × Multiset (UnorderedTree α)))

namespace CutChoice

/-- The crown of a choice of cuts gathers the crowns chosen for its trees. -/
def crown (s : CutChoice α) : Multiset (UnorderedTree α) := (s.map Prod.snd).sum.1

/-- The trunk of a choice of cuts gathers the trunks its trees leave. -/
def trunk (s : CutChoice α) : Multiset (UnorderedTree α) := (s.map Prod.snd).sum.2

/-- The number of trees a choice of cuts takes whole, leaving no trunk. -/
def numWhole [DecidableEq (UnorderedTree α)] (s : CutChoice α) : ℕ := s.countP (·.2.2 = 0)

variable {s t : CutChoice α}
  {x : UnorderedTree α × (Multiset (UnorderedTree α) × Multiset (UnorderedTree α))}

@[simp] theorem crown_zero : crown (0 : CutChoice α) = 0 := by simp [crown]

@[simp] theorem trunk_zero : trunk (0 : CutChoice α) = 0 := by simp [trunk]

@[simp] theorem crown_cons : crown (x ::ₘ s) = x.2.1 + s.crown := by simp [crown]

@[simp] theorem trunk_cons : trunk (x ::ₘ s) = x.2.2 + s.trunk := by simp [trunk]

@[simp] theorem crown_add : crown (s + t) = s.crown + t.crown := by simp [crown]

@[simp] theorem trunk_add : trunk (s + t) = s.trunk + t.trunk := by simp [trunk]

@[simp] theorem crown_singleton : crown {x} = x.2.1 := by simp [crown]

@[simp] theorem trunk_singleton : trunk {x} = x.2.2 := by simp [trunk]

theorem mem_crown {T : UnorderedTree α} : T ∈ s.crown ↔ ∃ x ∈ s, T ∈ x.2.1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih => simp [ih]

theorem mem_trunk {T : UnorderedTree α} : T ∈ s.trunk ↔ ∃ x ∈ s, T ∈ x.2.2 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih => simp [ih]

section NumWhole

variable [DecidableEq (UnorderedTree α)]

@[simp] theorem numWhole_zero : numWhole (0 : CutChoice α) = 0 := Multiset.countP_zero _

@[simp] theorem numWhole_cons : numWhole (x ::ₘ s) = s.numWhole + if x.2.2 = 0 then 1 else 0 :=
  Multiset.countP_cons _ _ _

@[simp] theorem numWhole_singleton : numWhole {x} = if x.2.2 = 0 then 1 else 0 := by
  rw [← Multiset.cons_zero, numWhole_cons, numWhole_zero, Nat.zero_add]

@[simp] theorem numWhole_add : numWhole (s + t) = s.numWhole + t.numWhole :=
  Multiset.countP_add _ _ _

theorem numWhole_eq_zero : s.numWhole = 0 ↔ ∀ x ∈ s, x.2.2 ≠ 0 :=
  Multiset.countP_eq_zero

end NumWhole

/-- A choice of cuts has extraction cost `k` in a measure `μ` when each tree it cuts rather than
    takes whole measures its crown and its trunk together, and `k` more for each tree it
    extracts. -/
def HasExtractionCost (μ : UnorderedTree α → ℕ) (k : ℕ) (s : CutChoice α) : Prop :=
  ∀ x ∈ s, x.2.2 ≠ 0 →
    μ x.1 = (x.2.1.map μ).sum + (x.2.2.map μ).sum + k * Multiset.card x.2.1

end CutChoice

open CutChoice

section CutChoices

/-- The ways of choosing one cut of `treeCuts cuts T` for each tree `T` of a forest. -/
def forestCutChoices
    (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))
    (F : Multiset (UnorderedTree α)) : Multiset (CutChoice α) :=
  Multiset.Sections (F.map fun T ↦ (treeCuts cuts T).map (Prod.mk T))

variable (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))

theorem forestCutChoices_zero : forestCutChoices cuts 0 = {0} := by
  simp [forestCutChoices, Multiset.sections_zero]

theorem forestCutChoices_cons (T : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    forestCutChoices cuts (T ::ₘ F) =
      (treeCuts cuts T).bind fun a ↦ (forestCutChoices cuts F).map ((T, a) ::ₘ ·) := by
  rw [forestCutChoices, Multiset.map_cons, Multiset.sections_cons, Multiset.bind_map]
  rfl

theorem forestCuts_eq_map_forestCutChoices (F : Multiset (UnorderedTree α)) :
    forestCuts cuts F = (forestCutChoices cuts F).map fun s ↦ (s.crown, s.trunk) := by
  change _ = (forestCutChoices cuts F).map fun s ↦ (s.map Prod.snd).sum
  induction F using Multiset.induction with
  | empty => simp [forestCuts_zero, forestCutChoices_zero]
  | cons T F ih =>
    rw [forestCuts_cons, ih, forestCutChoices_cons, Multiset.map_bind, Multiset.conv_eq_bind]
    simp only [Multiset.map_map, Function.comp_def, Multiset.map_cons, Multiset.sum_cons]

variable {cuts} {F G : Multiset (UnorderedTree α)} {s t : CutChoice α}
  {x : UnorderedTree α × (Multiset (UnorderedTree α) × Multiset (UnorderedTree α))}

theorem mem_treeCuts {T : UnorderedTree α}
    {a : Multiset (UnorderedTree α) × Multiset (UnorderedTree α)} :
    a ∈ treeCuts cuts T ↔ a = ({T}, 0) ∨ ∃ p ∈ cuts T, (p.1, {p.2}) = a := by
  simp [treeCuts]

theorem map_fst_of_mem_forestCutChoices (hs : s ∈ forestCutChoices cuts F) :
    s.map Prod.fst = F := by
  induction F using Multiset.induction generalizing s with
  | empty => rw [forestCutChoices_zero, Multiset.mem_singleton] at hs; rw [hs, Multiset.map_zero]
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.mem_bind] at hs
    obtain ⟨a, -, hs⟩ := hs
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.mp hs
    rw [Multiset.map_cons, ih hs']

theorem fst_mem_of_mem_forestCutChoices (hs : s ∈ forestCutChoices cuts F) (hx : x ∈ s) :
    x.1 ∈ F :=
  map_fst_of_mem_forestCutChoices hs ▸ Multiset.mem_map_of_mem Prod.fst hx

theorem mem_treeCuts_of_mem_forestCutChoices (hs : s ∈ forestCutChoices cuts F) (hx : x ∈ s) :
    x.2 ∈ treeCuts cuts x.1 := by
  induction F using Multiset.induction generalizing s with
  | empty =>
    rw [forestCutChoices_zero, Multiset.mem_singleton] at hs
    exact absurd (hs ▸ hx) (Multiset.notMem_zero x)
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.mem_bind] at hs
    obtain ⟨a, ha, hs⟩ := hs
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.mp hs
    rcases Multiset.mem_cons.mp hx with rfl | hx
    exacts [ha, ih hs' hx]

theorem snd_eq_of_mem_forestCutChoices (hs : s ∈ forestCutChoices cuts F) (hx : x ∈ s)
    (h : x.2.2 = 0) : x.2 = ({x.1}, 0) := by
  rcases mem_treeCuts.mp (mem_treeCuts_of_mem_forestCutChoices hs hx) with h' | ⟨p, -, h'⟩
  · exact h'
  · rw [← h'] at h; exact absurd h (Multiset.singleton_ne_zero _)

theorem CutChoice.fst_mem_crown (hs : s ∈ forestCutChoices cuts F) (hx : x ∈ s)
    (h : x.2.2 = 0) : x.1 ∈ s.crown :=
  mem_crown.mpr ⟨x, hx, by simp [snd_eq_of_mem_forestCutChoices hs hx h]⟩

theorem CutChoice.HasExtractionCost.of_mem_forestCutChoices {μ : UnorderedTree α → ℕ} {k : ℕ}
    (hs : s ∈ forestCutChoices cuts F)
    (h : ∀ x ∈ s, ∀ p ∈ cuts x.1, (p.1, {p.2}) = x.2 →
      μ x.1 = (p.1.map μ).sum + μ p.2 + k * Multiset.card p.1) :
    s.HasExtractionCost μ k := by
  intro x hx h0
  rcases mem_treeCuts.mp (mem_treeCuts_of_mem_forestCutChoices hs hx) with h2 | ⟨p, hp, h2⟩
  · exact absurd (by rw [h2]) h0
  · rw [← h2]
    simpa using h x hx p hp h2

section DecidableEq

variable [DecidableEq (UnorderedTree α)]

theorem CutChoice.card_trunk_add_numWhole (hs : s ∈ forestCutChoices cuts F) :
    Multiset.card s.trunk + s.numWhole = Multiset.card F := by
  induction F using Multiset.induction generalizing s with
  | empty => rw [forestCutChoices_zero, Multiset.mem_singleton] at hs; simp [hs]
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.mem_bind] at hs
    obtain ⟨a, ha, hs⟩ := hs
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.mp hs
    have := ih hs'
    rcases mem_treeCuts.mp ha with rfl | ⟨p, -, rfl⟩ <;> simp <;> omega

theorem CutChoice.card_add_numWhole_le_card_crown (hs : s ∈ forestCutChoices cuts F)
    (hx : x ∈ s) (h : x.2.2 ≠ 0) : Multiset.card x.2.1 + s.numWhole ≤ Multiset.card s.crown := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  have ht : ∀ y ∈ t, y.2.2 = 0 → y.2 = ({y.1}, 0) := fun y hy ↦
    snd_eq_of_mem_forestCutChoices hs (Multiset.mem_cons_of_mem hy)
  simp only [numWhole_cons, h, ite_false, add_zero, crown_cons, Multiset.card_add,
    add_le_add_iff_left]
  clear hs hx
  induction t using Multiset.induction with
  | empty => simp
  | cons y t ih =>
    have := ih fun z hz ↦ ht z (Multiset.mem_cons_of_mem hz)
    by_cases hy : y.2.2 = 0
    · simp only [numWhole_cons, ite_true, crown_cons, Multiset.card_add,
        ht y (Multiset.mem_cons_self _ _) hy, Multiset.card_singleton]
      omega
    · simp only [numWhole_cons, hy, ite_false, crown_cons, Multiset.card_add]
      omega

/-- A choice of cuts with extraction cost `k` in `μ` keeps the measure of the forest, counting
    `k` for each tree it extracts and each tree it takes whole as extracting itself. -/
theorem CutChoice.HasExtractionCost.sum_map_add_mul_numWhole {μ : UnorderedTree α → ℕ} {k : ℕ}
    (hs : s ∈ forestCutChoices cuts F) (hc : s.HasExtractionCost μ k) :
    (F.map μ).sum + k * s.numWhole =
      (s.crown.map μ).sum + (s.trunk.map μ).sum + k * Multiset.card s.crown := by
  induction F using Multiset.induction generalizing s with
  | empty => rw [forestCutChoices_zero, Multiset.mem_singleton] at hs; simp [hs]
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.mem_bind] at hs
    obtain ⟨a, ha, hs⟩ := hs
    obtain ⟨s', hs', rfl⟩ := Multiset.mem_map.mp hs
    have := ih hs' fun x hx ↦ hc x (Multiset.mem_cons_of_mem hx)
    have e : (fun x ↦ μ x) = μ := rfl
    rcases mem_treeCuts.mp ha with rfl | ⟨p, -, rfl⟩
    · simp only [Multiset.map_cons, Multiset.sum_cons, numWhole_cons, crown_cons, trunk_cons,
        ite_true, Multiset.map_add, Multiset.sum_add, Multiset.card_add, Multiset.map_singleton,
        Multiset.sum_singleton, Multiset.card_singleton, Multiset.map_zero, Multiset.sum_zero,
        Nat.mul_add, Nat.mul_one, e]
      omega
    · have h := hc _ (Multiset.mem_cons_self _ _) (Multiset.singleton_ne_zero _)
      simp only [Multiset.map_singleton, Multiset.sum_singleton] at h
      simp only [Multiset.map_cons, Multiset.sum_cons, numWhole_cons, crown_cons, trunk_cons,
        Multiset.singleton_ne_zero, ite_false, add_zero, Multiset.map_add, Multiset.sum_add,
        Multiset.card_add, Multiset.map_singleton, Multiset.sum_singleton, Nat.mul_add, e]
      omega

end DecidableEq

theorem add_mem_forestCutChoices (hs : s ∈ forestCutChoices cuts F)
    (ht : t ∈ forestCutChoices cuts G) : s + t ∈ forestCutChoices cuts (F + G) := by
  rw [forestCutChoices, Multiset.map_add, Multiset.sections_add]
  exact Multiset.mem_bind.mpr ⟨s, hs, Multiset.mem_map.mpr ⟨t, ht, rfl⟩⟩

theorem map_whole_mem_forestCutChoices (F : Multiset (UnorderedTree α)) :
    F.map (fun T ↦ (T, ({T}, 0))) ∈ forestCutChoices cuts F := by
  induction F using Multiset.induction with
  | empty => simp [forestCutChoices_zero]
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.map_cons]
    exact Multiset.mem_bind.mpr ⟨_, Multiset.mem_cons_self _ _, Multiset.mem_map.mpr ⟨_, ih, rfl⟩⟩

theorem map_uncut_mem_forestCutChoices
    (h : ∀ T ∈ F, ((0 : Multiset (UnorderedTree α)), T) ∈ cuts T) :
    F.map (fun T ↦ (T, (0, {T}))) ∈ forestCutChoices cuts F := by
  induction F using Multiset.induction with
  | empty => simp [forestCutChoices_zero]
  | cons T F ih =>
    rw [forestCutChoices_cons, Multiset.map_cons]
    exact Multiset.mem_bind.mpr ⟨_, Multiset.mem_cons_of_mem
      (Multiset.mem_map_of_mem (fun p ↦ (p.1, {p.2})) (h T (Multiset.mem_cons_self _ _))),
      Multiset.mem_map.mpr ⟨_, ih fun U hU ↦ h U (Multiset.mem_cons_of_mem hU), rfl⟩⟩

end CutChoices

namespace CutChoice

variable (F : Multiset (UnorderedTree α))

@[simp] theorem crown_map_whole : crown (F.map fun T ↦ (T, ({T}, 0))) = F := by
  induction F using Multiset.induction <;> simp_all [Multiset.singleton_add]

@[simp] theorem trunk_map_whole : trunk (F.map fun T ↦ (T, ({T}, 0))) = 0 := by
  induction F using Multiset.induction <;> simp_all

@[simp] theorem numWhole_map_whole [DecidableEq (UnorderedTree α)] :
    numWhole (F.map fun T ↦ (T, ({T}, 0))) = Multiset.card F := by
  induction F using Multiset.induction <;> simp_all

@[simp] theorem crown_map_uncut : crown (F.map fun T ↦ (T, (0, {T}))) = 0 := by
  induction F using Multiset.induction <;> simp_all

@[simp] theorem trunk_map_uncut : trunk (F.map fun T ↦ (T, (0, {T}))) = F := by
  induction F using Multiset.induction <;> simp_all [Multiset.singleton_add]

theorem hasExtractionCost_map_whole (μ : UnorderedTree α → ℕ) (k : ℕ) :
    HasExtractionCost μ k (F.map fun T ↦ (T, ({T}, 0))) := by
  intro x hx h
  obtain ⟨T, -, rfl⟩ := Multiset.mem_map.mp hx
  exact absurd rfl h

end CutChoice

/-! ### The empty cut -/

mutual

/-- The empty cut is the unique cut with empty crown. -/
theorem rootCuts_filter_empty :
    ∀ (T : RoseTree α),
      (rootCuts extract T).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), T)} : Multiset _)
  | .node a cs => by
    rw [rootCuts_node, Multiset.filter_map]
    simp only [Function.comp_def]
    rw [childrenCuts_filter_empty cs, Multiset.map_singleton]

theorem childrenCuts_filter_empty :
    ∀ (cs : List (RoseTree α)),
      (childrenCuts extract cs).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), cs)} : Multiset _)
  | [] => by simp
  | t :: ts => by
    rw [childrenCuts_cons, Multiset.filter_map,
      Multiset.filter_congr (q := fun x ↦ x.1.1.card = 0 ∧ x.2.1.card = 0) fun x _ ↦ by
        simp only [Function.comp_apply, Multiset.card_add, Nat.add_eq_zero_iff],
      Multiset.filter_product
        (fun x : Multiset (RoseTree α) × List (RoseTree α) ↦ x.1.card = 0)
        (fun x : Multiset (RoseTree α) × List (RoseTree α) ↦ x.1.card = 0),
      childCuts_filter_empty t, childrenCuts_filter_empty ts]
    rfl

theorem childCuts_filter_empty :
    ∀ (t : RoseTree α),
      (childCuts extract t).filter (fun p ↦ p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), [t])} : Multiset _)
  | t => by
    have h : ((rootCuts extract t).map fun p ↦ (p.1, [p.2])).filter (fun p ↦ p.1.card = 0) =
        {((0 : Multiset (RoseTree α)), [t])} := by
      rw [Multiset.filter_map]
      simp only [Function.comp_def]
      rw [rootCuts_filter_empty t, Multiset.map_singleton]
    cases hx : extract t with
    | none => rw [childCuts_eq_none extract t hx, h]
    | some r =>
      rw [childCuts_eq_some extract t r hx, Multiset.filter_cons_of_neg _ (by simp), h]

end

/-! ### Admissible cuts

The policy that leaves nothing at a cut gives the admissible cuts of the Connes–Kreimer
coproduct. It is invariant, so its cuts descend to `UnorderedTree`, where the cuts of a node are
the cut convolution over its children. -/

/-- The policy `leaveNothing` cuts anywhere and leaves nothing in place of the cut subtree. -/
def leaveNothing : RoseTree α → Option (List (RoseTree α)) := fun _ ↦ some []

theorem extractInvariant_leaveNothing : ExtractInvariant (leaveNothing (α := α)) := fun _ _ _ ↦ rfl

/-- The admissible cuts of an unordered tree, as pairs of a crown and a trunk. -/
def admissibleCuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α) :=
  Quotient.lift (fun T ↦ (rootCuts leaveNothing T).map projCut)
    fun _ _ h ↦ rootCuts_proj_perm extractInvariant_leaveNothing h

@[simp] theorem admissibleCuts_mk (T : RoseTree α) :
    admissibleCuts (UnorderedTree.mk T) = (rootCuts leaveNothing T).map projCut := rfl

theorem admissibleCuts_leaf (a : α) :
    admissibleCuts (UnorderedTree.leaf a : UnorderedTree α) =
      ({((0 : Multiset (UnorderedTree α)), UnorderedTree.leaf a)} : Multiset _) := by
  rw [UnorderedTree.leaf, RoseTree.leaf, admissibleCuts_mk, rootCuts_node, childrenCuts_nil]
  rfl

/-- The number of admissible cuts of `T` whose crown is `{T₁}` and whose trunk is
    `T₂`. -/
def countSingleCuts [DecidableEq α] (T T₁ T₂ : UnorderedTree α) : ℕ :=
  (admissibleCuts T).countP fun p ↦ p.1 = ({T₁} : Multiset (UnorderedTree α)) ∧ p.2 = T₂

private theorem treeCuts_admissibleCuts_mk (t : RoseTree α) :
    treeCuts admissibleCuts (UnorderedTree.mk t) =
      (childCuts leaveNothing t).map projChildrenCut := by
  rw [childCuts_eq_some leaveNothing t [] rfl, Multiset.map_cons, treeCuts, admissibleCuts_mk,
    Multiset.map_map, Multiset.map_map]
  rfl

private theorem forestCuts_admissibleCuts_coe (ps : List (RoseTree α)) :
    forestCuts admissibleCuts (Multiset.ofList (ps.map UnorderedTree.mk)) =
      (childrenCuts leaveNothing ps).map projChildrenCut := by
  induction ps with
  | nil => rw [childrenCuts_nil, Multiset.map_singleton]; exact forestCuts_zero _
  | cons p ps ih =>
    rw [List.map_cons, ← Multiset.cons_coe, forestCuts_cons, ih, treeCuts_admissibleCuts_mk,
      childrenCuts_cons_proj]

/-- The admissible cuts of a node choose, for each child, to cut it whole or to cut inside it. -/
@[simp] theorem admissibleCuts_node (a : α) (F : Multiset (UnorderedTree α)) :
    admissibleCuts (UnorderedTree.node a F) =
      (forestCuts admissibleCuts F).map fun pf ↦ (pf.1, UnorderedTree.node a pf.2) := by
  induction F using UnorderedTree.forest_inductionOn with
  | h ps =>
    rw [forestCuts_admissibleCuts_coe, UnorderedTree.node_mk_tree_list, admissibleCuts_mk,
      rootCuts_node, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun p _ ↦ projCut_node a p

/-- The enumeration whose only cut is the empty cut. Its coproduct makes every tree primitive. -/
def emptyCuts (T : UnorderedTree α) : Multiset (Multiset (UnorderedTree α) × UnorderedTree α) :=
  {(0, T)}

theorem forestCuts_emptyCuts (F : Multiset (UnorderedTree α)) :
    forestCuts emptyCuts F = Multiset.antidiagonal F := by
  induction F using Multiset.induction with
  | empty => rw [forestCuts_zero, Multiset.antidiagonal_zero]
  | cons T F ih =>
    rw [forestCuts_cons, ih, Multiset.antidiagonal_cons, treeCuts, emptyCuts, Multiset.conv,
      Multiset.map_singleton, ← Multiset.cons_zero (0, _), Multiset.cons_product,
      Multiset.cons_product, Multiset.zero_product, add_zero, Multiset.map_add, Multiset.map_map,
      Multiset.map_map, add_comm]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ ↦ by
      simp [Prod.ext_iff, Prod.map, Multiset.singleton_add]

theorem admissibleCuts_filter_empty (T : UnorderedTree α) :
    (admissibleCuts T).filter (fun p ↦ p.1.card = 0) = {((0 : Multiset (UnorderedTree α)), T)} :=
  Quotient.inductionOn T fun t ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, admissibleCuts_mk, Multiset.filter_map]
    simp only [Function.comp_def, projCut, Multiset.card_map]
    rw [rootCuts_filter_empty leaveNothing t, Multiset.map_singleton]
    rfl

end ConnesKreimer
