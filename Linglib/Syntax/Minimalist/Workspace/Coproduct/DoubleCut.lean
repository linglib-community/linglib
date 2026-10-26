/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Tactic.Abel

/-!
# Double cuts of rose trees

Both composites `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` enumerate the pairs of nested admissible
cuts of a tree, the second cut taken in the crown or in the trunk of the first. For a coherent
trace encoder the two enumerations agree up to the order of children. This file proves the
agreement on rose trees, where the cut enumeration recurses structurally, and `Trace.lean`
descends it to `UnorderedTree`, where it is the coassociativity of the coproduct `Δ^c` of
Marcolli, Chomsky and Berwick (their Lemma 1.2.10, p. 37).

## Main results

* `DoubleCut.coassT`: the two double-cut enumerations of a tree agree after projection.
* `DoubleCut.coassL`, `DoubleCut.coassA`: the same for a list of children and for one child;
  `coassA` is where trace coherence reconciles the marker a deeper cut writes on a trunk.
* `DoubleCut.dclN_clconv`, `DoubleCut.dcrN_clconv`: the two second cuts are multiplicative over
  the convolution `clconv` of the cuts of a list of children.

## References

* [marcolli-chomsky-berwick-2025]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree ConnesKreimer

namespace DoubleCut

variable {α β : Type*}

abbrev FP (α : Type*) := Multiset (RoseTree α)
abbrev Pair (α : Type*) := FP α × FP α

/-- RoseTree tree-cut enumerator (crown forest, trunk forest). -/
def treeCutsP (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    Multiset (Pair (α ⊕ β)) :=
  ({t}, 0) ::ₘ (cutSummandsCP τ t).map (fun p => (p.1, {p.2}))

/-- Forest-cut enumerator: convolution over the component trees. -/
def forestCutsP (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    Multiset (Pair (α ⊕ β)) :=
  (F.map (treeCutsP τ)).foldr Multiset.conv {(0, 0)}

/-- LHS double-cut: re-cut the crown. -/
def dcLHSP (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × FP (α ⊕ β)) :=
  (treeCutsP τ t).bind (fun AB =>
    (forestCutsP τ AB.1).map (fun A12 => (A12.1, A12.2, AB.2)))

/-- RHS double-cut: re-cut the trunk. -/
def dcRHSP (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × FP (α ⊕ β)) :=
  (treeCutsP τ t).bind (fun AB =>
    (forestCutsP τ AB.2).map (fun B12 => (AB.1, B12.1, B12.2)))

/-- Forest double-cut LHS (outer is a forest cut). -/
def dcForestLHSP (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × FP (α ⊕ β)) :=
  (forestCutsP τ F).bind (fun AB =>
    (forestCutsP τ AB.1).map (fun A12 => (A12.1, A12.2, AB.2)))

def dcForestRHSP (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × FP (α ⊕ β)) :=
  (forestCutsP τ F).bind (fun AB =>
    (forestCutsP τ AB.2).map (fun B12 => (AB.1, B12.1, B12.2)))

/-- Projection of a triple of planar forests to nonplanar (mod planar order). -/
def proj3 (q : FP (α ⊕ β) × FP (α ⊕ β) × FP (α ⊕ β)) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk, q.2.2.map UnorderedTree.mk)

/-! ### Basic recursions for forestCutsP -/

theorem forestCutsP_zero (τ : RoseTree (α ⊕ β) → β) :
    forestCutsP τ (0 : FP (α ⊕ β)) = {(0, 0)} := by
  unfold forestCutsP; simp

theorem forestCutsP_cons (τ : RoseTree (α ⊕ β) → β)
    (t : RoseTree (α ⊕ β)) (F : FP (α ⊕ β)) :
    forestCutsP τ (t ::ₘ F) = Multiset.conv (treeCutsP τ t) (forestCutsP τ F) := by
  unfold forestCutsP
  rw [Multiset.map_cons, Multiset.foldr_cons]

theorem forestCutsP_singleton (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    forestCutsP τ {t} = treeCutsP τ t := by
  rw [show ({t} : FP (α ⊕ β)) = t ::ₘ 0 from rfl, forestCutsP_cons, forestCutsP_zero]
  exact Multiset.conv_singleton_zero _

theorem forestCutsP_add (τ : RoseTree (α ⊕ β) → β) (F G : FP (α ⊕ β)) :
    forestCutsP τ (F + G) = Multiset.conv (forestCutsP τ F) (forestCutsP τ G) := by
  induction F using Multiset.induction with
  | empty => rw [zero_add, forestCutsP_zero]; exact (Multiset.singleton_zero_conv _).symm
  | cons t F ih =>
    rw [Multiset.cons_add, forestCutsP_cons, forestCutsP_cons, ih]
    exact (Multiset.conv_assoc _ _ _).symm

/-! ### Multiplicativity machinery -/

abbrev Triple (α : Type*) := FP α × FP α × FP α

/-! ### proj3 is additive -/

theorem proj3_add (p q : Triple (α ⊕ β)) : proj3 (p + q) = proj3 p + proj3 q := by
  obtain ⟨X, Y, Z⟩ := p; obtain ⟨X', Y', Z'⟩ := q
  simp only [proj3, Prod.mk_add_mk, Multiset.map_add]

theorem proj3_conv (X Y : Multiset (Triple (α ⊕ β))) :
    (Multiset.conv X Y).map proj3 = Multiset.conv (X.map proj3) (Y.map proj3) :=
  Multiset.map_conv X Y proj3_add

/-! ### The two second-cut maps are monoid homs -/

/-- The left-hand second cut re-cuts the crown `p.1`, carrying the trunk `p.2`. -/
def hL (τ : RoseTree (α ⊕ β) → β) (p : Pair (α ⊕ β)) : Multiset (Triple (α ⊕ β)) :=
  (forestCutsP τ p.1).map (fun A12 => (A12.1, A12.2, p.2))

/-- The right-hand second cut re-cuts the trunk `p.2`, carrying the crown `p.1`. -/
def hR (τ : RoseTree (α ⊕ β) → β) (p : Pair (α ⊕ β)) : Multiset (Triple (α ⊕ β)) :=
  (forestCutsP τ p.2).map (fun B12 => (p.1, B12.1, B12.2))

theorem hL_hom (τ : RoseTree (α ⊕ β) → β) (p q : Pair (α ⊕ β)) :
    hL τ (p + q) = Multiset.conv (hL τ p) (hL τ q) := by
  show (forestCutsP τ (p.1 + q.1)).map (fun A12 => (A12.1, A12.2, p.2 + q.2)) = _
  rw [forestCutsP_add]
  refine Multiset.map_conv (f := fun X : Pair (α ⊕ β) ↦ (X.1, X.2, p.2))
    (f' := fun Y : Pair (α ⊕ β) ↦ (Y.1, Y.2, q.2))
    (g := fun A12 : Pair (α ⊕ β) ↦ (A12.1, A12.2, p.2 + q.2)) _ _ ?_
  intro x y; rfl

theorem hR_hom (τ : RoseTree (α ⊕ β) → β) (p q : Pair (α ⊕ β)) :
    hR τ (p + q) = Multiset.conv (hR τ p) (hR τ q) := by
  show (forestCutsP τ (p.2 + q.2)).map (fun B12 => (p.1 + q.1, B12.1, B12.2)) = _
  rw [forestCutsP_add]
  refine Multiset.map_conv (f := fun X : Pair (α ⊕ β) ↦ (p.1, X.1, X.2))
    (f' := fun Y : Pair (α ⊕ β) ↦ (q.1, Y.1, Y.2))
    (g := fun B12 : Pair (α ⊕ β) ↦ (p.1 + q.1, B12.1, B12.2)) _ _ ?_
  intro x y; rfl

/-! ### Double-cut enumerators as binds of `hL`/`hR` -/

theorem dcLHSP_eq_bind (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcLHSP τ t = (treeCutsP τ t).bind (hL τ) := rfl

theorem dcRHSP_eq_bind (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcRHSP τ t = (treeCutsP τ t).bind (hR τ) := rfl

theorem dcForestLHSP_eq_bind (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    dcForestLHSP τ F = (forestCutsP τ F).bind (hL τ) := rfl

theorem dcForestRHSP_eq_bind (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    dcForestRHSP τ F = (forestCutsP τ F).bind (hR τ) := rfl

/-! ### Multiplicativity of the forest double-cut -/

theorem dcForestLHSP_cons (τ : RoseTree (α ⊕ β) → β)
    (t : RoseTree (α ⊕ β)) (F : FP (α ⊕ β)) :
    dcForestLHSP τ (t ::ₘ F) = Multiset.conv (dcLHSP τ t) (dcForestLHSP τ F) := by
  rw [dcForestLHSP_eq_bind, forestCutsP_cons, Multiset.bind_conv (hL_hom τ),
      ← dcLHSP_eq_bind, ← dcForestLHSP_eq_bind]

theorem dcForestRHSP_cons (τ : RoseTree (α ⊕ β) → β)
    (t : RoseTree (α ⊕ β)) (F : FP (α ⊕ β)) :
    dcForestRHSP τ (t ::ₘ F) = Multiset.conv (dcRHSP τ t) (dcForestRHSP τ F) := by
  rw [dcForestRHSP_eq_bind, forestCutsP_cons, Multiset.bind_conv (hR_hom τ),
      ← dcRHSP_eq_bind, ← dcForestRHSP_eq_bind]

theorem dcForestLHSP_zero (τ : RoseTree (α ⊕ β) → β) :
    dcForestLHSP τ (0 : FP (α ⊕ β)) = {(0, 0, 0)} := by
  rw [dcForestLHSP_eq_bind, forestCutsP_zero, Multiset.singleton_bind]
  show (forestCutsP τ 0).map (fun A12 => (A12.1, A12.2, (0 : FP (α ⊕ β)))) = _
  rw [forestCutsP_zero, Multiset.map_singleton]

theorem dcForestRHSP_zero (τ : RoseTree (α ⊕ β) → β) :
    dcForestRHSP τ (0 : FP (α ⊕ β)) = {(0, 0, 0)} := by
  rw [dcForestRHSP_eq_bind, forestCutsP_zero, Multiset.singleton_bind]
  show (forestCutsP τ 0).map (fun B12 => ((0 : FP (α ⊕ β)), B12.1, B12.2)) = _
  rw [forestCutsP_zero, Multiset.map_singleton]

/-! ### Forest coassoc from per-component tree coassoc -/

theorem coassFP_of_components (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β))
    (H : ∀ t ∈ F, (dcLHSP τ t).map proj3 = (dcRHSP τ t).map proj3) :
    (dcForestLHSP τ F).map proj3 = (dcForestRHSP τ F).map proj3 := by
  induction F using Multiset.induction with
  | empty => rw [dcForestLHSP_zero, dcForestRHSP_zero]
  | cons t F ih =>
    rw [dcForestLHSP_cons, dcForestRHSP_cons, proj3_conv, proj3_conv,
        H t (Multiset.mem_cons_self t F),
        ih (fun s hs => H s (Multiset.mem_cons_of_mem hs))]

/-! ### Node-level reduction of the per-tree double cut

The children-list cut enumerator (with trace leaves in the remainder),
distinct from `forestCutsP` (deletion). `treeCutsP`/`dcLHSP`/`dcRHSP` of a
`node a cs` decompose over it. -/

/-- Children-list cut enumerator: `cutListSummandsG (extractC τ)`. -/
abbrev Cl (τ : RoseTree (α ⊕ β) → β) (cs : List (RoseTree (α ⊕ β))) :
    Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :=
  cutListSummandsG (extractC τ) cs

/-- The cuts `treeCutsP` of a node are the full cut and the root-preserving cuts coming
    from the children-list cut wrapped with `node a`. -/
theorem treeCutsP_node (τ : RoseTree (α ⊕ β) → β) (a : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    treeCutsP τ (RoseTree.node a cs) =
      (({RoseTree.node a cs}, 0) : Pair (α ⊕ β)) ::ₘ
        (Cl τ cs).map (fun p => ((p.1, {RoseTree.node a p.2}) : Pair (α ⊕ β))) := by
  unfold treeCutsP
  rw [cutSummandsCP_node, Multiset.map_map]
  rfl

/-- The left-hand double cut of a node consists of the full-cut boundary triple, the
    "split-at-root" middle terms, and the genuine children-crown re-cuts. -/
theorem dcLHSP_node (τ : RoseTree (α ⊕ β) → β) (a : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    dcLHSP τ (RoseTree.node a cs) =
      ((({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β)), (0 : FP (α ⊕ β))) ::ₘ
        (Cl τ cs).map (fun p => (p.1, ({RoseTree.node a p.2} : FP (α ⊕ β)), (0 : FP (α ⊕ β)))))
      + (Cl τ cs).bind (fun p =>
          (forestCutsP τ p.1).map
            (fun c12 => (c12.1, c12.2, ({RoseTree.node a p.2} : FP (α ⊕ β))))) := by
  rw [dcLHSP_eq_bind, treeCutsP_node, Multiset.cons_bind, Multiset.bind_map]
  have h1 : hL τ (({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β))) =
      (({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β)), (0 : FP (α ⊕ β))) ::ₘ
        (Cl τ cs).map (fun p => (p.1, ({RoseTree.node a p.2} : FP (α ⊕ β)), (0 : FP (α ⊕ β)))) := by
    show (forestCutsP τ {RoseTree.node a cs}).map
        (fun A12 => (A12.1, A12.2, (0 : FP (α ⊕ β)))) = _
    rw [forestCutsP_singleton, treeCutsP_node, Multiset.map_cons, Multiset.map_map]
    rfl
  rw [h1]
  rfl

/-- The right-hand double cut of a node consists of the full-cut boundary triple and, for
    each children-cut, the re-cuts of the trunk tree `node a remainder`. -/
theorem dcRHSP_node (τ : RoseTree (α ⊕ β) → β) (a : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    dcRHSP τ (RoseTree.node a cs) =
      {(({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β)), (0 : FP (α ⊕ β)))}
      + (Cl τ cs).bind (fun p =>
          (treeCutsP τ (RoseTree.node a p.2)).map (fun B12 => (p.1, B12.1, B12.2))) := by
  rw [dcRHSP_eq_bind, treeCutsP_node, Multiset.cons_bind, Multiset.bind_map]
  have h1 : hR τ (({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β))) =
      {(({RoseTree.node a cs} : FP (α ⊕ β)), (0 : FP (α ⊕ β)), (0 : FP (α ⊕ β)))} := by
    show (forestCutsP τ (0 : FP (α ⊕ β))).map
        (fun B12 => (({RoseTree.node a cs} : FP (α ⊕ β)), B12.1, B12.2)) = _
    rw [forestCutsP_zero, Multiset.map_singleton]
  rw [h1]
  congr 1
  apply Multiset.bind_congr; intro p _
  show (forestCutsP τ {RoseTree.node a p.2}).map (fun B12 => (p.1, B12.1, B12.2)) = _
  rw [forestCutsP_singleton]

/-! ### Children-list convolution `clconv` and `Cl` as a monoid hom

`Cl τ = cutListSummandsG (extractC τ)` is a monoid hom from `(List, ++)` to
`(Multiset (Forest × List), clconv)`. `clconv` is the cons-combiner of
`cutListSummandsG` (forest add, list append) — a (non-commutative) monoid
with unit `{(0, [])}`. -/

/-- The children-list cut combiner: add crown forests, append remainders. -/
def clconv (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :=
  (S ×ˢ T).map (fun pr => (pr.1.1 + pr.2.1, pr.1.2 ++ pr.2.2))

theorem clconv_bind (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    clconv S T = S.bind (fun s => T.map (fun t => (s.1 + t.1, s.2 ++ t.2))) := by
  unfold clconv
  show ((S.bind fun a => T.map (Prod.mk a)).map _) = _
  rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro s _
  rw [Multiset.map_map]; rfl

theorem clconv_unit_left (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    clconv {((0 : FP (α ⊕ β)), ([] : List (RoseTree (α ⊕ β))))} S = S := by
  rw [clconv_bind, Multiset.singleton_bind]
  conv_rhs => rw [← Multiset.map_id' S]
  apply Multiset.map_congr rfl; rintro ⟨F, l⟩ _
  simp only [zero_add, List.nil_append]

theorem clconv_unit_right (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    clconv S {((0 : FP (α ⊕ β)), ([] : List (RoseTree (α ⊕ β))))} = S := by
  rw [clconv_bind]
  rw [show (fun s : FP (α ⊕ β) × List (RoseTree (α ⊕ β)) =>
        ({((0 : FP (α ⊕ β)), ([] : List (RoseTree (α ⊕ β))))} : Multiset _).map
          (fun t => (s.1 + t.1, s.2 ++ t.2))) = (fun s => {s}) from by
    funext s; rw [Multiset.map_singleton]; simp only [add_zero, List.append_nil]]
  rw [Multiset.bind_singleton, Multiset.map_id']

theorem clconv_assoc (S T U : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    clconv (clconv S T) U = clconv S (clconv T U) := by
  conv_lhs => rw [clconv_bind, clconv_bind, Multiset.bind_assoc]
  conv_rhs => rw [clconv_bind]
  apply Multiset.bind_congr; intro s _
  rw [Multiset.bind_map, clconv_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro t _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro u _
  simp only [Function.comp_apply, add_assoc, List.append_assoc]

theorem Cl_nil (τ : RoseTree (α ⊕ β) → β) :
    Cl τ ([] : List (RoseTree (α ⊕ β))) =
      {((0 : FP (α ⊕ β)), ([] : List (RoseTree (α ⊕ β))))} := cutListSummandsG_nil _

theorem Cl_cons (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) (ts : List (RoseTree (α ⊕ β))) :
    Cl τ (t :: ts) = clconv (augActionG (extractC τ) t) (Cl τ ts) := by
  rw [show Cl τ (t :: ts) = cutListSummandsG (extractC τ) (t :: ts) from rfl,
      cutListSummandsG_cons]
  rfl

theorem Cl_append (τ : RoseTree (α ⊕ β) → β) (l₁ l₂ : List (RoseTree (α ⊕ β))) :
    Cl τ (l₁ ++ l₂) = clconv (Cl τ l₁) (Cl τ l₂) := by
  induction l₁ with
  | nil => rw [List.nil_append, Cl_nil, clconv_unit_left]
  | cons t ts ih =>
    rw [List.cons_append, Cl_cons, ih, Cl_cons, clconv_assoc]

/-! ### The two double-cut maps and their `clconv`-multiplicativity (mod proj)

`dcl`/`dcr` are the children-list double-cut enumerators (re-cut crown via
`forestCutsP`, vs re-cut remainder via `Cl`). Projected through `proj3L`
(third component = remainder list → multiset of nonplanar trees), each is
multiplicative over `clconv`. -/

/-- Projection of a (crown, mid, remainder-list) triple to nonplanar. -/
def proj3L (q : FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk,
    Multiset.ofList (q.2.2.map UnorderedTree.mk))

theorem proj3L_add (a a' b b' : FP (α ⊕ β)) (l l' : List (RoseTree (α ⊕ β))) :
    proj3L (a + a', b + b', l ++ l') = proj3L (a, b, l) + proj3L (a', b', l') := by
  unfold proj3L
  rw [Multiset.map_add, Multiset.map_add, List.map_append]
  rfl

/-- LHS children-list double cut: re-cut crown `p.1`, keep remainder `p.2`. -/
def dcl (τ : RoseTree (α ⊕ β) → β) (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :=
  S.bind (fun p => (forestCutsP τ p.1).map (fun c12 => (c12.1, c12.2, p.2)))

/-- RHS children-list double cut: keep crown `p.1`, re-cut remainder `p.2`. -/
def dcr (τ : RoseTree (α ⊕ β) → β) (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    Multiset (FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :=
  S.bind (fun p => (Cl τ p.2).map (fun q => (p.1, q.1, q.2)))

theorem dclN_eq (τ : RoseTree (α ⊕ β) → β)
    (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcl τ S).map proj3L =
      S.bind (fun p => (forestCutsP τ p.1).map (fun c12 => proj3L (c12.1, c12.2, p.2))) := by
  unfold dcl; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

theorem dcrN_eq (τ : RoseTree (α ⊕ β) → β)
    (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcr τ S).map proj3L =
      S.bind (fun p => (Cl τ p.2).map (fun q => proj3L (p.1, q.1, q.2))) := by
  unfold dcr; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

/-- Per-element hom for `dcl`: re-cutting a combined crown with a combined
    remainder is the `Multiset.conv` of the parts. -/
private theorem hΦl (τ : RoseTree (α ⊕ β) → β) (s t : FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    (forestCutsP τ (s.1 + t.1)).map (fun c12 => proj3L (c12.1, c12.2, s.2 ++ t.2))
      = Multiset.conv ((forestCutsP τ s.1).map (fun c12 => proj3L (c12.1, c12.2, s.2)))
              ((forestCutsP τ t.1).map (fun c12 => proj3L (c12.1, c12.2, t.2))) := by
  rw [forestCutsP_add]
  exact Multiset.map_conv (f := fun c : Pair (α ⊕ β) ↦ proj3L (c.1, c.2, s.2))
    (f' := fun c : Pair (α ⊕ β) ↦ proj3L (c.1, c.2, t.2))
    (g := fun c : Pair (α ⊕ β) ↦ proj3L (c.1, c.2, s.2 ++ t.2)) _ _
    fun x y ↦ proj3L_add x.1 y.1 x.2 y.2 s.2 t.2

/-- Per-element hom for `dcr`: re-cutting the appended remainder with a
    combined crown is the `Multiset.conv` of the parts. -/
private theorem hΦr (τ : RoseTree (α ⊕ β) → β) (s t : FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    (Cl τ (s.2 ++ t.2)).map (fun q => proj3L (s.1 + t.1, q.1, q.2))
      = Multiset.conv ((Cl τ s.2).map (fun q => proj3L (s.1, q.1, q.2)))
              ((Cl τ t.2).map (fun q => proj3L (t.1, q.1, q.2))) := by
  rw [Cl_append]
  unfold clconv
  rw [Multiset.map_map]
  unfold Multiset.conv
  rw [← Multiset.prodMap_map_product, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨qs, qt⟩ _
  exact proj3L_add s.1 t.1 qs.1 qt.1 qs.2 qt.2

theorem dclN_clconv (τ : RoseTree (α ⊕ β) → β)
    (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcl τ (clconv S T)).map proj3L =
      Multiset.conv ((dcl τ S).map proj3L) ((dcl τ T).map proj3L) := by
  rw [dclN_eq, dclN_eq, dclN_eq]
  unfold clconv
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2)) (hΦl τ) S T

theorem dcrN_clconv (τ : RoseTree (α ⊕ β) → β)
    (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcr τ (clconv S T)).map proj3L =
      Multiset.conv ((dcr τ S).map proj3L) ((dcr τ T).map proj3L) := by
  rw [dcrN_eq, dcrN_eq, dcrN_eq]
  unfold clconv
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2)) (hΦr τ) S T

/-! ### The children-list coassociativity engine

`coassL`: the root-free children-list coassoc (LLEM3), proved by induction
on the list using `clconv`-multiplicativity, the per-child `coassA`, and
the tail IH. `coassA` (per-child) reduces to `coassL` of the child's
children with `TraceCoherent` reconciling the extract-whole marker. -/

/-- `τ` is trace-coherent on rose trees when `τ` of a cut trunk equals `τ` of the tree. The
    descent of `TraceCoherent` (UnorderedTree) along `UnorderedTree.mk`. -/
def TraceCoherentP (τ : RoseTree (α ⊕ β) → β) : Prop :=
  ∀ t : RoseTree (α ⊕ β), ∀ p ∈ cutSummandsCP τ t, τ p.2 = τ t

/-- Children-list cut of a singleton list is the per-child augmented action. -/
theorem Cl_singleton (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    Cl τ [t] = augActionG (extractC τ) t := by
  rw [show ([t] : List (RoseTree (α ⊕ β))) = t :: [] from rfl, Cl_cons, Cl_nil,
      clconv_unit_right]

/-- Projecting a triple whose remainder is a singleton `[node a' l]` equals
    nonplanar `node a'`-wrapping the projection with raw remainder `l`. -/
theorem proj3L_list_wrap (a' : α ⊕ β) (x y : FP (α ⊕ β)) (l : List (RoseTree (α ⊕ β))) :
    proj3L (x, y, [RoseTree.node a' l])
      = ((proj3L (x, y, l)).1, (proj3L (x, y, l)).2.1,
          ({UnorderedTree.node a' (proj3L (x, y, l)).2.2} : Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold proj3L
  simp only [List.map_cons, List.map_nil]
  rw [show (Multiset.ofList [UnorderedTree.mk (RoseTree.node a' l)])
        = ({UnorderedTree.mk (RoseTree.node a' l)} : Multiset (UnorderedTree (α ⊕ β))) from rfl,
      ← UnorderedTree.node_mk_tree_list]

/-- Splitting a `bind` whose body is a sum. -/
private theorem bind_add_split {γ : Type*} (S : Multiset γ)
    (A B : γ → Multiset (Triple (α ⊕ β))) :
    S.bind (fun p => A p + B p) = S.bind A + S.bind B := by
  induction S using Multiset.induction with
  | empty => simp
  | cons s S ih => rw [Multiset.cons_bind, Multiset.cons_bind, Multiset.cons_bind, ih]; abel

/-- Splitting a `bind` over `FP × FP × List`-triples whose body is a `cons`. -/
private theorem bind_cons_splitL {γ : Type*} (S : Multiset γ)
    (x : γ → FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β)))
    (h : γ → Multiset (FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    S.bind (fun p => x p ::ₘ h p) = S.map x + S.bind h := by
  induction S using Multiset.induction with
  | empty => simp
  | cons s S ih =>
    rw [Multiset.cons_bind, Multiset.map_cons, Multiset.cons_bind, ih]
    simp only [← Multiset.singleton_add]; abel

/-- The `[node a']`-wrapped `dcl` of the children cut, projected, equals the
    nonplanar `node a'`-wrap of the projected `dcl`. -/
theorem dcl_INH_wrap (τ : RoseTree (α ⊕ β) → β) (a' : α ⊕ β) (cs'' : List (RoseTree (α ⊕ β))) :
    (dcl τ
      ((Cl τ cs'').map
        (fun p => (p.1, ([RoseTree.node a' p.2] : List (RoseTree (α ⊕ β))))))).map proj3L
      = ((dcl τ (Cl τ cs'')).map proj3L).map
          (fun z => (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [dclN_eq, dclN_eq, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro c12 _
  exact proj3L_list_wrap a' c12.1 c12.2 p.2

/-- The non-extract-whole part of the trunk re-cut, projected, equals the
    nonplanar `node a'`-wrap of the projected `dcr`. -/
theorem dcr_nonEW_wrap (τ : RoseTree (α ⊕ β) → β) (a' : α ⊕ β) (cs'' : List (RoseTree (α ⊕ β))) :
    ((Cl τ cs'').bind (fun p => (Cl τ p.2).map
        (fun p'' => (p.1, p''.1, ([RoseTree.node a' p''.2] : List (RoseTree (α ⊕ β))))))).map proj3L
      = ((dcr τ (Cl τ cs'')).map proj3L).map
          (fun z => (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [dcrN_eq, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro p'' _
  exact proj3L_list_wrap a' p.1 p''.1 p''.2

/-- `dcl` distributes over a `cons` outer cut. -/
theorem dcl_cons (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) (l : List (RoseTree (α ⊕ β)))
    (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    dcl τ ((F, l) ::ₘ S)
      = (forestCutsP τ F).map (fun c12 => (c12.1, c12.2, l)) + dcl τ S := by
  unfold dcl; rw [Multiset.cons_bind]

/-- `dcr` distributes over a `cons` outer cut. -/
theorem dcr_cons (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) (l : List (RoseTree (α ⊕ β)))
    (S : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    dcr τ ((F, l) ::ₘ S)
      = (Cl τ l).map (fun q => (F, q.1, q.2)) + dcr τ S := by
  unfold dcr; rw [Multiset.cons_bind]

/-! **Children-list coassoc** (`coassL`) and **per-child coassoc**
    (`coassA`), proved by mutual structural recursion mirroring
    `cutListSummandsG`/`augActionG`. `coassL` is the engine of the per-tree
    node step; `coassA` is the coherence-using combinatorial core. -/
mutual
theorem coassL (τ : RoseTree (α ⊕ β) → β) (hτ : TraceCoherentP τ) :
    ∀ cs : List (RoseTree (α ⊕ β)),
      (dcl τ (Cl τ cs)).map proj3L = (dcr τ (Cl τ cs)).map proj3L
  | [] => by
    rw [Cl_nil]
    unfold dcl dcr
    rw [Multiset.singleton_bind, Multiset.singleton_bind, forestCutsP_zero, Cl_nil]
    simp only [Multiset.map_singleton]
  | c :: cs' => by
    rw [Cl_cons, dclN_clconv, dcrN_clconv, coassA τ hτ c, coassL τ hτ cs']
theorem coassA (τ : RoseTree (α ⊕ β) → β) (hτ : TraceCoherentP τ) :
    ∀ c : RoseTree (α ⊕ β),
      (dcl τ (augActionG (extractC τ) c)).map proj3L
        = (dcr τ (augActionG (extractC τ) c)).map proj3L
  | .node a' cs'' => by
    have hcoassL := coassL τ hτ cs''
    cases a' with
    | inr b' =>
      -- extractC = none: `Aa c = INH`, no extract-whole, no coherence needed.
      rw [show augActionG (extractC τ) (RoseTree.node (Sum.inr b') cs'')
            = (Cl τ cs'').map (fun p => (p.1, ([RoseTree.node (Sum.inr b') p.2]
                : List (RoseTree (α ⊕ β))))) from by
          rw [augActionG_eq_none _ _ (extractC_inr τ b' cs''), cutSummandsG_node,
              Multiset.map_map]; rfl]
      have hdcrINH : dcr τ ((Cl τ cs'').map
            (fun p => (p.1, ([RoseTree.node (Sum.inr b') p.2] : List (RoseTree (α ⊕ β))))))
          = (Cl τ cs'').bind (fun p => (Cl τ p.2).map
              (fun p'' => (p.1, p''.1, [RoseTree.node (Sum.inr b') p''.2]))) := by
        unfold dcr; rw [Multiset.bind_map]
        apply Multiset.bind_congr; intro p _
        rw [show Cl τ [RoseTree.node (Sum.inr b') p.2] = (Cl τ p.2).map
              (fun p'' => (p''.1, [RoseTree.node (Sum.inr b') p''.2])) from by
            rw [Cl_singleton, augActionG_eq_none _ _ (extractC_inr τ b' p.2),
                cutSummandsG_node, Multiset.map_map]; rfl,
          Multiset.map_map]
        rfl
      rw [dcl_INH_wrap, hdcrINH, dcr_nonEW_wrap, hcoassL]
    | inl a'' =>
      have hAa : augActionG (extractC τ) (RoseTree.node (Sum.inl a'') cs'')
          = (({RoseTree.node (Sum.inl a'') cs''} : FP (α ⊕ β)),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
              (Cl τ cs'').map (fun p => (p.1, [RoseTree.node (Sum.inl a'') p.2])) := by
        rw [augActionG_eq_some _ _ _ (extractC_inl τ a'' cs''), cutSummandsG_node,
            Multiset.map_map]; rfl
      have hCltl : Cl τ [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]
          = {((0 : FP (α ⊕ β)), [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))])} := by
        rw [Cl_singleton]
        show augActionG (extractC τ)
              (RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) [])
            = {((0 : FP (α ⊕ β)),
                [RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) []])}
        rw [augActionG_eq_none _ _ (extractC_inr τ _ []), cutSummandsG_node,
            cutListSummandsG_nil]; rfl
      have hdcrINH : dcr τ ((Cl τ cs'').map
            (fun p => (p.1, [RoseTree.node (Sum.inl a'') p.2])))
          = (Cl τ cs'').map (fun p => (p.1, ({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
                [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))
            + (Cl τ cs'').bind (fun p => (Cl τ p.2).map
                (fun p'' => (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
        have step1 : dcr τ ((Cl τ cs'').map
              (fun p => (p.1, [RoseTree.node (Sum.inl a'') p.2])))
            = (Cl τ cs'').bind (fun p =>
                (p.1, ({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
                  [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                (Cl τ p.2).map (fun p'' =>
                  (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
          unfold dcr; rw [Multiset.bind_map]
          apply Multiset.bind_congr; intro p _
          show (Cl τ [RoseTree.node (Sum.inl a'') p.2]).map
              (fun q => (p.1, q.1, q.2)) = _
          rw [show Cl τ [RoseTree.node (Sum.inl a'') p.2]
                = (({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
                    [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                  (Cl τ p.2).map (fun p'' =>
                    (p''.1, [RoseTree.node (Sum.inl a'') p''.2])) from by
              rw [Cl_singleton, augActionG_eq_some _ _ _ (extractC_inl τ a'' p.2),
                  cutSummandsG_node, Multiset.map_map]; rfl,
            Multiset.map_cons, Multiset.map_map]
          rfl
        rw [step1, bind_cons_splitL]
      -- Coherence: the trunk extract-whole markers collapse to `[tl]`.
      have hcoh : ((Cl τ cs'').map (fun p : FP (α ⊕ β) × List (RoseTree (α ⊕ β)) => (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))).map proj3L
          = ((Cl τ cs'').map (fun p : FP (α ⊕ β) × List (RoseTree (α ⊕ β)) => (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L := by
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl; intro p hp
        simp only [Function.comp_apply]
        rw [show τ (RoseTree.node (Sum.inl a'') p.2) = τ (RoseTree.node (Sum.inl a'') cs'') from
          hτ (RoseTree.node (Sum.inl a'') cs'') (p.1, RoseTree.node (Sum.inl a'') p.2)
            (by rw [cutSummandsCP_node]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩)]
      -- The extract-whole re-cut of `{c}` expands to the boundary plus interior.
      have hΦdcl : ((forestCutsP τ {RoseTree.node (Sum.inl a'') cs''}).map
            (fun c12 => (c12.1, c12.2,
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L
          = proj3L (({RoseTree.node (Sum.inl a'') cs''} : FP (α ⊕ β)), (0 : FP (α ⊕ β)),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
            ((Cl τ cs'').map (fun p : FP (α ⊕ β) × List (RoseTree (α ⊕ β)) => (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : FP (α ⊕ β)),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L := by
        rw [forestCutsP_singleton, treeCutsP_node, Multiset.map_cons, Multiset.map_map,
            Multiset.map_cons]
        rfl
      rw [hAa, dcl_cons, dcr_cons, hCltl, Multiset.map_singleton,
          Multiset.map_add, Multiset.map_add, dcl_INH_wrap, hdcrINH, Multiset.map_add,
          dcr_nonEW_wrap, hcoh, hcoassL, hΦdcl, Multiset.map_singleton]
      simp only [← Multiset.singleton_add]
      abel
end

/-! ### Per-tree coassoc `coassT` from `coassL` (node reduction + root wrap) -/

/-- Splitting a `bind` whose body is a `cons`. -/
private theorem bind_cons_split {γ : Type*}
    (S : Multiset γ) (x : γ → Triple (α ⊕ β)) (h : γ → Multiset (Triple (α ⊕ β))) :
    S.bind (fun p => x p ::ₘ h p) = S.map x + S.bind h := by
  induction S using Multiset.induction with
  | empty => simp
  | cons s S ih =>
    rw [Multiset.cons_bind, Multiset.map_cons, Multiset.cons_bind, ih]
    simp only [← Multiset.singleton_add]; abel

/-- Projecting a `node a`-wrapped triple equals nonplanar-wrapping the
    projected triple. -/
private theorem proj3_node_wrap (a : α ⊕ β)
    (q : FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    proj3 (q.1, q.2.1, ({RoseTree.node a q.2.2} : FP (α ⊕ β)))
      = ((proj3L q).1, (proj3L q).2.1,
          ({UnorderedTree.node a (proj3L q).2.2} : Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold proj3 proj3L
  simp only [Multiset.map_singleton]
  rw [UnorderedTree.node_mk_tree_list]

/-- The `node a`-wrap on planar triples, projected, equals the nonplanar
    `node a`-wrap on projected triples. -/
private theorem map_node_wrap_proj3 (a : α ⊕ β)
    (M : Multiset (FP (α ⊕ β) × FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (M.map (fun q => (q.1, q.2.1, ({RoseTree.node a q.2.2} : FP (α ⊕ β))))).map proj3
      = (M.map proj3L).map (fun z => (z.1, z.2.1,
          ({UnorderedTree.node a z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro q _
  exact proj3_node_wrap a q

theorem coassT (τ : RoseTree (α ⊕ β) → β) (hτ : TraceCoherentP τ) (t : RoseTree (α ⊕ β)) :
    (dcLHSP τ t).map proj3 = (dcRHSP τ t).map proj3 := by
  obtain ⟨a, cs⟩ := t
  -- Core: the two genuine remainder re-cuts agree (= `coassL` wrapped by `node a`).
  have hcore : ((Cl τ cs).bind (fun p => (forestCutsP τ p.1).map
        (fun c12 => (c12.1, c12.2, ({RoseTree.node a p.2} : FP (α ⊕ β)))))).map proj3
      = ((Cl τ cs).bind (fun p => (Cl τ p.2).map
        (fun q => (p.1, q.1, ({RoseTree.node a q.2} : FP (α ⊕ β)))))).map proj3 := by
    rw [show ((Cl τ cs).bind (fun p => (forestCutsP τ p.1).map
            (fun c12 => (c12.1, c12.2, ({RoseTree.node a p.2} : FP (α ⊕ β))))))
          = ((dcl τ (Cl τ cs)).map
              (fun q => (q.1, q.2.1, ({RoseTree.node a q.2.2} : FP (α ⊕ β))))) from by
        unfold dcl; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl,
      show ((Cl τ cs).bind (fun p => (Cl τ p.2).map
            (fun q => (p.1, q.1, ({RoseTree.node a q.2} : FP (α ⊕ β))))))
          = ((dcr τ (Cl τ cs)).map
              (fun q => (q.1, q.2.1, ({RoseTree.node a q.2.2} : FP (α ⊕ β))))) from by
        unfold dcr; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl]
    rw [map_node_wrap_proj3, map_node_wrap_proj3, coassL τ hτ cs]
  rw [dcLHSP_node, dcRHSP_node]
  rw [show (fun p : FP (α ⊕ β) × List (RoseTree (α ⊕ β)) =>
        (treeCutsP τ (RoseTree.node a p.2)).map (fun B12 => (p.1, B12.1, B12.2)))
        = (fun p => (p.1, ({RoseTree.node a p.2} : FP (α ⊕ β)), (0 : FP (α ⊕ β))) ::ₘ
            (Cl τ p.2).map (fun q => (p.1, q.1, ({RoseTree.node a q.2} : FP (α ⊕ β))))) from by
      funext p
      rw [treeCutsP_node, Multiset.map_cons, Multiset.map_map]; rfl]
  rw [bind_cons_split, Multiset.map_add, Multiset.map_add, Multiset.map_add,
      Multiset.map_cons, Multiset.map_singleton, hcore, ← Multiset.singleton_add]
  abel

end DoubleCut
