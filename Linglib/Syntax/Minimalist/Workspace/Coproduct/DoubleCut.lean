module

public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Tactic.Abel

/-!
# RoseTree double-cut coassociativity for Δ^c (combinatorial core of MCB 1.2.10)

The combinatorial heart of Δ^c coassociativity: both `(Δ^c ⊗ id) ∘ Δ^c` and
`(id ⊗ Δ^c) ∘ Δ^c` enumerate ordered pairs of nested admissible cuts of a
tree, and under trace coherence the two enumerations agree as UnorderedTree
multisets. This file proves that agreement at the **planar** level (where
`cutSummandsCP` recurses structurally); `Trace.lean`
descends it through `UnorderedTree.mk` to close the UnorderedTree `doubleCut_eq`.

## Main results

- `coassT` — per-tree coassoc `(dcLHSP τ t).map proj3 = (dcRHSP τ t).map proj3`.
- `coassL`/`coassA` — children-list / per-child coassoc (mutual, mirroring
  `cutListSummandsG`/`augActionG`); `coassA` is where `TraceCoherentP`
  reconciles the marker a deeper cut writes on a trunk.
- `dclN_clconv`/`dcrN_clconv` — the two second-cut maps are multiplicative
  over the children-list convolution `clconv` (the engine of the induction).
- `mconv` — multiset convolution monoid, with `mconv_prod_hom`.

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

/-! ### Generic multiset convolution over an additive monoid

`mconv s t = (s ×ˢ t).map (·+·)` — the convolution of two multisets over
an `AddCommMonoid`. This is the per-component combination of cut pairs
(forest crowns/trunks add) and, at the triple level, the combination of
double-cut layers. Proved a commutative monoid with unit `{0}`. -/

section Mconv
variable {M : Type*}

/-- Multiset convolution over an additive structure. -/
def mconv [Add M] (s t : Multiset M) : Multiset M :=
  (s ×ˢ t).map (fun p => p.1 + p.2)

variable [AddCommMonoid M]

theorem mconv_bind (s t : Multiset M) :
    mconv s t = s.bind (fun a => t.map (fun b => a + b)) := by
  unfold mconv
  show ((s.bind fun a => t.map (Prod.mk a)).map (fun p => p.1 + p.2)) = _
  rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro a _
  rw [Multiset.map_map]; rfl

theorem mconv_zero_left (t : Multiset M) : mconv {(0 : M)} t = t := by
  rw [mconv_bind, Multiset.singleton_bind]
  simp

theorem mconv_comm (s t : Multiset M) : mconv s t = mconv t s := by
  rw [mconv_bind, mconv_bind, Multiset.bind_map_comm]
  apply Multiset.bind_congr; intro b _
  apply Multiset.map_congr rfl; intro a _
  rw [add_comm]

theorem mconv_zero_right (s : Multiset M) : mconv s {(0 : M)} = s := by
  rw [mconv_comm, mconv_zero_left]

theorem mconv_assoc (s t u : Multiset M) :
    mconv (mconv s t) u = mconv s (mconv t u) := by
  conv_lhs => rw [mconv_bind, mconv_bind, Multiset.bind_assoc]
  conv_rhs => rw [mconv_bind]
  apply Multiset.bind_congr; intro a _
  rw [Multiset.bind_map, mconv_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro c _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro d _
  simp only [Function.comp_apply, add_assoc]

theorem mconv_left_comm (s t u : Multiset M) :
    mconv s (mconv t u) = mconv t (mconv s u) := by
  rw [← mconv_assoc, ← mconv_assoc, mconv_comm s t]

instance instLeftCommMconv : LeftCommutative (mconv (M := M)) :=
  ⟨mconv_left_comm⟩

theorem mconv_add_left (s t u : Multiset M) :
    mconv (s + t) u = mconv s u + mconv t u := by
  rw [mconv_bind, mconv_bind, mconv_bind, Multiset.add_bind]

theorem mconv_add_right (s t u : Multiset M) :
    mconv s (t + u) = mconv s t + mconv s u := by
  rw [mconv_comm s (t + u), mconv_add_left, mconv_comm t s, mconv_comm u s]

end Mconv

abbrev convFP : Multiset (Pair (α ⊕ β)) → Multiset (Pair (α ⊕ β)) →
    Multiset (Pair (α ⊕ β)) := mconv

theorem convFP_eq (s acc : Multiset (Pair (α ⊕ β))) :
    convFP s acc = (s ×ˢ acc).map (fun pq => (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2)) := by
  unfold convFP mconv
  apply Multiset.map_congr rfl; rintro ⟨x, y⟩ _; rfl

/-- RoseTree tree-cut enumerator (crown forest, trunk forest). -/
def treeCutsP (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    Multiset (Pair (α ⊕ β)) :=
  ({t}, 0) ::ₘ (cutSummandsCP τ t).map (fun p => (p.1, {p.2}))

/-- Forest-cut enumerator: convolution over the component trees. -/
def forestCutsP (τ : RoseTree (α ⊕ β) → β) (F : FP (α ⊕ β)) :
    Multiset (Pair (α ⊕ β)) :=
  (F.map (treeCutsP τ)).foldr convFP {(0, 0)}

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
    forestCutsP τ (t ::ₘ F) = convFP (treeCutsP τ t) (forestCutsP τ F) := by
  unfold forestCutsP
  rw [Multiset.map_cons, Multiset.foldr_cons]

theorem forestCutsP_singleton (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    forestCutsP τ {t} = treeCutsP τ t := by
  rw [show ({t} : FP (α ⊕ β)) = t ::ₘ 0 from rfl, forestCutsP_cons, forestCutsP_zero]
  exact mconv_zero_right _

theorem forestCutsP_add (τ : RoseTree (α ⊕ β) → β) (F G : FP (α ⊕ β)) :
    forestCutsP τ (F + G) = convFP (forestCutsP τ F) (forestCutsP τ G) := by
  induction F using Multiset.induction with
  | empty => rw [zero_add, forestCutsP_zero]; exact (mconv_zero_left _).symm
  | cons t F ih =>
    rw [Multiset.cons_add, forestCutsP_cons, forestCutsP_cons, ih]
    exact (mconv_assoc _ _ _).symm

/-! ### Multiplicativity machinery -/

abbrev Triple (α : Type*) := FP α × FP α × FP α

/-- `mconv` commutes with a map whose combination splits as `g (x+y) = f x + f' y`. -/
theorem mconv_map_hom2 {M N : Type*} [AddCommMonoid M] [Add N]
    (f f' g : M → N) (hg : ∀ x y, g (x + y) = f x + f' y) (X Y : Multiset M) :
    (mconv X Y).map g = mconv (X.map f) (Y.map f') := by
  unfold mconv
  rw [Multiset.map_map, ← Multiset.prodMap_map_product, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨x, y⟩ _
  exact hg x y

/-- A monoid hom `h : (M,+) → (Multiset T, mconv)` turns `bind` over a
    convolution into a convolution of binds. -/
theorem mconv_hom_bind {M T : Type*} [AddCommMonoid M] [AddCommMonoid T]
    (h : M → Multiset T) (hh : ∀ p q, h (p + q) = mconv (h p) (h q))
    (A B : Multiset M) :
    (mconv A B).bind h = mconv (A.bind h) (B.bind h) := by
  have hL : (mconv A B).bind h =
      A.bind (fun a => B.bind (fun b => mconv (h a) (h b))) := by
    rw [mconv_bind, Multiset.bind_assoc]
    apply Multiset.bind_congr; intro a _
    rw [Multiset.bind_map]
    apply Multiset.bind_congr; intro b _
    exact hh a b
  have hR : mconv (A.bind h) (B.bind h) =
      A.bind (fun a => B.bind (fun b => mconv (h a) (h b))) := by
    rw [mconv_bind, Multiset.bind_assoc]
    apply Multiset.bind_congr; intro a _
    rw [show (fun x => (B.bind h).map (fun y => x + y)) =
          (fun x => B.bind (fun b => (h b).map (fun y => x + y))) from by
            funext x; rw [Multiset.map_bind]]
    rw [Multiset.bind_bind]
    apply Multiset.bind_congr; intro b _
    rw [← mconv_bind]
  rw [hL, hR]

/-! ### proj3 is additive -/

theorem proj3_add (p q : Triple (α ⊕ β)) : proj3 (p + q) = proj3 p + proj3 q := by
  obtain ⟨X, Y, Z⟩ := p; obtain ⟨X', Y', Z'⟩ := q
  simp only [proj3, Prod.mk_add_mk, Multiset.map_add]

theorem proj3_mconv (X Y : Multiset (Triple (α ⊕ β))) :
    (mconv X Y).map proj3 = mconv (X.map proj3) (Y.map proj3) :=
  mconv_map_hom2 proj3 proj3 proj3 proj3_add X Y

/-! ### The two second-cut maps are monoid homs -/

/-- The left-hand second cut re-cuts the crown `p.1`, carrying the trunk `p.2`. -/
def hL (τ : RoseTree (α ⊕ β) → β) (p : Pair (α ⊕ β)) : Multiset (Triple (α ⊕ β)) :=
  (forestCutsP τ p.1).map (fun A12 => (A12.1, A12.2, p.2))

/-- The right-hand second cut re-cuts the trunk `p.2`, carrying the crown `p.1`. -/
def hR (τ : RoseTree (α ⊕ β) → β) (p : Pair (α ⊕ β)) : Multiset (Triple (α ⊕ β)) :=
  (forestCutsP τ p.2).map (fun B12 => (p.1, B12.1, B12.2))

theorem hL_hom (τ : RoseTree (α ⊕ β) → β) (p q : Pair (α ⊕ β)) :
    hL τ (p + q) = mconv (hL τ p) (hL τ q) := by
  show (forestCutsP τ (p.1 + q.1)).map (fun A12 => (A12.1, A12.2, p.2 + q.2)) = _
  rw [forestCutsP_add]
  refine mconv_map_hom2 (fun X : Pair (α ⊕ β) => (X.1, X.2, p.2))
    (fun Y : Pair (α ⊕ β) => (Y.1, Y.2, q.2))
    (fun A12 : Pair (α ⊕ β) => (A12.1, A12.2, p.2 + q.2)) ?_ _ _
  intro x y; rfl

theorem hR_hom (τ : RoseTree (α ⊕ β) → β) (p q : Pair (α ⊕ β)) :
    hR τ (p + q) = mconv (hR τ p) (hR τ q) := by
  show (forestCutsP τ (p.2 + q.2)).map (fun B12 => (p.1 + q.1, B12.1, B12.2)) = _
  rw [forestCutsP_add]
  refine mconv_map_hom2 (fun X : Pair (α ⊕ β) => (p.1, X.1, X.2))
    (fun Y : Pair (α ⊕ β) => (q.1, Y.1, Y.2))
    (fun B12 : Pair (α ⊕ β) => (p.1 + q.1, B12.1, B12.2)) ?_ _ _
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
    dcForestLHSP τ (t ::ₘ F) = mconv (dcLHSP τ t) (dcForestLHSP τ F) := by
  rw [dcForestLHSP_eq_bind, forestCutsP_cons, mconv_hom_bind (hL τ) (hL_hom τ),
      ← dcLHSP_eq_bind, ← dcForestLHSP_eq_bind]

theorem dcForestRHSP_cons (τ : RoseTree (α ⊕ β) → β)
    (t : RoseTree (α ⊕ β)) (F : FP (α ⊕ β)) :
    dcForestRHSP τ (t ::ₘ F) = mconv (dcRHSP τ t) (dcForestRHSP τ F) := by
  rw [dcForestRHSP_eq_bind, forestCutsP_cons, mconv_hom_bind (hR τ) (hR_hom τ),
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
    rw [dcForestLHSP_cons, dcForestRHSP_cons, proj3_mconv, proj3_mconv,
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

/-! ### Generic convolution-multiplicativity over a cartesian-product cut

`mconv_prod_hom`: when the per-element map `ΦN` is a convolution hom for a
combiner `comb`, binding `ΦN` over a `comb`-convolution of `S` and `T`
factors as the `mconv` of the per-side binds. This is the engine of the
children-list cons step. -/

theorem mconv_bind_distrib {M A B : Type*} [AddCommMonoid M]
    (f : A → Multiset M) (g : B → Multiset M) (S : Multiset A) (T : Multiset B) :
    mconv (S.bind f) (T.bind g) = S.bind (fun a => T.bind (fun b => mconv (f a) (g b))) := by
  rw [mconv_bind, Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a _
  rw [show (fun x => (T.bind g).map (fun y => x + y)) =
        (fun x => T.bind (fun b => (g b).map (fun y => x + y))) from by
          funext x; rw [Multiset.map_bind]]
  rw [Multiset.bind_bind]
  apply Multiset.bind_congr; intro b _
  rw [← mconv_bind]

theorem mconv_prod_hom {M A : Type*} [AddCommMonoid M]
    (ΦN : A → Multiset M) (comb : A → A → A)
    (hΦ : ∀ s t, ΦN (comb s t) = mconv (ΦN s) (ΦN t)) (S T : Multiset A) :
    ((S ×ˢ T).map (fun pr => comb pr.1 pr.2)).bind ΦN
      = mconv (S.bind ΦN) (T.bind ΦN) := by
  rw [mconv_bind_distrib, Multiset.bind_map]
  show ((S.bind fun a => T.map (Prod.mk a)).bind fun pr => ΦN (comb pr.1 pr.2)) = _
  rw [Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a _
  rw [Multiset.bind_map]
  apply Multiset.bind_congr; intro b _
  exact hΦ a b

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
    remainder is the `mconv` of the parts. -/
private theorem hΦl (τ : RoseTree (α ⊕ β) → β) (s t : FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    (forestCutsP τ (s.1 + t.1)).map (fun c12 => proj3L (c12.1, c12.2, s.2 ++ t.2))
      = mconv ((forestCutsP τ s.1).map (fun c12 => proj3L (c12.1, c12.2, s.2)))
              ((forestCutsP τ t.1).map (fun c12 => proj3L (c12.1, c12.2, t.2))) := by
  rw [forestCutsP_add]
  exact mconv_map_hom2 (fun c : Pair (α ⊕ β) => proj3L (c.1, c.2, s.2))
    (fun c : Pair (α ⊕ β) => proj3L (c.1, c.2, t.2))
    (fun c : Pair (α ⊕ β) => proj3L (c.1, c.2, s.2 ++ t.2))
    (fun x y => proj3L_add x.1 y.1 x.2 y.2 s.2 t.2)
    (forestCutsP τ s.1) (forestCutsP τ t.1)

/-- Per-element hom for `dcr`: re-cutting the appended remainder with a
    combined crown is the `mconv` of the parts. -/
private theorem hΦr (τ : RoseTree (α ⊕ β) → β) (s t : FP (α ⊕ β) × List (RoseTree (α ⊕ β))) :
    (Cl τ (s.2 ++ t.2)).map (fun q => proj3L (s.1 + t.1, q.1, q.2))
      = mconv ((Cl τ s.2).map (fun q => proj3L (s.1, q.1, q.2)))
              ((Cl τ t.2).map (fun q => proj3L (t.1, q.1, q.2))) := by
  rw [Cl_append]
  unfold clconv
  rw [Multiset.map_map]
  unfold mconv
  rw [← Multiset.prodMap_map_product, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨qs, qt⟩ _
  exact proj3L_add s.1 t.1 qs.1 qt.1 qs.2 qt.2

theorem dclN_clconv (τ : RoseTree (α ⊕ β) → β)
    (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcl τ (clconv S T)).map proj3L =
      mconv ((dcl τ S).map proj3L) ((dcl τ T).map proj3L) := by
  rw [dclN_eq, dclN_eq, dclN_eq]
  unfold clconv
  exact mconv_prod_hom
    (fun p => (forestCutsP τ p.1).map (fun c12 => proj3L (c12.1, c12.2, p.2)))
    (fun a b => (a.1 + b.1, a.2 ++ b.2)) (fun s t => hΦl τ s t) S T

theorem dcrN_clconv (τ : RoseTree (α ⊕ β) → β)
    (S T : Multiset (FP (α ⊕ β) × List (RoseTree (α ⊕ β)))) :
    (dcr τ (clconv S T)).map proj3L =
      mconv ((dcr τ S).map proj3L) ((dcr τ T).map proj3L) := by
  rw [dcrN_eq, dcrN_eq, dcrN_eq]
  unfold clconv
  exact mconv_prod_hom
    (fun p => (Cl τ p.2).map (fun q => proj3L (p.1, q.1, q.2)))
    (fun a b => (a.1 + b.1, a.2 ++ b.2)) (fun s t => hΦr τ s t) S T

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
