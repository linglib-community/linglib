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
# Double cuts

Both composites `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` enumerate the pairs of nested admissible
cuts of a tree, the second cut taken in the crown (`DoubleCut.dcLHS`) or in the trunk
(`DoubleCut.dcRHS`) of the first. For a coherent trace encoder [the two enumerations agree up to the
order of children](##DoubleCut.coassT). This file proves the agreement on rose trees, where the cut
enumeration recurses structurally, and `Trace.lean` descends it to `UnorderedTree`, where it is the
coassociativity of the coproduct `Δ^c` of Marcolli, Chomsky and Berwick (their Lemma 1.2.10, p. 37).
Trace coherence enters at [one child](##DoubleCut.coassA), where it reconciles the marker a deeper
cut writes on a trunk.

## References

* [marcolli-chomsky-berwick-2025]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree ConnesKreimer

namespace DoubleCut

/-! ### Double cuts over a cut enumeration -/

section Enumeration

variable {γ δ : Type*}

/-- The nested cuts of `t` whose second cut is in the crown of the first. -/
def dcLHS (cuts : γ → Multiset (Multiset γ × γ)) (t : γ) :
    Multiset (Multiset γ × Multiset γ × Multiset γ) :=
  (treeCutsG cuts t).bind fun p ↦ (forestCutsG cuts p.1).map fun q ↦ (q.1, q.2, p.2)

/-- The nested cuts of `t` whose second cut is in the trunk of the first. -/
def dcRHS (cuts : γ → Multiset (Multiset γ × γ)) (t : γ) :
    Multiset (Multiset γ × Multiset γ × Multiset γ) :=
  (treeCutsG cuts t).bind fun p ↦ (forestCutsG cuts p.2).map fun q ↦ (p.1, q.1, q.2)

variable {cuts : γ → Multiset (Multiset γ × γ)} {cuts' : δ → Multiset (Multiset δ × δ)} {f : γ → δ}

/-- A map carrying one enumeration to another carries the double cuts through the crown along. -/
theorem dcLHS_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f)) (t : γ) :
    dcLHS cuts' (f t) = (dcLHS cuts t).map fun q ↦ (q.1.map f, q.2.1.map f, q.2.2.map f) := by
  rw [dcLHS, treeCutsG_map h, Multiset.bind_map, dcLHS, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ ↦ ?_
  rw [Prod.map_fst, forestCutsG_map h, Multiset.map_map, Multiset.map_map]
  rfl

/-- A map carrying one enumeration to another carries the double cuts through the trunk along. -/
theorem dcRHS_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f)) (t : γ) :
    dcRHS cuts' (f t) = (dcRHS cuts t).map fun q ↦ (q.1.map f, q.2.1.map f, q.2.2.map f) := by
  rw [dcRHS, treeCutsG_map h, Multiset.bind_map, dcRHS, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ ↦ ?_
  rw [Prod.map_snd, forestCutsG_map h, Multiset.map_map, Multiset.map_map]
  rfl

end Enumeration

/-! ### Double cuts at the trace policy -/

variable {α β : Type*} (τ : RoseTree (α ⊕ β) → β)

/-- Forests of rose trees. -/
local notation "𝓕" => Multiset (RoseTree (α ⊕ β))

/-- Lists of children. -/
local notation "𝓛" => List (RoseTree (α ⊕ β))

/-- The cuts of a list of children at the trace policy, which keep the trace leaves of a cut. -/
local notation "Cl" => cutListSummandsG (extractC τ)

/-- The cuts of a tree with the trunk as a forest, at the trace policy. -/
local notation "𝒯" => treeCutsG (cutSummandsG (extractC τ))

/-- The cuts of a forest, at the trace policy. -/
local notation "ℱ" => forestCutsG (cutSummandsG (extractC τ))

/-- Projection of a triple of forests to unordered trees. -/
def proj3 (q : 𝓕 × 𝓕 × 𝓕) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk, q.2.2.map UnorderedTree.mk)

/-- The cuts of a node are the full cut and the cuts of its children under `node a`. -/
private theorem treeCuts_node (a : α ⊕ β) (cs : 𝓛) :
    𝒯 (RoseTree.node a cs) =
      (({RoseTree.node a cs} : 𝓕), (0 : 𝓕)) ::ₘ
        (Cl cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [treeCutsG, cutSummandsG_node, Multiset.map_map]
  rfl

/-- The double cuts of a node through the crown: the full cut, its re-cuts, and the re-cuts of the
    crowns of the cuts of its children. -/
private theorem dcLHS_node (a : α ⊕ β) (cs : 𝓛) :
    dcLHS (cutSummandsG (extractC τ)) (RoseTree.node a cs) =
      ((({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕)) ::ₘ
        (Cl cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), (0 : 𝓕)))
      + (Cl cs).bind fun p ↦ (ℱ p.1).map fun q ↦ (q.1, q.2, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [dcLHS, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCutsG_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- The double cuts of a node through the trunk: the full cut, and for each cut of its children
    the re-cuts of the trunk. -/
private theorem dcRHS_node (a : α ⊕ β) (cs : 𝓛) :
    dcRHS (cutSummandsG (extractC τ)) (RoseTree.node a cs) =
      {(({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕))}
      + (Cl cs).bind fun p ↦ (𝒯 (RoseTree.node a p.2)).map fun q ↦ (p.1, q.1, q.2) := by
  rw [dcRHS, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCutsG_zero, forestCutsG_singleton, Multiset.map_singleton]

/-! ### Double cuts of a list of children

`dcl` and `dcr` re-cut the crown and the remainder of a cut of a list of children. Projected through
`proj3L`, each is multiplicative over the combination of cuts in `cutListSummandsG_cons`. -/

/-- Projection of a (crown, mid, remainder-list) triple to nonplanar. -/
def proj3L (q : 𝓕 × 𝓕 × 𝓛) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk,
    Multiset.ofList (q.2.2.map UnorderedTree.mk))

private theorem proj3L_add (a a' b b' : 𝓕) (l l' : 𝓛) :
    proj3L (a + a', b + b', l ++ l') = proj3L (a, b, l) + proj3L (a', b', l') := by
  unfold proj3L
  rw [Multiset.map_add, Multiset.map_add, List.map_append]
  rfl

/-- LHS children-list double cut: re-cut crown `p.1`, keep remainder `p.2`. -/
def dcl (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ (c12.1, c12.2, p.2)))

/-- RHS children-list double cut: keep crown `p.1`, re-cut remainder `p.2`. -/
def dcr (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (Cl p.2).map (fun q ↦ (p.1, q.1, q.2)))

private theorem map_proj3L_dcl (S : Multiset (𝓕 × 𝓛)) :
    (dcl τ S).map proj3L =
      S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ proj3L (c12.1, c12.2, p.2))) := by
  unfold dcl; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

private theorem map_proj3L_dcr (S : Multiset (𝓕 × 𝓛)) :
    (dcr τ S).map proj3L =
      S.bind (fun p ↦ (Cl p.2).map (fun q ↦ proj3L (p.1, q.1, q.2))) := by
  unfold dcr; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

/-- Re-cutting a combined crown with a combined remainder is the convolution of the parts. -/
private theorem map_proj3L_crown_add (s t : 𝓕 × 𝓛) :
    (ℱ (s.1 + t.1)).map (fun c12 ↦ proj3L (c12.1, c12.2, s.2 ++ t.2))
      = Multiset.conv ((ℱ s.1).map (fun c12 ↦ proj3L (c12.1, c12.2, s.2)))
              ((ℱ t.1).map (fun c12 ↦ proj3L (c12.1, c12.2, t.2))) := by
  rw [forestCutsG_add]
  exact Multiset.map_conv (f := fun c : 𝓕 × 𝓕 ↦ proj3L (c.1, c.2, s.2))
    (f' := fun c : 𝓕 × 𝓕 ↦ proj3L (c.1, c.2, t.2))
    (g := fun c : 𝓕 × 𝓕 ↦ proj3L (c.1, c.2, s.2 ++ t.2)) _ _
    fun x y ↦ proj3L_add x.1 y.1 x.2 y.2 s.2 t.2

/-- Re-cutting an appended remainder with a combined crown is the convolution of the parts. -/
private theorem map_proj3L_remainder_add (s t : 𝓕 × 𝓛) :
    (Cl (s.2 ++ t.2)).map (fun q ↦ proj3L (s.1 + t.1, q.1, q.2))
      = Multiset.conv ((Cl s.2).map (fun q ↦ proj3L (s.1, q.1, q.2)))
              ((Cl t.2).map (fun q ↦ proj3L (t.1, q.1, q.2))) := by
  rw [cutListSummandsG_append, Multiset.map_map]
  unfold Multiset.conv
  rw [← Multiset.prodMap_map_product, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨qs, qt⟩ _
  exact proj3L_add s.1 t.1 qs.1 qt.1 qs.2 qt.2

private theorem dcl_conv (S T : Multiset (𝓕 × 𝓛)) :
    (dcl τ ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map proj3L =
      Multiset.conv ((dcl τ S).map proj3L) ((dcl τ T).map proj3L) := by
  rw [map_proj3L_dcl, map_proj3L_dcl, map_proj3L_dcl]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_proj3L_crown_add τ) S T

private theorem dcr_conv (S T : Multiset (𝓕 × 𝓛)) :
    (dcr τ ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map proj3L =
      Multiset.conv ((dcr τ S).map proj3L) ((dcr τ T).map proj3L) := by
  rw [map_proj3L_dcr, map_proj3L_dcr, map_proj3L_dcr]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_proj3L_remainder_add τ) S T

/-! ### Coassociativity on a list of children

`coassL` is proved by induction on the list, from the multiplicativity above and `coassA` at each
child. `coassA` reduces to `coassL` at the child's children, with `TraceCoherentP` reconciling the
marker of a child cut whole. -/

/-- `τ` is trace-coherent on rose trees when `τ` of a cut trunk equals `τ` of the tree. The
    descent of `TraceCoherent` (UnorderedTree) along `UnorderedTree.mk`. -/
def TraceCoherentP : Prop :=
  ∀ t : RoseTree (α ⊕ β), ∀ p ∈ cutSummandsG (extractC τ) t, τ p.2 = τ t

/-- Projecting a triple whose remainder is a singleton `[node a' l]` equals
    nonplanar `node a'`-wrapping the projection with raw remainder `l`. -/
private theorem proj3L_list_wrap (a' : α ⊕ β) (x y : 𝓕) (l : 𝓛) :
    proj3L (x, y, [RoseTree.node a' l])
      = ((proj3L (x, y, l)).1, (proj3L (x, y, l)).2.1,
          ({UnorderedTree.node a' (proj3L (x, y, l)).2.2} : Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold proj3L
  simp only [List.map_cons, List.map_nil]
  rw [show (Multiset.ofList [UnorderedTree.mk (RoseTree.node a' l)])
        = ({UnorderedTree.mk (RoseTree.node a' l)} : Multiset (UnorderedTree (α ⊕ β))) from rfl,
      ← UnorderedTree.node_mk_tree_list]

/-- The `[node a']`-wrapped `dcl` of the children cut, projected, equals the
    nonplanar `node a'`-wrap of the projected `dcl`. -/
private theorem dcl_node (a' : α ⊕ β) (cs'' : 𝓛) :
    (dcl τ
      ((Cl cs'').map
        (fun p ↦ (p.1, ([RoseTree.node a' p.2] : 𝓛))))).map proj3L
      = ((dcl τ (Cl cs'')).map proj3L).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [map_proj3L_dcl, map_proj3L_dcl, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro c12 _
  exact proj3L_list_wrap a' c12.1 c12.2 p.2

/-- Re-cutting the trunks of the cuts inside a child, projected, equals the
    nonplanar `node a'`-wrap of the projected `dcr`. -/
private theorem dcr_node (a' : α ⊕ β) (cs'' : 𝓛) :
    ((Cl cs'').bind (fun p ↦ (Cl p.2).map
        (fun p'' ↦ (p.1, p''.1, ([RoseTree.node a' p''.2] : 𝓛))))).map proj3L
      = ((dcr τ (Cl cs'')).map proj3L).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [map_proj3L_dcr, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro p'' _
  exact proj3L_list_wrap a' p.1 p''.1 p''.2

/-- `dcl` distributes over a `cons` outer cut. -/
private theorem dcl_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    dcl τ ((F, l) ::ₘ S)
      = (ℱ F).map (fun c12 ↦ (c12.1, c12.2, l)) + dcl τ S := by
  unfold dcl; rw [Multiset.cons_bind]

/-- `dcr` distributes over a `cons` outer cut. -/
private theorem dcr_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    dcr τ ((F, l) ::ₘ S)
      = (Cl l).map (fun q ↦ (F, q.1, q.2)) + dcr τ S := by
  unfold dcr; rw [Multiset.cons_bind]

/-! **Children-list coassoc** (`coassL`) and **per-child coassoc**
    (`coassA`), proved by mutual structural recursion mirroring
    `cutListSummandsG`/`augActionG`. `coassL` is the engine of the per-tree
    node step; `coassA` is the coherence-using combinatorial core. -/
mutual
theorem coassL (hτ : TraceCoherentP τ) :
    ∀ cs : 𝓛,
      (dcl τ (Cl cs)).map proj3L = (dcr τ (Cl cs)).map proj3L
  | [] => by
    rw [cutListSummandsG_nil]
    unfold dcl dcr
    rw [Multiset.singleton_bind, Multiset.singleton_bind, forestCutsG_zero, cutListSummandsG_nil]
    simp only [Multiset.map_singleton]
  | c :: cs' => by
    rw [cutListSummandsG_cons, dcl_conv, dcr_conv, coassA hτ c, coassL hτ cs']
theorem coassA (hτ : TraceCoherentP τ) :
    ∀ c : RoseTree (α ⊕ β),
      (dcl τ (augActionG (extractC τ) c)).map proj3L
        = (dcr τ (augActionG (extractC τ) c)).map proj3L
  | .node a' cs'' => by
    have hcoassL := coassL hτ cs''
    cases a' with
    | inr b' =>
      -- A trace is never cut whole, so coherence is not needed.
      rw [show augActionG (extractC τ) (RoseTree.node (Sum.inr b') cs'')
            = (Cl cs'').map (fun p ↦ (p.1, ([RoseTree.node (Sum.inr b') p.2]
                : 𝓛))) from by
          rw [augActionG_eq_none _ _ (extractC_inr τ b' cs''), cutSummandsG_node,
              Multiset.map_map]; rfl]
      have hdcr : dcr τ ((Cl cs'').map
            (fun p ↦ (p.1, ([RoseTree.node (Sum.inr b') p.2] : 𝓛))))
          = (Cl cs'').bind (fun p ↦ (Cl p.2).map
              (fun p'' ↦ (p.1, p''.1, [RoseTree.node (Sum.inr b') p''.2]))) := by
        unfold dcr; rw [Multiset.bind_map]
        apply Multiset.bind_congr; intro p _
        rw [show Cl [RoseTree.node (Sum.inr b') p.2] = (Cl p.2).map
              (fun p'' ↦ (p''.1, [RoseTree.node (Sum.inr b') p''.2])) from by
            rw [cutListSummandsG_singleton, augActionG_eq_none _ _ (extractC_inr τ b' p.2),
                cutSummandsG_node, Multiset.map_map]; rfl,
          Multiset.map_map]
        rfl
      rw [dcl_node, hdcr, dcr_node, hcoassL]
    | inl a'' =>
      have hAa : augActionG (extractC τ) (RoseTree.node (Sum.inl a'') cs'')
          = (({RoseTree.node (Sum.inl a'') cs''} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
              (Cl cs'').map (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])) := by
        rw [augActionG_eq_some _ _ _ (extractC_inl τ a'' cs''), cutSummandsG_node,
            Multiset.map_map]; rfl
      have hCltl : Cl [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]
          = {((0 : 𝓕), [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))])} := by
        rw [cutListSummandsG_singleton]
        show augActionG (extractC τ)
              (RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) [])
            = {((0 : 𝓕),
                [RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) []])}
        rw [augActionG_eq_none _ _ (extractC_inr τ _ []), cutSummandsG_node,
            cutListSummandsG_nil]; rfl
      have hdcr : dcr τ ((Cl cs'').map
            (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])))
          = (Cl cs'').map (fun p ↦ (p.1, ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))
            + (Cl cs'').bind (fun p ↦ (Cl p.2).map
                (fun p'' ↦ (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
        have step1 : dcr τ ((Cl cs'').map
              (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])))
            = (Cl cs'').bind (fun p ↦
                (p.1, ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                  [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                (Cl p.2).map (fun p'' ↦
                  (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
          unfold dcr; rw [Multiset.bind_map]
          apply Multiset.bind_congr; intro p _
          show (Cl [RoseTree.node (Sum.inl a'') p.2]).map
              (fun q ↦ (p.1, q.1, q.2)) = _
          rw [show Cl [RoseTree.node (Sum.inl a'') p.2]
                = (({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                    [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                  (Cl p.2).map (fun p'' ↦
                    (p''.1, [RoseTree.node (Sum.inl a'') p''.2])) from by
              rw [cutListSummandsG_singleton, augActionG_eq_some _ _ _ (extractC_inl τ a'' p.2),
                  cutSummandsG_node, Multiset.map_map]; rfl,
            Multiset.map_cons, Multiset.map_map]
          rfl
        rw [step1, Multiset.bind_cons]
      -- Coherence: every trunk of the child writes the marker of the child.
      have hcoh : ((Cl cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))).map proj3L
          = ((Cl cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L := by
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl; intro p hp
        simp only [Function.comp_apply]
        rw [show τ (RoseTree.node (Sum.inl a'') p.2) = τ (RoseTree.node (Sum.inl a'') cs'') from
          hτ (RoseTree.node (Sum.inl a'') cs'') (p.1, RoseTree.node (Sum.inl a'') p.2)
            (by rw [cutSummandsG_node]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩)]
      -- Re-cutting the child cut whole gives the full cut and the cuts inside it.
      have hΦdcl : ((ℱ {RoseTree.node (Sum.inl a'') cs''}).map
            (fun c12 ↦ (c12.1, c12.2,
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L
          = proj3L (({RoseTree.node (Sum.inl a'') cs''} : 𝓕), (0 : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
            ((Cl cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map proj3L := by
        rw [forestCutsG_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map,
            Multiset.map_cons]
        rfl
      rw [hAa, dcl_cons, dcr_cons, hCltl, Multiset.map_singleton,
          Multiset.map_add, Multiset.map_add, dcl_node, hdcr, Multiset.map_add,
          dcr_node, hcoh, hcoassL, hΦdcl, Multiset.map_singleton]
      simp only [← Multiset.singleton_add]
      abel
end

/-! ### Per-tree coassoc `coassT` from `coassL` (node reduction + root wrap) -/

/-- Projecting a `node a`-wrapped triple equals nonplanar-wrapping the
    projected triple. -/
private theorem proj3_node_wrap (a : α ⊕ β)
    (q : 𝓕 × 𝓕 × 𝓛) :
    proj3 (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕))
      = ((proj3L q).1, (proj3L q).2.1,
          ({UnorderedTree.node a (proj3L q).2.2} : Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold proj3 proj3L
  simp only [Multiset.map_singleton]
  rw [UnorderedTree.node_mk_tree_list]

/-- The `node a`-wrap on planar triples, projected, equals the nonplanar
    `node a`-wrap on projected triples. -/
private theorem map_node_wrap_proj3 (a : α ⊕ β)
    (M : Multiset (𝓕 × 𝓕 × 𝓛)) :
    (M.map (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))).map proj3
      = (M.map proj3L).map (fun z ↦ (z.1, z.2.1,
          ({UnorderedTree.node a z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro q _
  exact proj3_node_wrap a q

theorem coassT (hτ : TraceCoherentP τ) (t : RoseTree (α ⊕ β)) :
    (dcLHS (cutSummandsG (extractC τ)) t).map proj3 =
      (dcRHS (cutSummandsG (extractC τ)) t).map proj3 := by
  obtain ⟨a, cs⟩ := t
  -- Core: the two genuine remainder re-cuts agree (= `coassL` wrapped by `node a`).
  have hcore : ((Cl cs).bind (fun p ↦ (ℱ p.1).map
        (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕))))).map proj3
      = ((Cl cs).bind (fun p ↦ (Cl p.2).map
        (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕))))).map proj3 := by
    rw [show ((Cl cs).bind (fun p ↦ (ℱ p.1).map
            (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕)))))
          = ((dcl τ (Cl cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold dcl; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl,
      show ((Cl cs).bind (fun p ↦ (Cl p.2).map
            (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕)))))
          = ((dcr τ (Cl cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold dcr; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl]
    rw [map_node_wrap_proj3, map_node_wrap_proj3, coassL τ hτ cs]
  rw [dcLHS_node, dcRHS_node]
  rw [show (fun p : 𝓕 × 𝓛 ↦
        (𝒯 (RoseTree.node a p.2)).map (fun B12 ↦ (p.1, B12.1, B12.2)))
        = (fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), (0 : 𝓕)) ::ₘ
            (Cl p.2).map (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕)))) from by
      funext p
      rw [treeCuts_node, Multiset.map_cons, Multiset.map_map]; rfl]
  rw [Multiset.bind_cons, Multiset.map_add, Multiset.map_add, Multiset.map_add,
      Multiset.map_cons, Multiset.map_singleton, hcore, ← Multiset.singleton_add]
  abel

end DoubleCut
