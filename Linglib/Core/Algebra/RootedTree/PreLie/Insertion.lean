/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.Graft
public import Linglib.Core.Data.List.Sections
public import Linglib.Core.Data.List.Sublists
public import Linglib.Core.Data.Multiset.Powerset
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Data.Multiset.Bind

/-!
# Multi-tree insertion on rose trees

This file defines the insertion of several guest trees into a host. For a host `T` and guests
`gs`, `insertion T gs` is the multiset, over all assignments of the guests to vertices of `T`, of
the trees obtained by grafting every guest at its vertex at once (`multiGraft`); `insertionForest`
does the same for a host forest. This is the Guin–Oudom extension of the grafting pre-Lie product
to several guests, in the form Foissy gives for decorated trees.

## Main definitions

* `insertion`, `insertionForest`: multi-tree insertion into a tree and into a forest.

## Main results

* `insertion_node`, `insertionForest_cons`, `insertionForest_append`: the guests split between
  the root and the children, or between two parts of the host forest.
* `insertionForest_bind_revzip_sublists'`: splitting an output forest splits the hosts and the
  guests, each guest following its host.
* `insertion_node_msform`, `insertionForest_cons_msform`: the two recursions read through
  `UnorderedTree.mk`.

## References

* [foissy-2021]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

namespace RoseTree

open UnorderedTree

variable {α : Type*}

/-! ## Assignments of guests to vertices

An assignment of `n` guests to the vertices `xs` is a section of `replicate n xs`, a word of
length `n` over `xs`. -/

private theorem bind_sections_filter {β γ δ : Type*} (P : β → Prop) [DecidablePred P]
    (xs : List β) (gs : List γ) (G : List (β × γ) → List (β × γ) → Multiset δ) :
    ((List.replicate gs.length xs).sections : Multiset (List β)).bind (fun ch =>
        G ((ch.zip gs).filter fun p => decide (P p.1))
          ((ch.zip gs).filter fun p => decide (¬ P p.1))) =
      (gs.sublists'.revzip : Multiset (List γ × List γ)).bind fun p =>
        ((List.replicate p.1.length (xs.filter fun x => decide (P x))).sections :
            Multiset (List β)).bind fun u =>
          ((List.replicate p.2.length (xs.filter fun x => decide (¬ P x))).sections :
              Multiset (List β)).bind fun w =>
            G (u.zip p.1) (w.zip p.2) := by
  induction gs generalizing G with
  | nil => simp
  | cons g gs ih =>
    rw [List.length_cons, List.coe_sections_replicate_succ, Multiset.bind_assoc,
      ← Multiset.filter_add_not (fun x => P x) (xs : Multiset β), Multiset.add_bind,
      List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind, ← Multiset.map_coe,
      ← Multiset.map_coe, Multiset.bind_map, Multiset.bind_map]
    simp only [Prod.map_fst, Prod.map_snd, id_eq, List.length_cons,
      List.coe_sections_replicate_succ, Multiset.bind_assoc, Multiset.bind_map,
      Multiset.filter_coe, List.zip_cons_cons]
    rw [add_comm]
    congr 1
    · conv_rhs => enter [2, p]; rw [Multiset.bind_bind]
      rw [Multiset.bind_bind (↑gs.sublists'.revzip : Multiset (List γ × List γ))
        (↑(xs.filter fun x => decide (¬ P x)) : Multiset β)]
      refine Multiset.bind_congr fun v hv => ?_
      have hv : ¬ P v := by simpa using (List.mem_filter.mp (Multiset.mem_coe.mp hv)).2
      simp only [List.filter_cons, decide_eq_true_eq, hv, not_false_eq_true, ite_true, ite_false]
      exact ih fun a b => G a ((v, g) :: b)
    · rw [Multiset.bind_bind (↑gs.sublists'.revzip : Multiset (List γ × List γ))
        (↑(xs.filter fun x => decide (P x)) : Multiset β)]
      refine Multiset.bind_congr fun v hv => ?_
      have hv : P v := by simpa using (List.mem_filter.mp (Multiset.mem_coe.mp hv)).2
      simp only [List.filter_cons, decide_eq_true_eq, hv, not_true_eq_false, ite_true, ite_false]
      exact ih fun a b => G ((v, g) :: a) b

/-! ## `insertion`: single-tree host -/

/-- `insertion T [T₁, …, Tₙ]` is the multiset, over `(v₁, …, vₙ) ∈ V(T)ⁿ`, of
`multiGraft T [(v₁, T₁), …, (vₙ, Tₙ)]`. -/
def insertion (T : RoseTree α) (Ts : List (RoseTree α)) : Multiset (RoseTree α) :=
  Multiset.ofList <| (List.replicate Ts.length (vertices T)).sections.map
    fun choice => multiGraft T (choice.zip Ts)

theorem insertion_def (T : RoseTree α) (Ts : List (RoseTree α)) :
    insertion T Ts =
      Multiset.ofList ((List.replicate Ts.length (vertices T)).sections.map
        fun choice => multiGraft T (choice.zip Ts)) := rfl

/-! ## `insertionForest`: forest host -/

/-- `insertionForest cs gs` is the multiset, over assignments of the guests `gs` to vertices of
the forest `cs`, of the simultaneous grafts `multiGraftChildren`. -/
def insertionForest (cs gs : List (RoseTree α)) : Multiset (List (RoseTree α)) :=
  Multiset.ofList <| (List.replicate gs.length (verticesList cs)).sections.map
    fun ch => multiGraftChildren cs (ch.zip gs)

theorem insertionForest_def (cs gs : List (RoseTree α)) :
    insertionForest cs gs =
      Multiset.ofList ((List.replicate gs.length (verticesList cs)).sections.map
        fun ch => multiGraftChildren cs (ch.zip gs)) := rfl

@[simp] theorem insertionForest_nil_nil :
    insertionForest ([] : List (RoseTree α)) [] = ({[]} : Multiset (List (RoseTree α))) := rfl

@[simp] theorem insertionForest_empty_host_nonempty_guests
    (T_g : RoseTree α) (Ts : List (RoseTree α)) :
    insertionForest ([] : List (RoseTree α)) (T_g :: Ts) = 0 := by
  simp [insertionForest, List.replicate_succ]

@[simp] theorem insertionForest_cons_host_nil_guests
    (T : RoseTree α) (F : List (RoseTree α)) :
    insertionForest (T :: F) ([] : List (RoseTree α)) =
      ({T :: F} : Multiset (List (RoseTree α))) := by
  show (Multiset.ofList [multiGraftChildren (T :: F) []] : Multiset _) = _
  rw [multiGraftChildren_nil_pairs]
  rfl

theorem insertionForest_nil_guests (F : List (RoseTree α)) :
    insertionForest F [] = ({F} : Multiset (List (RoseTree α))) := by
  cases F
  · exact insertionForest_nil_nil
  · exact insertionForest_cons_host_nil_guests _ _

private theorem map_zip_map_left {β β' γ : Type*} {f : β → β'} {f' : β' → β}
    (h : ∀ x, f' (f x) = x) (l : List β) (r : List γ) :
    ((l.map f).zip r).map (Prod.map f' id) = l.zip r := by
  rw [List.zip_map_left, List.map_map]
  exact (List.map_congr_left fun ⟨x, y⟩ _ => by simp [h]).trans (List.map_id _)

theorem value_of_mem_insertion {T T' : RoseTree α} {gs : List (RoseTree α)}
    (h : T' ∈ insertion T gs) : T'.value = T.value := by
  obtain ⟨ch, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
  exact value_multiGraft T _

theorem length_of_mem_insertionForest {cs gs L : List (RoseTree α)}
    (h : L ∈ insertionForest cs gs) : L.length = cs.length := by
  obtain ⟨ch, -, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp h)
  exact multiGraftChildren_length cs _

theorem insertionForest_cons (T : RoseTree α) (F gs : List (RoseTree α)) :
    insertionForest (T :: F) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertion T p.1).bind fun T' => (insertionForest F p.2).map (T' :: ·) := by
  have hne : ∀ p ∈ verticesList (T :: F), p ≠ [] := fun p hp => by
    obtain ⟨k, q, rfl⟩ := exists_cons_of_mem_verticesList hp
    exact List.cons_ne_nil k q
  have hG : ∀ ch ∈ ((List.replicate gs.length (verticesList (T :: F))).sections :
      Multiset (List (List ℕ))),
      ({multiGraftChildren (T :: F) (ch.zip gs)} : Multiset (List (RoseTree α))) =
        {multiGraft T (((ch.zip gs).filter fun p => decide (p.1.head? = some 0)).map
            (Prod.map List.tail id)) ::
          multiGraftChildren F (((ch.zip gs).filter fun p => decide (¬ p.1.head? = some 0)).map
            (Prod.map (List.modifyHead (· - 1)) id))} := by
    intro ch hch
    rw [multiGraftChildren_cons_cs, filterMap_headChildFilter, filterMap_tailChildFilter]
    exact fun p hp =>
      hne _ ((List.mem_sections_replicate.mp (Multiset.mem_coe.mp hch)).2 _ (List.of_mem_zip hp).1)
  have hfilter :
      (verticesList (T :: F)).filter (fun q : List ℕ => decide (q.head? = some 0)) =
          (vertices T).map (0 :: ·) ∧
        (verticesList (T :: F)).filter (fun q : List ℕ => decide (¬ q.head? = some 0)) =
          (verticesList F).map (List.modifyHead (· + 1)) := by
    rw [verticesList_cons, List.filter_append,
      List.filter_append, List.filter_map, List.filter_map, List.filter_map, List.filter_map]
    constructor
    · rw [List.filter_eq_self.2 fun q _ => by simp, List.filter_eq_nil_iff.2 fun q hq => ?_,
        List.map_nil, List.append_nil]
      obtain ⟨k, q, rfl⟩ := exists_cons_of_mem_verticesList hq
      simp
    · rw [List.filter_eq_nil_iff.2 fun q _ => by simp, List.map_nil, List.nil_append,
        List.filter_eq_self.2 fun q hq => ?_]
      obtain ⟨k, q, rfl⟩ := exists_cons_of_mem_verticesList hq
      simp
  rw [insertionForest_def, ← Multiset.map_coe, ← Multiset.bind_singleton,
    Multiset.bind_congr hG,
    bind_sections_filter (fun q : List ℕ => q.head? = some 0) _ gs fun a b =>
      {multiGraft T (a.map (Prod.map List.tail id)) ::
        multiGraftChildren F (b.map (Prod.map (List.modifyHead (· - 1)) id))},
    hfilter.1, hfilter.2]
  symm
  refine Multiset.bind_congr fun p _ => ?_
  rw [insertion_def, insertionForest_def, ← Multiset.map_coe, ← Multiset.map_coe,
    Multiset.bind_map, List.sections_replicate_map, List.sections_replicate_map,
    ← Multiset.map_coe, ← Multiset.map_coe, Multiset.bind_map]
  refine Multiset.bind_congr fun u _ => ?_
  rw [Multiset.bind_map, Multiset.map_map, ← Multiset.bind_singleton]
  refine Multiset.bind_congr fun w _ => ?_
  rw [map_zip_map_left fun _ => rfl, map_zip_map_left fun q => by cases q <;> simp]
  rfl

private theorem bind_revzip_insertionForest_nil {δ : Type*} (gs : List (RoseTree α))
    (H : List (RoseTree α) → List (RoseTree α) → Multiset δ) :
    (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
        (fun p => (insertionForest [] p.1).bind fun A => H A p.2) = H [] gs := by
  induction gs generalizing H with
  | nil => simp
  | cons g gs ih =>
    simp only [List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind,
      ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd, id_eq,
      insertionForest_empty_host_nonempty_guests, Multiset.zero_bind, Multiset.bind_zero,
      add_zero]
    exact ih fun A s => H A (g :: s)

theorem insertionForest_append (xs ys gs : List (RoseTree α)) :
    insertionForest (xs ++ ys) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertionForest xs p.1).bind fun A => (insertionForest ys p.2).map (A ++ ·) := by
  induction xs generalizing gs with
  | nil =>
    rw [List.nil_append,
      bind_revzip_insertionForest_nil gs fun A s => (insertionForest ys s).map (A ++ ·)]
    exact (Multiset.map_id' _).symm
  | cons x xs ih =>
    rw [List.cons_append, insertionForest_cons]
    simp only [ih, insertionForest_cons, Multiset.map_bind, Multiset.map_map, Multiset.bind_assoc,
      Multiset.bind_map]
    rw [← Multiset.bind_revzip_sublists'_assoc gs fun r₁ s₁ s =>
      (insertion x r₁).bind fun T' => (insertionForest xs s₁).bind fun A =>
        (insertionForest ys s).map ((T' :: A) ++ ·)]
    exact Multiset.bind_congr fun p _ => Multiset.bind_bind _ _

theorem insertionForest_bind_revzip_sublists' {δ : Type*} (hs gs : List (RoseTree α))
    (K : List (RoseTree α) → List (RoseTree α) → Multiset δ) :
    (insertionForest hs gs).bind (fun L =>
        (L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
          K x.1 x.2) =
      (hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun h =>
        (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
          (insertionForest h.2 q.2).bind fun L₂ =>
            (insertionForest h.1 q.1).bind fun L₁ => K L₁ L₂ := by
  induction hs generalizing gs K with
  | nil =>
    simp only [List.sublists'_nil, List.revzip_singleton, Multiset.coe_singleton,
      Multiset.singleton_bind]
    rw [Multiset.bind_revzip_sublists'_swap gs fun x y =>
        (insertionForest [] y).bind fun L₂ => (insertionForest [] x).bind fun L₁ => K L₁ L₂,
      bind_revzip_insertionForest_nil gs fun L₂ s =>
        (insertionForest [] s).bind fun L₁ => K L₁ L₂]
    cases gs <;> simp
  | cons T hs ih =>
    have hL : (insertionForest (T :: hs) gs).bind (fun L =>
          (L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
            K x.1 x.2) =
        (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
          (insertion T p.1).bind fun T' =>
            ((hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
              fun h => (p.2.sublists'.revzip :
                  Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
                (insertionForest h.2 q.2).bind fun L₂ =>
                  (insertionForest h.1 q.1).bind fun L₁ => K L₁ (T' :: L₂)) +
            ((hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
              fun h => (p.2.sublists'.revzip :
                  Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
                (insertionForest h.2 q.2).bind fun L₂ =>
                  (insertionForest h.1 q.1).bind fun L₁ => K (T' :: L₁) L₂) := by
      rw [insertionForest_cons, Multiset.bind_assoc]
      refine Multiset.bind_congr fun p _ => ?_
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun T' _ => ?_
      simp only [Multiset.bind_map, List.revzip_sublists'_cons, ← Multiset.coe_add,
        Multiset.add_bind, ← Multiset.map_coe, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.bind_add]
      rw [ih p.2 fun a b => K a (T' :: b), ih p.2 fun a b => K (T' :: a) b]
    rw [hL]
    simp only [Multiset.bind_add, List.revzip_sublists'_cons, ← Multiset.coe_add,
      Multiset.add_bind, ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd,
      id_eq, insertionForest_cons, Multiset.bind_assoc]
    rw [Multiset.bind_bind_bind_comm, Multiset.bind_bind_bind_comm]
    congr 1
    · exact Multiset.bind_congr fun h _ => Multiset.bind_revzip_sublists'_bind_assoc gs
        (insertion T) fun T' g₁ g₂ => (insertionForest h.2 g₂).bind fun L₂ =>
          (insertionForest h.1 g₁).bind fun L₁ => K L₁ (T' :: L₂)
    · refine Multiset.bind_congr fun h _ => ?_
      rw [Multiset.bind_revzip_sublists'_bind_assoc' gs (insertion T) fun T' g₁ g₂ =>
        (insertionForest h.2 g₂).bind fun L₂ => (insertionForest h.1 g₁).bind fun L₁ =>
          K (T' :: L₁) L₂]
      exact Multiset.bind_congr fun q _ => Multiset.bind_bind_bind_comm _ _ _ _

theorem insertion_node (a : α) (cs gs : List (RoseTree α)) :
    insertion (RoseTree.node a cs) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertionForest cs p.2).map fun cs' => RoseTree.node a (p.1 ++ cs') := by
  have hG :
      ∀ ch ∈ ((List.replicate gs.length (vertices (RoseTree.node a cs))).sections :
        Multiset (List (List ℕ))),
      ({multiGraft (RoseTree.node a cs) (ch.zip gs)} : Multiset (RoseTree α)) =
        {RoseTree.node a (((ch.zip gs).filter fun p => decide (p.1 = [])).map Prod.snd ++
          multiGraftChildren cs ((ch.zip gs).filter fun p => decide (¬ p.1 = [])))} := by
    intro ch _
    rw [multiGraft_node, filterMap_rootPrependFilter, ← multiGraftChildren_filter_ne_nil]
  have hfilter :
      (vertices (RoseTree.node a cs)).filter (fun q : List ℕ => decide (q = [])) = [[]] ∧
        (vertices (RoseTree.node a cs)).filter (fun q : List ℕ => decide (¬ q = [])) =
          verticesList cs := by
    have h : ∀ q ∈ verticesList cs, q ≠ [] := fun q hq => by
      obtain ⟨k, q, rfl⟩ := exists_cons_of_mem_verticesList hq
      exact List.cons_ne_nil k q
    rw [vertices_node]
    constructor
    · rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 fun q hq => by simp [h q hq]]
    · rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2 fun q hq => by simp [h q hq]]
  rw [insertion_def, ← Multiset.map_coe, ← Multiset.bind_singleton, Multiset.bind_congr hG,
    bind_sections_filter (fun q : List ℕ => q = []) _ gs fun r s =>
      {RoseTree.node a (r.map Prod.snd ++ multiGraftChildren cs s)},
    hfilter.1, hfilter.2]
  refine Multiset.bind_congr fun p _ => ?_
  rw [List.sections_replicate_singleton, Multiset.coe_singleton, Multiset.singleton_bind,
    List.map_snd_zip (by simp), insertionForest_def, ← Multiset.map_coe,
    Multiset.map_map, ← Multiset.bind_singleton]
  rfl

/-! ## Reading the recursion through `UnorderedTree.mk`

`insertion_node` and `insertionForest_cons` with every output read through `UnorderedTree.mk`,
the form in which `UnorderedTree.insertion_mk` matches them against the nonplanar recursion. -/

private theorem msform_cons (T : RoseTree α) (L : List (RoseTree α)) :
    (↑((T :: L).map UnorderedTree.mk) : Multiset (UnorderedTree α)) =
      UnorderedTree.mk T ::ₘ ↑(L.map UnorderedTree.mk) := rfl

theorem insertionForest_cons_msform (T : RoseTree α) (F gs : List (RoseTree α)) :
    (insertionForest (T :: F) gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        ((insertion T p.1).map UnorderedTree.mk).bind fun X =>
          ((insertionForest F p.2).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))).map
            (X ::ₘ ·) := by
  rw [insertionForest_cons, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  rw [Multiset.map_bind, Multiset.bind_map]
  refine Multiset.bind_congr fun T' _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun L _ => msform_cons T' L

theorem insertion_node_msform (a : α) (cs gs : List (RoseTree α)) :
    (insertion (RoseTree.node a cs) gs).map UnorderedTree.mk =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        ((insertionForest cs p.2).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))).map fun X =>
          UnorderedTree.node a (↑(p.1.map UnorderedTree.mk) + X) := by
  rw [insertion_node, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun cs' _ => ?_
  show UnorderedTree.mk (RoseTree.node a (p.1 ++ cs')) = _
  rw [← UnorderedTree.node_mk_tree_list, List.map_append, ← Multiset.coe_add]
  rfl

/-! ## Singleton hosts and empty guest lists -/

theorem insertion_nil_guests (T : RoseTree α) :
    insertion T ([] : List (RoseTree α)) = ({T} : Multiset (RoseTree α)) := by
  rw [insertion_def]
  simp only [List.length_nil, List.replicate_zero, List.sections, List.zip_nil_right,
             multiGraft_nil, List.map_cons, List.map_nil,
             Multiset.coe_singleton]

theorem insertionForest_singleton (T : RoseTree α) (gs : List (RoseTree α)) :
    insertionForest [T] gs = (insertion T gs).map (fun T' => [T']) := by
  rw [insertionForest_def, insertion_def, verticesList_cons, verticesList_nil, List.map_nil,
    List.append_nil, List.sections_replicate_map, ← Multiset.map_coe, ← Multiset.map_coe,
    ← Multiset.map_coe, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun u _ => ?_
  show multiGraftChildren [T] ((u.map (0 :: ·)).zip gs) = [multiGraft T (u.zip gs)]
  rw [multiGraftChildren_cons_cs, multiGraftChildren_nil_cs, filterMap_headChildFilter,
    List.filter_eq_self.2 fun p hp => ?_, map_zip_map_left fun _ => rfl]
  obtain ⟨q, T'⟩ := p
  obtain ⟨q', -, rfl⟩ := List.mem_map.mp (List.of_mem_zip hp).1
  simp

end RoseTree
