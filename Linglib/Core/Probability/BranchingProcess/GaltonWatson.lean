/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.BinaryTree
public import Linglib.Core.Order.TreePath
public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.MeasureTheory.Integral.Lebesgue.Basic
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.Probability.Kernel.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Multitype Galton–Watson processes

A multitype Galton–Watson process with types `ι` is an offspring kernel `ξ : Kernel ι (List ι)`:
an individual of type `i` has offspring drawn from `ξ i`, an ordered list of types, each of which
founds an independent copy of the process. Following [neveu-1986], every address `u : TreePath` and
type `i` draws an offspring list independently, and the family tree of an individual is a function
of the draws. Subtrees at different children read disjoint draws, so
[a tree is complete within `n + 1` generations with the expected product of its children's
probabilities for `n`](##ProbabilityTheory.GaltonWatson.extinctWithin_succ),
[a finite tree has the product of the offspring probabilities at its
nodes](##ProbabilityTheory.GaltonWatson.law_singleton_value), and
[the extinction probabilities are a fixed point of the offspring generating
function](##ProbabilityTheory.GaltonWatson.extinctionProb_eq_lintegral).
[A finite excessive measure forces
extinction](##ProbabilityTheory.GaltonWatson.ae_extinctionProb_eq_one).

A probabilistic context-free grammar is the instance whose types are the symbols: a terminal has
no offspring, and a nonterminal's offspring is the right-hand side of a rule chosen with its
weight; see `PCFG.galtonWatson`.

## Implementation notes

The offspring kernel need not be Markov: the missing mass of a sub-probability offspring law is
the probability that the individual is killed, drawn as `none`, and the grammar instance has the
zero measure at a nonterminal no rule expands. An offspring law of mass more than one is always
killed, so the results that read `ξ` assume mass at most one. Trees carry the discrete σ-algebra.

## TODO

The extinction probability is the least fixed point of the offspring generating function and
equals one exactly when the mean matrix is subcritical or critical ([athreya-ney-1972]). Neither
is proved here, only the sufficient condition `GaltonWatson.ae_extinctionProb_eq_one`.

## References

* [neveu-1986]
* [athreya-ney-1972]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel RoseTree Core.Order
open scoped ENNReal

instance RoseTree.instMeasurableSpace {α : Type*} : MeasurableSpace (RoseTree α) := ⊤

namespace ProbabilityTheory.GaltonWatson

variable {ι : Type*} [MeasurableSpace ι]

/-! ### The draws -/

/-- A draw of offspring at every address and type; `none` is a killed individual. -/
abbrev Draws (ι : Type*) := TreePath × ι → Option (List ι)

open scoped Classical in
/-- A sub-probability offspring law, with its missing mass sent to the killed state. -/
noncomputable def killed (μ : Measure (List ι)) : Measure (Option (List ι)) :=
  if μ Set.univ ≤ 1 then μ.map some + (1 - μ Set.univ) • Measure.dirac none
  else Measure.dirac none

instance (μ : Measure (List ι)) : IsProbabilityMeasure (killed μ) := by
  refine ⟨?_⟩
  unfold killed
  split_ifs with h
  · rw [Measure.add_apply, Measure.map_apply measurable_some .univ, Measure.smul_apply]
    simp [add_tsub_cancel_of_le h]
  · simp

omit [MeasurableSpace ι] in
theorem killed_some {μ : Measure (List ι)} (h : μ Set.univ ≤ 1) (js : List ι) :
    killed μ {some js} = μ {js} := by
  have : (some ⁻¹' {(some js : Option (List ι))}) = {js} := by ext; simp
  rw [killed, ite_eq_left h, Measure.add_apply, Measure.map_apply measurable_some .of_discrete,
    Measure.smul_apply, this, Measure.dirac_apply' _ .of_discrete]
  simp

variable (ξ : Kernel ι (List ι))

/-- The draws are independent, the one at `(u, i)` with law `ξ i`. -/
noncomputable def draws : Measure (Draws ι) := Measure.infinitePi fun p ↦ killed (ξ p.2)

instance : IsProbabilityMeasure (draws ξ) := by rw [draws]; infer_instance

theorem draws_eval_eq_some (hξ : ∀ i, ξ i Set.univ ≤ 1) (u : TreePath) (i : ι) (js : List ι) :
    draws ξ {ω | ω (u, i) = some js} = ξ i {js} := by
  rw [← killed_some (hξ i), ← Measure.infinitePi_map_eval (fun p : TreePath × ι ↦ killed (ξ p.2))
    (u, i), Measure.map_apply (measurable_pi_apply _) .of_discrete]
  rfl

/-! ### The family tree -/

/-- The family tree of an individual of type `i` at address `u`, if it is complete within `n`
generations. -/
def treeWithin (ω : Draws ι) : ℕ → TreePath → ι → Option (RoseTree ι)
  | 0, _, _ => none
  | n + 1, u, i => (ω (u, i)).bind fun js ↦
      (js.zipIdx.mapM fun p ↦ treeWithin ω n (u.child p.2) p.1).map (node i)

section Tree

omit [MeasurableSpace ι]

variable {ω : Draws ι} {u : TreePath} {i : ι}

private theorem isSome_mapM {α β : Type*} (f : α → Option β) :
    ∀ l : List α, (l.mapM f).isSome ↔ ∀ a ∈ l, (f a).isSome
  | [] => by simp
  | a :: l => by
    have ih := isSome_mapM f l
    cases hfa : f a <;> cases hl : l.mapM f <;> simp_all [List.mapM_cons]

private theorem mapM_mono {α β : Type*} {f g : α → Option β}
    (h : ∀ a b, f a = some b → g a = some b) :
    ∀ (l : List α) (bs : List β), l.mapM f = some bs → l.mapM g = some bs
  | [], bs, hl => by simpa using hl
  | a :: l, bs, hl => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl ⊢
    obtain ⟨b, hb, bs', hbs', rfl⟩ := hl
    exact ⟨b, h a b hb, bs', mapM_mono h l bs' hbs', rfl⟩

private theorem exists_forall_mem_of_mono {α : Type*} {P : α → ℕ → Prop}
    (hP : ∀ a m n, m ≤ n → P a m → P a n) :
    ∀ l : List α, (∀ a ∈ l, ∃ n, P a n) → ∃ N, ∀ a ∈ l, P a N
  | [], _ => ⟨0, by simp⟩
  | a :: l, h => by
    obtain ⟨N, hN⟩ := exists_forall_mem_of_mono hP l fun b hb ↦ h b (.tail _ hb)
    obtain ⟨n, hn⟩ := h a (.head _)
    refine ⟨max n N, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hP a _ _ (le_max_left ..) hn, fun b hb ↦ hP b _ _ (le_max_right ..) (hN b hb)⟩

theorem isSome_treeWithin_succ (ω : Draws ι) (n : ℕ) (u : TreePath) (i : ι) :
    (treeWithin ω (n + 1) u i).isSome ↔ ∃ js, ω (u, i) = some js ∧
      ∀ p ∈ js.zipIdx, (treeWithin ω n (u.child p.2) p.1).isSome := by
  rw [treeWithin]
  cases hω : ω (u, i) <;> simp [isSome_mapM]

/-- The family tree of an individual of type `i` is rooted at `i`. -/
theorem value_eq_of_treeWithin_eq_some : ∀ {n : ℕ} {u : TreePath} {i : ι} {t : RoseTree ι},
    treeWithin ω n u i = some t → t.value = i
  | 0, _, _, _, h => by simp [treeWithin] at h
  | n + 1, u, i, t, h => by
    rw [treeWithin] at h
    cases hω : ω (u, i) with
    | none => simp [hω] at h
    | some js =>
      simp only [hω, Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨cs, -, rfl⟩ := h
      rfl

theorem treeWithin_succ_of_eq_some : ∀ {n : ℕ} {u : TreePath} {i : ι} {t : RoseTree ι},
    treeWithin ω n u i = some t → treeWithin ω (n + 1) u i = some t
  | 0, _, _, _, h => by simp [treeWithin] at h
  | n + 1, u, i, t, h => by
    rw [treeWithin] at h ⊢
    cases hω : ω (u, i) with
    | none => simp [hω] at h
    | some js =>
      simp only [hω, Option.bind_some, Option.map_eq_some_iff] at h ⊢
      obtain ⟨cs, hcs, rfl⟩ := h
      exact ⟨cs, mapM_mono (fun p t ht ↦ treeWithin_succ_of_eq_some ht) _ _ hcs, rfl⟩

/-- More generations complete the same tree. -/
theorem treeWithin_mono {m n : ℕ} (h : m ≤ n) {t : RoseTree ι}
    (ht : treeWithin ω m u i = some t) : treeWithin ω n u i = some t :=
  Nat.le_induction ht (fun _ _ ih ↦ treeWithin_succ_of_eq_some ih) n h

theorem isSome_treeWithin_mono {m n : ℕ} (h : m ≤ n) (ht : (treeWithin ω m u i).isSome) :
    (treeWithin ω n u i).isSome := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ht
  exact Option.isSome_iff_exists.2 ⟨t, treeWithin_mono h ht⟩

private theorem mapM_zipIdx_eq_some {g : ℕ → ι → Option (RoseTree ι)}
    (hg : ∀ k j c, g k j = some c → c.value = j) :
    ∀ (js : List ι) (s : ℕ) (cs : List (RoseTree ι)),
      (js.zipIdx s).mapM (fun p ↦ g p.2 p.1) = some cs ↔
        js = cs.map value ∧ ∀ p ∈ cs.zipIdx s, g p.2 p.1.value = some p.1
  | [], s, cs => by cases cs <;> simp
  | j :: js, s, [] => by simp [List.mapM_cons, Option.bind_eq_some_iff]
  | j :: js, s, c :: cs => by
    have ih := mapM_zipIdx_eq_some hg js (s + 1) cs
    simp only [List.zipIdx_cons, List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq, List.cons.injEq, List.map_cons, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨c', hc', cs', hcs', rfl, rfl⟩
      obtain ⟨rfl, h⟩ := ih.1 hcs'
      obtain rfl := hg _ _ _ hc'
      exact ⟨⟨rfl, rfl⟩, hc', h⟩
    · rintro ⟨⟨rfl, rfl⟩, hc, h⟩
      exact ⟨c, hc, cs, ih.2 ⟨rfl, h⟩, rfl, rfl⟩

private theorem map_zipIdx_eq_map {α β : Type*} (f : α → β) (l : List α) :
    (l.zipIdx.map fun p ↦ f p.1) = l.map f := by
  conv_rhs => rw [← List.zipIdx_map_fst 0 l, List.map_map]
  rfl

theorem setOf_treeWithin_eq_empty {t : RoseTree ι} (h : t.value ≠ i) :
    {ω : Draws ι | ∃ n, treeWithin ω n u i = some t} = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ by
    obtain ⟨n, hn⟩ := hω
    exact h (value_eq_of_treeWithin_eq_some hn)

/-- A node is the family tree at `u` when its children's types are drawn there and each child is
the family tree at its address. -/
theorem exists_treeWithin_eq_some_node (ω : Draws ι) (u : TreePath) (i : ι)
    (cs : List (RoseTree ι)) :
    (∃ n, treeWithin ω n u i = some (node i cs)) ↔ ω (u, i) = some (cs.map value) ∧
      ∀ p ∈ cs.zipIdx, ∃ n, treeWithin ω n (u.child p.2) p.1.value = some p.1 := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [treeWithin] at hn
    | succ n =>
      rw [treeWithin] at hn
      cases hω : ω (u, i) with
      | none => simp [hω] at hn
      | some js =>
        simp only [hω, Option.bind_some, Option.map_eq_some_iff, node.injEq, true_and] at hn
        obtain ⟨cs', hcs', rfl⟩ := hn
        obtain ⟨rfl, h⟩ := (mapM_zipIdx_eq_some (g := fun k j ↦ treeWithin ω n (u.child k) j)
          (fun _ _ _ ↦ value_eq_of_treeWithin_eq_some) js 0 cs').1 hcs'
        exact ⟨rfl, fun p hp ↦ ⟨n, h p hp⟩⟩
  · rintro ⟨hω, h⟩
    obtain ⟨N, hN⟩ := exists_forall_mem_of_mono
      (P := fun (p : RoseTree ι × ℕ) n ↦ treeWithin ω n (u.child p.2) p.1.value = some p.1)
      (fun _ _ _ hmn ↦ treeWithin_mono hmn) cs.zipIdx h
    refine ⟨N + 1, ?_⟩
    rw [treeWithin, hω, Option.bind_some,
      (mapM_zipIdx_eq_some (g := fun k j ↦ treeWithin ω N (u.child k) j)
        (fun _ _ _ ↦ value_eq_of_treeWithin_eq_some) (cs.map value) 0 cs).2 ⟨rfl, hN⟩]
    rfl

/-- A family tree is finite when the family trees of all the offspring are. -/
theorem exists_isSome_treeWithin (ω : Draws ι) (u : TreePath) (i : ι) :
    (∃ n, (treeWithin ω n u i).isSome) ↔ ∃ js, ω (u, i) = some js ∧
      ∀ p ∈ js.zipIdx, ∃ n, (treeWithin ω n (u.child p.2) p.1).isSome := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [treeWithin] at hn
    | succ n =>
      obtain ⟨js, h₁, h₂⟩ := (isSome_treeWithin_succ ω n u i).1 hn
      exact ⟨js, h₁, fun p hp ↦ ⟨n, h₂ p hp⟩⟩
  · rintro ⟨js, h₁, h₂⟩
    obtain ⟨N, hN⟩ := exists_forall_mem_of_mono
      (P := fun (p : ι × ℕ) n ↦ (treeWithin ω n (u.child p.2) p.1).isSome)
      (fun _ _ _ hmn ↦ isSome_treeWithin_mono hmn) js.zipIdx h₂
    exact ⟨N + 1, (isSome_treeWithin_succ ω N u i).2 ⟨js, h₁, hN⟩⟩

end Tree

/-- The probability of a finite family tree: the product over its nodes of the offspring
probability of the list of types below that node. -/
noncomputable def weight (t : RoseTree ι) : ℝ≥0∞ := (t.localTrees.map fun p ↦ ξ p.1 {p.2}).prod

theorem weight_node (i : ι) (cs : List (RoseTree ι)) :
    weight ξ (node i cs) = ξ i {cs.map value} * (cs.map (weight ξ)).prod := by
  simp only [weight, localTrees_node, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_map, Function.comp_def]
  rfl

/-! ### Independence of the subtrees -/

/-- The σ-algebra of the draws at the coordinates in `S`. -/
private abbrev gen (S : Set (TreePath × ι)) : MeasurableSpace (Draws ι) :=
  ⨆ q ∈ S, MeasurableSpace.comap (fun ω : Draws ι ↦ ω q) inferInstance

omit [MeasurableSpace ι] in
private theorem gen_le (S : Set (TreePath × ι)) : gen S ≤ MeasurableSpace.pi :=
  iSup₂_le fun q _ ↦ (measurable_pi_apply q).comap_le

omit [MeasurableSpace ι] in
private theorem gen_mono {S T : Set (TreePath × ι)} (h : S ⊆ T) : gen S ≤ gen T :=
  biSup_mono h

omit [MeasurableSpace ι] in
private theorem measurableSet_gen_eval {S : Set (TreePath × ι)} {q : TreePath × ι} (hq : q ∈ S)
    (x : Option (List ι)) : MeasurableSet[gen S] {ω : Draws ι | ω q = x} :=
  le_biSup (fun q ↦ MeasurableSpace.comap (fun ω : Draws ι ↦ ω q) inferInstance) hq _
    ⟨{x}, .of_discrete, rfl⟩

omit [MeasurableSpace ι] in
private theorem measurableSet_forall_mem {α : Type*} {m : MeasurableSpace (Draws ι)}
    (l : List α) {A : α → Set (Draws ι)} (h : ∀ p ∈ l, MeasurableSet[m] (A p)) :
    MeasurableSet[m] {ω | ∀ p ∈ l, ω ∈ A p} := by
  have : {ω | ∀ p ∈ l, ω ∈ A p} = ⋂ p ∈ {p | p ∈ l}, A p := by ext; simp
  rw [this]
  exact .biInter (List.finite_toSet l).countable h

private theorem indep_gen {S T : Set (TreePath × ι)} (h : Disjoint S T) :
    Indep (gen S) (gen T) (draws ξ) :=
  indep_iSup_of_disjoint (fun q ↦ (measurable_pi_apply q).comap_le)
    (iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id).iIndep h

/-- The coordinates not below any child of `u` numbered `s` or more. -/
private def before (u : TreePath) (s : ℕ) : Set (TreePath × ι) :=
  {q | ∀ k, s ≤ k → ¬ u.child k ≤ q.1}

/-- Events below the children of `u` numbered from `s` are independent of each other and of any
event before them. -/
private theorem draws_inter_children {α : Type*} (u : TreePath) {A : ℕ → α → Set (Draws ι)}
    (hA : ∀ k a, MeasurableSet[gen {q : TreePath × ι | u.child k ≤ q.1}] (A k a)) :
    ∀ (l : List α) (s : ℕ) {C : Set (Draws ι)}, MeasurableSet[gen (before u s)] C →
      draws ξ (C ∩ {ω | ∀ p ∈ l.zipIdx s, ω ∈ A p.2 p.1}) =
        draws ξ C * ((l.zipIdx s).map fun p ↦ draws ξ (A p.2 p.1)).prod
  | [], s, C, _ => by simp
  | a :: l, s, C, hC => by
    have hCA : MeasurableSet[gen (before u (s + 1))] (C ∩ A s a) :=
      .inter (gen_mono (S := before u s) (T := before u (s + 1))
          (fun q hq k hk ↦ hq k (by omega)) _ hC)
        (gen_mono (T := before u (s + 1)) (fun q (hq : u.child s ≤ q.1) k hk h ↦ by
          have := TreePath.eq_of_child_le_of_child_le hq h; omega) _ (hA s a))
    have hd : Disjoint (before (ι := ι) u s) {q | u.child s ≤ q.1} :=
      Set.disjoint_left.2 fun q hq h ↦ hq s le_rfl h
    have hset : C ∩ {ω | ∀ p ∈ (a :: l).zipIdx s, ω ∈ A p.2 p.1} =
        (C ∩ A s a) ∩ {ω | ∀ p ∈ l.zipIdx (s + 1), ω ∈ A p.2 p.1} := by
      ext ω
      simp [and_assoc]
    rw [hset, draws_inter_children u hA l (s + 1) hCA,
      (Indep_iff _ _ _).1 (indep_gen ξ hd) _ _ hC (hA s a), List.zipIdx_cons, List.map_cons,
      List.prod_cons, mul_assoc]

omit [MeasurableSpace ι] in
private theorem measurableSet_gen_eval_self (u : TreePath) (i : ι) (x : Option (List ι)) :
    MeasurableSet[gen (before u 0)] {ω : Draws ι | ω (u, i) = x} :=
  measurableSet_gen_eval (S := before u 0) (q := (u, i))
    (fun k _ (h : u.child k ≤ u) ↦ (u.lt_child k).not_ge h) _

/-! ### The probability of a finite tree -/

omit [MeasurableSpace ι] in
private theorem measurableSet_gen_treeWithin_eq (t : RoseTree ι) : ∀ u : TreePath,
    MeasurableSet[gen {q : TreePath × ι | u ≤ q.1}]
      {ω : Draws ι | ∃ n, treeWithin ω n u t.value = some t} := by
  induction t with
  | node i cs ih =>
    intro u
    have : {ω : Draws ι | ∃ n, treeWithin ω n u i = some (node i cs)} =
        {ω | ω (u, i) = some (cs.map value)} ∩ {ω | ∀ p ∈ cs.zipIdx,
          ω ∈ {ω : Draws ι | ∃ n, treeWithin ω n (u.child p.2) p.1.value = some p.1}} := by
      ext ω
      exact exists_treeWithin_eq_some_node ω u i cs
    rw [value_node, this]
    exact .inter (measurableSet_gen_eval (S := {q : TreePath × ι | u ≤ q.1}) (q := (u, i))
      (le_refl u) _) <| measurableSet_forall_mem _
      fun p hp ↦ gen_mono (fun q hq ↦ (u.le_child _).trans hq) _
        (ih p.1 (List.fst_mem_of_mem_zipIdx hp) _)

/-- A finite tree is the family tree of its root type, at any address, with probability
`weight`. -/
theorem draws_treeWithin_eq_some (hξ : ∀ i, ξ i Set.univ ≤ 1) (t : RoseTree ι) :
    ∀ u : TreePath, draws ξ {ω | ∃ n, treeWithin ω n u t.value = some t} = weight ξ t := by
  induction t with
  | node i cs ih =>
    intro u
    have hset : {ω : Draws ι | ∃ n, treeWithin ω n u i = some (node i cs)} =
        {ω | ω (u, i) = some (cs.map value)} ∩ {ω | ∀ p ∈ cs.zipIdx,
          ω ∈ {ω : Draws ι | ∃ n, treeWithin ω n (u.child p.2) p.1.value = some p.1}} := by
      ext ω
      exact exists_treeWithin_eq_some_node ω u i cs
    have hprod : (cs.zipIdx.map fun p ↦ draws ξ
        {ω : Draws ι | ∃ n, treeWithin ω n (u.child p.2) p.1.value = some p.1}) =
        cs.map (weight ξ) := by
      rw [List.map_congr_left fun p hp ↦ ih p.1 (List.fst_mem_of_mem_zipIdx hp) _,
        map_zipIdx_eq_map]
    rw [value_node, hset, draws_inter_children ξ u
      (A := fun k c ↦ {ω : Draws ι | ∃ n, treeWithin ω n (u.child k) c.value = some c})
      (fun k c ↦ measurableSet_gen_treeWithin_eq c _) cs 0 (measurableSet_gen_eval_self u i _),
      draws_eval_eq_some ξ hξ, hprod, weight_node]

/-! ### The branching step -/

variable [Countable ι]

/-- An event that holds when the offspring drawn at `(u, i)` each satisfy an event below their
own address has the expected product of the probabilities of those events. -/
private theorem draws_eq_lintegral (hξ : ∀ i, ξ i Set.univ ≤ 1) {u : TreePath} {i : ι}
    {B : Set (Draws ι)} {A : ℕ → ι → Set (Draws ι)}
    (hA : ∀ k j, MeasurableSet[gen {q : TreePath × ι | u.child k ≤ q.1}] (A k j))
    (hB : ∀ ω, ω ∈ B ↔ ∃ js, ω (u, i) = some js ∧ ∀ p ∈ js.zipIdx, ω ∈ A p.2 p.1) :
    draws ξ B = ∫⁻ js, (js.zipIdx.map fun p ↦ draws ξ (A p.2 p.1)).prod ∂ξ i := by
  have hset : B = ⋃ js : List ι,
      ({ω | ω (u, i) = some js} ∩ {ω | ∀ p ∈ js.zipIdx, ω ∈ A p.2 p.1}) := by
    ext ω
    simp [hB]
  have hmeas (js : List ι) : MeasurableSet ({ω : Draws ι | ω (u, i) = some js} ∩
      {ω | ∀ p ∈ js.zipIdx, ω ∈ A p.2 p.1}) :=
    .inter (gen_le _ _ (measurableSet_gen_eval_self u i _)) <|
      measurableSet_forall_mem (A := fun p : ι × ℕ ↦ A p.2 p.1) _
        fun p _ ↦ gen_le _ _ (hA p.2 p.1)
  have hdisj : Pairwise (Function.onFun Disjoint fun js : List ι ↦
      {ω : Draws ι | ω (u, i) = some js} ∩ {ω | ∀ p ∈ js.zipIdx, ω ∈ A p.2 p.1}) :=
    fun js js' h ↦ Set.disjoint_left.2 fun ω hω hω' ↦
      h (Option.some.inj (hω.1.symm.trans hω'.1))
  rw [hset, measure_iUnion hdisj hmeas, lintegral_countable']
  exact tsum_congr fun js ↦ by
    rw [draws_inter_children ξ u hA js 0 (measurableSet_gen_eval_self u i _),
      draws_eval_eq_some ξ hξ, mul_comm]

omit [MeasurableSpace ι] in
/-- Completion within `n` generations at `u` reads only the draws at addresses below `u`. -/
private theorem measurableSet_gen_isSome : ∀ (n : ℕ) (u : TreePath) (i : ι),
    MeasurableSet[gen {q : TreePath × ι | u ≤ q.1}] {ω : Draws ι | (treeWithin ω n u i).isSome}
  | 0, _, _ => by simp [treeWithin]
  | n + 1, u, i => by
    have : {ω : Draws ι | (treeWithin ω (n + 1) u i).isSome} = ⋃ js : List ι,
        ({ω | ω (u, i) = some js} ∩ {ω | ∀ p ∈ js.zipIdx,
          ω ∈ {ω : Draws ι | (treeWithin ω n (u.child p.2) p.1).isSome}}) := by
      ext ω
      simp [isSome_treeWithin_succ]
    rw [this]
    exact .iUnion fun js ↦ .inter (measurableSet_gen_eval (S := {q : TreePath × ι | u ≤ q.1})
      (q := (u, i)) (le_refl u) _) <|
      measurableSet_forall_mem _ fun p _ ↦
        gen_mono (fun q hq ↦ (u.le_child _).trans hq) _
          (measurableSet_gen_isSome n _ _)

omit [MeasurableSpace ι] in
private theorem measurableSet_gen_exists_isSome (u : TreePath) (i : ι) :
    MeasurableSet[gen {q : TreePath × ι | u ≤ q.1}]
      {ω : Draws ι | ∃ n, (treeWithin ω n u i).isSome} := by
  rw [Set.ofPred_exists]
  exact .iUnion fun n ↦ measurableSet_gen_isSome n u i

/-- The probability that the family tree of type `i` is complete within `n` generations. -/
noncomputable def extinctWithin (n : ℕ) (i : ι) : ℝ≥0∞ :=
  draws ξ {ω | (treeWithin ω n ⊥ i).isSome}

omit [Countable ι] in
@[simp] theorem extinctWithin_zero (i : ι) : extinctWithin ξ 0 i = 0 := by
  simp [extinctWithin, treeWithin]

omit [Countable ι] in
theorem monotone_extinctWithin (i : ι) : Monotone fun n ↦ extinctWithin ξ n i :=
  fun _ _ h ↦ measure_mono fun _ hω ↦ isSome_treeWithin_mono h hω

/-- The branching step at an address: the children's trees are independent of each other and of
the draw at the parent. -/
theorem draws_isSome_treeWithin_succ (hξ : ∀ i, ξ i Set.univ ≤ 1) (n : ℕ) (u : TreePath) (i : ι) :
    draws ξ {ω | (treeWithin ω (n + 1) u i).isSome} = ∫⁻ js,
      (js.zipIdx.map fun p ↦ draws ξ {ω | (treeWithin ω n (u.child p.2) p.1).isSome}).prod ∂ξ i :=
  draws_eq_lintegral ξ hξ (fun _ j ↦ measurableSet_gen_isSome n _ j)
    fun ω ↦ isSome_treeWithin_succ ω n u i

/-- The probability of completing within `n` generations does not depend on the address. -/
theorem draws_isSome_treeWithin (hξ : ∀ i, ξ i Set.univ ≤ 1) : ∀ (n : ℕ) (u : TreePath) (i : ι),
    draws ξ {ω | (treeWithin ω n u i).isSome} = extinctWithin ξ n i
  | 0, _, _ => by simp [treeWithin]
  | n + 1, u, i => by
    rw [extinctWithin, draws_isSome_treeWithin_succ ξ hξ, draws_isSome_treeWithin_succ ξ hξ]
    exact lintegral_congr fun js ↦ congrArg List.prod <| List.map_congr_left fun p _ ↦
      (draws_isSome_treeWithin hξ n _ _).trans (draws_isSome_treeWithin hξ n _ _).symm

/-- The branching step: a tree is complete within `n + 1` generations when the trees of its
children are complete within `n`, and these are independent. -/
theorem extinctWithin_succ (hξ : ∀ i, ξ i Set.univ ≤ 1) (n : ℕ) (i : ι) :
    extinctWithin ξ (n + 1) i = ∫⁻ js, (js.map (extinctWithin ξ n)).prod ∂ξ i := by
  rw [extinctWithin, draws_isSome_treeWithin_succ ξ hξ]
  refine lintegral_congr fun js ↦ congrArg List.prod ?_
  rw [← map_zipIdx_eq_map (extinctWithin ξ n) js]
  exact List.map_congr_left fun p _ ↦ draws_isSome_treeWithin ξ hξ n _ _

/-! ### The law of the family tree -/

variable [MeasurableSingletonClass ι]

/-- The law of the finite family tree at each type; the missing mass is the probability that the
family is killed or survives forever. -/
noncomputable def law : Kernel ι (RoseTree ι) :=
  ofFunOfCountable fun i ↦ Measure.sum fun t ↦
    draws ξ {ω | ∃ n, treeWithin ω n ⊥ i = some t} • Measure.dirac t

theorem law_singleton_eq_draws (i : ι) (t : RoseTree ι) :
    law ξ i {t} = draws ξ {ω | ∃ n, treeWithin ω n ⊥ i = some t} := by
  rw [law, ofFunOfCountable_apply, Measure.sum_apply _ .of_discrete, tsum_eq_single t fun t' h ↦ by
    simp [Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := {t})), h]]
  simp

theorem law_singleton_of_ne {t : RoseTree ι} {i : ι} (h : t.value ≠ i) : law ξ i {t} = 0 := by
  rw [law_singleton_eq_draws, setOf_treeWithin_eq_empty h, measure_empty]

/-- A finite tree has probability `weight` under the law at its root type. -/
theorem law_singleton_value (hξ : ∀ i, ξ i Set.univ ≤ 1) (t : RoseTree ι) :
    law ξ t.value {t} = weight ξ t := by
  rw [law_singleton_eq_draws, draws_treeWithin_eq_some ξ hξ]

open scoped Classical in
theorem law_singleton (hξ : ∀ i, ξ i Set.univ ≤ 1) (t : RoseTree ι) (i : ι) :
    law ξ i {t} = if t.value = i then weight ξ t else 0 := by
  split_ifs with h
  · subst h; exact law_singleton_value ξ hξ t
  · exact law_singleton_of_ne ξ h

/-- The mass of the law is the probability that the family tree is finite. -/
theorem law_apply_univ (i : ι) :
    law ξ i Set.univ = draws ξ {ω | ∃ n, (treeWithin ω n ⊥ i).isSome} := by
  have hmeas (t : RoseTree ι) :
      MeasurableSet {ω : Draws ι | ∃ n, treeWithin ω n ⊥ i = some t} := by
    by_cases h : t.value = i
    · subst h; exact gen_le _ _ (measurableSet_gen_treeWithin_eq t ⊥)
    · rw [setOf_treeWithin_eq_empty h]
      exact .empty
  have hdisj : Pairwise (Function.onFun Disjoint fun t : RoseTree ι ↦
      {ω : Draws ι | ∃ n, treeWithin ω n ⊥ i = some t}) := fun t t' h ↦
    Set.disjoint_left.2 fun ω hω hω' ↦ by
      obtain ⟨n, hn⟩ := hω
      obtain ⟨n', hn'⟩ := hω'
      exact h <| Option.some.inj <| (treeWithin_mono (le_max_left n n') hn).symm.trans
        (treeWithin_mono (le_max_right n n') hn')
  rw [law, ofFunOfCountable_apply, Measure.sum_apply _ .univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← measure_iUnion hdisj hmeas]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Option.isSome_iff_exists]
  exact exists_comm

theorem law_univ_le_one (i : ι) : law ξ i Set.univ ≤ 1 :=
  (law_apply_univ ξ i).trans_le prob_le_one

/-- The extinction probability of an individual of type `i` is the total mass of the law on finite
family trees. -/
noncomputable def extinctionProb (i : ι) : ℝ≥0∞ := law ξ i Set.univ

omit [MeasurableSingletonClass ι] in
theorem draws_exists_isSome_treeWithin (hξ : ∀ i, ξ i Set.univ ≤ 1) (u : TreePath) (i : ι) :
    draws ξ {ω | ∃ n, (treeWithin ω n u i).isSome} = ⨆ n, extinctWithin ξ n i := by
  rw [Set.ofPred_exists, Monotone.measure_iUnion
    (s := fun n ↦ {ω : Draws ι | (treeWithin ω n u i).isSome})
    fun _ _ h _ hω ↦ isSome_treeWithin_mono h hω]
  exact iSup_congr fun n ↦ draws_isSome_treeWithin ξ hξ n u i

/-- The extinction probability is the limit of the probabilities of extinction within `n`
generations. -/
theorem extinctionProb_eq_iSup (i : ι) : extinctionProb ξ i = ⨆ n, extinctWithin ξ n i := by
  rw [extinctionProb, law_apply_univ, Set.ofPred_exists, Monotone.measure_iUnion
    (s := fun n ↦ {ω : Draws ι | (treeWithin ω n ⊥ i).isSome})
    fun _ _ h _ hω ↦ isSome_treeWithin_mono h hω]
  rfl

/-- The extinction probabilities are a fixed point of the offspring generating function: a family
tree is finite exactly when the family trees of all the offspring are. -/
theorem extinctionProb_eq_lintegral (hξ : ∀ i, ξ i Set.univ ≤ 1) (i : ι) :
    extinctionProb ξ i = ∫⁻ js, (js.map (extinctionProb ξ)).prod ∂ξ i := by
  rw [extinctionProb, law_apply_univ, draws_eq_lintegral ξ hξ
    (B := {ω : Draws ι | ∃ n, (treeWithin ω n ⊥ i).isSome})
    (A := fun k j ↦ {ω : Draws ι | ∃ n, (treeWithin ω n ((⊥ : TreePath).child k) j).isSome})
    (fun k j ↦ measurableSet_gen_exists_isSome _ j) fun ω ↦ exists_isSome_treeWithin ω ⊥ i]
  refine lintegral_congr fun js ↦ congrArg List.prod ?_
  rw [← map_zipIdx_eq_map (extinctionProb ξ) js]
  exact List.map_congr_left fun p _ ↦
    (draws_exists_isSome_treeWithin ξ hξ _ _).trans (extinctionProb_eq_iSup ξ _).symm

/-! ### The mean offspring -/

/-- The mean kernel of the process: the expected number of offspring of each type. -/
noncomputable def mean : Kernel ι ι :=
  ofFunOfCountable fun i ↦ (ξ i).bind fun js ↦ (js.map Measure.dirac).sum

theorem lintegral_mean (f : ι → ℝ≥0∞) (i : ι) :
    ∫⁻ j, f j ∂mean ξ i = ∫⁻ js, (js.map f).sum ∂ξ i := by
  show ∫⁻ j, f j ∂(ξ i).bind _ = _
  rw [Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  simp only [lintegral_listSum_measure, List.map_map, Function.comp_def, lintegral_dirac]

variable {ξ}

/-- Independent events of probabilities `f a` fail jointly with probability at most the sum of
bounds `g a` on their failure probabilities. -/
private theorem one_le_prod_add_sum {α : Type*} {f g : α → ℝ≥0∞} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ 1) → (∀ a ∈ l, 1 ≤ f a + g a) →
      1 ≤ (l.map f).prod + (l.map g).sum
  | [], _, _ => by simp
  | a :: l, hf, hfg => by
    have ih := one_le_prod_add_sum (l := l) (fun b hb ↦ hf b (.tail _ hb))
      fun b hb ↦ hfg b (.tail _ hb)
    calc 1 ≤ f a + g a := hfg a (.head _)
      _ ≤ f a * ((l.map f).prod + (l.map g).sum) + g a := by
        gcongr; exact le_mul_of_one_le_right' ih
      _ ≤ f a * (l.map f).prod + (l.map g).sum + g a := by
        rw [mul_add]; gcongr; exact mul_le_of_le_one_left' (hf a (.head _))
      _ = ((a :: l).map f).prod + ((a :: l).map g).sum := by
        rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons, add_assoc,
          add_comm (List.sum _)]

/-- The survival probability is subharmonic for the mean kernel: an individual whose family
survives has an offspring whose family survives. -/
theorem one_sub_extinctionProb_le_lintegral_mean (hξ : ∀ i, ξ i Set.univ ≤ 1) {i : ι}
    (hi : ξ i Set.univ = 1) :
    1 - extinctionProb ξ i ≤ ∫⁻ j, 1 - extinctionProb ξ j ∂mean ξ i := by
  have he : ∀ j, extinctionProb ξ j ≤ 1 := law_univ_le_one ξ
  refine (ENNReal.add_le_add_iff_left (ne_top_of_le_ne_top ENNReal.one_ne_top (he i))).mp ?_
  rw [add_tsub_cancel_of_le (he i), lintegral_mean, extinctionProb_eq_lintegral ξ hξ i,
    ← lintegral_add_left .of_discrete]
  calc 1 = ∫⁻ _, 1 ∂ξ i := by rw [lintegral_one, hi]
    _ ≤ _ := lintegral_mono fun js ↦ one_le_prod_add_sum (fun j _ ↦ he j) fun j _ ↦
      (add_tsub_cancel_of_le (he j)).ge

/-- **A finite excessive measure forces extinction.** If a finite measure `ν` on types dominates
`ρ` together with the mean offspring of `ν`, as the expected numbers of individuals of each type
in a family founded from `ρ` do when they are finite, then a family founded at `ρ`-almost every
type is finite almost surely. -/
theorem ae_extinctionProb_eq_one (hξ : ∀ i, ξ i Set.univ ≤ 1) {ν ρ : Measure ι}
    [IsFiniteMeasure ν] (hν : ∀ᵐ i ∂ν, ξ i Set.univ = 1) (h : ρ + mean ξ ∘ₘ ν ≤ ν) :
    ∀ᵐ i ∂ρ, extinctionProb ξ i = 1 := by
  have he : ∀ j, extinctionProb ξ j ≤ 1 := law_univ_le_one ξ
  have hsub : ∫⁻ i, 1 - extinctionProb ξ i ∂ν ≤ ∫⁻ i, 1 - extinctionProb ξ i ∂(mean ξ ∘ₘ ν) := by
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) Measurable.of_discrete.aemeasurable]
    exact lintegral_mono_ae (hν.mono fun i hi ↦ one_sub_extinctionProb_le_lintegral_mean hξ hi)
  have hfin : ∫⁻ i, 1 - extinctionProb ξ i ∂(mean ξ ∘ₘ ν) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top ν Set.univ) <|
      (lintegral_mono' ((Measure.le_add_left le_rfl).trans h) fun _ ↦ tsub_le_self).trans_eq
        lintegral_one
  have hsum : ∫⁻ i, 1 - extinctionProb ξ i ∂ρ + ∫⁻ i, 1 - extinctionProb ξ i ∂(mean ξ ∘ₘ ν) ≤
      ∫⁻ i, 1 - extinctionProb ξ i ∂ν := by
    rw [← lintegral_add_measure]
    exact lintegral_mono' h le_rfl
  have h0 : ∫⁻ i, 1 - extinctionProb ξ i ∂ρ = 0 :=
    le_zero_iff.mp <| (ENNReal.add_le_add_iff_right hfin).mp <| by
      rw [zero_add]; exact hsum.trans hsub
  filter_upwards [(lintegral_eq_zero_iff .of_discrete).mp h0] with i hi
  exact le_antisymm (he i) (tsub_eq_zero_iff_le.mp hi)

end ProbabilityTheory.GaltonWatson
