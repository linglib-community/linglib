/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Encodable
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.MeasureTheory.Constructions.List
public import Mathlib.Order.Iterate
public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Multitype Galton–Watson processes

A multitype Galton–Watson process with types `ι` is an offspring kernel `ξ : Kernel ι (List ι)`:
an individual of type `i` has offspring drawn from `ξ i`, an ordered list of types, each of which
founds an independent copy of the process. The family tree of an individual is the plane tree of
[neveu-1986], a `RoseTree ι`; its law on finite trees is the least fixed point of the
one-generation operator on the Giry monad, and the missing mass is the probability of surviving
forever.

A probabilistic context-free grammar is the instance whose types are the symbols: a terminal has
no offspring, and a nonterminal's offspring is the right-hand side of a rule chosen with its
weight; see `PCFG.galtonWatson`.

## Main definitions

* `GaltonWatson.PartialTree`: family trees with holes, the states of the generation chain.
* `GaltonWatson.fill`: the kernel filling the holes of a partial tree with independent draws
  from a family of laws, and `GaltonWatson.generation`: the kernel expanding every hole by one
  generation.
* `GaltonWatson.expand`: one generation from a single hole followed by filling, and
  `GaltonWatson.law`: its least fixed point, the law of the finite family tree at each type.
* `GaltonWatson.weight`: the probability of a finite family tree, the product over its nodes of
  the offspring probability there.
* `GaltonWatson.extinctionProb`: the total mass of `law`, the probability that the family tree
  is finite.
* `GaltonWatson.chainKernel`, `GaltonWatson.trajectory`: with Markov offspring, the generation
  chain in Ionescu–Tulcea form and, through `ProbabilityTheory.Kernel.traj`, the law of its
  whole trajectory.

## Main results

* `GaltonWatson.law_eq_iSup_iterate`: the law is the supremum of the Kleene iterates of
  `expand` from the zero kernel.
* `GaltonWatson.law_singleton`: a finite tree rooted at type `i` has probability `weight` under
  the law at `i`, and trees rooted elsewhere have probability `0`.
* `GaltonWatson.law_univ_le_one`: with sub-probability offspring the law is a sub-probability
  kernel.
* `GaltonWatson.fill_expand`: filling with one more generation is one generation followed by
  filling, so `GaltonWatson.fill_iterate` identifies the Kleene iterates with the completed part
  of the generation chain and `GaltonWatson.law_eq_iSup_generation` expresses the law as their
  supremum.
* `GaltonWatson.trajectory_map_eval`: at time `n` the trajectory is distributed as `n`
  generations, so the Kleene iterates are the marginals of the trajectory measure.

## Implementation notes

Trees and lists carry the discrete σ-algebra `⊤`, so every function out of them is measurable
and, with `ι` countable, every measure on them is s-finite and every kernel between them is an
s-finite kernel; Fubini then needs no finiteness hypotheses. Partial trees are
`RoseTree (ι ⊕ ι)`, a hole of type `i` being a leaf `Sum.inl i` and an expanded individual a node
`Sum.inr i`. The offspring kernel is not required to be Markov: sub-probability offspring model
killing, and the grammar instance produces the zero measure at a nonterminal no rule expands. The
extinction probability is the least fixed point of the offspring generating function and equals
one exactly when the mean matrix is subcritical or critical ([athreya-ney-1972]); that theorem is
not proved here.

## References

* [neveu-1986]
* [athreya-ney-1972]
-/

@[expose] public section

open MeasureTheory OmegaCompletePartialOrder ProbabilityTheory Kernel Finset Preorder RoseTree
open scoped ENNReal

instance {α : Type*} : MeasurableSpace (RoseTree α) := ⊤

namespace ProbabilityTheory.GaltonWatson

variable {ι : Type*} [MeasurableSpace ι]

/-- In a partial family tree a leaf `Sum.inl i` is a hole of type `i`, yet to be expanded, and a
node `Sum.inr i` is an individual of type `i` whose offspring is known. -/
abbrev PartialTree (ι : Type*) := RoseTree (ι ⊕ ι)

/-- The hole of type `i`. -/
abbrev hole (i : ι) : PartialTree ι := leaf (.inl i)

/-! ### Filling the holes -/

section Fill

variable (κ : Kernel ι (RoseTree ι))

/-- Fill the holes of a partial tree with independent draws from the laws `κ`. -/
noncomputable def fill : Kernel (PartialTree ι) (RoseTree ι) :=
  ⟨fold fun s μs => match s with
    | .inl i => κ i
    | .inr i => (Measure.listProd μs).map (node i), .of_discrete⟩

/-- Fill the holes of a list of partial trees independently. -/
noncomputable def fillList : Kernel (List (PartialTree ι)) (List (RoseTree ι)) :=
  ⟨fun ss => Measure.listProd (ss.map (fill κ)), .of_discrete⟩

@[simp] theorem fill_inl (i : ι) (cs : List (PartialTree ι)) : fill κ (node (.inl i) cs) = κ i := by
  simp only [fill, coe_mk, fold_node]

@[simp] theorem fill_hole (i : ι) : fill κ (hole i) = κ i := fill_inl κ i []

theorem fill_inr (i : ι) (cs : List (PartialTree ι)) :
    fill κ (node (.inr i) cs) = (fillList κ cs).map (node i) := by
  simp only [fill, fillList, coe_mk, fold_node]

@[simp] theorem fillList_apply (ss : List (PartialTree ι)) :
    fillList κ ss = Measure.listProd (ss.map (fill κ)) := rfl

variable {κ} [Countable ι]

theorem fill_univ_le_one (hκ : ∀ i, κ i Set.univ ≤ 1) (s : PartialTree ι) :
    fill κ s Set.univ ≤ 1 := by
  induction s using RoseTree.rec' with
  | node s cs ih =>
    cases s with
    | inl i => rw [fill_inl]; exact hκ i
    | inr i =>
      rw [fill_inr, Measure.map_apply .of_discrete .univ, Set.preimage_univ, fillList_apply]
      exact Measure.listProd_univ_le_one fun μ hμ => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hμ
        exact ih c hc

omit [Countable ι] in
theorem isProbabilityMeasure_fill [IsMarkovKernel κ] (s : PartialTree ι) :
    IsProbabilityMeasure (fill κ s) := by
  induction s using RoseTree.rec' with
  | node s cs ih =>
    cases s with
    | inl i => rw [fill_inl]; infer_instance
    | inr i =>
      have := Measure.isProbabilityMeasure_listProd fun μ hμ => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hμ
        exact ih c hc
      rw [fill_inr, fillList_apply]
      infer_instance

instance [IsMarkovKernel κ] : IsMarkovKernel (fill κ) := ⟨isProbabilityMeasure_fill⟩

instance [IsMarkovKernel κ] : IsMarkovKernel (fillList κ) :=
  ⟨fun ss => Measure.isProbabilityMeasure_listProd fun μ hμ => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hμ
    exact isProbabilityMeasure_fill c⟩

theorem fillList_map_hole_singleton_of_ne
    (hκ : ∀ i (c : RoseTree ι), c.value ≠ i → κ i {c} = 0) :
    ∀ (js : List ι) (cs : List (RoseTree ι)), cs.map value ≠ js →
      fillList κ (js.map hole) {cs} = 0
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => by simp
  | _ :: _, [], _ => by simp
  | j :: rest, c :: cs, h => by
    rw [fillList_apply, List.map_cons, List.map_cons, Measure.listProd_cons_singleton_cons,
      fill_hole]
    by_cases hc : c.value = j
    · simp only [List.map_cons, hc, ne_eq, List.cons.injEq, true_and] at h
      rw [← fillList_apply, fillList_map_hole_singleton_of_ne hκ rest cs h, mul_zero]
    · rw [hκ j c hc, zero_mul]

end Fill

/-! ### One generation -/

section Generation

variable (ξ : Kernel ι (List ι))

/-- In one synchronous generation every hole draws its offspring and becomes a node whose
children are fresh holes. -/
noncomputable def generation : Kernel (PartialTree ι) (PartialTree ι) :=
  ⟨fold fun s μs => match s with
    | .inl i => (ξ i).map fun js => node (.inr i) (js.map hole)
    | .inr i => (Measure.listProd μs).map (node (.inr i)), .of_discrete⟩

/-- One synchronous generation on a list of partial trees. -/
noncomputable def generationList : Kernel (List (PartialTree ι)) (List (PartialTree ι)) :=
  ⟨fun ss => Measure.listProd (ss.map (generation ξ)), .of_discrete⟩

@[simp] theorem generation_inl (i : ι) (cs : List (PartialTree ι)) :
    generation ξ (node (.inl i) cs) = (ξ i).map fun js => node (.inr i) (js.map hole) := by
  simp only [generation, coe_mk, fold_node]

@[simp] theorem generation_hole (i : ι) :
    generation ξ (hole i) = (ξ i).map fun js => node (.inr i) (js.map hole) :=
  generation_inl ξ i []

theorem generation_inr (i : ι) (cs : List (PartialTree ι)) :
    generation ξ (node (.inr i) cs) = (generationList ξ cs).map (node (.inr i)) := by
  simp only [generation, generationList, coe_mk, fold_node]

@[simp] theorem generationList_apply (ss : List (PartialTree ι)) :
    generationList ξ ss = Measure.listProd (ss.map (generation ξ)) := rfl

variable [Countable ι]

omit [Countable ι] in
theorem isProbabilityMeasure_generation [IsMarkovKernel ξ] (s : PartialTree ι) :
    IsProbabilityMeasure (generation ξ s) := by
  induction s using RoseTree.rec' with
  | node s cs ih =>
    cases s with
    | inl i =>
      rw [generation_inl]
      infer_instance
    | inr i =>
      have := Measure.isProbabilityMeasure_listProd fun μ hμ => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hμ
        exact ih c hc
      rw [generation_inr, generationList_apply]
      infer_instance

instance [IsMarkovKernel ξ] : IsMarkovKernel (generation ξ) := ⟨isProbabilityMeasure_generation ξ⟩

instance [IsMarkovKernel ξ] : IsMarkovKernel (generationList ξ) :=
  ⟨fun ss => Measure.isProbabilityMeasure_listProd fun μ hμ => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hμ
    exact isProbabilityMeasure_generation ξ c⟩

theorem fillList_comp_generationList {κ : Kernel ι (RoseTree ι)} (ss : List (PartialTree ι)) :
    fillList κ ∘ₘ generationList ξ ss =
      Measure.listProd (ss.map fun s => fill κ ∘ₘ generation ξ s) := by
  induction ss with
  | nil =>
    rw [generationList_apply, List.map_nil, Measure.listProd_nil,
      Measure.dirac_bind (Kernel.measurable _), fillList_apply, List.map_nil, List.map_nil,
      Measure.listProd_nil]
  | cons s ss ih =>
    rw [List.map_cons, Measure.listProd_cons, ← ih, generationList_apply, List.map_cons,
      Measure.listProd_cons, ← generationList_apply, ← Measure.parallelComp_comp_prod,
      Measure.map_comp _ _ .of_discrete,
      Measure.bind_map Measurable.of_discrete.aemeasurable (Kernel.measurable _).aemeasurable]
    congr 1
    funext ⟨s', ss'⟩
    rw [Function.uncurry_apply_pair, fillList_apply, List.map_cons,
      Measure.listProd_cons, ← fillList_apply, Kernel.map_apply _ .of_discrete, parallelComp_apply]

variable [MeasurableSingletonClass ι]

/-- In one generation from a type `i`, a single hole of type `i` draws its offspring, and each
type among them grows a family tree with law `κ`. -/
noncomputable def expand (κ : Kernel ι (RoseTree ι)) : Kernel ι (RoseTree ι) :=
  (fill κ ∘ₖ generation ξ).comap hole .of_discrete

variable {ξ} {κ : Kernel ι (RoseTree ι)}

@[simp]
theorem expand_apply (i : ι) : expand ξ κ i = fill κ ∘ₘ generation ξ (hole i) := by
  rw [expand, comap_apply, comp_apply]

instance [IsMarkovKernel ξ] [IsMarkovKernel κ] : IsMarkovKernel (expand ξ κ) := by
  rw [expand]; infer_instance

theorem expand_apply' (i : ι) (s : Set (RoseTree ι)) :
    expand ξ κ i s = ∫⁻ js, fillList κ (js.map hole) (node i ⁻¹' s) ∂ξ i := by
  rw [expand_apply, Measure.bind_apply .of_discrete (Kernel.aemeasurable _), generation_hole,
    lintegral_map (Kernel.measurable_coe _ .of_discrete) .of_discrete]
  simp_rw [fill_inr, Measure.map_apply .of_discrete .of_discrete]

theorem fill_expand_apply (s : PartialTree ι) : fill (expand ξ κ) s = fill κ ∘ₘ generation ξ s := by
  induction s using RoseTree.rec' with
  | node s cs ih =>
    cases s with
    | inl i => rw [fill_inl, expand_apply, generation_hole, generation_inl]
    | inr i =>
      rw [fill_inr, fillList_apply, List.map_congr_left ih, ← fillList_comp_generationList,
        generation_inr,
        Measure.map_bind (Kernel.measurable _).aemeasurable Measurable.of_discrete.aemeasurable,
        Measure.bind_map Measurable.of_discrete.aemeasurable (Kernel.measurable _).aemeasurable]
      congr 1
      funext a
      rw [fill_inr]

/-- Filling with one more generation is one generation followed by filling. -/
theorem fill_expand : fill (expand ξ κ) = fill κ ∘ₖ generation ξ :=
  Kernel.ext fill_expand_apply

end Generation

/-! ### The weight of a finite family tree -/

section Weight

variable (ξ : Kernel ι (List ι))

/-- The probability of a finite family tree is the product over its nodes of the offspring
probability of the list of types below that node. -/
noncomputable def weight (t : RoseTree ι) : ℝ≥0∞ := (t.localTrees.map fun p => ξ p.1 {p.2}).prod

theorem weight_node (i : ι) (cs : List (RoseTree ι)) :
    weight ξ (node i cs) = ξ i {cs.map value} * (cs.map (weight ξ)).prod := by
  simp only [weight, localTrees_node, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_map, Function.comp_def]
  rfl

end Weight

/-! ### The law of the family tree -/

section Law

variable (ξ : Kernel ι (List ι)) [Countable ι] [MeasurableSingletonClass ι]

theorem ωScottContinuous_fill (s : PartialTree ι) :
    ωScottContinuous fun κ : ι → Measure (RoseTree ι) => fill (ofFunOfCountable κ) s := by
  induction s using RoseTree.rec' with
  | node s cs ih =>
    cases s with
    | inl i => exact ωScottContinuous.apply i
    | inr i =>
      simp only [fill_inr, fillList_apply]
      exact Measure.ωScottContinuous_map
        (Measure.ωScottContinuous_listProd (F := fun c κ => fill (ofFunOfCountable κ) c) ih)
        .of_discrete

theorem ωScottContinuous_expand :
    ωScottContinuous fun κ : ι → Measure (RoseTree ι) => ⇑(expand ξ (ofFunOfCountable κ)) :=
  ωScottContinuous.of_apply₂ fun i => by
    simp only [expand_apply]
    exact Measure.ωScottContinuous_bind_right (fun s => ωScottContinuous_fill s) fun _ =>
      Kernel.measurable _

/-- The generation operator on families of laws indexed by type, as an order homomorphism. -/
noncomputable def expandHom : (ι → Measure (RoseTree ι)) →o (ι → Measure (RoseTree ι)) :=
  ⟨fun κ => ⇑(expand ξ (ofFunOfCountable κ)), (ωScottContinuous_expand ξ).monotone⟩

/-- The law of the family tree of an individual of each type, on finite trees, is the least fixed
point of the generation operator. Its total mass is the extinction probability. -/
noncomputable def law : Kernel ι (RoseTree ι) := ofFunOfCountable (expandHom ξ).lfp

theorem expand_law : expand ξ (law ξ) = law ξ :=
  Kernel.ext fun i => congrFun (expandHom ξ).map_lfp i

theorem coe_iterate_expand : ∀ n : ℕ, ⇑((expand ξ)^[n] 0) = (expandHom ξ)^[n] ⊥
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← coe_iterate_expand n]
    rfl

/-- The law is the supremum of the Kleene iterates of `expand` from the zero kernel. -/
theorem law_eq_iSup_iterate : ⇑(law ξ) = ⨆ n, ⇑((expand ξ)^[n] 0) := by
  simp_rw [coe_iterate_expand]
  exact OrderHom.lfp_eq_iSup_iterate _ fun c => by
    show ⇑(expand ξ (ofFunOfCountable (⨆ n, c n))) = ⨆ n, ⇑(expand ξ (ofFunOfCountable (c n)))
    rw [← Pi.ωSup_eq_iSup (L := fun _ => Measure (RoseTree ι)) c,
      (ωScottContinuous_expand ξ).map_ωSup, Pi.ωSup_eq_iSup]
    rfl

theorem monotone_iterate_expand : Monotone fun n => ⇑((expand ξ)^[n] 0) := by
  simp_rw [coe_iterate_expand]
  exact (expandHom ξ).monotone.monotone_iterate_of_le_map bot_le

theorem law_singleton_of_ne {t : RoseTree ι} {i : ι} (h : t.value ≠ i) : law ξ i {t} = 0 := by
  rw [← expand_law, expand_apply']
  have : node i ⁻¹' ({t} : Set (RoseTree ι)) = ∅ := by
    ext cs
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact h rfl
  simp [this]

theorem fillList_law_map_hole_singleton {cs : List (RoseTree ι)}
    (h : ∀ c ∈ cs, law ξ c.value {c} = weight ξ c) :
    fillList (law ξ) ((cs.map value).map hole) {cs} = (cs.map (weight ξ)).prod := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.map_cons, fillList_apply, List.map_cons,
      Measure.listProd_cons_singleton_cons, fill_hole, h c (List.mem_cons_self ..), List.map_cons,
      List.prod_cons, ← fillList_apply, ih fun d hd => h d (List.mem_cons_of_mem _ hd)]

theorem law_singleton_value (t : RoseTree ι) : law ξ t.value {t} = weight ξ t := by
  induction t using RoseTree.rec' with
  | node i cs ih =>
    rw [value_node, ← expand_law, expand_apply', weight_node]
    have hpre : node i ⁻¹' ({node i cs} : Set (RoseTree ι)) = {cs} := by ext; simp
    have hind : (fun js => fillList (law ξ) (js.map hole) {cs}) =
        ({cs.map value} : Set (List ι)).indicator fun _ => (cs.map (weight ξ)).prod := by
      funext js
      by_cases hs : cs.map value = js
      · subst hs
        rw [fillList_law_map_hole_singleton ξ ih, Set.indicator_of_mem (Set.mem_singleton _)]
      · rw [fillList_map_hole_singleton_of_ne (fun _ _ => law_singleton_of_ne ξ) _ _ hs,
          Set.indicator_of_notMem (by simpa using Ne.symm hs)]
    rw [hpre, hind, lintegral_indicator_const .of_discrete, mul_comm]

theorem law_singleton_node (i : ι) (cs : List (RoseTree ι)) :
    law ξ i {node i cs} = weight ξ (node i cs) :=
  law_singleton_value ξ (node i cs)

open scoped Classical in
/-- Under the law at `i`, a finite tree has probability `weight` when its root has type `i`
and `0` otherwise. -/
theorem law_singleton (t : RoseTree ι) (i : ι) :
    law ξ i {t} = if t.value = i then weight ξ t else 0 := by
  split_ifs with h
  · exact h ▸ law_singleton_value ξ t
  · exact law_singleton_of_ne ξ h

/-! ### Extinction -/

variable {ξ}

theorem expand_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) {κ : Kernel ι (RoseTree ι)}
    (hκ : ∀ i, κ i Set.univ ≤ 1) (i : ι) : expand ξ κ i Set.univ ≤ 1 := by
  rw [expand_apply, Measure.bind_apply .univ (Kernel.aemeasurable _)]
  calc ∫⁻ s, fill κ s Set.univ ∂generation ξ (hole i)
      ≤ ∫⁻ _, 1 ∂generation ξ (hole i) := lintegral_mono fun s => fill_univ_le_one hκ s
    _ = ξ i Set.univ := by
      rw [lintegral_one, generation_hole, Measure.map_apply .of_discrete .univ, Set.preimage_univ]
    _ ≤ 1 := hξ i

theorem iterate_expand_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) :
    ∀ (n : ℕ) (i : ι), ((expand ξ)^[n] 0) i Set.univ ≤ 1
  | 0, _ => by simp
  | n + 1, i => by
    rw [Function.iterate_succ_apply']
    exact expand_univ_le_one hξ (iterate_expand_univ_le_one hξ n) i

/-- With sub-probability offspring, the law on finite family trees is a sub-probability kernel;
the missing mass is the probability of survival forever. -/
theorem law_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) (i : ι) : law ξ i Set.univ ≤ 1 := by
  rw [law_eq_iSup_iterate, iSup_apply,
    Measure.iSup_apply_of_monotone (fun m n h => monotone_iterate_expand ξ h i) .univ]
  exact iSup_le fun n => iterate_expand_univ_le_one hξ n i

variable (ξ)

/-- The extinction probability of an individual of type `i` is the total mass of the law on finite
family trees, which for Markov offspring is the probability that the family tree is finite. -/
noncomputable def extinctionProb (i : ι) : ℝ≥0∞ := law ξ i Set.univ

/-! ### Generations -/

/-- The `n`-th Kleene iterate fills a partial tree exactly as `n` synchronous generations do,
followed by the completion of what remains. -/
theorem fill_iterate : ∀ n : ℕ, fill ((expand ξ)^[n] 0) = fill 0 ∘ₖ (generation ξ ^ n)
  | 0 => (comp_id _).symm
  | n + 1 => by
    rw [Function.iterate_succ_apply', fill_expand, fill_iterate n, comp_assoc, pow_succ]
    rfl

/-- The law of the family tree at type `i` is the supremum over `n` of the completed part of
`n` synchronous generations from a single hole of type `i`. -/
theorem law_eq_iSup_generation (i : ι) :
    law ξ i = ⨆ n, fill 0 ∘ₘ (generation ξ ^ n) (hole i) := by
  rw [law_eq_iSup_iterate, iSup_apply]
  exact iSup_congr fun n => by rw [← fill_hole, fill_iterate, comp_apply]

end Law

/-! ### The generation chain as a Markov chain -/

section Chain

variable (ξ : Kernel ι (List ι)) [Countable ι]

/-- In the Ionescu–Tulcea form of the generation chain, the state at time `n + 1` depends on the
trajectory up to time `n` only through its last coordinate. -/
noncomputable def chainKernel (n : ℕ) :
    Kernel (Π i : Iic n, (fun _ : ℕ => PartialTree ι) i) ((fun _ : ℕ => PartialTree ι) (n + 1)) :=
  (generation ξ).comap (fun x => x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

variable [IsMarkovKernel ξ]

instance (n : ℕ) : IsMarkovKernel (chainKernel ξ n) := IsMarkovKernel.comap _ _

/-- The Ionescu–Tulcea trajectory kernel of the generation chain. -/
noncomputable def chainTraj (n : ℕ) :
    Kernel (Π i : Iic n, (fun _ : ℕ => PartialTree ι) i) (ℕ → PartialTree ι) :=
  traj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) n

/-- The law of the whole trajectory of generations started at a partial tree. -/
noncomputable def trajectory (s : PartialTree ι) : Measure (ℕ → PartialTree ι) :=
  chainTraj ξ 0 fun _ => s

instance (s : PartialTree ι) : IsProbabilityMeasure (trajectory ξ s) :=
  inferInstanceAs (IsProbabilityMeasure
    (traj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) 0 _))

/-- At time `n` the generation chain is distributed as `n` synchronous generations. -/
theorem trajectory_map_eval (s : PartialTree ι) :
    ∀ n : ℕ, (trajectory ξ s).map (fun ω => ω n) = (generation ξ ^ n) s
  | 0 => by
    have h := traj_map_frestrictLe_apply (X := fun _ : ℕ => PartialTree ι) (κ := chainKernel ξ)
      0 0 (fun _ => s)
    rw [partialTraj_self, Kernel.id_apply] at h
    show (trajectory ξ s).map (fun ω => ω 0) = Measure.dirac s
    have hm : (trajectory ξ s).map (fun ω => ω 0) = ((trajectory ξ s).map (frestrictLe 0)).map
        (fun x : Π i : Iic 0, (fun _ : ℕ => PartialTree ι) i => x ⟨0, mem_Iic.2 le_rfl⟩) :=
      (Measure.map_map (μ := trajectory ξ s) (measurable_pi_apply (⟨0, mem_Iic.2 le_rfl⟩ : Iic 0))
        (measurable_frestrictLe 0)).symm
    rw [hm, show (trajectory ξ s).map (frestrictLe 0) = Measure.dirac (fun _ => s) from h]
    exact Measure.map_dirac _
  | n + 1 => by
    have hpt : ∀ x : Π i : Iic n, (fun _ : ℕ => PartialTree ι) i,
        (traj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) n x).map (fun ω => ω (n + 1)) =
          generation ξ (x ⟨n, mem_Iic.2 le_rfl⟩) := fun x => by
      rw [← Kernel.map_apply (traj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) n)
          (measurable_pi_apply (n + 1)) x,
        map_traj_succ_self (X := fun _ : ℕ => PartialTree ι) (κ := chainKernel ξ), chainKernel,
        comap_apply]
    have hmarg : (trajectory ξ s).map (fun ω => ω n) =
        (partialTraj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) 0 n (fun _ => s)).map
          (fun x : Π i : Iic n, (fun _ : ℕ => PartialTree ι) i => x ⟨n, mem_Iic.2 le_rfl⟩) := by
      rw [← traj_map_frestrictLe_apply (X := fun _ : ℕ => PartialTree ι) (κ := chainKernel ξ) 0 n
        (fun _ => s)]
      exact (Measure.map_map (μ := trajectory ξ s)
        (measurable_pi_apply (⟨n, mem_Iic.2 le_rfl⟩ : Iic n)) (measurable_frestrictLe n)).symm
    have hcomp := traj_comp_partialTraj (X := fun _ : ℕ => PartialTree ι) (κ := chainKernel ξ)
      (Nat.zero_le n)
    calc (trajectory ξ s).map (fun ω => ω (n + 1))
        = ((partialTraj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) 0 n (fun _ => s)).bind
            (traj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) n)).map
              (fun ω => ω (n + 1)) := by
          rw [trajectory, chainTraj, ← hcomp, comp_apply]
      _ = (partialTraj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) 0 n (fun _ => s)).bind
            fun x => generation ξ (x ⟨n, mem_Iic.2 le_rfl⟩) := by
          rw [Measure.map_bind (Kernel.measurable _).aemeasurable
            (measurable_pi_apply _).aemeasurable]
          simp_rw [hpt]
      _ = ((partialTraj (X := fun _ : ℕ => PartialTree ι) (chainKernel ξ) 0 n (fun _ => s)).map
            (fun x : Π i : Iic n, (fun _ : ℕ => PartialTree ι) i => x ⟨n, mem_Iic.2 le_rfl⟩)).bind
              (generation ξ) :=
          (Measure.bind_map (measurable_pi_apply _).aemeasurable
            (Kernel.measurable _).aemeasurable).symm
      _ = generation ξ ∘ₘ (generation ξ ^ n) s := by rw [← hmarg, trajectory_map_eval s n]
      _ = (generation ξ ^ (n + 1)) s := by rw [pow_succ']; rfl

end Chain

end ProbabilityTheory.GaltonWatson
