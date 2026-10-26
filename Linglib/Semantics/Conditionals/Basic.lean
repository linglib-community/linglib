module

public import Mathlib.Data.Set.Basic
public import Linglib.Logic.Nonmonotonic.Preferential
public import Linglib.Semantics.Modality.OrderingSemantics
public import Linglib.Logic.Modal.Defs

/-!
# Conditional operators

This file defines conditional operators on propositions, taken as sets of worlds. Most theories
of the conditional derive it from a domain of antecedent-worlds: *if p, q* is true when `q` holds
throughout the domain that `p` picks out from the evaluation point. The theories differ in the
domain, which is the accessible antecedent-worlds for the strict conditional and the closest
accessible antecedent-worlds under the Limit Assumption. Lewis's variably strict conditional
needs no such domain: *if p, q* is true when `q` holds at every accessible `p`-world from some
point on as the `p`-worlds come closer, and it reduces to the closest-world conditional exactly
where the Limit Assumption holds.

## Main definitions

* `ofDomain`: the conditional quantifying over a domain of antecedent-worlds.
* `materialImp`, `strictImp`: the material and strict conditionals.
* `variablyStrictImp`: Lewis's variably strict conditional over an accessibility assignment and a
  family of preorders.
* `IsCentered`: strong centering of a family of preorders.
* `closestImp`: the conditional of the minimal antecedent-worlds.
* `orderingImp`: the conditional over the best accessible antecedent-worlds under a preorder.
* `might`: the *might* counterfactual of a *would* conditional.

## Main results

* `ofDomain_eq_core`: the conditional over a domain is necessity along the relation of its domain.
* `variablyStrictImp_subset_orderingImp`, `mem_variablyStrictImp_iff_mem_orderingImp`: the
  variably strict conditional entails truth at the best accessible antecedent-worlds, and is it
  under the Limit Assumption.
* `mem_variablyStrictImp_iff_of_total`: on a total preorder it is Lewis's clause over comparative
  similarity.
* `mem_variablyStrictImp_compl_singleton`: without closest antecedent-worlds, *if p, it would not
  be v* holds for every world `v`.
* `isPreferential_variablyStrictImp`, `isRational_variablyStrictImp`: the conditional at a world
  satisfies system P on every preorder, and rational monotonicity on every total one.

## References

* [D. Lewis, *Counterfactuals* (1973)][lewis-1973b]
* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [S. Kraus, D. Lehmann and M. Magidor, *Nonmonotonic Reasoning, Preferential Models and
  Cumulative Logics* (1990)][kraus-magidor-1990]
* [D. Lehmann and M. Magidor, *What Does a Conditional Knowledge Base Entail?*
  (1992)][lehmann-magidor-1992]
* [J. P. Burgess, *Quick Completeness Proofs for Some Logics of Conditionals* (1981)][burgess-1981]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [C. Condoravdi, *Temporal Interpretation of Modals: Modals for the Present and for the Past*
  (2002)][condoravdi-2002]
* [K. von Fintel, *NPI Licensing, Strawson Entailment, and Context Dependency*
  (1999)][von-fintel-1999]
* [B. Grusdt, D. Lassiter and M. Franke, *Probabilistic Modeling of Rational Communication with
  Conditionals* (2022)][grusdt-lassiter-franke-2022]
* [T. Mizuno, *Strategies for Anderson Conditionals: Their Implications for the Typology of
  O-Marking and X-Marking* (2024)][mizuno-2024]
-/

@[expose] public section


namespace Conditional

variable {I W : Type*} {access : I → Set W} {p p' q q' : Set W} {i : I} {w : W}

/-! ### Material conditional -/

/-- The material conditional, true wherever the antecedent fails or the consequent holds.
Classical semantics keeps this meaning and derives its apparent exceptions pragmatically
([grusdt-lassiter-franke-2022]). -/
def materialImp (p q : Set W) : Set W := {w | w ∈ p → w ∈ q}

@[simp]
theorem mem_materialImp : w ∈ materialImp p q ↔ (w ∈ p → w ∈ q) := Iff.rfl

theorem contraposition : materialImp p q ⊆ materialImp qᶜ pᶜ :=
  fun _ h hq hp ↦ hq (h hp)

/-! ### Conditionals over a domain

A theory of the conditional picks out, for an evaluation point `i` and an antecedent `p`, a
domain of `p`-worlds, and *if p, q* is true at `i` iff `q` holds throughout it (`ofDomain`): the
accessible `p`-worlds for the strict conditional, the closest ones for [lewis-1973b] under the
Limit Assumption (`closestImp`), the selected one for [stalnaker-1968] (`selectionConditional`),
the best worlds of the modal base restricted by the antecedent for the restrictor analysis
([lewis-1975], [kratzer-1986]). Principles about a single antecedent are properties of its
domain: consequent monotonicity and agglomeration always hold, Conditional Excluded Middle and
distribution over a disjunctive consequent when the domain has at most one world, and modus
ponens when an antecedent-world lies in its own domain. Principles relating antecedents, such as
antecedent strengthening or reasoning by cases, depend on how the domain varies with the
antecedent. -/

section Domain

variable {D : I → Set W → Set W} {r : Set W}

/-- The conditional quantifying over the domain `D i p`, true at `i` when `q` holds at every
world of `D i p`. -/
def ofDomain (D : I → Set W → Set W) (p q : Set W) : Set I := {i | D i p ⊆ q}

@[simp]
theorem mem_ofDomain : i ∈ ofDomain D p q ↔ D i p ⊆ q := Iff.rfl

/-- The conditional over a domain is necessity along the relation sending `i` to the worlds of
its domain, `SetRel.core` of `SetRel.ofSuccessors`. -/
theorem ofDomain_eq_core : ofDomain D p q = (SetRel.ofSuccessors (D · p)).core q := rfl

theorem ofDomain_mono_right (hq : q ⊆ q') : ofDomain D p q ⊆ ofDomain D p q' :=
  fun _ h ↦ h.trans hq

theorem ofDomain_inter : ofDomain D p (q ∩ r) = ofDomain D p q ∩ ofDomain D p r :=
  Set.ext fun _ ↦ Set.subset_inter_iff

theorem ofDomain_eq_univ (h : ∀ i, D i p ⊆ q) : ofDomain D p q = Set.univ :=
  Set.eq_univ_of_forall h

/-- Antecedent strengthening holds when the domain of the stronger antecedent lies within the
domain of the weaker. -/
theorem ofDomain_anti_left (hD : ∀ i, D i p' ⊆ D i p) : ofDomain D p q ⊆ ofDomain D p' q :=
  fun i h ↦ (hD i).trans h

theorem mem_ofDomain_union (hD : D i (p ∪ p') ⊆ D i p ∪ D i p') (hp : i ∈ ofDomain D p q)
    (hp' : i ∈ ofDomain D p' q) : i ∈ ofDomain D (p ∪ p') q :=
  fun _ hv ↦ (hD hv).elim (hp ·) (hp' ·)

theorem mem_ofDomain_or (h : (D i p).Subsingleton) (hq : i ∈ ofDomain D p (q ∪ r)) :
    i ∈ ofDomain D p q ∨ i ∈ ofDomain D p r := by
  rcases h.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · exact .inl (by simp [h0])
  · simpa only [mem_ofDomain, hv, Set.singleton_subset_iff, Set.mem_union] using hq

theorem mem_ofDomain_or_compl (h : (D i p).Subsingleton) :
    i ∈ ofDomain D p q ∨ i ∈ ofDomain D p qᶜ :=
  mem_ofDomain_or h (by simp)

theorem not_mem_ofDomain_and_compl {v v' : W} (hv : v ∈ D i p) (hv' : v' ∈ D i p) (hq : v ∈ q)
    (hq' : v' ∉ q) : i ∉ ofDomain D p q ∧ i ∉ ofDomain D p qᶜ :=
  ⟨fun h ↦ hq' (h hv'), fun h ↦ h hv hq⟩

theorem forall_mem_ofDomain_or_compl_iff :
    (∀ r : Set W, i ∈ ofDomain D p r ∨ i ∈ ofDomain D p rᶜ) ↔ (D i p).Subsingleton :=
  ModalLogic.box_or_box_not_at_iff (R := SetRel.ofSuccessors (D · p))

theorem ofDomain_subset_materialImp {D : W → Set W → Set W} (hD : ∀ w ∈ p, w ∈ D w p) :
    ofDomain D p q ⊆ materialImp p q :=
  fun w h hp ↦ h (hD w hp)

theorem materialImp_eq_ofDomain : materialImp p q = ofDomain (fun w p ↦ {w} ∩ p) p q :=
  Set.ext fun _ ↦ ⟨fun h _ hv ↦
      (Set.mem_singleton_iff.1 hv.1) ▸ h ((Set.mem_singleton_iff.1 hv.1) ▸ hv.2),
    fun h hp ↦ h ⟨rfl, hp⟩⟩

end Domain

/-! ### Strict conditional -/

/-- The strict conditional over an accessibility map, true at `i` when the consequent holds at
every accessible antecedent-world. The evaluation points may differ from the worlds quantified
over, as for a historical modal base evaluated at world-time indices ([condoravdi-2002]). -/
def strictImp (access : I → Set W) (p q : Set W) : Set I :=
  ofDomain (fun i p ↦ access i ∩ p) p q

@[simp]
theorem mem_strictImp : i ∈ strictImp access p q ↔ access i ∩ p ⊆ q := Iff.rfl

theorem mem_strictImp_forall :
    i ∈ strictImp access p q ↔ ∀ w ∈ access i, w ∈ p → w ∈ q :=
  ⟨fun h _ hw hp ↦ h ⟨hw, hp⟩, fun h w hw ↦ h w hw.1 hw.2⟩

theorem strictImp_mono_right (hq : q ⊆ q') :
    strictImp access p q ⊆ strictImp access p q' :=
  ofDomain_mono_right hq

theorem strictImp_anti_left (hp : p' ⊆ p) :
    strictImp access p q ⊆ strictImp access p' q :=
  ofDomain_anti_left fun _ ↦ Set.inter_subset_inter_right _ hp

theorem strictImp_union_left :
    strictImp access (p ∪ p') q = strictImp access p q ∩ strictImp access p' q :=
  Set.ext fun _ ↦ by
    simp only [mem_strictImp, Set.inter_union_distrib_left, Set.union_subset_iff,
      Set.mem_inter_iff]

theorem mem_strictImp_of_subset (h : access i ⊆ q) :
    i ∈ strictImp access p q :=
  Set.inter_subset_left.trans h

theorem not_subset_of_mem_strictImp
    (hm : i ∈ strictImp access p q) (hq : ¬ access i ⊆ q) :
    ¬ access i ⊆ p :=
  fun hp ↦ hq (fun _ hw ↦ hm ⟨hw, hp hw⟩)

theorem strict_implies_material {R : W → Set W} (h_refl : w ∈ R w)
    (h : w ∈ strictImp R p q) : w ∈ materialImp p q :=
  fun hp ↦ h ⟨h_refl, hp⟩

/-! ### Closest worlds

Lewis requires comparative similarity to be a total preorder of the worlds for each center, each
world closer to itself than any other is (`IsCentered`). Under the Limit Assumption, that closest
antecedent-worlds exist whenever antecedent-worlds do, his clause simplifies to the consequent
holding at every closest antecedent-world (`closestImp`, [lewis-1973b] §1.4). The operators take
any family `ord : W → Preorder W` of preorders indexed by the evaluation world, the closest
antecedent-worlds being the minimal ones (`Preorder.minimals`); `closestImp` is also meaningful on
preorders that are not total. `might` is §1.5's *might* counterfactual, the dual of a *would*
conditional. -/

/-- The *might* counterfactual of a *would* conditional `op`, *not (if p, would not q)*
([lewis-1973b] §1.5). -/
def might (op : Set W → Set W → Set W) (p q : Set W) : Set W := (op p qᶜ)ᶜ

@[simp]
theorem mem_might {op : Set W → Set W → Set W} : w ∈ might op p q ↔ w ∉ op p qᶜ := Iff.rfl

instance {op : Set W → Set W → Set W} [Decidable (w ∈ op p qᶜ)] : Decidable (w ∈ might op p q) :=
  inferInstanceAs (Decidable (w ∉ _))

section Closest

variable {ord : W → Preorder W} {r : Set W}

/-- A family of preorders is strongly centered when every world is strictly below every other
world in its own preorder, [lewis-1973b]'s requirement that each world be closer to itself than
any other world is. -/
def IsCentered (ord : W → Preorder W) : Prop := ∀ w w' : W, w ≠ w' → (ord w).lt w w'

theorem IsCentered.le (hc : IsCentered ord) (w w' : W) : (ord w).le w w' := by
  let := ord w
  rcases eq_or_ne w w' with rfl | h
  exacts [le_rfl, (hc w w' h).le]

theorem IsCentered.not_le (hc : IsCentered ord) {w w' : W} (h : w ≠ w') : ¬ (ord w).le w' w :=
  let := ord w
  (hc w w' h).not_ge

theorem IsCentered.minimals_eq_singleton (hc : IsCentered ord) (hw : w ∈ p) :
    (ord w).minimals p = {w} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hw, fun u _ _ ↦ hc.le w u⟩, fun u hu ↦ ?_⟩
  by_contra hne
  exact hc.not_le (Ne.symm hne) (hu.2 hw (hc.le w u))


/-- The conditional of the closest antecedent-worlds, true when the consequent holds at every
closest antecedent-world. It is [lewis-1973b]'s simplification of the variably strict
conditional under the Limit Assumption (§1.4). -/
def closestImp (ord : W → Preorder W) (p q : Set W) : Set W :=
  ofDomain (fun w ↦ (ord w).minimals) p q

@[simp]
theorem mem_closestImp : w ∈ closestImp ord p q ↔ (ord w).minimals p ⊆ q := Iff.rfl

theorem mem_closestImp_iff_forall_filter [Fintype W] [DecidablePred (· ∈ p)] :
    w ∈ closestImp ord p q ↔ ∀ v ∈ Finset.univ.filter (· ∈ p),
      (∀ u ∈ Finset.univ.filter (· ∈ p), (ord w).le u v → (ord w).le v u) → v ∈ q := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h v hv hmin ↦ h ⟨hv, fun u hu ↦ hmin u hu⟩, fun h v hv ↦ h v hv.1 fun u hu ↦ hv.2 hu⟩

instance [Fintype W] [DecidableRel (ord w).le] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    Decidable (w ∈ closestImp ord p q) :=
  decidable_of_iff _ mem_closestImp_iff_forall_filter.symm

theorem mem_closestImp_of_closest_eq_empty (h : (ord w).minimals p = ∅) :
    w ∈ closestImp ord p q :=
  (mem_closestImp.2 (h ▸ Set.empty_subset q))

theorem closestImp_subset_materialImp (hc : IsCentered ord) :
    closestImp ord p q ⊆ materialImp p q :=
  ofDomain_subset_materialImp fun w hw ↦ ⟨hw, fun u _ _ ↦ hc.le w u⟩

theorem closestImp_eq_univ_of_subset (h : p ⊆ q) : closestImp ord p q = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ (Preorder.minimals_subset _ p).trans h

theorem mem_closestImp_union (hp : w ∈ closestImp ord p r) (hq : w ∈ closestImp ord q r) :
    w ∈ closestImp ord (p ∪ q) r :=
  fun _ hu ↦ (Preorder.minimals_union_subset hu).elim (hp ·) (hq ·)

theorem mem_closestImp_or_of_mem_union (htot : ∀ w, Std.Total (ord w).le)
    (h : w ∈ closestImp ord (p ∪ q) r) :
    w ∈ closestImp ord p r ∨ w ∈ closestImp ord q r := by
  by_contra hn
  simp only [not_or, mem_closestImp, Set.not_subset] at hn
  obtain ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩ := hn
  rw [Preorder.mem_minimals_iff_forall_le (htot _)] at hx hy
  rcases (htot w).total x y with hxy | hyx
  · refine hxr (h ((Preorder.mem_minimals_iff_forall_le (htot _)).2 ⟨.inl hx.1, ?_⟩))
    exact fun u hu ↦ hu.elim (hx.2 u) fun hu ↦ (ord w).le_trans x y u hxy (hy.2 u hu)
  · refine hyr (h ((Preorder.mem_minimals_iff_forall_le (htot _)).2 ⟨.inr hy.1, ?_⟩))
    exact fun u hu ↦ hu.elim (fun hu ↦ (ord w).le_trans y x u hyx (hx.2 u hu)) (hy.2 u)

theorem mem_might_closestImp_iff_of_closest_eq_singleton {v : W} (h : (ord w).minimals p = {v}) :
    w ∈ might (closestImp ord) p q ↔ w ∈ closestImp ord p q := by
  simp [h]

theorem mem_might_closestImp_iff_of_cem (h_nonempty : ((ord w).minimals p).Nonempty)
    (h_cem : w ∈ closestImp ord p q ∨ w ∈ closestImp ord p qᶜ) :
    w ∈ might (closestImp ord) p q ↔ w ∈ closestImp ord p q := by
  obtain ⟨v, hv⟩ := h_nonempty
  rcases h_cem with h | h
  · exact ⟨fun _ ↦ h, fun _ hn ↦ hn hv (h hv)⟩
  · exact ⟨fun hm ↦ absurd h hm, fun hq ↦ absurd (hq hv) (h hv)⟩

end Closest

/-! ### Variably strict conditionals

[lewis-1973b] interprets the counterfactual over an assignment to each world of a set of accessible
worlds and a total preorder of comparative similarity (§2.3), and a modal base and an ordering
source ([kratzer-1981]) give each evaluation point the same two items. *If p, q* is true at `i`
when `q` is a necessity of ordering semantics over the accessible `p`-worlds: every accessible
`p`-world has one at least as close all of whose accessible `p`-worlds at least as close are
`q`-worlds (`variablyStrictImp`). The clause needs neither the Limit Assumption nor a total
preorder, and on a total preorder it is §2.3's (`mem_variablyStrictImp_iff_of_total`). Under the
Limit Assumption it is truth at the best accessible antecedent-worlds (`orderingImp`), the
restrictor analysis of [lewis-1975] and [kratzer-1986]. The strict conditional is the case of the
preorder relating every two worlds (`strictImp_eq_orderingImp`), and the conditional of the
closest worlds the case in which every world is accessible (`closestImp_eq_orderingImp`). -/

section Ordering

variable {ord : I → Preorder W}

/-- The variably strict conditional, true at `i` when the consequent is a necessity over the
accessible antecedent-worlds under the preorder `ord i`. -/
def variablyStrictImp (access : I → Set W) (ord : I → Preorder W) (p q : Set W) : Set I :=
  {i | q ∈ OrderingSemantics.necessityFilter (ord i) (access i ∩ p)}

@[simp]
theorem mem_variablyStrictImp :
    i ∈ variablyStrictImp access ord p q ↔
      q ∈ OrderingSemantics.necessityFilter (ord i) (access i ∩ p) :=
  Iff.rfl

/-- On a total preorder the variably strict conditional holds when no antecedent-world is
accessible, or some accessible antecedent-world has only consequent-worlds among the accessible
antecedent-worlds at least as close ([lewis-1973b] §2.3). -/
theorem mem_variablyStrictImp_iff_of_total (htot : Std.Total (ord i).le) :
    i ∈ variablyStrictImp access ord p q ↔
      access i ∩ p = ∅ ∨ OrderingSemantics.IsGoodPossibility (ord i) (access i ∩ p) q := by
  rw [mem_variablyStrictImp]
  rcases (access i ∩ p).eq_empty_or_nonempty with h | h
  · exact iff_of_true (fun u hu ↦ absurd (h ▸ hu) (Set.notMem_empty u)) (.inl h)
  · rw [or_iff_right h.ne_empty]
    exact OrderingSemantics.mem_necessityFilter_iff_isGoodPossibility_of_total htot h

/-- The conditional over the best accessible antecedent-worlds, the minimal worlds of
`access i ∩ p` under the preorder `ord i`. -/
def orderingImp (access : I → Set W) (ord : I → Preorder W) (p q : Set W) : Set I :=
  ofDomain (fun i p ↦ (ord i).minimals (access i ∩ p)) p q

@[simp]
theorem mem_orderingImp :
    i ∈ orderingImp access ord p q ↔ (ord i).minimals (access i ∩ p) ⊆ q := Iff.rfl

theorem strictImp_eq_orderingImp : strictImp access p q = orderingImp access (fun _ ↦ ⊤) p q := by
  ext; simp [strictImp]

theorem closestImp_eq_orderingImp {ord : W → Preorder W} :
    closestImp ord p q = orderingImp (fun _ ↦ Set.univ) ord p q := by
  ext; simp

theorem variablyStrictImp_subset_orderingImp :
    variablyStrictImp access ord p q ⊆ orderingImp access ord p q :=
  fun _ hi ↦ OrderingSemantics.minimals_subset_of_mem_necessityFilter hi

/-- Under the Limit Assumption at `i`, the variably strict conditional is truth at the best
accessible antecedent-worlds ([lewis-1973b] §1.4). -/
theorem mem_variablyStrictImp_iff_mem_orderingImp
    (hlim : ∀ B : Set W, (access i ∩ B).Nonempty → ((ord i).minimals (access i ∩ B)).Nonempty) :
    i ∈ variablyStrictImp access ord p q ↔ i ∈ orderingImp access ord p q := by
  refine ⟨fun h ↦ variablyStrictImp_subset_orderingImp h, fun hi ↦ ?_⟩
  let := ord i
  refine OrderingSemantics.mem_necessityFilter_of_minimals_subset (fun h hh ↦ ?_) hi
  obtain ⟨j, ⟨hjS, hjA, hjh⟩, hmin⟩ := hlim {g ∈ p | g ≤ h} ⟨h, hh.1, hh.2, le_rfl⟩
  exact ⟨j, ⟨⟨hjS, hjA⟩, fun f hf hfj ↦ hmin ⟨hf.1, hf.2, hfj.trans hjh⟩ hfj⟩, hjh⟩

theorem variablyStrictImp_subset_materialImp {ord : W → Preorder W} {access : W → Set W}
    (hR : ∀ w, w ∈ access w) (hc : IsCentered ord) :
    variablyStrictImp access ord p q ⊆ materialImp p q := fun w h hp ↦
  let ⟨v, _, _, hvq⟩ := h w ⟨hR w, hp⟩
  hvq w ⟨hR w, hp⟩ (hc.le w v)

end Ordering

/-! ### Every world accessible -/

section Universal

variable {ord : W → Preorder W}

theorem variablyStrictImp_subset_closestImp :
    variablyStrictImp (fun _ ↦ Set.univ) ord p q ⊆ closestImp ord p q := fun _ hw ↦ by
  rw [closestImp_eq_orderingImp]
  exact variablyStrictImp_subset_orderingImp hw

/-- On a total ordering satisfying the Limit Assumption for `p`, the two conditionals coincide
([lewis-1973b] §1.4). -/
theorem closestImp_eq_variablyStrictImp (htot : ∀ w, Std.Total (ord w).le)
    (hlim : ∀ w, p.Nonempty → ((ord w).minimals p).Nonempty) :
    closestImp ord p q = variablyStrictImp (fun _ ↦ Set.univ) ord p q := by
  refine subset_antisymm (fun w hw ↦ ?_) variablyStrictImp_subset_closestImp
  rw [mem_variablyStrictImp, Set.univ_inter]
  refine OrderingSemantics.mem_necessityFilter_of_minimals_subset (fun u hu ↦ ?_) hw
  obtain ⟨v, hv⟩ := hlim w ⟨u, hu⟩
  exact ⟨v, hv, ((Preorder.mem_minimals_iff_forall_le (htot w)).1 hv).2 u hu⟩

theorem closestImp_eq_variablyStrictImp_of_finite (htot : ∀ w, Std.Total (ord w).le)
    (hp : p.Finite) :
    closestImp ord p q = variablyStrictImp (fun _ ↦ Set.univ) ord p q :=
  closestImp_eq_variablyStrictImp htot fun w ↦ (ord w).minimals_nonempty_of_finite hp

/-- Where an antecedent has no closest worlds, as for [lewis-1973b]'s line more than an inch long,
*if p, it would not be v* is true for every world `v`, since every antecedent-world has a
strictly closer one. -/
theorem mem_variablyStrictImp_compl_singleton {w : W} (h : (ord w).minimals p = ∅) (v : W) :
    w ∈ variablyStrictImp (fun _ ↦ Set.univ) ord p {v}ᶜ := by
  rw [mem_variablyStrictImp, Set.univ_inter]
  intro u hu
  by_cases hvu : v ∈ p ∧ (ord w).le v u
  · have hvm : v ∉ (ord w).minimals p := h ▸ Set.notMem_empty v
    simp only [Preorder.mem_minimals_iff, hvu.1, true_and, not_forall] at hvm
    obtain ⟨x, hx, hxv, hvx⟩ := hvm
    exact ⟨x, hx, (ord w).le_trans _ _ _ hxv hvu.2, fun y _ hyx hyv ↦ hvx (hyv ▸ hyx)⟩
  · exact ⟨u, hu, (ord w).le_refl u, fun y hy hyu hyv ↦ hvu ⟨hyv ▸ hy, hyv ▸ hyu⟩⟩

theorem notMem_might_variablyStrictImp_singleton {w : W} (h : (ord w).minimals p = ∅) (v : W) :
    w ∉ might (variablyStrictImp (fun _ ↦ Set.univ) ord) p {v} :=
  fun hm ↦ hm (mem_variablyStrictImp_compl_singleton h v)

end Universal

/-! ### The logic of the conditional at a world

At `i` the variably strict conditional relates each antecedent to the necessities over its
accessible worlds, so it satisfies the rules of system P ([kraus-magidor-1990]) on every preorder,
with no Limit Assumption ([burgess-1981]), and rational monotonicity ([lehmann-magidor-1992]) on
every total one, as [lewis-1973b] requires. The conditional of the closest worlds is the relation
of the minimal worlds, which has these rules when the preorder is well-founded but not in general
(`Nonmonotonic.exists_not_isPreferential_minimals`). On a preorder that is not total, such as an
ordering source can induce, rational monotonicity can fail (`exists_not_isRational_closestImp`). -/

section Logic

theorem isPreferential_variablyStrictImp {ord : I → Preorder W} :
    Nonmonotonic.IsPreferential fun p q ↦ i ∈ variablyStrictImp access ord p q where
  refl _ := Filter.mem_of_superset OrderingSemantics.self_mem_necessityFilter
    Set.inter_subset_right
  rightWeakening h hψχ :=
    Filter.mem_of_superset (f := OrderingSemantics.necessityFilter (ord i) _) h hψχ
  and h h' := Filter.inter_mem (f := OrderingSemantics.necessityFilter (ord i) _) h h'
  or h h' := by
    rw [mem_variablyStrictImp, Set.inter_union_distrib_left]
    exact OrderingSemantics.necessityFilter_union_le (Filter.mem_sup.2 ⟨h, h'⟩)
  cautiousMonotonicity h h' := by
    rw [mem_variablyStrictImp, ← Set.inter_assoc, OrderingSemantics.necessityFilter_inter_of_mem h]
    exact h'

theorem isRational_variablyStrictImp {ord : I → Preorder W} (htot : Std.Total (ord i).le) :
    Nonmonotonic.IsRational fun p q ↦ i ∈ variablyStrictImp access ord p q where
  toIsPreferential := isPreferential_variablyStrictImp
  rationalMonotonicity h h' := by
    rw [mem_variablyStrictImp, ← Set.inter_assoc,
      OrderingSemantics.necessityFilter_inter_of_frequently htot h']
    exact Filter.mem_inf_of_left h

variable {ord : W → Preorder W}

/-- On a well-founded preorder the conditional of the closest worlds is preferential. -/
theorem isPreferential_closestImp (hwf : WellFounded (ord w).lt) :
    Nonmonotonic.IsPreferential fun p q ↦ w ∈ closestImp ord p q :=
  Nonmonotonic.isPreferential_minimals hwf

/-- On a well-founded total preorder the conditional of the closest worlds is rational. -/
theorem isRational_closestImp (hwf : WellFounded (ord w).lt) (htot : Std.Total (ord w).le) :
    Nonmonotonic.IsRational fun p q ↦ w ∈ closestImp ord p q :=
  Nonmonotonic.isRational_minimals hwf htot

theorem exists_not_isRational_closestImp :
    ∃ ord : Fin 3 → Preorder (Fin 3),
      ¬ Nonmonotonic.IsRational fun p q ↦ (0 : Fin 3) ∈ closestImp ord p q := by
  obtain ⟨p, hp⟩ := Nonmonotonic.exists_not_isRational_necessityFilter
  refine ⟨fun _ ↦ p, ?_⟩
  simp only [OrderingSemantics.necessityFilter_eq_principal_of_wellFounded
    (letI := p; wellFounded_lt), Filter.mem_principal] at hp
  exact hp

end Logic


end Conditional
