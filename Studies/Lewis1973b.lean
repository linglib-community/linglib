module

public import Linglib.Semantics.Modality.OrderingSemantics.Filter
public import Linglib.Core.Order.Filter.Ultrafilter
public import Studies.Stalnaker1968
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Lewis (1973b): Counterfactuals

Lewis analyses the counterfactual as a variably strict conditional over comparative similarity:
*if p, q* holds when, as the accessible `p`-worlds come closer, the consequent eventually holds at
all of them, and *if p, might q* when it holds at some of them however close one comes. This file
takes as primitive the theory layer's conditional over an accessibility assignment and a family
of similarity preorders (`Conditional.variablyStrictImp`), which is membership in the filter of
necessities over the accessible antecedent-worlds, and derives the book's apparatus from it.
Lewis's systems of spheres are the sets of accessible worlds each closer than every accessible
world outside, and his truth condition by spheres is the primitive on a total preorder. No strict
conditional makes two adjacent stages of a Sobel sequence true, and a variably strict one does.
Under the Limit Assumption the conditional is truth at the closest accessible antecedent-worlds;
without it, as for a line longer than an inch, the closest-world conditional is vacuously true of
every consequent while the variably strict one is not, and conditional excluded middle fails
although the ordering has no ties. Stalnaker's theory is the special case of a linear,
well-founded ordering, and conditional excluded middle at an antecedent is the filter being an
ultrafilter, which ties between closest worlds rule out.

## Main statements

* `mem_variablyStrictImp_iff_spheres`: the truth condition by spheres is the primitive.
* `sobel`: a variably strict conditional makes a Sobel sequence true; `mem_strictImp_of_sobel`:
  a strict one cannot without vacuity.
* `closestImp_line`, `not_mem_variablyStrictImp_line_two`, `not_cem_line`: the line example.
* `variablyStrictImp_eq_ofDomain_selection`: Stalnaker's theory is a special case.
* `forall_mem_variablyStrictImp_or_compl_iff`: conditional excluded middle is an ultrafilter.

## Implementation notes

Propositions are all sets of worlds, so Lewis's assumptions for every antecedent of the language
are assumptions for every set. The conditions of §2.3 placing inaccessible worlds above the
accessible ones enter by restricting antecedents to the accessible worlds.

## TODO

* The logic VC of §6.1, its soundness, and the coincidence of the theorems of VCS with those of
  Stalnaker's C2.
* Comparative possibility (§2.5) as the lifting of comparative similarity to propositions, and the
  representation of set-selection functions (§2.7).
* Stalnaker's Assumption as a well-ordering of the accessible worlds (§3.4).

## References

* [lewis-1973b]
* [stalnaker-1968]
-/

@[expose] public section

namespace Lewis1973b

open Conditional OrderingSemantics Filter Set

variable {I W : Type*} {access : I → Set W} {ord : I → Preorder W} {i : I} {p q : Set W}

/-! ### Eventual and frequent truth -/

theorem mem_variablyStrictImp_iff_mem_necessityFilter :
    i ∈ variablyStrictImp access ord p q ↔ q ∈ necessityFilter (ord i) (access i ∩ p) := Iff.rfl

/-- The *might* counterfactual holds when the consequent holds at antecedent-worlds however close
one comes (§1.5). -/
theorem mem_might_variablyStrictImp_iff {access : W → Set W} {ord : W → Preorder W} {w : W} :
    w ∈ might (variablyStrictImp access ord) p q ↔
      ∃ᶠ v in necessityFilter (ord w) (access w ∩ p), v ∈ q := Iff.rfl

/-! ### Systems of spheres -/

/-- The spheres around `i` (§1.3) that comparative similarity determines (§2.3): the sets of
accessible worlds each closer to `i` than every accessible world outside. -/
def spheres (access : I → Set W) (ord : I → Preorder W) (i : I) : Set (Set W) :=
  {S | S ⊆ access i ∧ ∀ j ∈ S, ∀ k ∈ access i, k ∉ S → (ord i).lt j k}

variable {S : Set W} {j k : W}

theorem mem_of_mem_spheres (hS : S ∈ spheres access ord i) (hj : j ∈ S) (hk : k ∈ access i)
    (hkj : (ord i).le k j) : k ∈ S :=
  by_contra fun hkS ↦ (((ord i).lt_iff_le_not_ge _ _).1 (hS.2 j hj k hk hkS)).2 hkj

theorem isChain_spheres : IsChain (· ⊆ ·) (spheres access ord i) := fun _ hS _ hT _ ↦ by
  by_contra h
  simp only [not_or, Set.not_subset] at h
  obtain ⟨⟨j, hjS, hjT⟩, ⟨k, hkT, hkS⟩⟩ := h
  exact (((ord i).lt_iff_le_not_ge _ _).1 (hS.2 j hjS k (hT.1 hkT) hkS)).2
    (((ord i).lt_iff_le_not_ge _ _).1 (hT.2 k hkT j (hS.1 hjS) hjT)).1

theorem sUnion_mem_spheres {𝒮 : Set (Set W)} (h𝒮 : 𝒮 ⊆ spheres access ord i) :
    ⋃₀ 𝒮 ∈ spheres access ord i :=
  ⟨sUnion_subset fun _ hS ↦ (h𝒮 hS).1, fun _ ⟨S, hS, hjS⟩ k hk hkU ↦
    (h𝒮 hS).2 _ hjS k hk fun hkS ↦ hkU ⟨S, hS, hkS⟩⟩

theorem sInter_mem_spheres {𝒮 : Set (Set W)} (h𝒮 : 𝒮 ⊆ spheres access ord i)
    (hne : 𝒮.Nonempty) : ⋂₀ 𝒮 ∈ spheres access ord i := by
  obtain ⟨S₀, hS₀⟩ := hne
  refine ⟨(sInter_subset_of_mem hS₀).trans (h𝒮 hS₀).1, fun j hj k hk hkI ↦ ?_⟩
  simp only [mem_sInter, not_forall] at hkI
  obtain ⟨S, hS, hkS⟩ := hkI
  exact (h𝒮 hS).2 j (hj S hS) k hk hkS

theorem singleton_mem_spheres {access : W → Set W} {ord : W → Preorder W} {w : W}
    (hR : w ∈ access w) (hc : IsCentered ord) : {w} ∈ spheres access ord w := by
  refine ⟨singleton_subset_iff.2 hR, fun j hj k _ hk ↦ ?_⟩
  rw [mem_singleton_iff] at hj
  subst hj
  exact hc j k fun h ↦ hk h.symm

/-- On a total preorder, *if p, q* holds when no sphere contains a `p`-world, or some sphere
contains one and `q` holds at every `p`-world in it (§1.3). -/
theorem mem_variablyStrictImp_iff_spheres (htot : Std.Total (ord i).le) :
    i ∈ variablyStrictImp access ord p q ↔ (∀ S ∈ spheres access ord i, Disjoint S p) ∨
      ∃ S ∈ spheres access ord i, (S ∩ p).Nonempty ∧ S ∩ p ⊆ q := by
  constructor
  · intro h
    rcases (access i ∩ p).eq_empty_or_nonempty with he | ⟨u, hu⟩
    · exact .inl fun S hS ↦ Set.disjoint_iff_inter_eq_empty.2
        (subset_empty_iff.1 (he ▸ inter_subset_inter_left p hS.1))
    obtain ⟨b, hb, -, hbq⟩ := h u hu
    refine .inr ⟨{x ∈ access i | (ord i).le x b}, ⟨fun x hx ↦ hx.1, fun j hj k hk hkS ↦ ?_⟩,
      ⟨b, ⟨hb.1, (ord i).le_refl b⟩, hb.2⟩, fun x hx ↦ hbq x ⟨hx.1.1, hx.2⟩ hx.1.2⟩
    have hbk : ¬ (ord i).le k b := fun h ↦ hkS ⟨hk, h⟩
    refine ((ord i).lt_iff_le_not_ge _ _).2 ⟨(ord i).le_trans _ _ _ hj.2
      ((htot.total k b).resolve_left hbk), fun hkj ↦ hbk ((ord i).le_trans _ _ _ hkj hj.2)⟩
  · rintro (h | ⟨S, hS, ⟨x, hxS, hxp⟩, hSq⟩) u hu
    · exact absurd hu.2 (Set.disjoint_left.1 (h _ ⟨subset_rfl, fun _ _ k hk hkS ↦
        absurd hk hkS⟩) hu.1)
    by_cases huS : u ∈ S
    · exact ⟨u, hu, (ord i).le_refl u, fun c hc hcu ↦
        hSq ⟨mem_of_mem_spheres hS huS hc.1 hcu, hc.2⟩⟩
    · exact ⟨x, ⟨hS.1 hxS, hxp⟩, ((ord i).lt_iff_le_not_ge _ _).1 (hS.2 x hxS u hu.1 huS) |>.1,
        fun c hc hcx ↦ hSq ⟨mem_of_mem_spheres hS hxS hc.1 hcx, hc.2⟩⟩

/-! ### Sobel sequences

*If Otto had come it would have been lively; but if both Otto and Anna had come it would have
been dreary* (§1.2). -/

/-- A strict conditional true of `p` and of `p ∩ r` with opposite consequents is true of `p ∩ r`
for every consequent: the stronger antecedent has no accessible worlds. -/
theorem mem_strictImp_of_sobel {r t : Set W} (h₁ : i ∈ strictImp access p q)
    (h₂ : i ∈ strictImp access (p ∩ r) qᶜ) : i ∈ strictImp access (p ∩ r) t :=
  fun _ hx ↦ absurd (h₁ ⟨hx.1, hx.2.1⟩) (h₂ hx)

/-- Similarity of three worlds by distance ahead: `0` closest to itself, then `1`, then `2`. -/
abbrev ahead (w : Fin 3) : Preorder (Fin 3) := Preorder.lift (· - w)

/-- At `0`, with Otto coming at `1` and `2`, Anna at `2`, and the party lively only at `1`, if Otto
had come it would have been lively and not dreary, and if Otto and Anna had come it would have
been dreary and not lively. -/
theorem sobel :
    let otto : Set (Fin 3) := {v | v ≠ 0}
    let anna : Set (Fin 3) := {v | v = 2}
    let lively : Set (Fin 3) := {v | v = 1}
    (0 ∈ variablyStrictImp (fun _ ↦ .univ) ahead otto lively ∧
      0 ∉ variablyStrictImp (fun _ ↦ .univ) ahead otto livelyᶜ) ∧
    (0 ∈ variablyStrictImp (fun _ ↦ .univ) ahead (otto ∩ anna) livelyᶜ ∧
      0 ∉ variablyStrictImp (fun _ ↦ .univ) ahead (otto ∩ anna) lively) := by
  intro otto anna lively
  simp only [← closestImp_eq_variablyStrictImp_of_finite (fun w ↦ Preorder.total_lift _)
    (Set.toFinite _)]
  decide

/-! ### The Limit Assumption

Lengths of a line, the actual one at most an inch, similar to the actual one as their lengths
are close to it (§1.4). -/

/-- Similarity of lengths by distance. -/
abbrev lineSim (w : ℝ) : Preorder ℝ := Preorder.lift fun x ↦ |x - w|

variable {a : ℝ}

theorem abs_sub_eq (ha : a ≤ 1) {x : ℝ} (hx : 1 < x) : |x - a| = x - a :=
  abs_of_pos (by linarith)

/-- No length over an inch is closest to an actual length of at most an inch. -/
theorem minimals_lineSim (ha : a ≤ 1) : (lineSim a).minimals (Ioi 1) = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have hx1 : (1 : ℝ) < x := hx.1
  have hy : (1 : ℝ) < (1 + x) / 2 := by linarith
  have := hx.2 (show (1 + x) / 2 ∈ Ioi (1 : ℝ) from hy) (by
    change |(1 + x) / 2 - a| ≤ |x - a|
    rw [abs_sub_eq ha hy, abs_sub_eq ha hx1]; linarith)
  change |x - a| ≤ |(1 + x) / 2 - a| at this
  rw [abs_sub_eq ha hy, abs_sub_eq ha hx1] at this
  linarith

/-- The conditional of the closest worlds makes *if the line were over an inch long, it would be
`q`* true of every `q`. -/
theorem closestImp_line (ha : a ≤ 1) (q : Set ℝ) : a ∈ closestImp lineSim (Ioi 1) q :=
  mem_closestImp_of_closest_eq_empty (minimals_lineSim ha)

/-- The variably strict conditional does not make *if the line were over an inch long, it would
be two inches long* true. -/
theorem not_mem_variablyStrictImp_line_two (ha : a ≤ 1) :
    a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) {2} := fun h ↦ by
  obtain ⟨b, ⟨-, hb⟩, -, hbq⟩ := h 2 ⟨trivial, by norm_num [Ioi]⟩
  have hb1 : (1 : ℝ) < b := hb
  have hc : (1 : ℝ) < min b (3 / 2) := lt_min hb1 (by norm_num)
  have h2 := hbq (min b (3 / 2)) ⟨trivial, hc⟩ (by
    change |min b (3 / 2) - a| ≤ |b - a|
    rw [abs_sub_eq ha hc, abs_sub_eq ha hb1]; linarith [min_le_left b (3 / 2)])
  have : min b (3 / 2) ≤ 3 / 2 := min_le_right _ _
  rw [mem_singleton_iff] at h2
  linarith

/-- It makes *if the line were over an inch long, it would be under an inch and a half* true. -/
theorem mem_variablyStrictImp_line (ha : a ≤ 1) :
    a ∈ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) (Iio (3 / 2)) := fun u hu ↦ by
  have hu1 : (1 : ℝ) < u := hu.2
  have hb : (1 : ℝ) < min u (5 / 4) := lt_min hu1 (by norm_num)
  refine ⟨min u (5 / 4), ⟨trivial, hb⟩, ?_, fun c hc hcb ↦ ?_⟩
  · change |min u (5 / 4) - a| ≤ |u - a|
    rw [abs_sub_eq ha hb, abs_sub_eq ha hu1]; linarith [min_le_left u (5 / 4)]
  · have hc1 : (1 : ℝ) < c := hc.2
    change |c - a| ≤ |min u (5 / 4) - a| at hcb
    rw [abs_sub_eq ha hc1, abs_sub_eq ha hb] at hcb
    exact show c < 3 / 2 by linarith [min_le_right u (5 / 4)]

/-- Conditional excluded middle at an antecedent is the filter of necessities over its accessible
worlds being trivial or an ultrafilter. -/
theorem forall_mem_variablyStrictImp_or_compl_iff :
    (∀ q, i ∈ variablyStrictImp access ord p q ∨ i ∈ variablyStrictImp access ord p qᶜ) ↔
      necessityFilter (ord i) (access i ∩ p) = ⊥ ∨
        IsAtom (necessityFilter (ord i) (access i ∩ p)) :=
  show (∀ q, q ∈ necessityFilter _ _ ∨ qᶜ ∈ necessityFilter _ _) ↔ _ from
    Filter.forall_mem_or_compl_mem_iff

/-- Conditional excluded middle fails for the line although lengths over an inch are never tied:
whether the length would be rational is settled by no closeness to the actual length. -/
theorem not_cem_line (ha : a ≤ 1) :
    (∀ x ∈ Ioi (1 : ℝ), ∀ y ∈ Ioi (1 : ℝ), (lineSim a).le x y → (lineSim a).le y x → x = y) ∧
      a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) (range ((↑) : ℚ → ℝ)) ∧
      a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) (range ((↑) : ℚ → ℝ))ᶜ := by
  refine ⟨fun x hx y hy hxy hyx ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · change |x - a| ≤ |y - a| at hxy
    change |y - a| ≤ |x - a| at hyx
    rw [abs_sub_eq ha hx, abs_sub_eq ha hy] at hxy hyx
    linarith
  all_goals
    obtain ⟨b, ⟨-, hb⟩, -, hbq⟩ := h 2 ⟨trivial, by norm_num [Ioi]⟩
    have hb1 : (1 : ℝ) < b := hb
  · obtain ⟨c, hc, hc1, hcb⟩ := exists_irrational_btwn hb1
    refine hc (hbq c ⟨trivial, hc1⟩ ?_)
    change |c - a| ≤ |b - a|
    rw [abs_sub_eq ha hc1, abs_sub_eq ha hb1]; linarith
  · obtain ⟨c, hc1, hcb⟩ := exists_rat_btwn hb1
    refine hbq c ⟨trivial, hc1⟩ ?_ ⟨c, rfl⟩
    change |(c : ℝ) - a| ≤ |b - a|
    rw [abs_sub_eq ha hc1, abs_sub_eq ha hb1]; linarith

/-! ### Stalnaker's theory

Stalnaker's selection is Lewis's similarity with two further assumptions: the Limit Assumption,
and that closest antecedent-worlds are never tied (§3.4). -/

/-- Stalnaker's theory is a special case: on a centered similarity ordering that is linear and
well-founded, the closest accessible antecedent-world is a selection function satisfying
Stalnaker's conditions, and the variably strict conditional is truth at the world it selects. -/
theorem variablyStrictImp_eq_ofDomain_selection {access : W → Set W} {ord : W → Preorder W}
    (hR : ∀ w, w ∈ access w) (hc : IsCentered ord) (htot : ∀ w, Std.Total (ord w).le)
    (hanti : ∀ w, Std.Antisymm (ord w).le) (hwf : ∀ w, WellFounded (ord w).lt) :
    Stalnaker1968.IsSelectionFunction access (fun w A ↦ (ord w).minimals (access w ∩ A)) ∧
      variablyStrictImp access ord p q =
        ofDomain (fun w A ↦ (ord w).minimals (access w ∩ A)) p q :=
  ⟨Stalnaker1968.isSelectionFunction_minimals hR hc htot hanti hwf, Set.ext fun _ ↦
    mem_variablyStrictImp_iff_mem_orderingImp fun _ hB ↦
      (Preorder.minimals_nonempty_iff (hwf _)).2 hB⟩

/-- Two tied closest antecedent-worlds falsify conditional excluded middle, as when Bizet and
Verdi are compatriots at equally close worlds where both are Italian and where both are French
(§3.4). -/
theorem not_cem_of_tie {v v' : W} (hv : v ∈ (ord i).minimals (access i ∩ p))
    (hv' : v' ∈ (ord i).minimals (access i ∩ p)) (hne : v ≠ v') :
    i ∉ variablyStrictImp access ord p {v} ∧ i ∉ variablyStrictImp access ord p {v}ᶜ :=
  ⟨fun h ↦ hne (variablyStrictImp_subset_orderingImp h hv').symm,
    fun h ↦ variablyStrictImp_subset_orderingImp h hv rfl⟩

end Lewis1973b
