module

public import Linglib.Semantics.Modality.OrderingSemantics
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
ultrafilter, which ties between closest worlds rule out. Lewis's axiomatization of the V-logics
with the counterfactual primitive is sound, its axioms being the laws of the filter, and every
theorem of Stalnaker's C2 holds under centering and Stalnaker's Assumption, while conditional
excluded middle is not a theorem of VC.

## Main statements

* `mem_variablyStrictImp_iff_spheres`: the truth condition by spheres is the primitive.
* `sobel`: a variably strict conditional makes a Sobel sequence true; `mem_strictImp_of_sobel`:
  a strict one cannot without vacuity.
* `closestImp_line`, `not_mem_variablyStrictImp_line_two`, `not_cem_line`: the line example.
* `variablyStrictImp_eq_ofDomain_selection`, `forall_mem_variablyStrictImp_or_compl_iff`:
  Stalnaker's theory is a special case, and conditional excluded middle is an ultrafilter.
* `Provable.sound`, `valid_vcs_of_c2`, `not_provable_vc_cem`: VW, VC and VCS are sound, the
  theorems of C2 are valid for VCS, and conditional excluded middle is not a theorem of VC.

## Implementation notes

Propositions are all sets of worlds, so Lewis's assumptions for every antecedent of the language
are assumptions for every set. The conditions of §2.3 placing inaccessible worlds above the
accessible ones enter by restricting antecedents to the accessible worlds.

The V-logics are stated over Stalnaker's formulas (`Stalnaker1968.Formula`), the corner read as
the counterfactual. The other operators are Lean definitions, so the axiom schema of definitions
holds by definition, and Deduction within Conditionals takes the conjunction of its premises as a
`List.foldr`. Centering is `Conditional.IsCentered`, stated over all worlds.

## TODO

* The completeness of the V-logics (§6.1), and that every theorem of VCS is a theorem of
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

-- §1.5
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

-- §3.4
theorem not_cem_of_tie {v v' : W} (hv : v ∈ (ord i).minimals (access i ∩ p))
    (hv' : v' ∈ (ord i).minimals (access i ∩ p)) (hne : v ≠ v') :
    i ∉ variablyStrictImp access ord p {v} ∧ i ∉ variablyStrictImp access ord p {v}ᶜ :=
  ⟨fun h ↦ hne (variablyStrictImp_subset_orderingImp h hv').symm,
    fun h ↦ variablyStrictImp_subset_orderingImp h hv rfl⟩

/-! ### The V-logics with the counterfactual primitive

Lewis axiomatizes VC with the counterfactual primitive by Modus Ponens, Deduction within
Conditionals and Interchange of Logical Equivalents, the tautologies, the definitions of the other
operators, and axioms (3)–(7). VW drops (7), and VCS adds conditional excluded middle as (8)
(§6.1). Axioms (3)–(5) and the rules hold on every total preorder. (3) and Deduction within
Conditionals hold because the necessities over the antecedent-worlds form a filter containing
them, (4) because an antecedent whose negation would imply it holds at every accessible world, and
(5) because restricting an antecedent to a proposition possible over it restricts its filter to
that proposition. (6) holds under weak centering, (7) under centering and (8) under Stalnaker's
Assumption. -/

section VLogic

universe u

open Stalnaker1968 (Formula)

variable {α : Type*} {access : W → Set W} {ord : W → Preorder W} {V : α → Set W} {w : W}

/-- The proposition a formula expresses when its corner is read as the variably strict
conditional over `access` and `ord`. -/
def eval (access : W → Set W) (ord : W → Preorder W) (V : α → Set W) : Formula α → Set W
  | .atom a => V a
  | .neg A => (eval access ord V A)ᶜ
  | .imp A B => materialImp (eval access ord V A) (eval access ord V B)
  | .corner A B => variablyStrictImp access ord (eval access ord V A) (eval access ord V B)

@[simp] theorem eval_neg {A : Formula α} : eval access ord V A.neg = (eval access ord V A)ᶜ :=
  rfl

@[simp] theorem mem_eval_imp {A B : Formula α} :
    w ∈ eval access ord V (A.imp B) ↔ (w ∈ eval access ord V A → w ∈ eval access ord V B) :=
  Iff.rfl

theorem mem_eval_corner {A B : Formula α} :
    w ∈ eval access ord V (A.corner B) ↔
      eval access ord V B ∈ necessityFilter (ord w) (access w ∩ eval access ord V A) :=
  Iff.rfl

@[simp] theorem eval_and {A B : Formula α} :
    eval access ord V (A.and B) = eval access ord V A ∩ eval access ord V B :=
  Set.ext fun _ ↦ by simp [Formula.and]

theorem mem_eval_iff {A B : Formula α} :
    w ∈ eval access ord V (A.iff B) ↔ (w ∈ eval access ord V A ↔ w ∈ eval access ord V B) := by
  simp [Formula.iff, iff_def]

/-- `C'` is `C` with some occurrences of `A` interchanged with `B`. -/
inductive Interchange (A B : Formula α) : Formula α → Formula α → Prop
  | refl (C : Formula α) : Interchange A B C C
  | here : Interchange A B A B
  | neg {C C' : Formula α} : Interchange A B C C' → Interchange A B C.neg C'.neg
  | imp {C C' D D' : Formula α} : Interchange A B C C' → Interchange A B D D' →
      Interchange A B (C.imp D) (C'.imp D')
  | corner {C C' D D' : Formula α} : Interchange A B C C' → Interchange A B D D' →
      Interchange A B (C.corner D) (C'.corner D')

theorem Interchange.eval_eq {A B C C' : Formula α}
    (hAB : eval access ord V A = eval access ord V B) (h : Interchange A B C C') :
    eval access ord V C = eval access ord V C' := by
  induction h with
  | refl => rfl
  | here => exact hAB
  | neg _ ih => rw [eval_neg, eval_neg, ih]
  | imp _ _ ih ih' => simp only [eval, ih, ih']
  | corner _ _ ih ih' => simp only [eval, ih, ih']

/-- Lewis's V-logics VW, VC and VCS. -/
inductive VLogic
  | VW
  | VC
  | VCS

/-- The conditions under which a V-logic is sound: weak centering for VW, centering for VC, and
for VCS centering with Stalnaker's Assumption, a single closest accessible antecedent-world
whenever there is an accessible one. -/
def VLogic.Holds (access : W → Set W) (ord : W → Preorder W) : VLogic → Prop
  | .VW => (∀ w, w ∈ access w) ∧ ∀ w v, (ord w).le w v
  | .VC => (∀ w, w ∈ access w) ∧ IsCentered ord
  | .VCS => ((∀ w, w ∈ access w) ∧ IsCentered ord) ∧
      ∀ w p, (access w ∩ p).Nonempty → ∃ v, (ord w).minimals (access w ∩ p) = {v}

variable {L : VLogic}

theorem VLogic.Holds.mem (h : L.Holds access ord) (w : W) : w ∈ access w := by
  cases L
  exacts [h.1 w, h.1 w, h.1.1 w]

theorem VLogic.Holds.le (h : L.Holds access ord) (w v : W) : (ord w).le w v := by
  cases L
  exacts [h.2 w v, h.2.le w v, h.1.2.le w v]

theorem VLogic.Holds.isCentered (h : L.Holds access ord) (hL : L ≠ .VW) : IsCentered ord := by
  cases L
  exacts [absurd rfl hL, h.2, h.1.2]

/-- The theorems of Lewis's axiomatization of a V-logic with the counterfactual primitive: the
tautologies and axioms (3)–(6), with (7) except in VW and (8) in VCS, closed under Modus Ponens,
Deduction within Conditionals and Interchange of Logical Equivalents. -/
inductive Provable (L : VLogic) : Formula α → Prop
  | taut {A : Formula α} : A.IsTautology → Provable L A
  | a3 (φ : Formula α) : Provable L (φ.corner φ)
  | a4 (φ ψ : Formula α) : Provable L ((φ.neg.corner φ).imp (ψ.corner φ))
  | a5 (φ ψ χ : Formula α) :
      Provable L ((φ.corner ψ.neg).or (((φ.and ψ).corner χ).iff (φ.corner (ψ.imp χ))))
  | a6 (φ ψ : Formula α) : Provable L ((φ.corner ψ).imp (φ.imp ψ))
  | a7 (φ ψ : Formula α) : L ≠ .VW → Provable L ((φ.and ψ).imp (φ.corner ψ))
  | a8 (φ ψ : Formula α) : L = .VCS → Provable L ((φ.corner ψ).or (φ.corner ψ.neg))
  | mp {A B : Formula α} : Provable L (A.imp B) → Provable L A → Provable L B
  | deduction (φ ψ χ : Formula α) (χs : List (Formula α)) :
      Provable L ((χs.foldr Formula.and χ).imp ψ) →
        Provable L (((χs.map φ.corner).foldr Formula.and (φ.corner χ)).imp (φ.corner ψ))
  | interchange {A B C C' : Formula α} :
      Provable L (A.iff B) → Interchange A B C C' → Provable L C → Provable L C'

/-- A formula is valid in a V-logic when it holds at every world of every interpretation over a
total preorder satisfying the logic's conditions. -/
def Valid (L : VLogic) (A : Formula α) : Prop :=
  ∀ {W : Type u} {access : W → Set W} {ord : W → Preorder W}, (∀ w, Std.Total (ord w).le) →
    L.Holds access ord → ∀ V : α → Set W, eval access ord V A = Set.univ

/-- The V-logics are sound. -/
theorem Provable.sound {A : Formula α} (h : Provable L A) : Valid.{u} L A := by
  intro W access ord htot hL V
  refine Set.eq_univ_of_forall fun w ↦ ?_
  induction h generalizing w with
  | taut h => exact h (fun B ↦ w ∈ eval access ord V B) (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl
  | a3 φ =>
    rw [mem_eval_corner]
    exact mem_of_superset self_mem_necessityFilter Set.inter_subset_right
  | a4 φ ψ =>
    rw [mem_eval_imp, mem_eval_corner, mem_eval_corner, eval_neg]
    intro h
    have hbot : (∅ : Set W) ∈ necessityFilter (ord w) (access w ∩ (eval access ord V φ)ᶜ) := by
      simpa using inter_mem h (mem_of_superset self_mem_necessityFilter Set.inter_subset_right)
    have hemp : access w ∩ (eval access ord V φ)ᶜ = ∅ := Set.not_nonempty_iff_eq_empty.1
      fun hne ↦ (necessityFilter_neBot_iff.2 hne).ne (empty_mem_iff_bot.1 hbot)
    exact mem_of_superset self_mem_necessityFilter fun x hx ↦
      by_contra fun hxφ ↦ Set.eq_empty_iff_forall_notMem.1 hemp x ⟨hx.1, hxφ⟩
  | a5 φ ψ χ =>
    simp only [Formula.or, mem_eval_imp, eval_neg, Set.mem_compl_iff]
    intro hfr
    have e : necessityFilter (ord w) (access w ∩ eval access ord V φ ∩ eval access ord V ψ) =
        necessityFilter (ord w) (access w ∩ eval access ord V φ) ⊓ 𝓟 (eval access ord V ψ) :=
      necessityFilter_inter_of_frequently (htot w) hfr
    rw [mem_eval_iff, mem_eval_corner, mem_eval_corner, eval_and, ← Set.inter_assoc, e,
      mem_inf_principal]
    rfl
  | a6 φ ψ =>
    rw [mem_eval_imp, mem_eval_corner, mem_eval_imp]
    intro h hφ
    obtain ⟨v, -, -, hvψ⟩ := h w ⟨hL.mem w, hφ⟩
    exact hvψ w ⟨hL.mem w, hφ⟩ (hL.le w v)
  | a7 φ ψ hL' =>
    rw [mem_eval_imp, eval_and, mem_eval_corner]
    rintro ⟨hφ, hψ⟩
    have hc := hL.isCentered hL'
    have hw : w ∈ access w ∩ eval access ord V φ := ⟨hL.mem w, hφ⟩
    refine (mem_necessityFilter_iff_of_least hw fun v _ ↦ hc.le w v).2 fun x _ hxw ↦ ?_
    by_contra hxψ
    have hne : w ≠ x := fun e ↦ hxψ (e ▸ hψ)
    exact hc.not_le hne hxw
  | a8 φ ψ hL' =>
    subst hL'
    simp only [Formula.or, mem_eval_imp, eval_neg, Set.mem_compl_iff, mem_eval_corner]
    rcases (access w ∩ eval access ord V φ).eq_empty_or_nonempty with h | h
    · intro _ u hu
      exact absurd (h ▸ hu) (Set.notMem_empty u)
    · obtain ⟨v, hv⟩ := hL.2 w _ h
      have hmin : v ∈ (ord w).minimals (access w ∩ eval access ord V φ) := by
        rw [hv]; exact Set.mem_singleton v
      rw [necessityFilter_eq_principal fun u hu ↦
        ⟨v, hmin, ((Preorder.mem_minimals_iff_forall_le (htot w)).1 hmin).2 u hu⟩, hv,
        mem_principal, mem_principal, Set.singleton_subset_iff, Set.singleton_subset_iff]
      exact id
  | mp _ _ ihab iha => exact ihab w (iha w)
  | deduction φ ψ χ χs hprem ih =>
    rw [mem_eval_imp, mem_eval_corner]
    intro h
    refine mem_of_superset ?_ fun x hx ↦ ih x hx
    clear ih hprem
    induction χs with
    | nil => exact h
    | cons c cs ihc =>
      rw [List.map_cons, List.foldr_cons, eval_and] at h
      rw [List.foldr_cons, eval_and]
      exact inter_mem (mem_eval_corner.1 h.1) (ihc h.2)
  | interchange _ hI _ ihAB ihC =>
    rw [← hI.eval_eq (Set.ext fun x ↦ mem_eval_iff.1 (ihAB x))]
    exact ihC w

theorem eval_eq_formula_eval
    (hlim : ∀ w B, (access w ∩ B).Nonempty → ((ord w).minimals (access w ∩ B)).Nonempty)
    (A : Formula α) :
    eval access ord V A = A.eval (fun w B ↦ (ord w).minimals (access w ∩ B)) V := by
  induction A with
  | atom => rfl
  | neg A ih => rw [eval_neg, ih]; rfl
  | imp A B ihA ihB => simp only [eval, Stalnaker1968.Formula.eval, ihA, ihB]
  | corner A B ihA ihB =>
    ext w
    show w ∈ variablyStrictImp access ord _ _ ↔ w ∈ ofDomain _ _ _
    rw [ihA, ihB]
    exact mem_variablyStrictImp_iff_mem_orderingImp (hlim w)

theorem isSelectionFunction_of_stalnaker (hR : ∀ w, w ∈ access w) (hc : IsCentered ord)
    (htot : ∀ w, Std.Total (ord w).le)
    (hS : ∀ w p, (access w ∩ p).Nonempty → ∃ v, (ord w).minimals (access w ∩ p) = {v}) :
    Stalnaker1968.IsSelectionFunction access fun w A ↦ (ord w).minimals (access w ∩ A) where
  refl := hR
  subsingleton w A := by
    rcases (access w ∩ A).eq_empty_or_nonempty with h | h
    · rw [h, Preorder.minimals_empty]; exact Set.subsingleton_empty
    · obtain ⟨v, hv⟩ := hS w A h
      rw [hv]; exact Set.subsingleton_singleton
  subset w _ := ((ord w).minimals_subset _).trans Set.inter_subset_right
  absurdity w A h := Set.not_nonempty_iff_eq_empty.1 fun hA ↦
    let ⟨v, hv⟩ := hS w A hA
    Set.singleton_ne_empty v (hv ▸ h)
  centering w _ h := hc.minimals_eq_singleton ⟨hR w, h⟩
  cso w A B h₁ h₂ := by
    have key {A B : Set W} (h₁ : (ord w).minimals (access w ∩ B) ⊆ A)
        (h₂ : (ord w).minimals (access w ∩ A) ⊆ B) :
        (ord w).minimals (access w ∩ A) ⊆ (ord w).minimals (access w ∩ B) := fun a ha ↦ by
      have haB : a ∈ access w ∩ B := ⟨ha.1.1, h₂ ha⟩
      obtain ⟨b, hb⟩ := hS w B ⟨a, haB⟩
      have hbm : b ∈ (ord w).minimals (access w ∩ B) := by rw [hb]; exact Set.mem_singleton b
      have hab := ((Preorder.mem_minimals_iff_forall_le (htot w)).1 ha).2 b ⟨hbm.1.1, h₁ hbm⟩
      exact (Preorder.mem_minimals_iff_forall_le (htot w)).2 ⟨haB, fun x hx ↦
        (ord w).le_trans _ _ _ hab (((Preorder.mem_minimals_iff_forall_le (htot w)).1 hbm).2 x hx)⟩
    exact (key h₁ h₂).antisymm (key h₂ h₁)

/-- Every theorem of Stalnaker's C2 is valid under centering and Stalnaker's Assumption. -/
theorem valid_vcs_of_c2 {A : Formula α} (h : Stalnaker1968.Provable A) : Valid.{u} .VCS A := by
  intro W access ord htot ⟨⟨hR, hc⟩, hS⟩ V
  rw [eval_eq_formula_eval fun w B hB ↦ by obtain ⟨v, hv⟩ := hS w B hB; rw [hv]; simp]
  exact h.sound (isSelectionFunction_of_stalnaker hR hc htot hS) V

/-- Comparative similarity from `w` under which every other world is equally far. -/
abbrev tieSim (w : Fin 3) : Preorder (Fin 3) := Preorder.lift fun v ↦ if v = w then (0 : ℕ) else 1

/-- Conditional excluded middle is not a theorem of VC: two worlds tied for closest falsify both
of its disjuncts (§3.4). -/
theorem not_provable_vc_cem :
    ¬ Provable .VC (((Formula.atom 0 : Formula (Fin 2)).corner (.atom 1)).or
      ((Formula.atom 0).corner (Formula.atom 1).neg)) := fun h ↦ by
  have hc : IsCentered tieSim := fun w w' hne ↦ by
    show (if w = w then (0 : ℕ) else 1) < if w' = w then 0 else 1
    simp [Ne.symm hne]
  have hL : VLogic.Holds (fun _ : Fin 3 ↦ Set.univ) tieSim .VC := ⟨fun _ ↦ trivial, hc⟩
  have h0 := h.sound (fun _ ↦ Preorder.total_lift _) hL ![{1, 2}, {1}]
  have hmem : ∀ v : Fin 3, v ∈ (tieSim 0).minimals (Set.univ ∩ {1, 2}) ↔ v = 1 ∨ v = 2 := by
    simp only [Preorder.mem_minimals_lift, Set.univ_inter, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    decide
  have ht := not_cem_of_tie (access := fun _ : Fin 3 ↦ Set.univ) (ord := tieSim) (i := 0)
    ((hmem 1).2 (.inl rfl)) ((hmem 2).2 (.inr rfl)) (by decide)
  have h0' : (0 : Fin 3) ∈ eval (fun _ ↦ Set.univ) tieSim ![{1, 2}, {1}]
      (((Formula.atom 0 : Formula (Fin 2)).corner (.atom 1)).or
        ((Formula.atom 0).corner (Formula.atom 1).neg)) := by
    rw [h0]; exact Set.mem_univ 0
  exact ht.2 (h0' ht.1)

end VLogic

end Lewis1973b
