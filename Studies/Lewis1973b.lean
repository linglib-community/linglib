module

public import Linglib.Semantics.Modality.ComparativePossibility
public import Linglib.Core.Order.Filter.Ultrafilter
public import Studies.Stalnaker1968
public import Mathlib.Data.Nat.Dist
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Lewis (1973b): Counterfactuals

Lewis analyses the counterfactual as a variably strict conditional: *if p, q* holds when, as the
accessible `p`-worlds come closer, `q` eventually holds at all of them. The primitive is the theory
layer's conditional over accessibility and similarity preorders (`Conditional.variablyStrictImp`),
whose spheres are [exactly Lewis's systems of spheres](##isSystemOfSpheres_iff). It [verifies
every stage of a Sobel sequence](##sobel); for a line over an inch, with no closest length, it is
[truth near an inch on the right](##atBotOn_line). Stalnaker's theory is the case in which
[similarity well-orders the accessible worlds](##stalnakerAssumption_iff), and Lewis's
[axiomatizations of the V-logics are sound](##Provable.sound).

## Implementation notes

Propositions are all sets of worlds, so Lewis's assumptions for every antecedent of the language
are assumptions for every set. The conditions of §2.3 placing inaccessible worlds above the
accessible ones enter by restricting antecedents to the accessible worlds, so the correspondence
between similarity and spheres is one-to-one on the accessible worlds.

The V-logics are stated over Stalnaker's formulas (`Stalnaker1968.Formula`), the corner read as
the counterfactual. The other operators are Lean definitions, so the axiom schema of definitions
holds by definition, and Deduction within Conditionals takes the conjunction of its premises as a
`List.foldr`. Centering is `Conditional.IsCentered`, stated over all worlds.

## TODO

* The completeness of the V-logics (§6.1), and that every theorem of VCS is a theorem of
  Stalnaker's C2.
* The representation of set-selection functions (§2.7).

## References

* [lewis-1973b]
* [stalnaker-1968]
-/

@[expose] public section

namespace Lewis1973b

open Conditional Filter Set Topology

variable {I W : Type*} {access : I → Set W} {ord : I → Preorder W} {i : I} {p q : Set W}
  {A S : Set W} {𝒮 : Set (Set W)} {j k : W}

/-! ### Systems of spheres -/

/-- Lewis's conditions (1)–(3) on the spheres around a world (§1.3), centering aside: they are
nested, closed under unions and closed under nonempty intersections. -/
structure IsSystemOfSpheres (𝒮 : Set (Set W)) : Prop where
  /-- Of two spheres, one includes the other. -/
  isChain : IsChain (· ⊆ ·) 𝒮
  /-- The union of any spheres is a sphere. -/
  sUnion_mem ⦃𝒯 : Set (Set W)⦄ : 𝒯 ⊆ 𝒮 → ⋃₀ 𝒯 ∈ 𝒮
  /-- The intersection of a nonempty set of spheres is a sphere. -/
  sInter_mem ⦃𝒯 : Set (Set W)⦄ : 𝒯 ⊆ 𝒮 → 𝒯.Nonempty → ⋂₀ 𝒯 ∈ 𝒮

/-- The spheres a similarity preorder `r` determines over the accessible worlds `A` (§2.3): the
sets of accessible worlds each closer than every accessible world outside. -/
def spheres (A : Set W) (r : Preorder W) : Set (Set W) :=
  {S | S ⊆ A ∧ ∀ j ∈ S, ∀ k ∈ A, k ∉ S → r.lt j k}

theorem mem_of_mem_spheres {r : Preorder W} (hS : S ∈ spheres A r) (hj : j ∈ S) (hk : k ∈ A)
    (hkj : r.le k j) : k ∈ S :=
  by_contra fun hkS ↦ ((r.lt_iff_le_not_ge _ _).1 (hS.2 j hj k hk hkS)).2 hkj

theorem self_mem_spheres {r : Preorder W} : A ∈ spheres A r :=
  ⟨subset_rfl, fun _ _ _ hk hkA ↦ absurd hk hkA⟩

theorem sUnion_spheres {r : Preorder W} : ⋃₀ spheres A r = A :=
  (sUnion_subset fun _ hS ↦ hS.1).antisymm (subset_sUnion_of_mem self_mem_spheres)

theorem setOf_le_mem_spheres {r : Preorder W} [Std.Total r.le] (j : W) :
    {x ∈ A | r.le x j} ∈ spheres A r :=
  ⟨fun _ hx ↦ hx.1, fun _ hx _ hk hkS ↦
    Preorder.lt_iff_not_ge.2 fun hkx ↦ hkS ⟨hk, r.le_trans _ _ _ hkx hx.2⟩⟩

-- (C), §1.3
theorem singleton_mem_spheres {access : W → Set W} {ord : W → Preorder W} {w : W}
    (hR : w ∈ access w) (hc : IsCentered ord) : {w} ∈ spheres (access w) (ord w) := by
  refine ⟨singleton_subset_iff.2 hR, fun j hj k _ hk ↦ ?_⟩
  rw [mem_singleton_iff] at hj
  subst hj
  exact hc j k fun h ↦ hk h.symm

theorem isSystemOfSpheres_spheres {r : Preorder W} : IsSystemOfSpheres (spheres A r) where
  isChain S hS T hT _ := by
    by_contra h
    simp only [not_or, Set.not_subset] at h
    obtain ⟨⟨j, hjS, hjT⟩, ⟨k, hkT, hkS⟩⟩ := h
    exact ((r.lt_iff_le_not_ge _ _).1 (hS.2 j hjS k (hT.1 hkT) hkS)).2
      ((r.lt_iff_le_not_ge _ _).1 (hT.2 k hkT j (hS.1 hjS) hjT)).1
  sUnion_mem 𝒯 h𝒯 := ⟨sUnion_subset fun _ hS ↦ (h𝒯 hS).1, fun _ ⟨S, hS, hjS⟩ k hk hkU ↦
    (h𝒯 hS).2 _ hjS k hk fun hkS ↦ hkU ⟨S, hS, hkS⟩⟩
  sInter_mem 𝒯 h𝒯 := fun ⟨S₀, hS₀⟩ ↦ ⟨(sInter_subset_of_mem hS₀).trans (h𝒯 hS₀).1,
    fun j hj k hk hkI ↦
      let ⟨S, hS, hkS⟩ := not_forall₂.1 (fun h ↦ hkI (mem_sInter.2 h))
      (h𝒯 hS).2 j (hj S hS) k hk hkS⟩

/-- The comparative similarity a set of spheres determines (§2.3): `j` is at least as close as `k`
when every sphere containing `k` contains `j`. -/
@[reducible] def similarity (𝒮 : Set (Set W)) : Preorder W where
  le j k := ∀ S ∈ 𝒮, k ∈ S → j ∈ S
  le_refl _ _ _ := id
  le_trans _ _ _ h h' S hS hk := h S hS (h' S hS hk)

theorem similarity_le_iff : (similarity 𝒮).le j k ↔ ∀ S ∈ 𝒮, k ∈ S → j ∈ S := Iff.rfl

theorem total_similarity (h : IsChain (· ⊆ ·) 𝒮) : Std.Total (similarity 𝒮).le where
  total j k := or_iff_not_imp_left.2 fun hjk S hS hj ↦ by
    obtain ⟨T, hT, hkT, hjT⟩ : ∃ T ∈ 𝒮, k ∈ T ∧ j ∉ T := by
      simpa [similarity_le_iff] using hjk
    exact (h.total hS hT).elim (fun hST ↦ absurd (hST hj) hjT) (· hkT)

theorem spheres_similarity (h : IsSystemOfSpheres 𝒮) : spheres (⋃₀ 𝒮) (similarity 𝒮) = 𝒮 := by
  ext S
  refine ⟨fun hS ↦ ?_, fun hS ↦ ⟨subset_sUnion_of_mem hS, fun j hj k _ hk ↦
    ((similarity 𝒮).lt_iff_le_not_ge _ _).2 ⟨fun T hT hkT ↦ (h.isChain.total hS hT).elim
      (fun hST ↦ hST hj) (fun hTS ↦ absurd (hTS hkT) hk), fun hkj ↦ hk (hkj S hS hj)⟩⟩⟩
  -- each world of `S` lies in the smallest sphere containing it, which `S` includes
  have key (j) (hj : j ∈ S) : ∃ T ∈ 𝒮, T ⊆ S ∧ j ∈ T := by
    obtain ⟨T₀, hT₀, hjT₀⟩ := hS.1 hj
    refine ⟨⋂₀ {T ∈ 𝒮 | j ∈ T}, h.sInter_mem (sep_subset _ _) ⟨T₀, hT₀, hjT₀⟩,
      fun x hx ↦ by_contra fun hxS ↦ ?_, mem_sInter.2 fun T hT ↦ hT.2⟩
    obtain ⟨T, hT, hjT, hxT⟩ : ∃ T ∈ 𝒮, j ∈ T ∧ x ∉ T := by
      simpa [similarity_le_iff] using ((similarity 𝒮).lt_iff_le_not_ge _ _).1
        (hS.2 j hj x ⟨T₀, hT₀, hx T₀ ⟨hT₀, hjT₀⟩⟩ hxS) |>.2
    exact hxT (hx T ⟨hT, hjT⟩)
  have hS' : S = ⋃₀ {T ∈ 𝒮 | T ⊆ S} := Subset.antisymm (fun j hj ↦ by
      obtain ⟨T, hT, hTS, hjT⟩ := key j hj
      exact ⟨T, ⟨hT, hTS⟩, hjT⟩) (sUnion_subset fun _ hT ↦ hT.2)
  rw [hS']
  exact h.sUnion_mem (sep_subset _ _)

/-- The systems of spheres are exactly the sets of spheres that total similarity preorders
determine over the accessible worlds (§2.3). -/
theorem isSystemOfSpheres_iff :
    IsSystemOfSpheres 𝒮 ↔ ∃ (A : Set W) (r : Preorder W), Std.Total r.le ∧ spheres A r = 𝒮 :=
  ⟨fun h ↦ ⟨_, _, total_similarity h.isChain, spheres_similarity h⟩,
    fun ⟨_, _, _, h⟩ ↦ h ▸ isSystemOfSpheres_spheres⟩

-- §2.3: on the accessible worlds the correspondence is one-to-one
theorem similarity_spheres_le_iff {r : Preorder W} [Std.Total r.le] (hj : j ∈ A) (hk : k ∈ A) :
    (similarity (spheres A r)).le j k ↔ r.le j k :=
  ⟨fun h ↦ (h _ (setOf_le_mem_spheres k) ⟨hk, r.le_refl k⟩).2,
    fun h _ hS hkS ↦ mem_of_mem_spheres hS hkS hj h⟩

/-! ### Truth conditions by spheres -/

-- §1.3
theorem mem_variablyStrictImp_iff_spheres [Std.Total (ord i).le] :
    i ∈ variablyStrictImp access ord p q ↔ (∀ S ∈ spheres (access i) (ord i), Disjoint S p) ∨
      ∃ S ∈ spheres (access i) (ord i), (S ∩ p).Nonempty ∧ S ∩ p ⊆ q := by
  constructor
  · intro h
    rcases (access i ∩ p).eq_empty_or_nonempty with he | ⟨u, hu⟩
    · exact .inl fun S hS ↦ disjoint_iff_inter_eq_empty.2
        (subset_empty_iff.1 (he ▸ inter_subset_inter_left p hS.1))
    obtain ⟨b, hb, -, hbq⟩ := h u hu
    exact .inr ⟨_, setOf_le_mem_spheres b, ⟨b, ⟨hb.1, (ord i).le_refl b⟩, hb.2⟩,
      fun x hx ↦ hbq x ⟨hx.1.1, hx.2⟩ hx.1.2⟩
  · rintro (h | ⟨S, hS, ⟨x, hxS, hxp⟩, hSq⟩) u hu
    · exact absurd hu.2 (disjoint_left.1 (h _ self_mem_spheres) hu.1)
    by_cases huS : u ∈ S
    · exact ⟨u, hu, (ord i).le_refl u, fun c hc hcu ↦
        hSq ⟨mem_of_mem_spheres hS huS hc.1 hcu, hc.2⟩⟩
    · exact ⟨x, ⟨hS.1 hxS, hxp⟩, ((ord i).lt_iff_le_not_ge _ _).1 (hS.2 x hxS u hu.1 huS) |>.1,
        fun c hc hcx ↦ hSq ⟨mem_of_mem_spheres hS hxS hc.1 hcx, hc.2⟩⟩

-- §1.5
theorem mem_might_iff_spheres {access : W → Set W} {ord : W → Preorder W} {w : W}
    [Std.Total (ord w).le] :
    w ∈ might (variablyStrictImp access ord) p q ↔
      (∃ S ∈ spheres (access w) (ord w), (S ∩ p).Nonempty) ∧
        ∀ S ∈ spheres (access w) (ord w), (S ∩ p).Nonempty → (S ∩ (p ∩ q)).Nonempty := by
  simp only [mem_might, mem_variablyStrictImp_iff_spheres, not_or, not_forall, not_exists,
    not_and, exists_prop, not_disjoint_iff_nonempty_inter, subset_compl_iff_disjoint_right,
    ← inter_assoc]

/-! ### Comparative possibility (§2.5) -/

-- p. 53
theorem forall_spheres_iff_lewis {r : Preorder W} [Std.Total r.le] :
    (∀ S ∈ spheres A r, (S ∩ q).Nonempty → (S ∩ p).Nonempty) ↔
      ComparativePossibility.Lewis r.le (A ∩ p) (A ∩ q) := by
  refine ⟨fun h b hb ↦ ?_, fun h S hS ⟨b, hbS, hbq⟩ ↦ ?_⟩
  · obtain ⟨a, ⟨ha, hab⟩, hap⟩ := h _ (setOf_le_mem_spheres b)
      ⟨b, ⟨hb.1, r.le_refl b⟩, hb.2⟩
    exact ⟨a, ⟨ha, hap⟩, hab⟩
  · obtain ⟨a, ⟨ha, hap⟩, hab⟩ := h ⟨hS.1 hbS, hbq⟩
    exact ⟨a, mem_of_mem_spheres hS hbS ha hab, hap⟩

-- p. 53: the counterfactual defined from comparative possibility
theorem mem_variablyStrictImp_iff_asymmRel_lewis [Std.Total (ord i).le] :
    i ∈ variablyStrictImp access ord p q ↔ access i ∩ p = ∅ ∨
      AsymmRel (ComparativePossibility.Lewis (ord i).le) (access i ∩ p ∩ q) ((access i ∩ p) \ q) :=
  letI := ord i
  ComparativePossibility.mem_atBotOn_iff_asymmRel_lewis

-- p. 54: `φ ≼ ψ` is `(φ ∨ ψ) ◇⇒ φ`, the *might* counterfactual unless its antecedent is
-- impossible (§1.6)
theorem lewis_iff_might {access : W → Set W} {ord : W → Preorder W} {w : W}
    [Std.Total (ord w).le] :
    ComparativePossibility.Lewis (ord w).le (access w ∩ p) (access w ∩ q) ↔
      ((access w ∩ (p ∪ q)).Nonempty → w ∈ might (variablyStrictImp access ord) (p ∪ q) p) := by
  rw [← forall_spheres_iff_lewis, mem_might_iff_spheres, union_inter_cancel_left]
  refine ⟨fun h hne ↦ ⟨⟨_, self_mem_spheres, hne⟩, fun S hS ⟨x, hxS, hx⟩ ↦
      hx.elim (fun hxp ↦ ⟨x, hxS, hxp⟩) fun hxq ↦ h S hS ⟨x, hxS, hxq⟩⟩,
    fun h S hS ⟨x, hxS, hxq⟩ ↦ (h ⟨x, hS.1 hxS, .inr hxq⟩).2 S hS ⟨x, hxS, .inr hxq⟩⟩

/-! ### Sobel sequences

Otto's coming would have made the party lively, Otto's and Anna's dreary, and Waldo's as well
lively again (§1.2). -/

-- p. 11: if Otto and Anna had come, the cow would have jumped over the moon
theorem mem_strictImp_of_sobel {s t : Set W} (h₁ : i ∈ strictImp access p q)
    (h₂ : i ∈ strictImp access (p ∩ s) qᶜ) : i ∈ strictImp access (p ∩ s) t :=
  fun _ hx ↦ absurd (h₁ ⟨hx.1, hx.2.1⟩) (h₂ hx)

/-- Similarity of the worlds `0, 1, 2, …` by distance. -/
abbrev natSim (w : ℕ) : Preorder ℕ := Preorder.lift (Nat.dist · w)

/-- Where no guest came, with the guests arriving in order and the party lively when an odd number
came, if the first `n` guests had come the party would have been lively for odd `n` and dreary for
even `n`, and not the other way: every stage of the Sobel sequence holds, however far it is
prolonged (§1.2). -/
theorem sobel (n : ℕ) :
    0 ∈ variablyStrictImp (fun _ ↦ .univ) natSim (Ici n) {v | Odd v ↔ Odd n} ∧
      0 ∉ variablyStrictImp (fun _ ↦ .univ) natSim (Ici n) {v | Odd v ↔ Odd n}ᶜ := by
  have hle (u v : ℕ) : (natSim 0).le u v ↔ u ≤ v := by
    change Nat.dist u 0 ≤ Nat.dist v 0 ↔ _
    rw [Nat.dist_zero_right, Nat.dist_zero_right]
  have hpure : atBotOn (Nat.dist · 0) (Ici n) = pure n :=
    atBotOn_eq_pure (mem_Ici.2 le_rfl) (fun u hu ↦ (hle n u).2 hu)
      fun u hu hun ↦ le_antisymm ((hle u n).1 hun) hu
  simp [mem_variablyStrictImp, hpure]

/-! ### The Limit Assumption

Lengths of a line, the actual one at most an inch, similar to the actual one as their lengths are
close to it (§1.4). -/

section Line

/-- Similarity of lengths by distance. -/
abbrev lineSim (w : ℝ) : Preorder ℝ := Preorder.lift fun x ↦ |x - w|

variable {a : ℝ}

private theorem lineSim_le_iff (ha : a ≤ 1) {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    (lineSim a).le x y ↔ x ≤ y := by
  change |x - a| ≤ |y - a| ↔ x ≤ y
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith), sub_le_sub_iff_right]

/-- *If the line were over an inch long, it would be `q`* is true when `q` holds of every length
over an inch close enough to an inch: what holds toward the closest lengths over an inch is what
holds in the neighbourhoods of an inch on the right (§1.4). -/
theorem atBotOn_line (ha : a ≤ 1) : atBotOn (fun x ↦ |x - a|) (Ioi 1) = 𝓝[>] 1 := by
  ext t
  rw [mem_atBotOn_iff_exists nonempty_Ioi,
    mem_nhdsGT_iff_exists_Ioc_subset]
  exact exists_congr fun v ↦ and_congr_right fun hv ↦
    ⟨fun h x hx ↦ h x hx.1 ((lineSim_le_iff ha hx.1 hv).2 hx.2),
      fun h x hx hxv ↦ h ⟨hx, (lineSim_le_iff ha hx hv).1 hxv⟩⟩

-- p. 20: no closest length over an inch
theorem minimals_lineSim (ha : a ≤ 1) : (lineSim a).minimals (Ioi 1) = ∅ :=
  eq_empty_of_forall_notMem fun m hm ↦ lt_irrefl m <| (setOf_minimalFor_subset_of_mem_atBotOn
    (f := fun x ↦ |x - a|) (t := Ioo 1 m) (by rw [atBotOn_line ha]; exact Ioo_mem_nhdsGT hm.1)
    hm).2

theorem closestImp_line (ha : a ≤ 1) (q : Set ℝ) : a ∈ closestImp lineSim (Ioi 1) q :=
  mem_closestImp_of_closest_eq_empty (minimals_lineSim ha)

theorem not_mem_variablyStrictImp_line_two (ha : a ≤ 1) :
    a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) {2} := fun h ↦ by
  rw [mem_variablyStrictImp, univ_inter, atBotOn_lift, atBotOn_line ha] at h
  obtain ⟨_, rfl, hx⟩ := Filter.nonempty_of_mem (inter_mem h (Ioo_mem_nhdsGT one_lt_two))
  exact lt_irrefl _ hx.2

-- §3.4: conditional excluded middle at an antecedent
theorem forall_mem_variablyStrictImp_or_compl_iff :
    (∀ q, i ∈ variablyStrictImp access ord p q ∨ i ∈ variablyStrictImp access ord p qᶜ) ↔
      @atBotOn W W (ord i) id (access i ∩ p) = ⊥ ∨
        IsAtom (@atBotOn W W (ord i) id (access i ∩ p)) :=
  show (∀ q, q ∈ @atBotOn W W (ord i) id _ ∨ qᶜ ∈ @atBotOn W W (ord i) id _) ↔ _ from
    Filter.forall_mem_or_compl_mem_iff

-- Conditional excluded middle fails for the line although lengths over an inch are never tied.
theorem not_cem_line (ha : a ≤ 1) :
    (∀ x ∈ Ioi (1 : ℝ), ∀ y ∈ Ioi (1 : ℝ), (lineSim a).le x y → (lineSim a).le y x → x = y) ∧
      a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) (range ((↑) : ℚ → ℝ)) ∧
      a ∉ variablyStrictImp (fun _ ↦ .univ) lineSim (Ioi 1) (range ((↑) : ℚ → ℝ))ᶜ := by
  refine ⟨fun x hx y hy hxy hyx ↦
    ((lineSim_le_iff ha hx hy).1 hxy).antisymm ((lineSim_le_iff ha hy hx).1 hyx), ?_, ?_⟩ <;>
    rw [mem_variablyStrictImp, univ_inter, atBotOn_lift, atBotOn_line ha,
      mem_nhdsGT_iff_exists_Ioc_subset] <;>
    rintro ⟨u, hu, hsub⟩
  · obtain ⟨c, hc, h1c, hcu⟩ := exists_irrational_btwn hu
    exact hc (hsub ⟨h1c, hcu.le⟩)
  · obtain ⟨c, h1c, hcu⟩ := exists_rat_btwn hu
    exact hsub ⟨h1c, hcu.le⟩ ⟨c, rfl⟩

end Line

/-! ### Stalnaker's theory -/

/-- Stalnaker's Assumption at `i` (§3.4): an antecedent true at some accessible world has exactly
one closest accessible antecedent-world. -/
def StalnakerAssumption (access : I → Set W) (ord : I → Preorder W) (i : I) : Prop :=
  ∀ p : Set W, (access i ∩ p).Nonempty → ∃ v, (ord i).minimals (access i ∩ p) = {v}

-- p. 78: Stalnaker's Assumption implies the Limit Assumption
theorem StalnakerAssumption.limit (h : StalnakerAssumption access ord i) (B : Set W)
    (hB : (access i ∩ B).Nonempty) : ((ord i).minimals (access i ∩ B)).Nonempty :=
  let ⟨v, hv⟩ := h B hB
  ⟨v, hv ▸ rfl⟩

/-- Stalnaker's Assumption holds exactly when similarity well-orders the accessible worlds: it is
linear on them, and every nonempty set of them has a closest member (§3.4). -/
theorem stalnakerAssumption_iff [Std.Total (ord i).le] :
    StalnakerAssumption access ord i ↔
      (∀ j ∈ access i, ∀ k ∈ access i, (ord i).le j k → (ord i).le k j → j = k) ∧
        ∀ B ⊆ access i, B.Nonempty → ∃ b ∈ B, ∀ x ∈ B, (ord i).le b x := by
  have hmin (s : Set W) (a : W) : a ∈ (ord i).minimals s ↔ a ∈ s ∧ ∀ b ∈ s, (ord i).le a b :=
    Preorder.mem_minimals_iff_forall_le
  refine ⟨fun h ↦ ⟨fun j hj k hk hjk hkj ↦ ?_, fun B hB hne ↦ ?_⟩, fun ⟨hanti, hleast⟩ p hp ↦ ?_⟩
  · -- two tied accessible worlds are both closest among themselves
    obtain ⟨v, hv⟩ := h {j, k} ⟨j, hj, .inl rfl⟩
    have hjv : j ∈ (ord i).minimals (access i ∩ {j, k}) := (hmin _ _).2 ⟨⟨hj, .inl rfl⟩,
      fun y hy ↦ by rcases hy.2 with rfl | rfl; exacts [(ord i).le_refl _, hjk]⟩
    have hkv : k ∈ (ord i).minimals (access i ∩ {j, k}) := (hmin _ _).2 ⟨⟨hk, .inr rfl⟩,
      fun y hy ↦ by rcases hy.2 with rfl | rfl; exacts [hkj, (ord i).le_refl _]⟩
    rw [hv] at hjv hkv
    exact (mem_singleton_iff.1 hjv).trans (mem_singleton_iff.1 hkv).symm
  · rw [← inter_eq_right.2 hB] at hne ⊢
    obtain ⟨v, hv⟩ := h B hne
    exact ⟨v, (hmin _ _).1 (hv ▸ mem_singleton v)⟩
  · obtain ⟨b, hb, hbl⟩ := hleast _ inter_subset_left hp
    refine ⟨b, eq_singleton_iff_unique_mem.2 ⟨(hmin _ _).2 ⟨hb, hbl⟩, fun m hm ↦ ?_⟩⟩
    have hm' := (hmin _ _).1 hm
    exact hanti m hm'.1.1 b hb.1 (hm'.2 b hb) (hbl m hm'.1)

-- §3.4: if Bizet and Verdi were compatriots
theorem not_cem_of_tie {v v' : W} (hv : v ∈ (ord i).minimals (access i ∩ p))
    (hv' : v' ∈ (ord i).minimals (access i ∩ p)) (hq : v ∈ q) (hq' : v' ∉ q) :
    i ∉ variablyStrictImp access ord p q ∧ i ∉ variablyStrictImp access ord p qᶜ :=
  ⟨fun h ↦ hq' (variablyStrictImp_subset_orderingImp h hv'),
    fun h ↦ variablyStrictImp_subset_orderingImp h hv hq⟩

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
      eval access ord V B ∈ @atBotOn W W (ord w) id (access w ∩ eval access ord V A) :=
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
centering with Stalnaker's Assumption for VCS. -/
def VLogic.Holds (access : W → Set W) (ord : W → Preorder W) : VLogic → Prop
  | .VW => (∀ w, w ∈ access w) ∧ ∀ w v, (ord w).le w v
  | .VC => (∀ w, w ∈ access w) ∧ IsCentered ord
  | .VCS => ((∀ w, w ∈ access w) ∧ IsCentered ord) ∧ ∀ w, StalnakerAssumption access ord w

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
  ∀ {W : Type u} {access : W → Set W} {ord : W → Preorder W} [∀ w, Std.Total (ord w).le],
    L.Holds access ord → ∀ V : α → Set W, eval access ord V A = Set.univ

/-- Lewis's axiomatizations of the V-logics with the counterfactual primitive are sound (§6.1). -/
theorem Provable.sound {A : Formula α} (h : Provable L A) : Valid.{u} L A := by
  intro W access ord _ hL V
  refine Set.eq_univ_of_forall fun w ↦ ?_
  induction h generalizing w with
  | taut h => exact h (fun B ↦ w ∈ eval access ord V B) (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl
  | a3 φ =>
    letI := ord w
    rw [mem_eval_corner]
    exact mem_of_superset self_mem_atBotOn Set.inter_subset_right
  | a4 φ ψ =>
    letI := ord w
    rw [mem_eval_imp, mem_eval_corner, mem_eval_corner, eval_neg]
    intro h
    have hbot : (∅ : Set W) ∈ atBotOn id (access w ∩ (eval access ord V φ)ᶜ) := by
      simpa using inter_mem h (mem_of_superset self_mem_atBotOn Set.inter_subset_right)
    have hemp : access w ∩ (eval access ord V φ)ᶜ = ∅ := Set.not_nonempty_iff_eq_empty.1
      fun hne ↦ (atBotOn_neBot_iff.2 hne).ne (empty_mem_iff_bot.1 hbot)
    exact mem_of_superset self_mem_atBotOn fun x hx ↦
      by_contra fun hxφ ↦ Set.eq_empty_iff_forall_notMem.1 hemp x ⟨hx.1, hxφ⟩
  | a5 φ ψ χ =>
    letI := ord w
    simp only [Formula.or, mem_eval_imp, eval_neg, Set.mem_compl_iff]
    intro hfr
    have e : atBotOn id (access w ∩ eval access ord V φ ∩ eval access ord V ψ) =
        atBotOn id (access w ∩ eval access ord V φ) ⊓ 𝓟 (eval access ord V ψ) :=
      atBotOn_inter_of_frequently hfr
    rw [mem_eval_iff, mem_eval_corner, mem_eval_corner, eval_and, ← Set.inter_assoc, e,
      mem_inf_principal]
    rfl
  | a6 φ ψ =>
    rw [mem_eval_imp, mem_eval_corner, mem_eval_imp]
    intro h hφ
    obtain ⟨v, -, -, hvψ⟩ := h w ⟨hL.mem w, hφ⟩
    exact hvψ w ⟨hL.mem w, hφ⟩ (hL.le w v)
  | a7 φ ψ hL' =>
    letI := ord w
    rw [mem_eval_imp, eval_and, mem_eval_corner]
    rintro ⟨hφ, hψ⟩
    have hc := hL.isCentered hL'
    have hw : w ∈ access w ∩ eval access ord V φ := ⟨hL.mem w, hφ⟩
    refine (mem_atBotOn_iff_of_least hw fun v _ ↦ hc.le w v).2 fun x _ hxw ↦ ?_
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
      letI := ord w
      have hv' : {x | MinimalFor (· ∈ access w ∩ eval access ord V φ) id x} = {v} := hv
      rw [atBotOn_eq_principal (f := id) fun u hu ↦
        ⟨v, hmin, (Preorder.mem_minimals_iff_forall_le.1 hmin).2 u hu⟩, hv',
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

-- Every theorem of Stalnaker's C2 is valid under centering and Stalnaker's Assumption, since the
-- Assumption makes the closest world a selection function in Stalnaker's sense (p. 78).
theorem valid_vcs_of_c2 {A : Formula α} (h : Stalnaker1968.Provable A) : Valid.{u} .VCS A := by
  intro W access ord _ ⟨⟨hR, hc⟩, hS⟩ V
  rw [eval_eq_formula_eval fun w ↦ (hS w).limit]
  exact h.sound (Stalnaker1968.isSelectionFunction_minimals hR hc hS) V

/-- Comparative similarity from `w` under which every other world is equally far. -/
abbrev tieSim (w : Fin 3) : Preorder (Fin 3) := Preorder.lift fun v ↦ if v = w then (0 : ℕ) else 1

-- §3.4: conditional excluded middle is not a theorem of VC
theorem not_provable_vc_cem :
    ¬ Provable .VC (((Formula.atom 0 : Formula (Fin 2)).corner (.atom 1)).or
      ((Formula.atom 0).corner (Formula.atom 1).neg)) := fun h ↦ by
  have hc : IsCentered tieSim := fun w w' hne ↦ by
    show (if w = w then (0 : ℕ) else 1) < if w' = w then 0 else 1
    simp [Ne.symm hne]
  have hL : VLogic.Holds (fun _ : Fin 3 ↦ Set.univ) tieSim .VC := ⟨fun _ ↦ trivial, hc⟩
  have h0 := h.sound hL ![{1, 2}, {1}]
  have hmem : ∀ v : Fin 3, v ∈ (tieSim 0).minimals (Set.univ ∩ {1, 2}) ↔ v = 1 ∨ v = 2 := by
    simp only [Preorder.mem_minimals_lift, Set.univ_inter, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    decide
  have ht := not_cem_of_tie (access := fun _ : Fin 3 ↦ Set.univ) (ord := tieSim) (i := 0)
    (q := {1}) ((hmem 1).2 (.inl rfl)) ((hmem 2).2 (.inr rfl)) rfl (by decide)
  have h0' : (0 : Fin 3) ∈ eval (fun _ ↦ Set.univ) tieSim ![{1, 2}, {1}]
      (((Formula.atom 0 : Formula (Fin 2)).corner (.atom 1)).or
        ((Formula.atom 0).corner (Formula.atom 1).neg)) := by
    rw [h0]; exact Set.mem_univ 0
  exact ht.2 (h0' ht.1)

end VLogic

end Lewis1973b
