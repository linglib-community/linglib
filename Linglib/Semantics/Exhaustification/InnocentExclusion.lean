module

public import Linglib.Semantics.Exhaustification.Alternatives
public import Linglib.Semantics.Exhaustification.Excluder
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Minimal
public import Mathlib.Order.SupClosed

/-!
# Innocent exclusion

A set of alternatives is a consistent exclusion when denying all of them is consistent with the
prejacent. Fox calls an alternative innocently excludable when it belongs to every maximal
consistent exclusion, and the exhaustifier `exhIE` asserts the prejacent and denies the
innocently excludable alternatives. The maximal consistent exclusions are the sets of
alternatives false at the minimal worlds of `Alternatives`, so an alternative is innocently
excludable iff it fails at every minimal world. Hence minimal-world exhaustification entails
innocent exclusion, with equality when the alternatives are closed under conjunction, and closing
them under disjunction changes neither exhaustifier. Innocent exclusion is `exh` with its
alternative set selected by innocent excludability.

## Main definitions

* `IsConsistentExclusion`: a set of alternatives whose joint denial is consistent with the
  prejacent.
* `IsInnocentlyExcludable`, `exhIE`: membership in every maximal consistent exclusion, and the
  exhaustifier denying such alternatives.

## Main results

* `maximal_sdiff_satisfied_iff`, `Maximal.exists_eq_sdiff_satisfied`: the maximal consistent
  exclusions are the sets of alternatives false at a minimal world.
* `isInnocentlyExcludable_iff_exhMW_subset_compl`
* `exhIE_eq_exh`, `exhIE_eq_exh_of_nonempty`, `exhIE_eq_sdiff_of_maximal_unique`
* `exh_nonempty_iff`, `mem_exhIE_iff_subset_sUnion`: `exh` is consistent iff some prejacent world
  verifies the least set of alternatives, and `exhIE` keeps the worlds verifying only alternatives
  in a minimal verified set
* `exhMW_eq_exhIE_of_infClosed`, `exhIE_sUnion_image_powerset`

## References

* [fox-2007]
* [spector-2016]
-/

@[expose] public section

namespace Exhaustification

open Set

variable {World : Type*} (ALT : Set (Set World)) (φ : Set World)

/-! ### Consistent exclusions -/

/-- A set of alternatives is a consistent exclusion when denying all of them is consistent with
the prejacent. -/
def IsConsistentExclusion (X : Set (Set World)) : Prop :=
  X ⊆ ALT ∧ (φ \ ⋃₀ X).Nonempty

/-- An alternative is innocently excludable when it belongs to every maximal consistent
exclusion. -/
def IsInnocentlyExcludable (a : Set World) : Prop :=
  a ∈ ALT ∧ ∀ X, Maximal (IsConsistentExclusion ALT φ) X → a ∈ X

/-- The innocent-exclusion exhaustifier asserts the prejacent and denies every innocently
excludable alternative. -/
def exhIE : Set World :=
  {u ∈ φ | ∀ a, IsInnocentlyExcludable ALT φ a → u ∉ a}

theorem mem_exhIE_iff {u : World} :
    u ∈ exhIE ALT φ ↔ u ∈ φ ∧ ∀ a, IsInnocentlyExcludable ALT φ a → u ∉ a :=
  Iff.rfl

theorem exhIE_subset : exhIE ALT φ ⊆ φ := fun _ h ↦ h.1

variable {ALT φ}

theorem IsConsistentExclusion.mono {X Y : Set (Set World)} (hY : IsConsistentExclusion ALT φ Y)
    (hXY : X ⊆ Y) : IsConsistentExclusion ALT φ X :=
  ⟨hXY.trans hY.1, hY.2.mono (sdiff_subset_sdiff_right (sUnion_mono hXY))⟩

theorem IsInnocentlyExcludable.of_forall_maximal {a : Set World} (ha : a ∈ ALT)
    (h : ∀ X, Maximal (IsConsistentExclusion ALT φ) X → (φ \ ⋃₀ insert a X).Nonempty) :
    IsInnocentlyExcludable ALT φ a :=
  ⟨ha, fun X hX ↦ hX.mem_of_prop_insert ⟨insert_subset ha hX.1.1, h X hX⟩⟩

theorem Maximal.not_isInnocentlyExcludable {X : Set (Set World)} {a : Set World}
    (hX : Maximal (IsConsistentExclusion ALT φ) X) (ha : a ∉ X) :
    ¬ IsInnocentlyExcludable ALT φ a :=
  fun h ↦ ha (h.2 X hX)

theorem IsInnocentlyExcludable.of_forall_subset_or_notMem {a : Set World} {w : World}
    (ha : a ∈ ALT) (hw : w ∈ φ) (hwa : w ∉ a) (h : ∀ b ∈ ALT, φ ⊆ b ∨ w ∉ b) :
    IsInnocentlyExcludable ALT φ a := by
  refine .of_forall_maximal ha fun X hX ↦ ⟨w, hw, ?_⟩
  rintro ⟨b, hb, hwb⟩
  obtain rfl | hbX := hb
  · exact hwa hwb
  · obtain ⟨v, hv, hvX⟩ := hX.1.2
    exact (h b (hX.1.1 hbX)).elim (fun hφb ↦ hvX ⟨b, hbX, hφb hv⟩) (· hwb)

theorem IsInnocentlyExcludable.of_full_exclusion_consistent {a : Set World} (ha : a ∈ ALT)
    (h : ∃ w ∈ φ, ∀ b ∈ ALT, w ∉ b) : IsInnocentlyExcludable ALT φ a :=
  let ⟨_, hw, hall⟩ := h
  .of_forall_subset_or_notMem ha hw (hall a ha) fun b hb ↦ Or.inr (hall b hb)

theorem IsInnocentlyExcludable.exhIE_subset_compl {a : Set World}
    (h : IsInnocentlyExcludable ALT φ a) : exhIE ALT φ ⊆ aᶜ :=
  fun _ hu ↦ hu.2 a h

theorem IsInnocentlyExcludable.exhIE_subset_compl_exhIE {a : Set World}
    (h : IsInnocentlyExcludable ALT φ a) : exhIE ALT φ ⊆ (exhIE ALT a)ᶜ :=
  h.exhIE_subset_compl.trans (compl_subset_compl.2 (exhIE_subset ALT a))

/-! ### Maximal consistent exclusions and minimal worlds -/

theorem mem_sdiff_satisfied {u : World} {b : Set World} :
    b ∈ ALT \ Preorder.satisfied (· ∈ ·) ALT u ↔ b ∈ ALT ∧ u ∉ b := by
  simp only [Set.mem_sdiff, Preorder.mem_satisfied, not_and]
  exact and_congr_right fun hb ↦ ⟨fun h ↦ h hb, fun h _ ↦ h⟩

theorem isConsistentExclusion_sdiff_satisfied {u : World} (hu : u ∈ φ) :
    IsConsistentExclusion ALT φ (ALT \ Preorder.satisfied (· ∈ ·) ALT u) :=
  ⟨Set.sdiff_subset, u, hu, fun ⟨_, hb, hub⟩ ↦ (mem_sdiff_satisfied.1 hb).2 hub⟩

theorem IsConsistentExclusion.subset_sdiff_satisfied {X : Set (Set World)}
    (hX : IsConsistentExclusion ALT φ X) {u : World} (hu : u ∉ ⋃₀ X) :
    X ⊆ ALT \ Preorder.satisfied (· ∈ ·) ALT u :=
  fun b hb ↦ mem_sdiff_satisfied.2 ⟨hX.1 hb, fun hub ↦ hu ⟨b, hb, hub⟩⟩

/-- The alternatives false at a prejacent world form a maximal consistent exclusion iff the world
is minimal. -/
theorem maximal_sdiff_satisfied_iff {u : World} (hu : u ∈ φ) :
    Maximal (IsConsistentExclusion ALT φ) (ALT \ Preorder.satisfied (· ∈ ·) ALT u) ↔
      IsMinimal ALT φ u := by
  refine ⟨fun hmax ↦ ⟨hu, fun ⟨v, hv, hvu, huv⟩ ↦ huv fun c hc huc ↦ by_contra fun hvc ↦ ?_⟩,
    fun ⟨_, hmin⟩ ↦ maximal_subset_iff'.2 ⟨isConsistentExclusion_sdiff_satisfied hu,
      fun Y ⟨hY, v, hv, hvY⟩ hXY b hb ↦ mem_sdiff_satisfied.2 ⟨hY hb, fun hub ↦ ?_⟩⟩⟩
  · have hle := hmax.2 (isConsistentExclusion_sdiff_satisfied hv) fun b hb ↦
      let ⟨hbA, hub⟩ := mem_sdiff_satisfied.1 hb
      mem_sdiff_satisfied.2 ⟨hbA, fun hvb ↦ hub (hvu b hbA hvb)⟩
    exact (mem_sdiff_satisfied.1 (hle (mem_sdiff_satisfied.2 ⟨hc, hvc⟩))).2 huc
  · exact hmin ⟨v, hv, fun c hc hvc ↦ by_contra fun huc ↦
      hvY ⟨c, hXY (mem_sdiff_satisfied.2 ⟨hc, huc⟩), hvc⟩, fun huv ↦ hvY ⟨b, hb, huv b (hY hb) hub⟩⟩

/-- Every maximal consistent exclusion is the set of alternatives false at a minimal world. -/
theorem Maximal.exists_eq_sdiff_satisfied {X : Set (Set World)}
    (hX : Maximal (IsConsistentExclusion ALT φ) X) :
    ∃ u, IsMinimal ALT φ u ∧ X = ALT \ Preorder.satisfied (· ∈ ·) ALT u := by
  obtain ⟨u, hu, huX⟩ := hX.1.2
  have hXu := hX.1.subset_sdiff_satisfied huX
  have heq := hXu.antisymm (hX.2 (isConsistentExclusion_sdiff_satisfied hu) hXu)
  exact ⟨u, (maximal_sdiff_satisfied_iff hu).1 (heq ▸ hX), heq⟩

variable (ALT φ)

/-- An alternative is innocently excludable iff it fails at every minimal world. -/
theorem isInnocentlyExcludable_iff_exhMW_subset_compl (a : Set World) (ha : a ∈ ALT) :
    IsInnocentlyExcludable ALT φ a ↔ exhMW ALT φ ⊆ aᶜ := by
  refine ⟨fun h u hu ↦ (mem_sdiff_satisfied.1 (h.2 _ ((maximal_sdiff_satisfied_iff hu.1).2 hu))).2,
    fun h ↦ ⟨ha, fun X hX ↦ ?_⟩⟩
  obtain ⟨u, hu, rfl⟩ := Maximal.exists_eq_sdiff_satisfied hX
  exact mem_sdiff_satisfied.2 ⟨ha, h hu⟩

theorem exists_maximal_isConsistentExclusion (hfin : ALT.Finite) (hsat : φ.Nonempty) :
    ∃ X, Maximal (IsConsistentExclusion ALT φ) X :=
  let ⟨_, hu⟩ := exists_minimal_of_finite ALT φ hfin hsat
  ⟨_, (maximal_sdiff_satisfied_iff hu.1).2 hu⟩

theorem not_isInnocentlyExcludable_of_phi_subset {ALT : Set (Set World)} {φ : Set World}
    (hfin : ALT.Finite) (hsat : φ.Nonempty) {a : Set World} (h : φ ⊆ a) :
    ¬ IsInnocentlyExcludable ALT φ a := fun ha ↦
  let ⟨X, hX⟩ := exists_maximal_isConsistentExclusion ALT φ hfin hsat
  let ⟨_, hu, huX⟩ := hX.1.2
  huX ⟨a, ha.2 X hX, h hu⟩

theorem mem_exhIE_of_forall_subset_or_notMem (hfin : ALT.Finite) {u : World} (hu : u ∈ φ)
    (h : ∀ a ∈ ALT, φ ⊆ a ∨ u ∉ a) : u ∈ exhIE ALT φ :=
  ⟨hu, fun a ha ↦ (h a ha.1).resolve_left fun hs ↦
    not_isInnocentlyExcludable_of_phi_subset hfin ⟨u, hu⟩ hs ha⟩

theorem exhIE_eq_of_iff {P : Set World → Prop}
    (h : ∀ q ∈ ALT, IsInnocentlyExcludable ALT φ q ↔ P q) :
    exhIE ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, P q → w ∉ q} := by
  ext w
  exact and_congr_right fun _ ↦ ⟨fun h' q hq hP ↦ h' q ((h q hq).2 hP),
    fun h' q hq ↦ h' q hq.1 ((h q hq.1).1 hq)⟩

/-- Innocent exclusion is exhaustification over the innocently excludable alternatives. -/
theorem exhIE_eq_exh (hfin : ALT.Finite) :
    exhIE ALT φ = exh {a | IsInnocentlyExcludable ALT φ a} φ := by
  ext u
  rw [mem_exhIE_iff, mem_exh]
  refine and_congr_right fun hu ↦ ⟨fun h a ha hua ↦ absurd hua (h a ha), fun h a ha hua ↦ ?_⟩
  exact not_isInnocentlyExcludable_of_phi_subset hfin ⟨u, hu⟩ (h a ha hua) ha

theorem exhIE_preimage_image {β : Type*} {f : World → β} (hφ : f ⁻¹' (f '' φ) = φ)
    (hALT : ∀ a ∈ ALT, f ⁻¹' (f '' a) = a) : f ⁻¹' (f '' exhIE ALT φ) = exhIE ALT φ := by
  refine (subset_preimage_image f _).antisymm' ?_
  rintro u ⟨v, hv, hvu⟩
  refine ⟨by rw [← hφ]; exact ⟨v, hv.1, hvu⟩, fun a ha hua ↦ hv.2 a ha ?_⟩
  rw [← hALT a ha.1]
  exact ⟨u, hua, hvu.symm⟩

theorem exhIE_eq_self_iff : exhIE ALT φ = φ ↔ ∀ a, IsInnocentlyExcludable ALT φ a → Disjoint φ a :=
  ⟨fun h a ha ↦ disjoint_left.2 fun _ hw ↦ (h.ge hw).2 a ha,
    fun h ↦ (exhIE_subset ALT φ).antisymm fun _ hw ↦ ⟨hw, fun a ha ↦ disjoint_left.1 (h a ha) hw⟩⟩

theorem exhIE_empty : exhIE ∅ φ = φ :=
  (exhIE_eq_self_iff ∅ φ).2 fun _ h ↦ h.1.elim

/-- Exhaustification is antitone in the innocently excludable alternatives, more of them giving a
stronger result. -/
theorem exhIE_subset_exhIE {ALT' : Set (Set World)}
    (h : ∀ q, IsInnocentlyExcludable ALT' φ q → IsInnocentlyExcludable ALT φ q) :
    exhIE ALT φ ⊆ exhIE ALT' φ :=
  fun _ hu ↦ ⟨hu.1, fun q hq ↦ hu.2 q (h q hq)⟩

/-! ### Innocent exclusion and minimal worlds -/

theorem exhMW_subset_exhIE : exhMW ALT φ ⊆ exhIE ALT φ := fun _ hu ↦
  ⟨hu.1, fun a ha ↦ (isInnocentlyExcludable_iff_exhMW_subset_compl ALT φ a ha.1).1 ha hu⟩

theorem exhIE_univ : exhIE univ φ = φ :=
  (exhIE_subset _ _).antisymm ((exhMW_univ φ).ge.trans (exhMW_subset_exhIE _ _))

theorem exh_subset_exhMW : exh ALT φ ⊆ exhMW ALT φ :=
  fun _ ⟨hu, hex⟩ ↦ ⟨hu, fun ⟨_, hv, _, hvu⟩ ↦ hvu fun a ha hau ↦ hex a ha hau hv⟩

theorem exh_subset_exhIE : exh ALT φ ⊆ exhIE ALT φ :=
  (exh_subset_exhMW ALT φ).trans (exhMW_subset_exhIE ALT φ)

/-- With a unique maximal consistent exclusion, innocent exclusion denies exactly its members. -/
theorem exhIE_eq_sdiff_of_maximal_unique {X₀ : Set (Set World)}
    (h₀ : Maximal (IsConsistentExclusion ALT φ) X₀)
    (huniq : ∀ X, Maximal (IsConsistentExclusion ALT φ) X → X = X₀) :
    exhIE ALT φ = φ \ ⋃₀ X₀ := by
  ext u
  simp only [mem_exhIE_iff, Set.mem_sdiff, Set.mem_sUnion, not_exists, not_and]
  exact and_congr_right fun _ ↦ ⟨fun h a ha ↦ h a ⟨h₀.prop.1 ha, fun X hX ↦ huniq X hX ▸ ha⟩,
    fun h a ha ↦ h a (ha.2 X₀ h₀)⟩

/-- When the prejacent is consistent with the denial of every alternative it does not entail,
innocent exclusion denies them all ([fox-2007]). -/
theorem exhIE_eq_exh_of_nonempty (h : (exh ALT φ).Nonempty) : exhIE ALT φ = exh ALT φ := by
  obtain ⟨v, hv, hvex⟩ := h
  refine Subset.antisymm (fun u hu ↦ ⟨exhIE_subset ALT φ hu, fun q hq huq ↦ by_contra fun hφq ↦ ?_⟩)
    (exh_subset_exhIE ALT φ)
  have hIE : IsInnocentlyExcludable ALT φ q :=
    .of_forall_subset_or_notMem hq hv (fun hvq ↦ hφq (hvex q hq hvq))
      fun b hb ↦ or_iff_not_imp_left.2 fun hφb hvb ↦ hφb (hvex b hb hvb)
  exact hu.2 q hIE huq

theorem exhIE_eq_self_of_forall (h : ∀ a ∈ ALT, (φ ∩ a).Nonempty → φ ⊆ a) : exhIE ALT φ = φ :=
  (exhIE_subset ALT φ).antisymm ((exh_eq_self_iff.2 h).ge.trans (exh_subset_exhIE ALT φ))

theorem exhIE_singleton_self : exhIE {φ} φ = φ :=
  exhIE_eq_self_of_forall _ _ fun _ ha _ ↦ (mem_singleton_iff.1 ha).ge

theorem exhIE_pair_sdiff {d : Set World} (hne : (φ \ d).Nonempty) : exhIE {φ, d} φ = φ \ d := by
  have hexh : exh {φ, d} φ = φ \ d := by
    obtain ⟨w, hw, hwd⟩ := hne
    ext u
    simp only [mem_exh, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_sdiff]
    exact and_congr_right fun _ ↦ ⟨fun h hud ↦ hwd (h.2 hud hw), fun hud ↦
      ⟨fun _ ↦ subset_rfl, fun h ↦ (hud h).elim⟩⟩
  rw [exhIE_eq_exh_of_nonempty _ _ (hexh ▸ hne), hexh]

theorem not_isInnocentlyExcludable_of_subset_union (hfin : ALT.Finite) {p q : Set World}
    (hp : p ∈ ALT) (hq : q ∈ ALT) (hcov : φ ⊆ p ∪ q) (hne : (φ \ q).Nonempty) :
    ¬ IsInnocentlyExcludable ALT φ p := by
  obtain ⟨w, hw, hwq⟩ := hne
  obtain ⟨u, hu, huw⟩ := exists_isMinimal_le ALT φ hfin hw
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl ALT φ p hp]
  exact fun h ↦ h hu ((hcov hu.1).resolve_right fun huq ↦ hwq (huw q hq huq))

theorem exhIE_eq_setOf_exhMW_subset_compl :
    exhIE ALT φ = {u | u ∈ φ ∧ ∀ a ∈ ALT, exhMW ALT φ ⊆ aᶜ → u ∉ a} :=
  exhIE_eq_of_iff ALT φ (isInnocentlyExcludable_iff_exhMW_subset_compl ALT φ)

section MinimalCover

variable {ALT φ} {M : Set World}

theorem IsMinimalCover.isInnocentlyExcludable_iff (hM : IsMinimalCover ALT φ M) {a : Set World}
    (ha : a ∈ ALT) : IsInnocentlyExcludable ALT φ a ↔ ∀ v ∈ M, v ∉ a := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl ALT φ a ha, hM.exhMW_eq]
  constructor
  · exact fun h v hv hva ↦ h ⟨hM.mem v hv, v, hv, leALT_refl _ _, leALT_refl _ _⟩ hva
  · rintro h u ⟨_, v, hv, _, huv⟩ hua
    exact h v hv (huv a ha hua)

theorem IsMinimalCover.exhIE_eq (hM : IsMinimalCover ALT φ M) :
    exhIE ALT φ = {u | u ∈ φ ∧ ∀ a ∈ ALT, (∀ v ∈ M, v ∉ a) → u ∉ a} :=
  exhIE_eq_of_iff ALT φ fun _ ha ↦ hM.isInnocentlyExcludable_iff ha

end MinimalCover

/-! ### Closure under conjunction and disjunction -/

/-- With finitely many alternatives closed under conjunction the two exhaustifiers coincide. A
prejacent world above another verifies the conjunction of the alternatives true at it, which
every minimal world falsifies. -/
theorem exhMW_eq_exhIE_of_infClosed (hfin : ALT.Finite) (hinf : InfClosed ALT) :
    exhMW ALT φ = exhIE ALT φ := by
  refine (exhMW_subset_exhIE ALT φ).antisymm fun u hu ↦ ⟨hu.1, fun ⟨v, hv, hvu, huv⟩ ↦ ?_⟩
  have hne : {a ∈ ALT | u ∈ a}.Nonempty := by
    by_contra h
    exact huv fun a ha hua ↦ (h ⟨a, ha, hua⟩).elim
  have hA : ⋂₀ {a ∈ ALT | u ∈ a} ∈ ALT :=
    hinf.sInf_mem_of_nonempty (hfin.subset fun _ h ↦ h.1) hne fun _ h ↦ h.1
  refine hu.2 _ ((isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ hA).2 ?_) fun a ha ↦ ha.2
  rintro w ⟨-, hmin⟩ hwA
  have huw : u ≤[ALT] w := fun a ha hua ↦ hwA a ⟨ha, hua⟩
  exact hmin ⟨v, hv, leALT_trans _ _ _ _ hvu huw, fun hwv ↦ huv (leALT_trans _ _ _ _ huw hwv)⟩

theorem leALT_sUnion_image_powerset {u v : World} :
    (u ≤[sUnion '' 𝒫 ALT] v) ↔ u ≤[ALT] v := by
  refine ⟨fun h a ha hua ↦ ?_, fun h _ ⟨X, hX, hXa⟩ hua ↦ ?_⟩
  · have := h a ⟨{a}, singleton_subset_iff.2 ha, sUnion_singleton a⟩ hua
    exact this
  · subst hXa
    obtain ⟨b, hb, hub⟩ := hua
    exact ⟨b, hb, h b (hX hb) hub⟩

theorem exhMW_sUnion_image_powerset : exhMW (sUnion '' 𝒫 ALT) φ = exhMW ALT φ := by
  unfold exhMW ltALT
  simp only [leALT_sUnion_image_powerset]

/-- Innocent exclusion is unchanged by closing the alternatives under disjunction, since a
disjunction fails at every minimal world iff each disjunct does. -/
theorem exhIE_sUnion_image_powerset : exhIE (sUnion '' 𝒫 ALT) φ = exhIE ALT φ := by
  ext u
  refine and_congr_right fun _ ↦ ⟨fun h a ha ↦ h a ?_, fun h a ha ↦ ?_⟩
  · have ha' : a ∈ sUnion '' 𝒫 ALT := ⟨{a}, singleton_subset_iff.2 ha.1, sUnion_singleton a⟩
    rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha', exhMW_sUnion_image_powerset]
    exact (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha.1).1 ha
  · obtain ⟨X, hX, rfl⟩ := ha.1
    rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha.1,
      exhMW_sUnion_image_powerset] at ha
    rintro ⟨b, hb, hub⟩
    refine h b ((isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (hX hb)).2 ?_) hub
    exact fun w hw hwb ↦ ha hw ⟨b, hb, hwb⟩

theorem exhMW_eq_exhIE_of_infClosed_sUnion_image (hfin : ALT.Finite)
    (hinf : InfClosed (sUnion '' 𝒫 ALT)) : exhMW ALT φ = exhIE ALT φ := by
  rw [← exhMW_sUnion_image_powerset, ← exhIE_sUnion_image_powerset]
  exact exhMW_eq_exhIE_of_infClosed _ _ (hfin.finite_subsets.image _) hinf

/-! ### Verified alternatives

Each operator reads a world only through the alternatives it verifies, and the prejacent only
through the sets of alternatives its worlds verify. `exh` keeps the worlds verifying the least such
set, `exhMW` those verifying a minimal one (`mem_exhMW_iff_minimal`), and `exhIE` those verifying
only alternatives that some minimal verified set contains. -/

section Verified

variable {ALT φ} {w : World}

theorem mem_exh_iff_isLeast :
    w ∈ exh ALT φ ↔
      w ∈ φ ∧ IsLeast (Preorder.satisfied (· ∈ ·) ALT '' φ) (Preorder.satisfied (· ∈ ·) ALT w) := by
  rw [mem_exh]
  refine and_congr_right fun hw ↦ ⟨fun h ↦ ⟨⟨w, hw, rfl⟩, ?_⟩,
    fun ⟨_, h⟩ a ha hwa v hv ↦ (h ⟨v, hv, rfl⟩ ⟨ha, hwa⟩).2⟩
  rintro _ ⟨v, hv, rfl⟩ a ⟨ha, hwa⟩
  exact ⟨ha, h a ha hwa hv⟩

/-- Exhaustification is consistent iff the sets of alternatives the prejacent worlds verify have a
least element. -/
theorem exh_nonempty_iff :
    (exh ALT φ).Nonempty ↔ ∃ P, IsLeast (Preorder.satisfied (· ∈ ·) ALT '' φ) P := by
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨_, (mem_exh_iff_isLeast.1 hw).2⟩, ?_⟩
  rintro ⟨P, ⟨w, hw, rfl⟩, hP⟩
  exact ⟨w, mem_exh_iff_isLeast.2 ⟨hw, ⟨w, hw, rfl⟩, hP⟩⟩

theorem isInnocentlyExcludable_iff_forall_minimal {a : Set World} (ha : a ∈ ALT) :
    IsInnocentlyExcludable ALT φ a ↔
      ∀ P, Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P → a ∉ P := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha]
  refine ⟨?_, fun h u hu hua ↦ h _ ((mem_exhMW_iff_minimal ALT φ).1 hu).2 ⟨ha, hua⟩⟩
  rintro h _ ⟨⟨u, hu, rfl⟩, hmin⟩ ⟨-, hua⟩
  exact h ((mem_exhMW_iff_minimal ALT φ).2 ⟨hu, ⟨u, hu, rfl⟩, hmin⟩) hua

/-- Innocent exclusion keeps the prejacent worlds verifying only alternatives that some minimal
verified set contains. -/
theorem mem_exhIE_iff_subset_sUnion :
    w ∈ exhIE ALT φ ↔ w ∈ φ ∧ Preorder.satisfied (· ∈ ·) ALT w ⊆
      ⋃₀ {P | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P} := by
  rw [mem_exhIE_iff]
  refine and_congr_right fun _ ↦ ⟨fun h a ⟨ha, hwa⟩ ↦ ?_, fun h a ha hwa ↦ ?_⟩
  · by_contra hn
    exact h a ((isInnocentlyExcludable_iff_forall_minimal ha).2 fun P hP haP ↦
      hn ⟨P, hP, haP⟩) hwa
  · obtain ⟨P, hP, haP⟩ := h ⟨ha.1, hwa⟩
    exact (isInnocentlyExcludable_iff_forall_minimal ha.1).1 ha P hP haP

end Verified

end Exhaustification
