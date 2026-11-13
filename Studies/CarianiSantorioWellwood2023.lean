module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Core.Algebra.Order.Group.Indicator
public import Linglib.Semantics.Delineation
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Fragments.English.Adjectives

/-!
# Cariani, Santorio and Wellwood (2023): Positive gradable adjective ascriptions without positive morphemes

Cariani, Santorio and Wellwood give a gradable adjective a background ordering of states, the
states of having some heat for *hot*, and in each context a threshold property, an upward-closed
set of those states. The positive form says that the subject holds a state with the threshold
property, so no covert *pos* is needed; the comparative compares an admissible measure of the
subject's states with the greatest degree of the standard's, after Wellwood, and [does not entail
the positive](##maxComparative_and_not_mem_image). *Barcelona is hot* and *Miami is hotter than
Barcelona* entail *Miami is hot* under every admissible measure
[exactly on a total background](##total_iff_forall_mem_image_of_maxComparative).
Scale-mates share a background and differ in threshold, *hot* [entailing *warm* and not
conversely](##image_Ici_subset_image_Ici_iff) when its threshold lies strictly above. Two states
[meet the same thresholds](##antisymmRel_iff_forall_isUpperSet) iff they are tied, and the
thresholds are [preimages of standards on degrees](##forall_isUpperSet_exists_preimage_iff), as in
the authors' degree-based variant, iff the measure reflects the background.

## Implementation notes

* The states of all holders form a type `S` with the background preorder, and `holder : S → X`
  sends each state to its holder. The presupposition that a state lies in the domain of the
  background is membership in `S`.
* The positive form of `x` is `x ∈ holder '' T` for a threshold `T` with `IsUpperSet T`, and the
  comparative of `a` over `b` is `MaxComparative .gt (holder · = a) (holder · = b) μ`, the
  standard degree being the greatest measure of `b`'s states. An admissible measure is
  `StrictMono μ`, Schwarzschild's monotonicity.
* `holder` need not be injective, since the standard's maximum ranges over several states. The
  converse of the scale-mate entailment and the failure of (19) off a total background need each
  holder to hold one state, the one-to-one thematic relation the paper assumes.

## TODO

* The crispness contrast (8) and the *for*-phrases (33), (34), for which the paper gives no
  semantics.

## References

* [cariani-santorio-wellwood-2023]
* [wellwood-2015]
* [klein-1980]
* [schwarzschild-2002a]
-/

public section

namespace CarianiSantorioWellwood2023

open Set

variable {S X D : Type*} [Preorder S] [Preorder D] {holder : S → X} {μ : S → D} {T : Set S}

/-! ### The positive form and the comparative -/

omit [Preorder S] in
/-- The comparative does not entail the positive form: when `s` and `t` are the only states of
their holders and `s` measures above `t` without the threshold property, the holder of `s` is
hotter than the holder of `t` without being hot. -/
theorem maxComparative_and_not_mem_image {s t : S} (hlt : μ t < μ s) (hsT : s ∉ T)
    (hs : ∀ u, holder u = holder s → u = s) (ht : ∀ u, holder u = holder t → u = t) :
    MaxComparative .gt (holder · = holder s) (holder · = holder t) μ ∧ holder s ∉ holder '' T :=
  ⟨(maxComparative_iff_of_unique (P := (holder · = holder s)) (Q := (holder · = holder t)) rfl hs
      rfl ht).2 hlt,
    fun ⟨u, hu, hus⟩ ↦ hsT (hs u hus ▸ hu)⟩

-- (19), (18)
theorem mem_image_of_maxComparative [@Std.Total S (· ≤ ·)] (hT : IsUpperSet T)
    (hμ : StrictMono μ) {a b : X} (hb : b ∈ holder '' T)
    (h : MaxComparative .gt (holder · = a) (holder · = b) μ) : a ∈ holder '' T :=
  let ⟨_, hs, hsb⟩ := hb
  let ⟨y, hya, hlt⟩ := h.exists_lt hsb
  ⟨y, hT (by_contra fun hn ↦
    (hμ (lt_of_le_not_ge ((total_of _ _ _).resolve_left hn) hn)).not_gt hlt) hs, hya⟩

-- On three heat states `0 < 1 < 2`, Barcelona holding `0` and `1` and Miami `2`, *hot* the
-- states from `1` up: (19a) and (19b) hold, and so (19c).
example :
    let holder : Fin 3 → Bool := fun s ↦ decide (s = 2)
    false ∈ holder '' Ici 1 ∧ MaxComparative .gt (holder · = true) (holder · = false) id ∧
      true ∈ holder '' Ici 1 := by
  intro holder
  have hb : false ∈ holder '' Ici 1 := ⟨1, self_mem_Ici, by decide⟩
  have hc : MaxComparative .gt (holder · = true) (holder · = false) id := by
    refine ⟨1, ⟨⟨1, by decide, rfl⟩, ?_⟩, 2, by decide, by decide⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (by decide : ∀ s : Fin 3, decide (s = 2) = false → s ≤ 1) s hs
  exact ⟨hb, hc, mem_image_of_maxComparative (isUpperSet_Ici 1) strictMono_id hb hc⟩

-- Without admissibility (19) fails on a total background: with the measure reversed on `Bool`,
-- `true` has the property `Ici true` and `false` measures above it.
example :
    (true : Bool) ∈ id '' Ici true ∧ MaxComparative .gt (· = false) (· = true) (fun b : Bool ↦ !b) ∧
      false ∉ id '' Ici true := by
  refine ⟨⟨true, self_mem_Ici, rfl⟩, (maxComparative_eq_iff _ _ _).2 (by decide), ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact absurd (mem_Ici.1 hu) (by decide)

-- (19) off a total background: the holder of `s` is hot at the threshold `Ici s`, and the holder
-- of `t`, measured above it though `s ≤ t` fails, is hotter and not hot.
theorem not_mem_image_Ici_of_not_le {s t : S} (hst : ¬ s ≤ t) (hlt : μ s < μ t)
    (hs : ∀ u, holder u = holder s → u = s) (ht : ∀ u, holder u = holder t → u = t) :
    holder s ∈ holder '' Ici s ∧ MaxComparative .gt (holder · = holder t) (holder · = holder s) μ ∧
      holder t ∉ holder '' Ici s :=
  ⟨⟨s, self_mem_Ici, rfl⟩,
    (maxComparative_iff_of_unique (P := (holder · = holder t)) (Q := (holder · = holder s)) rfl ht
      rfl hs).2 hlt,
    fun ⟨u, hu, hut⟩ ↦ hst (ht u hut ▸ hu)⟩

/-- The inference (19) holds under every admissible measure exactly on a total background, when
each holder holds one state and some admissible measure into a nontrivial linearly ordered
additive group exists. -/
theorem total_iff_forall_mem_image_of_maxComparative {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Nontrivial G] (hinj : holder.Injective) {μ₀ : S → G}
    (hμ₀ : StrictMono μ₀) :
    (∀ s t : S, s ≤ t ∨ t ≤ s) ↔ ∀ μ : S → G, StrictMono μ → ∀ T : Set S, IsUpperSet T →
      ∀ a b, b ∈ holder '' T → MaxComparative .gt (holder · = a) (holder · = b) μ →
        a ∈ holder '' T := by
  refine ⟨fun htot μ hμ T hT a b ↦ ?_, fun h s t ↦ by_contra fun hst ↦ ?_⟩
  · have : @Std.Total S (· ≤ ·) := ⟨htot⟩
    exact mem_image_of_maxComparative hT hμ
  · obtain ⟨hst, hts⟩ := not_or.1 hst
    obtain ⟨μ, hμ, hlt⟩ := hμ₀.exists_strictMono_lt_of_not_ge hts
    obtain ⟨hs, hc, hn⟩ :=
      not_mem_image_Ici_of_not_le hst hlt (fun _ h ↦ hinj h) (fun _ h ↦ hinj h)
    exact hn (h μ hμ _ (isUpperSet_Ici s) _ _ hs hc)

-- With one state per holder, (19) holds under every admissible measure on a linearly ordered
-- additive group, a total background, and fails under some admissible measure on its componentwise
-- plane.
example {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Nontrivial G] :
    ∀ μ : G → G, StrictMono μ → ∀ T : Set G, IsUpperSet T → ∀ a b, b ∈ id '' T →
      MaxComparative .gt (id · = a) (id · = b) μ → a ∈ id '' T :=
  (total_iff_forall_mem_image_of_maxComparative Function.injective_id strictMono_id).1 le_total

example {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {ε : G} (hε : 0 < ε) :
    ¬ ∀ μ : G × G → G, StrictMono μ → ∀ T : Set (G × G), IsUpperSet T → ∀ a b,
      b ∈ id '' T → MaxComparative .gt (id · = a) (id · = b) μ → a ∈ id '' T := fun h ↦ by
  have : Nontrivial G := ⟨0, ε, hε.ne⟩
  have hμ₀ : StrictMono fun p : G × G ↦ p.1 + p.2 := fun p q h ↦
    (Prod.lt_iff.1 h).elim (fun h ↦ add_lt_add_of_lt_of_le h.1 h.2)
      fun h ↦ add_lt_add_of_le_of_lt h.1 h.2
  simpa [Prod.le_def, hε.not_ge] using
    (total_iff_forall_mem_image_of_maxComparative Function.injective_id hμ₀).2 h (ε, 0) (0, ε)

/-! ### States of equal temperature -/

/-- Two states meet the same thresholds iff they are tied, so two cities of equal temperature,
holding one state each, are alike hot in every context iff their states are tied (§4). -/
theorem antisymmRel_iff_forall_isUpperSet {s t : S} :
    AntisymmRel (· ≤ ·) s t ↔ ∀ T : Set S, IsUpperSet T → (s ∈ T ↔ t ∈ T) :=
  ⟨fun h _ hT ↦ ⟨hT h.1, hT h.2⟩, fun h ↦
    ⟨(h _ (isUpperSet_Ici s)).1 self_mem_Ici, (h _ (isUpperSet_Ici t)).2 self_mem_Ici⟩⟩

-- fn. 10
theorem total_of_reflect_le {D : Type*} [LinearOrder D] {μ : S → D}
    (h : ∀ a b, μ a ≤ μ b → a ≤ b) (s t : S) :
    s ≤ t ∨ t ≤ s :=
  (le_total (μ s) (μ t)).imp (h s t) (h t s)

/-! ### Scale-mates -/

/-- The scale-mates (26): with *hot* the states from `u` up, *warm* those from `l` up and one state
per holder, *warm* entails *hot* iff `u ≤ l`, so *hot* entails *warm* alone iff `l < u`. -/
theorem image_Ici_subset_image_Ici_iff (h : holder.Injective) {u l : S} :
    holder '' Ici l ⊆ holder '' Ici u ↔ u ≤ l :=
  (image_subset_image_iff h).trans Ici_subset_Ici

-- (24): the fragment puts *hot* and *warm* on one dimension.
example : English.Adjectives.hot.dimension = English.Adjectives.warm.dimension := rfl

/-! ### Thresholds as degree standards -/

/-- Every threshold is the preimage of an upward-closed standard on the degrees, as in the
degree-based variant (28), iff the measure reflects the background. -/
theorem forall_isUpperSet_exists_preimage_iff :
    (∀ T : Set S, IsUpperSet T → ∃ U : UpperSet D, T = μ ⁻¹' U) ↔ ∀ a b, μ a ≤ μ b → a ≤ b := by
  refine ⟨fun h a b hab ↦ ?_, fun h T hT ↦ ⟨upperClosure (μ '' T), ?_⟩⟩
  · obtain ⟨U, hT⟩ := h (Ici a) (isUpperSet_Ici a)
    exact (Set.ext_iff.1 hT b).2 (U.upper hab ((Set.ext_iff.1 hT a).1 self_mem_Ici))
  · refine Set.ext fun s ↦ ⟨fun hs ↦ subset_upperClosure ⟨s, hs, rfl⟩, ?_⟩
    rintro ⟨_, ⟨t, ht, rfl⟩, hts⟩
    exact hT (h t s hts) ht

/-! ### Thresholds as delineations -/

-- fn. 5, fn. 11
theorem isMonotoneOn_upperSets_iff :
    (Delineation.ofExtension id : Delineation S).IsMonotoneOn {C | IsUpperSet C} ↔
      ∀ s t : S, s ≤ t ∨ t ≤ s := by
  rw [Delineation.isMonotoneOn_ofExtension_iff]
  refine ⟨fun h s t ↦ by_contra fun hst ↦ ?_, fun htot C₁ h₁ C₂ h₂ a b ha hb hb₂ ↦ ?_⟩
  · obtain ⟨hst, hts⟩ := not_or.1 hst
    exact hts (h (Ici s) (isUpperSet_Ici s) (Ici t) (isUpperSet_Ici t) s t le_rfl hst le_rfl)
  · exact (htot a b).elim (fun hab ↦ absurd (h₁ hab ha) hb) fun hba ↦ h₂ hba hb₂

-- §2: on a total background the comparative is the delineation comparative, some threshold
-- holding of `a` and not of `b`.
theorem maxComparative_iff_exists_isUpperSet [@Std.Total S (· ≤ ·)] (hμ : StrictMono μ)
    (hm : Monotone μ) {a b : X} (hb : ∃ δ, IsGreatest (μ '' {s | holder s = b}) δ) :
    MaxComparative .gt (holder · = a) (holder · = b) μ ↔
      ∃ T, IsUpperSet T ∧ a ∈ holder '' T ∧ b ∉ holder '' T := by
  refine ⟨fun ⟨δ, hδ, s, hsa, hlt⟩ ↦ ⟨Ici s, isUpperSet_Ici s, ⟨s, self_mem_Ici, hsa⟩, ?_⟩, ?_⟩
  · rintro ⟨t, hst, htb⟩
    exact ((hδ.2 ⟨t, htb, rfl⟩).trans_lt hlt).not_ge (hm hst)
  · rintro ⟨T, hT, ⟨s, hsT, hsa⟩, hbT⟩
    obtain ⟨δ, hδ⟩ := hb
    obtain ⟨t, htb, rfl⟩ := hδ.1
    have hst : ¬ s ≤ t := fun hst ↦ hbT ⟨t, hT hst hsT, htb⟩
    exact ⟨_, hδ, s, hsa, hμ (lt_of_le_not_ge ((total_of (· ≤ ·) t s).resolve_right hst) hst)⟩

end CarianiSantorioWellwood2023
