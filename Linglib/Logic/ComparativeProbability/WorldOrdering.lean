module

public import Linglib.Logic.ComparativeProbability.Defs
public import Linglib.Semantics.Modality.ComparativePossibility
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic

/-!
# Comparative likelihood from an ordering of worlds

This file reads comparative possibility as comparative likelihood. Lewis's comparative
possibility is a monotone, transitive likelihood order with Halpern's two properties, right-union
and determination by singletons, and a monotone, transitive relation on the subsets of a finite
set is Lewis's comparative possibility of a reflexive relation on worlds exactly when it has both.
Kratzer's revised notion is monotone and qualitatively additive. Holliday and Icard's m-lifting
asks for an injective dominating map where Lewis's notion asks for any dominating map; the
m-lifting of a preorder is a monotone, transitive likelihood order, and on a finite set it
reverses complements.

## Main definitions

* `ComparativeProbability.MatchingLift`: the m-lifting.

## Main statements

* `ComparativeProbability.lewis_iff_exists_dominating`: Lewis's notion by a dominating map.
* `ComparativeProbability.MatchingLift.compl`: the m-lifting of a finite preorder reverses
  complements.
* `ComparativeProbability.exists_eq_lewis_iff`: the representation for Halpern's logic WJR.

## Implementation notes

Complement reversal follows each point of `A \ B` along the dominating injection until it
leaves `A`, the chain construction of Harrison-Trainor, Holliday and Icard's matching argument.

## References

* [lewis-1973b]
* [kratzer-2012]
* [holliday-icard-2013]
* [harrison-trainor-holliday-icard-2018]
* [halpern-2003]
-/

@[expose] public section

namespace ComparativeProbability

open ComparativePossibility

variable {α : Type*} {r : α → α → Prop} {A A' B B' C : Set α} {b : α}

/-! ### Lewis's comparative possibility as likelihood -/

instance [Std.Refl r] : IsLikelihoodMono (Lewis r) := ⟨fun _ _ h ↦ lewis_of_subset h⟩

instance [Nonempty α] : IsNontrivial (Lewis r) :=
  ⟨fun h ↦ Set.univ_nonempty.ne_empty (lewis_empty_left_iff.1 h)⟩

/-- Lewis's comparative possibility is right-union closed, Halpern's axiom `J`. -/
theorem rightUnion_lewis : RightUnion (Lewis r) := fun _ _ _ ↦ Lewis.union

theorem determinedBySingletons_lewis : DeterminedBySingletons (Lewis r) :=
  fun _ _ hAb ↦
    let ⟨a, ha, hab⟩ := hAb rfl
    ⟨a, ha, lewis_singleton_iff.2 ⟨a, rfl, hab⟩⟩

/-- `A` is at least as possible as `B` exactly when some map sends each world of `B` to a world of
`A` that dominates it (Holliday and Icard, p. 524). -/
theorem lewis_iff_exists_dominating :
    Lewis r A B ↔ ∃ f : α → α, ∀ b ∈ B, f b ∈ A ∧ r (f b) b := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ b hb ↦ ⟨f b, hf b hb⟩⟩
  choose! f hf using lewis_iff.1 h
  exact ⟨f, hf⟩

/-! ### Kratzer's revised comparative possibility as likelihood -/

instance : IsLikelihoodMono (Kratzer r) := ⟨fun _ _ h ↦ kratzer_of_subset h⟩

instance : IsQualitativeAdditive (Kratzer r) := ⟨fun _ _ ↦ kratzer_sdiff_sdiff_iff.symm⟩

instance [Nonempty α] : IsNontrivial (Kratzer r) :=
  ⟨fun h ↦ Set.univ_nonempty.ne_empty (kratzer_univ_iff.1 h).symm⟩

/-! ### The m-lifting -/

/-- The m-lifting `MatchingLift r A B` holds when some map injective on `B` sends each world of `B`
to a world of `A` that dominates it (Holliday and Icard, p. 524), Harrison-Trainor, Holliday and
Icard's injection extension (their Definition 3.1, p. 65). -/
def MatchingLift (r : α → α → Prop) (A B : Set α) : Prop :=
  ∃ f : α → α, (∀ b ∈ B, f b ∈ A ∧ r (f b) b) ∧ Set.InjOn f B

theorem MatchingLift.lewis (h : MatchingLift r A B) : Lewis r A B :=
  let ⟨f, hf, _⟩ := h
  lewis_iff_exists_dominating.2 ⟨f, hf⟩

theorem matchingLift_empty (A : Set α) : MatchingLift r A ∅ :=
  ⟨id, fun _ h ↦ h.elim, Set.injOn_empty id⟩

theorem matchingLift_empty_left_iff : MatchingLift r ∅ B ↔ B = ∅ :=
  ⟨fun h ↦ lewis_empty_left_iff.1 h.lewis, by rintro rfl; exact matchingLift_empty ∅⟩

theorem matchingLift_singleton_iff : MatchingLift r A {b} ↔ ∃ a ∈ A, r a b :=
  ⟨fun h ↦ lewis_singleton_iff.1 h.lewis,
    fun ⟨a, ha, hab⟩ ↦ ⟨fun _ ↦ a, fun _ hb ↦ ⟨ha, hb ▸ hab⟩, Set.injOn_singleton _ _⟩⟩

theorem matchingLift_of_subset [Std.Refl r] (h : B ⊆ A) : MatchingLift r A B :=
  ⟨id, fun b hb ↦ ⟨h hb, refl_of r b⟩, Set.injOn_id B⟩

instance [Std.Refl r] : Std.Refl (MatchingLift r) :=
  ⟨fun _ ↦ matchingLift_of_subset subset_rfl⟩

instance [Std.Refl r] : IsLikelihoodMono (MatchingLift r) :=
  ⟨fun _ _ h ↦ matchingLift_of_subset h⟩

instance [Nonempty α] : IsNontrivial (MatchingLift r) :=
  ⟨fun h ↦ Set.univ_nonempty.ne_empty (matchingLift_empty_left_iff.1 h)⟩

theorem MatchingLift.mono_left (h : MatchingLift r A B) (hA : A ⊆ A') : MatchingLift r A' B :=
  let ⟨f, hf, hinj⟩ := h
  ⟨f, fun b hb ↦ ⟨hA (hf b hb).1, (hf b hb).2⟩, hinj⟩

theorem MatchingLift.anti_right (h : MatchingLift r A B) (hB : B' ⊆ B) : MatchingLift r A B' :=
  let ⟨f, hf, hinj⟩ := h
  ⟨f, fun b hb ↦ hf b (hB hb), hinj.mono hB⟩

theorem MatchingLift.trans [IsTrans α r] (hAB : MatchingLift r A B) (hBC : MatchingLift r B C) :
    MatchingLift r A C :=
  let ⟨f, hf, hfinj⟩ := hAB
  let ⟨g, hg, hginj⟩ := hBC
  ⟨f ∘ g, fun c hc ↦ ⟨(hf _ (hg c hc).1).1, _root_.trans (hf _ (hg c hc).1).2 (hg c hc).2⟩,
    hfinj.comp hginj fun c hc ↦ (hg c hc).1⟩

instance [IsTrans α r] : IsTrans (Set α) (MatchingLift r) :=
  ⟨fun _ _ _ ↦ MatchingLift.trans⟩

theorem MatchingLift.ncard_le [Finite α] (h : MatchingLift r A B) : B.ncard ≤ A.ncard :=
  let ⟨f, hf, hinj⟩ := h
  Set.ncard_le_ncard_of_injOn f (fun b hb ↦ (hf b hb).1) hinj

/-! #### Complement reversal

A dominating injection `f : A → B` is followed from each point `p ∈ A \ B`: the chain
`p, f p, f (f p), …` stays above `p`, cannot revisit `A` forever when `α` is finite, and
chains from distinct origins never merge, because `f` is injective on `A` and no origin
lies in the image `B`. Sending `p` to the first point of its chain outside `A`, and fixing
the points outside `A ∪ B`, is a dominating injection `Bᶜ → Aᶜ`. -/

section Compl

variable {f : α → α}

private theorem iterate_mem_of_ne_zero (hfB : Set.MapsTo f A B) {p : α} {n : ℕ} (hn : n ≠ 0)
    (hA : ∀ m < n, f^[m] p ∈ A) : f^[n] p ∈ B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Function.iterate_succ_apply']
  exact hfB (hA m m.lt_succ_self)

private theorem eq_of_iterate_eq (hinj : Set.InjOn f A) {x y : α} {n : ℕ}
    (hx : ∀ m < n, f^[m] x ∈ A) (hy : ∀ m < n, f^[m] y ∈ A) (h : f^[n] x = f^[n] y) : x = y := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
    exact ih (fun m hm ↦ hx m (by omega)) (fun m hm ↦ hy m (by omega))
      (hinj (hx n (by omega)) (hy n (by omega)) h)

private theorem exists_iterate_notMem [Finite α] (hfB : Set.MapsTo f A B) (hinj : Set.InjOn f A)
    {p : α} (hp : p ∉ B) : ∃ n, f^[n] p ∉ A := by
  by_contra h
  push Not at h
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun n ↦ f^[n] p
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm heq.symm (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  rw [add_assoc, Function.iterate_add_apply] at heq
  have hpd : p = f^[d + 1] p := eq_of_iterate_eq hinj (fun m _ ↦ h m)
    (fun m _ ↦ by rw [← Function.iterate_add_apply]; exact h _) heq
  have := iterate_mem_of_ne_zero hfB d.succ_ne_zero fun m _ ↦ h m
  rw [← hpd] at this
  exact hp this

private theorem chain_origin_eq (hfB : Set.MapsTo f A B) (hinj : Set.InjOn f A) {p₁ p₂ : α}
    {k₁ k₂ : ℕ} (hp₁ : p₁ ∉ B) (hp₂ : p₂ ∉ B) (hk₁ : ∀ m < k₁, f^[m] p₁ ∈ A)
    (hk₂ : ∀ m < k₂, f^[m] p₂ ∈ A) (h : f^[k₁] p₁ = f^[k₂] p₂) : p₁ = p₂ := by
  wlog hle : k₁ ≤ k₂ generalizing p₁ p₂ k₁ k₂
  · exact (this hp₂ hp₁ hk₂ hk₁ h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Function.iterate_add_apply] at h
  have hpd : p₁ = f^[d] p₂ := eq_of_iterate_eq hinj hk₁
    (fun m hm ↦ by rw [← Function.iterate_add_apply]; exact hk₂ _ (by omega)) h
  obtain rfl | hd := eq_or_ne d 0
  · simpa using hpd
  · have := iterate_mem_of_ne_zero hfB hd fun m hm ↦ hk₂ m (by omega)
    rw [← hpd] at this
    exact absurd this hp₁

private theorem chain_dominance [IsPreorder α r] (hfr : ∀ a ∈ A, r (f a) a) {p : α} {n : ℕ}
    (hA : ∀ m < n, f^[m] p ∈ A) : r (f^[n] p) p := by
  induction n with
  | zero => exact refl_of r p
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact _root_.trans (hfr _ (hA n n.lt_succ_self)) (ih fun m hm ↦ hA m (by omega))

theorem MatchingLift.compl [Finite α] [IsPreorder α r] (h : MatchingLift r B A) :
    MatchingLift r Aᶜ Bᶜ := by
  classical
  obtain ⟨f, hf, hinj⟩ := h
  have hfB : Set.MapsTo f A B := fun a ha ↦ (hf a ha).1
  have hex : ∀ p, p ∉ B → ∃ n, f^[n] p ∉ A := fun p hp ↦ exists_iterate_notMem hfB hinj hp
  have hg : ∀ p (hp : p ∉ B),
      f^[Nat.find (hex p hp)] p ∉ A ∧ ∀ m < Nat.find (hex p hp), f^[m] p ∈ A :=
    fun p hp ↦ ⟨Nat.find_spec (hex p hp), fun m hm ↦ by_contra (Nat.find_min (hex p hp) hm)⟩
  refine ⟨fun p ↦ if hp : p ∈ B then p else f^[Nat.find (hex p hp)] p, fun p hp ↦ ?_,
    fun p₁ hp₁ p₂ hp₂ heq ↦ ?_⟩
  · have hp' : p ∉ B := hp
    dsimp only
    rw [dite_eq_right hp']
    exact ⟨(hg p hp').1, chain_dominance (fun a ha ↦ (hf a ha).2) (hg p hp').2⟩
  · have hp₁' : p₁ ∉ B := hp₁
    have hp₂' : p₂ ∉ B := hp₂
    dsimp only at heq
    rw [dite_eq_right hp₁', dite_eq_right hp₂'] at heq
    exact chain_origin_eq hfB hinj hp₁' hp₂' (hg p₁ hp₁').2 (hg p₂ hp₂').2 heq

theorem matchingLift_compl_compl [Finite α] [IsPreorder α r] :
    MatchingLift r Aᶜ Bᶜ ↔ MatchingLift r B A :=
  ⟨fun h ↦ by simpa using h.compl, MatchingLift.compl⟩

instance [Finite α] [IsPreorder α r] : IsComplementReversing (MatchingLift r) :=
  ⟨fun _ _ ↦ MatchingLift.compl⟩

end Compl

/-! ### The WJR representation -/

section Representation

variable {W : Type*} [Finite W] {ge : Set W → Set W → Prop}

private lemma rel_of_forall_singleton [IsLikelihoodMono ge] (hJ : RightUnion ge) {A B : Set W}
    (h : ∀ b ∈ B, ge A {b}) : ge A B := by
  induction B, B.toFinite using Set.Finite.induction_on with
  | empty => exact mono _ _ (Set.empty_subset A)
  | @insert b B _ _ ih =>
    rw [Set.insert_eq]
    exact hJ A _ _ (h b (Set.mem_insert b B)) (ih fun c hc ↦ h c (Set.mem_insert_of_mem b hc))

/-- A monotone, transitive relation on the subsets of a finite set is Lewis's comparative
possibility of a reflexive relation on worlds exactly when it has right-union and is determined
by singletons: the model-theoretic content of the soundness and completeness of Halpern's logic
WJR over Lewis's comparative possibility (Holliday and Icard's Theorem 2, p. 520, citing Halpern's
Theorem 7.5.1a). -/
theorem exists_eq_lewis_iff [IsLikelihoodMono ge] [IsTrans (Set W) ge] :
    (∃ r : W → W → Prop, Std.Refl r ∧ Lewis r = ge) ↔
      RightUnion ge ∧ DeterminedBySingletons ge := by
  refine ⟨fun ⟨r, _, h⟩ ↦ h ▸ ⟨rightUnion_lewis, determinedBySingletons_lewis⟩,
    fun ⟨hJ, hDS⟩ ↦ ⟨fun u v ↦ ge {u} {v}, ⟨fun w ↦ mono _ _ subset_rfl⟩, ?_⟩⟩
  funext A B
  refine propext ⟨fun h ↦ rel_of_forall_singleton hJ fun b hb ↦ ?_, fun h b hb ↦
    hDS A b (trans_of ge h (mono _ _ (Set.singleton_subset_iff.2 hb)))⟩
  obtain ⟨a, ha, hab⟩ := h hb
  exact trans_of ge (mono _ _ (Set.singleton_subset_iff.2 ha)) hab

end Representation

end ComparativeProbability
