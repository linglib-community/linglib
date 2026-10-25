module

public import Linglib.Logic.ComparativeProbability.Defs
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Defs.Unbundled

/-!
# World-ordering semantics: lifting an order on worlds to propositions

Lewis's comparative possibility lifts a relation `r` on worlds to propositions: `A` is at
least as possible as `B` when every world of `B` is `r`-dominated by a world of `A`, that is
when `B` lies in the image of `A` under `r` (`LewisLift`). Kratzer uses it for the comparative
epistemic modal. Holliday and Icard replace it by the m-lifting `MatchingLift`, which asks the
dominating worlds to be distinct, and Kratzer's later revision `KratzerLift` compares only the
worlds in exactly one of the two propositions. The l- and m-liftings of a preorder are
monotone, transitive likelihood orders, and the m-lifting of a finite preorder reverses
complements, as Harrison-Trainor, Holliday and Icard show by following each point of `A \ B`
along the dominating injection until it leaves `A`.

The l-lifting has the two closure properties of Halpern's logic WJR, right-union `J` and
determination by singletons, and a monotone, transitive relation on `Set W` is an l-lifting
exactly when it has both (`lewisLift_repr_iff`). The revised lift keeps right-union for
disjoint alternatives, an observation Holliday and Icard credit to Lassiter.

## Main statements

* `lewisLift_iff`, `rightUnion_lewisLift`, `determinedBySingletons_lewisLift`, and the
  `Std.Refl`/`IsTrans`/`IsLikelihoodMono` instances for both lifts, with `IsNontrivial`
  over a nonempty domain.
* `MatchingLift.ncard_le`, `matchingLift_compl_compl` and the `IsComplementReversing`
  instance.
* `strict_lewisLift_iff` — over a total relation the strict lift is Lewis's ∃∀ clause.
* `KratzerLift` with `kratzerLift_rightUnion_of_disjoint`, the disjunction puzzle it keeps for
  disjoint alternatives.
* `exists_lewisLift_repr`, `lewisLift_repr_iff` — the WJR representation and its round
  trip.

## References

* [lewis-1973]
* [kratzer-1991]
* [kratzer-2012]
* [holliday-icard-2013]
* [harrison-trainor-holliday-icard-2018]
* [halpern-2003]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*}

/-- A relation on propositions is determined by singletons when `r A {b}` gives some `a ∈ A`
with `r {a} {b}`. -/
def DeterminedBySingletons (r : Set α → Set α → Prop) : Prop :=
  ∀ (A : Set α) (b : α), r A {b} → ∃ a ∈ A, r {a} {b}

/-- The l-lifting `LewisLift r A B` holds when every world of `B` is `r`-dominated by some
world of `A`, that is when `B` lies in the image of `A` under `r`. -/
def LewisLift (r : α → α → Prop) (A B : Set α) : Prop :=
  B ⊆ SetRel.image {p : α × α | r p.1 p.2} A

/-- The m-lifting `MatchingLift r A B` holds when some injection `f : B ↪ A` dominates
pointwise. -/
def MatchingLift (r : α → α → Prop) (A B : Set α) : Prop :=
  ∃ f : α → α, (∀ b ∈ B, f b ∈ A ∧ r (f b) b) ∧ Set.InjOn f B

variable {r : α → α → Prop} {A A' B B' C : Set α} {b : α}

/-! ### The l-lifting -/

theorem lewisLift_iff : LewisLift r A B ↔ ∀ b ∈ B, ∃ a ∈ A, r a b := Iff.rfl

theorem lewisLift_empty (A : Set α) : LewisLift r A ∅ := Set.empty_subset _

theorem lewisLift_empty_left_iff : LewisLift r ∅ B ↔ B = ∅ := by
  rw [LewisLift, SetRel.image_empty_right, Set.subset_empty_iff]

theorem lewisLift_singleton_iff : LewisLift r A {b} ↔ ∃ a ∈ A, r a b :=
  Set.singleton_subset_iff

theorem lewisLift_of_subset [Std.Refl r] (h : B ⊆ A) : LewisLift r A B :=
  fun b hb ↦ ⟨b, h hb, refl_of r b⟩

instance [Std.Refl r] : Std.Refl (LewisLift r) := ⟨fun _ ↦ lewisLift_of_subset subset_rfl⟩

theorem LewisLift.mono_left (h : LewisLift r A B) (hA : A ⊆ A') : LewisLift r A' B :=
  h.trans (SetRel.image_mono hA)

theorem LewisLift.anti_right (h : LewisLift r A B) (hB : B' ⊆ B) : LewisLift r A B' :=
  hB.trans h

theorem LewisLift.trans [IsTrans α r] (hAB : LewisLift r A B) (hBC : LewisLift r B C) :
    LewisLift r A C := fun _ hc ↦
  let ⟨_, hb, hbc⟩ := hBC hc
  let ⟨a, ha, hab⟩ := hAB hb
  ⟨a, ha, _root_.trans hab hbc⟩

instance [IsTrans α r] : IsTrans (Set α) (LewisLift r) := ⟨fun _ _ _ ↦ LewisLift.trans⟩

instance [Std.Refl r] : IsLikelihoodMono (LewisLift r) := ⟨fun _ _ h ↦ lewisLift_of_subset h⟩

instance [Nonempty α] : IsNontrivial (LewisLift r) :=
  ⟨fun h ↦ Set.univ_nonempty.ne_empty (lewisLift_empty_left_iff.1 h)⟩

/-- The l-lifting is right-union closed, Halpern's axiom `J`. -/
theorem rightUnion_lewisLift : RightUnion (LewisLift r) :=
  fun _ _ _ h₁ h₂ ↦ Set.union_subset h₁ h₂

theorem determinedBySingletons_lewisLift : DeterminedBySingletons (LewisLift r) :=
  fun _ _ hAb ↦
    let ⟨a, ha, hab⟩ := hAb rfl
    ⟨a, ha, lewisLift_singleton_iff.2 ⟨a, rfl, hab⟩⟩

/-- Over a **total** relation, the strict l-lifting collapses to Lewis's ∃∀ comparative
possibility: some `A`-world strictly dominates every `B`-world. -/
theorem strict_lewisLift_iff (hTotal : ∀ a b, r a b ∨ r b a) (A B : Set α) :
    Strict (LewisLift r) A B ↔ ∃ a ∈ A, ∀ b ∈ B, r a b ∧ ¬ r b a := by
  constructor
  · rintro ⟨-, hn⟩
    rw [lewisLift_iff] at hn
    push Not at hn
    obtain ⟨a, haA, ha⟩ := hn
    exact ⟨a, haA, fun b hbB ↦ ⟨(hTotal a b).resolve_right (ha b hbB), ha b hbB⟩⟩
  · rintro ⟨a, haA, ha⟩
    refine ⟨fun b hbB ↦ ⟨a, haA, (ha b hbB).1⟩, fun h ↦ ?_⟩
    obtain ⟨b, hbB, hba⟩ := h haA
    exact (ha b hbB).2 hba

/-! ### The m-lifting -/

theorem MatchingLift.lewisLift (h : MatchingLift r A B) : LewisLift r A B :=
  let ⟨f, hf, _⟩ := h
  fun b hb ↦ ⟨f b, hf b hb⟩

theorem matchingLift_empty (A : Set α) : MatchingLift r A ∅ :=
  ⟨id, fun _ h ↦ h.elim, Set.injOn_empty id⟩

theorem matchingLift_empty_left_iff : MatchingLift r ∅ B ↔ B = ∅ :=
  ⟨fun h ↦ lewisLift_empty_left_iff.1 h.lewisLift,
    by rintro rfl; exact matchingLift_empty ∅⟩

theorem matchingLift_singleton_iff : MatchingLift r A {b} ↔ ∃ a ∈ A, r a b :=
  ⟨fun h ↦ lewisLift_singleton_iff.1 h.lewisLift,
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

variable {W : Type*} [Fintype W] {ge : Set W → Set W → Prop}

private lemma ge_of_forall_singleton (hT : ∀ A B : Set W, A ⊆ B → ge B A) (hJ : RightUnion ge)
    (A B : Set W) (h : ∀ b ∈ B, ge A {b}) : ge A B := by
  classical
  suffices ∀ (s : Finset W), (∀ b, b ∈ s → ge A {b}) → ge A (↑s) by
    rw [← Set.coe_toFinset B]
    exact this B.toFinset (fun b hb ↦ h b (Set.mem_toFinset.mp hb))
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty]
    exact hT ∅ A (Set.empty_subset A)
  | @insert b s hbs ih =>
    intro hsub
    rw [Finset.coe_insert]
    exact hJ A _ _ (hsub _ (Finset.mem_insert_self _ _))
      (ih (fun c hc ↦ hsub c (Finset.mem_insert_of_mem hc)))

/-- A monotone, transitive relation satisfying `J` and `DS` is the l-lifting of a reflexive relation
on worlds (Holliday and Icard's Theorem 2; Halpern's Thm. 7.5.1a). -/
theorem exists_lewisLift_repr (hMono : ∀ A B : Set W, A ⊆ B → ge B A)
    (hTran : ∀ A B C : Set W, ge A B → ge B C → ge A C)
    (hJ : RightUnion ge) (hDS : DeterminedBySingletons ge) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w), ∀ A B, ge A B ↔ LewisLift ge_w A B := by
  refine ⟨fun u v ↦ ge {u} {v}, fun w ↦ hMono {w} {w} subset_rfl, fun A B ↦ ?_⟩
  constructor
  · intro hAB b hbB
    have hBb : ge B {b} := hMono {b} B (Set.singleton_subset_iff.mpr hbB)
    exact hDS A b (hTran A B {b} hAB hBb)
  · intro hLift
    apply ge_of_forall_singleton hMono hJ A B
    intro b hbB
    obtain ⟨a, haA, hab⟩ := hLift hbB
    have hAa : ge A {a} := hMono {a} A (Set.singleton_subset_iff.mpr haA)
    exact hTran A {a} {b} hAa hab

/-- A monotone, transitive comparison relation is the l-lifting of a reflexive world relation
**iff** it satisfies right-union and determination by singletons, the model-theoretic form of
soundness and completeness for WJR. -/
theorem lewisLift_repr_iff (hMono : ∀ A B : Set W, A ⊆ B → ge B A)
    (hTran : ∀ A B C : Set W, ge A B → ge B C → ge A C) :
    (∃ ge_w : W → W → Prop, (∀ w, ge_w w w) ∧ ∀ A B, ge A B ↔ LewisLift ge_w A B) ↔
      RightUnion ge ∧ DeterminedBySingletons ge := by
  constructor
  · rintro ⟨ge_w, -, hiff⟩
    refine ⟨fun A B C hab hac ↦ ?_, fun A b hA ↦ ?_⟩
    · exact (hiff _ _).mpr (rightUnion_lewisLift _ _ _ ((hiff _ _).mp hab) ((hiff _ _).mp hac))
    · obtain ⟨a, ha, hab⟩ := determinedBySingletons_lewisLift A b ((hiff _ _).mp hA)
      exact ⟨a, ha, (hiff _ _).mpr hab⟩
  · rintro ⟨hJ, hDS⟩
    obtain ⟨ge_w, hrefl, hiff⟩ := exists_lewisLift_repr hMono hTran hJ hDS
    exact ⟨ge_w, hrefl, hiff⟩

end Representation

/-! ### Kratzer's revised comparative possibility -/

/-- The k-lifting `KratzerLift r A B` holds unless some world in `B` outside `A` strictly
dominates every world in `A` outside `B`, so only the worlds in exactly one of the two
propositions count. -/
def KratzerLift (r : α → α → Prop) (A B : Set α) : Prop :=
  ¬ ∃ b ∈ B \ A, ∀ a ∈ A \ B, r b a ∧ ¬ r a b

theorem kratzerLift_iff : KratzerLift r A B ↔ ∀ b ∈ B \ A, ∃ a ∈ A \ B, ¬(r b a ∧ ¬ r a b) := by
  simp only [KratzerLift, not_exists, not_and, not_forall]
  exact forall₂_congr fun _ _ ↦ by simp

theorem kratzerLift_univ_iff : KratzerLift r A Set.univ ↔ A = Set.univ := by
  rw [kratzerLift_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem A).1 hne
    obtain ⟨a, ha, -⟩ := h b ⟨Set.mem_univ b, hb⟩
    exact ha.2 (Set.mem_univ a)
  · rintro rfl b hb
    exact absurd hb.1 hb.2

/-- When `A` is disjoint from both alternatives the revised lift is right-union closed, so the
disjunction puzzle survives it. -/
theorem kratzerLift_rightUnion_of_disjoint (r : α → α → Prop) {A B C : Set α}
    (hB : Disjoint A B) (hC : Disjoint A C) (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) :
    KratzerLift r A (B ∪ C) := by
  rintro ⟨b, ⟨hb | hb, hbA⟩, hall⟩
  · exact hAB ⟨b, ⟨hb, hbA⟩, fun a ha ↦
      hall a ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩
  · exact hAC ⟨b, ⟨hb, hbA⟩, fun a ha ↦
      hall a ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩

end ComparativeProbability
