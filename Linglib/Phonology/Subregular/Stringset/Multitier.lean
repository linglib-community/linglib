/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.Stringset.TierStrictlyLocal
public import Linglib.Phonology.Subregular.WordModel.Stringset
public import Linglib.Core.Computability.Definite
public import Linglib.Core.Computability.LocallyTestable
public import Linglib.Core.Computability.PiecewiseTestable
public import Linglib.Core.Computability.Variety.Basic
public import Linglib.Core.Order.BooleanSubalgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Multitier extensions of subregular classes

The tier-based extension of a class `𝒞` of languages collects the members of `𝒞` read on some
tier. Lambert's *multitier extension* `Language.multitier 𝒞` is the Boolean subalgebra these
generate, so that the parts of a Boolean combination may sit on different tiers.

The multitier extension [lies in a Boolean subalgebra exactly when the subalgebra holds every
member of `𝒞` on every tier](##Language.multitier_le_iff). It is therefore [closed under reading on
a tier](##Language.multitier_le_comap_onTier) and [idempotent](##Language.multitier_multitier), it
[stays inside every variety of languages containing `𝒞`](##Language.multitier_le_languageVariety),
a tier projection being a homomorphism of free monoids, and so is star-free whenever `𝒞` is. A
multitier language [cannot separate two words that no member of `𝒞` separates on any
tier](##Language.mem_iff_of_mem_multitier). When `𝒞` is the class of languages deciding membership
by an invariant of the word, such as its suffix of length `k`, and the alphabet is finite, the
converse holds: the multitier extension consists of [the languages deciding membership by the
invariants of the tier projections](##Language.mem_multitier_factorsThrough_iff). For the definite
languages and their relatives these are the Boolean combinations of Lambert's tier affixes, and
for the strictly local languages of width two or more, which generate the locally testable ones,
the invariant is the test vector of a word. The finite and cofinite languages have no such
invariant, but their multitier extension [is piecewise
testable](##Language.exists_isPiecewiseTestable_of_mem_multitierFiniteOrCofinite).

## Implementation notes

The classes carry the window `k` that Lambert leaves implicit; his classes are their unions over
`k`.

## References

* [lambert-2026]
* [heinz-rawal-tanner-2011]
* [de-santo-graf-2019]
* [simon-1975]
-/

@[expose] public section

namespace Language

open BooleanSubalgebra

variable {α : Type*} {𝒞 𝒟 : Set (Language α)} {L : Language α} {k : ℕ} {w w₁ w₂ : List α}

/-! ### The multitier extension -/

/-- The *multitier extension* of a class `𝒞` is the Boolean subalgebra of `Language α` generated
by its tier-based extension. -/
def multitier (𝒞 : Set (Language α)) : BooleanSubalgebra (Language α) :=
  closure (tierBased 𝒞)

theorem tierBased_subset_multitier : tierBased 𝒞 ⊆ multitier 𝒞 := subset_closure

theorem onTier_mem_multitier (T : α → Prop) [DecidablePred T] (h : L ∈ 𝒞) :
    onTier T L ∈ multitier 𝒞 :=
  tierBased_subset_multitier (onTier_mem_tierBased T h)

theorem subset_multitier : 𝒞 ⊆ multitier 𝒞 := subset_tierBased.trans tierBased_subset_multitier

/-- The multitier extension of `𝒞` lies in a Boolean subalgebra exactly when the subalgebra holds
every member of `𝒞` on every tier. -/
theorem multitier_le_iff {B : BooleanSubalgebra (Language α)} :
    multitier 𝒞 ≤ B ↔ ∀ (T : α → Prop) [DecidablePred T], 𝒞 ⊆ B.comap (onTier T) :=
  closure_le.trans ⟨fun h T _ _ hL ↦ h (onTier_mem_tierBased T hL), by
    rintro h _ ⟨T, _, L, hL, rfl⟩
    exact h T hL⟩

theorem multitier_mono (h : 𝒞 ⊆ 𝒟) : multitier 𝒞 ≤ multitier 𝒟 := closure_mono (tierBased_mono h)

/-- A multitier language read on a tier is a multitier language. -/
theorem multitier_le_comap_onTier (T : α → Prop) [DecidablePred T] :
    multitier 𝒞 ≤ (multitier 𝒞).comap (onTier T) :=
  multitier_le_iff.2 fun T' _ L hL ↦ by
    show onTier T (onTier T' L) ∈ multitier 𝒞
    rw [onTier_onTier]
    exact onTier_mem_multitier _ hL

/-- The multitier extension of a class is that of the Boolean subalgebra it generates. -/
@[simp] theorem multitier_closure (𝒞 : Set (Language α)) :
    multitier (closure 𝒞 : Set (Language α)) = multitier 𝒞 :=
  le_antisymm (multitier_le_iff.2 fun T _ ↦ closure_le.2 fun _ hL ↦ onTier_mem_multitier T hL)
    (multitier_mono subset_closure)

/-- The multitier extension is idempotent. -/
@[simp] theorem multitier_multitier (𝒞 : Set (Language α)) :
    multitier (multitier 𝒞 : Set (Language α)) = multitier 𝒞 :=
  le_antisymm (multitier_le_iff.2 fun T _ ↦ multitier_le_comap_onTier T)
    (multitier_mono subset_multitier)

/-! ### Separation

A multitier language separates two words only if some member of the base class separates their
projections to some tier, and over a finite alphabet nothing else constrains it when the base class
consists of the languages deciding membership by a finitely valued invariant. -/

/-- Two words that no member of `𝒞` separates on any tier are separated by no language of the
multitier extension of `𝒞`. -/
theorem mem_iff_of_mem_multitier (hL : L ∈ multitier 𝒞)
    (h : ∀ (T : α → Prop) [DecidablePred T], ∀ L' ∈ 𝒞, w₁.filter T ∈ L' ↔ w₂.filter T ∈ L') :
    w₁ ∈ L ↔ w₂ ∈ L :=
  mem_iff_of_mem_closure hL <| by
    rintro _ ⟨T, _, L', hL', rfl⟩
    exact h T L' hL'

/-- Over a finite alphabet, the multitier extension of the languages deciding membership by a
finitely valued invariant `f` consists of the languages deciding membership by the values of `f`
at the tier projections. -/
theorem mem_multitier_factorsThrough_iff [Finite α] {κ : Type*} {f : List α → κ}
    (hf : (Set.range f).Finite) :
    L ∈ multitier {L' | Function.FactorsThrough (· ∈ L') f} ↔
      ∀ w w' : List α,
        (∀ (T : α → Prop) [DecidablePred T], f (w.filter T) = f (w'.filter T)) →
          (w ∈ L ↔ w' ∈ L) := by
  refine ⟨fun hL w w' h ↦ mem_iff_of_mem_multitier hL fun T _ L' hL' ↦ iff_of_eq (hL' (h T)),
    fun h ↦ ?_⟩
  let Φ : List α → (α → Bool) → κ := fun w T ↦ f (w.filter T)
  have : Finite (Φ '' L) := Set.Finite.to_subtype <|
    (Set.Finite.pi fun _ ↦ hf).subset <| by
      rintro _ ⟨w, -, rfl⟩ T -
      exact Set.mem_range_self _
  have e : L = ⨆ p : Φ '' L, ⨅ T : α → Bool,
      onTier (T · = true) {v | f v = (p : (α → Bool) → κ) T} := by
    ext w
    refine Iff.trans ?_ Language.mem_iSup.symm
    refine ⟨fun hw ↦ ⟨⟨Φ w, w, hw, rfl⟩, Set.mem_iInter.2 fun _ ↦ rfl⟩, ?_⟩
    rintro ⟨⟨_, w', hw', rfl⟩, hT⟩
    exact (h w w' fun T _ ↦ Set.mem_iInter.1 hT fun a ↦ decide (T a)).2 hw'
  rw [e]
  exact iSup_mem fun p ↦ iInf_mem fun T ↦
    onTier_mem_multitier _ fun _ _ hab ↦ congrArg (· = _) hab

/-! ### Varieties of languages -/

/-- The multitier extension of `𝒞` lies in every variety of languages containing `𝒞`. -/
theorem multitier_le_languageVariety {𝒱 : Monoid.LanguageVariety} (h : 𝒞 ⊆ 𝒱 α) :
    multitier 𝒞 ≤ 𝒱 α :=
  multitier_le_iff.2 fun T _ _ hL ↦ 𝒱.comap_mem (FreeMonoid.filter T) (h hL)

/-- The multitier extension of a class of star-free languages is star-free. -/
theorem isStarFree_of_mem_multitier (h𝒞 : ∀ L ∈ 𝒞, L.IsStarFree) (h : L ∈ multitier 𝒞) :
    L.IsStarFree :=
  multitier_le_languageVariety (𝒱 := Monoid.aperiodicVariety.toLanguageVariety) h𝒞 h

/-! ### The multitier classes

Lambert's classes are the multitier extensions of the strictly local, definite, reverse definite,
generalized definite, and finite or cofinite languages. -/

section Classes

variable (k)

/-- The *multitier locally testable* languages are the multitier extension of the strictly
`k`-local languages, Lambert's BTSL. They are not the multi-tier strictly local languages of
[de-santo-graf-2019], which close the tier-based strictly local languages under intersection
only. -/
def multitierLocallyTestable : BooleanSubalgebra (Language α) := multitier {L | L.IsStrictlyLocal k}

/-- The *multitier definite* languages are the multitier extension of the `k`-definite
languages, Lambert's BTD. -/
def multitierDefinite : BooleanSubalgebra (Language α) := multitier {L | L.IsDefinite k}

/-- The *multitier reverse definite* languages are the multitier extension of the reverse
`k`-definite languages, Lambert's BTK. -/
def multitierReverseDefinite : BooleanSubalgebra (Language α) :=
  multitier {L | L.IsReverseDefinite k}

/-- The *multitier generalized definite* languages are the multitier extension of the generalized
`k`-definite languages, Lambert's BTLI. -/
def multitierGeneralizedDefinite : BooleanSubalgebra (Language α) :=
  multitier {L | L.IsGeneralizedDefinite k}

/-- The *multitier co/finite* languages are the multitier extension of the finite or cofinite
languages, Lambert's BTN. -/
def multitierFiniteOrCofinite : BooleanSubalgebra (Language α) :=
  multitier {L | L.IsFiniteOrCofinite}

end Classes

theorem multitierDefinite_le_multitierGeneralizedDefinite :
    (multitierDefinite k : BooleanSubalgebra (Language α)) ≤ multitierGeneralizedDefinite k :=
  multitier_mono fun _ ↦ IsDefinite.toIsGeneralizedDefinite

theorem multitierReverseDefinite_le_multitierGeneralizedDefinite :
    (multitierReverseDefinite k : BooleanSubalgebra (Language α)) ≤
      multitierGeneralizedDefinite k :=
  multitier_mono fun _ ↦ IsReverseDefinite.toIsGeneralizedDefinite

theorem IsTierStrictlyLocal.mem_multitierLocallyTestable (h : L.IsTierStrictlyLocal k) :
    L ∈ multitierLocallyTestable k :=
  tierBased_subset_multitier (isTierStrictlyLocal_iff_mem_tierBased.1 h)

/-- Over a finite alphabet and for `2 ≤ k`, the multitier locally testable languages are the
multitier extension of the locally `k`-testable languages as well, since the strictly `k`-local
languages generate those. -/
theorem multitier_isLocallyTestable [Finite α] (hk : 2 ≤ k) :
    multitier {K : Language α | K.IsLocallyTestable k} = multitierLocallyTestable k := by
  have h : {K : Language α | K.IsLocallyTestable k} =
      (closure {K : Language α | K.IsStrictlyLocal k} : Set (Language α)) :=
    Set.ext fun _ ↦ isLocallyTestable_iff_mem_closure hk
  rw [h, multitier_closure, multitierLocallyTestable]

/-- Over a finite alphabet and for `2 ≤ k`, a language is multitier locally testable with window
`k` exactly when the `k`-test vectors of the tier projections of a word decide its membership. -/
theorem mem_multitierLocallyTestable_iff [Finite α] (hk : 2 ≤ k) :
    L ∈ multitierLocallyTestable k ↔ ∀ w w' : List α,
      (∀ (T : α → Prop) [DecidablePred T],
        (w.filter T).kTestVector k = (w'.filter T).kTestVector k) → (w ∈ L ↔ w' ∈ L) := by
  rw [← multitier_isLocallyTestable hk]
  exact mem_multitier_factorsThrough_iff (List.finite_range_kTestVector k)

/-! ### Reversal

Reversal commutes with reading on a tier and with the Boolean operations, so it carries the
multitier extension of a class to that of the reversed class, and exchanges the multitier definite
and reverse definite languages. -/

theorem reverse_mem_multitier (h : L ∈ multitier 𝒞) : L.reverse ∈ multitier (reverse '' 𝒞) := by
  unfold multitier at h ⊢
  induction h using closure_bot_sup_induction with
  | mem _ hL =>
    obtain ⟨T, _, L', hL', rfl⟩ := hL
    rw [reverse_onTier]
    exact subset_closure (onTier_mem_tierBased T ⟨L', hL', rfl⟩)
  | bot => exact bot_mem
  | sup _ _ _ _ ih₁ ih₂ => exact sup_mem ih₁ ih₂
  | compl _ _ ih => exact compl_mem ih

/-- A language is multitier definite exactly when its reversal is multitier reverse definite. -/
theorem reverse_mem_multitierReverseDefinite_iff :
    L.reverse ∈ multitierReverseDefinite k ↔ L ∈ multitierDefinite k := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← L.reverse_reverse]
    refine multitier_mono ?_ (reverse_mem_multitier h)
    rintro _ ⟨L', hL', rfl⟩
    exact isReverseDefinite_iff_isDefinite_reverse.1 hL'
  · refine multitier_mono ?_ (reverse_mem_multitier h)
    rintro _ ⟨L', hL', rfl⟩
    exact isReverseDefinite_iff_isDefinite_reverse.2 (by rwa [reverse_reverse])

/-! ### Tier affixes

Lambert's propositional logic has as literals the words whose projection to a tier `T` is exactly
`xs`, begins with `xs`, or ends in `xs`: the languages `{xs}`, `ofPrefix xs` and `ofSuffix xs`
read on `T`. Each lies in the multitier extension of the class its affix belongs to, with a window
at least the length of the affix, strictly more for a whole word. -/

section Affixes

variable {T : α → Prop} [DecidablePred T] {xs : List α}

theorem ofSuffix_mem_multitierDefinite (hk : xs.length ≤ k) :
    ofSuffix xs ∈ multitierDefinite k :=
  subset_multitier ((isDefinite_ofSuffix xs).mono hk)

theorem ofPrefix_mem_multitierReverseDefinite (hk : xs.length ≤ k) :
    ofPrefix xs ∈ multitierReverseDefinite k :=
  subset_multitier ((isReverseDefinite_ofPrefix xs).mono hk)

theorem onTier_ofSuffix_mem_multitierDefinite (hk : xs.length ≤ k) :
    onTier T (ofSuffix xs) ∈ multitierDefinite k :=
  onTier_mem_multitier T ((isDefinite_ofSuffix xs).mono hk)

theorem onTier_ofPrefix_mem_multitierReverseDefinite (hk : xs.length ≤ k) :
    onTier T (ofPrefix xs) ∈ multitierReverseDefinite k :=
  onTier_mem_multitier T ((isReverseDefinite_ofPrefix xs).mono hk)

theorem onTier_singleton_mem_multitierDefinite (hk : xs.length < k) :
    onTier T {xs} ∈ multitierDefinite k :=
  onTier_mem_multitier T ((isDefinite_succ_of_forall_length_le
    fun _ hw ↦ le_of_eq (congrArg List.length hw)).mono hk)

theorem onTier_singleton_mem_multitierReverseDefinite (hk : xs.length < k) :
    onTier T {xs} ∈ multitierReverseDefinite k :=
  onTier_mem_multitier T ((isReverseDefinite_succ_of_forall_length_le
    fun _ hw ↦ le_of_eq (congrArg List.length hw)).mono hk)

theorem onTier_singleton_mem_multitierFiniteOrCofinite :
    onTier T {xs} ∈ multitierFiniteOrCofinite :=
  onTier_mem_multitier T (Or.inl (Set.finite_singleton xs))

end Affixes

/-! ### Membership by tier affixes

The definite languages and their relatives decide membership by the affixes of length `k`, so
their multitier extensions cannot separate two words with the same such affixes on every tier,
and over a finite alphabet contain every language that does not. -/

/-- Two words with the same prefix and suffix of length `k` on every tier are separated by no
multitier generalized definite language of window `k`. -/
theorem mem_iff_of_mem_multitierGeneralizedDefinite (hL : L ∈ multitierGeneralizedDefinite k)
    (h : ∀ (T : α → Prop) [DecidablePred T],
      Edge.left.takeAt k (w₁.filter T) = Edge.left.takeAt k (w₂.filter T) ∧
      Edge.right.takeAt k (w₁.filter T) = Edge.right.takeAt k (w₂.filter T)) :
    w₁ ∈ L ↔ w₂ ∈ L :=
  mem_iff_of_mem_multitier hL fun T _ _ hL' ↦
    isGeneralizedDefinite_iff_edges.1 hL' (h T).1 (h T).2

section Finite

variable [Finite α]

/-- Over a finite alphabet, a language is multitier definite with window `k` exactly when the
suffixes of length `k` of the tier projections of a word decide its membership. -/
theorem mem_multitierDefinite_iff :
    L ∈ multitierDefinite k ↔ ∀ w w' : List α,
      (∀ (T : α → Prop) [DecidablePred T],
        Edge.right.takeAt k (w.filter T) = Edge.right.takeAt k (w'.filter T)) →
          (w ∈ L ↔ w' ∈ L) :=
  mem_multitier_factorsThrough_iff (Edge.finite_range_takeAt _ _)

/-- Over a finite alphabet, a language is multitier reverse definite with window `k` exactly when
the prefixes of length `k` of the tier projections of a word decide its membership. -/
theorem mem_multitierReverseDefinite_iff :
    L ∈ multitierReverseDefinite k ↔ ∀ w w' : List α,
      (∀ (T : α → Prop) [DecidablePred T],
        Edge.left.takeAt k (w.filter T) = Edge.left.takeAt k (w'.filter T)) →
          (w ∈ L ↔ w' ∈ L) :=
  mem_multitier_factorsThrough_iff (Edge.finite_range_takeAt _ _)

/-- Over a finite alphabet, a language is multitier generalized definite with window `k` exactly
when the prefixes and suffixes of length `k` of the tier projections of a word decide its
membership. -/
theorem mem_multitierGeneralizedDefinite_iff :
    L ∈ multitierGeneralizedDefinite k ↔ ∀ w w' : List α,
      (∀ (T : α → Prop) [DecidablePred T],
        Edge.left.takeAt k (w.filter T) = Edge.left.takeAt k (w'.filter T) ∧
        Edge.right.takeAt k (w.filter T) = Edge.right.takeAt k (w'.filter T)) →
          (w ∈ L ↔ w' ∈ L) := by
  have h := mem_multitier_factorsThrough_iff (L := L)
    (f := fun w : List α ↦ (Edge.left.takeAt k w, Edge.right.takeAt k w))
    (((Edge.finite_range_takeAt .left k).prod (Edge.finite_range_takeAt .right k)).subset <| by
      rintro _ ⟨w, rfl⟩
      exact ⟨⟨w, rfl⟩, ⟨w, rfl⟩⟩)
  simp only [Prod.mk.injEq] at h
  exact h

end Finite

/-! ### Multitier co/finite languages are piecewise testable

A word projects to `u` on a tier exactly when `u` is among its subsequences and no subsequence
longer than `u` lies on the tier, so a tier word is decided by the subsequences of length at most
one more than its own. -/

theorem isPiecewiseTestable_onTier_singleton (T : α → Prop) [DecidablePred T] (u : List α) :
    (onTier T {u}).IsPiecewiseTestable (u.length + 1) := by
  have key (w : List α) : w.filter T = u ↔ (u ∈ subseqSet (u.length + 1) w ∧ ∀ a ∈ u, T a) ∧
      ∀ s ∈ subseqSet (u.length + 1) w, (∀ a ∈ s, T a) → s.length ≤ u.length := by
    constructor
    · rintro rfl
      refine ⟨⟨⟨List.filter_sublist, Nat.le_succ _⟩,
        fun a ha ↦ of_decide_eq_true (List.mem_filter.1 ha).2⟩, fun s hs hsT ↦ ?_⟩
      rw [← List.filter_eq_self.2 fun a ha ↦ decide_eq_true (hsT a ha)]
      exact (hs.1.filter _).length_le
    · rintro ⟨⟨⟨hu, -⟩, huT⟩, hs⟩
      have h₁ : u.Sublist (w.filter T) := by
        have := hu.filter (fun a ↦ decide (T a))
        rwa [List.filter_eq_self.2 fun a ha ↦ decide_eq_true (huT a ha)] at this
      have h₂ : (w.filter T).length ≤ u.length := by
        by_contra hlt
        have := hs ((w.filter T).take (u.length + 1))
          ⟨(List.take_sublist _ _).trans List.filter_sublist, by simp⟩
          fun a ha ↦ of_decide_eq_true (List.mem_filter.1 (List.mem_of_mem_take ha)).2
        simp only [List.length_take] at this
        omega
      exact (h₁.eq_of_length_le h₂).symm
  intro a b e
  show (a.filter T = u) = (b.filter T = u)
  rw [eq_iff_iff, key, key, e]

/-- A finite or cofinite language read on a tier is piecewise testable. -/
theorem exists_isPiecewiseTestable_onTier (T : α → Prop) [DecidablePred T]
    (h : L.IsFiniteOrCofinite) : ∃ k, (onTier T L).IsPiecewiseTestable k := by
  have fin : ∀ s : Set (List α), s.Finite →
      ∃ k, (onTier T (s : Language α)).IsPiecewiseTestable k :=
    fun s hs ↦ Set.Finite.induction_on
      (motive := fun s _ ↦ ∃ k, (onTier T (s : Language α)).IsPiecewiseTestable k) s hs
      ⟨0, fun _ _ _ ↦ rfl⟩ fun {u} _ _ _ ⟨k, hk⟩ ↦ ⟨max (u.length + 1) k,
        ((isPiecewiseTestable_onTier_singleton T u).mono (le_max_left _ _)).union
          (hk.mono (le_max_right _ _))⟩
  rcases h with h | h
  · exact fin L h
  · obtain ⟨k, hk⟩ := fin Lᶜ h
    exact ⟨k, by simpa [map_compl'] using hk.compl⟩

/-- Every multitier co/finite language is piecewise testable. -/
theorem exists_isPiecewiseTestable_of_mem_multitierFiniteOrCofinite
    (h : L ∈ multitierFiniteOrCofinite) : ∃ k, L.IsPiecewiseTestable k := by
  unfold multitierFiniteOrCofinite multitier at h
  induction h using closure_bot_sup_induction with
  | mem _ hL =>
    obtain ⟨T, _, L', hL', rfl⟩ := hL
    exact exists_isPiecewiseTestable_onTier T hL'
  | bot => exact ⟨0, fun _ _ _ ↦ rfl⟩
  | sup _ _ _ _ ih₁ ih₂ =>
    obtain ⟨k, hk⟩ := ih₁
    obtain ⟨k', hk'⟩ := ih₂
    exact ⟨max k k', (hk.mono (le_max_left _ _)).union (hk'.mono (le_max_right _ _))⟩
  | compl _ _ ih => exact ih.imp fun _ ↦ IsPiecewiseTestable.compl

end Language
