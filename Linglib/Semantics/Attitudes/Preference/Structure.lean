module

public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Preference structures

A preference structure, in the sense of Condoravdi and Lauer, is a set of propositions with a
strict ranking by importance. A structure is consistent with an information state when any family
of its preferences that the information rules out jointly contains a strictly ranked pair, and
realistic when each preference is compatible with the information. Consistency entails realism and
makes the maximal preferences jointly realizable.

*Want* relates an agent to the maximal elements of the effective preference structure its context
supplies, which plays the role of a Kratzerian conversational background. Its readings differ in
how a maximal preference relates to the complement: identity is the exact-match reading, a
preference the complement entails gives the success-oriented reading, downward entailing in the
complement, and a preference that entails the complement gives the Quine–Hintikka reading, upward
entailing. Over a consistent background, *want φ* and *want ¬φ* do not hold together on the
exact-match reading.

## Main definitions

* `PreferenceStructure`, with `maxElts`, `Consistent` and `Realistic`.
* `PreferenceStructure.discrete`, `PreferenceStructure.rankBelow`: the unranked structure on a
  set of preferences, and the one that ranks a single preference below another.
* `Desire.Preferential.Want`, `Desire.Preferential.WantSufficient`,
  `Desire.Preferential.WantNecessary`: the exact-match, success-oriented and Quine–Hintikka
  readings of *want*.

## Main statements

* `PreferenceStructure.Consistent.realistic`: consistency entails realism.
* `PreferenceStructure.Consistent.inter_sInter_maxElts_nonempty`: the maximal preferences of a
  consistent structure are jointly compatible with the information.
* `PreferenceStructure.consistent_of_realistic_of_isChain`: a realistic chain is consistent.
* `Desire.Preferential.WantSufficient.anti`, `Desire.Preferential.WantNecessary.mono`: the
  success-oriented reading is downward and the Quine–Hintikka reading upward entailing.
* `Desire.Preferential.Want.not_compl`: over a consistent background, a proposition and its
  negation are not both wanted.

## Implementation notes

The ranking is a strict order on all of `Set W`, of which only its restriction to the preferences
is observed.

## References

* [condoravdi-lauer-2011]
* [condoravdi-lauer-2012]
* [condoravdi-lauer-2016]
* [lauer-2013]
* [lauer-condoravdi-2014]
* [kratzer-1981]
-/

@[expose] public section

variable {W : Type*}

/-- A preference structure is a set of propositions `prefs` with a strict ranking `prec`, where
`prec p q` reads "`q` is strictly preferred to `p`". The ranking is a relation on all of `Set W`,
and only its restriction to `prefs` is ever observed. -/
structure PreferenceStructure (W : Type*) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking, where `prec p q` reads "`q` is strictly preferred to `p`". -/
  prec : Set W → Set W → Prop
  /-- The strict-partial-order axioms, packaged as a mathlib typeclass. -/
  isStrictOrder : IsStrictOrder (Set W) prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder (Set W) P.prec := P.isStrictOrder

/-- The maximal elements of the preference structure are the preferences with nothing in `prefs`
strictly above them. -/
def maxElts : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := fun _ h ↦ h.1

/-- A preference structure is consistent with respect to an information state `B` when any subfamily
of preferences whose joint realization is incompatible with `B` contains a strictly ranked pair. -/
def Consistent (B : Set W) : Prop :=
  ∀ X ⊆ P.prefs, B ∩ ⋂₀ X = ∅ → ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- A preference structure is realistic with respect to an information state when every preference
is compatible with it. -/
def Realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

section Consistent

variable {P} {B : Set W}

/-- Consistency relative to an information state persists to any weaker one. -/
theorem Consistent.mono {H : Set W} (hC : P.Consistent B) (h : B ⊆ H) : P.Consistent H :=
  fun X hX hXH ↦ hC X hX (Set.subset_eq_empty (Set.inter_subset_inter_left _ h) hXH)

/-- Consistency entails realism, by the singleton subfamilies and irreflexivity. -/
theorem Consistent.realistic (hC : P.Consistent B) : P.Realistic B := by
  intro p hp hpB
  obtain ⟨_, rfl, _, rfl, hqr⟩ := hC {p} (Set.singleton_subset_iff.2 hp)
    (by rw [Set.sInter_singleton, Set.inter_comm]; exact hpB)
  exact irrefl_of P.prec _ hqr

theorem Consistent.nonempty (hC : P.Consistent B) : B.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦
    let ⟨_, hp, _⟩ := hC ∅ (Set.empty_subset _) (by rw [Set.sInter_empty, Set.inter_univ]; exact h)
    hp

/-- A preference incompatible with a maximal one is ranked strictly below it. -/
theorem Consistent.prec_of_mem_maxElts (hC : P.Consistent B) {p q : Set W} (hp : p ∈ P.maxElts)
    (hq : q ∈ P.prefs) (h : B ∩ (p ∩ q) = ∅) : P.prec q p := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC {p, q}
    (Set.insert_subset hp.1 (Set.singleton_subset_iff.2 hq)) (by rwa [Set.sInter_pair])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  exacts [absurd hxy (irrefl_of P.prec _), absurd hxy (hp.2 _ hq), hxy,
    absurd hxy (irrefl_of P.prec _)]

/-- The maximal preferences of a consistent structure are jointly belief-compatible. -/
theorem Consistent.inter_sInter_maxElts_nonempty (hC : P.Consistent B) :
    (B ∩ ⋂₀ P.maxElts).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦
    let ⟨_, hp, _, hq, hpq⟩ := hC _ P.maxElts_subset_prefs h
    hp.2 _ hq.1 hpq

/-- Two maximal preferences of a consistent structure are jointly belief-compatible, which blocks
conflicting desires. -/
theorem Consistent.inter_inter_nonempty_of_mem_maxElts (hC : P.Consistent B) {φ ψ : Set W}
    (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) : (B ∩ (φ ∩ ψ)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.sInter_subset_of_mem hφ) (Set.sInter_subset_of_mem hψ)

/-- A chain of realistic preferences is consistent. -/
theorem consistent_of_realistic_of_isChain (hR : P.Realistic B) (hc : IsChain P.prec P.prefs)
    (hB : B.Nonempty) : P.Consistent B := by
  intro X hX hXB
  by_contra h
  have hs : X.Subsingleton := fun p hp q hq ↦
    by_contra fun hne ↦ (hc (hX hp) (hX hq) hne).elim (fun hpq ↦ h ⟨p, hp, q, hq, hpq⟩)
      (fun hqp ↦ h ⟨q, hq, p, hp, hqp⟩)
  rcases hs.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · rw [Set.sInter_empty, Set.inter_univ] at hXB
    exact hB.ne_empty hXB
  · rw [Set.sInter_singleton, Set.inter_comm] at hXB
    exact hR p (hX (Set.mem_singleton p)) hXB

end Consistent

/-! ### Unranked preferences -/

/-- The discrete structure has the preferences `S` and no ranking, so all of them are maximal. -/
def discrete (S : Set (Set W)) : PreferenceStructure W where
  prefs := S
  prec _ _ := False
  isStrictOrder := { irrefl := fun _ h ↦ h, trans := fun _ _ _ h _ ↦ h }

@[simp] theorem maxElts_discrete (S : Set (Set W)) : (discrete S).maxElts = S :=
  Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, fun _ _ h ↦ h⟩⟩

/-- Unranked preferences are consistent when jointly belief-compatible. -/
theorem consistent_discrete {S : Set (Set W)} {B : Set W} (h : (B ∩ ⋂₀ S).Nonempty) :
    (discrete S).Consistent B := fun _ hX hXB ↦
  absurd hXB (h.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hX))).ne_empty

/-- The structure with the single preference `p`. -/
abbrev single (p : Set W) : PreferenceStructure W := discrete {p}

@[simp] theorem maxElts_single (p : Set W) : (single p).maxElts = {p} := maxElts_discrete _

theorem consistent_single {p B : Set W} (h : (p ∩ B).Nonempty) : (single p).Consistent B :=
  consistent_discrete (by rwa [Set.sInter_singleton, Set.inter_comm])

/-! ### Ranking one preference below another -/

/-- The structure on `S` that ranks `p` strictly below `q` and leaves the rest unranked. -/
def rankBelow (S : Set (Set W)) {p q : Set W} (h : p ≠ q) : PreferenceStructure W where
  prefs := S
  prec r s := r = p ∧ s = q
  isStrictOrder :=
    { irrefl := fun _ hr ↦ h (hr.1.symm.trans hr.2)
      trans := fun _ _ _ hr hs ↦ absurd (hr.2.symm.trans hs.1) h.symm }

variable {S : Set (Set W)} {p q : Set W} (h : p ≠ q)

/-- Once `q` is a preference, everything but `p` is maximal. -/
theorem maxElts_rankBelow (hq : q ∈ S) : (rankBelow S h).maxElts = S \ {p} :=
  Set.ext fun _ ↦ ⟨fun hr ↦ ⟨hr.1, fun hrp ↦ hr.2 q hq ⟨hrp, rfl⟩⟩,
    fun hr ↦ ⟨hr.1, fun _ _ hs ↦ hr.2 hs.1⟩⟩

/-- Ranking `p` below `q` resolves every conflict when the preferences without `p` and those
without `q` are each jointly compatible with the information. -/
theorem consistent_rankBelow {B : Set W} (hp : (B ∩ ⋂₀ (S \ {p})).Nonempty)
    (hq : (B ∩ ⋂₀ (S \ {q})).Nonempty) : (rankBelow S h).Consistent B := by
  intro X hX hXB
  have mem {r : Set W} (hr : (B ∩ ⋂₀ (S \ {r})).Nonempty) : r ∈ X := by
    by_contra hrX
    refine hr.ne_empty (Set.subset_eq_empty (Set.inter_subset_inter_right _ ?_) hXB)
    exact Set.sInter_subset_sInter fun x hx ↦ ⟨hX hx, fun hxr ↦ hrX (hxr ▸ hx)⟩
  exact ⟨p, mem hp, q, mem hq, rfl, rfl⟩

end PreferenceStructure

/-! ### Effective-preference *want* -/

namespace Desire.Preferential

variable {Agent W : Type*} (P : Agent → W → PreferenceStructure W) (a : Agent) (φ : Set W)
  (w : W)

/-- On the exact-match reading, `a` wants `φ` at `w` when `φ` is itself a maximal preference of
the background `P a w`. -/
def Want : Prop := φ ∈ (P a w).maxElts

/-- On the success-oriented reading, `a` wants `φ` when `φ` entails a maximal preference, which
`φ` then satisfies. -/
def WantSufficient : Prop := ∃ p ∈ (P a w).maxElts, φ ⊆ p

/-- On the Quine–Hintikka reading, `a` wants `φ` when a maximal preference entails `φ`, so that the
preference is satisfied only if `φ` holds. -/
def WantNecessary : Prop := ∃ p ∈ (P a w).maxElts, p ⊆ φ

variable {P a φ w}

theorem Want.wantSufficient (h : Want P a φ w) : WantSufficient P a φ w := ⟨φ, h, subset_rfl⟩

theorem Want.wantNecessary (h : Want P a φ w) : WantNecessary P a φ w := ⟨φ, h, subset_rfl⟩

/-- Over a consistent background a proposition and its negation are not both wanted. -/
theorem Want.not_compl {B : Set W} (hC : (P a w).Consistent B) (h : Want P a φ w) :
    ¬ Want P a φᶜ w := fun hn ↦
  (hC.inter_inter_nonempty_of_mem_maxElts h hn).ne_empty <| by
    rw [Set.inter_compl_self, Set.inter_empty]

theorem WantSufficient.anti {ψ : Set W} (hφψ : φ ⊆ ψ) (h : WantSufficient P a ψ w) :
    WantSufficient P a φ w :=
  let ⟨p, hp, hψp⟩ := h; ⟨p, hp, hφψ.trans hψp⟩

theorem WantNecessary.mono {ψ : Set W} (hφψ : φ ⊆ ψ) (h : WantNecessary P a φ w) :
    WantNecessary P a ψ w :=
  let ⟨p, hp, hpφ⟩ := h; ⟨p, hp, hpφ.trans hφψ⟩

end Desire.Preferential
