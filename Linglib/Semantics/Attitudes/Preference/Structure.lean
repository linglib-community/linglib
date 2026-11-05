module

public import Mathlib.Order.Antichain
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Preference structures

A preference structure is a set of propositions strictly ranked by importance. It is consistent
with an information state when [every family of mutually unranked preferences is jointly
realizable](##PreferenceStructure.consistent_iff_forall_isAntichain), in particular [the maximal
ones](##PreferenceStructure.Consistent.inter_sInter_maximals_nonempty). For an unranked structure
consistency is [joint realizability](##PreferenceStructure.consistent_discrete_iff), and for a
totally ranked one [realism over a nonempty information
state](##PreferenceStructure.consistent_iff_realistic_and_nonempty_of_isChain). *Want* relates an
agent to the maximal preferences of the structure its context supplies.

## Implementation notes

The ranking is a strict order on all of `Set W` of which only the restriction to the preferences is
observed, as with mathlib's `IsChain r s` and `IsAntichain r s`.

## References

* [condoravdi-lauer-2011]
* [condoravdi-lauer-2012]
* [condoravdi-lauer-2016]
* [lauer-2013]
* [lauer-condoravdi-2014]
* [zimmermann-2006]
-/

@[expose] public section

variable {W : Type*}

/-- A preference structure is a set of propositions `prefs` with a strict ranking `prec`, where
`prec p q` reads "`q` is strictly preferred to `p`". -/
structure PreferenceStructure (W : Type*) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking, where `prec p q` reads "`q` is strictly preferred to `p`". -/
  prec : Set W → Set W → Prop
  /-- The ranking is a strict partial order. -/
  isStrictOrder : IsStrictOrder (Set W) prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder (Set W) P.prec := P.isStrictOrder

/-- The maximal preferences are those with no preference strictly above them. -/
def maximals : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maximals {φ : Set W} :
    φ ∈ P.maximals ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maximals_subset_prefs : P.maximals ⊆ P.prefs := fun _ h ↦ h.1

theorem isAntichain_maximals : IsAntichain P.prec P.maximals :=
  fun _ hp _ hq _ h ↦ hp.2 _ hq.1 h

/-- A preference structure is consistent with an information state `B` when every family of
preferences whose joint realization `B` rules out contains a strictly ranked pair. -/
def Consistent (B : Set W) : Prop :=
  ∀ X ⊆ P.prefs, B ∩ ⋂₀ X = ∅ → ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- A preference structure is realistic with respect to an information state when every preference
is compatible with it. -/
def Realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, (B ∩ p).Nonempty

section Consistent

variable {P} {B : Set W}

/-- A structure is consistent exactly when every family of mutually unranked preferences is
jointly realizable. -/
theorem consistent_iff_forall_isAntichain :
    P.Consistent B ↔ ∀ X ⊆ P.prefs, IsAntichain P.prec X → (B ∩ ⋂₀ X).Nonempty := by
  refine forall₂_congr fun X _ ↦ ⟨fun h hX ↦ Set.nonempty_iff_ne_empty.2 fun hB ↦ ?_, fun h hB ↦ ?_⟩
  · obtain ⟨p, hp, q, hq, hpq⟩ := h hB
    exact hX hp hq (ne_of_irrefl hpq) hpq
  · by_contra! hn
    exact (h fun p hp q hq _ ↦ hn p hp q hq).ne_empty hB

/-- Consistency relative to an information state persists to any weaker one. -/
theorem Consistent.mono {H : Set W} (hC : P.Consistent B) (h : B ⊆ H) : P.Consistent H :=
  fun X hX hXH ↦ hC X hX (Set.subset_eq_empty (Set.inter_subset_inter_left _ h) hXH)

/-- Consistency entails realism. -/
theorem Consistent.realistic (hC : P.Consistent B) : P.Realistic B := fun p hp ↦ by
  simpa using consistent_iff_forall_isAntichain.1 hC {p} (by simpa) .singleton

/-- No structure is consistent with the empty information state. -/
theorem Consistent.nonempty (hC : P.Consistent B) : B.Nonempty := by
  simpa using consistent_iff_forall_isAntichain.1 hC ∅ (Set.empty_subset _) .empty

/-- The maximal preferences of a consistent structure are jointly realizable. -/
theorem Consistent.inter_sInter_maximals_nonempty (hC : P.Consistent B) :
    (B ∩ ⋂₀ P.maximals).Nonempty :=
  consistent_iff_forall_isAntichain.1 hC _ P.maximals_subset_prefs P.isAntichain_maximals

/-- Two maximal preferences of a consistent structure are jointly realizable, which blocks
conflicting desires. -/
theorem Consistent.inter_inter_nonempty_of_mem_maximals (hC : P.Consistent B) {φ ψ : Set W}
    (hφ : φ ∈ P.maximals) (hψ : ψ ∈ P.maximals) : (B ∩ (φ ∩ ψ)).Nonempty :=
  hC.inter_sInter_maximals_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.sInter_subset_of_mem hφ) (Set.sInter_subset_of_mem hψ)

/-- A preference that the information rules out together with a maximal one is ranked strictly
below it. -/
theorem Consistent.prec_of_mem_maximals (hC : P.Consistent B) {p q : Set W}
    (hp : p ∈ P.maximals) (hq : q ∈ P.prefs) (h : B ∩ (p ∩ q) = ∅) : P.prec q p := by
  by_contra hqp
  refine (consistent_iff_forall_isAntichain.1 hC {p, q} (Set.pair_subset hp.1 hq) ?_).ne_empty
    (by rwa [Set.sInter_pair])
  exact isAntichain_insert.2 ⟨.singleton, by rintro _ rfl -; exact ⟨hp.2 _ hq, hqp⟩⟩

/-- Under a total ranking, consistency is realism with respect to a nonempty information state. -/
theorem consistent_iff_realistic_and_nonempty_of_isChain (hc : IsChain P.prec P.prefs) :
    P.Consistent B ↔ P.Realistic B ∧ B.Nonempty := by
  refine ⟨fun hC ↦ ⟨hC.realistic, hC.nonempty⟩, fun ⟨hR, hB⟩ ↦
    consistent_iff_forall_isAntichain.2 fun X hX hXa ↦ ?_⟩
  rcases (subsingleton_of_isChain_of_isAntichain (hc.mono hX) hXa).eq_empty_or_singleton with
    rfl | ⟨p, rfl⟩
  · simpa using hB
  · simpa using hR p (hX rfl)

end Consistent

/-! ### Unranked preferences -/

/-- The discrete structure has the preferences `S` and no ranking, so all of them are maximal. -/
@[simps]
def discrete (S : Set (Set W)) : PreferenceStructure W where
  prefs := S
  prec _ _ := False
  isStrictOrder := { irrefl := fun _ h ↦ h, trans := fun _ _ _ h _ ↦ h }

@[simp] theorem maximals_discrete (S : Set (Set W)) : (discrete S).maximals = S :=
  Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, fun _ _ h ↦ h⟩⟩

theorem mem_maximals_discrete {S : Set (Set W)} {p : Set W} (h : p ∈ S) :
    p ∈ (discrete S).maximals :=
  (maximals_discrete S).symm.subset h

/-- Unranked preferences are consistent exactly when they are jointly realizable. -/
theorem consistent_discrete_iff {S : Set (Set W)} {B : Set W} :
    (discrete S).Consistent B ↔ (B ∩ ⋂₀ S).Nonempty :=
  consistent_iff_forall_isAntichain.trans ⟨fun h ↦ h S subset_rfl fun _ _ _ _ _ h ↦ h,
    fun h _ hX _ ↦ h.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hX))⟩

/-- The structure with the single preference `p`. -/
abbrev single (p : Set W) : PreferenceStructure W := discrete {p}

theorem consistent_single_iff {p B : Set W} : (single p).Consistent B ↔ (B ∩ p).Nonempty := by
  rw [consistent_discrete_iff, Set.sInter_singleton]

/-! ### Ranking one preference below another -/

/-- The structure on `S` that ranks `p` strictly below `q` and leaves the rest unranked. -/
@[simps]
def rankBelow (S : Set (Set W)) {p q : Set W} (h : p ≠ q) : PreferenceStructure W where
  prefs := S
  prec r s := r = p ∧ s = q
  isStrictOrder :=
    { irrefl := fun _ hr ↦ h (hr.1.symm.trans hr.2)
      trans := fun _ _ _ hr hs ↦ absurd (hr.2.symm.trans hs.1) h.symm }

section rankBelow

variable {S : Set (Set W)} {p q : Set W} (h : p ≠ q)

/-- Once `q` is a preference, everything but `p` is maximal. -/
theorem maximals_rankBelow (hq : q ∈ S) : (rankBelow S h).maximals = S \ {p} :=
  Set.ext fun _ ↦ ⟨fun hr ↦ ⟨hr.1, fun hrp ↦ hr.2 q hq ⟨hrp, rfl⟩⟩,
    fun hr ↦ ⟨hr.1, fun _ _ hs ↦ hr.2 hs.1⟩⟩

/-- Ranking `p` below `q` makes the structure consistent exactly when the preferences without `p`
and those without `q` are each jointly realizable. -/
theorem consistent_rankBelow_iff {B : Set W} :
    (rankBelow S h).Consistent B ↔
      (B ∩ ⋂₀ (S \ {p})).Nonempty ∧ (B ∩ ⋂₀ (S \ {q})).Nonempty := by
  rw [consistent_iff_forall_isAntichain]
  refine ⟨fun hC ↦ ⟨hC _ Set.sdiff_subset fun _ hr _ _ _ hrs ↦ hr.2 hrs.1,
    hC _ Set.sdiff_subset fun _ _ _ hs _ hrs ↦ hs.2 hrs.2⟩, fun ⟨hp, hq⟩ X hX hXa ↦ ?_⟩
  have sub {r : Set W} (hr : r ∉ X) : B ∩ ⋂₀ (S \ {r}) ⊆ B ∩ ⋂₀ X :=
    Set.inter_subset_inter_right _ <| Set.sInter_subset_sInter fun x hx ↦
      ⟨hX hx, fun hxr ↦ hr (hxr ▸ hx)⟩
  by_cases hpX : p ∈ X
  exacts [hq.mono (sub fun hqX ↦ hXa hpX hqX h ⟨rfl, rfl⟩), hp.mono (sub hpX)]

end rankBelow

end PreferenceStructure

/-! ### Effective-preference *want* -/

namespace Desire.Preferential

variable {Agent : Type*} (P : Agent → W → PreferenceStructure W) (a : Agent) (φ : Set W) (w : W)

/-- On the exact-match reading, `a` wants `φ` at `w` when `φ` is itself a maximal preference of
the structure `P a w`. -/
def Want : Prop := φ ∈ (P a w).maximals

/-- On the success-oriented reading, `a` wants `φ` when `φ` entails a maximal preference, which
`φ` then satisfies. -/
def WantSuccessOriented : Prop := ∃ p ∈ (P a w).maximals, φ ⊆ p

/-- On the Quine–Hintikka reading, `a` wants `φ` when a maximal preference entails `φ`, so that the
preference is satisfied only if `φ` holds. -/
def WantQuineHintikka : Prop := ∃ p ∈ (P a w).maximals, p ⊆ φ

variable {P a φ w}

theorem Want.wantSuccessOriented (h : Want P a φ w) : WantSuccessOriented P a φ w :=
  ⟨φ, h, subset_rfl⟩

theorem Want.wantQuineHintikka (h : Want P a φ w) : WantQuineHintikka P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-- Over a consistent background a proposition and its negation are not both wanted. -/
theorem Want.not_compl {B : Set W} (hC : (P a w).Consistent B) (h : Want P a φ w) :
    ¬ Want P a φᶜ w := fun hn ↦
  (hC.inter_inter_nonempty_of_mem_maximals h hn).ne_empty <| by
    rw [Set.inter_compl_self, Set.inter_empty]

/-- The success-oriented reading is downward entailing. -/
theorem antitone_wantSuccessOriented : Antitone (WantSuccessOriented P a · w) :=
  fun _ _ hφψ ⟨p, hp, hψp⟩ ↦ ⟨p, hp, hφψ.trans hψp⟩

/-- The Quine–Hintikka reading is upward entailing. -/
theorem monotone_wantQuineHintikka : Monotone (WantQuineHintikka P a · w) :=
  fun _ _ hφψ ⟨p, hp, hpφ⟩ ↦ ⟨p, hp, hpφ.trans hφψ⟩

end Desire.Preferential
