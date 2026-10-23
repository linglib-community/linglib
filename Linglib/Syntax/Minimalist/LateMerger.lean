module

public import Mathlib.Data.Nat.Notation

/-!
# Late merger

Late merger introduces a sub-constituent of a moved phrase countercyclically at a non-base
position of its movement chain: adjuncts in [lebeaux-1988], the NP restrictor of a determiner in
[takahashi-hulsey-2009]'s wholesale late merger, degree clauses in [bhatt-pancheva-2004]. The
flavors differ only in which chain positions admit the merger and share one Condition C profile:
late merger bleeds Condition C exactly when an admissible position lies strictly above the
pronoun binder. `LateMergerBleeds` is that profile, polymorphic in the position type and the
admissibility predicate, and `WLMBleedsCondC` its case-licensing instance on `ChainPosition`,
whose admissible positions are those where the resulting DP receives case; [gong-2022] shows
that reconstruction under scrambling tracks these case positions rather than the A/Ā
distinction.

## References

* [lebeaux-1988]
* [takahashi-hulsey-2009]
* [bhatt-pancheva-2004]
* [gong-2022]
-/

@[expose] public section

namespace Minimalist

variable {α : Type*} {admissible : α → Prop} {height : α → ℕ} {chain : List α} {binder : ℕ}

/-- Late merger bleeds Condition C when an admissible chain position lies strictly above the
binder. -/
def LateMergerBleeds (admissible : α → Prop) (height : α → ℕ) (chain : List α) (binder : ℕ) :
    Prop :=
  ∃ p ∈ chain, admissible p ∧ binder < height p

instance [DecidablePred admissible] :
    Decidable (LateMergerBleeds admissible height chain binder) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem lateMergerBleeds_cons_of (p : α) (hp : admissible p) (hgt : binder < height p) :
    LateMergerBleeds admissible height (p :: chain) binder :=
  ⟨p, List.mem_cons_self .., hp, hgt⟩

theorem LateMergerBleeds.cons (p : α) (h : LateMergerBleeds admissible height chain binder) :
    LateMergerBleeds admissible height (p :: chain) binder :=
  let ⟨q, hq, hpq⟩ := h; ⟨q, List.mem_cons_of_mem p hq, hpq⟩

theorem not_lateMergerBleeds_of_le (h : ∀ p ∈ chain, height p ≤ binder) :
    ¬ LateMergerBleeds admissible height chain binder :=
  λ ⟨p, hp, _, hgt⟩ => absurd hgt (Nat.not_lt.mpr (h p hp))

theorem not_lateMergerBleeds_of_none (h : ∀ p ∈ chain, ¬ admissible p) :
    ¬ LateMergerBleeds admissible height chain binder :=
  λ ⟨p, hp, hadm, _⟩ => h p hp hadm

/-- A position on a movement chain: its height and whether it admits the late merger, for NP
restrictors whether the DP receives case there. -/
structure ChainPosition where
  height : ℕ
  admissible : Bool
  deriving DecidableEq, Repr

/-- Wholesale late merger of an NP restrictor bleeds Condition C when a case position lies
strictly above the binder ([takahashi-hulsey-2009], [gong-2022]'s condition (2)). -/
def WLMBleedsCondC (chain : List ChainPosition) (binder : ℕ) : Prop :=
  LateMergerBleeds (·.admissible = true) ChainPosition.height chain binder

instance (chain : List ChainPosition) (binder : ℕ) : Decidable (WLMBleedsCondC chain binder) :=
  inferInstanceAs (Decidable (LateMergerBleeds _ _ _ _))

theorem wlmBleedsCondC_cons_of {chain : List ChainPosition} {binder h : ℕ} (hgt : binder < h) :
    WLMBleedsCondC (⟨h, true⟩ :: chain) binder :=
  lateMergerBleeds_cons_of _ rfl hgt

theorem not_wlmBleedsCondC_of_none {chain : List ChainPosition} {binder : ℕ}
    (h : ∀ p ∈ chain, p.admissible = false) : ¬ WLMBleedsCondC chain binder :=
  not_lateMergerBleeds_of_none λ p hp => by simp [h p hp]

end Minimalist
