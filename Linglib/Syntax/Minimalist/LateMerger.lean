module

public import Mathlib.Data.Nat.Notation

/-!
# Late merger

Late merger introduces a sub-constituent of a moved phrase countercyclically at a non-base
position of its movement chain: adjuncts in [lebeaux-1988], the NP restrictor of a determiner at
the positions where the DP receives case in [takahashi-hulsey-2009]'s wholesale late merger, and
a degree clause at the scope of its degree head in [bhatt-pancheva-2004]. The flavors differ only
in which chain positions admit the merger and share one Condition C profile: late merger bleeds
Condition C exactly when an admissible position lies strictly above the pronoun binder.
`LateMergerBleeds` is that profile, polymorphic in the positions, their heights and the
admissibility predicate.

## References

* [lebeaux-1988]
* [takahashi-hulsey-2009]
* [bhatt-pancheva-2004]
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

end Minimalist
