module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Trivalent exhaustification

This file defines Spector and Sudo's two trivalent exhaustification operators. Both assert the
prejacent and deny its innocently excludable alternatives, computed by Fox's algorithm on the
classical truth conditions, the worlds where each proposition is `1`; they differ in the negation
applied to a denied alternative. `exh1` uses weak negation, under which an undefined alternative
counts as denied, so the operator is undefined exactly where the prejacent is (`exh1_eq_zero_iff`).
`exh2` uses strong negation, under which an undefined alternative leaves the whole undefined, so the
operator inherits the presuppositions of the alternatives it denies (`exh2_eq_zero_iff`).

## References

* [spector-sudo-2017]
* [fox-2007]
-/

@[expose] public section

namespace Exhaustification.Trivalent

open Exhaustification

variable {W ι : Type*} [Fintype W] [Fintype ι] (alts : ι → W → Trivalent) (p : W → Trivalent)

/-- An alternative is excluded when its classical truth conditions are innocently excludable given
the prejacent's. -/
def Excluded (i : ι) : Prop :=
  IsInnocentlyExcludable (Set.range fun j ↦ posExt (alts j)) (posExt p)
    (posExt (alts i))

instance (i : ι) : Decidable (Excluded alts p i) :=
  inferInstanceAs (Decidable (IsInnocentlyExcludable (Set.range fun j ↦ posExt (alts j))
    (posExt p) ((fun j ↦ posExt (alts j)) i)))

/-- Weak-negation exhaustification is `0` where the prejacent is, and elsewhere classical innocent
exclusion on the worlds where each proposition is `1`. -/
def exh1 (w : W) : Trivalent :=
  if p w = 0 then 0
  else if w ∈ exhIE (Set.range fun j ↦ posExt (alts j)) (posExt p) then 1 else -1

/-- Strong-negation exhaustification is `0` where the prejacent or some excluded alternative is,
`1` where the prejacent is `1` and every excluded alternative is `-1`, and `-1` otherwise. -/
def exh2 (w : W) : Trivalent :=
  if p w = 0 ∨ ∃ i, Excluded alts p i ∧ alts i w = 0 then 0
  else if p w = 1 ∧ ∀ i, Excluded alts p i → alts i w = -1 then 1 else -1

variable (w : W)

theorem exh1_eq_zero_iff : exh1 alts p w = 0 ↔ p w = 0 := by
  unfold exh1; split_ifs <;> simp_all

theorem exh2_eq_zero_iff :
    exh2 alts p w = 0 ↔ p w = 0 ∨ ∃ i, Excluded alts p i ∧ alts i w = 0 := by
  unfold exh2; split_ifs <;> simp_all

theorem exh1_preserves_presup (h : p w = 0) : exh1 alts p w = 0 :=
  (exh1_eq_zero_iff alts p w).2 h

theorem exh2_preserves_presup (h : p w = 0) : exh2 alts p w = 0 :=
  (exh2_eq_zero_iff alts p w).2 (Or.inl h)

end Exhaustification.Trivalent
