module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Trivalent exhaustification

This file defines Spector and Sudo's two trivalent exhaustification operators. Both assert the
prejacent and deny its innocently excludable alternatives, computed by Fox's algorithm on the
classical truth conditions, the worlds where each proposition is true; they differ in the negation
applied to a denied alternative. `exh1` uses weak negation, under which an undefined alternative
counts as denied, so the operator is undefined exactly where the prejacent is (`exh1_eq_undefined_iff`).
`exh2` uses strong negation, under which an undefined alternative leaves the whole undefined, so the
operator inherits the presuppositions of the alternatives it denies (`exh2_eq_undefined_iff`).

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
  IsInnocentlyExcludable (Set.range fun j ↦ Trivalent.posExt (alts j)) (Trivalent.posExt p)
    (Trivalent.posExt (alts i))

instance (i : ι) : Decidable (Excluded alts p i) :=
  inferInstanceAs (Decidable (IsInnocentlyExcludable (Set.range fun j ↦ Trivalent.posExt (alts j))
    (Trivalent.posExt p) ((fun j ↦ Trivalent.posExt (alts j)) i)))

/-- Weak-negation exhaustification is undefined where the prejacent is, and elsewhere classical
innocent exclusion on the worlds where each proposition is true. -/
def exh1 (w : W) : Trivalent :=
  if p w = .undefined then .undefined
  else if w ∈ exhIE (Set.range fun j ↦ Trivalent.posExt (alts j)) (Trivalent.posExt p) then .true else .false

/-- Strong-negation exhaustification is undefined where the prejacent or some excluded alternative
is, true where the prejacent is true and every excluded alternative false, and false otherwise. -/
def exh2 (w : W) : Trivalent :=
  if p w = .undefined ∨ ∃ i, Excluded alts p i ∧ alts i w = .undefined then .undefined
  else if p w = .true ∧ ∀ i, Excluded alts p i → alts i w = .false then .true else .false

variable (w : W)

theorem exh1_eq_undefined_iff : exh1 alts p w = .undefined ↔ p w = .undefined := by
  unfold exh1; split_ifs <;> simp_all

theorem exh2_eq_undefined_iff :
    exh2 alts p w = .undefined ↔ p w = .undefined ∨ ∃ i, Excluded alts p i ∧ alts i w = .undefined := by
  unfold exh2; split_ifs <;> simp_all

theorem exh1_preserves_presup (h : p w = .undefined) : exh1 alts p w = .undefined :=
  (exh1_eq_undefined_iff alts p w).2 h

theorem exh2_preserves_presup (h : p w = .undefined) : exh2 alts p w = .undefined :=
  (exh2_eq_undefined_iff alts p w).2 (Or.inl h)

end Exhaustification.Trivalent
