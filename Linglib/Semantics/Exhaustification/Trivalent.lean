module

public import Linglib.Semantics.Exhaustification.Finite
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Trivalent exhaustification

This file defines Spector and Sudo's two trivalent exhaustification operators. Both assert the
prejacent and deny its innocently excludable alternatives, computed by Fox's algorithm on the
classical truth conditions; they differ in the negation applied to a denied alternative. `exh1` uses
weak negation, under which an undefined alternative counts as denied, so the operator is undefined
exactly where the prejacent is (`exh1_eq_zero_iff`). `exh2` uses strong negation, under which an
undefined alternative leaves the whole undefined, so the operator inherits the presuppositions of
the alternatives it denies (`exh2_eq_zero_iff`).

## Implementation notes

The innocently excludable alternatives are `Exhaustification.innocent.excluded` applied to the
classical parts of the trivalent propositions, where the classical part sends `1` to `true` and
both `-1` and `0` to `false`.

## References

* [spector-sudo-2017]
* [fox-2007]
-/

@[expose] public section

namespace Exhaustification.Trivalent

open Exhaustification

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The classical truth conditions of a trivalent proposition hold exactly where it is `1`. -/
def classicalPart (p : W → SignType) : W → Bool :=
  fun w ↦ decide (p w = 1)

/-- The innocently excludable alternatives of a trivalent prejacent, computed classically. -/
def excluded (alts : List (W → SignType)) (p : W → SignType) :
    Finset (Finset W) :=
  innocent.excluded (altsFromPreds (alts.map classicalPart)) (predToFinset (classicalPart p))

/-- Weak-negation exhaustification is `1` where the prejacent is `1` and no excludable
alternative is, `-1` where the prejacent is `-1` or some excludable alternative is `1`, and `0`
where the prejacent is `0`. -/
def exh1 (alts : List (W → SignType)) (p : W → SignType) :
    W → SignType :=
  fun w ↦ match p w with
    | .zero => 0
    | .neg => -1
    | .pos =>
      if alts.all fun q ↦
        if predToFinset (classicalPart q) ∈ excluded alts p then q w != 1 else true
      then 1
      else -1

/-- Strong-negation exhaustification is `0` where the prejacent or some excludable alternative
is `0`, `1` where the prejacent is `1` and every excludable alternative is `-1`, and `-1`
otherwise. -/
def exh2 (alts : List (W → SignType)) (p : W → SignType) :
    W → SignType :=
  fun w ↦
    if alts.any fun q ↦ predToFinset (classicalPart q) ∈ excluded alts p ∧ q w == 0
    then 0
    else match p w with
      | .zero => 0
      | .neg => -1
      | .pos =>
        if alts.all fun q ↦
          if predToFinset (classicalPart q) ∈ excluded alts p then q w == -1 else true
        then 1
        else -1

variable (alts : List (W → SignType)) (p : W → SignType) (w : W)

theorem exh1_eq_zero_iff : exh1 alts p w = 0 ↔ p w = 0 := by
  unfold exh1; split <;> (try split) <;> simp_all

theorem exh2_eq_zero_iff :
    exh2 alts p w = 0 ↔
      p w = 0 ∨
        ∃ q ∈ alts, predToFinset (classicalPart q) ∈ excluded alts p ∧ q w = 0 := by
  unfold exh2
  simp only [List.any_eq_true, decide_eq_true_eq, beq_iff_eq]
  split
  · exact iff_of_true rfl (Or.inr ‹_›)
  · split <;> (try split) <;> simp_all

theorem exh1_preserves_presup (h : p w = 0) : exh1 alts p w = 0 :=
  (exh1_eq_zero_iff alts p w).2 h

theorem exh2_preserves_presup (h : p w = 0) : exh2 alts p w = 0 :=
  (exh2_eq_zero_iff alts p w).2 (Or.inl h)

end Exhaustification.Trivalent
