module

public import Linglib.Core.Order.Minimals
public import Mathlib.Data.Set.Finite.Basic

/-!
# Conditional desire semantics

On Heim's conditional semantics, *a wants p* holds at `w` when for every belief world `w'`, every
`p`-world maximally similar to `w'` is more desirable than every non-`p`-world maximally similar
to `w'`, with similarity as in Stalnaker and Lewis. Heim states the rule first with the similar
worlds drawn from all worlds, then, as a context change rule, with them drawn from the belief
worlds alone, so `Desire.Conditional.Want` takes the domain of comparison as an argument. On the
belief worlds the rule makes a believed `p` trivially wanted, and so its negation; her amendment,
that the ascription is undefined when `p` or its negation is already believed, is
`Desire.IsContingent`, which von Fintel's best-worlds *want* shares. Under it an antisymmetric
desirability relation cannot make both `p` and `¬p` wanted.

## Main definitions

* `Desire.Conditional.Frame`: similarity preorders with comparative desirability at each world.
* `Desire.Conditional.Frame.closest`: the `p`-worlds of a domain maximally similar to a world.
* `Desire.Conditional.Want`, `Desire.IsContingent`: Heim's rule over a domain of comparison, and
  her amendment.

## Main results

* `Desire.Conditional.Want.not_compl`: under the amendment, `p` and `¬p` are not both wanted.

## References

* [heim-1992]
* [stalnaker-1968]
* [lewis-1973b]
* [von-fintel-1999]
-/

@[expose] public section


namespace Desire

variable {W : Type*}

/-- A domain `D` is contingent on `p` when it contains both `p`-worlds and non-`p`-worlds, what
Heim's (40) amendment requires of the belief worlds, and von Fintel adopts as presuppositions of
*want*. -/
def IsContingent (D p : Set W) : Prop := (D ∩ p).Nonempty ∧ (D \ p).Nonempty

instance [Fintype W] {D p : Set W} [DecidablePred (· ∈ D)] [DecidablePred (· ∈ p)] :
    Decidable (IsContingent D p) :=
  inferInstanceAs (Decidable ((∃ x, x ∈ D ∩ p) ∧ ∃ x, x ∈ D \ p))

end Desire

namespace Desire.Conditional

variable {W : Type*}

/-- A frame has similarity preorders on worlds and comparative desirability, `pref w x y` saying
that at evaluation world `w`, `x` is more desirable than `y`. -/
structure Frame (W : Type*) where
  /-- Similarity to each world. -/
  sim : W → Preorder W
  /-- Comparative desirability at each evaluation world. -/
  pref : W → W → W → Prop

variable (F : Frame W) (D bel : Set W) (w : W) (p : Set W)

/-- `F.closest D p w'`, Heim's `Sim_w'(p)` with the similar worlds drawn from `D`, is the set of
`p`-worlds of `D` that are maximally similar to `w'`. -/
def Frame.closest (w' : W) : Set W := (F.sim w').minimals (D ∩ p)

/-- `a wants p` at `w`, the similar worlds drawn from `D`, when for every belief-world `w'`, every
closest `p`-world to `w'` is more desirable than every closest `¬p`-world to `w'`. Heim's (31)
draws them from all worlds, `D = univ`, and her context change rule (39) from the belief worlds,
`D = bel`. -/
def Want : Prop :=
  ∀ w' ∈ bel, ∀ x ∈ F.closest D p w', ∀ y ∈ F.closest D pᶜ w', F.pref w x y

section Decidable

instance [Fintype W] [∀ w, DecidableRel (F.sim w).le] [DecidablePred (· ∈ D)]
    [DecidablePred (· ∈ p)] (w' : W) : DecidablePred (· ∈ F.closest D p w') :=
  inferInstanceAs (DecidablePred (· ∈ (F.sim w').minimals (D ∩ p)))

instance [Fintype W] [∀ w, DecidableRel (F.sim w).le] [DecidablePred (· ∈ D)]
    [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] [∀ w, DecidableRel (F.pref w)] :
    Decidable (Want F D bel w p) :=
  inferInstanceAs
    (Decidable (∀ w' ∈ bel, ∀ x ∈ F.closest D p w', ∀ y ∈ F.closest D pᶜ w', F.pref w x y))

end Decidable

variable {F D bel p w}

/-- When the domain of comparison is contingent on `p`, as (40) requires of the belief worlds,
an antisymmetric desirability relation cannot make both `p` and `¬p` wanted. -/
theorem Want.not_compl [Finite W] [Std.Antisymm (F.pref w)] (hb : bel.Nonempty)
    (hd : IsContingent D p) (hp : Want F D bel w p) : ¬ Want F D bel w pᶜ := by
  intro hnp
  obtain ⟨w', hw'⟩ := hb
  obtain ⟨x, hx⟩ := (F.sim w').minimals_nonempty_of_finite (Set.toFinite _) hd.1
  obtain ⟨y, hy⟩ := (F.sim w').minimals_nonempty_of_finite (Set.toFinite _) hd.2
  have hxy : x = y :=
    antisymm (hp w' hw' x hx y hy) (hnp w' hw' y hy x (by simpa [Frame.closest] using hx))
  exact (Preorder.minimals_subset _ _ hy).2 (hxy ▸ (Preorder.minimals_subset _ _ hx).2)

end Desire.Conditional
