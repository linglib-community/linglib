module

public import Linglib.Core.Order.Minimals
public import Mathlib.Data.Set.Finite.Basic

/-!
# Conditional desire semantics

On Heim's conditional semantics, *a wants p* holds at `w` when for every belief world `w'`, every
`p`-world maximally similar to `w'` is more desirable than every non-`p`-world maximally similar
to `w'`, with the comparison restricted to the belief state and similarity as in Stalnaker and
Lewis. Her amendment, that the ascription is undefined when `p` or its negation is already
believed, is `Desire.IsContingent`, which von Fintel's best-worlds *want* shares; under it an
antisymmetric desirability relation cannot make both `p` and `¬p` wanted.

## Main definitions

* `Desire.Conditional.Frame`: similarity preorders with comparative desirability at each world.
* `Desire.Conditional.Frame.closest`: the `p`-worlds of the belief state maximally similar to a
  world.
* `Desire.Conditional.Want`, `Desire.IsContingent`: Heim's (31) and her (40) amendment.

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

/-- A domain `D` is contingent on `p` when it contains both `p`-worlds and non-`p`-worlds, Heim's
(40) amendment, which von Fintel adopts as presuppositions of *want*. -/
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

variable (F : Frame W) (bel : Set W) (w : W) (p : Set W)

/-- `F.closest bel p w'`, Heim's `Sim_w'(Bel ∩ p)`, is the set of belief-worlds satisfying `p`
that are maximally similar to `w'`. -/
def Frame.closest (w' : W) : Set W := (F.sim w').minimals (bel ∩ p)

/-- `a wants p` at `w` when for every belief-world `w'`, every closest `p`-world to `w'` is more
desirable than every closest `¬p`-world to `w'`. -/
def Want : Prop :=
  ∀ w' ∈ bel, ∀ x ∈ F.closest bel p w', ∀ y ∈ F.closest bel pᶜ w', F.pref w x y

section Decidable

instance [Fintype W] [∀ w, DecidableRel (F.sim w).le] [DecidablePred (· ∈ bel)]
    [DecidablePred (· ∈ p)] (w' : W) : DecidablePred (· ∈ F.closest bel p w') :=
  inferInstanceAs (DecidablePred (· ∈ (F.sim w').minimals (bel ∩ p)))

instance [Fintype W] [∀ w, DecidableRel (F.sim w).le] [DecidablePred (· ∈ bel)]
    [DecidablePred (· ∈ p)] [∀ w, DecidableRel (F.pref w)] : Decidable (Want F bel w p) :=
  inferInstanceAs
    (Decidable (∀ w' ∈ bel, ∀ x ∈ F.closest bel p w', ∀ y ∈ F.closest bel pᶜ w', F.pref w x y))

end Decidable

variable {F bel p w}

/-- Under (40) and antisymmetric desirability, `p` and `¬p` cannot both be wanted. -/
theorem Want.not_compl [Finite W] [Std.Antisymm (F.pref w)] (hd : IsContingent bel p)
    (hp : Want F bel w p) : ¬ Want F bel w pᶜ := by
  intro hnp
  obtain ⟨⟨w', hw'⟩, hn⟩ := hd
  obtain ⟨x, hx⟩ := (F.sim w').minimals_nonempty_of_finite (Set.toFinite _) ⟨w', hw'⟩
  obtain ⟨y, hy⟩ := (F.sim w').minimals_nonempty_of_finite (Set.toFinite _) hn
  have hxy : x = y :=
    antisymm (hp w' hw'.1 x hx y hy)
      (hnp w' hw'.1 y hy x (by simpa [Frame.closest] using hx))
  exact (Preorder.minimals_subset _ _ hy).2 (hxy ▸ (Preorder.minimals_subset _ _ hx).2)

end Desire.Conditional
