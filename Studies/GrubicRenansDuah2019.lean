/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Data.Examples.GrubicRenansDuah2019
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Grubic, Renans, and Duah (2019): Focus, Exhaustivity and Existence in Akan, Ga and Ngamo

Grubic, Renans and Duah analyse the marked focus/background constructions of Akan, Ga and Ngamo
(section 8), whose data, the rows of `Data.Examples.GrubicRenansDuah2019`, they collect in
sections 5 and 6. In none of the three is the exhaustive inference asserted: negating the
construction targets the prejacent, so an additive continuation loses its antecedent, where
negating overt *only*, the substrate's `Focus.only`, keeps it. The Akan *nà* and Ga
*ni* constructions are clefts that assert the prejacent and presuppose conditional exhaustivity,
that if the prejacent holds no other alternative does, together with existence. The Ngamo
*=i/ye* construction only presupposes that its background is salient.

## Implementation notes

Constructions are trivalent propositions over an arbitrary set of alternatives containing the
prejacent, so the theorems are general rather than checked on a two-world model. The background
of (78) is the existential closure of the alternatives, and its salience an abstract predicate on
propositions. Section 4's contrast finding, which the paper concludes is pragmatic rather than
conventional, and section 7's argument that salience is not givenness are not formalized.

## References

* [grubic-renans-duah-2019]
* [kiss-1998]
-/

@[expose] public section

namespace GrubicRenansDuah2019

open Exhaustification Presupposition Focus

variable {W : Type*} (alts : Set (Set W)) (p : Set W)

open Classical in
/-- The Akan *nà* and Ga *ni* constructions, (75) and (76), assert the prejacent and presuppose
conditional exhaustivity together with existence. -/
noncomputable def cleft : W → Trivalent := fun w ↦
  Trivalent.transplication (Trivalent.ofProp ((w ∈ p → w ∈ excludes alts p) ∧ w ∈ ⋃₀ alts))
    (Trivalent.ofProp (w ∈ p))

open Classical in
/-- The Ngamo *=i/ye* construction (78) asserts the prejacent and presupposes the salience of the
background, the existential closure of the alternatives. -/
noncomputable def marked (salient : Set W → Prop) : W → Trivalent := fun w ↦
  Trivalent.transplication (Trivalent.ofProp (salient (⋃₀ alts))) (Trivalent.ofProp (w ∈ p))

/-! ### The exhaustive inference is not asserted, section 5.2.1 -/

/-- Negated overt *only* keeps the prejacent and verifies a non-entailed alternative, giving *also*
its antecedent ((36b), (37b)). -/
theorem negated_only_licenses_also {w : W} (h : (only (· ⊆ ·) alts id p w)ᶜ = .true) :
    w ∈ p ∧ ∃ q ∈ alts, ¬ p ⊆ q ∧ w ∈ q := by
  rw [Trivalent.compl_eq_true_iff, only_eq_false_iff] at h
  refine ⟨atLeast_subset_subset h.1, ?_⟩
  by_contra hno
  push Not at hno
  exact h.2 fun q hq hwq ↦ by_contra fun hne ↦ hno q hq hne hwq

/-- Negating a marked construction targets the prejacent, so *also* lacks its antecedent, (36a)
to (38a). -/
theorem negated_cleft_notMem {w : W} (h : (cleft alts p w)ᶜ = .true) : w ∉ p := by
  simp_all [cleft]

/-! ### Implicature in Ngamo, presupposition in Akan and Ga, section 5.2.2 -/

/-- The Ngamo construction holds with its presupposition where a non-entailed alternative also
holds, so its exhaustivity is cancellable ((42), (45)). -/
theorem marked_exhaustivity_cancellable {salient : Set W → Prop} {q : Set W} {w : W}
    (hs : salient (⋃₀ alts)) (hq : q ∈ alts) (hne : ¬ p ⊆ q) (hw : w ∈ p ∩ q) :
    marked alts p salient w = .true ∧ w ∉ excludes alts p :=
  ⟨by simp [marked, hs, hw.1], fun h ↦ hne (h q hq hw.2)⟩

/-- Where defined and true, the cleft is exhaustive ((43), (44), (77)), so it cannot answer a
mention-some question ((49), (50)). -/
theorem cleft_exhaustive {w : W} (h : cleft alts p w = .true) : w ∈ excludes alts p := by
  simp only [cleft, Trivalent.transplication_eq_true_iff, Trivalent.ofProp_eq_true_iff] at h
  exact h.1.1 h.2

/-- A negated cleft is true where the prejacent fails and another alternative holds, so the
conditional presupposition projects (54). -/
theorem cleft_neg_of_alt {q : Set W} {w : W} (hq : q ∈ alts) (hw : w ∈ q) (hp : w ∉ p) :
    (cleft alts p w)ᶜ = .true := by
  simpa [cleft, hp] using ⟨q, hq, hw⟩

/-! ### Existence, section 6 -/

/-- The cleft presupposes that some alternative holds, so a focused negative quantifier clashes
with it ((60) and (61)). -/
theorem cleft_existence {w : W} (h : cleft alts p w ≠ .undefined) : w ∈ ⋃₀ alts := by
  simp only [cleft, ne_eq, Trivalent.transplication_eq_undefined_iff,
    Trivalent.ofProp_eq_true_iff, Trivalent.ofProp_ne_undefined, or_false, not_not] at h
  exact h.2

/-- The Ngamo construction is defined at a world where no alternative holds, so it carries no
existence presupposition (59). -/
theorem marked_of_not_exists {salient : Set W → Prop} (hs : salient (⋃₀ alts)) {w : W}
    (_ : w ∉ ⋃₀ alts) : marked alts p salient w ≠ .undefined := by
  simp [marked, hs]

end GrubicRenansDuah2019
