/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Control.Defs

/-!
# Control: Basic Lemmas

Lemmas about the control vocabulary of `Syntax/Control/Defs.lean`: exhaustive control
(refinement, composition, and the exclusion of partial readings and split antecedents), the
localization of a partial reading to a leg of a composite dependency, saturation, and the
mismatch argument by which the overt-copy diagnostics of Polinsky and Potsdam refute a shared
occupant.

## References

* [landau-2000]
* [bresnan-1982]
* [polinsky-potsdam-2006]
-/

@[expose] public section

namespace Control

open SetRel

/-! ### Exhaustive control -/

variable {Pos Ref : Type*} {val : Pos → Ref} {ante bind pred d : SetRel Pos Pos}
  {a b p q c : Pos}

/-- Related positions of an exhaustive dependency are co-valued. -/
theorem IsExhaustive.eq (hs : IsExhaustive val ante) (h : a ~[ante] b) :
    val a = val b :=
  hs h

/-- A refinement of an exhaustive dependency is exhaustive. -/
theorem IsExhaustive.mono (h : ante ⊆ bind) (hs : IsExhaustive val bind) :
    IsExhaustive val ante :=
  h.trans hs

/-- Exhaustivity composes through the mediating position. -/
theorem IsExhaustive.comp (hb : IsExhaustive val bind)
    (hp : IsExhaustive val pred) : IsExhaustive val (bind ○ pred) := by
  rintro ⟨a, c⟩ ⟨m, ham, hmc⟩
  exact (hb.eq ham).trans (hp.eq hmc)

/-- Exhaustive control excludes partial readings ([landau-2000]): no referent grows strictly
along the dependency. -/
theorem IsExhaustive.not_lt [Preorder Ref] (hs : IsExhaustive val ante)
    (h : a ~[ante] b) : ¬ val a < val b := by
  simp [hs.eq h]

/-- Under exhaustive control, joint antecedents are co-valued, so split control needs a
non-exhaustive leg. -/
theorem IsExhaustive.eq_of_two (hs : IsExhaustive val ante)
    (ha : a ~[ante] p) (hb : b ~[ante] p) : val a = val b :=
  (hs.eq ha).trans (hs.eq hb).symm

/-- An exhaustive dependency admits no partial reading. -/
theorem IsExhaustive.not_isPartial [Preorder Ref]
    (h : IsExhaustive val d) : ¬ IsPartial val d :=
  fun ⟨_, _, hab, hlt⟩ ↦ absurd (h.eq hab) hlt.ne

/-- A partial reading in a composite localizes to a leg. If referents grow monotonely along the
first leg and strictly across the composite, one of the two legs already grows strictly. -/
theorem exists_lt_of_comp_lt [PartialOrder Ref]
    (hb : ∀ ⦃x m⦄, x ~[bind] m → val x ≤ val m)
    (h : a ~[bind ○ pred] c) (hlt : val a < val c) :
    (∃ x m, x ~[bind] m ∧ val x < val m) ∨
      ∃ m x, m ~[pred] x ∧ val m < val x := by
  obtain ⟨m, ham, hmc⟩ := h
  rcases (hb ham).lt_or_eq with hlt' | heq
  · exact Or.inl ⟨a, m, ham, hlt'⟩
  · exact Or.inr ⟨m, c, hmc, heq ▸ hlt⟩

/-! ### Saturation -/

/-- A saturating dependency admits no partial reading. -/
theorem IsSaturating.not_isPartial [Preorder Ref] (h : IsSaturating val d) :
    ¬ IsPartial val d :=
  h.exhaustive.not_isPartial

/-- A saturating dependency admits no split, since joint controllers coincide. -/
theorem IsSaturating.eq_of_controllers (h : IsSaturating val d)
    (ha : a ~[d] p) (hb : b ~[d] p) : a = b :=
  h.biUnique.1 ha hb

/-- A saturating dependency admits no split antecedents. -/
theorem IsSaturating.not_isSplit (h : IsSaturating val d) : ¬ IsSplit d :=
  not_not_intro h.biUnique.1

/-- A saturating controller saturates a single slot, so its dependents coincide. -/
theorem IsSaturating.eq_of_controlled (h : IsSaturating val d)
    (hp : a ~[d] p) (hq : a ~[d] q) : p = q :=
  h.biUnique.2 hp hq

/-! ### Enforcement

Which assignment a dependency exhaustively shares distinguishes the enforcement species
([bresnan-1982]). Functional control shares the occupant assignment itself (structure sharing,
movement chains, LFG control equations), anaphoric control only the referent valuation. Occupant
sharing is the stronger: a shared assignment transports along every map of it
(`IsExhaustive.map`), so every occupant property transports across the dependency
(`IsExhaustive.iff_of_rel`), and one observed mismatch refutes it
(`not_isExhaustive_of_mismatch`), the argument of the overt-copy diagnostics
([polinsky-potsdam-2006]). -/

variable {Item : Type*} {occ : Pos → Item}

/-- Sharing an assignment transports along any map of it: token identity yields referential
co-valuation for every referent map. -/
theorem IsExhaustive.map (hs : IsExhaustive occ ante) (f : Item → Ref) :
    IsExhaustive (f ∘ occ) ante := by
  rintro ⟨a, b⟩ h
  exact congrArg f (hs.eq h)

/-- Under a shared assignment, every property of the assigned value transports across the
dependency, so copies are indistinguishable. -/
theorem IsExhaustive.iff_of_rel (hs : IsExhaustive occ ante)
    (h : a ~[ante] b) (P : Item → Prop) : P (occ a) ↔ P (occ b) :=
  iff_of_eq (congrArg P (hs.eq h))

/-- One observed mismatch refutes a shared assignment, the argument of the copy-control
diagnostics. -/
theorem not_isExhaustive_of_mismatch {P : Item → Prop} (h : a ~[ante] b)
    (hPa : P (occ a)) (hPb : ¬ P (occ b)) : ¬ IsExhaustive occ ante :=
  fun hs ↦ hPb (hs.eq h ▸ hPa)

end Control
