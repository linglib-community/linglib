/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Control.Defs

/-!
# Control: Basic Lemmas

Lemmas about the control vocabulary of `Syntax/Control/Defs.lean`. An exhaustive dependency
admits no partial reading, and a dependency inside the identity relation is exhaustive at every
valuation. A partial reading of a composite dependency whose second leg is exhaustive sits on its
first leg, the shape of a binding leg composed over predication. A saturating dependency admits
neither a partial reading nor a split. Finally, a dependency that shares occupants shares every
property of them, so one observed mismatch refutes it, the argument of the overt-copy
diagnostics of Polinsky and Potsdam.

## References

* [landau-2000]
* [bresnan-1982]
* [polinsky-potsdam-2006]
-/

@[expose] public section

namespace Control

open SetRel

/-! ### Exhaustive control -/

variable {Pos Ref : Type*} {val : Pos → Ref} {ante bind pred d : SetRel Pos Pos} {a b p : Pos}

/-- Related positions of an exhaustive dependency are co-valued. -/
theorem IsExhaustive.eq (hs : IsExhaustive val ante) (h : a ~[ante] b) : val a = val b :=
  hs h

theorem IsExhaustive.mono (hs : IsExhaustive val bind) (h : ante ⊆ bind) :
    IsExhaustive val ante :=
  h.trans hs

theorem isExhaustive_id : IsExhaustive val (.id : SetRel Pos Pos) :=
  fun _ h ↦ congrArg val h

theorem IsExhaustive.of_subset_id (h : d ⊆ .id) : IsExhaustive val d :=
  isExhaustive_id.mono h

theorem IsExhaustive.not_lt [Preorder Ref] (hs : IsExhaustive val ante) (h : a ~[ante] b) :
    ¬ val a < val b :=
  fun hlt ↦ hlt.ne (hs.eq h)

theorem IsExhaustive.not_isPartial [Preorder Ref] (h : IsExhaustive val d) : ¬ IsPartial val d :=
  fun ⟨_, _, hab, hlt⟩ ↦ h.not_lt hab hlt

theorem IsPartial.of_comp [Preorder Ref] (h : IsPartial val (bind ○ pred))
    (hp : IsExhaustive val pred) : IsPartial val bind :=
  let ⟨a, _, ⟨m, ham, hmc⟩, hlt⟩ := h
  ⟨a, m, ham, hp.eq hmc ▸ hlt⟩

/-! ### Saturation -/

theorem IsSaturating.not_isPartial [Preorder Ref] (h : IsSaturating val d) : ¬ IsPartial val d :=
  h.exhaustive.not_isPartial

theorem IsSaturating.eq_of_controllers (h : IsSaturating val d) (ha : a ~[d] p)
    (hb : b ~[d] p) : a = b :=
  h.biUnique.1 ha hb

theorem IsSaturating.not_isSplit (h : IsSaturating val d) : ¬ IsSplit d :=
  not_not_intro h.biUnique.1

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
    IsExhaustive (f ∘ occ) ante :=
  fun _ h ↦ congrArg f (hs h)

theorem IsExhaustive.iff_of_rel (hs : IsExhaustive occ ante) (h : a ~[ante] b) (P : Item → Prop) :
    P (occ a) ↔ P (occ b) :=
  iff_of_eq ((hs.map P).eq h)

theorem not_isExhaustive_of_mismatch {P : Item → Prop} (h : a ~[ante] b) (hPa : P (occ a))
    (hPb : ¬ P (occ b)) : ¬ IsExhaustive occ ante :=
  fun hs ↦ hPb ((hs.iff_of_rel h P).1 hPa)

end Control
