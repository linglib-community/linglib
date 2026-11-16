/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Logic.Relator
public import Mathlib.Order.Bounds.Basic

/-!
# Control dependencies

A control dependency is a relation `SetRel Pos Pos` on argument positions, read
`antecedent ~[d] dependent`, with a valuation `val : Pos → Ref` assigning referents. This is
Stiebels's definition of control as referential inclusion, "open as to how the control reading
is obtained": each controller's referent is part of the dependent's (`IsInclusive`). The reading
types are Landau's and compare the dependent's referent with those of all its controllers
together, the set `val '' d.preimage {b}`: a reading is partial when the dependent strictly exceeds
some bound of them, and [under inclusion it is not partial](##Control.IsInclusive.not_isPartial_iff)
exactly when the dependent is their least upper bound. A split dependency, one with two
controllers of a dependent, can therefore be read either way.

`IsExhaustive` is the stronger, pairwise condition that related positions are co-valued, which
[agrees with the least upper bound](##Control.isExhaustive_iff_isLUB) when each dependent has one
controller. It is the hypothesis under which a valuation
[descends to the quotient](##Control.IsExhaustive.lift) by the dependency, and what a dependency
shares is a choice of valuation: functional control, in Bresnan's sense, shares the occupant of
each position, anaphoric control only its referent. A shared occupant transports along every map
of it, so one observed mismatch [refutes](##Control.not_isExhaustive_of_mismatch) occupant
sharing, the argument of the overt-copy diagnostics of Polinsky and Potsdam. `IsSaturating` is
the bi-unique, exhaustive profile of saturation (predication, structure sharing).

## Implementation notes

Grammatical dependencies share Koster's configurational-matrix format, as Neeleman and van de
Koot state it, and its clauses are mathlib vocabulary and are not named here: refinement
`r ⊆ s`, `Relator.LeftUnique` and `dependent ⊆ r.cod`. Control shift varies the antecedent across
readings of one construction, so it is not a property of a single dependency.

## References

* [stiebels-2007]
* [landau-2000]
* [bresnan-1982]
* [koster-1987]
* [neeleman-vandekoot-2002]
* [polinsky-potsdam-2006]
-/

@[expose] public section

namespace Control

open SetRel

variable {Pos Ref Item : Type*} {val : Pos → Ref} {occ : Pos → Item}
  {ante bind pred d : SetRel Pos Pos} {a b p : Pos}

/-! ### Exhaustive sharing -/

/-- A dependency is exhaustive ([landau-2000]) when it relates only co-valued positions, that is,
when it refines the kernel of the valuation. -/
def IsExhaustive (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ante ⊆ {(a, b) | val a = val b}

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

/-- An exhaustively shared valuation descends to the quotient by the dependency, the value of a
chain of related positions. -/
def IsExhaustive.lift (hs : IsExhaustive val d) : Quot (· ~[d] ·) → Ref :=
  Quot.lift val fun _ _ h ↦ hs h

@[simp] theorem IsExhaustive.lift_mk (hs : IsExhaustive val d) (a : Pos) :
    hs.lift (Quot.mk _ a) = val a :=
  rfl

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

/-! ### Referential inclusion and partial readings -/

section Preorder
variable [Preorder Ref]

/-- A dependency is referentially inclusive ([stiebels-2007]) when each controller's referent is
part of its dependent's. -/
def IsInclusive (val : Pos → Ref) (d : SetRel Pos Pos) : Prop :=
  d ⊆ {(a, b) | val a ≤ val b}

/-- A dependency has a partial reading ([landau-2000]) when some dependent's referent strictly
exceeds a bound of its controllers' referents. -/
def IsPartial (val : Pos → Ref) (d : SetRel Pos Pos) : Prop :=
  ∃ b ∈ d.cod, ∃ u ∈ upperBounds (val '' d.preimage {b}), u < val b

theorem IsInclusive.le (h : IsInclusive val d) (hab : a ~[d] b) : val a ≤ val b :=
  h hab

theorem isInclusive_iff :
    IsInclusive val d ↔ ∀ b, val b ∈ upperBounds (val '' d.preimage {b}) :=
  ⟨by rintro h b _ ⟨a, ⟨_, rfl, hab⟩, rfl⟩; exact h hab,
    fun h ⟨a, b⟩ hab ↦ h b ⟨a, ⟨b, rfl, hab⟩, rfl⟩⟩

theorem IsExhaustive.isInclusive (hs : IsExhaustive val d) : IsInclusive val d :=
  fun _ h ↦ (hs h).le

/-- A partial reading puts some controller's referent strictly below its dependent's. With two
controllers the converse fails, each being a proper part of their sum. -/
theorem IsPartial.exists_lt (h : IsPartial val d) : ∃ a b, a ~[d] b ∧ val a < val b :=
  let ⟨b, ⟨a, hab⟩, _, hu, hlt⟩ := h
  ⟨a, b, hab, (hu ⟨a, ⟨b, rfl, hab⟩, rfl⟩).trans_lt hlt⟩

theorem isPartial_iff_of_leftUnique (hd : Relator.LeftUnique (· ~[d] ·)) :
    IsPartial val d ↔ ∃ a b, a ~[d] b ∧ val a < val b := by
  refine ⟨IsPartial.exists_lt, fun ⟨a, b, hab, hlt⟩ ↦ ⟨b, ⟨a, hab⟩, val a, ?_, hlt⟩⟩
  rintro _ ⟨a', ⟨_, rfl, ha'⟩, rfl⟩
  exact (congrArg val (hd ha' hab)).le

theorem IsExhaustive.not_lt (hs : IsExhaustive val ante) (h : a ~[ante] b) : ¬ val a < val b :=
  fun hlt ↦ hlt.ne (hs.eq h)

theorem IsExhaustive.not_isPartial (h : IsExhaustive val d) : ¬ IsPartial val d :=
  fun hp ↦ let ⟨_, _, hab, hlt⟩ := hp.exists_lt; h.not_lt hab hlt

/-- A partial reading of a composite dependency whose second leg is exhaustive sits on its first
leg, the shape of a binding leg composed over predication. -/
theorem IsPartial.of_comp (h : IsPartial val (bind ○ pred)) (hp : IsExhaustive val pred) :
    IsPartial val bind := by
  obtain ⟨c, ⟨a, hac⟩, u, hu, hlt⟩ := h
  obtain ⟨m, ham, hmc⟩ : ∃ m, a ~[bind] m ∧ m ~[pred] c := hac
  refine ⟨m, ⟨a, ham⟩, u, ?_, hp.eq hmc ▸ hlt⟩
  rintro _ ⟨a', ⟨m', hm', ha'⟩, rfl⟩
  exact hu ⟨a', ⟨c, rfl, m, (show m' = m from hm') ▸ ha', hmc⟩, rfl⟩

end Preorder

/-- With one controller per dependent, a dependency is exhaustive exactly when each dependent's
referent is the least upper bound of its controllers'. -/
theorem isExhaustive_iff_isLUB [PartialOrder Ref] (hd : Relator.LeftUnique (· ~[d] ·)) :
    IsExhaustive val d ↔ ∀ b ∈ d.cod, IsLUB (val '' d.preimage {b}) (val b) := by
  have hs {a b} (hab : a ~[d] b) : val '' d.preimage {b} = {val a} :=
    Set.ext fun x ↦ ⟨by rintro ⟨a', ⟨_, rfl, ha'⟩, rfl⟩; exact congrArg val (hd ha' hab),
      by rintro rfl; exact ⟨a, ⟨b, rfl, hab⟩, rfl⟩⟩
  refine ⟨fun h b ⟨a, hab⟩ ↦ ?_, fun h ⟨a, b⟩ hab ↦ ?_⟩
  · rw [hs hab, ← h.eq hab]
    exact isLUB_singleton
  · have := h b ⟨a, hab⟩
    rw [hs hab] at this
    exact isLUB_singleton.unique this

/-- Under referential inclusion a dependency has no partial reading exactly when each dependent's
referent is the least upper bound of its controllers', whether one or several. -/
theorem IsInclusive.not_isPartial_iff [SemilatticeInf Ref] (h : IsInclusive val d) :
    ¬ IsPartial val d ↔ ∀ b ∈ d.cod, IsLUB (val '' d.preimage {b}) (val b) := by
  refine ⟨fun hp b hb ↦ ⟨isInclusive_iff.1 h b, fun u hu ↦ ?_⟩, fun hl ⟨b, hb, u, hu, hlt⟩ ↦
    ((hl b hb).2 hu).not_gt hlt⟩
  by_contra hle
  exact hp ⟨b, hb, u ⊓ val b, fun _ hx ↦ le_inf (hu hx) (isInclusive_iff.1 h b hx),
    lt_of_le_not_ge inf_le_right fun h' ↦ hle (h'.trans inf_le_left)⟩

/-! ### Split control and saturation -/

/-- A dependency is split when some dependent has two distinct controllers, that is, when it is
not left-unique. -/
abbrev IsSplit (d : SetRel Pos Pos) : Prop :=
  ¬ Relator.LeftUnique (· ~[d] ·)

/-- A dependency is saturating, as predication and structure sharing are, when each dependent has a
unique controller, each controller saturates a single slot, and the referent is shared
exhaustively. -/
structure IsSaturating (val : Pos → Ref) (d : SetRel Pos Pos) : Prop where
  /-- Each dependent has one controller and each controller one dependent. -/
  biUnique : Relator.BiUnique (· ~[d] ·)
  /-- Related positions are co-valued. -/
  exhaustive : IsExhaustive val d

theorem IsSaturating.not_isPartial [Preorder Ref] (h : IsSaturating val d) : ¬ IsPartial val d :=
  h.exhaustive.not_isPartial

theorem IsSaturating.eq_of_controllers (h : IsSaturating val d) (ha : a ~[d] p)
    (hb : b ~[d] p) : a = b :=
  h.biUnique.1 ha hb

theorem IsSaturating.not_isSplit (h : IsSaturating val d) : ¬ IsSplit d :=
  not_not_intro h.biUnique.1

end Control
