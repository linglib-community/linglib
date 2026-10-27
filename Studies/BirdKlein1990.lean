/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.IntervalOrder
public import Linglib.Phonology.Autosegmental.TwoTier
public import Linglib.Phonology.Tone.Basic

/-!
# Bird and Klein (1990): Phonological events

Bird and Klein read an autosegmental diagram in time: the left-to-right order of a tier is
precedence, and an association line is overlap. Their axioms (13) govern the two relations on
events: overlap is reflexive and symmetric, precedence is asymmetric and disjoint from overlap,
and an event preceding one member of an overlapping pair precedes every event following the
other. Intervals of points satisfy the axioms under the definitions (11), and the No-Crossing
Constraint is not stipulated but derived (Section 1.1): two crossing lines would make an event
precede an event it overlaps. A representation is consistent when an event structure on its
positions extends the order of its tiers and makes its lines overlaps (26).

## Main definitions

* `IsEventStructure prec ov`: the axioms (13).
* `IsEventStructureOf X prec ov`: an event structure on the positions of a representation,
  extending its tiers and associations.

## Implementation notes

The paper's event structures are the structures of precedence and overlap of the logic of time;
they are unrelated to the decompositions of `ArgumentStructure.EventStructure`. In modern terms,
a precedence satisfying (13) with overlap its incomparability is an interval order. The
endpoint definitions (12), which the paper considers and sets aside, state overlap strictly, so
under them a one-point interval does not overlap itself; the point-set definitions (11) read off
closed intervals are those of `NonemptyInterval`. The cycle of three tiers is a consequence of
the axioms that the paper does not discuss: they agree with the classical pairwise No-Crossing
Constraint when lines join only tiers adjacent in a forest, and are strictly stronger once lines
join three tiers in a cycle.

## References

* [bird-klein-1990]
* [sagey-1988]
* [fishburn-1970]
-/

@[expose] public section

namespace BirdKlein1990

open Autosegmental

/-! ### The axioms for events -/

section Axioms

variable {E : Type*}

/-- The axioms (13) on a precedence `prec` and an overlap `ov` between events. -/
structure IsEventStructure (prec ov : E → E → Prop) : Prop where
  /-- Overlap is reflexive (13a). -/
  ov_refl : ∀ x, ov x x
  /-- Overlap is symmetric (13b). -/
  ov_symm : ∀ ⦃x y⦄, ov x y → ov y x
  /-- Precedence is asymmetric (13c). -/
  prec_asymm : ∀ ⦃x y⦄, prec x y → ¬ prec y x
  /-- Precedence is disjoint from overlap (13d). -/
  not_ov_of_prec : ∀ ⦃x y⦄, prec x y → ¬ ov x y
  /-- An event preceding one member of an overlapping pair precedes every event following the
  other (13e). -/
  prec_of_prec_of_ov : ∀ ⦃w x y z⦄, prec w x → ov x y → prec y z → prec w z

variable {prec ov : E → E → Prop}

theorem IsEventStructure.prec_trans (h : IsEventStructure prec ov) {x y z : E}
    (hxy : prec x y) (hyz : prec y z) : prec x z :=
  h.prec_of_prec_of_ov hxy (h.ov_refl y) hyz

/-- The axioms of an event structure entail the No-Crossing Constraint (Section 1.1). -/
theorem IsEventStructure.not_crossing (h : IsEventStructure prec ov) {w x y z : E}
    (hwx : prec w x) (hyz : prec y z) (hwz : ov w z) (hxy : ov x y) : False :=
  h.not_ov_of_prec (h.prec_of_prec_of_ov hwx hxy hyz) hwz

/-- With overlap the incomparability, the axioms say exactly that precedence is an interval
order. -/
theorem isEventStructure_iff_isIntervalOrder :
    IsEventStructure prec (fun x y ↦ ¬ prec x y ∧ ¬ prec y x) ↔ IsIntervalOrder E prec := by
  constructor
  · intro h
    refine { irrefl x hx := h.prec_asymm hx hx, two_plus_two a b c d hab hcd := ?_ }
    by_cases hcb : prec c b
    · exact .inr hcb
    by_cases hbc : prec b c
    · exact .inl (h.prec_trans (h.prec_trans hab hbc) hcd)
    · exact .inl (h.prec_of_prec_of_ov hab ⟨hbc, hcb⟩ hcd)
  · intro h
    exact { ov_refl x := ⟨h.irrefl x, h.irrefl x⟩
            ov_symm _ _ hxy := hxy.symm
            prec_asymm _ _ hxy hyx := h.irrefl _ (h.toIsStrictOrder.trans _ _ _ hxy hyx)
            not_ov_of_prec _ _ hxy hov := hov.1 hxy
            prec_of_prec_of_ov _ _ _ _ hwx hxy hyz :=
              (h.two_plus_two hwx hyz).resolve_right hxy.2 }

end Axioms

/-! ### Intervals -/

section Intervals

variable {T : Type*} [LinearOrder T]

/-- Intervals form an event structure under the precedence and overlap of (11). -/
theorem isEventStructure_intervals :
    IsEventStructure (fun x y : NonemptyInterval T ↦ ∀ p ∈ x, ∀ q ∈ y, p < q)
      fun x y ↦ ∃ p, p ∈ x ∧ p ∈ y := by
  have hp : (fun x y : NonemptyInterval T ↦ ∀ p ∈ x, ∀ q ∈ y, p < q) =
      NonemptyInterval.Precedes := by
    ext x y
    exact NonemptyInterval.precedes_iff_forall_mem.symm
  have ho : (fun x y : NonemptyInterval T ↦ ∃ p, p ∈ x ∧ p ∈ y) = NonemptyInterval.Overlaps := by
    ext x y
    exact NonemptyInterval.overlaps_iff_exists_mem.symm
  have h := isEventStructure_iff_isIntervalOrder.2
    (NonemptyInterval.isIntervalOrder_precedes (α := T))
  rw [hp, ho]
  exact { ov_refl := NonemptyInterval.overlaps_refl
          ov_symm _ _ := NonemptyInterval.overlaps_symm
          prec_asymm := h.prec_asymm
          not_ov_of_prec _ _ := NonemptyInterval.Precedes.not_overlaps
          prec_of_prec_of_ov _ _ _ _ hwx hxy hyz := h.prec_of_prec_of_ov hwx
            (NonemptyInterval.overlaps_iff_not_precedes.1 hxy) hyz }

end Intervals

/-! ### Phonological event structures -/

section Representations

variable {ι : Type*} {τ : ι → Type*}

/-- An event structure on the positions of a representation (26): it satisfies the axioms,
extends the order of each tier, and makes each line an overlap. -/
structure IsEventStructureOf (X : AR τ) (prec ov : X.Pos → X.Pos → Prop) : Prop extends
    IsEventStructure prec ov where
  /-- The order of each tier is precedence. -/
  prec_of_lt : ∀ i ⦃p q : Fin (X.word i).length⦄, p < q → prec ⟨i, p⟩ ⟨i, q⟩
  /-- Each line is an overlap. -/
  ov_of_adj : ∀ ⦃v w⦄, X.assoc.Adj v w → ov v w

variable {X : AR τ} {prec ov : X.Pos → X.Pos → Prop}

/-- A representation with an event structure obeys the No-Crossing Constraint. -/
theorem IsEventStructureOf.noCrossing (h : IsEventStructureOf X prec ov) : X.NoCrossing :=
  fun i j ↦ AR.isNonCrossing_lines_iff.2 fun p q p' q' ⟨hp, hq, h₁⟩ ⟨hp', hq', h₂⟩ hlt ↦ by
    by_contra! hgt
    exact h.not_crossing (h.prec_of_lt i (show (⟨p, hp⟩ : Fin _) < ⟨p', hp'⟩ from hlt))
      (h.prec_of_lt j (show (⟨q', hq'⟩ : Fin _) < ⟨q, hq⟩ from hgt)) (h.ov_of_adj h₁)
      (h.ov_of_adj h₂)

theorem exists_isEventStructureOf_of_hasIntervalOrder (h : X.HasIntervalOrder) :
    ∃ prec ov, IsEventStructureOf X prec ov := by
  obtain ⟨r, hr, htier, hadj⟩ := h
  exact ⟨r, _, { toIsEventStructure := isEventStructure_iff_isIntervalOrder.2 hr
                 prec_of_lt := htier
                 ov_of_adj _ _ h := ⟨hadj h, hadj h.symm⟩ }⟩

end Representations

/-! ### Examples -/

open Tone Tone.TRN

/-- The tone-bearing units of (27). -/
inductive Syl
  | mo
  | ye
  | ka
  deriving DecidableEq

/-- Clements's `mo yɛ ka` (27): `mo` and `yɛ` overlap the first L, `ka` the H, and the final L
floats, with no precedence across the tiers (28). -/
abbrev clements : AR (TwoTier TRN Syl) :=
  AR.ofWords [L, H, L] [.mo, .ye, .ka] fun p q ↦ (p, q) ∈ [(0, 0), (0, 1), (1, 2)]

/-- (27) is consistent: it has an event structure. -/
theorem clements_consistent : ∃ prec ov, IsEventStructureOf clements prec ov :=
  exists_isEventStructureOf_of_hasIntervalOrder
    (AR.noCrossing_iff_hasIntervalOrder.1 (by decide))

/-- Three tiers, each tier's first position linked to the next tier's second around the cycle
of tiers. -/
abbrev cycle : AR fun _ : Fin 3 ↦ Unit :=
  AR.fromRel (fun _ ↦ [(), ()]) fun i j p q ↦ p = 0 ∧ q = 1 ∧ j = i + 1

theorem cycle_noCrossing : cycle.NoCrossing := by decide

/-- Yet the cycle has no event structure: the precedences chain through the overlaps from the
last tier's first position to the first tier's second, which it overlaps. -/
theorem not_isEventStructureOf_cycle (prec ov : cycle.Pos → cycle.Pos → Prop) :
    ¬ IsEventStructureOf cycle prec ov := by
  intro h
  have h₀ := h.prec_of_lt 0 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₁ := h.prec_of_lt 1 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₂ := h.prec_of_lt 2 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₂₀ := h.prec_of_prec_of_ov h₂ (h.ov_of_adj (by decide)) h₁
  exact h.not_ov_of_prec (h.prec_of_prec_of_ov h₂₀ (h.ov_of_adj (by decide)) h₀)
    (h.ov_of_adj (by decide))

/-- The cycle without the line from the last tier back to the first, so that the tiers form a
path. -/
abbrev path : AR fun _ : Fin 3 ↦ Unit :=
  AR.fromRel (fun _ ↦ [(), ()]) fun i j p q ↦ p = 0 ∧ q = 1 ∧ j = i + 1 ∧ i ≠ 2

/-- The path is consistent: its lines cross none pairwise and join only tiers adjacent in a
path, a forest. -/
example : ∃ prec ov, IsEventStructureOf path prec ov := by
  have hX : ∀ v w : path.Pos, path.assoc.Adj v w → (SimpleGraph.pathGraph 3).Adj v.1 w.1 := by
    decide
  exact exists_isEventStructureOf_of_hasIntervalOrder <|
    (AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic (SimpleGraph.isAcyclic_pathGraph 3)
      fun v w ↦ hX v w).1 (by decide)

end BirdKlein1990
