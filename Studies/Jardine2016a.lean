/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ElgotMezei
public import Linglib.Data.Wordlist.Jardine2016a
public import Linglib.Phonology.Tone.Plateauing

/-!
# Jardine (2016): Computationally, tone is different

Jardine argues that unbounded circumambient processes, whose application depends on material
unboundedly far away on both sides of the target, (2), are common in tonal phonology and rare in
segmental phonology. His witness is unbounded tonal plateauing, every TBU between two H-toned
TBUs surfacing H (Hyman and Katamba's rule, (7)), as the string map (36) of Section 4.1, which is
`Tone.utp`. The map is subsequential in neither direction (Section 4.2) but regular: the mark-up
decomposition (43), a left-to-right pass writing `?` after an H and a right-to-left pass
resolving it, is computed by a bimachine. Read back into autosegmental representations by (40),
the OCP-merged output is one H linked to the plateau (Section 4.4).

## Implementation notes

* The conjecture of Section 5.2, after Heinz and Lai, that plateauing has no mark-up-free
  decomposition and so is not weakly deterministic, is not stated.
* The words of `Data/Wordlist/Jardine2016a.json` carry the paper's string representation one symbol
  per mora, a long vowel counting two; the Digo, Xhosa and Yaka data, whose plateaus interact
  with tone shift or an accentual analysis, are not encoded.

## References

* [jardine-2016a]
* [hyman-katamba-2010]
* [heinz-lai-2013]
* [elgot-mezei-1965]
-/

@[expose] public section

namespace Jardine2016a

open Tone

/-! ### The plateauing data

The words of Section 2.2 carry their underlying and surface TBU strings in the paper's string
representation of Section 4.1, one symbol per mora, `H` a TBU associated to a H tone and Ø,
written `O`, an unspecified one, read off the paper's autosegmental diagrams. -/

/-- `tbuString s` is the TBU string spelled `s` in `H` and `O`. -/
def tbuString (s : String) : List AssociationState :=
  s.toList.map fun c ↦ if c = 'H' then .H else .O

/-- `ofAnalysis a` is the underlying and the surface TBU string of the word `a` analyses. -/
def ofAnalysis (a : Wordlist.Analysis) : List AssociationState × List AssociationState :=
  (tbuString a.underlyingTones, tbuString a.surfaceTones)

/-- The map (36) reproduces every plateau of Section 2.2, Luganda (8) to (12), Zulu (18b) and
Saramaccan (21). -/
theorem utp_map_forms : ∀ a ∈ Wordlist.analyses, utp.map (ofAnalysis a).1 = (ofAnalysis a).2 := by
  decide

variable {w : List AssociationState} {j k : ℕ}

/-! ### UTP is not subsequential

Whether a toneless TBU surfaces H depends on a H arbitrarily far away on each side of it, and
the map preserves length, so a machine reading in either direction would have to withhold
unboundedly many symbols. -/

/-- UTP is subsequential in neither direction (§4.2, online appendix). -/
theorem utp_not_isSubsequential : ∀ d, ¬ IsSubsequential d utp.map :=
  utp.twoSidedUnboundedDependence.not_isSubsequential fun _ ↦ utp.map_length

/-! ### The (43) mark-up decomposition

With one extra symbol the two-pass decomposition exists: a left pass marks every toneless
TBU after a H with `?`; a right pass resolves `?` by whether a H follows. The mark is
exactly the alphabet enlargement that Heinz and Lai's weak determinism disallows. -/

/-- The mark-up alphabet of (43) adds `Q`, the paper's `?`. -/
inductive Mark | H | O | Q
  deriving DecidableEq, Repr

/-- The left pass of (43) marks every toneless TBU after a H with `?`. -/
def markLeft : Mealy Bool AssociationState Mark :=
  .ofFlag (· == .H) fun l a => match a with | .H => .H | .O => if l then .Q else .O

/-- The right pass of (43), run right-to-left, resolves `?` to H when a H follows, else to Ø. -/
def resolveRight : Mealy Bool Mark AssociationState :=
  .ofFlag (· == .H) fun r a =>
    match a with | .H => .H | .O => .O | .Q => if r then .H else .O

theorem markLeft_run_getElem?_H_iff :
    (markLeft.run w)[j]? = some Mark.H ↔ w[j]? = some AssociationState.H := by
  rw [markLeft, Mealy.getElem?_ofFlag_run]
  cases hv : w[j]? with
  | none => simp
  | some a => cases a <;> simp [ite_eq_iff]

/-- UTP is the left-to-right marking pass followed by the right-to-left resolving pass of (43). -/
theorem utp_eq_resolve_mark (w : List AssociationState) :
    utp.map w = resolveRight.runRight (markLeft.run w) := by
  have hmark (i : ℕ) :
      Mark.H ∈ (markLeft.run w).drop (i + 1) ↔ AssociationState.H ∈ w.drop (i + 1) := by
    simp only [List.mem_iff_getElem?, List.getElem?_drop, markLeft_run_getElem?_H_iff]
  refine List.ext_getElem? fun i => ?_
  rw [utp.map_getElem?, resolveRight, Mealy.getElem?_ofFlag_runRight]
  simp only [List.any_beq', List.contains_eq_mem, decide_eq_decide.mpr (hmark i)]
  rw [markLeft, Mealy.getElem?_ofFlag_run, Option.map_map]
  simp only [List.any_beq', List.contains_eq_mem]
  cases ha : w[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Function.comp_apply]
    congr 1
    cases a with
    | H => simp [utp.surfaces_of_hi ha]
    | O =>
      by_cases hL : AssociationState.H ∈ w.take i <;>
        by_cases hR : AssociationState.H ∈ w.drop (i + 1) <;>
        simp [utp.surfaces_split ha, hL, hR]

/-- UTP is computable by a bimachine via the (43) decomposition, hence regular (§4.2). -/
theorem utp_isBimachineComputable : IsBimachineComputable utp.map := by
  rw [show utp.map = resolveRight.runRight ∘ markLeft.run from funext utp_eq_resolve_mark]
  exact resolveRight.isRightSubsequential.isBimachineComputable_comp
    markLeft.isLeftSubsequential rfl

/-! ### The autosegmental reading (§4.4)

The string representation reads back into autosegmental representations by `AssociationState.toAR`
((40)); the OCP-merged representation of the output has one `H`, linked exactly to the
plateau, Hyman and Katamba's rule as given in (7). -/

open Autosegmental in
theorem link_collapse_prod_map_toAR_map :
    (((utp.map w).map AssociationState.toAR).prod.collapse true).Link true false k j ↔
      k = 0 ∧ utp.Surfaces w j := by
  rw [AssociationState.link_collapse_prod_map_toAR, utp.map_getElem?_H_iff]

/-- `HØØH` fuses to one H linked to all four TBUs. -/
example : ∀ j < 4,
    (((utp.map [.H, .O, .O, .H]).map AssociationState.toAR).prod.collapse true).Link true false
      0 j := by
  simp only [link_collapse_prod_map_toAR_map, true_and]
  decide

end Jardine2016a
