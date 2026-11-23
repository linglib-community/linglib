/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.OCP
public import Linglib.Phonology.FeatureGeometry.Linking
public import Linglib.Fragments.Laal.Prosody

/-!
# Lionnet (2022): The Features and Geometry of Tone in Laal

Lionnet analyses the three tone heights of Laal subtonally, as bundles of two register
features on a tonal root node, in the two-feature model of Yip and Pulleyblank and the geometry
of Snider. H is `[+upper, −raised]`, M is `[−upper, +raised]`, L is `[−upper, −raised]`, and
`[+upper, +raised]` is the system's gap (`featural_analysis`, `superHigh_is_the_gap`). The
analysis unifies the behaviour of the mid tone. It never shares a stem with another height
(`M_exclusive`); it lowers to L under a `[−raised]` neighbour, the only `[+raised]` tone being
the only target (`mLowering_from_L`, `H_stable`); and the ventive suffix, a floating
`[−raised]` taking `[upper]` from the root, surfaces as H after H and as L after M and L
(`ventive_after_M`). The tonal root node lets a feature act on its own tier apart from the
whole tone: the geometry is a feature geometry with one class node, and in its autosegmental
representation delinking the `[raised]` feature leaves the association of the tone to its mora
untouched (`partial_indep_of_full`).

## Implementation notes

The substrate `TRN` bundle carries the two register features, and `TRN.assimilate` and
`TRN.dock` are the `[−raised]` spreading and docking of the paper's derivations. The fusion
of adjacent identical `[−raised]` autosegments, which the paper mentions as an option it does
not adopt, is the `OCP.collapse` face of the tier-relative OCP. The full-tone spreading and
deletion processes of the paper's §6, its vowel harmony, and the alternative analyses of its
§7 are not represented.

## References

* [lionnet-2022]
* [yip-1980]
* [pulleyblank-1986]
* [snider-2020]
-/

@[expose] public section

namespace Lionnet2022

open Tone
open Laal.Prosody

/-! ### The subtonal featural analysis (§5.1) -/

/-- The featural analysis (ex. 51) as a map into the register-tier `TRN` encoding. -/
def toneToTRN : Tone → TRN
  | .H => TRN.H
  | .M => TRN.M
  | .L => TRN.L

/-- The substrate's `TRN.H`, `TRN.M`, `TRN.L` are the feature matrix of (51). -/
theorem featural_analysis :
    TRN.H = ⟨some true, some false⟩ ∧
    TRN.M = ⟨some false, some true⟩ ∧
    TRN.L = ⟨some false, some false⟩ := ⟨rfl, rfl, rfl⟩

/-- Paradigmatic pitch (§5.1) counts `[upper]` as two and `[raised]` as one, independently per
node, with no register state. -/
def absolutePitch (t : TRN) : Int :=
  (if t.upper = some true then 2 else 0) + if t.raised = some true then 1 else 0

theorem absolutePitch_ordered :
    absolutePitch TRN.L = 0 ∧ absolutePitch TRN.M = 1 ∧ absolutePitch TRN.H = 2 ∧
      absolutePitch TRN.superHigh = 3 := by
  decide

/-! ### M-exclusivity: `*MX/XM` (§3, §5.4) -/

theorem M_exclusive :
    ∀ m ∈ attestedMelodies, Tone.M ∈ m → ∀ t ∈ m, t = Tone.M := by decide

/-! ### M-lowering as `[−raised]` assimilation (§5.2) -/

theorem mLowering_from_L : TRN.assimilate .raised TRN.L TRN.M = TRN.L := by decide

theorem mLowering_from_H : TRN.assimilate .raised TRN.H TRN.M = TRN.L := by decide

theorem H_stable : TRN.assimilate .raised TRN.L TRN.H = TRN.H := by decide

theorem L_stable : TRN.assimilate .raised TRN.H TRN.L = TRN.L := by decide

/-! ### The ventive suffix (§5.5) -/

theorem ventive_after_H : TRN.dock .raised false TRN.H = TRN.H := by decide
theorem ventive_after_M : TRN.dock .raised false TRN.M = TRN.L := by decide
theorem ventive_after_L : TRN.dock .raised false TRN.L = TRN.L := by decide

/-! ### The `[+upper, +raised]` gap (§5.6) -/

/-- The Laal tone inventory, as TRNs. -/
def laalToneInventory : List TRN := ([Tone.H, Tone.M, Tone.L]).map toneToTRN

/-- The fourth feature combination `[+upper, +raised]` (`TRN.superHigh`) is absent, the
systematic gap that makes Laal a Table-4 type-A system (§5.6). -/
theorem superHigh_is_the_gap : TRN.superHigh ∉ laalToneInventory := by decide

/-! ### The optional OCP-`[raised]` merger (§5.2, ex. 53–55, 58) -/

theorem ocp_raised_merge_LL :
    OCP.collapse [TRN.L, TRN.L] = [TRN.L] := by decide

theorem ocp_raised_is_tier_relative :
    ¬ OCP.IsCleanOn (fun _ : TRN ↦ True) (·.raised) [TRN.H, TRN.L] ∧
      OCP.IsClean [TRN.H, TRN.L] := by decide

theorem ocp_raised_merge_clean (tier : List TRN) :
    OCP.IsClean (OCP.collapse (tier.map (·.raised))) :=
  OCP.isClean_collapse _

/-! ### The register-tier geometry (§5–§6)

The geometry of (52) is a hub and spokes around the tonal root node, from which `[±upper]` and
`[±raised]` hang and which associates to its mora. It is a feature geometry with one class node,
so a tone is realized by `ofSpec` with a tier for each subtonal feature, and a feature can be
delinked apart from the whole node, the paper's partial activity, which the bundled `TRN` record
cannot express. -/

open Autosegmental Phonology.FeatureGeometry

/-- The tonal root node, the one class node of the geometry (52). -/
inductive ToneNode where
  | root
  deriving DecidableEq, Fintype

/-- The tree of one node. -/
def ToneNode.tree : ParentTree ToneNode := .ofIterate id .root 0 fun | .root => rfl

instance : PartialOrder ToneNode := ToneNode.tree.toPartialOrder

instance : DecidableLE ToneNode := ToneNode.tree.decidableLE

instance : OrderBot ToneNode := ToneNode.tree.toOrderBot

instance : PredOrder ToneNode := ToneNode.tree.toPredOrder

/-- (52): both subtonal features hang from the tonal root node. -/
def toneNode : Subtonal → Option ToneNode := fun _ ↦ some .root

/-- An M tone on its mora, with its tonal root node and its two features. -/
def mForm : AR (Tiers ToneNode Subtonal Bool) := ofSpec toneNode TRN.M.toBundle

theorem mForm_noCrossing : mForm.NoCrossing := noCrossing_ofSpec _ _

/-- The M form with the subtonal `[+raised]` feature delinked from the tonal root node. -/
def delinkRaised : AR (Tiers ToneNode Subtonal Bool) :=
  mForm.eraseLine (some (.inl .root)) (some (.inr .raised)) 0 0

/-- Delinking a subtonal feature leaves the line from the tonal root node to its mora
untouched, so partial activity is independent of full activity. -/
theorem partial_indep_of_full (p q : ℕ) :
    delinkRaised.Link (some (.inl .root)) none p q ↔ mForm.Link (some (.inl .root)) none p q := by
  simp [delinkRaised, AR.link_eraseLine]

theorem delinkRaised_erases (p q : ℕ) :
    ¬ delinkRaised.Link (some (.inr .raised)) (some (.inl .root)) p q := by
  rw [delinkRaised, AR.link_eraseLine]
  rintro ⟨h, -, h₂⟩
  have hp : p < (tierWord (β := Bool) toneNode TRN.M.toBundle (some (.inr .raised))).length :=
    h.lt_left
  have hq : q < (tierWord (β := Bool) toneNode TRN.M.toBundle (some (.inl .root))).length :=
    h.lt_right
  have := length_tierWord_le_one (β := Bool) toneNode TRN.M.toBundle (some (.inr .raised))
  have := length_tierWord_le_one (β := Bool) toneNode TRN.M.toBundle (some (.inl .root))
  exact h₂ ⟨rfl, rfl, by omega, by omega⟩

-- After delinking, the mora no longer reads `[+raised]` and still reads `[−upper]`.
theorem reads_delinkRaised :
    ¬ delinkRaised.Reads (tiers toneNode) 0 (some (.inr .raised)) true ∧
      delinkRaised.Reads (tiers toneNode) 0 (some (.inr .upper)) false := by
  decide

end Lionnet2022
