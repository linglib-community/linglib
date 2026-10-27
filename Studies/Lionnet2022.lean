/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.Basic
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
whole tone: on the multi-tier autosegmental foundation, delinking the `[raised]` feature
leaves the association of the tone to its mora untouched (`partial_indep_of_full`).

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

/-! ### The register-tier geometry on the multi-tier substrate (§5–§6)

The geometry of (52) is a hub and spokes around the tonal root node: the `[±upper]` tier,
the `[±raised]` tier, and the mora tier each associate to it. On the multi-tier substrate this
is a four-tier representation, on which a subtonal feature is a tier of its own and so can be
manipulated apart from the whole node, the paper's partial activity, which the bundled
`TRN` record cannot express; whole-node operations act on the node-to-mora layer. -/

open Autosegmental

/-- The four Laal tone tiers are the `[±upper]` register, `[±raised]`, the TRN, and the
mora. -/
abbrev laalTier : Fin 4 → Type := ![Option Bool, Option Bool, Unit, Unit]

/-- The tier words of a one-node M-toned form. -/
def laalWords : ∀ i : Fin 4, List (laalTier i) :=
  Fin.cons [some false] (Fin.cons [some true] (Fin.cons [()] (Fin.cons [()] finZeroElim)))

/-- In the hub-and-spoke links (ex. 52) register, `[raised]`, and mora each associate to the
TRN. -/
def laalSpokes (i j : Fin 4) (p q : ℕ) : Prop :=
  ((i, j) = (0, 2) ∨ (i, j) = (1, 2) ∨ (i, j) = (2, 3)) ∧ p = 0 ∧ q = 0

instance (i j : Fin 4) (p q : ℕ) : Decidable (laalSpokes i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The M-toned form on the multi-tier substrate. -/
def mForm : AR laalTier := AR.fromRel laalWords laalSpokes

theorem mForm_noCrossing : mForm.NoCrossing := by decide

/-- Delinking a feature acts on one tier-pair layer alone (**partial activity**, §5), here
`[raised]`↔TRN, the pair `(1, 2)`. -/
def delink (L : Fin 4 → Fin 4 → ℕ → ℕ → Prop) (i₀ j₀ : Fin 4)
    (i j : Fin 4) (p q : ℕ) : Prop :=
  ¬ (i = i₀ ∧ j = j₀) ∧ L i j p q

instance (L : Fin 4 → Fin 4 → ℕ → ℕ → Prop) [∀ i j p q, Decidable (L i j p q)]
    (i₀ j₀ i j : Fin 4) (p q : ℕ) : Decidable (delink L i₀ j₀ i j p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The M form with the subtonal `[−raised]` feature delinked. -/
def delinkRaised : AR laalTier := AR.fromRel laalWords (delink laalSpokes 1 2)

/-- Delinking the subtonal `[−raised]` feature leaves the node-to-mora layer, the tier pair
`(2, 3)`, untouched, so partial activity is independent of full activity. -/
theorem partial_indep_of_full (p q : ℕ) :
    delinkRaised.Link 2 3 p q ↔ mForm.Link 2 3 p q := by
  simp [delinkRaised, mForm, delink, laalSpokes]

theorem delinkRaised_erases (p q : ℕ) : ¬ delinkRaised.Link 1 2 p q := by
  rw [delinkRaised, AR.link_fromRel]
  rintro ⟨-, -, -, ⟨hne, -⟩ | ⟨-, h2, -⟩⟩
  · exact hne ⟨rfl, rfl⟩
  · rcases h2 with h2 | h2 | h2 <;> simp_all

end Lionnet2022
