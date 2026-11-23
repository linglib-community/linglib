/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.TierTree
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
whole tone. `toAR` puts a tone on its mora with the tonal root node and each feature on a tier
of its own; there M-lowering is the spreading of `[−raised]` on its tier
(`mLowering_spreadTier`), and delinking the `[raised]` feature leaves the association of the
tone to its mora untouched (`partial_indep_of_full`).

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

/-! ### The geometry of tone (§5–§6)

The geometry of (52) is a hub and spokes around the tonal root node: the root node associates to
its mora, and `[±upper]` and `[±raised]` hang from it, each on a tier of its own. A feature can
then be spread or delinked apart from the whole tone, the paper's partial activity, which the
bundled `TRN` record cannot express. -/

open Autosegmental

/-- The tiers of (52): the mora, the tonal root node, and the two register features. -/
inductive ToneTier where
  | mora
  | root
  | upper
  | raised
  deriving DecidableEq, Fintype

/-- A mora and a tonal root node carry no label, and a feature carries its value. -/
abbrev ToneTier.Label : ToneTier → Type
  | .upper | .raised => Bool
  | _ => Unit

instance : ∀ i, DecidableEq (ToneTier.Label i)
  | .mora => inferInstanceAs (DecidableEq Unit)
  | .root => inferInstanceAs (DecidableEq Unit)
  | .upper => inferInstanceAs (DecidableEq Bool)
  | .raised => inferInstanceAs (DecidableEq Bool)

/-- (52): the tonal root node hangs from its mora, and each register feature from the tonal
root node. -/
def toneTiers : ParentTree ToneTier :=
  .ofIterate (fun | .mora | .root => .mora | .upper | .raised => .root) .mora 2 (by decide)

/-- The tokens of a tone on each tier: a mora, a tonal root node, and each feature the tone
specifies. -/
def toneWord (t : TRN) : ∀ i, List (ToneTier.Label i)
  | .mora => [()]
  | .root => [()]
  | .upper => t.upper.toList
  | .raised => t.raised.toList

/-- (52): a tone on its mora, the tonal root node linked to the mora and to each feature the
tone specifies. -/
def toAR (t : TRN) : AR ToneTier.Label :=
  AR.fromRel (toneWord t) fun i j _ _ ↦ toneTiers.parent j = i ∧ j ≠ .mora

/-- A word of tones, each on its mora, as a monoid homomorphism. -/
def toARHom : FreeMonoid TRN →* AR ToneTier.Label := FreeMonoid.lift toAR

theorem reads_toAR_upper (t : TRN) (b : Bool) :
    (toAR t).Reads toneTiers 0 .upper b ↔ t.upper = some b := by
  obtain ⟨u, r⟩ := t
  rcases u with _ | _ | _ <;> rcases r with _ | _ | _ <;> cases b <;> decide

theorem reads_toAR_raised (t : TRN) (b : Bool) :
    (toAR t).Reads toneTiers 0 .raised b ↔ t.raised = some b := by
  obtain ⟨u, r⟩ := t
  rcases u with _ | _ | _ <;> rcases r with _ | _ | _ <;> cases b <;> decide

/-- A word of tones reads at each mora the `[raised]` value of its tone. -/
theorem reads_prod_map_toAR_raised {w : List TRN} {k : ℕ} {b : Bool} :
    (w.map toAR).prod.Reads toneTiers k .raised b ↔ ∃ hk : k < w.length, w[k].raised = some b :=
  (AR.reads_prod_map toneTiers toAR fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ reads_toAR_raised _ _)

-- (§5.2) M-lowering as the spreading of `[−raised]` on its own tier: the M after an L comes to
-- share the L's `[−raised]` and keeps its own `[−upper]`, which is L.
theorem mLowering_spreadTier :
    (AR.spreadTier toneTiers toAR [TRN.L, TRN.M] .raised 0 1).Reads toneTiers 1 .raised false ∧
      ¬ (AR.spreadTier toneTiers toAR [TRN.L, TRN.M] .raised 0 1).Reads toneTiers 1 .raised true ∧
      (AR.spreadTier toneTiers toAR [TRN.L, TRN.M] .raised 0 1).Reads toneTiers 1 .upper false ∧
      (AR.spreadTier toneTiers toAR [TRN.L, TRN.M] .raised 0 1).NoCrossing := by
  decide

/-- An M tone on its mora. -/
def mForm : AR ToneTier.Label := toAR TRN.M

theorem mForm_noCrossing : mForm.NoCrossing := by decide

/-- The M form with its `[+raised]` feature delinked from the tonal root node. -/
def delinkRaised : AR ToneTier.Label := mForm.eraseLine .root .raised 0 0

/-- Delinking a subtonal feature leaves the line from the tonal root node to its mora
untouched, so partial activity is independent of full activity. -/
theorem partial_indep_of_full (p q : ℕ) :
    delinkRaised.Link .root .mora p q ↔ mForm.Link .root .mora p q := by
  simp [delinkRaised, AR.link_eraseLine]

theorem delinkRaised_erases (p q : ℕ) : ¬ delinkRaised.Link .raised .root p q := by
  rw [delinkRaised, AR.link_eraseLine]
  rintro ⟨h, -, h₂⟩
  have hp : p < 1 := h.lt_left
  have hq : q < 1 := h.lt_right
  exact h₂ ⟨rfl, rfl, by omega, by omega⟩

-- After delinking, the mora no longer reads `[+raised]` and still reads `[−upper]`.
theorem reads_delinkRaised :
    ¬ delinkRaised.Reads toneTiers 0 .raised true ∧
      delinkRaised.Reads toneTiers 0 .upper false := by
  decide

end Lionnet2022
