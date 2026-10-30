/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.PNat.Defs

/-!
# Register features and terracing

In Register Tier Theory a *register feature* shifts the register relative to the preceding
register setting, `h` one step up and `l` one step down; the shift is syntagmatic, unlike the
paradigmatic `[±upper]` of a tonal root node. A *register tier* gives each register-bearing unit
the features it bears, and it is realized by *terracing*, the running sums of the shifts from a
baseline, which [realize piecewise](##Tone.terrace_append) and are
[pointwise monotone in the shifts and the baseline](##Tone.terrace_mono). A *registered word* is a
syllable sequence with a register tier over its morae, split by syllable along the
`Composition` of its mora counts.

## Main definitions

* `terrace` — the levels reached from a baseline by cumulative shifts (`List.scanl`).
* `RegisterFeature`, `RegisterFeature.shift`, `RegisterFeature.totalShift` — the register
  features and the shifts they effect.
* `RegisterTier`, `RegisterTier.realize`, `RegisterTier.bearing` — the features on each
  register-bearing unit, the level each unit reaches, and the units bearing a feature.
* `Registered` — syllables with a register tier over their morae; `composition`,
  `syllableFeatures`, `IsAligned`, `append`, `concat`.

## References

* [snider-1999]
* [lionnet-2025]
-/

@[expose] public section

namespace Tone

/-! ### Terracing -/

/-- **Terracing**: the register levels reached from a baseline by a sequence of shifts,
each cumulative — the running sums of the shifts. -/
def terrace (level : ℤ) (shifts : List ℤ) : List ℤ :=
  (shifts.scanl (· + ·) level).tail

@[simp] theorem terrace_nil (level : ℤ) : terrace level [] = [] := by
  simp [terrace]

@[simp] theorem terrace_cons (level d : ℤ) (rest : List ℤ) :
    terrace level (d :: rest) = (level + d) :: terrace (level + d) rest := by
  cases rest <;> simp [terrace, List.scanl_cons, List.scanl_nil]

@[simp] theorem length_terrace (level : ℤ) (shifts : List ℤ) :
    (terrace level shifts).length = shifts.length := by
  simp [terrace]

/-- A sequence realizes piecewise: the second part continues from the register the first
part leaves. -/
theorem terrace_append (level : ℤ) (ds es : List ℤ) :
    terrace level (ds ++ es) = terrace level ds ++ terrace (level + ds.sum) es := by
  induction ds generalizing level with
  | nil => simp
  | cons d ds ih => simp only [List.cons_append, terrace_cons, ih, List.sum_cons, add_assoc]

/-- **Monotonicity**: pointwise lower shifts and a lower baseline give pointwise lower
levels. -/
theorem terrace_mono {ds es : List ℤ} (h : List.Forall₂ (· ≤ ·) ds es) {n m : ℤ}
    (hnm : n ≤ m) : List.Forall₂ (· ≤ ·) (terrace n ds) (terrace m es) := by
  induction h generalizing n m with
  | nil => simp only [terrace_nil]; exact .nil
  | cons hhead _ ih =>
    have hstep := add_le_add hnm hhead
    simp only [terrace_cons]
    exact .cons hstep (ih hstep)

/-! ### Register features -/

/-- A **register feature** of Register Tier Theory ([snider-1999] p. 25): `h` effects a
register shift higher and `l` a shift lower, relative to the preceding register setting, so `h`
is an upstep and `l` a downstep. The shift is syntagmatic, unlike the paradigmatic `[±upper]` of
a `TRN`, which places a tone in the upper or lower half of the current register. -/
inductive RegisterFeature where
  /-- A register shift higher, an upstep. -/
  | h
  /-- A register shift lower, a downstep. -/
  | l
  deriving DecidableEq, Repr

namespace RegisterFeature

/-- The register shift a feature effects: `h` one step up, `l` one step down. -/
def shift : RegisterFeature → ℤ
  | .h => 1
  | .l => -1

@[simp] theorem shift_h : h.shift = 1 := rfl

@[simp] theorem shift_l : l.shift = -1 := rfl

/-- The shift a sequence of features effects together, the sum of their shifts. -/
def totalShift (fs : List RegisterFeature) : ℤ := (fs.map shift).sum

@[simp] theorem totalShift_nil : totalShift [] = 0 := rfl

@[simp] theorem totalShift_cons (f : RegisterFeature) (fs : List RegisterFeature) :
    totalShift (f :: fs) = f.shift + totalShift fs := by
  simp [totalShift]

end RegisterFeature

/-! ### Register tiers -/

/-- A **register tier**: the register features each register-bearing unit bears, in order —
none for a registerless unit, one for a downstepped or upstepped unit, two for a register
contour or a double downstep ([lionnet-2025]). -/
abbrev RegisterTier := List (List RegisterFeature)

namespace RegisterTier

/-- The register level each unit reaches: terracing by the units' total shifts. -/
def realize (level : ℤ) (tier : RegisterTier) : List ℤ :=
  terrace level (tier.map RegisterFeature.totalShift)

@[simp] theorem length_realize (level : ℤ) (tier : RegisterTier) :
    (realize level tier).length = tier.length := by
  simp [realize]

/-- A tier realizes piecewise: the second part continues from the register the first leaves. -/
theorem realize_append (level : ℤ) (tier tier' : RegisterTier) :
    realize level (tier ++ tier') =
      realize level tier ++ realize (level + (tier.map RegisterFeature.totalShift).sum) tier' := by
  simp only [realize, List.map_append, terrace_append]

/-- A lower baseline gives pointwise lower levels. -/
theorem realize_baseline_mono (tier : RegisterTier) {n m : ℤ} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realize n tier) (realize m tier) :=
  terrace_mono (List.forall₂_refl _) h

/-- The units bearing a given feature. -/
def bearing (f : RegisterFeature) (tier : RegisterTier) : List ℕ :=
  tier.findIdxs (f ∈ ·)

theorem mem_bearing {f : RegisterFeature} {tier : RegisterTier} {i : ℕ} :
    i ∈ bearing f tier ↔ ∃ h : i < tier.length, f ∈ tier[i] := by
  simp [bearing]

end RegisterTier

/-! ### Registered words -/

/-- A syllable sequence bearing a register tier: the syllables, whose morae are the
register-bearing units ([lionnet-2025]), and the register features each mora bears. Mora counts
are read by a weight function `w`, positive as every syllable has a nucleus. -/
structure Registered (S : Type*) where
  /-- The syllables. -/
  syllables : List S
  /-- The register features on each mora, left to right. -/
  tier : RegisterTier
  deriving DecidableEq

namespace Registered

variable {S : Type*} (w : S → ℕ+) (r : Registered S)

/-- The mora count of each syllable. -/
def shape : List ℕ := r.syllables.map fun σ ↦ (w σ : ℕ)

/-- The number of morae. -/
def moraCount : ℕ := (r.shape w).sum

/-- The syllabification of the morae: the composition whose blocks are the syllables' mora
counts. -/
def composition : Composition (r.moraCount w) where
  blocks := r.shape w
  blocks_pos hi := by obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hi; exact (w σ).pos
  blocks_sum := rfl

/-- The tier has one entry per mora. -/
def IsAligned : Prop := r.tier.length = r.moraCount w

instance : Decidable (r.IsAligned w) := inferInstanceAs (Decidable (_ = _))

/-- The register features on the morae of each syllable: the tier split along the
syllabification. -/
def syllableFeatures : List (List (List RegisterFeature)) :=
  r.tier.splitWrtComposition (r.composition w)

/-- Concatenation: the syllables and the tier in sequence. -/
def append (r s : Registered S) : Registered S := ⟨r.syllables ++ s.syllables, r.tier ++ s.tier⟩

instance : Append (Registered S) := ⟨append⟩

@[simp] theorem append_syllables (r s : Registered S) :
    (r ++ s).syllables = r.syllables ++ s.syllables := rfl

@[simp] theorem append_tier (r s : Registered S) : (r ++ s).tier = r.tier ++ s.tier := rfl

/-- The word of a sequence of words. -/
def concat (rs : List (Registered S)) : Registered S := rs.foldr (· ++ ·) ⟨[], []⟩

@[simp] theorem concat_nil : concat ([] : List (Registered S)) = ⟨[], []⟩ := rfl

@[simp] theorem concat_cons (r : Registered S) (rs : List (Registered S)) :
    concat (r :: rs) = r ++ concat rs := rfl

end Registered

end Tone
