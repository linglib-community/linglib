/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.PNat.Defs
public import Mathlib.Logic.Function.Defs
public import Linglib.Phonology.Tone.Basic

/-!
# Register features and terracing

In Snider's Register Tier Theory a register feature on the register tier shifts the register
relative to the preceding register setting, `h` higher and `l` lower: an upstep and a downstep.
The shift is syntagmatic, and a register feature is a different object from the paradigmatic
tone features of a `TRN`, `[±upper]` among them, which Yip and Pulleyblank also call a register
feature but which places a tone in a half of the current register. A sequence of register
features is realized as the running sum of its shifts from a baseline, which is terracing, as in
the register-only systems of Drubea and Numèè ([lionnet-2025]) and in the catathesis of Japanese
and English intonation ([beckman-pierrehumbert-1986]).

A register tier gives each register-bearing unit the register features it bears: none, one, or
several, a register contour or the double downstep of [lionnet-2025]. In Drubea and Numèè the
register-bearing unit is the mora, and a registered word is its syllables together with the tier
over their morae, generic over the syllable type with mora counts read by a weight function, as
`Prosody.Foot`. The syllabification of the morae is the `Composition` whose blocks are the
weights, and the per-syllable features are the tier split along it.

## Main definitions

* `terrace` — the levels reached from a baseline by cumulative shifts (`List.scanl`).
* `RegisterFeature`, `RegisterFeature.shift` — Snider's register features and their shifts.
* `RegisterTier`, `RegisterTier.realize` — the features on each register-bearing unit and the
  level each unit reaches.
* `Registered` — syllables with a register tier over their morae; `composition`, the
  syllabification of the morae; `syllableFeatures`, `IsAligned`, `append`, `concat`.

## Main results

* `terrace_append`, `terrace_add`, `terrace_mono` — piecewise realization, a baseline only
  shifts the levels, and pointwise monotonicity in the shifts and the baseline: the basis
  of catathesis blocking.
* `RegisterTier.realize_append`, `RegisterTier.realize_baseline_mono` — the same for a tier.

## References

* [snider-1999]
* [lionnet-2025]
* [beckman-pierrehumbert-1986]
-/

@[expose] public section

namespace Tone

open Function

/-! ### Terracing -/

/-- **Terracing**: the register levels reached from a baseline by a sequence of shifts,
each cumulative — the running sums of the shifts. -/
def terrace (level : Int) (shifts : List Int) : List Int :=
  (shifts.scanl (· + ·) level).tail

@[simp] theorem terrace_nil (level : Int) : terrace level [] = [] := by
  simp [terrace, List.scanl_nil]

@[simp] theorem terrace_cons (level d : Int) (rest : List Int) :
    terrace level (d :: rest) = (level + d) :: terrace (level + d) rest := by
  cases rest <;> simp [terrace, List.scanl_cons, List.scanl_nil]

@[simp] theorem length_terrace (level : Int) (shifts : List Int) :
    (terrace level shifts).length = shifts.length := by
  simp [terrace]

/-- A sequence realizes piecewise: the second part continues from the register the first
part leaves. -/
theorem terrace_append (level : Int) (ds es : List Int) :
    terrace level (ds ++ es) = terrace level ds ++ terrace (level + ds.sum) es := by
  induction ds generalizing level with
  | nil => simp
  | cons d ds ih => simp only [List.cons_append, terrace_cons, ih, List.sum_cons, Int.add_assoc]

/-- A baseline only shifts the levels. -/
theorem terrace_add (level d : Int) (shifts : List Int) :
    terrace (level + d) shifts = (terrace level shifts).map (· + d) := by
  induction shifts generalizing level with
  | nil => simp
  | cons e rest ih =>
    simp only [terrace_cons, List.map_cons]
    rw [show level + d + e = level + e + d by omega, ih]

/-- **Monotonicity**: pointwise lower shifts and a lower baseline give pointwise lower
levels. Structural basis of catathesis blocking ([beckman-pierrehumbert-1986]): a register
reset at a phrase boundary leaves everything after it higher than continued compression
would. -/
theorem terrace_mono {ds es : List Int} (h : List.Forall₂ (· ≤ ·) ds es) {n m : Int}
    (hnm : n ≤ m) : List.Forall₂ (· ≤ ·) (terrace n ds) (terrace m es) := by
  induction h generalizing n m with
  | nil => simp only [terrace_nil]; exact .nil
  | cons hhead _ ih =>
    have hstep := Int.add_le_add hnm hhead
    simp only [terrace_cons]
    exact .cons hstep (ih hstep)

/-! ### Register features -/

/-- A **register feature** of Snider's Register Tier Theory ([snider-1999] p. 25): `h` effects a
register shift higher and `l` a shift lower, relative to the preceding register setting, so `h`
is an upstep and `l` a downstep. The shift is syntagmatic, unlike the paradigmatic `[±upper]` of
a `TRN`, which places a tone in the upper or lower half of the current register. -/
inductive RegisterFeature where
  /-- A register shift higher, an upstep. -/
  | h
  /-- A register shift lower, a downstep. -/
  | l
  deriving DecidableEq, Repr

/-- The register shift a feature effects: `h` one step up, `l` one step down. -/
def RegisterFeature.shift : RegisterFeature → Int
  | .h => 1
  | .l => -1

/-! ### Register tiers -/

/-- A **register tier**: the register features each register-bearing unit bears, in order —
none for a registerless unit, one for a downstepped or upstepped unit, two for a register
contour or a double downstep ([lionnet-2025]). -/
abbrev RegisterTier := List (List RegisterFeature)

namespace RegisterTier

/-- The shift a unit's features effect together. -/
def moraShift (fs : List RegisterFeature) : Int := (fs.map RegisterFeature.shift).sum

@[simp] theorem moraShift_nil : moraShift [] = 0 := rfl

@[simp] theorem moraShift_singleton (f : RegisterFeature) : moraShift [f] = f.shift := by
  simp [moraShift]

/-- The register level each unit reaches: terracing by the units' total shifts. -/
def realize (level : Int) (tier : RegisterTier) : List Int :=
  terrace level (tier.map moraShift)

@[simp] theorem length_realize (level : Int) (tier : RegisterTier) :
    (realize level tier).length = tier.length := by
  simp [realize]

/-- A tier realizes piecewise: the second part continues from the register the first leaves. -/
theorem realize_append (level : Int) (tier tier' : RegisterTier) :
    realize level (tier ++ tier') =
      realize level tier ++ realize (level + (tier.map moraShift).sum) tier' := by
  simp only [realize, List.map_append, terrace_append]

/-- A lower baseline gives pointwise lower levels. -/
theorem realize_baseline_mono (tier : RegisterTier) {n m : Int} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realize n tier) (realize m tier) :=
  terrace_mono (List.forall₂_same.mpr fun _ _ ↦ le_rfl) h

/-- All the features of a tier, in order. -/
abbrev features (tier : RegisterTier) : List RegisterFeature := tier.flatten

/-- The units bearing a given feature. -/
def bearing (f : RegisterFeature) (tier : RegisterTier) : List ℕ :=
  (List.range tier.length).filter fun i ↦ f ∈ tier.getD i []

end RegisterTier

/-! ### Registered words -/

/-- A syllable sequence bearing a register tier: the syllables, whose morae are the
register-bearing units ([lionnet-2025]), and the register features each mora bears. Mora counts
are read by a weight function `w`, positive as a syllable has a nucleus, as in `Prosody.Foot`. -/
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

/-- Syllable `i` bears no register feature. -/
def IsRegisterless (i : ℕ) : Prop := ∀ fs ∈ (r.syllableFeatures w).getD i [], fs = []

instance (i : ℕ) : Decidable (r.IsRegisterless w i) := List.decidableBAll _ _

theorem length_syllableFeatures : (r.syllableFeatures w).length = r.syllables.length := by
  simp [syllableFeatures, List.length_splitWrtComposition, composition, Composition.length, shape]

variable {w}

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

theorem moraCount_append (r s : Registered S) :
    (r ++ s).moraCount w = r.moraCount w + s.moraCount w := by
  simp [moraCount, shape, List.map_append, List.sum_append]

theorem isAligned_append {r s : Registered S} (hr : r.IsAligned w) (hs : s.IsAligned w) :
    (r ++ s).IsAligned w := by
  unfold IsAligned at *
  simp only [append_tier, List.length_append, moraCount_append, hr, hs]

theorem isAligned_concat {rs : List (Registered S)} (h : ∀ r ∈ rs, r.IsAligned w) :
    (concat rs).IsAligned w := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    exact isAligned_append (h r (List.mem_cons_self ..))
      (ih fun s hs ↦ h s (List.mem_cons_of_mem _ hs))

end Registered

end Tone
