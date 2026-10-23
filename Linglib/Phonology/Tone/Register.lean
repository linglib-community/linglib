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
# Register: the terracing realization of `[raised]`

The syntagmatic reading of `[raised]` ([snider-1999], [lionnet-2025]): each `[-raised]`
node lowers the register for everything that follows and each `[+raised]` node raises it,
so a node sequence is realized as the running sum of its shifts from a baseline —
terracing, as in the register-only systems of Drubea and Numèè and in the catathesis of
Japanese and English intonation ([beckman-pierrehumbert-1986]).

A register tier associates its nodes to morae ([snider-1999]'s register-bearing units). A
mora may bear no node, one, or several — a register contour, or the double downstep of
[lionnet-2025] — so the tier over a word is the list of each mora's nodes, and a registered
word is its syllables together with that tier, generic over the syllable type with mora
counts read by a weight function, as `Prosody.Foot`. The syllabification of the morae is
the `Composition` whose blocks are the weights, and the per-syllable nodes are the tier split
along it.

## Main definitions

* `terrace` — the levels reached from a baseline by cumulative shifts (`List.scanl`).
* `TRN.pitchEffect`, `realizePitch` — the shift a node contributes and the levels of a node
  sequence; `pitchDeltas`, the same from `0`.
* `RegisterTier`, `RegisterTier.realize` — the nodes on each mora and the level each mora
  reaches.
* `Registered` — syllables with a register tier; `composition`, the syllabification of the
  morae; `syllableNodes`, `IsAligned`, `append`, `concat`.

## Main results

* `terrace_append`, `terrace_add`, `terrace_mono` — piecewise realization, a baseline only
  shifts the levels, and pointwise monotonicity in the shifts and the baseline: the basis
  of catathesis blocking.
* `RegisterTier.realize_map_singleton` — a tier with one node per mora realizes as the node
  sequence.

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

/-! ### Node sequences -/

/-- The register shift a node contributes: `[-raised]` lowers, `[+raised]` raises, an
unspecified `[raised]` is inert. -/
def TRN.pitchEffect (t : TRN) : Int :=
  match t.raised with
  | none => 0
  | some false => -1
  | some true => 1

/-- The pitch levels of a node sequence from a baseline, each node's shift cumulative. -/
def realizePitch (level : Int) (ts : List TRN) : List Int :=
  terrace level (ts.map TRN.pitchEffect)

@[simp] theorem realizePitch_nil (level : Int) : realizePitch level [] = [] := by
  simp [realizePitch]

@[simp] theorem realizePitch_cons (level : Int) (t : TRN) (rest : List TRN) :
    realizePitch level (t :: rest) =
      (level + t.pitchEffect) :: realizePitch (level + t.pitchEffect) rest :=
  terrace_cons _ _ _

@[simp] theorem length_realizePitch (level : Int) (ts : List TRN) :
    (realizePitch level ts).length = ts.length := by
  simp [realizePitch]

theorem realizePitch_append (level : Int) (ts us : List TRN) :
    realizePitch level (ts ++ us) =
      realizePitch level ts ++ realizePitch (level + (ts.map TRN.pitchEffect).sum) us := by
  simp only [realizePitch, List.map_append, terrace_append]

/-- The register shifts from the start: no privileged pitch, only the differences. -/
def pitchDeltas (ts : List TRN) : List Int := realizePitch 0 ts

theorem realizePitch_eq_pitchDeltas_shift (level : Int) (ts : List TRN) :
    realizePitch level ts = (pitchDeltas ts).map (· + level) := by
  simpa [pitchDeltas, realizePitch] using terrace_add 0 level (ts.map TRN.pitchEffect)

theorem realizePitch_mono {ts₁ ts₂ : List TRN}
    (hts : List.Forall₂ ((· ≤ ·) on TRN.pitchEffect) ts₁ ts₂) {n m : Int}
    (hnm : n ≤ m) : List.Forall₂ (· ≤ ·) (realizePitch n ts₁) (realizePitch m ts₂) :=
  terrace_mono (List.forall₂_map_right_iff.2 <| List.forall₂_map_left_iff.2 hts) hnm

theorem realizePitch_baseline_mono (ts : List TRN) {n m : Int} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n ts) (realizePitch m ts) :=
  realizePitch_mono (List.forall₂_same.mpr fun _ _ => le_rfl) h

/-! ### Register tiers over morae -/

/-- A **register tier** as associated to the morae of a word: the nodes each mora bears, in
order — none for a registerless mora, one for a downstepped or upstepped mora, two for a
register contour or a double downstep ([lionnet-2025]). -/
abbrev RegisterTier := List (List TRN)

namespace RegisterTier

/-- The shift a mora's nodes contribute together. -/
def moraShift (ns : List TRN) : Int := (ns.map TRN.pitchEffect).sum

@[simp] theorem moraShift_nil : moraShift [] = 0 := rfl

@[simp] theorem moraShift_singleton (t : TRN) : moraShift [t] = t.pitchEffect := by
  simp [moraShift]

/-- The register level each mora reaches: terracing by the morae's total shifts. -/
def realize (level : Int) (tier : RegisterTier) : List Int :=
  terrace level (tier.map moraShift)

@[simp] theorem length_realize (level : Int) (tier : RegisterTier) :
    (realize level tier).length = tier.length := by
  simp [realize]

/-- A tier with one node per mora realizes as the node sequence. -/
theorem realize_map_singleton (level : Int) (ts : List TRN) :
    realize level (ts.map ([·])) = realizePitch level ts := by
  simp [realize, realizePitch, List.map_map, Function.comp_def]

/-- All the nodes of a tier, in order. -/
abbrev nodes (tier : RegisterTier) : List TRN := tier.flatten

/-- The morae bearing a given node. -/
def bearing (t : TRN) (tier : RegisterTier) : List ℕ :=
  (List.range tier.length).filter fun i ↦ t ∈ tier.getD i []

end RegisterTier

/-! ### Registered words -/

/-- A syllable sequence bearing a register tier: the syllables, whose morae are the
register-bearing units ([lionnet-2025]), and the nodes each mora bears. Mora counts are
read by a weight function `w`, positive as a syllable has a nucleus, as in `Prosody.Foot`. -/
structure Registered (S : Type*) where
  /-- The syllables. -/
  syllables : List S
  /-- The nodes on each mora, left to right. -/
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

/-- The nodes on the morae of each syllable: the tier split along the syllabification. -/
def syllableNodes : List (List (List TRN)) := r.tier.splitWrtComposition (r.composition w)

/-- Syllable `i` bears no node. -/
def IsRegisterless (i : ℕ) : Prop := ∀ ns ∈ (r.syllableNodes w).getD i [], ns = []

instance (i : ℕ) : Decidable (r.IsRegisterless w i) := List.decidableBAll _ _

theorem length_syllableNodes : (r.syllableNodes w).length = r.syllables.length := by
  simp [syllableNodes, List.length_splitWrtComposition, composition, Composition.length, shape]

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
