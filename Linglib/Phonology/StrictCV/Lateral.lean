/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range

/-!
# Lateral relations

In Strict CV syllable structure is a network of two lateral forces that nuclei discharge
leftwards. Government diminishes the melody of its target and licensing supports it. Each force
lands on the onset of the nucleus that discharges it or on the nucleus before, and no position
receives both. Government takes precedence: it goes to the preceding nucleus when that nucleus
is unexpressed and the governor is able to govern it, and to the onset otherwise, and licensing
goes to the position that escaped government. Which nuclei are lateral actors, and what each
can govern, varies with the language and is the theory's parameter; a governed nucleus is never
one. The forces of a domain are then [determined](##StrictCV.Lateral.isLateral_iff). A consonant
is weak when governed, strong when licensed and a coda when its nucleus discharges nothing; a
syllable is open when its nucleus is licensed. The Empty Category Principle lets a nucleus stay
unexpressed when it is governed, enclosed in a domain of infrasegmental government, or final.

## Implementation notes

A domain is its list of nuclei together with the set of positions that are phonetically
expressed. All relations are local, between a nucleus and its own onset or the nucleus before
it, as the handbook states the theory; Scheer's book lets government apply over a domain of
infrasegmental government instead, and the two agree on which nuclei are unexpressed when the
enclosed nucleus governs whatever a full nucleus does. What may support a domain of
infrasegmental government is open in the sources and is a field of the parameter. An initial
nucleus that governs its own onset has no nucleus to license; its licensing is recorded with
the target `Target.nucleus` and lands on nothing.

## TODO

Every theorem is stated and unproved. Not stated: long vowels, whose empty complement calls for
licensing; degrees of licensing strength, by which a final empty nucleus may act and yet fail
to license length; stress; and a second, autosegmental licensing that every nucleus discharges.

## References

* [scheer-2004]
* [scheer-zikova-2010]
* [cavirani-2022]
-/

@[expose] public section

namespace StrictCV.Lateral

/-! ### Nuclei -/

/-- The melody of a nucleus: none, melody that alternates with zero, or melody that is always
expressed. -/
inductive Melody
  /-- No melody. -/
  | empty
  /-- Melody that is expressed unless the nucleus is governed. -/
  | floating
  /-- Associated melody. -/
  | associated
  deriving DecidableEq, Repr

/-- A nucleus as the lexicon gives it. -/
structure Nucleus where
  /-- The melody of the nucleus. -/
  melody : Melody
  /-- The consonants flanking the nucleus may contract infrasegmental government. -/
  cluster : Bool := false
  deriving DecidableEq, Repr

/-- The nuclear objects that differ in lateral ability. -/
inductive Kind
  /-- A full nucleus, expressed with associated melody. -/
  | full
  /-- Schwa, a nucleus expressed without associated melody, by alternation or epenthesis. -/
  | schwa
  /-- An unexpressed nucleus with the given melody, final in its domain or not. -/
  | silent (m : Melody) (final : Bool)
  deriving DecidableEq, Repr

/-- The kind of a nucleus that is expressed or not and final or not. -/
def Nucleus.kind (x : Nucleus) (expressed final : Bool) : Kind :=
  if expressed then (if x.melody = .associated then .full else .schwa) else .silent x.melody final

/-- The lateral actorship of a language: what each kind of ungoverned nucleus can do. -/
structure Actorship where
  /-- A nucleus of this kind can govern a nucleus with the given melody. -/
  governs : Kind → Melody → Bool
  /-- A nucleus of this kind can license. -/
  licenses : Kind → Bool
  /-- A nucleus of this kind supports a domain of infrasegmental government whose governing
  consonant is its onset. -/
  governmentLicenses : Kind → Bool

variable (A : Actorship) (l : List Nucleus) (s : Finset ℕ) {i j : ℕ}

/-! ### Government between nuclei -/

/-- The first nucleus of the stretch `x :: r` is enclosed in a domain of infrasegmental
government: it is unexpressed and empty, its flanking consonants may contract government, and
the next nucleus supports the domain. -/
def EnclosedFrom : ℕ → List Nucleus → Prop
  | _, [] | _, [_] => False
  | i, x :: y :: r => i ∉ s ∧ x.melody = .empty ∧ x.cluster = true ∧
      A.governmentLicenses (y.kind (decide (i + 1 ∈ s)) (decide (r = []))) = true

/-- `GovernedFrom A s i r` says that the first nucleus of the stretch `r`, nucleus `i` of its
domain, is governed by the next: it is unexpressed, not final and not enclosed, and the next
nucleus is not itself governed and can govern its melody. -/
def GovernedFrom : ℕ → List Nucleus → Prop
  | _, [] | _, [_] => False
  | i, x :: y :: r => i ∉ s ∧ ¬ EnclosedFrom A s i (x :: y :: r) ∧
      ¬ GovernedFrom (i + 1) (y :: r) ∧
      A.governs (y.kind (decide (i + 1 ∈ s)) (decide (r = []))) x.melody = true

/-- Nucleus `i` is enclosed in a domain of infrasegmental government. -/
def Enclosed (i : ℕ) : Prop := EnclosedFrom A s i (l.drop i)

/-- Nucleus `i` is governed by nucleus `i + 1`. -/
def Governed (i : ℕ) : Prop := GovernedFrom A s i (l.drop i)

/-- The kind of nucleus `i`, if the domain has one. -/
def kind (i : ℕ) : Option Kind :=
  l[i]?.map fun x ↦ x.kind (decide (i ∈ s)) (decide (i + 1 = l.length))

/-- Nucleus `i` is a governor: it is not governed and can govern at least an empty nucleus. -/
def IsGovernor (i : ℕ) : Prop := ¬ Governed A l s i ∧ ∃ k ∈ kind l s i, A.governs k .empty = true

/-- Nucleus `i` is a licensor: it is not governed and can license. -/
def IsLicensor (i : ℕ) : Prop := ¬ Governed A l s i ∧ ∃ k ∈ kind l s i, A.licenses k = true

variable {A l s}

theorem governed_iff : Governed A l s i ↔ i ∉ s ∧ ¬ Enclosed A l s i ∧ ¬ Governed A l s (i + 1) ∧
    ∃ x ∈ l[i]?, ∃ k ∈ kind l s (i + 1), A.governs k x.melody = true := by
  sorry

/-- Whether a nucleus is governed depends only on the nuclei from it onwards. -/
theorem governed_drop (k : ℕ) :
    Governed A (l.drop k) (s.filter (k ≤ ·) |>.image (· - k)) i ↔ Governed A l s (i + k) := by
  sorry

/-- A governed nucleus governs nothing. -/
theorem Governed.not_succ (h : Governed A l s i) : ¬ Governed A l s (i + 1) := by
  sorry

theorem Governed.isGovernor_succ (h : Governed A l s i) : IsGovernor A l s (i + 1) := by
  sorry

/-! ### The two forces -/

/-- The target of a lateral force: the onset of the nucleus that discharges it, or the nucleus
before. -/
inductive Target
  /-- The onset of the discharging nucleus. -/
  | onset
  /-- The preceding nucleus. -/
  | nucleus
  deriving DecidableEq, Repr

open Classical in
variable (A l s) in
/-- Where nucleus `j` discharges its government: on the preceding nucleus when it governs it,
and otherwise on its own onset if it is a governor. -/
noncomputable def gov (j : ℕ) : Option Target :=
  if ∃ i, i + 1 = j ∧ Governed A l s i then some .nucleus
  else if IsGovernor A l s j then some .onset else none

open Classical in
variable (A l s) in
/-- Where nucleus `j` discharges its licensing: on its own onset unless it governs it, and then
on the preceding nucleus. -/
noncomputable def lic (j : ℕ) : Option Target :=
  if IsLicensor A l s j then (if gov A l s j = some .onset then some .nucleus else some .onset)
  else none

/-- An assignment of a target to the government and to the licensing of each nucleus. -/
@[ext] structure Assignment where
  /-- Where nucleus `j` discharges its government, if it governs. -/
  gov : ℕ → Option Target
  /-- Where nucleus `j` discharges its licensing, if it licenses. -/
  lic : ℕ → Option Target

variable (A l s) in
/-- The principles that distribute the lateral forces of a domain. -/
structure IsLateral (a : Assignment) : Prop where
  /-- Exactly the governors govern. -/
  gov_isSome_iff (j : ℕ) : (a.gov j).isSome ↔ IsGovernor A l s j
  /-- Exactly the licensors license. -/
  lic_isSome_iff (j : ℕ) : (a.lic j).isSome ↔ IsLicensor A l s j
  /-- Government goes to the preceding nucleus exactly when it governs that nucleus. -/
  gov_eq_nucleus_iff (j : ℕ) : a.gov j = some .nucleus ↔ ∃ i, i + 1 = j ∧ Governed A l s i
  /-- A nucleus does not govern and license the same position. -/
  gov_ne_lic (j : ℕ) (t : Target) : a.gov j = some t → a.lic j ≠ some t
  /-- Licensing goes to the preceding nucleus only when the onset is governed. -/
  gov_of_lic_eq_nucleus (j : ℕ) : a.lic j = some .nucleus → a.gov j = some .onset

/-- The principles determine the forces of a domain. -/
theorem isLateral_iff {a : Assignment} : IsLateral A l s a ↔ a = ⟨gov A l s, lic A l s⟩ := by
  sorry

variable (A l s) in
/-- The onset of nucleus `j` is governed, the weak position of an intervocalic consonant. -/
def OnsetGoverned (j : ℕ) : Prop := gov A l s j = some .onset

variable (A l s) in
/-- The onset of nucleus `j` is licensed, the strong position. -/
def OnsetLicensed (j : ℕ) : Prop := lic A l s j = some .onset

variable (A l s) in
/-- Nucleus `i` is licensed by the next nucleus, as the nucleus of an open syllable is. -/
def Licensed (i : ℕ) : Prop := lic A l s (i + 1) = some .nucleus

/-- No onset is both governed and licensed. -/
theorem not_onsetGoverned_and_onsetLicensed :
    ¬ (OnsetGoverned A l s j ∧ OnsetLicensed A l s j) := by
  sorry

/-- No nucleus is both governed and licensed. -/
theorem not_governed_and_licensed : ¬ (Governed A l s i ∧ Licensed A l s i) := by
  sorry

/-- The Coda Mirror: where every governor licenses, an onset is licensed exactly when its
nucleus governs the nucleus before it, which is the position after a governed nucleus. -/
theorem onsetLicensed_iff_governed (h : IsGovernor A l s (j + 1) → IsLicensor A l s (j + 1)) :
    OnsetLicensed A l s (j + 1) ↔ Governed A l s j ∨
      IsLicensor A l s (j + 1) ∧ ¬ IsGovernor A l s (j + 1) := by
  sorry

/-- An onset is a coda, neither governed nor licensed, exactly when its nucleus neither governs
nor licenses, as a governed nucleus does not. -/
theorem not_onsetGoverned_and_not_onsetLicensed_iff :
    ¬ OnsetGoverned A l s (j + 1) ∧ ¬ OnsetLicensed A l s (j + 1) ↔
      ¬ IsGovernor A l s (j + 1) ∧ ¬ IsLicensor A l s (j + 1) := by
  sorry

/-- A nucleus is licensed exactly when the next nucleus is a licensor that governs its own
onset. -/
theorem licensed_iff :
    Licensed A l s i ↔ IsLicensor A l s (i + 1) ∧ OnsetGoverned A l s (i + 1) := by
  sorry

/-! ### The Empty Category Principle -/

variable (A l s) in
/-- The Empty Category Principle: associated melody is expressed, and a nucleus is unexpressed
only if it is governed, enclosed in a domain of infrasegmental government, or final. -/
structure SatisfiesECP : Prop where
  /-- Only nuclei of the domain are expressed. -/
  lt_length : ∀ i ∈ s, i < l.length
  /-- Associated melody is expressed. -/
  mem_of_associated : ∀ i, (∃ x ∈ l[i]?, x.melody = .associated) → i ∈ s
  /-- The silence of an unexpressed nucleus is licensed. -/
  licensed : ∀ i < l.length, i ∉ s →
    Governed A l s i ∨ Enclosed A l s i ∨ i + 1 = l.length

/-- Of two successive unexpressed nuclei before the last, one is enclosed. -/
theorem SatisfiesECP.enclosed_of_notMem (h : SatisfiesECP A l s) (hi : i ∉ s) (hj : i + 1 ∉ s)
    (hl : i + 2 < l.length) : Enclosed A l s i ∨ Enclosed A l s (i + 1) := by
  sorry

/-! ### The obligatory realization -/

variable (A) in
/-- The expression of each nucleus of a stretch when every nucleus that may be unexpressed is,
except those of `R`, which are required to be expressed; and whether the first is governed. -/
def obligatoryFrom (R : Finset ℕ) : ℕ → List Nucleus → List Bool × Bool
  | _, [] => ([], false)
  | i, x :: r =>
    match r, obligatoryFrom R (i + 1) r with
    | [], _ => ([decide (x.melody = .associated ∨ i ∈ R)], false)
    | y :: r', (es, gy) =>
      let ky := y.kind (es.headD false) (decide (r' = []))
      let enclosed := decide (x.melody = .empty) && x.cluster && A.governmentLicenses ky
      let governable := !gy && A.governs ky x.melody
      let e := decide (x.melody = .associated ∨ i ∈ R) || !(enclosed || governable)
      (e :: es, !e && !enclosed && governable)

variable (A l) in
/-- The obligatory realization, computed from the right: a nucleus is expressed when it has
associated melody, is required to be, or nothing licenses its silence. -/
def obligatory (R : Finset ℕ) : Finset ℕ :=
  (Finset.range l.length).filter fun i ↦ (obligatoryFrom A R 0 l).1.getD i false = true

variable {R : Finset ℕ}

theorem satisfiesECP_obligatory : SatisfiesECP A l (obligatory A l R) := by
  sorry

theorem subset_obligatory (hR : ∀ i ∈ R, i < l.length) : R ⊆ obligatory A l R := by
  sorry

/-- The obligatory realization is the one that satisfies the Empty Category Principle,
expresses the required nuclei, and expresses no other nucleus without associated melody whose
silence would be licensed. -/
theorem eq_obligatory_iff (hR : ∀ i ∈ R, i < l.length) :
    s = obligatory A l R ↔ SatisfiesECP A l s ∧ R ⊆ s ∧
      ∀ i ∈ s, (∃ x ∈ l[i]?, x.melody = .associated) ∨ i ∈ R ∨
        ¬ (Governed A l (s.erase i) i ∨ Enclosed A l (s.erase i) i ∨ i + 1 = l.length) := by
  sorry

/-- Havlík's Law: where schwa governs alternating vowels and an unexpressed final nucleus does
not, a word of alternating vowels expresses those at an even distance from its end, the last
standing at distance one. -/
theorem mem_obligatory_of_schwa_governs (hl : ∀ x ∈ l, x.melody = .floating)
    (hs : A.governs .schwa .floating = true)
    (hf : A.governs (.silent .floating true) .floating = false) :
    i ∈ obligatory A l ∅ ↔ i < l.length ∧ Even (l.length - i) := by
  sorry

/-- Lower: where no nucleus without associated melody governs alternating vowels, a word of
alternating vowels expresses all but the last. -/
theorem mem_obligatory_of_not_schwa_governs (hl : ∀ x ∈ l, x.melody = .floating)
    (hs : A.governs .schwa .floating = false)
    (hf : ∀ b, A.governs (.silent .floating b) .floating = false) :
    i ∈ obligatory A l ∅ ↔ i + 1 < l.length := by
  sorry

end StrictCV.Lateral
