/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Harmony.Basic
public import Linglib.Phonology.Segmental.Basic
public import Linglib.Phonology.SearchCopy

/-!
# Harmony systems

A harmony system is Rose and Walker's descriptive object: a `Phonology.Harmony.Pattern`,
whose participation classes are the triggers, blockers and transparent segments, together
with the targets and a write of the harmonic value into them. It commits to no mechanism.
Its search-and-copy reading (`System.searchCopy`) is Nevins's procedure with the
pattern's tier as the visible segments, the targets on it as the needy segments, its
participating segments as the sources and its direction as the direction of search; the
rival accounts, Goldsmith's autosegmental spreading, Rose and Walker's Agreement by
Correspondence and OT alignment, are not derived here. Under that reading a harmonic word is a
fixed point of the run (`System.scan_eq_self_of_harmonic`), and on a saturated system the fixed
points are exactly the harmonic words (`System.harmonic_iff_scan_eq_self`), the TSL₂ language of
`Pattern.harmonic_iff_mem_tsl`.

## Main definitions

* `System`: a pattern, its targets and its write; `System.mk'` compiles the
  Rose and Walker roles over `Phonology.Segment`.
* `System.searchCopy`: the search-and-copy reading of a system.
* `System.Saturated`: every visible segment is a participating target with a value.

## Main results

* `System.scan_eq_self_of_harmonic`, `System.harmonic_iff_scan_eq_self`,
  `System.harmonic_scan`: the run's fixed points and image against the pattern's surface
  harmonicity.
* `System.scan_eq_map`: on a saturated system the run writes the first visible segment's
  value into every visible segment.

## Implementation notes

Under the search-and-copy reading a blocker is a visible non-source: the search stops at it
and the target takes the default, as in Nevins's defective intervention and
Belth's Khalkha rule. Ritter and van der Hulst's reading, on which a blocker
imposes its own value, is the case where the blocker's pattern value is the default;
`Pattern.Harmonic` follows that reading, so the fixed-point results assume no default and
blockers that are not targets. Every participating segment donates whether or not it is a
target, as Nevins requires, and a transparent target does not undergo, since Rose and Walker's
transparent segments neither undergo nor block. An icy target is a target that is not a
source, which the reading expresses because participation is stored on the segment; on bare
segments Burness, McMullin and Nevins show that search and copy cannot. A bidirectional pattern is
run left to right; the outward-from-root pass is not modelled. A single tier is not always
enough: Uyghur backness harmony is not TSL, as Mayer and Major show.

## References

* [rose-walker-2011]
* [nevins-2010]
* [ritter-vanderhulst-2024-themes]
* [burness-mcmullin-nevins-2024]
* [belth-2026]
* [jurgec-2011]
* [goldsmith-1976]
* [rose-walker-2004]
* [mayer-major-2018]
-/

@[expose] public section

namespace Phonology.Harmony

/-- The edge a pattern's scan starts from, bidirectional patterns being run from the left. -/
def Direction.scanEdge : Direction → Edge
  | .rightward | .bidirectional => .left
  | .leftward => .right

/-! ### Systems -/

/-- A harmony system consists of a pattern, the targets, a write of the harmonic value into
a target, which with the pattern's valuation forms a lens on the targets, and a last-resort
default. -/
structure System (α : Type*) where
  /-- The descriptive pattern. -/
  pattern : Pattern α Bool
  /-- The segments that undergo. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- The segment with the harmonic value written into it. -/
  write : Bool → α → α
  /-- Reading back a value written into a target gives that value. -/
  value_write : ∀ v s, IsTarget s → pattern.value (write v s) = some v
  /-- Writing the value a target already carries leaves it unchanged. -/
  write_value : ∀ v s, IsTarget s → pattern.value s = some v → write v s = s
  /-- The value a target takes when no source reaches it. -/
  default : Option Bool := none

attribute [instance] System.decTarget

namespace System

variable {α : Type*} (sys : System α)

/-- The search-and-copy reading of a system takes the pattern's tier as the visible segments,
the targets on it as the needy segments, its participating segments as the sources, and its
direction as the direction of search. -/
def searchCopy : SearchCopy α where
  tier := sys.pattern.OnTier
  IsTarget s := sys.IsTarget s ∧ sys.pattern.OnTier s
  IsSource s _ := sys.pattern.participation s = .participating
  value := sys.pattern.value
  write := sys.write
  value_write v s h := sys.value_write v s h.1
  write_value v s h := sys.write_value v s h.1
  default := sys.default
  direction := sys.pattern.direction.scanEdge

@[simp] theorem searchCopy_tier : sys.searchCopy.tier = sys.pattern.OnTier := rfl

@[simp] theorem searchCopy_isTarget (s : α) :
    sys.searchCopy.IsTarget s ↔ sys.IsTarget s ∧ sys.pattern.OnTier s :=
  Iff.rfl

@[simp] theorem searchCopy_isSource (s t : α) :
    sys.searchCopy.IsSource s t ↔ sys.pattern.participation s = .participating :=
  Iff.rfl

@[simp] theorem searchCopy_value : sys.searchCopy.value = sys.pattern.value := rfl

@[simp] theorem searchCopy_write : sys.searchCopy.write = sys.write := rfl

@[simp] theorem searchCopy_default : sys.searchCopy.default = sys.default := rfl

@[simp] theorem searchCopy_direction :
    sys.searchCopy.direction = sys.pattern.direction.scanEdge := rfl

theorem found_some_of_participating {a : α} (h : sys.pattern.participation a = .participating)
    (t : α) : sys.searchCopy.found t (some a) = sys.pattern.value a :=
  sys.searchCopy.found_some_of_isSource h

theorem found_some_of_not_participating {a : α}
    (h : sys.pattern.participation a ≠ .participating) (t : α) :
    sys.searchCopy.found t (some a) = none :=
  sys.searchCopy.found_some_of_not_isSource h

@[simp] theorem searchCopy_relation : sys.searchCopy.relation = .agree := rfl

theorem emit_eq_write_of_found_eq_some {s : α} (h : sys.IsTarget s) (hs : sys.pattern.OnTier s)
    {w : Option α} {v : Bool} (hf : sys.searchCopy.found s w = some v) :
    sys.searchCopy.emit w s = sys.write v s := by
  rw [sys.searchCopy.emit_of_isTarget ⟨h, hs⟩, SearchCopy.copied, hf]; rfl

/-- A segment off the tier does not undergo. -/
theorem emit_of_not_onTier {s : α} (h : ¬ sys.pattern.OnTier s) (w : Option α) :
    sys.searchCopy.emit w s = s :=
  sys.searchCopy.emit_of_not_isTarget (fun ht ↦ h ht.2) w

/-- Compiles the [rose-walker-2011] roles over `Phonology.Segment` from the harmonic feature,
the targets, the transparent segments, the direction, the blockers, and the default; every
other segment is a trigger. -/
def mk' (feature : Feature) (IsTarget IsTransparent : Segment → Prop) [DecidablePred IsTarget]
    [DecidablePred IsTransparent] (direction : Direction := .rightward)
    (IsBlocker : Segment → Prop := fun _ ↦ False) [DecidablePred IsBlocker]
    (default : Option Bool := none) : System Segment where
  pattern :=
    { value := fun s ↦ s feature
      participation := fun s ↦
        if IsBlocker s then .opaque
        else if IsTransparent s then .transparent
        else .participating
      direction := direction }
  IsTarget := IsTarget
  write v s := Function.update s feature (some v)
  value_write _ _ _ := Function.update_self ..
  write_value _ _ _ h := h ▸ Function.update_eq_self ..
  default := default

/-! ### Fixed points and image -/

private theorem isChain_toList_append_cons {R : α → α → Prop} (a? : Option α) (x : α)
    (l : List α) :
    (a?.toList ++ x :: l).IsChain R ↔ (∀ a ∈ a?, R a x) ∧ (x :: l).IsChain R := by
  cases a? with
  | none => simp
  | some a => simp [List.isChain_cons_cons]

/-- After the visible segment `a?`, a word whose tier continues it compatibly is left
unchanged, provided there is no default and blockers do not undergo. -/
private theorem runFrom_eq_self (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) :
    ∀ (w : List α) (a? : Option α),
      (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible →
        sys.searchCopy.toMealy.runFrom a? w = w
  | [], _, _ => rfl
  | x :: xs, a?, h => by
    by_cases hx : sys.pattern.OnTier x
    · rw [sys.pattern.tier_cons_of_onTier hx, isChain_toList_append_cons] at h
      have hemit : sys.searchCopy.emit a? x = x := by
        cases a? with
        | none => exact sys.searchCopy.emit_of_found_eq_none hd (sys.searchCopy.found_none x)
        | some a =>
          by_cases ht : sys.IsTarget x
          · by_cases hs : sys.pattern.participation a = .participating
            · rcases h.1 a rfl with hicy | hop | hval
              · rw [hicy] at hs; cases hs
              · exact absurd ht (hb x hop)
              · rcases hv : sys.pattern.value a with _ | v
                · exact sys.searchCopy.emit_of_found_eq_none hd
                    (by rw [sys.found_some_of_participating hs, hv])
                · exact sys.searchCopy.emit_eq_self
                    (by rw [sys.found_some_of_participating hs, hv]) (hval ▸ hv)
            · exact sys.searchCopy.emit_of_found_eq_none hd
                (sys.found_some_of_not_participating hs x)
          · exact sys.searchCopy.emit_of_not_isTarget (fun h ↦ ht h.1) _
      rw [sys.searchCopy.toMealy_runFrom_cons_of_tier hx, hemit]
      exact congrArg _ (runFrom_eq_self hd hb xs (some x) (by simpa using h.2))
    · rw [sys.pattern.tier_cons_of_not_onTier hx] at h
      rw [sys.searchCopy.toMealy_runFrom_cons_of_not_tier hx, sys.emit_of_not_onTier hx]
      exact congrArg _ (runFrom_eq_self hd hb xs a? h)

/-- A harmonic word is a fixed point of the run, provided there is no default and blockers
do not undergo. -/
theorem scan_eq_self_of_harmonic (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) {w : List α}
    (h : sys.pattern.Harmonic w) : sys.searchCopy.scan w = w :=
  sys.runFrom_eq_self hd hb w none h

/-- A system is saturated when every visible segment is a participating target with a value;
on such a system the run decides the surface language. -/
def Saturated : Prop :=
  ∀ s, sys.pattern.OnTier s →
    sys.IsTarget s ∧ sys.pattern.participation s = .participating ∧ (sys.pattern.value s).isSome

private theorem harmonic_of_runFrom_eq_self (hs : sys.Saturated) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      sys.searchCopy.toMealy.runFrom a? w = w →
        (a?.toList ++ sys.pattern.tier w).IsChain sys.pattern.Compatible
  | [], none, _, _ => List.isChain_nil
  | [], some _, _, _ => List.isChain_singleton _
  | x :: xs, a?, ha, h => by
    by_cases hx : sys.pattern.OnTier x
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_tier hx] at h
      obtain ⟨hemit, hrest⟩ := List.cons.inj h
      rw [hemit] at hrest
      have ih := harmonic_of_runFrom_eq_self hs xs (some x)
        (fun _ h ↦ Option.mem_some_iff.mp h ▸ hx) hrest
      rw [sys.pattern.tier_cons_of_onTier hx, isChain_toList_append_cons]
      refine ⟨fun a ha' ↦ ?_, by simpa using ih⟩
      obtain ⟨_, hpa, hv⟩ := hs a (ha a ha')
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
      rw [Option.mem_def] at ha'
      subst ha'
      rw [sys.emit_eq_write_of_found_eq_some (hs x hx).1 hx
        (by rw [sys.found_some_of_participating hpa, hv])] at hemit
      have hvx : sys.pattern.value x = some v := by
        have := sys.value_write v x (hs x hx).1; rwa [hemit] at this
      exact Or.inr (Or.inr (hv.trans hvx.symm))
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_not_tier hx, sys.emit_of_not_onTier hx] at h
      rw [sys.pattern.tier_cons_of_not_onTier hx]
      exact harmonic_of_runFrom_eq_self hs xs a? ha (List.cons.inj h).2

/-- On a saturated system without a default the harmonic words are exactly the fixed points
of the run. -/
theorem harmonic_iff_scan_eq_self (hs : sys.Saturated) (hd : sys.default = none)
    (hb : ∀ s, sys.pattern.participation s = .opaque → ¬ sys.IsTarget s) (w : List α) :
    sys.pattern.Harmonic w ↔ sys.searchCopy.scan w = w :=
  ⟨sys.scan_eq_self_of_harmonic hd hb,
    sys.harmonic_of_runFrom_eq_self hs w none (fun _ h ↦ by cases h)⟩

private theorem runFrom_some_eq_map (hs : sys.Saturated) (hw : sys.searchCopy.PreservesTier)
    (v : Bool) : ∀ (w : List α) (a : α), sys.pattern.OnTier a → sys.pattern.value a = some v →
      sys.searchCopy.toMealy.runFrom (some a) w =
        w.map fun s ↦ if sys.pattern.OnTier s then sys.write v s else s
  | [], _, _, _ => rfl
  | x :: xs, a, ha, hv => by
    rw [List.map_cons]
    by_cases hx : sys.pattern.OnTier x
    · have he : sys.searchCopy.emit (some a) x = sys.write v x :=
        sys.emit_eq_write_of_found_eq_some (hs x hx).1 hx
          (by rw [sys.found_some_of_participating (hs a ha).2.1, hv])
      rw [sys.searchCopy.toMealy_runFrom_cons_of_tier hx, ite_eq_left hx, he,
        runFrom_some_eq_map hs hw v xs (sys.write v x) ((hw v x ⟨(hs x hx).1, hx⟩).2 hx)
          (sys.value_write v x (hs x hx).1)]
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_not_tier hx, ite_eq_right hx,
        sys.emit_of_not_onTier hx, runFrom_some_eq_map hs hw v xs a ha hv]

/-- On a saturated system without a default whose writes stay visible, the run writes the
first visible segment's value into every visible segment. -/
theorem scan_eq_map (hs : sys.Saturated) (hw : sys.searchCopy.PreservesTier)
    (hd : sys.default = none) (w : List α) : sys.searchCopy.scan w = w.map fun s ↦
      if sys.pattern.OnTier s then
        ((sys.pattern.tier w).head?.bind sys.pattern.value).elim s (sys.write · s)
      else s := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [SearchCopy.scan_eq_runFrom, List.map_cons]
    by_cases hx : sys.pattern.OnTier x
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs x hx).2.2
      rw [sys.searchCopy.toMealy_runFrom_cons_of_tier hx, ite_eq_left hx,
        sys.searchCopy.emit_of_found_eq_none hd (sys.searchCopy.found_none x),
        sys.pattern.tier_cons_of_onTier hx, List.head?_cons, Option.bind_some, hv,
        Option.elim_some, sys.write_value v x (hs x hx).1 hv,
        sys.runFrom_some_eq_map hs hw v xs x hx hv]
      simp only [Option.elim_some]
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_not_tier hx, ite_eq_right hx,
        sys.emit_of_not_onTier hx, sys.pattern.tier_cons_of_not_onTier hx]
      exact congrArg _ ih

private theorem runFrom_harmonic (hs : sys.Saturated) (hw : sys.searchCopy.PreservesTier) :
    ∀ (w : List α) (a? : Option α), (∀ a ∈ a?, sys.pattern.OnTier a) →
      (a?.toList ++ sys.pattern.tier (sys.searchCopy.toMealy.runFrom a? w)).IsChain
        sys.pattern.Compatible
  | [], none, _ => List.isChain_nil
  | [], some _, _ => List.isChain_singleton _
  | x :: xs, a?, ha => by
    by_cases hx : sys.pattern.OnTier x
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_tier hx]
      have he : sys.pattern.OnTier (sys.searchCopy.emit a? x) :=
        (sys.searchCopy.tier_emit_iff hw _ x).2 hx
      rw [sys.pattern.tier_cons_of_onTier he, isChain_toList_append_cons]
      have ih := runFrom_harmonic hs hw xs (some (sys.searchCopy.emit a? x))
        (fun _ h ↦ Option.mem_some_iff.mp h ▸ he)
      refine ⟨fun a ha' ↦ ?_, by simpa using ih⟩
      obtain ⟨_, hpa, hv⟩ := hs a (ha a ha')
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hv
      rw [Option.mem_def] at ha'
      subst ha'
      rw [sys.emit_eq_write_of_found_eq_some (hs x hx).1 hx
        (by rw [sys.found_some_of_participating hpa, hv])]
      exact Or.inr (Or.inr (hv.trans (sys.value_write v x (hs x hx).1).symm))
    · rw [sys.searchCopy.toMealy_runFrom_cons_of_not_tier hx, sys.emit_of_not_onTier hx,
        sys.pattern.tier_cons_of_not_onTier hx]
      exact runFrom_harmonic hs hw xs a? ha

/-- On a saturated system whose writes stay visible, the run's output is harmonic. -/
theorem harmonic_scan (hs : sys.Saturated) (hw : sys.searchCopy.PreservesTier) (w : List α) :
    sys.pattern.Harmonic (sys.searchCopy.scan w) :=
  sys.runFrom_harmonic hs hw w none (fun _ h ↦ by cases h)

end System

end Phonology.Harmony
