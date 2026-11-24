module

public import Linglib.Phonology.SearchCopy
public import Linglib.Phonology.Segmental.NasalCompatibility

/-!
# Nasal harmony

In a nasal harmony nasality spreads from a trigger through a contiguous string of segments, in
one direction, until a segment that does not undergo it. A harmony is given by its triggers, by
the cut `c` on the nasalization hierarchy that separates the classes it spreads through from the
classes that block it, and by its direction.

The harmony is a search-and-copy rule in which every segment is visible. A target, a segment
with `c.IsTarget`, searches the adjacent segment on the side the scan comes from and takes
[+nasal] from it when that segment is nasal and is a trigger or a target; any other segment
halts the search.

## Main definitions

* `Phonology.Harmony.IsNasalSource`: the nasal segments that pass nasality on, the nasal
  triggers and the nasal targets.
* `Phonology.Harmony.nasalSpread`: the harmony with given triggers, cut and direction.

## Main results

* `Phonology.Harmony.nasalSpread_apply_eq_self_iff`: a harmony fixes a word exactly when no
  target that is not nasal stands next to a nasal trigger or target on the side nasality comes
  from.
* `Phonology.Harmony.map_restrict_nasalSpread`: a harmony changes nothing but nasality.
* `Phonology.Harmony.nasalSpread_sonorantStop_apply`: with the cut at the sonorant stops a
  harmony changes no word.

## Implementation notes

Spreading is strictly local, as [walker-2000] argues: no segment is skipped, so a segment that
does not undergo blocks. The obstruents that surface oral inside a nasal span, which she
analyses as targets, are not derived by the rule. A nasal segment that is neither a trigger nor
a target, such as a nasal stop where vowels alone trigger, donates nothing, since the string
does not record which segments share one [nasal] specification.

## References

* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
* [S. Rose and R. Walker, *Harmony systems* (2011)][rose-walker-2011]
* [A. Nevins, *Locality in Vowel Harmony* (2010)][nevins-2010]
-/

@[expose] public section

namespace Phonology.Harmony

variable (IsTrigger : Segment → Prop) [DecidablePred IsTrigger] (c : NasalCompatibility)
  (d : Edge)

/-- A nasal segment that passes nasality on in a harmony with triggers `IsTrigger` and cut `c`:
a nasal trigger, or a nasal target. -/
def IsNasalSource (s : Segment) : Prop := s .nasal = true ∧ (IsTrigger s ∨ c.IsTarget s)

instance : DecidablePred (IsNasalSource IsTrigger c) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The nasal harmony with triggers `IsTrigger` and cut `c`, scanning from the edge `d`: a
target takes [+nasal] from an adjacent nasal trigger or target on that side. -/
def nasalSpread : SearchCopy Segment where
  tier _ := True
  IsTarget s := c.IsTarget s
  IsSource a _ := IsNasalSource IsTrigger c a
  value s := s .nasal
  write v s := s.setFeature .nasal v
  value_write v s _ := Segment.setFeature_apply_self s .nasal v
  write_value _ _ _ h := Segment.setFeature_eq_self_iff.2 h
  direction := d

variable {IsTrigger c d}

theorem nasalSpread_emit (q : Option Segment) (s : Segment) :
    (nasalSpread IsTrigger c d).emit q s =
      if c.IsTarget s ∧ ∃ a ∈ q, IsNasalSource IsTrigger c a then s.setFeature .nasal true
      else s := by
  cases q with
  | none => simp [SearchCopy.emit, SearchCopy.copied, nasalSpread]
  | some a =>
    by_cases ha : IsNasalSource IsTrigger c a
    · simp [SearchCopy.emit, SearchCopy.copied, nasalSpread, ha, ha.1]
    · simp [SearchCopy.emit, SearchCopy.copied, nasalSpread, ha]

/-- A target `s` stands unchanged after `a` exactly when it is nasal or `a` passes no nasality
on. -/
theorem nasalSpread_emit_eq_self_iff (a s : Segment) :
    (nasalSpread IsTrigger c d).emit (some a) s = s ↔
      ¬ (IsNasalSource IsTrigger c a ∧ c.IsTarget s ∧ s .nasal ≠ some true) := by
  rw [nasalSpread_emit]
  split_ifs with h
  · obtain ⟨hs, b, hba, hb⟩ := h
    obtain rfl : a = b := Option.some.inj hba
    rw [Segment.setFeature_eq_self_iff]
    exact ⟨fun hn hh ↦ hh.2.2 hn, fun hh ↦ by_contra fun hn ↦ hh ⟨hb, hs, hn⟩⟩
  · exact iff_of_true rfl fun hh ↦ h ⟨hh.2.1, a, rfl, hh.1⟩

/-- A nasal harmony fixes a word exactly when, read in its direction, no target that is not
nasal follows a nasal trigger or target. -/
theorem nasalSpread_apply_eq_self_iff (w : List Segment) :
    (nasalSpread IsTrigger c d).apply w = w ↔ (d.orient w).IsChain fun a s ↦
      ¬ (IsNasalSource IsTrigger c a ∧ c.IsTarget s ∧ s .nasal ≠ some true) := by
  rw [SearchCopy.apply_eq_self_iff_isChain _ (fun _ ↦ trivial) rfl]
  exact List.IsChain.iff fun a s ↦ nasalSpread_emit_eq_self_iff a s

/-- With the cut at the sonorant stops no segment is a target, and the harmony changes no
word. -/
theorem nasalSpread_sonorantStop_apply (w : List Segment) :
    (nasalSpread IsTrigger .sonorantStop d).apply w = w :=
  (nasalSpread_apply_eq_self_iff w).2 <| List.isChain_iff_forall_rel_of_append_cons_cons.2
    fun _ _ _ _ _ h ↦ lt_irrefl _ (h.2.1.1.trans_lt h.2.1.2)

/-- A nasal harmony changes nothing but nasality. -/
theorem map_restrict_nasalSpread (w : List Segment) :
    ((nasalSpread IsTrigger c d).apply w).map (Segment.restrict {.nasal}ᶜ) =
      w.map (Segment.restrict {.nasal}ᶜ) :=
  SearchCopy.map_apply _ (fun q s ↦ by
    rw [nasalSpread_emit]
    split_ifs
    · exact Segment.restrict_eq_restrict_iff.2 fun _ hg ↦
        Segment.setFeature_apply_of_ne (by rintro rfl; simp at hg) s true
    · rfl) w

/-- A harmony scanning from the right outputs the first segment of a word nasal when it is a
target and the output of the next segment is a nasal trigger or target. -/
theorem nasalSpread_apply_cons (s : Segment) (w : List Segment) :
    (nasalSpread IsTrigger c .right).apply (s :: w) =
      (if c.IsTarget s ∧ ∃ a ∈ ((nasalSpread IsTrigger c .right).apply w).head?,
          IsNasalSource IsTrigger c a then s.setFeature .nasal true else s) ::
        (nasalSpread IsTrigger c .right).apply w := by
  have h : ((nasalSpread IsTrigger c .right).apply w).filter
      ((nasalSpread IsTrigger c .right).tier ·) = (nasalSpread IsTrigger c .right).apply w :=
    List.filter_eq_self.2 fun _ _ ↦ decide_eq_true trivial
  rw [(nasalSpread IsTrigger c .right).apply_cons rfl (fun _ _ _ ↦ Iff.rfl), nasalSpread_emit, h]

end Phonology.Harmony
