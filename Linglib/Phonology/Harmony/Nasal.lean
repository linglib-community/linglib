module

public import Linglib.Phonology.SearchCopy
public import Linglib.Phonology.Segmental.NasalCompatibility

/-!
# Nasal harmony

In a nasal harmony nasality spreads from a trigger through a contiguous string of segments, in
one direction, until a segment that does not undergo it. A harmony is given here by its
triggers, by its targets, the segments nasality spreads through, and by its direction. In the
typology of [walker-2000] the targets are those of a cut `c` on the nasalization hierarchy,
`c.IsTarget`, which separates the classes that undergo from the classes that block.

The harmony is a search-and-copy rule in which every segment is visible. A target searches the
adjacent segment on the side the scan comes from and takes [+nasal] from it when that segment
is nasal and is a trigger or a target; any other segment halts the search.

## Main definitions

* `Phonology.Harmony.IsNasalSource`: the nasal segments that pass nasality on, the nasal
  triggers and the nasal targets.
* `Phonology.Harmony.nasalSpread`: the harmony with given triggers, targets and direction.

## Main results

* `Phonology.Harmony.nasalSpread_apply_eq_self_iff`: a harmony fixes a word exactly when no
  target that is not nasal stands next to a nasal trigger or target on the side nasality comes
  from.
* `Phonology.Harmony.map_restrict_nasalSpread`: a harmony changes nothing but nasality.
* `Phonology.Harmony.nasalSpread_apply_of_forall_not`: a harmony without targets changes no
  word, as with the cut at the sonorant stops.

## Implementation notes

* Spreading is strictly local, as [walker-2000] argues: no segment is skipped, so a segment
  that does not undergo blocks.
* A nasal target passes nasality on whether or not it is a trigger, so the triggers matter only
  outside the targets. A nasal segment that is neither, such as a nasal stop where vowels alone
  trigger, passes nothing on and halts the search. This is a choice made for rules stated with
  a class of triggers: in [walker-2000] every nasal segment spreads, and a nasal stop does not
  block.
* The rule is unidirectional and applies to a whole word. Bidirectional spreading and
  spreading bounded by a morpheme or a syllable are not represented.
* The rule changes nothing but [nasal]. It does not derive the obstruents that surface oral
  inside a nasal span, which [walker-2000] analyses as targets, nor the voiced stops that
  surface as nasal stops there.

## References

* [R. Walker, *Nasalization, Neutral Segments, and Opacity Effects* (2000)][walker-2000]
* [S. Rose and R. Walker, *Harmony systems* (2011)][rose-walker-2011]
* [A. Nevins, *Locality in Vowel Harmony* (2010)][nevins-2010]
-/

@[expose] public section

namespace Phonology.Harmony

variable (IsTrigger IsTarget : Segment → Prop) [DecidablePred IsTrigger] [DecidablePred IsTarget]
  (d : Edge)

/-- A nasal segment that passes nasality on in a harmony with the given triggers and targets: a
nasal trigger, or a nasal target. -/
def IsNasalSource (s : Segment) : Prop := s .nasal = true ∧ (IsTrigger s ∨ IsTarget s)

instance : DecidablePred (IsNasalSource IsTrigger IsTarget) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- A target passes nasality on exactly when it is nasal, whatever the triggers. -/
theorem isNasalSource_iff_of_isTarget {IsTrigger IsTarget : Segment → Prop} {s : Segment}
    (h : IsTarget s) : IsNasalSource IsTrigger IsTarget s ↔ s .nasal = true :=
  and_iff_left (.inr h)

/-- The nasal harmony with triggers `IsTrigger` and targets `IsTarget`, scanning from the edge
`d`: a target takes [+nasal] from an adjacent nasal trigger or target on that side. -/
def nasalSpread : SearchCopy Segment where
  tier _ := True
  IsTarget := IsTarget
  IsSource a _ := IsNasalSource IsTrigger IsTarget a
  value s := s .nasal
  write v s := s.setFeature .nasal v
  value_write v s _ := Segment.setFeature_apply_self s .nasal v
  write_value _ _ _ h := Segment.setFeature_eq_self_iff.2 h
  direction := d

variable {IsTrigger IsTarget d}

theorem nasalSpread_emit (q : Option Segment) (s : Segment) :
    (nasalSpread IsTrigger IsTarget d).emit q s =
      if IsTarget s ∧ ∃ a ∈ q, IsNasalSource IsTrigger IsTarget a then s.setFeature .nasal true
      else s := by
  cases q with
  | none => simp [SearchCopy.emit, SearchCopy.copied, nasalSpread]
  | some a =>
    by_cases ha : IsNasalSource IsTrigger IsTarget a
    · simp [SearchCopy.emit, SearchCopy.copied, nasalSpread, ha, ha.1]
    · simp [SearchCopy.emit, SearchCopy.copied, nasalSpread, ha]

/-- A target `s` stands unchanged after `a` exactly when it is nasal or `a` passes no nasality
on. -/
theorem nasalSpread_emit_eq_self_iff (a s : Segment) :
    (nasalSpread IsTrigger IsTarget d).emit (some a) s = s ↔
      ¬ (IsNasalSource IsTrigger IsTarget a ∧ IsTarget s ∧ s .nasal ≠ some true) := by
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
    (nasalSpread IsTrigger IsTarget d).apply w = w ↔ (d.orient w).IsChain fun a s ↦
      ¬ (IsNasalSource IsTrigger IsTarget a ∧ IsTarget s ∧ s .nasal ≠ some true) := by
  rw [SearchCopy.apply_eq_self_iff_isChain _ (fun _ ↦ trivial) rfl]
  exact List.IsChain.iff fun a s ↦ nasalSpread_emit_eq_self_iff a s

/-- A harmony without targets changes no word. -/
theorem nasalSpread_apply_of_forall_not (h : ∀ s, ¬ IsTarget s) (w : List Segment) :
    (nasalSpread IsTrigger IsTarget d).apply w = w :=
  (nasalSpread_apply_eq_self_iff w).2 <| List.isChain_iff_forall_rel_of_append_cons_cons.2
    fun _ _ _ _ _ hs ↦ h _ hs.2.1

/-- With the cut at the sonorant stops a harmony changes no word. -/
theorem nasalSpread_sonorantStop_apply (w : List Segment) :
    (nasalSpread IsTrigger NasalCompatibility.sonorantStop.IsTarget d).apply w = w :=
  nasalSpread_apply_of_forall_not (fun _ ↦ NasalCompatibility.not_isTarget_sonorantStop) w

/-- A nasal harmony changes nothing but nasality. -/
theorem map_restrict_nasalSpread (w : List Segment) :
    ((nasalSpread IsTrigger IsTarget d).apply w).map (Segment.restrict {.nasal}ᶜ) =
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
    (nasalSpread IsTrigger IsTarget .right).apply (s :: w) =
      (if IsTarget s ∧ ∃ a ∈ ((nasalSpread IsTrigger IsTarget .right).apply w).head?,
          IsNasalSource IsTrigger IsTarget a then s.setFeature .nasal true else s) ::
        (nasalSpread IsTrigger IsTarget .right).apply w := by
  set r := nasalSpread IsTrigger IsTarget .right
  have h : (r.apply w).filter (r.tier ·) = r.apply w :=
    List.filter_eq_self.2 fun _ _ ↦ decide_eq_true trivial
  rw [r.apply_cons rfl (fun _ _ _ ↦ Iff.rfl), nasalSpread_emit, h]

end Phonology.Harmony
