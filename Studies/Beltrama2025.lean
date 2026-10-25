module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Linglib.Semantics.Degree.Adjective

/-!
# Beltrama (2025): Evaluation, thresholds, and practical commitments

Mildly positive adjectives, *decent*, *acceptable*, *adequate*, are context-sensitive and
gradable like *good* yet crisp, *barely*-friendly and without a zone of indifference like
the absolute adjectives, and they resist *slightly*, the diagnostic of a minimum standard
([beltrama-2025], against [kennedy-mcnally-2005]'s absolute class). Their positive form
takes a necessity standard: the greatest degree of value the object has in every
circumstantially accessible world in which it is pursued, the standard that *enough*
supplies with an overt purpose ([nadathur-2023]) and a functional standard in
[kagan-alexeyenko-2011]'s sense, so that [kennedy-2007]'s standard-fixing function must
range over functional standards beside the endpoints and comparison-class norms of
Interpretive Economy. The middling inference of *decent* is a scalar implicature against
*good*, and the missing zone of indifference follows from the standard's existential
force: an object is acceptable only if some accessible circumstance pursues it, and
unacceptable only if none does.

## Implementation notes

The necessity standard is the greatest lower bound of the object's values over the pursued
accessible worlds, mathlib's `IsGLB`, which is the paper's maximum of the lower bounds; the
value scale is any partial order, open above where a theorem needs it. Existential force is
derived under the assumption that circumstantial alternatives leave the object's value
fixed. The behaviour with *barely*, emphasis in downward-entailing contexts and *-able*
derivation are recorded in the example rows only.

## References

* [beltrama-2025]
* [kennedy-2007]
* [kennedy-mcnally-2005]
* [nadathur-2023]
* [kagan-alexeyenko-2011]
-/

@[expose] public section

namespace Beltrama2025

variable {W E D : Type*}

section Standard

variable [PartialOrder D] (Acc : W → Set W) (pursued : E → W → Prop) (μ : E → W → D) (x : E)
  (w : W) (s : D)

/-! ### The necessity standard -/

/-- The values an object takes in the accessible worlds where it is pursued. -/
def pursuedValues : Set D := μ x '' {w' | w' ∈ Acc w ∧ pursued x w'}

/-- (64): the necessity standard is the greatest degree the object's value reaches in every
accessible world where it is pursued, the greatest lower bound of `pursuedValues`. -/
def IsNecessityStandard : Prop := IsGLB (pursuedValues Acc pursued μ x w) s

/-- (65): the positive form at a standard. -/
def Pos : Prop := s ≤ μ x w

/-- *acceptable*: the object meets a necessity standard. -/
def Acceptable : Prop := ∃ s, IsNecessityStandard Acc pursued μ x w s ∧ Pos μ x w s

/-- *unacceptable*, the negated form's universal force: no accessible world pursues the
object. -/
def Unacceptable : Prop := ∀ w' ∈ Acc w, ¬ pursued x w'

/-- The middling reading: decent, at the standard `s`, and not good, at the standard `t`. -/
def Middling (t : D) : Prop := Pos μ x w s ∧ ¬ Pos μ x w t

variable {Acc pursued μ x w s}

theorem pos_of_pursued (hs : IsNecessityStandard Acc pursued μ x w s) (hw : w ∈ Acc w)
    (hp : pursued x w) : Pos μ x w s :=
  hs.1 ⟨w, ⟨hw, hp⟩, rfl⟩

theorem exists_pursued [NoMaxOrder D] (hs : IsNecessityStandard Acc pursued μ x w s) :
    ∃ w' ∈ Acc w, pursued x w' := by
  by_contra h
  have : pursuedValues Acc pursued μ x w = ∅ := by
    rw [pursuedValues, Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
    exact fun w' hw' ↦ h ⟨w', hw'.1, hw'.2⟩
  rw [IsNecessityStandard, this, isGLB_empty_iff] at hs
  obtain ⟨t, ht⟩ := exists_gt s
  exact lt_irrefl s (ht.trans_le (hs t))

theorem standard_antitone {Acc' : W → Set W} {s' : D}
    (hs : IsNecessityStandard Acc pursued μ x w s) (hs' : IsNecessityStandard Acc' pursued μ x w s')
    (h : Acc w ⊆ Acc' w) : s' ≤ s :=
  hs.2 fun _ hv ↦ by
    obtain ⟨w', hw', rfl⟩ := hv
    exact hs'.1 ⟨w', ⟨h hw'.1, hw'.2⟩, rfl⟩

/-! ### Force and the zone of indifference -/

variable (x w) in
theorem acceptable_iff [NoMaxOrder D] (hμ : ∀ w' ∈ Acc w, μ x w' = μ x w) :
    Acceptable Acc pursued μ x w ↔ ∃ w' ∈ Acc w, pursued x w' := by
  refine ⟨fun ⟨_, hs, _⟩ ↦ exists_pursued hs, fun ⟨w', hw', hp⟩ ↦ ⟨μ x w, ?_, le_rfl⟩⟩
  have h : pursuedValues Acc pursued μ x w = {μ x w} :=
    Set.eq_singleton_iff_unique_mem.2
      ⟨⟨w', ⟨hw', hp⟩, hμ w' hw'⟩, fun _ ⟨w'', hw'', e⟩ ↦ e ▸ hμ w'' hw''.1⟩
  rw [IsNecessityStandard, h]
  exact isGLB_singleton

variable (x w) in
theorem neither_defective [NoMaxOrder D] (hμ : ∀ w' ∈ Acc w, μ x w' = μ x w) :
    ¬ (¬ Acceptable Acc pursued μ x w ∧ ¬ Unacceptable Acc pursued x w) := by
  rw [acceptable_iff x w hμ]
  simp [Unacceptable]

theorem good_gap (tp : Degree.ThresholdPair D) (h : tp.neg ≤ tp.pos) : tp.gap.Nonempty :=
  tp.gap_nonempty_iff.2 h

/-! ### Against the minimum-standard analysis -/

theorem comparative_entails_minStandard [OrderBot D] {y : E} (h : μ y w < μ x w) :
    x ∈ (μ · w) ⁻¹' Set.Ioi ⊥ :=
  bot_le.trans_lt h

/-- Under a necessity standard it does not ((51b)): an object can outvalue another and fall
short of the standard. -/
theorem comparative_not_entails_pos {y : E} (h : μ y w < μ x w) (hs : μ x w < s) :
    μ y w < μ x w ∧ ¬ Pos μ x w s :=
  ⟨h, not_le_of_gt hs⟩

theorem bot_lt_standard [OrderBot D] (hs : IsLeast (pursuedValues Acc pursued μ x w) s)
    (h : ∀ v ∈ pursuedValues Acc pursued μ x w, ⊥ < v) : ⊥ < s :=
  h s hs.1

/-! ### The middling inference -/

theorem pos_of_pos_of_le {t : D} (h : s ≤ t) (ht : Pos μ x w t) : Pos μ x w s := h.trans ht

theorem middling_cancelable {t : D} (h : s ≤ t) (ht : Pos μ x w t) :
    Pos μ x w s ∧ Pos μ x w t :=
  ⟨pos_of_pos_of_le h ht, ht⟩

end Standard

section Linear

variable [LinearOrder D] {μ : E → W → D} {x : E} {w : W} {s : D}

theorem not_pos_iff : ¬ Pos μ x w s ↔ μ x w < s := not_le

end Linear

section Complete

variable [CompleteLattice D] {Acc : W → Set W} {pursued : E → W → Prop} {μ : E → W → D}
  {x : E} {w : W} {s : D}

/-- On a complete scale the standard (64) is the maximum of the degrees below the object's value in
every pursued accessible world. -/
theorem isNecessityStandard_iff :
    IsNecessityStandard Acc pursued μ x w s ↔
      s = sSup {d | ∀ w' ∈ Acc w, pursued x w' → d ≤ μ x w'} := by
  have h : {d | ∀ w' ∈ Acc w, pursued x w' → d ≤ μ x w'} =
      lowerBounds (pursuedValues Acc pursued μ x w) := by
    ext d
    constructor
    · rintro hd v ⟨w', hw', rfl⟩
      exact hd w' hw'.1 hw'.2
    · exact fun hd w' hw' hp ↦ hd ⟨w', ⟨hw', hp⟩, rfl⟩
  rw [h, sSup_lowerBounds_eq_sInf, IsNecessityStandard]
  exact ⟨fun hs ↦ hs.sInf_eq.symm, fun hs ↦ hs ▸ isGLB_sInf _⟩

end Complete

end Beltrama2025
