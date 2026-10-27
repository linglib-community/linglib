module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Semantics.Tense.RunTimes

/-!
# Anscombe 1964: before and after

*Before* and *after* are not converses: *the Parthenon was there after St. Peter's was* and
*St. Peter's was there after the Parthenon was* are compatible, while the corresponding
*before* claims are not (§I). *p before q* is *p and not q, and then q*; it is asymmetric and
transitive once *repetition* — *p, then not p, then p* — is excluded, whereas *p after q*,
*q and then p*, is neither, and *p before q* entails *q after p* but not conversely (§II).
Quantifying over times renders *p before q* as *a time of p before every time of q* (§IV),
which is right for *before ever* rather than *before* (§V): the two agree exactly when *q*
does not repeat. For instantaneous events *before* and *after* are genuine converses
(§VIII); otherwise a beginning or an ending is always involved (§IX–§X).

A clause's present-tense proposition holds at the times of its `timeTrace`, so excluding
repetition is `Set.OrdConnected` and an instantaneous event has a singleton trace.

## References

* [anscombe-1964]
-/

@[expose] public section

namespace Anscombe1964

open Tense NonemptyInterval

variable {T : Type*} [LinearOrder T] {A B C : Set (NonemptyInterval T)}

/-! ### Definitions -/

/-- *p before q* holds when *p and not q, and then q* (§II). -/
def Anscombe.before (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A \ timeTrace B, ∃ t' ∈ timeTrace B, t < t'

/-- *p after q* holds when *q, and then p*, a time of *p* after a time of *q* (§II, §IV). -/
def Anscombe.after (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' < t

/-- A clause repeats when *p, and then not p, and then p* (§II). -/
def Repetition (A : Set (NonemptyInterval T)) : Prop :=
  ∃ t₁ ∈ timeTrace A, ∃ t₂ ∉ timeTrace A, ∃ t₃ ∈ timeTrace A, t₁ < t₂ ∧ t₂ < t₃

/-- A clause reports an instantaneous event when it holds at a single time (§VIII). -/
def Instantaneous (A : Set (NonemptyInterval T)) : Prop := ∃ t, timeTrace A = {t}

/-! ### The logical properties (§II) -/

theorem not_repetition_iff_ordConnected : ¬ Repetition A ↔ (timeTrace A).OrdConnected :=
  ⟨fun h => ⟨fun _ hx _ hy _ hz => by_contra fun hz' => h ⟨_, hx, _, hz', _, hy,
      lt_of_le_of_ne hz.1 fun e => hz' (e ▸ hx), lt_of_le_of_ne hz.2 fun e => hz' (e ▸ hy)⟩⟩,
    fun h ⟨_, h₁, _, h₂, _, h₃, h₁₂, h₂₃⟩ => h₂ (h.out h₁ h₃ ⟨h₁₂.le, h₂₃.le⟩)⟩

theorem before_asymm (hA : (timeTrace A).OrdConnected) (hB : (timeTrace B).OrdConnected) :
    Anscombe.before A B → ¬ Anscombe.before B A := by
  rintro ⟨a, ⟨ha, haB⟩, b, hb, hab⟩ ⟨b', ⟨hb', hb'A⟩, a', ha', hb'a'⟩
  have hab' : a < b' := lt_of_not_ge fun h => haB (hB.out hb' hb ⟨h, hab.le⟩)
  exact hb'A (hA.out ha ha' ⟨hab'.le, hb'a'.le⟩)

theorem before_trans (hB : (timeTrace B).OrdConnected) (hC : (timeTrace C).OrdConnected) :
    Anscombe.before A B → Anscombe.before B C → Anscombe.before A C := by
  rintro ⟨a, ⟨ha, haB⟩, b, hb, hab⟩ ⟨b', ⟨hb', hb'C⟩, c, hc, hb'c⟩
  have hab' : a < b' := lt_of_not_ge fun h => haB (hB.out hb' hb ⟨h, hab.le⟩)
  exact ⟨a, ⟨ha, fun haC => hb'C (hC.out haC hc ⟨hab'.le, hb'c.le⟩)⟩, c, hc, hab'.trans hb'c⟩

theorem before_not_asymm :
    ∃ A B : Set (NonemptyInterval ℤ), Anscombe.before A B ∧ Anscombe.before B A :=
  ⟨{pure 0, pure 2}, {pure 1, pure 3},
    ⟨0, by simp, 1, by simp, by decide⟩, ⟨1, by simp, 2, by simp, by decide⟩⟩

theorem after_of_before : Anscombe.before A B → Anscombe.after B A :=
  fun ⟨a, ⟨ha, _⟩, b, hb, hab⟩ => ⟨b, hb, a, ha, hab⟩

theorem after_not_asymm :
    ∃ A B : Set (NonemptyInterval ℤ), Anscombe.after A B ∧ Anscombe.after B A :=
  ⟨Set.Iic ⟨(0, 10), by decide⟩, Set.Iic ⟨(5, 15), by decide⟩,
    ⟨10, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩,
      5, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, by decide⟩,
    ⟨15, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩,
      0, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, by decide⟩⟩

theorem after_self_iff : Anscombe.after A A ↔ (timeTrace A).Nontrivial :=
  ⟨fun ⟨t, ht, t', ht', h⟩ => ⟨t', ht', t, ht, h.ne⟩, fun h =>
    let ⟨x, hx, y, hy, hxy⟩ := Set.nontrivial_iff_exists_lt.1 h; ⟨y, hy, x, hx, hxy⟩⟩

theorem not_after_self_of_instantaneous (hA : Instantaneous A) : ¬ Anscombe.after A A :=
  fun h => let ⟨_, ht⟩ := hA
    Set.not_nontrivial_iff.2 (ht ▸ Set.subsingleton_singleton) (after_self_iff.1 h)

theorem after_not_trans :
    ∃ A B : Set (NonemptyInterval ℤ),
      Anscombe.after A B ∧ Anscombe.after B A ∧ ¬ Anscombe.after A A :=
  ⟨{pure 5}, Set.Iic ⟨(0, 10), by decide⟩,
    ⟨5, by simp, 0, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, by decide⟩,
    ⟨10, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, 5, by simp, by decide⟩,
    not_after_self_of_instantaneous ⟨5, by simp⟩⟩

/-! ### Quantification over times (§IV–§V) -/

theorem before_of_beforeEver (hB : (timeTrace B).Nonempty) :
    Tense.beforeEver A B → Anscombe.before A B :=
  fun ⟨a, ha, h⟩ => let ⟨b, hb⟩ := hB
    ⟨a, ⟨ha, fun haB => lt_irrefl a (h a haB)⟩, b, hb, h b hb⟩

theorem before_iff_beforeEver (hB : (timeTrace B).OrdConnected) :
    Anscombe.before A B ↔ Tense.beforeEver A B ∧ (timeTrace B).Nonempty :=
  ⟨fun ⟨a, ⟨ha, haB⟩, b, hb, hab⟩ =>
    ⟨⟨a, ha, fun _ hb' => lt_of_not_ge fun h => haB (hB.out hb' hb ⟨h, hab.le⟩)⟩, b, hb⟩,
    fun ⟨h, hne⟩ => before_of_beforeEver hne h⟩

theorem before_not_beforeEver :
    ∃ A B : Set (NonemptyInterval ℤ), Anscombe.before A B ∧ ¬ Tense.beforeEver A B :=
  ⟨{pure 5}, {pure 1, pure 9}, ⟨5, by simp, 9, by simp, by decide⟩,
    fun ⟨t, ht, h⟩ => absurd (h 1 (by simp)) (by simp at ht; subst ht; decide)⟩

/-! ### Instantaneous events (§VI–§VIII) -/

theorem after_iff_before_of_instantaneous (hA : Instantaneous A) :
    Anscombe.after A B ↔ Anscombe.before B A := by
  obtain ⟨a, ha⟩ := hA
  simp only [Anscombe.after, Anscombe.before, ha, Set.mem_singleton_iff, exists_eq_left,
    Set.mem_sdiff]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, ⟨hb, h.ne⟩, h⟩, fun ⟨b, ⟨hb, _⟩, h⟩ => ⟨b, hb, h⟩⟩

theorem not_after_of_before_of_instantaneous (hA : Instantaneous A)
    (hB : (timeTrace B).OrdConnected) (h : Anscombe.before A B) : ¬ Anscombe.after A B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨a', ⟨ha', ha'B⟩, b', hb', ha'b'⟩ := h
  rintro ⟨t, ht, b, hb, hbt⟩
  rw [ha, Set.mem_singleton_iff] at ht ha'
  subst ht ha'
  exact ha'B (hB.out hb hb' ⟨hbt.le, ha'b'.le⟩)

theorem after_and_before_of_extended :
    ∃ A B : Set (NonemptyInterval ℤ), Instantaneous B ∧ Anscombe.before A B ∧ Anscombe.after A B :=
  ⟨Set.Iic ⟨(1, 7), by decide⟩, {pure 4}, ⟨4, by simp⟩,
    ⟨1, ⟨mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, by simp⟩,
      4, by simp, by decide⟩,
    ⟨7, mem_timeTrace_Iic.2 ⟨by decide, by decide⟩, 4, by simp, by decide⟩⟩

/-! ### Beginnings and endings (§IX–§X) -/

theorem nonempty_of_before : Anscombe.before A B → (timeTrace B).Nonempty :=
  fun ⟨_, _, b, hb, _⟩ => ⟨b, hb⟩

theorem before_iff_lt_least {lb : T} (hB : (timeTrace B).OrdConnected)
    (hlb : IsLeast (timeTrace B) lb) : Anscombe.before A B ↔ ∃ t ∈ timeTrace A, t < lb := by
  rw [before_iff_beforeEver hB, beforeEver_iff_of_isLeast hlb, and_iff_left ⟨lb, hlb.1⟩]

-- (3)
theorem after_iff_least_lt {lb : T} (hlb : IsLeast (timeTrace B) lb) :
    Anscombe.after A B ↔ ∃ t ∈ timeTrace A, lb < t :=
  ⟨fun ⟨a, ha, _, ht', h⟩ => ⟨a, ha, (hlb.2 ht').trans_lt h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, lb, hlb.1, h⟩⟩

-- (4), (3)
theorem after_of_greatest_lt {ub : T} (hub : IsGreatest (timeTrace B) ub) :
    (∃ t ∈ timeTrace A, ub < t) → Anscombe.after A B :=
  fun ⟨a, ha, h⟩ => ⟨a, ha, ub, hub.1, h⟩

end Anscombe1964
