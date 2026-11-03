module

public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Finset.Defs

/-!
# Position-class templates

In templatic morphology the formatives of a word fill a flat string of positions. A formative's
position can be determined by its formal category rather than by its function, and fillers of the
same position cannot co-occur. These properties tend to hold of individual formatives rather than
of the whole string, so a template may contain a position whose fillers stack, as the voice
suffixes of the Turkish verb do.

An `AffixTemplate` lists the positions of a word's prefixes and of its suffixes and marks those
that stack. It admits [the strings over its positions, in their order, in which only stacking
positions repeat](##mem_language_iff). Each position may be skipped, so these strings are [closed
under dropping a filler](##isSublistClosed_language) and [regular](##isRegular_language). Order
and repetition are conditions on pairs, so they are also [strictly
2-piecewise](##isStrictlyPiecewise_language). A string of exponents, each tagged with its
position, is licensed when its positions are admitted.

## Implementation notes

A template can forbid a filler but not require one, the limit of strictly piecewise grammars, so a
dependency between fillers is a further condition in the citing grammar. The template of prosodic
morphology, a CV skeleton, is `Autosegmental.Skeleton`, matched in
`Morphology/Morphotactics/TemplateMatch.lean`.

## References

* [bickel-nichols-2007]
* [aksenova-graf-moradi-2016]
-/

@[expose] public section

namespace Morphology

/-- A word's position-class template, over the positions `Slot`. Slots are tags, not exponents:
the exponents of each position live in the citing grammar. -/
structure AffixTemplate (Slot : Type*) where
  /-- The prefix positions, word-edge inward. -/
  prefixSlots : List Slot := []
  /-- The suffix positions, stem-outward. -/
  suffixSlots : List Slot := []
  /-- The positions whose fillers stack, any number of them in one word. -/
  stacking : Finset Slot := ∅
  /-- A position occurs once. -/
  nodup : (prefixSlots ++ suffixSlots).Nodup := by decide

namespace AffixTemplate

variable {Slot : Type*} (t : AffixTemplate Slot)

/-- The positions in linear order, the stem left out. -/
def slots : List Slot := t.prefixSlots ++ t.suffixSlots

theorem nodup_slots : t.slots.Nodup := t.nodup

variable [DecidableEq Slot]

open RegularExpression in
/-- A position as a regular expression, admitting one filler at most, or any number if it
stacks. -/
def position (a : Slot) : RegularExpression Slot :=
  if a ∈ t.stacking then (char a).star else char a + 1

/-- The positions in order, each as `position`. -/
def toRegularExpression : RegularExpression Slot := t.slots.foldr (t.position · * ·) 1

/-- The strings of positions the template admits. -/
def language : Language Slot := t.toRegularExpression.matches'

instance : DecidablePred (· ∈ t.language) :=
  inferInstanceAs (DecidablePred (· ∈ t.toRegularExpression.matches'))

/-- A string of exponents, each tagged with its position, is licensed when its positions are
admitted. -/
def Licensed {E : Slot → Type*} (w : List (Σ σ, E σ)) : Prop := w.map Sigma.fst ∈ t.language

instance {E : Slot → Type*} : DecidablePred (t.Licensed (E := E)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ t.language))

variable {t} {v : List Slot}

open List RegularExpression

private theorem mem_position_iff {a : Slot} :
    v ∈ (t.position a).matches' ↔ ∃ n, (a ∈ t.stacking ∨ n ≤ 1) ∧ v = replicate n a := by
  unfold position
  split_ifs with h
  · simp only [matches'_star, matches'_char, h, true_or, true_and]
    refine ⟨fun hv ↦ ?_, ?_⟩
    · obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hv
      have hS' : S = replicate S.length [a] := eq_replicate_length.2 hS
      exact ⟨S.length, by rw [hS']; simp⟩
    · rintro ⟨n, rfl⟩
      exact Language.mem_kstar.2 ⟨replicate n [a], by simp, fun y hy ↦ eq_of_mem_replicate hy⟩
  · simp only [matches'_add, matches'_char, matches'_epsilon, Language.mem_add, Language.mem_one,
      h, false_or]
    refine ⟨?_, ?_⟩
    · rintro (rfl | rfl)
      exacts [⟨1, le_rfl, rfl⟩, ⟨0, Nat.zero_le _, rfl⟩]
    · rintro ⟨_ | _ | n, hn, rfl⟩
      exacts [.inr rfl, .inl rfl, by omega]

/-- The strings of the positions `l`. -/
private abbrev stringsOf (t : AffixTemplate Slot) (l : List Slot) : Language Slot :=
  (l.foldr (t.position · * ·) 1).matches'

private theorem mem_stringsOf_cons {a : Slot} {l : List Slot} :
    v ∈ stringsOf t (a :: l) ↔
      ∃ n, (a ∈ t.stacking ∨ n ≤ 1) ∧ ∃ y ∈ stringsOf t l, v = replicate n a ++ y := by
  simp only [stringsOf, foldr_cons, matches'_mul, Language.mem_mul, mem_position_iff]
  exact ⟨fun ⟨_, ⟨n, hn, e⟩, y, hy, h⟩ ↦ ⟨n, hn, y, hy, by rw [← h, e]⟩,
    fun ⟨n, hn, y, hy, e⟩ ↦ ⟨_, ⟨n, hn, rfl⟩, y, hy, e.symm⟩⟩

private theorem stringsOf_sound {r : Slot → Slot → Prop} (hr : ∀ a, r a a) {l : List Slot}
    (hl : l.Pairwise r) (hn : l.Nodup) (hv : v ∈ stringsOf t l) :
    v ⊆ l ∧ v.Pairwise r ∧ ∀ a ∉ t.stacking, v.count a ≤ 1 := by
  induction l generalizing v with
  | nil =>
    obtain rfl : v = [] := (Language.mem_one _).1 hv
    simp
  | cons a l ih =>
    obtain ⟨hal, hl⟩ := pairwise_cons.1 hl
    obtain ⟨han, hn⟩ := nodup_cons.1 hn
    obtain ⟨n, hna, y, hy, rfl⟩ := mem_stringsOf_cons.1 hv
    obtain ⟨hsub, hp, hc⟩ := ih hl hn hy
    refine ⟨fun x hx ↦ (mem_append.1 hx).elim (fun h ↦ eq_of_mem_replicate h ▸ mem_cons_self)
      fun h ↦ mem_cons_of_mem _ (hsub h), pairwise_append.2 ⟨pairwise_replicate.2 (.inr (hr a)), hp,
      fun x hx b hb ↦ eq_of_mem_replicate hx ▸ hal b (hsub hb)⟩, fun b hb ↦ ?_⟩
    rw [count_append, count_replicate]
    by_cases hab : a = b
    · subst hab
      simpa [count_eq_zero_of_not_mem fun h ↦ han (hsub h)] using hna.resolve_left hb
    · simpa [hab] using hc b hb

private theorem stringsOf_complete {r : Slot → Slot → Prop} {l : List Slot}
    (hl : l.Pairwise fun a b ↦ ¬ r b a) (hsub : v ⊆ l) (hv : v.Pairwise r)
    (hc : ∀ a ∉ t.stacking, v.count a ≤ 1) : v ∈ stringsOf t l := by
  induction l generalizing v with
  | nil =>
    obtain rfl : v = [] := subset_nil.1 hsub
    exact Language.nil_mem_one
  | cons a l ihl =>
    obtain ⟨hal, hl⟩ := pairwise_cons.1 hl
    induction v with
    | nil =>
      exact mem_stringsOf_cons.2 ⟨0, .inr (Nat.zero_le _), [], ihl hl (by simp) (by simp) (by simp),
        rfl⟩
    | cons x v ihv =>
      obtain ⟨hxv, hv'⟩ := pairwise_cons.1 hv
      by_cases hxa : x = a
      · subst hxa
        obtain ⟨n, -, y, hy, e⟩ := mem_stringsOf_cons.1 (ihv
          (fun b hb ↦ hsub (mem_cons_of_mem _ hb)) hv'
          fun b hb ↦ (count_le_count_cons ..).trans (hc b hb))
        refine mem_stringsOf_cons.2 ⟨n + 1, ?_, y, hy, by rw [e, replicate_succ, cons_append]⟩
        refine or_iff_not_imp_left.2 fun hs ↦ ?_
        have := hc x hs
        rw [count_cons_self, e, count_append, count_replicate_self] at this
        omega
      · have hxl : x ∈ l := (mem_cons.1 (hsub mem_cons_self)).resolve_left hxa
        have hav : a ∉ x :: v := by
          rintro (_ | ⟨_, h⟩)
          exacts [hxa rfl, hal x hxl (hxv a h)]
        exact mem_stringsOf_cons.2 ⟨0, .inr (Nat.zero_le _), x :: v, ihl hl (fun b hb ↦
          (mem_cons.1 (hsub hb)).resolve_left fun e ↦ hav (e ▸ hb)) hv hc, rfl⟩

private theorem sublist_of_mem_stringsOf (h : t.stacking = ∅) {l : List Slot}
    (hv : v ∈ stringsOf t l) : v <+ l := by
  induction l generalizing v with
  | nil => exact (Language.mem_one _).1 hv ▸ .refl _
  | cons a l ih =>
    obtain ⟨_ | _ | n, hn, y, hy, rfl⟩ := mem_stringsOf_cons.1 hv
    · exact (ih hy).cons a
    · exact (ih hy).cons_cons a
    · simp [h] at hn

private theorem pairwise_idxOf_lt (t : AffixTemplate Slot) :
    t.slots.Pairwise (t.slots.idxOf · < t.slots.idxOf ·) :=
  pairwise_iff_getElem.2 fun i j hi hj hij ↦ by
    rwa [t.nodup_slots.idxOf_getElem, t.nodup_slots.idxOf_getElem]

/-- A template admits exactly the strings over its positions, in their order, in which only
stacking positions repeat. -/
theorem mem_language_iff :
    v ∈ t.language ↔ v ⊆ t.slots ∧ (v.map t.slots.idxOf).SortedLE ∧
      ∀ a ∉ t.stacking, v.count a ≤ 1 := by
  rw [sortedLE_iff_pairwise, pairwise_map]
  exact ⟨stringsOf_sound (r := (t.slots.idxOf · ≤ t.slots.idxOf ·)) (fun _ ↦ le_rfl)
      (t.pairwise_idxOf_lt.imp le_of_lt) t.nodup_slots,
    fun ⟨hsub, hv, hc⟩ ↦ stringsOf_complete (t.pairwise_idxOf_lt.imp not_le.2) hsub hv hc⟩

/-- Dropping a filler keeps a string admitted. -/
theorem isSublistClosed_language : t.language.IsSublistClosed := fun v w hvw hw ↦ by
  obtain ⟨hsub, hs, hc⟩ := mem_language_iff.1 hw
  exact mem_language_iff.2 ⟨fun _ hx ↦ hsub (hvw.subset hx),
    (hs.pairwise.sublist (hvw.map _)).sortedLE, fun a ha ↦ (hvw.count_le a).trans (hc a ha)⟩

theorem isRegular_language [Finite Slot] : t.language.IsRegular :=
  isSublistClosed_language.isRegular

/-- A template is a condition on pairs: a string is admitted when each of its fillers and each
ordered pair of them is. -/
theorem isStrictlyPiecewise_language : t.language.IsStrictlyPiecewise 2 := by
  refine ⟨t.language, Set.ext fun v ↦ ⟨fun h ↦ ?_, fun h s _ hs ↦ isSublistClosed_language hs h⟩⟩
  replace h : ∀ s, s.length ≤ 2 → s <+ v → s ∈ t.language := h
  refine mem_language_iff.2 ⟨fun a ha ↦ ?_, ?_, fun a ha ↦ ?_⟩
  · exact (mem_language_iff.1 (h [a] (by simp) (singleton_sublist.2 ha))).1 mem_cons_self
  · rw [sortedLE_iff_pairwise, pairwise_map, pairwise_iff_forall_sublist]
    intro a b hab
    simpa [sortedLE_iff_pairwise] using (mem_language_iff.1 (h [a, b] (by simp) hab)).2.1
  · by_contra hc
    have h2 : replicate 2 a <+ v := replicate_sublist_iff.2 (by omega)
    simpa using (mem_language_iff.1 (h _ (by simp) h2)).2.2 a ha

theorem mem_language_of_sublist (h : v <+ t.slots) : v ∈ t.language :=
  mem_language_iff.2 ⟨h.subset,
    ((pairwise_map.2 (t.pairwise_idxOf_lt.imp le_of_lt)).sublist (h.map _)).sortedLE,
    fun a _ ↦ (h.count_le a).trans (nodup_iff_count_le_one.1 t.nodup_slots a)⟩

/-- Without stacking positions, a string is admitted exactly when it fills positions at most
once, in order. -/
theorem mem_language_iff_sublist (h : t.stacking = ∅) : v ∈ t.language ↔ v <+ t.slots :=
  ⟨sublist_of_mem_stringsOf h, mem_language_of_sublist⟩

end AffixTemplate

end Morphology
