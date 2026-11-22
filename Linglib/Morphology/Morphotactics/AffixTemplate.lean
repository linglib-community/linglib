module

public import Linglib.Phonology.Subregular.Precedence
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
positions repeat](##language). Each position may be skipped, so these strings are [closed under
dropping a filler](##isSublistClosed_language) and [regular](##isRegular_language). Order and
repetition are conditions on pairs, so they are also [strictly
2-piecewise](##isStrictlyPiecewise_language). A string of exponents, each tagged with its
position, is licensed when its positions are admitted.

Mathematically a template is a ranking of exponents with ties. `AffixTemplate.Precedes` is the
relation "may stand before" that a template induces, and the admitted strings are those in
which every exponent may stand before every later one (`mem_language_iff_pairwise`,
`Language.pairwise`). Without stacking positions the relation is a strict weak order on
exponents, whose classes of mutually exclusive exponents are the positions
(`isStrictWeakOrder_precedes`); conversely every strict weak order on a finite set of exponents
arises from a template (`exists_template_of_isStrictWeakOrder`).

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

namespace AffixTemplate

variable {Slot : Type*} (t : AffixTemplate Slot)

/-- The positions in linear order, the stem left out. -/
def slots : List Slot := t.prefixSlots ++ t.suffixSlots

/-! ### Order along a scale

A scale of categories is compared with a template through a partial map `cat` from positions to
the scale: a position of no category on the scale is passed over. The scale may be a partial
order, and positions of incomparable categories are then left free. -/

section Scale

variable {α : Type*} [Preorder α] (cat : Slot → Option α)

/-- The suffix positions ascend along `cat` away from the stem: no position stands inside one
that `cat` places strictly lower on the scale. -/
def SuffixesAscend : Prop := (t.suffixSlots.filterMap cat).Pairwise fun x y ↦ ¬ y < x

/-- The prefix positions ascend along `cat` away from the stem. -/
def PrefixesAscend : Prop := (t.prefixSlots.reverse.filterMap cat).Pairwise fun x y ↦ ¬ y < x

instance [DecidableLT α] : Decidable (t.SuffixesAscend cat) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

instance [DecidableLT α] : Decidable (t.PrefixesAscend cat) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

variable {t cat} {v : List Slot}

theorem suffixesAscend_iff_pairwise :
    t.SuffixesAscend cat ↔
      t.suffixSlots.Pairwise fun a b ↦ ∀ x ∈ cat a, ∀ y ∈ cat b, ¬ y < x := by
  simp [SuffixesAscend, List.pairwise_filterMap]

theorem prefixesAscend_iff_pairwise :
    t.PrefixesAscend cat ↔
      t.prefixSlots.Pairwise fun a b ↦ ∀ x ∈ cat a, ∀ y ∈ cat b, ¬ x < y := by
  simp only [PrefixesAscend, List.pairwise_filterMap, List.pairwise_reverse, Option.mem_def]
  exact List.Pairwise.iff fun a b ↦ ⟨fun h x hx y hy ↦ h y hy x hx, fun h y hy x hx ↦ h x hx y hy⟩

/-- A string of suffixes in the template's order ascends along `cat`. -/
theorem SuffixesAscend.pairwise_filterMap (h : t.SuffixesAscend cat)
    (hv : v.Sublist t.suffixSlots) : (v.filterMap cat).Pairwise fun x y ↦ ¬ y < x :=
  h.sublist (hv.filterMap cat)

/-- A string of prefixes in the template's order descends along `cat` towards the stem. -/
theorem PrefixesAscend.pairwise_filterMap (h : t.PrefixesAscend cat)
    (hv : v.Sublist t.prefixSlots) : (v.reverse.filterMap cat).Pairwise fun x y ↦ ¬ y < x :=
  h.sublist (hv.reverse.filterMap cat)

end Scale

section LinearScale

variable {α : Type*} [LinearOrder α] {cat : Slot → Option α} {t}

/-- Along a linear scale, the suffixes ascend when their categories are sorted. -/
theorem suffixesAscend_iff_sortedLE :
    t.SuffixesAscend cat ↔ (t.suffixSlots.filterMap cat).SortedLE := by
  simp [SuffixesAscend, List.sortedLE_iff_pairwise]

theorem prefixesAscend_iff_sortedLE :
    t.PrefixesAscend cat ↔ (t.prefixSlots.reverse.filterMap cat).SortedLE := by
  simp [PrefixesAscend, List.sortedLE_iff_pairwise]

end LinearScale

variable [DecidableEq Slot]

/-- The strings of positions the template admits: those over its positions, in their order, in
which only stacking positions repeat. -/
def language : Language Slot :=
  {v | (v.map t.slots.idxOf).SortedLE ∧ ∀ a ∈ v, a ∈ t.slots ∧ (a ∈ t.stacking ∨ v.count a ≤ 1)}

instance : DecidablePred (· ∈ t.language) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A string of exponents, each tagged with its position, is licensed when its positions are
admitted. -/
def Licensed {E : Slot → Type*} (w : List (Σ σ, E σ)) : Prop := w.map Sigma.fst ∈ t.language

instance {E : Slot → Type*} : DecidablePred (t.Licensed (E := E)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ t.language))

variable {t} {v : List Slot}

open List

/-- Dropping a filler keeps a string admitted. -/
theorem isSublistClosed_language : t.language.IsSublistClosed := fun _ _ hvw ⟨hs, h⟩ ↦
  ⟨(hs.pairwise.sublist (hvw.map _)).sortedLE, fun a ha ↦
    (h a (hvw.subset ha)).imp_right (Or.imp_right (hvw.count_le a).trans)⟩

theorem isRegular_language [Finite Slot] : t.language.IsRegular :=
  isSublistClosed_language.isRegular

/-- A template is a condition on pairs: a string is admitted when each of its fillers and each
ordered pair of them is. -/
theorem isStrictlyPiecewise_language : t.language.IsStrictlyPiecewise 2 := by
  refine ⟨t.language, Set.ext fun v ↦ ⟨fun h ↦ ?_, fun h s _ hs ↦ isSublistClosed_language hs h⟩⟩
  replace h : ∀ s, s.length ≤ 2 → s <+ v → s ∈ t.language := h
  refine ⟨?_, fun a ha ↦ ⟨(h [a] (by simp) (singleton_sublist.2 ha)).2 a (by simp) |>.1, ?_⟩⟩
  · rw [sortedLE_iff_pairwise, pairwise_map, pairwise_iff_forall_sublist]
    intro a b hab
    simpa [sortedLE_iff_pairwise] using (h [a, b] (by simp) hab).1
  · refine or_iff_not_imp_left.2 fun hs ↦ not_lt.1 fun hc ↦ ?_
    have h2 : replicate 2 a <+ v := replicate_sublist_iff.2 hc
    simpa [hs] using ((h _ (by simp) h2).2 a (by simp)).2

/-- Without stacking positions, a string is admitted exactly when it fills positions at most
once, in order. -/
theorem mem_language_iff_sublist (ht : t.slots.Nodup) (h : t.stacking = ∅) :
    v ∈ t.language ↔ v <+ t.slots := by
  have hle : t.slots.Pairwise (t.slots.idxOf · ≤ t.slots.idxOf ·) :=
    pairwise_iff_getElem.2 fun i j hi hj hij ↦ by
      rw [ht.idxOf_getElem, ht.idxOf_getElem]; exact hij.le
  refine ⟨fun ⟨hs, hv⟩ ↦ ?_, fun hv ↦ ⟨((pairwise_map.2 hle).sublist (hv.map _)).sortedLE,
    fun a ha ↦ ⟨hv.subset ha, .inr ((hv.count_le a).trans (nodup_iff_count_le_one.1 ht a))⟩⟩⟩
  have hnd : v.Nodup := nodup_iff_count_le_one.2 fun a ↦ by
    by_cases ha : a ∈ v
    · simpa [h] using (hv a ha).2
    · simp [count_eq_zero_of_not_mem ha]
  obtain ⟨w, hwv, hw⟩ := subperm_of_subset hnd fun a ha ↦ (hv a ha).1
  refine hwv.eq_of_pairwise (fun a b ha hb hab hba ↦ ?_) (hle.sublist hw)
    (pairwise_map.1 (sortedLE_iff_pairwise.1 hs)) ▸ hw
  exact (idxOf_inj (hw.subset ha)).1 (le_antisymm hab hba)

/-! ### The precedence relation of a template -/

variable (t) in
/-- `a` may stand before `b` in the template: its position comes earlier, or the two are one
stacking position. -/
def Precedes (a b : Slot) : Prop :=
  t.slots.idxOf a < t.slots.idxOf b ∨ a = b ∧ a ∈ t.stacking

instance : DecidableRel t.Precedes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A string is admitted when its positions are the template's and each may stand before every
later one. -/
theorem mem_language_iff_pairwise :
    v ∈ t.language ↔ (∀ a ∈ v, a ∈ t.slots) ∧ v.Pairwise t.Precedes := by
  refine ⟨fun ⟨hs, h⟩ ↦ ⟨fun a ha ↦ (h a ha).1, ?_⟩, fun ⟨hm, hp⟩ ↦ ⟨?_, fun a ha ↦ ⟨hm a ha, ?_⟩⟩⟩
  · refine pairwise_iff_forall_sublist.2 fun {a b} hab ↦ ?_
    have hle := pairwise_iff_forall_sublist.1 (pairwise_map.1 (sortedLE_iff_pairwise.1 hs)) hab
    rcases hle.lt_or_eq with hlt | heq
    · exact .inl hlt
    · have ha : a ∈ v := hab.subset (by simp)
      obtain rfl := (idxOf_inj (h a ha).1).1 heq
      refine .inr ⟨rfl, (h a ha).2.resolve_right fun hc ↦ ?_⟩
      have := hab.count_le a
      simp at this
      omega
  · exact (pairwise_map.2 (hp.imp fun {a b} h ↦
      h.elim le_of_lt fun h ↦ h.1 ▸ le_rfl)).sortedLE
  · refine or_iff_not_imp_left.2 fun hs ↦ not_lt.1 fun hc ↦ ?_
    have h2 : [a, a] <+ v := replicate_sublist_iff.2 hc
    exact (pairwise_iff_forall_sublist.1 hp h2).elim (lt_irrefl _) fun h ↦ hs h.2

/-- The language of a template is the language of its precedence relation, cut down to the
template's positions. -/
theorem language_eq_pairwise_inf :
    t.language = Language.pairwise t.Precedes ⊓ {v | ∀ a ∈ v, a ∈ t.slots} :=
  Set.ext fun _ ↦ mem_language_iff_pairwise.trans and_comm

/-- A string of exponents is licensed when its positions are the template's and each exponent
may stand before every later one. -/
theorem licensed_iff_pairwise {E : Slot → Type*} {w : List (Σ σ, E σ)} :
    t.Licensed w ↔ (∀ x ∈ w, x.1 ∈ t.slots) ∧ w.Pairwise (Sigma.fst ⁻¹'o t.Precedes) := by
  rw [Licensed, mem_language_iff_pairwise, pairwise_map]
  exact and_congr forall_mem_map .rfl

/-- On the exponents of a template without stacking positions, "may stand before" is a strict
weak order: exponents of one position exclude each other, and positions are linearly ordered. -/
theorem isStrictWeakOrder_precedes (h : t.stacking = ∅) (E : Slot → Type*) :
    IsStrictWeakOrder (Σ σ, E σ) (Sigma.fst ⁻¹'o t.Precedes) := by
  have key (a b : Σ σ, E σ) :
      (Sigma.fst ⁻¹'o t.Precedes) a b ↔ t.slots.idxOf a.1 < t.slots.idxOf b.1 := by
    simp [Order.Preimage, Precedes, h]
  exact
    { irrefl := fun a ha ↦ lt_irrefl _ ((key a a).1 ha)
      trans := fun a b c hab hbc ↦ (key a c).2 (((key a b).1 hab).trans ((key b c).1 hbc))
      incomp_trans := fun a b c hab hbc ↦ by simp only [key] at *; omega }

open Classical in
/-- In a strict weak order on a finite type, an element is below another exactly when fewer
elements are below it. -/
private theorem rel_iff_card_lt {F : Type*} [Fintype F] (R : F → F → Prop)
    [IsStrictWeakOrder F R] (a b : F) :
    R a b ↔ (Finset.univ.filter (R · a)).card < (Finset.univ.filter (R · b)).card := by
  have incomp {a b : F} (h : ¬ R a b ∧ ¬ R b a) (c : F) (hc : R c a) : R c b := by
    by_contra hcb
    have hbc : ¬ R b c := fun hbc ↦ h.2 (_root_.trans hbc hc)
    exact (IsStrictWeakOrder.incomp_trans c b a ⟨hcb, hbc⟩ ⟨h.2, h.1⟩).1 hc
  refine ⟨fun hab ↦ Finset.card_lt_card ⟨fun c hc ↦ ?_, fun hsub ↦ ?_⟩, fun hlt ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact _root_.trans hc hab
  · have := hsub (show a ∈ Finset.univ.filter (R · b) by simpa using hab)
    exact irrefl a (by simpa using this)
  · by_contra hab
    by_cases hba : R b a
    · refine absurd (Finset.card_le_card fun c hc ↦ ?_) (not_le.2 hlt)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact _root_.trans hc hba
    · refine absurd (Finset.card_le_card fun c hc ↦ ?_) (not_le.2 hlt)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact incomp ⟨hba, hab⟩ c hc

open Classical in
/-- Every strict weak order on a finite set of exponents is the precedence relation of a
template: its positions are the classes of mutually exclusive exponents. -/
theorem exists_template_of_isStrictWeakOrder {F : Type*} [Finite F] (R : F → F → Prop)
    [IsStrictWeakOrder F R] :
    ∃ (t : AffixTemplate ℕ) (slot : F → ℕ), t.stacking = ∅ ∧
      ∀ w : List F, w.Pairwise R ↔ w.map slot ∈ t.language := by
  have := Fintype.ofFinite F
  let rank (a : F) : ℕ := (Finset.univ.filter (R · a)).card
  have hrank (a : F) : rank a < Fintype.card F + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_univ _)
  refine ⟨{ suffixSlots := List.range (Fintype.card F + 1) }, rank, rfl, fun w ↦ ?_⟩
  have hidx (i : ℕ) (hi : i < Fintype.card F + 1) :
      (List.range (Fintype.card F + 1)).idxOf i = i := by
    have := (List.nodup_range (n := Fintype.card F + 1)).idxOf_getElem i
      (by rw [List.length_range]; exact hi)
    simpa using this
  rw [mem_language_iff_pairwise, pairwise_map]
  refine ⟨fun h ↦ ⟨by simpa [slots] using fun a _ ↦ hrank a, h.imp fun {a b} hab ↦ ?_⟩,
    fun h ↦ h.2.imp fun {a b} hab ↦ ?_⟩
  · exact .inl (by simpa [slots, hidx _ (hrank a), hidx _ (hrank b)] using
      (rel_iff_card_lt R a b).1 hab)
  · refine (rel_iff_card_lt R a b).2 ?_
    simpa [Precedes, slots, hidx _ (hrank a), hidx _ (hrank b)] using hab

/-- Fillers of one position cannot co-occur, unless the position stacks. -/
theorem count_le_one_of_mem_language {a : Slot} (ha : a ∉ t.stacking) (hv : v ∈ t.language) :
    v.count a ≤ 1 := by
  by_cases hav : a ∈ v
  · exact ((hv.2 a hav).2).resolve_left ha
  · simp [count_eq_zero_of_not_mem hav]

/-- In a template of suffixes that ascends along `cat`, every admitted string ascends. -/
theorem SuffixesAscend.pairwise_of_mem_language {α : Type*} [Preorder α] {cat : Slot → Option α}
    (h : t.SuffixesAscend cat) (hp : t.prefixSlots = []) (hv : v ∈ t.language) :
    (v.filterMap cat).Pairwise fun x y ↦ ¬ y < x := by
  have hs : t.slots = t.suffixSlots := by simp [slots, hp]
  have hR := pairwise_iff_getElem.1 (suffixesAscend_iff_pairwise.1 h)
  rw [List.pairwise_filterMap]
  refine (pairwise_map.1 (sortedLE_iff_pairwise.1 hv.1)).imp_of_mem
    fun {a b} ha hb hab x hx y hy ↦ ?_
  have ha' := (hv.2 a ha).1
  have hb' := (hv.2 b hb).1
  rcases hab.eq_or_lt with heq | hlt
  · obtain rfl := (idxOf_inj ha').1 heq
    exact Option.some.inj (hx.symm.trans hy) ▸ lt_irrefl x
  · rw [hs] at ha' hb' hlt
    have := hR _ _ (idxOf_lt_length_of_mem ha') (idxOf_lt_length_of_mem hb') hlt
    simp only [getElem_idxOf] at this
    exact this x hx y hy

end AffixTemplate

end Morphology
