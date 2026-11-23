module

public import Linglib.Morphology.Morphotactics.Template.Basic

/-!
# Templates ascending along a scale

A scale of categories is compared with a template through a partial map `cat` from positions to
the scale: a position of no category on the scale is passed over. The suffixes ascend along
`cat` away from the stem, `Template.SuffixesAscend`, when no position stands inside one
that `cat` places strictly lower, and likewise the prefixes, `Template.PrefixesAscend`. The
scale may be a partial order, and positions of incomparable categories are then left free.

In a template of suffixes that ascends, every admitted string ascends
(`SuffixesAscend.pairwise_of_mem_language`).

## References

* [bickel-nichols-2007]
-/

@[expose] public section

namespace Morphology.Morphotactics

namespace Template

variable {Slot : Type*} (t : Template Slot)

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

open List

variable [DecidableEq Slot] {t} {v : List Slot}

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
end Template

end Morphology.Morphotactics
