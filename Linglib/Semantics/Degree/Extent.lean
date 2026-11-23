module

public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.UpperLower.Basic

/-!
# Extents

An extent on a scale `D` is a set of degrees closed in one direction: a positive extent is a
lower set and a negative extent an upper set. Since the negative polarity acts on sets by
complement and the complement of an upper set is a lower set, we define `Polarity.IsExtent p s`
as `IsLowerSet (p • s)`. An object measuring `a` has the positive extent `Set.Iic a`; its negative
extent is `Set.Ici a` where the measure is included and `Polarity.negative • Set.Iic a`, that is
`Set.Ioi a`, where the negative extent is the complement of the positive one.

On a linear scale a nonempty extent included in an extent other than the whole scale has the
polarity of that extent, `Polarity.IsExtent.polarity_eq`. A positive and a negative extent are
therefore never properly included in one another, apart from the degenerate cases.

## References

* [kennedy-1999]
* [kennedy-2001]
* [heim-2006]
-/

@[expose] public section

namespace Polarity

variable {D : Type*} {p q : Polarity} {s t : Set D} {a b : D}

section Preorder

variable [Preorder D]

/-- A set of degrees is an extent of polarity `p` when it is a lower set for the positive
polarity and an upper set for the negative one. -/
def IsExtent (p : Polarity) (s : Set D) : Prop := IsLowerSet (p • s)

theorem isExtent_positive : IsExtent .positive s ↔ IsLowerSet s := .rfl

theorem isExtent_negative : IsExtent .negative s ↔ IsUpperSet s := isLowerSet_compl

theorem isExtent_Iic (a : D) : IsExtent .positive (Set.Iic a) := IsLowerSet.Iic a

theorem isExtent_Ici (a : D) : IsExtent .negative (Set.Ici a) :=
  isExtent_negative.mpr (IsUpperSet.Ici a)

theorem isExtent_smul_Iic (q : Polarity) (a : D) : IsExtent q (q • Set.Iic a) := by
  cases q
  · exact IsLowerSet.Iic a
  · simpa [IsExtent] using IsLowerSet.Iic a

end Preorder

variable [LinearOrder D]

/-- On a linear scale, a nonempty extent included in an extent other than the whole scale has
the polarity of that extent. -/
theorem IsExtent.polarity_eq (hs : IsExtent p s) (ht : IsExtent q t) (hne : s.Nonempty)
    (ht' : t ≠ Set.univ) (h : s ⊆ t) : p = q := by
  by_contra hpq
  obtain ⟨l, hl⟩ := hne
  refine ht' (Set.eq_univ_of_forall fun z ↦ ?_)
  rcases p with _ | _ <;> rcases q with _ | _
  · exact absurd rfl hpq
  · exact (le_total z l).elim (fun hz ↦ h (hs hz hl)) fun hz ↦ isExtent_negative.mp ht hz (h hl)
  · exact (le_total z l).elim (fun hz ↦ ht hz (h hl)) fun hz ↦ h (isExtent_negative.mp hs hz hl)
  · exact absurd rfl hpq

theorem nonempty_smul_Iic [NoMaxOrder D] (q : Polarity) (a : D) : (q • Set.Iic a).Nonempty := by
  cases q
  · exact ⟨a, le_rfl⟩
  · exact (exists_gt a).imp fun _ h ↦ not_le.mpr h

theorem smul_Iic_ne_univ [NoMaxOrder D] (q : Polarity) (a : D) : q • Set.Iic a ≠ Set.univ := by
  cases q
  · exact fun h ↦ (exists_gt a).elim fun d hd ↦ hd.not_ge (h.ge trivial)
  · exact fun h ↦ (h.ge trivial : a ∈ (Set.Iic a)ᶜ) le_rfl

/-- On a scale with no greatest degree, the extents of two measures are included in one another
only if they have the same polarity. -/
theorem eq_of_smul_Iic_subset [NoMaxOrder D] (h : p • Set.Iic a ⊆ q • Set.Iic b) : p = q :=
  (isExtent_smul_Iic p a).polarity_eq (isExtent_smul_Iic q b) (nonempty_smul_Iic p a)
    (smul_Iic_ne_univ q b) h

end Polarity
