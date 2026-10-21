module

public import Linglib.Core.Order.Flat
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

/-!
# The values a flat value extends to

`Flat.extensions x` is the finset of values of a finite type that `x` extends to: every value for
`⊥`, and `a` alone for `↑a`. A nonempty finset of values has a most informative flat value
extending to all of them, its meet, which is `⊥` once the finset has two values.

## Main declarations

* `Flat.extensions`: the values a flat value extends to.
* `Flat.le_inf'_iff_subset_extensions`: the meet of a finset of values is the greatest flat value
  extending to all of them.
* `Flat.subset_extensions_iff_eq_bot`: only `⊥` extends to two distinct values.
* `Flat.finsetInf`: the meet of a finset-indexed family of flat values.
-/

@[expose] public section

namespace Flat

open Finset

variable {α ι : Type*} [DecidableEq α] {x : Flat α} {s : Finset α} {a : α}

/-- Two distinct values have no common flat value but `⊥`. -/
theorem inf'_coe_eq_bot (hs : s.Nontrivial) : s.inf' hs.nonempty (↑) = (⊥ : Flat α) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  refine le_bot_iff.1 (le_of_le_of_eq (le_inf (inf'_le _ ha) (inf'_le _ hb)) ?_)
  simpa [inf_def, eq_comm] using hab

/-- The meet of the flat values `v i` over a finset `s` of indices, `⊥` on the empty finset. -/
def finsetInf (s : Finset ι) (v : ι → Flat α) : Flat α :=
  if h : s.Nonempty then s.inf' h v else ⊥

@[simp] theorem finsetInf_singleton (i : ι) (v : ι → Flat α) : finsetInf {i} v = v i := by
  simp [finsetInf]

variable [Fintype α]

/-- The values `x` extends to. -/
def extensions (x : Flat α) : Finset α := univ.filter (x ≤ ↑·)

@[simp] theorem mem_extensions : a ∈ x.extensions ↔ x ≤ ↑a := by simp [extensions]

@[simp] theorem extensions_bot : (⊥ : Flat α).extensions = univ := by ext; simp

@[simp] theorem extensions_coe (a : α) : (a : Flat α).extensions = {a} := by
  ext; simp [coe_le_iff, eq_comm]

/-- The meet of a nonempty finset of values is the greatest flat value extending to all of them. -/
theorem le_inf'_iff_subset_extensions (hs : s.Nonempty) :
    x ≤ s.inf' hs (↑) ↔ s ⊆ x.extensions := by
  simp [Finset.le_inf'_iff, subset_iff]

theorem subset_extensions_iff_eq_bot (hs : s.Nontrivial) : s ⊆ x.extensions ↔ x = ⊥ := by
  rw [← le_inf'_iff_subset_extensions hs.nonempty, inf'_coe_eq_bot hs, le_bot_iff]

end Flat
