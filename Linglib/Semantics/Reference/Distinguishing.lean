module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Monotone.Basic
public import Linglib.Core.Order.Prop
public import Linglib.Semantics.Reference.Iota

/-!
# Distinguishing descriptions

A description distinguishes its referent from a contrast set when its compatibility with the
referent strictly exceeds its compatibility with every distractor, compatibility taking values in a
preorder. At truth values this is the distinguishing description of Dale and Reiter, which holds of
the referent and of no distractor, and the Russellian uniqueness of `iota` over the domain
the contrast set restricts. Under a graded semantics it says the referent is the literal listener's
best guess, since a strictly monotone rescaling of compatibility such as the listener's
normalization does not change it (`distinguishes_comp_iff`). A graded
description distinguishes exactly when some level set of its compatibility does, so the truth-valued
notion is the general one at a threshold.

## Main definitions

* `Distinguishes compat C r d`: the compatibility of `d` with `r` strictly exceeds its
  compatibility with every member of `C`.

## Main results

* `distinguishes_prop_iff`: at truth values, `d` holds of `r` and of no distractor.
* `distinguishes_iff_iota`, `distinguishes_univ_erase_iff`: identification is the
  definite's uniqueness on the domain, and `r` is the whole extension against everything else.
* `distinguishes_comp_iff`: invariance under strictly monotone rescaling of compatibility.
* `distinguishes_iff_exists_threshold`: a graded compatibility distinguishes exactly when some
  threshold of it does.

## References

* [dale-reiter-1995]
* [grice-1975]
* [engelhardt-etal-2006]
* [degen-etal-2020]
-/

@[expose] public section

variable {D E α β : Type*}

section Preorder

variable [Preorder α] (compat : D → E → α) (C : Finset E) (r : E) (d : D)

/-- The compatibility of the description `d` with the referent `r` strictly exceeds its
compatibility with every member of the contrast set `C`. -/
def Distinguishes : Prop := ∀ c ∈ C, compat d c < compat d r

instance [DecidableLT α] : Decidable (Distinguishes compat C r d) := by
  unfold Distinguishes; infer_instance

variable {compat C r d}

/-- A distinguishing description distinguishes against any smaller contrast set. -/
theorem Distinguishes.anti (h : Distinguishes compat C r d) {C' : Finset E} (hC : C' ⊆ C) :
    Distinguishes compat C' r d :=
  fun c hc ↦ h c (hC hc)

end Preorder

section LinearOrder

variable [LinearOrder α] {compat : D → E → α} {C : Finset E} {r : E} {d : D}

/-- A rescaling of a description's compatibility that is strictly monotone on the values the
description takes, such as the literal listener's normalization of a nonnegative meaning,
preserves distinguishing. -/
theorem distinguishes_comp_iff [Preorder β] {compat' : D → E → β} {φ : α → β} {s : Set α}
    (hφ : StrictMonoOn φ s) (hs : ∀ x, compat d x ∈ s) (h : ∀ x, compat' d x = φ (compat d x)) :
    Distinguishes compat' C r d ↔ Distinguishes compat C r d :=
  forall₂_congr fun c _ ↦ by rw [h, h]; exact hφ.lt_iff_lt (hs c) (hs r)

/-- A graded compatibility distinguishes exactly when some threshold of it does, and the
referent's own compatibility is such a threshold. -/
theorem distinguishes_iff_exists_threshold :
    Distinguishes compat C r d ↔ ∃ t, Distinguishes (fun d x ↦ t ≤ compat d x) C r d := by
  refine ⟨fun h ↦ ⟨compat d r, fun c hc ↦ Prop.lt_iff.2 ⟨not_le.2 (h c hc), le_rfl⟩⟩, ?_⟩
  rintro ⟨t, h⟩ c hc
  obtain ⟨hc', hr⟩ := Prop.lt_iff.1 (h c hc)
  exact (not_le.1 hc').trans_le hr

end LinearOrder

/-! ### Truth-valued compatibility -/

section TruthValues

variable (compat : D → E → Prop) (C : Finset E) (r : E) (d : D)

instance [∀ d x, Decidable (compat d x)] : Decidable (Distinguishes compat C r d) := by
  unfold Distinguishes; infer_instance

variable {compat C r d}

/-- At truth values, a description distinguishes `r` from a nonempty contrast set exactly when
it holds of `r` and of no distractor. -/
theorem distinguishes_prop_iff (hC : C.Nonempty) :
    Distinguishes compat C r d ↔ compat d r ∧ ∀ c ∈ C, ¬ compat d c := by
  simp only [Distinguishes, Prop.lt_iff]
  exact ⟨fun h ↦ ⟨(h _ hC.choose_spec).2, fun c hc ↦ (h c hc).1⟩,
    fun ⟨hr, h⟩ c hc ↦ ⟨h c hc, hr⟩⟩

/-- Identification against a nonempty contrast set that excludes the referent is the Russellian
uniqueness of the description on the domain `insert r C`. -/
theorem distinguishes_iff_iota [DecidableEq E] (hC : C.Nonempty) (hr : r ∉ C) :
    Distinguishes compat C r d ↔ iota (fun x ↦ compat d x ∧ x ∈ insert r C) = some r := by
  rw [distinguishes_prop_iff hC, iota_eq_some_iff]
  simp only [Finset.mem_insert, true_or, and_true]
  exact and_congr_right fun _ ↦
    ⟨fun h x ⟨hx, hxr⟩ ↦ hxr.elim id fun hxC ↦ (h x hxC hx).elim,
      fun h c hc hc' ↦ hr (h c ⟨hc', .inr hc⟩ ▸ hc)⟩

/-- Against every other individual of a finite domain with at least two, a description
distinguishes `r` exactly when `r` is its whole extension. -/
theorem distinguishes_univ_erase_iff [Fintype E] [DecidableEq E] [Nontrivial E] :
    Distinguishes compat (Finset.univ.erase r) r d ↔ {x | compat d x} = {r} := by
  obtain ⟨x, hx⟩ := exists_ne r
  rw [distinguishes_prop_iff ⟨x, Finset.mem_erase.2 ⟨hx, Finset.mem_univ x⟩⟩]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Set.eq_singleton_iff_unique_mem,
    Set.mem_ofPred_eq]
  exact and_congr_right fun _ ↦ ⟨fun h x hx ↦ by_contra fun hxr ↦ h x hxr hx,
    fun h c hc hc' ↦ hc (h c hc')⟩

end TruthValues

