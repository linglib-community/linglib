module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Monotone.Basic
public import Linglib.Core.Order.Prop
public import Linglib.Semantics.Reference.Iota

/-!
# Distinguishing descriptions

A description is compatible with each individual to some degree, a truth value or a value in any
other preorder, and it distinguishes its referent from a contrast set when its compatibility with
the referent strictly exceeds its compatibility with every distractor. A truth-valued description
that holds of the referent distinguishes it exactly when it
[holds of no distractor](##distinguishes_iff_forall_not), which are the two conditions of Dale and
Reiter's distinguishing description, and these say that the referent is
[the only individual of the context set the description holds of](##and_distinguishes_iff_mem_iota),
the uniqueness of the definite article and the definition of Chen and van Deemter. A graded
description distinguishes exactly when [some threshold of it
does](##distinguishes_iff_exists_threshold), and distinguishing
[survives a strictly monotone rescaling](##distinguishes_comp_iff), such as the normalization that
makes the degrees a literal listener's probabilities.

## Implementation notes

Against an empty contrast set every description distinguishes, whether or not it holds of the
referent, so the first of Dale and Reiter's conditions is stated separately: their distinguishing
description is `p r ∧ Distinguishes p C r`, and against a nonempty contrast set the conjunct
[follows](##distinguishes_prop_iff).

## References

* [dale-reiter-1995]
* [chen-van-deemter-2023]
* [degen-etal-2020]
-/

@[expose] public section

variable {E α β : Type*}

section Preorder

variable [Preorder α] (f : E → α) (C : Finset E) (r : E)

/-- A description of compatibility `f` distinguishes the referent `r` from the contrast set `C`:
its compatibility with `r` strictly exceeds its compatibility with every member of `C`. -/
def Distinguishes : Prop := ∀ c ∈ C, f c < f r

instance [∀ c, Decidable (f c < f r)] : Decidable (Distinguishes f C r) :=
  Finset.decidableDforallFinset

variable {f C r}

theorem Distinguishes.of_subset {C' : Finset E} (h : Distinguishes f C r) (hC : C' ⊆ C) :
    Distinguishes f C' r :=
  fun c hc ↦ h c (hC hc)

end Preorder

section LinearOrder

variable [LinearOrder α] {f : E → α} {C : Finset E} {r : E}

/-- A rescaling of a description's compatibility that is strictly monotone on the values the
description takes, such as the literal listener's normalization of a nonnegative meaning,
preserves distinguishing. -/
theorem distinguishes_comp_iff [Preorder β] {φ : α → β} {s : Set α} (hφ : StrictMonoOn φ s)
    (hs : ∀ x, f x ∈ s) : Distinguishes (φ ∘ f) C r ↔ Distinguishes f C r :=
  forall₂_congr fun c _ ↦ hφ.lt_iff_lt (hs c) (hs r)

/-- A graded compatibility distinguishes exactly when some threshold of it does, and the
referent's own compatibility is such a threshold. -/
theorem distinguishes_iff_exists_threshold :
    Distinguishes f C r ↔ ∃ t, Distinguishes (fun x ↦ t ≤ f x) C r := by
  refine ⟨fun h ↦ ⟨f r, fun c hc ↦ Prop.lt_iff.2 ⟨not_le.2 (h c hc), le_rfl⟩⟩, ?_⟩
  rintro ⟨t, h⟩ c hc
  obtain ⟨hc', hr⟩ := Prop.lt_iff.1 (h c hc)
  exact (not_le.1 hc').trans_le hr

end LinearOrder

/-! ### Truth-valued compatibility -/

section TruthValues

variable {p : E → Prop} {C : Finset E} {r : E}

/-- A truth-valued description that holds of the referent distinguishes it exactly when it holds
of no distractor. -/
theorem distinguishes_iff_forall_not (hr : p r) : Distinguishes p C r ↔ ∀ c ∈ C, ¬ p c :=
  forall₂_congr fun _ _ ↦ Prop.lt_iff.trans (and_iff_left hr)

/-- A truth-valued description that distinguishes the referent from some distractor holds of
the referent. -/
theorem Distinguishes.apply (h : Distinguishes p C r) (hC : C.Nonempty) : p r :=
  (Prop.lt_iff.1 (h _ hC.choose_spec)).2

theorem Distinguishes.not_apply (h : Distinguishes p C r) {c : E} (hc : c ∈ C) : ¬ p c :=
  (Prop.lt_iff.1 (h c hc)).1

/-- At truth values, a description distinguishes `r` from a nonempty contrast set exactly when
it holds of `r` and of no distractor. -/
theorem distinguishes_prop_iff (hC : C.Nonempty) :
    Distinguishes p C r ↔ p r ∧ ∀ c ∈ C, ¬ p c :=
  ⟨fun h ↦ ⟨h.apply hC, fun _ ↦ h.not_apply⟩, fun h ↦ (distinguishes_iff_forall_not h.1).2 h.2⟩

/-- A truth-valued description holds of the referent and distinguishes it from a contrast set
that excludes it exactly when the referent is the only individual of the context set
`insert r C` that the description holds of, the uniqueness of the definite article. -/
theorem and_distinguishes_iff_mem_iota [DecidableEq E] (hr : r ∉ C) :
    p r ∧ Distinguishes p C r ↔ r ∈ iota {x | p x ∧ x ∈ insert r C} := by
  rw [mem_iota]
  simp only [Set.mem_ofPred_eq, Finset.mem_insert, true_or, and_true]
  exact and_congr_right fun hp ↦ (distinguishes_iff_forall_not hp).trans
    ⟨fun h x ⟨hx, hxr⟩ ↦ hxr.elim id fun hxC ↦ (h x hxC hx).elim,
      fun h c hc hc' ↦ hr (h c ⟨hc', .inr hc⟩ ▸ hc)⟩

theorem distinguishes_iff_mem_iota [DecidableEq E] (hC : C.Nonempty) (hr : r ∉ C) :
    Distinguishes p C r ↔ r ∈ iota {x | p x ∧ x ∈ insert r C} := by
  rw [← and_distinguishes_iff_mem_iota hr, and_iff_right_of_imp (·.apply hC)]

end TruthValues
