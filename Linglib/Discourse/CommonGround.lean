module

public import Mathlib.Order.Filter.Ker

/-!
# Common ground

The common ground of a conversation is the set of propositions the interlocutors mutually
accept, as Stalnaker and, independently, Karttunen describe it. Acceptance is closed under
entailment and finite conjunction and contains the trivial proposition, so the common ground is
a filter on worlds, like Chellas's augmented models and Gärdenfors's deductively closed belief
sets. Stalnaker's context set, the worlds compatible with everything accepted, is its kernel
`Filter.ker`, and a bare context set `cs` is the principal common ground `𝓟 cs`, the two related
by mathlib's `Filter.giPrincipalKer`. Asserting `φ` takes a common ground `c` to `c ⊓ 𝓟 φ`, which
intersects the context set with `φ` (`Filter.ker_inf`), so a history of assertions lands on the
principal filter of their intersection in whatever order they are made, and a history that
asserts more leaves a stronger common ground.

A framework whose discourse states carry more than a common ground projects them to one, and its
assertion is Stalnakerian when the projection semiconjugates it to `· ⊓ 𝓟 φ`
(`Function.Semiconj`), which `List.foldl_hom` extends to histories: the mood state's assertion is
(`Mood.State.semiconj_assert`), and so is the scoreboard's
(`Roberts2023.Scoreboard.semiconj_assert`). Farkas and Bruce's assertion leaves the common ground
as it is, a proposal until it is settled (`Commitment.Table.commonGround_assert`), and Anderson's
graded update joins the common ground with the evidence's instead of meeting it
(`Anderson2021.ae_updateCG`).

## Main statements

* `Filter.foldl_inf_principal`: a history of assertions lands on the principal filter of the
  intersection of what it asserts.
* `Filter.foldl_inf_principal_anti`: a history that asserts more leaves a stronger common ground.

## Implementation notes

The filter axioms are the body-of-information view of the common ground that Geurts surveys,
and they carry no epistemology. Whether what grounds them is Stalnaker's iterated common belief,
his later common acceptance as a primitive, or Lederman's non-iterated minimal theory is stated
separately, as `Filter.GroundedIn` in `Logic/Modal/Epistemic.lean`; closure of acceptance under
conjunction, the filter's `inter_sets`, is the axiom Lederman contests.

## References

* [stalnaker-1973]
* [stalnaker-1978]
* [stalnaker-2002]
* [stalnaker-2014]
* [karttunen-1974-presupposition]
* [chellas-1980]
* [gardenfors-1988]
* [geurts-2024]
* [lederman-2014]
* [farkas-bruce-2010]
* [anderson-2021]
-/

@[expose] public section

open Set

namespace Filter

variable {W : Type*} (c : Filter W) (h : List (Set W))

theorem foldl_inf_principal : h.foldl (· ⊓ 𝓟 ·) c = c ⊓ 𝓟 (⋂ p ∈ h, p) := by
  induction h generalizing c with
  | nil => simp
  | cons φ t ih =>
    rw [List.foldl_cons, ih, inf_assoc, inf_principal]
    congr 2
    ext
    simp

/-- From the trivial common ground, a history of assertions is the principal filter of what it
asserts, the free model of Stalnakerian assertion ([stalnaker-1973] p. 450). -/
theorem foldl_inf_principal_top : h.foldl (· ⊓ 𝓟 ·) ⊤ = 𝓟 (⋂ p ∈ h, p) := by
  rw [foldl_inf_principal, top_inf_eq]

variable {c} in
theorem foldl_inf_principal_anti {h₁ h₂ : List (Set W)} (hs : h₁ ⊆ h₂) :
    h₂.foldl (· ⊓ 𝓟 ·) c ≤ h₁.foldl (· ⊓ 𝓟 ·) c := by
  simp only [foldl_inf_principal]
  exact inf_le_inf_left _ (principal_mono.2 (subset_iInter₂ fun p hp ↦ iInter₂_subset p (hs hp)))

end Filter
