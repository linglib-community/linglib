module

public import Mathlib.Order.Filter.Ker

/-!
# Common ground

The common ground of a conversation is the set of propositions the interlocutors mutually
accept, as Stalnaker and, independently, Karttunen describe it. Acceptance is closed under
entailment and finite conjunction and contains the trivial proposition, so the common ground is
a filter on worlds, like Chellas's augmented models and Gärdenfors's deductively closed belief
sets. Stalnaker's context set, the worlds compatible with everything accepted, is its kernel
`Filter.ker`, and a bare context set `cs` is the principal common ground `𝓟 cs`. Asserting `φ`
takes a common ground `c` to `c ⊓ 𝓟 φ`, so a history of assertions lands on the principal filter
of their intersection in whatever order they are made, and a history that asserts more leaves a
stronger common ground.

`HasCommonGround` and `HasAssertion` connect richer discourse states (commitment slates,
gameboards, probabilistic states) to this projection.

## Main definitions

* `HasCommonGround`: discourse states projecting to a common ground `Filter W`, with the
  derived `contextSet`.
* `HasAssertion`: discourse states with a Stalnakerian `assert`, projecting to `· ⊓ 𝓟 φ`,
  and assertion histories `HasAssertion.play`.

## Main results

* `HasAssertion.contextSet_assert`: assertion intersects the context set by exactly the
  asserted proposition.
* `HasAssertion.commonGround_play`, `HasAssertion.commonGround_play_perm`: a history lands on
  the principal filter of its intersection, whatever the order of its assertions.
* `HasAssertion.antitone_commonGround_play`: along histories each asserting what the earlier
  ones assert, the common ground only grows.

## Implementation notes

The filter axioms are the body-of-information view of the common ground that Geurts surveys,
and they carry no epistemology. Whether what grounds them is Stalnaker's iterated common belief,
his later common acceptance as a primitive, or Lederman's non-iterated minimal theory is stated
separately, as `Filter.GroundedIn` in `Logic/Modal/Epistemic.lean`; closure of acceptance under
conjunction, the filter's `inter_sets`, is the axiom Lederman contests. Farkas and Bruce's
proposal-based assertion and Anderson's graded non-monotonic assertion are deliberate
non-instances of `HasAssertion` (`FarkasBruce2010.assert_not_narrowing`,
`Anderson2021.graded_update_keeps_false_world`).

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

open Filter Set

variable {W : Type*}

/-! ### Discourse states and their common ground -/

/-- A discourse state projects to a common ground, the filter of propositions the
interlocutors mutually accept at that state. -/
class HasCommonGround (S : Type*) (W : outParam Type*) where
  /-- The common ground of the state. -/
  commonGround : S → Filter W

export HasCommonGround (commonGround)

/-- The context set of a discourse state is the set of worlds compatible with everything
accepted. -/
def HasCommonGround.contextSet {S : Type*} [HasCommonGround S W] (s : S) : Set W :=
  (commonGround s).ker

/-- A filter is its own common ground. -/
instance : HasCommonGround (Filter W) W := ⟨id⟩

@[simp] theorem HasCommonGround.commonGround_filter (f : Filter W) : commonGround f = f := rfl

/-- A bare context set is the principal common ground. -/
instance : HasCommonGround (Set W) W := ⟨principal⟩

@[simp] theorem HasCommonGround.commonGround_set (s : Set W) : commonGround s = 𝓟 s := rfl

/-! ### Stalnakerian assertion -/

/-- A discourse state with a Stalnakerian `assert`, under which the projected common ground grows
by exactly the asserted proposition ([stalnaker-1978]). -/
class HasAssertion (S : Type*) (W : outParam Type*) extends HasCommonGround S W where
  /-- The initial dialogue state. -/
  initial : S
  /-- Assert `φ`. -/
  assert : S → Set W → S
  /-- Nothing is presupposed initially. -/
  commonGround_initial : commonGround initial = ⊤
  /-- Assertion adds exactly `φ` to the common ground. -/
  commonGround_assert : ∀ (s : S) (φ : Set W), commonGround (assert s φ) = commonGround s ⊓ 𝓟 φ

/-- In the regular model a common ground is asserted into by `· ⊓ 𝓟 φ`. Every `HasAssertion`
state projects onto this flow. -/
instance : HasAssertion (Filter W) W where
  initial := ⊤
  assert f φ := f ⊓ 𝓟 φ
  commonGround_initial := rfl
  commonGround_assert _ _ := rfl

namespace HasAssertion

open HasCommonGround (contextSet)

variable {S : Type*} [HasAssertion S W] (s : S) (φ ψ : Set W)

attribute [simp] commonGround_initial commonGround_assert

theorem mem_commonGround_assert : φ ∈ commonGround (assert s φ) := by
  simp [le_principal_iff.1 inf_le_right]

theorem commonGround_assert_le : commonGround (assert s φ) ≤ commonGround s := by
  simp [inf_le_left]

/-- Assertion intersects the context set by exactly the asserted proposition
([stalnaker-1973] p. 455). -/
@[simp] theorem contextSet_assert : contextSet (assert s φ) = contextSet s ∩ φ := by
  simp [contextSet, HasCommonGround.contextSet]

@[simp] theorem commonGround_assert_initial :
    commonGround (assert (initial : S) φ) = 𝓟 φ := by simp

theorem commonGround_assert_assert :
    commonGround (assert (assert s φ) ψ) = commonGround s ⊓ 𝓟 (φ ∩ ψ) := by
  simp [inf_assoc, inf_principal]

theorem commonGround_assert_comm :
    commonGround (assert (assert s φ) ψ) = commonGround (assert (assert s ψ) φ) := by
  simp only [commonGround_assert_assert, inter_comm]

theorem commonGround_assert_idem :
    commonGround (assert (assert s φ) φ) = commonGround (assert s φ) := by
  simp

/-- Asserting what is already accepted is a no-op on the common ground
([stalnaker-1973] p. 454). -/
theorem commonGround_assert_of_mem (h : φ ∈ commonGround s) :
    commonGround (assert s φ) = commonGround s := by
  simp [inf_eq_left.2 (le_principal_iff.2 h)]

/-! ### Assertion histories -/

/-- Play a history of assertions from a state. -/
def play (s : S) (h : List (Set W)) : S :=
  h.foldl assert s

@[simp] theorem play_nil (s : S) : play s [] = s := rfl

@[simp] theorem play_cons (s : S) (φ : Set W) (t : List (Set W)) :
    play s (φ :: t) = play (assert s φ) t := rfl

@[simp] theorem play_append (s : S) (h₁ h₂ : List (Set W)) :
    play s (h₁ ++ h₂) = play (play s h₁) h₂ :=
  List.foldl_append

/-- A played history adds the principal filter of the history's intersection. -/
theorem commonGround_play (h : List (Set W)) (s : S) :
    commonGround (play s h) = commonGround s ⊓ 𝓟 (⋂ p ∈ h, p) := by
  induction h generalizing s with
  | nil => simp
  | cons φ t ih =>
    rw [play_cons, ih, commonGround_assert, inf_assoc, inf_principal]
    congr 2
    ext
    simp

/-- From the initial state, a played history *is* its common ground, the free model of
Stalnakerian assertion ([stalnaker-1973] p. 450). -/
theorem commonGround_play_initial (h : List (Set W)) :
    commonGround (play (initial : S) h) = 𝓟 (⋂ p ∈ h, p) := by
  simp [commonGround_play]

theorem commonGround_play_le_of_subset {h₁ h₂ : List (Set W)} (hs : h₁ ⊆ h₂) :
    commonGround (play s h₂) ≤ commonGround (play s h₁) := by
  simp only [commonGround_play]
  exact inf_le_inf_left _
    (principal_mono.2 (Set.subset_iInter₂ fun p hp ↦ Set.iInter₂_subset p (hs hp)))

/-- Along a family of histories, each asserting everything the earlier ones do, the common
ground only grows. -/
theorem antitone_commonGround_play {ι : Type*} [Preorder ι] {h : ι → List (Set W)}
    (hh : ∀ ⦃i j⦄, i ≤ j → h i ⊆ h j) : Antitone fun i ↦ commonGround (play s (h i)) :=
  fun _ _ hij ↦ commonGround_play_le_of_subset s (hh hij)

/-- Assertion order is irrelevant, so permuted histories project to the same common ground.
States may differ, since frameworks can record order, but the projection cannot. -/
theorem commonGround_play_perm {h₁ h₂ : List (Set W)} (p : h₁.Perm h₂) :
    commonGround (play (initial : S) h₁) = commonGround (play (initial : S) h₂) := by
  simp [commonGround_play_initial, p.mem_iff]

end HasAssertion
