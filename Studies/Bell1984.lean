module

public import Linglib.Data.Statistics.Bell1984
public import Linglib.Syntax.Feature.Person.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Order.UpperLower.Basic

/-!
# Bell (1984): Language style as audience design

Bell derives the variation within one speaker's speech from the variation between speakers: a
speaker designs her style for her audience. The members of an audience hold one of four roles,
[ordered](##Bell1984.AudienceRole.le_iff) by whether the speaker knows, ratifies and addresses
them, and the effect of a role on a variable is graded by its distance from the speaker. A
graded family of effects [varies by a role only if it varies by every closer
one](##Bell1984.Graded.isLowerSet_support), which is Bell's implicational scale. A speaker who
approaches her addressees without overshooting them
[shifts no further than her community differs](##Bell1984.Accommodates.diam_range_le), which is
the style axiom's bound on the ratio of stylistic to social variation. When every speaker goes
the same fraction $c$ of the way, the speakers heard by one addressee differ by $1 - c$ of the
community's range, and style stays within that social range
[exactly when $c \le 1/2$](##Bell1984.diam_style_le_diam_social_iff).

## Implementation notes

* The level of a variable is a real number indexed by speaker and addressee, both drawn from one
  community, and a speaker's base level is her level to an addressee like herself, as Bell takes
  the travel assistant's.
* The quantitative hypothesis is stated with a weak clause for a pair of zero effects, since an
  indicator has no addressee effect and no auditor effect.
* Persons are those of `Person`: the speaker is first person, the addressee second, and the
  remaining audience roles are third persons.

## TODO

* Initiative style shift and referee design are not formalized.
* Bell's exceptions to the ratio, the crossover of the second highest class and the hyperstyle
  variables of Tehran Persian, are printed as figures and are not stored.

## References

* [bell-1984]
-/

@[expose] public section

namespace Bell1984

open Metric Set
open scoped Pointwise

/-! ### Audience roles -/

/-- The role of a member of the audience, from the closest to the speaker to the farthest. -/
inductive AudienceRole where
  /-- The addressee is known, ratified and addressed. -/
  | addressee
  /-- An auditor is known and ratified but not addressed. -/
  | auditor
  /-- An overhearer is known to be present but is no ratified participant. -/
  | overhearer
  /-- An eavesdropper's presence is unknown to the speaker. -/
  | eavesdropper
  deriving DecidableEq, Repr, Fintype

namespace AudienceRole

/-- The speaker knows that the hearer is there. -/
def Known (r : AudienceRole) : Prop := r ≠ eavesdropper

/-- The hearer is a ratified participant. -/
def Ratified (r : AudienceRole) : Prop := r = addressee ∨ r = auditor

/-- The speaker addresses the hearer. -/
def Addressed (r : AudienceRole) : Prop := r = addressee

instance : DecidablePred Known := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred Ratified := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred Addressed := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem Addressed.ratified {r : AudienceRole} (h : r.Addressed) : r.Ratified := .inl h

theorem Ratified.known {r : AudienceRole} (h : r.Ratified) : r.Known := by
  rcases h with rfl | rfl <;> decide

/-- Roles are ordered by distance from the speaker. -/
instance : LinearOrder AudienceRole := LinearOrder.lift' AudienceRole.ctorIdx (by decide)

theorem le_iff {r s : AudienceRole} :
    r ≤ s ↔ (s.Known → r.Known) ∧ (s.Ratified → r.Ratified) ∧ (s.Addressed → r.Addressed) := by
  revert r s; decide

/-- The addressee is the second person and the rest of the audience third persons. -/
def person : AudienceRole → Person
  | addressee => .second
  | _ => .third

theorem person_eq_second_iff {r : AudienceRole} : r.person = .second ↔ r.Addressed := by
  revert r; decide

end AudienceRole

/-! ### The hierarchy of effects -/

section Graded

variable {ι : Type*} [PartialOrder ι] {e : ι → ℝ}

/-- A family of effects is graded when each is less than every closer one, two effects of zero
apart. With the speaker below the audience roles this is the quantitative hypothesis. -/
def Graded (e : ι → ℝ) : Prop := ∀ ⦃i j⦄, i < j → e j < e i ∨ e i = 0 ∧ e j = 0

/-- The quantitative hypothesis gives the implicational scale: a variable that varies by a role
varies by every role closer to the speaker. -/
theorem Graded.isLowerSet_support (h : Graded e) (h₀ : ∀ i, 0 ≤ e i) :
    IsLowerSet (Function.support e) := fun j i hij hj ↦ by
  rcases hij.eq_or_lt with rfl | hlt
  · exact hj
  · rcases h hlt with h | h
    · exact (lt_of_le_of_lt (h₀ j) h).ne'
    · exact absurd h.2 hj

end Graded

/-- In each case of Tables 4 and 5 the outsider shifts the speaker less as auditor than as
addressee. -/
theorem auditor_lt_addressee :
    (∀ v, (sailorShift v).auditor < (sailorShift v).addressee) ∧
      ∀ s v, (outsiderShift s v).auditor < (outsiderShift s v).addressee := by
  decide

theorem topic_lt_addressee : ∀ v, (travelShift v).topic < (travelShift v).addressee := by decide

-- a variable may shift by addressee and not by auditor
example : (outsiderShift .e .ai).auditor = 0 ∧ 0 < (outsiderShift .e .ai).addressee := by decide

/-! ### Attention paid to speech -/

/-- For (th) the subject is more standard facing the interviewer whether or not he hears himself,
while masking his voice lowers the standard variant only when he faces the interviewer. -/
theorem th_facing_and_noise :
    (∀ n, (thStandard n .notFacing).percent < (thStandard n .facing).percent) ∧
      (thStandard .quiet .notFacing).percent < (thStandard .noise .notFacing).percent := by
  decide

theorem dh_noise : ∀ f, (dhStandard .noise f).percent < (dhStandard .quiet f).percent := by decide

/-! ### The ratio of stylistic to social variation -/

section Ratio

variable {G S α : Type*} [AddGroup α] [LE α]

/-- A table of groups by styles keeps style within social variation over the styles `t` when the
largest shift of style by any group is at most the largest difference between two groups in one
style. -/
def StyleWithinSocial (x : G → S → α) (t : Set S) : Prop :=
  ∀ g, ∀ s₁ ∈ t, ∀ s₂ ∈ t, ∃ s ∈ t, ∃ g₁ g₂, x g s₁ - x g s₂ ≤ x g₁ s - x g₂ s

instance [Fintype G] [Fintype S] [DecidableLE α] (x : G → S → α) (t : Set S)
    [DecidablePred (· ∈ t)] : Decidable (StyleWithinSocial x t) := by
  unfold StyleWithinSocial; infer_instance

end Ratio

/-! ### Accommodation -/

section Accommodation

variable {I : Type*} {level : I → I → ℝ} {b : I → ℝ} {c : ℝ}

/-- A community accommodates when each speaker's level to an addressee lies between her base
level and the addressee's: she approaches the addressee and does not overshoot. -/
def Accommodates (level : I → I → ℝ) : Prop :=
  ∀ s a, level s a ∈ segment ℝ (level s s) (level a a)

/-- An accommodating speaker's range of style is at most the range of base levels in her
community. -/
theorem Accommodates.diam_range_le (h : Accommodates level)
    (hb : Bornology.IsBounded (range fun i ↦ level i i)) (s : I) :
    diam (range (level s)) ≤ diam (range fun i ↦ level i i) := by
  rw [← convexHull_diam (range fun i ↦ level i i)]
  refine diam_mono ?_ (isBounded_convexHull.2 hb)
  rintro _ ⟨a, rfl⟩
  exact segment_subset_convexHull (s := range fun i ↦ level i i) ⟨s, rfl⟩ ⟨a, rfl⟩ (h s a)

/-- Every speaker goes the fraction `c` of the way from her base level to her addressee's. -/
def linear (b : I → ℝ) (c : ℝ) (s a : I) : ℝ := b s + c * (b a - b s)

@[simp] theorem linear_self (s : I) : linear b c s s = b s := by simp [linear]

theorem accommodates_linear (hc : c ∈ Icc (0 : ℝ) 1) : Accommodates (linear b c) := fun s a ↦ by
  rw [linear_self, linear_self, segment_eq_image_lineMap]
  exact ⟨c, hc, by simp [linear, AffineMap.lineMap_apply_ring']; ring⟩

private theorem diam_range_mul_add (k d : ℝ) (f : I → ℝ) :
    diam (range fun i ↦ k * f i + d) = |k| * diam (range f) := by
  have : (range fun i ↦ k * f i + d) = (· + d) '' (k • range f) := by
    ext x
    simp only [mem_range, mem_image, mem_smul_set, smul_eq_mul, exists_exists_eq_and]
  rw [this, (isometry_add_right d).diam_image, diam_smul₀, Real.norm_eq_abs]

theorem diam_range_linear_style (s : I) :
    diam (range (linear b c s)) = |c| * diam (range b) := by
  rw [← diam_range_mul_add c (b s - c * b s) b]
  congr 2
  ext a
  simp only [linear]
  ring

theorem diam_range_linear_social (a : I) :
    diam (range fun s ↦ linear b c s a) = |1 - c| * diam (range b) := by
  rw [← diam_range_mul_add (1 - c) (c * b a) b]
  congr 2
  ext s
  simp only [linear]
  ring

/-- When every speaker goes the same fraction of the way to her addressee, style varies no more
than speakers heard by one addressee do exactly when the fraction is at most a half. -/
theorem diam_style_le_diam_social_iff (hc : c ∈ Icc (0 : ℝ) 1) (hb : 0 < diam (range b))
    (s a : I) :
    diam (range (linear b c s)) ≤ diam (range fun s ↦ linear b c s a) ↔ c ≤ 1 / 2 := by
  rw [diam_range_linear_style, diam_range_linear_social, mul_le_mul_iff_of_pos_right hb,
    abs_of_nonneg hc.1, abs_of_nonneg (sub_nonneg.2 hc.2)]
  constructor <;> intro h <;> linarith

end Accommodation

end Bell1984
