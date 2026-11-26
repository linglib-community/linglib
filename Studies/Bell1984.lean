module

public import Linglib.Data.Statistics.Bell1984
public import Linglib.Syntax.Feature.Person.Defs
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Order.UpperLower.Basic

/-!
# Bell (1984): Language style as audience design

A speaker designs her style for her audience, so variation within one speaker derives from
variation between speakers. Audience roles are [ordered](##Bell1984.AudienceRole.le_iff) by
whether the speaker knows, ratifies and addresses the hearer, and a family of effects graded by
that order [varies by a role only if it varies by every closer
one](##Bell1984.Graded.isLowerSet_support). A speaker who approaches her addressees without
overshooting them [shifts no further than her community
differs](##Bell1984.Accommodates.diam_range_le). Against the speakers one addressee hears, with
convergence by a fraction $c_\uparrow$ toward higher levels and $c_\downarrow$ toward lower
ones, style stays within social variation [exactly when $c_\uparrow + c_\downarrow \le
1$](##Bell1984.diam_style_le_diam_social_iff).

## Implementation notes

* The level of a variable is a real number indexed by speaker and addressee, both drawn from one
  community, and a speaker's base level is her level to an addressee like herself, as Bell takes
  the travel assistant's.
* Convergence is two constant fractions, one toward addressees whose level is higher and one
  toward those whose level is lower. Bell reports the travel assistant going a little more than
  halfway to the classes below her own and shifting slightly and inconsistently toward those
  above.
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

/-- Every speaker goes the fraction `cUp` of the way to an addressee whose level is at least her
own, and the fraction `cDown` of the way to one whose level is lower. -/
noncomputable def converge (b : I → ℝ) (cUp cDown : ℝ) (s a : I) : ℝ :=
  b s + (if b s ≤ b a then cUp else cDown) * (b a - b s)

variable {cUp cDown : ℝ} {lo hi : I}

@[simp] theorem converge_self (s : I) : converge b cUp cDown s s = b s := by simp [converge]

theorem accommodates_converge (hu : cUp ∈ Icc (0 : ℝ) 1) (hd : cDown ∈ Icc (0 : ℝ) 1) :
    Accommodates (converge b cUp cDown) := fun s a ↦ by
  rw [converge_self, converge_self, segment_eq_image_lineMap]
  refine ⟨if b s ≤ b a then cUp else cDown, by split_ifs <;> assumption, ?_⟩
  simp only [converge, AffineMap.lineMap_apply_ring']
  ring

private theorem diam_range_eq_sub {f : I → ℝ} (h : ∀ i, f lo ≤ f i ∧ f i ≤ f hi) :
    diam (range f) = f hi - f lo := by
  have hsub : range f ⊆ Icc (f lo) (f hi) := by rintro _ ⟨i, rfl⟩; exact h i
  refine le_antisymm ((diam_mono hsub (isBounded_Icc _ _)).trans_eq (Real.diam_Icc (h lo).2)) ?_
  have := dist_le_diam_of_mem ((isBounded_Icc _ _).subset hsub) (mem_range_self hi)
    (mem_range_self lo)
  rw [Real.dist_eq] at this
  exact (le_abs_self _).trans this

-- a speaker's range of style
theorem diam_range_converge_style (hlo : ∀ i, b lo ≤ b i) (hhi : ∀ i, b i ≤ b hi)
    (hu : 0 ≤ cUp) (hd : 0 ≤ cDown) (s : I) :
    diam (range (converge b cUp cDown s)) = cUp * (b hi - b s) + cDown * (b s - b lo) := by
  have key (a : I) : converge b cUp cDown s lo ≤ converge b cUp cDown s a ∧
      converge b cUp cDown s a ≤ converge b cUp cDown s hi := by
    have := hlo a; have := hhi a; have := hlo s; have := hhi s
    simp only [converge]
    split_ifs <;> constructor <;> nlinarith
  rw [diam_range_eq_sub key]
  have := hlo s; have := hhi s
  simp only [converge]
  split_ifs <;> nlinarith

-- the range of the speakers one addressee hears
theorem diam_range_converge_social (hlo : ∀ i, b lo ≤ b i) (hhi : ∀ i, b i ≤ b hi)
    (hu : cUp ≤ 1) (hd : cDown ≤ 1) (a : I) :
    diam (range fun s ↦ converge b cUp cDown s a) =
      (b hi - b lo) - cUp * (b a - b lo) - cDown * (b hi - b a) := by
  have key (s : I) : converge b cUp cDown lo a ≤ converge b cUp cDown s a ∧
      converge b cUp cDown s a ≤ converge b cUp cDown hi a := by
    have := hlo a; have := hhi a; have := hlo s; have := hhi s
    simp only [converge]
    split_ifs <;> constructor <;> nlinarith
  rw [diam_range_eq_sub (f := fun s ↦ converge b cUp cDown s a) key]
  have := hlo a; have := hhi a
  simp only [converge]
  split_ifs <;> nlinarith

/-- When speakers converge by one fraction toward higher levels and by another toward lower ones,
every speaker's range of style is within the range of the speakers some addressee hears exactly
when the two fractions sum to at most one. -/
theorem diam_style_le_diam_social_iff (hlo : ∀ i, b lo ≤ b i) (hhi : ∀ i, b i ≤ b hi)
    (hb : b lo < b hi) (hu : cUp ∈ Icc (0 : ℝ) 1) (hd : cDown ∈ Icc (0 : ℝ) 1) :
    (∀ s, ∃ a, diam (range (converge b cUp cDown s)) ≤
      diam (range fun s' ↦ converge b cUp cDown s' a)) ↔ cUp + cDown ≤ 1 := by
  simp only [diam_range_converge_style hlo hhi hu.1 hd.1,
    diam_range_converge_social hlo hhi hu.2 hd.2]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h lo
    obtain ⟨a', ha'⟩ := h hi
    have := hlo a; have := hhi a; have := hlo a'; have := hhi a'
    by_contra hc
    rcases le_total cDown cUp with hle | hle <;> nlinarith [hu.1, hd.1]
  · intro h s
    have := hlo s; have := hhi s
    rcases le_total cDown cUp with hle | hle
    · exact ⟨lo, by nlinarith [hu.1, hd.1]⟩
    · exact ⟨hi, by nlinarith [hu.1, hd.1]⟩

end Accommodation

end Bell1984
