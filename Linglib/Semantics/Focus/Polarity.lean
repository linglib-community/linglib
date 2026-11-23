/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Focus.Marking
public import Linglib.Semantics.Questions.Inquisitive.Polar

/-!
# Polarity focus

The polarity head of a clause, [laka-1990]'s Σ, composes with the clause by its action on
propositions. Unfeatured [it adds nothing](##Focus.sigma_unfeatured), and F-marked it evokes the
clause under each polarity:
[the alternatives of the clause and their negations](##Focus.alternatives_sigma_focused). Over a
clause with no other focus these are [the proposition and its
negation](##Focus.polarityFocus_alternatives), which
[generate the polar question](##Focus.generate_polarityFocus) the sentence answers
([wilder-2013], [goodhue-2022a]).

## References

* [laka-1990]
* [wilder-2013]
* [goodhue-2022a]
-/

@[expose] public section

namespace Focus

variable {W : Type*} {c : WithAlternatives (Set W)} {a : Set W}

/-- An affirmative polarity head bearing the mark `m` over a clause meaning. -/
def sigma (m : Mark) (c : WithAlternatives (Set W)) : WithAlternatives (Set W) :=
  WithAlternatives.map₂ (· • ·) ((WithAlternatives.unfeatured Polarity.positive).mark m) c

/-- Polarity focus, an F-marked polarity head over a proposition with no other focus. -/
def polarityFocus (p : Set W) : WithAlternatives (Set W) := sigma .focused (.unfeatured p)

@[simp] theorem sigma_ordinary (m : Mark) (c : WithAlternatives (Set W)) :
    (sigma m c).ordinary = c.ordinary := by
  cases m <;> rfl

@[simp] theorem polarityFocus_ordinary (p : Set W) : (polarityFocus p).ordinary = p := rfl

@[simp] theorem sigma_unfeatured (c : WithAlternatives (Set W)) : sigma .unfeatured c = c := by
  ext : 1
  · rfl
  · simp [sigma, WithAlternatives.map₂]

/-- An F-marked polarity head adds the negation of each alternative of the clause. -/
theorem alternatives_sigma_focused (c : WithAlternatives (Set W)) :
    (sigma .focused c).alternatives = c.alternatives ∪ compl '' c.alternatives := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨s, -, b, hb, rfl⟩
    cases s
    exacts [.inl hb, .inr ⟨b, hb, rfl⟩]
  · rintro (ha | ⟨b, hb, rfl⟩)
    exacts [⟨.positive, trivial, a, ha, Polarity.positive_smul a⟩, ⟨.negative, trivial, b, hb, rfl⟩]

theorem alternatives_subset_sigma (m : Mark) (c : WithAlternatives (Set W)) :
    c.alternatives ⊆ (sigma m c).alternatives := by
  cases m
  · rw [sigma_unfeatured]
  · exact alternatives_sigma_focused c ▸ Set.subset_union_left

theorem alternatives_sigma_subset (m : Mark) (c : WithAlternatives (Set W)) :
    (sigma m c).alternatives ⊆ c.alternatives ∪ compl '' c.alternatives := by
  cases m
  · rw [sigma_unfeatured]; exact Set.subset_union_left
  · rw [alternatives_sigma_focused]

theorem compl_mem_alternatives_sigma_focused (ha : a ∈ (sigma .focused c).alternatives) :
    aᶜ ∈ (sigma .focused c).alternatives := by
  rw [alternatives_sigma_focused] at ha ⊢
  obtain ha | ⟨b, hb, rfl⟩ := ha
  exacts [.inr ⟨a, ha, rfl⟩, .inl (by rwa [compl_compl])]

theorem polarityFocus_alternatives_eq_orbit (p : Set W) :
    (polarityFocus p).alternatives = MulAction.orbit Polarity p := by
  simp [polarityFocus, sigma, Set.image2_singleton_right, MulAction.orbit]

/-- The alternatives of a proposition under polarity focus are the proposition and its
negation. -/
theorem polarityFocus_alternatives (p : Set W) :
    (polarityFocus p).alternatives = {p, pᶜ} :=
  (polarityFocus_alternatives_eq_orbit p).trans (Polarity.orbit_eq_pair_compl p)

theorem polarityFocus_wellFormed (p : Set W) : (polarityFocus p).WellFormed :=
  (WithAlternatives.WellFormed.focused _).map₂ (WithAlternatives.WellFormed.unfeatured _)

/-- Polarity focus evokes the polar question the sentence answers. -/
theorem generate_polarityFocus (p : Set W) :
    Question.generate (polarityFocus p).alternatives = Question.polar p := by
  rw [polarityFocus_alternatives_eq_orbit, Question.polar_eq_generate_orbit]

end Focus
