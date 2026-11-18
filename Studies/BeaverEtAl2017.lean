module

public import Studies.TonhauserEtAl2013
public import Linglib.Semantics.Questions.Polar
public import Linglib.Semantics.Questions.Resolution

/-!
# Beaver, Roberts, Simons and Tonhauser (2017): Questions Under Discussion: Where Information Structure Meets Projective Content

Beaver, Roberts, Simons and Tonhauser call a content at-issue when it has obligatory local effect
and entails that some possible answer to the question under discussion is false, and hypothesize
that content under an entailment-cancelling operator projects if and only if it is not at-issue.
The definition simplifies that of Simons, Tonhauser, Beaver and Roberts, on which a content is
at-issue when the question whether it holds is relevant: [the earlier notion is the
weaker](##BeaverEtAl2017.exists_excludes_compl_and_not_excludes), since it also counts a content
whose negation excludes an answer. A content that every answer contextually entails [excludes
none](##BeaverEtAl2017.not_excludes_of_forall_alt), so neither what the common ground entails nor
what the current question entails is at-issue, while a contingent content with obligatory local
effect [is at-issue for the question whether it holds](##BeaverEtAl2017.atIssue_polar).

## Implementation notes

* Entailment is relative to a context set, as in the earlier paper's relevance and in the
  argument the paper gives from the common ground.
* Obligatory local effect is the property of Tonhauser, Beaver, Roberts and Simons, stated for
  the contexts in which a belief report with the trigger in its complement is acceptable.
* Whether a content projects is not defined, and the Projection Principle is not a hypothesis
  of any theorem. The earlier paper's revised definition, by what the speaker intends to
  address, is not formalized.

## References

* [beaver-roberts-simons-tonhauser-2017]
* [simons-tonhauser-beaver-roberts-2010]
* [simons-beaver-roberts-tonhauser-2016]
* [tonhauser-beaver-roberts-simons-2013]
* [roberts-2012]
-/

@[expose] public section

namespace BeaverEtAl2017

open Question TonhauserEtAl2013

variable {W : Type*} {Q : Question W} {c m : Set W}

/-! ### Excluding an answer -/

/-- In the context `c`, the content `m` entails that some possible answer to the question is
false: the second condition of (32), and a partial answer as [simons-tonhauser-beaver-roberts-2010]
gloss it, one that eliminates at least one alternative. -/
def Excludes (c m : Set W) (Q : Question W) : Prop := ∃ a ∈ alt Q, c ∩ m ⊆ aᶜ

theorem Excludes.partiallyAnsweredBy (h : Excludes c m Q) : PartiallyAnsweredBy Q (c ∩ m) :=
  let ⟨a, ha, hm⟩ := h; ⟨a, ha, .inr hm⟩

-- On a question with at least two mutually exclusive answers, excluding an answer is partially
-- answering in the sense of [roberts-2012], which also counts entailing one.
theorem partiallyAnsweredBy_iff_excludes (hQ : (alt Q).PairwiseDisjoint id)
    (h2 : (alt Q).Nontrivial) : PartiallyAnsweredBy Q (c ∩ m) ↔ Excludes c m Q := by
  refine ⟨?_, Excludes.partiallyAnsweredBy⟩
  rintro ⟨a, ha, h | h⟩
  · obtain ⟨b, hb, hne⟩ := h2.exists_ne a
    exact ⟨b, hb, fun x hx hxb ↦ Set.disjoint_left.1 (hQ hb ha hne) hxb (h hx)⟩
  · exact ⟨a, ha, h⟩

/-- A content that every answer contextually entails excludes no answer compatible with the
context. The content of the common ground, `c ⊆ m`, is one case, and a content the current
question entails, each of its answers entailing it, is the other. -/
theorem not_excludes_of_forall_alt (h : ∀ a ∈ alt Q, c ∩ a ⊆ m)
    (hQ : ∀ a ∈ alt Q, (c ∩ a).Nonempty) : ¬ Excludes c m Q := by
  rintro ⟨a, ha, hm⟩
  obtain ⟨w, hw⟩ := hQ a ha
  exact hm ⟨hw.1, h a ha hw⟩ hw.2

theorem excludes_polar (hne : m.Nonempty) (hnu : m ≠ Set.univ) : Excludes c m (polar m) :=
  ⟨mᶜ, by simp [alt_polar_of_nontrivial hne.ne_empty hnu],
    Set.inter_subset_right.trans (compl_compl m).ge⟩

/-- By (14) of [simons-tonhauser-beaver-roberts-2010] a content is at-issue when the question
whether it holds is relevant, that is when the content or its negation excludes an answer. The
negation can do so where the content does not, and (32) then calls the content not at-issue. -/
theorem exists_excludes_compl_and_not_excludes :
    ∃ (Q : Question (Fin 3)) (m : Set (Fin 3)),
      Excludes Set.univ mᶜ Q ∧ ¬ Excludes Set.univ m Q := by
  have halt : alt (ofSet ({0} : Set (Fin 3)) ⊔ ofSet {1, 2}) = {{0}, {1, 2}} :=
    alt_ofSet_sup_ofSet (by simp) (by simp [Set.subset_def])
  refine ⟨ofSet {0} ⊔ ofSet {1, 2}, {0, 1}, ⟨{0}, by simp [halt], ?_⟩, ?_⟩
  · rintro x ⟨-, hx⟩ rfl
    exact hx (by simp)
  · rintro ⟨a, ha, h⟩
    rw [halt] at ha
    rcases ha with rfl | rfl
    · exact h (a := 0) (by simp) rfl
    · exact h (a := 1) (by simp) (by simp)

/-! ### At-issueness -/

variable {R : SetRel W W} {Acc : Set W → Prop}

/-- (32): the content `m` is at-issue relative to the question under discussion `Q` in the
context `c`. -/
structure AtIssue (R : SetRel W W) (Acc : Set W → Prop) (c m : Set W) (Q : Question W) :
    Prop where
  /-- The content contributes to the ordinary semantics of its clause. -/
  localEffect : ObligatoryLocalEffect R m Acc
  /-- The content entails that some possible answer to the question is false. -/
  excludes : Excludes c m Q

/-- A contingent content with obligatory local effect is at-issue for the question whether it
holds. -/
theorem atIssue_polar (h : ObligatoryLocalEffect R m Acc) (hne : m.Nonempty)
    (hnu : m ≠ Set.univ) : AtIssue R Acc c m (polar m) :=
  ⟨h, excludes_polar hne hnu⟩

end BeaverEtAl2017
