module

public import Linglib.Semantics.Questions.Polar
public import Linglib.Semantics.Questions.Resolution
public import Linglib.Data.Examples.Umbach2004

/-!
# Umbach (2004): On the Notion of Contrast in Information Structure and Discourse Structure

This file formalizes [umbach-2004]'s decomposition of contrast. The alternatives a focus evokes
must be comparable, similar and dissimilar at once: following [lang-1984]'s conditions on
coordination, no alternative subsumes another, `SemanticallyIndependent`, and a common
integrator subsumes them all, `CommonIntegrator`, together `WellFormedAlts`, which rules out
*drink* beside *martini*, (9a) and (10a), `not_wellFormedAlts_of_subset`, and keeps the singular
individuals out of the alternatives of a focused coordination, Krifka's problem. This is the
contrast of any focus, in the sense of [rooth-1992]. A contrastive focus in the sense of
[chafe-1976] and [kiss-1998] adds exclusion, of which there are two varieties with different
presuppositions, (14): a contrastive focus presupposes that some alternative satisfies the
predicate and asserts that it is the focused one, excluding the others *instead of* it,
`instead`, whereas an *only*-phrase presupposes the focused alternative and excludes the others
*in addition to* it, `inAddition`, [horn-1969]. The two convey the same total content,
`instead_content_eq_inAddition_content`, and differ in what they presuppose,
`presupposition_inAddition_eq_assertion_instead`. In discourse, *but* is focus-sensitive, (16), and
answers a conjunctive question by confirming one part and denying the other, (17), the
confirm+deny condition, `ConfirmDeny`: such an answer resolves the conjunctive question,
`mem_polar_inf_polar_of_confirmDeny`, and its content is that of the corresponding
*only*-phrase, (19) and (20), `confirmDeny_content_eq_inAddition`. CONTRAST and CORRECTION,
(24) and (25), differ as the two exclusions do: the contrastive *but* excludes the second
alternative in addition to the first, `contrastBut`, the corrective *but*, German *sondern*,
excludes the first alternative instead of the second, `correctionBut`, with the same assertion
and different licensing contexts, `contrastBut_content_eq_correctionBut_content`,
`presupposition_contrastBut`, `presupposition_correctionBut`.

## Implementation notes

Alternatives are propositions, sets of worlds, and a predicate over a set of alternatives is a
function to propositions; the presupposition of a contrastive focus is taken in the strengthened
form of footnote 8, that exactly one alternative satisfies the predicate. The implicit question
of a *but*-sentence is the meet of the polar questions of its conjuncts, following
[roberts-1998]'s implicit questions. The double-contrast cases (22) and the *it*-cleft data are
recorded as rows only. The examples are the rows of `Data.Examples.Umbach2004`.

## TODO

Footnote 12 observes that the contrastive counterfactual (24c), read as a no-yes sequence,
presupposes the second conjunct and prefers the yes-no reading; `presupposition_contrastBut`
follows the main text.

## References

* [umbach-2004]
* [lang-1984]
* [rooth-1992]
* [chafe-1976]
* [kiss-1998]
* [horn-1969]
* [roberts-1998]
-/

@[expose] public section

namespace Umbach2004

open Question

variable {W α : Type*}

/-! ### Similarity plus dissimilarity -/

/-- Two alternatives are semantically independent when neither subsumes the other. -/
def SemanticallyIndependent (a b : Set W) : Prop := ¬ a ⊆ b ∧ ¬ b ⊆ a

/-- A common integrator subsumes every alternative. -/
def CommonIntegrator (alts : Set (Set W)) (integ : Set W) : Prop := ∀ a ∈ alts, a ⊆ integ

/-- A well-formed alternative set is similar, under a common integrator, and dissimilar,
pairwise semantically independent. -/
def WellFormedAlts (alts : Set (Set W)) (integ : Set W) : Prop :=
  CommonIntegrator alts integ ∧ alts.Pairwise SemanticallyIndependent

theorem not_semanticallyIndependent_of_subset {a b : Set W} (h : a ⊆ b) :
    ¬ SemanticallyIndependent a b :=
  λ hi => hi.1 h

/-- (9a), (10a): an alternative set containing an alternative and one it subsumes is not
well-formed under any integrator. -/
theorem not_wellFormedAlts_of_subset {alts : Set (Set W)} {a b : Set W} (ha : a ∈ alts)
    (hb : b ∈ alts) (hne : a ≠ b) (h : a ⊆ b) (integ : Set W) : ¬ WellFormedAlts alts integ :=
  λ hw => not_semanticallyIndependent_of_subset h (hw.2 ha hb hne)

-- (9b)
theorem wellFormedAlts_pair_of_disjoint {a b : Set W} (ha : a.Nonempty) (hb : b.Nonempty)
    (hab : Disjoint a b) : WellFormedAlts {a, b} (a ∪ b) := by
  refine ⟨λ c hc => ?_, ?_⟩
  · rcases hc with rfl | rfl
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  · have hind : SemanticallyIndependent a b :=
      ⟨λ h => ha.ne_empty (hab.eq_bot_of_le h), λ h => hb.ne_empty (hab.symm.eq_bot_of_le h)⟩
    exact Set.pairwise_pair.2 λ _ => ⟨hind, ⟨hind.2, hind.1⟩⟩

/-! ### Two varieties of exclusion -/

/-- A presupposition with an assertion. -/
structure Exclusion (W : Type*) where
  presupposition : Set W
  assertion : Set W

/-- The total content of an exclusion. -/
def Exclusion.content (e : Exclusion W) : Set W := e.presupposition ∩ e.assertion

variable (P : α → Set W) (A : Set α) (a : α)

/-- The alternatives other than the focused one satisfy the predicate nowhere. -/
def noOther : Set W := ⋂ x ∈ A \ {a}, (P x)ᶜ

/-- (14a): a contrastive focus presupposes that exactly one alternative satisfies the predicate
and asserts that it is the focused one, excluding the others instead of it. -/
def instead : Exclusion W where
  presupposition := ⋃ x ∈ A, P x ∩ noOther P A x
  assertion := P a

/-- (14b): an *only*-phrase presupposes the focused alternative and asserts that no other
alternative satisfies the predicate, excluding the others in addition to it. -/
def inAddition : Exclusion W where
  presupposition := P a
  assertion := noOther P A a

variable {P A a}

theorem instead_content_eq_inAddition_content (ha : a ∈ A) :
    (instead P A a).content = (inAddition P A a).content := by
  ext w
  simp only [Exclusion.content, instead, inAddition, Set.mem_inter_iff, Set.mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨⟨x, hx, hwx, hno⟩, hwa⟩
    by_cases hxa : x = a
    · subst hxa
      exact ⟨hwa, hno⟩
    · exact absurd hwa (by
        simp only [noOther, Set.mem_iInter, Set.mem_compl_iff] at hno
        exact hno a ⟨ha, λ h => hxa (Set.mem_singleton_iff.1 h).symm⟩)
  · rintro ⟨hwa, hno⟩
    exact ⟨⟨a, ha, hwa, hno⟩, hwa⟩

theorem presupposition_inAddition_eq_assertion_instead :
    (inAddition P A a).presupposition = (instead P A a).assertion := rfl

/-! ### The discourse relation CONTRAST -/

/-- (17): the confirm+deny condition on a *but*-sentence answering the conjunctive question of
`q₁` and `q₂`: the first conjunct confirms `q₁` and the second denies `q₂`. -/
def ConfirmDeny (q₁ q₂ c₁ c₂ : Set W) : Prop := c₁ ⊆ q₁ ∧ c₂ ⊆ q₂ᶜ

-- (17b–d)
theorem not_confirmDeny_of_confirm_confirm {q₁ q₂ c₁ c₂ : Set W} (h₂ : c₂ ⊆ q₂)
    (hne : c₂.Nonempty) : ¬ ConfirmDeny q₁ q₂ c₁ c₂ :=
  λ h => hne.ne_empty (Set.subset_empty_iff.1 λ _ hw => (h.2 hw) (h₂ hw))

/-- A confirm+deny answer resolves the implicit conjunctive question, the meet of the two polar
questions, (18). -/
theorem mem_polar_inf_polar_of_confirmDeny {q₁ q₂ c₁ c₂ : Set W} (h : ConfirmDeny q₁ q₂ c₁ c₂) :
    c₁ ∩ c₂ ∈ polar q₁ ⊓ polar q₂ := by
  rw [mem_inf, mem_polar, mem_polar]
  exact ⟨Or.inl (Set.inter_subset_left.trans h.1), Or.inr (Set.inter_subset_right.trans h.2)⟩

/-- The content of a confirm+deny *but*-sentence is that of the *only*-phrase over the two
alternatives ((19), (20)). -/
theorem confirmDeny_content_eq_inAddition {a b : α} (hab : a ≠ b) :
    P a ∩ (P b)ᶜ = (inAddition P {a, b} a).content := by
  ext w
  simp only [Exclusion.content, inAddition, noOther, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hwa, hwb⟩
    refine ⟨hwa, λ x ⟨hx, hxa⟩ => ?_⟩
    rcases hx with hx | rfl
    · exact absurd hx hxa
    · exact hwb
  · rintro ⟨hwa, hno⟩
    exact ⟨hwa, hno b ⟨Or.inr rfl, hab.symm⟩⟩

/-! ### CONTRAST and CORRECTION -/

/-- (24a): the contrastive *but*, *John didn't go to Berlin but he went to Paris*, confirms the
second alternative and excludes the first in addition to it. -/
def contrastBut (P : α → Set W) (a b : α) : Exclusion W := inAddition P {a, b} a

/-- (25a): the corrective *but*, German *sondern*, *John didn't go to Berlin but to Paris*,
excludes the first alternative instead of the second. -/
def correctionBut (P : α → Set W) (a b : α) : Exclusion W := instead P {a, b} a

theorem contrastBut_content_eq_correctionBut_content {a b : α} :
    (contrastBut P a b).content = (correctionBut P a b).content :=
  (instead_content_eq_inAddition_content (Set.mem_insert a {b})).symm

/-- (24c): the contexts licensing a contrast are those where the confirmed alternative holds,
whether or not the denied one does too. -/
theorem presupposition_contrastBut (a b : α) : (contrastBut P a b).presupposition = P a := rfl

/-- A correction is licensed exactly in contexts where one of the two alternatives holds and the
other does not (25c). -/
theorem presupposition_correctionBut {a b : α} (hab : a ≠ b) :
    (correctionBut P a b).presupposition = symmDiff (P a) (P b) := by
  ext w
  simp only [correctionBut, instead, noOther, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
    Set.mem_symmDiff]
  constructor
  · rintro ⟨x, hx, hwx, hno⟩
    rcases hx with rfl | rfl
    · exact Or.inl ⟨hwx, hno b ⟨Or.inr rfl, hab.symm⟩⟩
    · exact Or.inr ⟨hwx, hno a ⟨Or.inl rfl, hab⟩⟩
  · rintro (⟨hwa, hwb⟩ | ⟨hwb, hwa⟩)
    · refine ⟨a, Or.inl rfl, hwa, λ x ⟨hx, hxa⟩ => ?_⟩
      rcases hx with hx | rfl
      · exact absurd hx hxa
      · exact hwb
    · refine ⟨b, Or.inr rfl, hwb, λ x ⟨hx, hxb⟩ => ?_⟩
      rcases hx with rfl | hx
      · exact hwa
      · exact absurd hx hxb

end Umbach2004
