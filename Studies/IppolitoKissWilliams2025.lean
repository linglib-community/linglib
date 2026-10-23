module

public import Studies.IppolitoKissWilliams2022

/-!
# Ippolito, Kiss and Williams (2025): Discourse *only*

This file formalizes [ippolito-kiss-williams-2025], the account of discourse *only*, the
particle of *the house is beautiful, only it's too expensive* whose prejacent may be a
declarative, an interrogative, an imperative or an exclamative. Support, agreement and
disagreement are those of [ippolito-kiss-williams-2022], with sentences of every clause type
denoting sets of propositions, (13) to (15). A context (`Context`) adds the true partial
answers to the question under discussion established in the discourse, and the meaning (16)
has a definedness condition, that both arguments are relevant and the left argument supports
an answer (`Context.Defined`), and a conventional implicature (`Context.CI`): some answer that
every established partial answer other than the prejacent supports and the prejacent does not.
A canonical question, none of whose answers the speaker believes, supports nothing, so it
cannot be the left argument, (19) and (6), while as prejacent it satisfies the second clause of
the implicature, (18); a rhetorical or otherwise committed question can be the left argument,
(20) and (21). The house-buying context of Section 5 is built explicitly and the declarative
and interrogative cases derived in it.

## Implementation notes

* The paper's first clause of the implicature quantifies over every true partial answer outside
  the question under discussion; its prose excludes the prejacent, which the formal statement
  would contradict, so the exclusion is built in as `p ∉ alt S'`.
* The implicature "ensures lack of agreement" between the arguments only when the left argument
  supports no answer but the implicature's, which `not_agree_of_ci` assumes.
* The cross-linguistic distribution of Section 7 (Italian *solo che*, Russian *tol'ko*,
  Hungarian *csak* and *csakhogy*, Mandarin *zhǐshì*) and the weight asymmetry of Section 6 are
  recorded as example rows; the paper derives from the semantics only that a left-argument
  question must be non-canonical.

## References

* [ippolito-kiss-williams-2025]
* [ippolito-kiss-williams-2022]
* [roberts-2012]
* [anscombre-ducrot-1977]
-/

@[expose] public section

namespace IppolitoKissWilliams2025

open Question IppolitoKissWilliams2022

variable {W : Type*}

/-- A context for discourse *only*: the context of [ippolito-kiss-williams-2022] with the true
partial answers to the question under discussion established in the discourse. -/
structure Context (W : Type*) extends IppolitoKissWilliams2022.Context W where
  partialAnswers : Set (Set W)

namespace Context

variable (c : Context W)

/-- (16), definedness: both arguments are relevant to the question under discussion and the
left argument supports one of its answers. -/
def Defined (S S' : Question W) : Prop :=
  S.IsRelevantTo c.issues ∧ S'.IsRelevantTo c.issues ∧ ∃ α ∈ alt c.qud, c.QSupports S α

/-- (16), the conventional implicature: some answer to the question under discussion that every
established true partial answer outside the question and other than the prejacent supports,
and the prejacent does not. -/
def CI (S' : Question W) : Prop :=
  ∃ α ∈ alt c.qud,
    (∀ p ∈ c.partialAnswers, p ∉ alt c.qud → p ∉ alt S' → c.Supports p α) ∧ ¬ c.QSupports S' α

variable {c} {S S' : Question W}

/-- Section 5.2, (19b) and (6a): a left argument none of whose answers the speaker believes, a
canonical question, leaves the sentence undefined. -/
theorem not_defined_of_no_belief (h : ∀ q ∈ alt S, ¬ c.dox ⊆ q) : ¬ c.Defined S S' :=
  λ ⟨_, _, α, _, hα⟩ => Context.not_qSupports_of_no_belief h α hα

/-- (18): a canonical question as prejacent satisfies the second clause of the implicature for
every answer, so the implicature reduces to its first clause. -/
theorem ci_iff_of_no_belief (h : ∀ q ∈ alt S', ¬ c.dox ⊆ q) :
    c.CI S' ↔ ∃ α ∈ alt c.qud,
      ∀ p ∈ c.partialAnswers, p ∉ alt c.qud → p ∉ alt S' → c.Supports p α :=
  ⟨λ ⟨α, hα, h₁, _⟩ => ⟨α, hα, h₁⟩,
    λ ⟨α, hα, h₁⟩ => ⟨α, hα, h₁, Context.not_qSupports_of_no_belief h α⟩⟩

theorem not_agree_of_ci {α : Set W} (hS' : ¬ c.QSupports S' α)
    (hS : ∀ r ∈ alt c.qud, c.QSupports S r → r = α) :
    ¬ c.Agree (c.QSupports S) (c.QSupports S') :=
  λ ⟨r, hr, hSr, hS'r⟩ => hS' (hS r hr hSr ▸ hS'r)

/-- Section 5.1: when the prejacent supports an answer of its own, the arguments disagree, the
special case of lack of agreement. -/
theorem disagree_of_ci {α : Set W} (hα : α ∈ alt c.qud) (hSα : c.QSupports S α)
    (hS' : ¬ c.QSupports S' α) (hS : ∀ r ∈ alt c.qud, c.QSupports S r → r = α)
    (hS'' : ∃ r ∈ alt c.qud, c.QSupports S' r) :
    c.Disagree (c.QSupports S) (c.QSupports S') :=
  ⟨⟨α, hα, hSα⟩, hS'', not_agree_of_ci hS' hS⟩

/-- (18) and the prose of Section 5.2: with a canonical question as prejacent the arguments
neither agree nor disagree. -/
theorem weak_non_agreement (h : ∀ q ∈ alt S', ¬ c.dox ⊆ q) :
    ¬ c.Agree (c.QSupports S) (c.QSupports S') ∧ ¬ c.Disagree (c.QSupports S) (c.QSupports S') :=
  ⟨λ ⟨r, _, _, hr⟩ => Context.not_qSupports_of_no_belief h r hr,
    λ ⟨_, ⟨r, _, hr⟩, _⟩ => Context.not_qSupports_of_no_belief h r hr⟩

end Context

/-! ### The house-buying context of Section 5 -/

namespace House

/-- A world: whether the house is beautiful, expensive, affordable, and to be bought. -/
structure World where
  beautiful : Bool
  expensive : Bool
  afford : Bool
  buy : Bool
  deriving DecidableEq

/-- The house is beautiful. -/
def beautiful : Set World := {w | w.beautiful}

/-- The house is expensive. -/
def expensive : Set World := {w | w.expensive}

/-- We can afford the house. -/
def afford : Set World := {w | w.afford}

/-- We should buy the house. -/
def buy : Set World := {w | w.buy}

/-- The evidence of Section 5.1: beauty for buying, expense against. -/
def Evidence (p r : Set World) : Prop := (p = beautiful ∧ r = buy) ∨ (p = expensive ∧ r = buyᶜ)

/-- The context of (17): whether to buy the house is under discussion, with its beauty, its
price and its affordability as subquestions; the speaker believes the house beautiful and
expensive, and both are established partial answers. -/
def ctx₁₇ : Context World where
  qud := polar buy
  subquestions := {polar beautiful, polar expensive, polar afford}
  dox := beautiful ∩ expensive
  salient := {beautiful}
  Evidence := Evidence
  partialAnswers := {beautiful, expensive}

/-- The context of (18): only the beauty of the house has been established. -/
def ctx₁₈ : Context World := { ctx₁₇ with partialAnswers := {beautiful} }

/-- The context of (6a) and (19b): a speaker neutral about the house's beauty. -/
def ctxNeutral : Context World := { ctx₁₇ with dox := expensive }

private theorem ne_of_mem {p : Set World} {w : World} (hw : w ∈ p) : p ≠ ∅ := λ h =>
  by simp [h] at hw

private theorem ne_univ_of_notMem {p : Set World} {w : World} (hw : w ∉ p) : p ≠ Set.univ :=
  λ h => hw (h ▸ Set.mem_univ w)

private theorem buy_ne_compl : buy ≠ buyᶜ := λ h =>
  by simpa [buy] using Set.ext_iff.1 h ⟨false, false, false, true⟩

private theorem beautiful_ne_expensive : beautiful ≠ expensive := λ h =>
  by simpa [beautiful, expensive] using Set.ext_iff.1 h ⟨true, false, false, false⟩

private theorem mem_alt_polar_beautiful (q : Set World) :
    q ∈ alt (polar beautiful) ↔ q = beautiful ∨ q = beautifulᶜ :=
  mem_alt_polar_of_nontrivial
    (ne_of_mem (show (⟨true, false, false, false⟩ : World) ∈ beautiful by simp [beautiful]))
    (ne_univ_of_notMem
      (show (⟨false, false, false, false⟩ : World) ∉ beautiful by simp [beautiful])) q

private theorem mem_alt_polar_afford (q : Set World) :
    q ∈ alt (polar afford) ↔ q = afford ∨ q = affordᶜ :=
  mem_alt_polar_of_nontrivial (ne_of_mem (show (⟨false, false, true, false⟩ : World) ∈ afford
    by simp [afford])) (ne_univ_of_notMem (show (⟨false, false, false, false⟩ : World) ∉ afford
    by simp [afford])) q

private theorem mem_alt_polar_buy (q : Set World) : q ∈ alt (polar buy) ↔ q = buy ∨ q = buyᶜ :=
  mem_alt_polar_of_nontrivial
    (ne_of_mem (show (⟨false, false, false, true⟩ : World) ∈ buy by simp [buy]))
    (ne_univ_of_notMem (show (⟨false, false, false, false⟩ : World) ∉ buy by simp [buy])) q

private theorem buy_mem_alt : buy ∈ alt (polar buy) := (mem_alt_polar_buy _).2 (Or.inl rfl)

private theorem relevant_beautiful : (ofSet beautiful).IsRelevantTo ctx₁₇.issues :=
  ⟨beautiful, by simp, polar beautiful, by simp [IppolitoKissWilliams2022.Context.issues, ctx₁₇],
    partiallyAnsweredBy_of_mem_alt ((mem_alt_polar_beautiful _).2 (Or.inl rfl))⟩

private theorem relevant_expensive : (ofSet expensive).IsRelevantTo ctx₁₇.issues :=
  ⟨expensive, by simp, polar expensive, by simp [IppolitoKissWilliams2022.Context.issues, ctx₁₇],
    partiallyAnsweredBy_of_mem_alt ((mem_alt_polar_of_nontrivial
      (ne_of_mem (show (⟨false, true, false, false⟩ : World) ∈ expensive by simp [expensive]))
      (ne_univ_of_notMem (show (⟨false, false, false, false⟩ : World) ∉ expensive
        by simp [expensive])) _).2 (Or.inl rfl))⟩

private theorem relevant_afford : (polar afford).IsRelevantTo ctx₁₇.issues :=
  ⟨afford, (mem_alt_polar_afford _).2 (Or.inl rfl), polar afford,
    by simp [IppolitoKissWilliams2022.Context.issues, ctx₁₇],
    partiallyAnsweredBy_of_mem_alt ((mem_alt_polar_afford _).2 (Or.inl rfl))⟩

/-- The speaker of (17) supports buying by the house's beauty. -/
private theorem supports_beautiful : ctx₁₇.QSupports (ofSet beautiful) buy :=
  ⟨beautiful, by simp, Set.inter_subset_left, Or.inl ⟨rfl, rfl⟩⟩

private theorem not_evidence_expensive_buy : ¬ Evidence expensive buy := by
  rintro (⟨h, -⟩ | ⟨-, h⟩)
  · exact beautiful_ne_expensive h.symm
  · exact buy_ne_compl h

/-- The speaker of (17) does not support buying by the house's expense. -/
private theorem not_qSupports_expensive_buy : ¬ ctx₁₇.QSupports (ofSet expensive) buy := by
  rintro ⟨q, hq, -, hev⟩
  simp only [alt_ofSet, Set.mem_singleton_iff] at hq
  exact not_evidence_expensive_buy (hq ▸ hev)

/-- (17): *the house is beautiful, only it's too expensive* is defined. -/
theorem defined₁₇ : ctx₁₇.Defined (ofSet beautiful) (ofSet expensive) :=
  ⟨relevant_beautiful, relevant_expensive, buy, buy_mem_alt, supports_beautiful⟩

/-- (17): its implicature holds with buying as the answer beauty supports and expense does
not. -/
theorem ci₁₇ : ctx₁₇.CI (ofSet expensive) := by
  refine ⟨buy, buy_mem_alt, ?_, ?_⟩
  · intro p hp _ hp'
    simp only [ctx₁₇, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    simp only [alt_ofSet, Set.mem_singleton_iff] at hp'
    rcases hp with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd rfl hp'
  · exact not_qSupports_expensive_buy

/-- (17): the two arguments disagree, expense supporting not buying. -/
theorem disagree₁₇ :
    ctx₁₇.Disagree (ctx₁₇.QSupports (ofSet beautiful)) (ctx₁₇.QSupports (ofSet expensive)) := by
  refine Context.disagree_of_ci buy_mem_alt supports_beautiful not_qSupports_expensive_buy ?_ ?_
  · rintro r _ ⟨q, hq, -, hev⟩
    simp only [alt_ofSet, Set.mem_singleton_iff] at hq
    subst hq
    rcases hev with ⟨-, rfl⟩ | ⟨h, -⟩
    · rfl
    · exact absurd h beautiful_ne_expensive
  · exact ⟨buyᶜ, (mem_alt_polar_buy _).2 (Or.inr rfl), expensive, by simp,
      Set.inter_subset_right, Or.inr ⟨rfl, rfl⟩⟩

/-- The speaker of (18) is neutral about affordability. -/
private theorem no_belief_afford : ∀ q ∈ alt (polar afford), ¬ ctx₁₈.dox ⊆ q := by
  intro q hq h
  rw [mem_alt_polar_afford] at hq
  rcases hq with rfl | rfl
  · exact absurd (h (show (⟨true, true, false, false⟩ : World) ∈ ctx₁₈.dox
      by simp [ctx₁₈, ctx₁₇, beautiful, expensive])) (by simp [afford])
  · exact absurd (h (show (⟨true, true, true, false⟩ : World) ∈ ctx₁₈.dox
      by simp [ctx₁₈, ctx₁₇, beautiful, expensive])) (by simp [afford])

/-- (18): *the house is beautiful, only can we afford it?* is defined and carries its
implicature, the canonical question supporting nothing. -/
theorem defined_ci₁₈ :
    ctx₁₈.Defined (ofSet beautiful) (polar afford) ∧ ctx₁₈.CI (polar afford) := by
  refine ⟨⟨relevant_beautiful, relevant_afford, buy, buy_mem_alt, supports_beautiful⟩, ?_⟩
  rw [Context.ci_iff_of_no_belief no_belief_afford]
  refine ⟨buy, buy_mem_alt, λ p hp _ _ => ?_⟩
  simp only [ctx₁₈, Set.mem_singleton_iff] at hp
  exact hp ▸ Or.inl ⟨rfl, rfl⟩

/-- (18): the arguments neither agree nor disagree. -/
theorem weak₁₈ :
    ¬ ctx₁₈.Agree (ctx₁₈.QSupports (ofSet beautiful)) (ctx₁₈.QSupports (polar afford)) ∧
      ¬ ctx₁₈.Disagree (ctx₁₈.QSupports (ofSet beautiful)) (ctx₁₈.QSupports (polar afford)) :=
  Context.weak_non_agreement no_belief_afford

/-- (6a) and (19b): a speaker neutral about the house's beauty cannot ask whether it is
beautiful as the left argument. -/
theorem not_defined_neutral : ¬ ctxNeutral.Defined (polar beautiful) (ofSet expensive) := by
  refine Context.not_defined_of_no_belief λ q hq h => ?_
  rw [mem_alt_polar_beautiful] at hq
  rcases hq with rfl | rfl
  · exact absurd (h (show (⟨false, true, false, false⟩ : World) ∈ ctxNeutral.dox
      by simp [ctxNeutral, ctx₁₇, expensive])) (by simp [beautiful])
  · exact absurd (h (show (⟨true, true, false, false⟩ : World) ∈ ctxNeutral.dox
      by simp [ctxNeutral, ctx₁₇, expensive])) (by simp [beautiful])

/-- (6b) and (21): read rhetorically, by a speaker committed to the house's beauty, the same
question is a fine left argument. -/
theorem defined_rhetorical : ctx₁₇.Defined (polar beautiful) (ofSet expensive) :=
  ⟨⟨beautiful, (mem_alt_polar_beautiful _).2 (Or.inl rfl), polar beautiful,
      by simp [IppolitoKissWilliams2022.Context.issues, ctx₁₇],
      partiallyAnsweredBy_of_mem_alt ((mem_alt_polar_beautiful _).2 (Or.inl rfl))⟩,
    relevant_expensive, buy, buy_mem_alt, beautiful, (mem_alt_polar_beautiful _).2 (Or.inl rfl),
    Set.inter_subset_left, Or.inl ⟨rfl, rfl⟩⟩

end House

end IppolitoKissWilliams2025
