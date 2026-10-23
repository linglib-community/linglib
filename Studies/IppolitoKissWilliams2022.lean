module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Resolution

/-!
# Ippolito, Kiss and Williams (2022): The Discourse Function of Adversative Conjunction

This file formalizes [ippolito-kiss-williams-2022], the account of Italian *ma* and English
*but* introducing a single declarative or interrogative clause. A context (`Context`) fixes the
question under discussion, the speaker's doxastic state, the propositions made salient by
previous moves, and the evidence relation of [buring-gunlogson-2000] and [gunlogson-2008] that
the paper leaves informal. A salient proposition supports an answer to the question under
discussion when it provides evidence for it, (15) (`Context.Supports`); a question uttered by
the speaker supports an answer when some answer to it that the speaker believes provides
evidence for it, (21) (`Context.QSupports`). Two moves agree when they support a common answer
and disagree when each supports an answer but no common one, (16), (17), (22) and (23).
Discourse *ma* requires a salient relevant proposition that does not agree with its argument,
(18) and (24) (`Context.Ma`), and *but* one that disagrees with it, (29) and (34)
(`Context.But`). The table of question types follows: with nothing salient neither particle is
licensed; a question none of whose answers the speaker believes, on the ignorance reading or
with the negative bias, supports nothing, so *ma* is licensed by any salient relevant
proposition and *but* by none; and a negative polar question whose believed answer supports the
opposite answer from the salient proposition disagrees with it and licenses both.

## Implementation notes

* Relevance to the question under discussion, which the paper does not define, is the
  substrate's `Question.IsRelevantTo` to the question under discussion together with the
  subquestions of its strategy, as the sequel [ippolito-kiss-williams-2025] assumes.
* A declarative argument of *ma* or *but* is asserted, so its support is that of the singleton
  question: belief plus evidence (Section 3.2.3).
* The amended notion of support (45), on which the interrogative speech act itself provides
  evidence, is not formalized.

## References

* [ippolito-kiss-williams-2022]
* [buring-gunlogson-2000]
* [gunlogson-2008]
* [roberts-2012]
-/

@[expose] public section

namespace IppolitoKissWilliams2022

open Question

variable {W : Type*}

/-- A discourse context: the question under discussion, the subquestions of its strategy, the
speaker's doxastic state, the propositions made salient by previous verbal or non-verbal moves,
and the evidence relation, `Evidence p r` when `p` provides evidence for `r` in the context. -/
structure Context (W : Type*) where
  qud : Question W
  subquestions : Set (Question W)
  dox : Set W
  salient : Set (Set W)
  Evidence : Set W → Set W → Prop

namespace Context

variable (c : Context W)

/-- The questions a move must be relevant to: the question under discussion and the
subquestions of its strategy. -/
def issues : Set (Question W) := insert c.qud c.subquestions

/-- (15): a proposition supports an answer to the question under discussion when it provides
evidence for it. -/
def Supports (p r : Set W) : Prop := c.Evidence p r

/-- (21): a question uttered by the speaker supports an answer when some answer to it that the
speaker believes provides evidence for it. -/
def QSupports (S : Question W) (r : Set W) : Prop := ∃ q ∈ alt S, c.dox ⊆ q ∧ c.Evidence q r

/-- (16) and (22): two moves, given by what they support, agree when they support a common
answer to the question under discussion. -/
def Agree (s t : Set W → Prop) : Prop := ∃ r ∈ alt c.qud, s r ∧ t r

/-- (17) and (23): two moves disagree when each supports an answer but no common one. -/
def Disagree (s t : Set W → Prop) : Prop :=
  (∃ r ∈ alt c.qud, s r) ∧ (∃ r ∈ alt c.qud, t r) ∧ ¬ c.Agree s t

/-- (18) and (24): discourse *ma* with a declarative or interrogative argument is defined when
the argument is relevant and some salient relevant proposition does not agree with it. -/
def Ma (S : Question W) : Prop :=
  S.IsRelevantTo c.issues ∧
    ∃ p ∈ c.salient, (ofSet p).IsRelevantTo c.issues ∧ ¬ c.Agree (c.Supports p) (c.QSupports S)

/-- (29) and (34): discourse *but* is defined when some salient relevant proposition disagrees
with its argument. -/
def But (S : Question W) : Prop :=
  S.IsRelevantTo c.issues ∧
    ∃ p ∈ c.salient, (ofSet p).IsRelevantTo c.issues ∧ c.Disagree (c.Supports p) (c.QSupports S)

variable {c} {s t : Set W → Prop} {S : Question W}

theorem Agree.symm (h : c.Agree s t) : c.Agree t s :=
  let ⟨r, hr, hs, ht⟩ := h
  ⟨r, hr, ht, hs⟩

theorem Disagree.symm (h : c.Disagree s t) : c.Disagree t s :=
  ⟨h.2.1, h.1, λ h' => h.2.2 h'.symm⟩

/-- Disagreement is the stronger relation. -/
theorem Disagree.not_agree (h : c.Disagree s t) : ¬ c.Agree s t := h.2.2

theorem Ma.of_but (h : c.But S) : c.Ma S :=
  let ⟨hS, p, hp, hr, hd⟩ := h
  ⟨hS, p, hp, hr, hd.not_agree⟩

/-- A declarative argument supports an answer when the speaker believes it and it provides
evidence for the answer (Section 3.2.3). -/
@[simp] theorem qSupports_ofSet_iff {q r : Set W} :
    c.QSupports (ofSet q) r ↔ c.dox ⊆ q ∧ c.Evidence q r := by
  simp [QSupports]

theorem not_qSupports_of_no_belief (h : ∀ q ∈ alt S, ¬ c.dox ⊆ q) (r : Set W) :
    ¬ c.QSupports S r :=
  λ ⟨q, hq, hd, _⟩ => h q hq hd

/-- Out of the blue, with nothing salient, *ma* is not licensed (BAKERY, (7) and (36)). -/
theorem not_ma_of_salient_empty (h : c.salient = ∅) : ¬ c.Ma S :=
  λ ⟨_, p, hp, _⟩ => by simp [h] at hp

theorem not_but_of_salient_empty (h : c.salient = ∅) : ¬ c.But S :=
  λ hb => not_ma_of_salient_empty h (Ma.of_but hb)

/-- With a question the speaker has no belief about, *ma* is licensed by any salient relevant
proposition: HELP, TWIN SISTERS, NIGHT and KEY, (26), (27), (28) and (35). -/
theorem ma_of_no_belief (hS : S.IsRelevantTo c.issues) (h : ∀ q ∈ alt S, ¬ c.dox ⊆ q) {p : Set W}
    (hp : p ∈ c.salient) (hr : (ofSet p).IsRelevantTo c.issues) : c.Ma S :=
  ⟨hS, p, hp, hr, λ ⟨r, _, _, hq⟩ => not_qSupports_of_no_belief h r hq⟩

/-- With such a question *but* is never licensed: (31), (32), (33) and (37). -/
theorem not_but_of_no_belief (h : ∀ q ∈ alt S, ¬ c.dox ⊆ q) : ¬ c.But S :=
  λ ⟨_, _, _, _, _, ⟨r, _, hq⟩, _⟩ => not_qSupports_of_no_belief h r hq

/-- The second argument of Section 3.3, (38): a question biased toward an answer that supports
what every salient proposition supports agrees with them all, and *ma* is not licensed. -/
theorem not_ma_of_agree (h : ∀ p ∈ c.salient, c.Agree (c.Supports p) (c.QSupports S)) :
    ¬ c.Ma S :=
  λ ⟨_, p, hp, _, hn⟩ => hn (h p hp)

/-- VEGETARIAN, (25) and (30): with a polar question under discussion, a salient proposition
supporting one answer and a question whose believed answers support the other disagree, so both
particles are licensed. -/
theorem but_of_polar {α : Set W} (hqud : c.qud = polar α) (hne : α ≠ ∅) (hnu : α ≠ Set.univ)
    (hS : S.IsRelevantTo c.issues) {p : Set W} (hp : p ∈ c.salient)
    (hr : (ofSet p).IsRelevantTo c.issues) (hpα : c.Evidence p α) (hpα' : ¬ c.Evidence p αᶜ)
    (hq : ∃ q ∈ alt S, c.dox ⊆ q)
    (hS' : ∀ q ∈ alt S, c.dox ⊆ q → c.Evidence q αᶜ ∧ ¬ c.Evidence q α) : c.But S := by
  refine ⟨hS, p, hp, hr, ?_, ?_, ?_⟩
  · exact ⟨α, by simp [hqud, alt_polar_of_nontrivial hne hnu], hpα⟩
  · obtain ⟨q, hq, hd⟩ := hq
    exact ⟨αᶜ, by simp [hqud, alt_polar_of_nontrivial hne hnu], q, hq, hd, (hS' q hq hd).1⟩
  · rintro ⟨r, hr, hpr, q, hq, hd, hqr⟩
    simp only [hqud, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact (hS' q hq hd).2 hqr
    · exact hpα' hpr

theorem ma_of_polar {α : Set W} (hqud : c.qud = polar α) (hne : α ≠ ∅) (hnu : α ≠ Set.univ)
    (hS : S.IsRelevantTo c.issues) {p : Set W} (hp : p ∈ c.salient)
    (hr : (ofSet p).IsRelevantTo c.issues) (hpα : c.Evidence p α) (hpα' : ¬ c.Evidence p αᶜ)
    (hq : ∃ q ∈ alt S, c.dox ⊆ q)
    (hS' : ∀ q ∈ alt S, c.dox ⊆ q → c.Evidence q αᶜ ∧ ¬ c.Evidence q α) : c.Ma S :=
  Ma.of_but (but_of_polar hqud hne hnu hS hp hr hpα hpα' hq hS')

end Context

/-! ### VEGETARIAN, (25) and (30) -/

namespace Vegetarian

/-- A world: whether Mia was vegetarian, has ordered a steak, and will eat meat. -/
structure World where
  veg : Bool
  steak : Bool
  meat : Bool
  deriving DecidableEq

/-- Mia was vegetarian. -/
def veg : Set World := {w | w.veg}

/-- Mia has ordered a steak. -/
def steak : Set World := {w | w.steak}

/-- Mia will eat meat. -/
def meat : Set World := {w | w.meat}

/-- Carla's context: whether Mia will eat meat is under discussion, with whether she was
vegetarian and whether she ordered a steak as subquestions; Carla believes Mia was vegetarian;
the steak order is salient; the order is evidence that Mia will eat meat and vegetarianism
evidence that she will not. -/
def ctx : Context World where
  qud := polar meat
  subquestions := {polar veg, polar steak}
  dox := veg
  salient := {steak}
  Evidence p r := (p = steak ∧ r = meat) ∨ (p = veg ∧ r = meatᶜ)

private theorem meat_ne_empty : meat ≠ ∅ := λ h =>
  by simpa [meat] using Set.ext_iff.1 h ⟨false, false, true⟩

private theorem meat_ne_univ : meat ≠ Set.univ := λ h =>
  by simpa [meat] using Set.ext_iff.1 h ⟨false, false, false⟩

private theorem veg_ne_empty : veg ≠ ∅ := λ h =>
  by simpa [veg] using Set.ext_iff.1 h ⟨true, false, false⟩

private theorem veg_ne_univ : veg ≠ Set.univ := λ h =>
  by simpa [veg] using Set.ext_iff.1 h ⟨false, false, false⟩

private theorem steak_ne_veg : steak ≠ veg := λ h =>
  by simpa [steak, veg] using Set.ext_iff.1 h ⟨false, true, false⟩

private theorem meat_ne_compl : meat ≠ meatᶜ := λ h =>
  by simpa [meat] using Set.ext_iff.1 h ⟨false, false, true⟩

theorem but : ctx.But (polar veg) := by
  refine Context.but_of_polar rfl meat_ne_empty meat_ne_univ ?_ rfl ?_ (Or.inl ⟨rfl, rfl⟩) ?_ ?_ ?_
  · exact ⟨veg, mem_alt_polar_of_nontrivial veg_ne_empty veg_ne_univ veg |>.2 (Or.inl rfl),
      polar veg, by simp [Context.issues, ctx], partiallyAnsweredBy_of_mem_alt
        (mem_alt_polar_of_nontrivial veg_ne_empty veg_ne_univ veg |>.2 (Or.inl rfl))⟩
  · exact ⟨steak, by simp, polar steak, by simp [Context.issues, ctx],
      partiallyAnsweredBy_of_mem_alt (mem_alt_polar_of_nontrivial
        (λ h => by simpa [steak] using Set.ext_iff.1 h ⟨false, true, false⟩)
        (λ h => by simpa [steak] using Set.ext_iff.1 h ⟨false, false, false⟩) steak |>.2
        (Or.inl rfl))⟩
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact meat_ne_compl h.symm
    · exact steak_ne_veg h
  · exact ⟨veg, mem_alt_polar_of_nontrivial veg_ne_empty veg_ne_univ veg |>.2 (Or.inl rfl),
      subset_rfl⟩
  · intro q hq hd
    rw [mem_alt_polar_of_nontrivial veg_ne_empty veg_ne_univ] at hq
    rcases hq with rfl | rfl
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact steak_ne_veg h.symm
      · exact meat_ne_compl h
    · exact absurd (hd (show (⟨true, false, false⟩ : World) ∈ veg by simp [veg])) (by simp [veg])

theorem ma : ctx.Ma (polar veg) := Context.Ma.of_but but

end Vegetarian

end IppolitoKissWilliams2022
