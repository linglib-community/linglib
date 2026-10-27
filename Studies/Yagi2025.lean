module

public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Semantics.Dynamic.Partial

/-!
# Yagi (2025): Conflicting Presuppositions in Disjunction

This file formalizes Yagi's survey of disjunctions whose disjuncts carry contradictory
presuppositions (`Conflict`), *Either the King of Buganda is opening parliament or the
President of Buganda is conducting the ceremony*. Such a disjunction presupposes the
disjunction of the two presuppositions and is false when that holds and both disjuncts are
false. Four theories fail the second observation. Under Strong Kleene disjunction the sentence
is true whenever defined, so it is never false and its negation never true
(`sup_ne_neg_one`, `neg_sup_ne_one`); the symmetric two-dimensional disjunction in the
tradition of Karttunen and Peters has a presupposition that entails the assertion
(`orKPSymmetric_ne_neg_one`), and replacing it by the disjunction of the presuppositions
(`orPresupOr`) fixes the case but predicts a tautologous presupposition for *either baldness is
not hereditary or all of Bill's children are bald* (`orPresupOr_notAtIssue_of_left`); the update
semantics of Heim and Beaver, with failure as a designated state, is defined only when the
first disjunct already holds throughout the input, so it is uninformative wherever defined
(`mem_disj_iff`); and Schlenker's local contexts admit only worlds where one disjunct is
true (`local_contexts_force_truth`). Of the two reactions, Beaver and Krahmer's meta-assertion
operator makes the disjunction false, but also where neither presupposition holds, and leaves it
presuppositionless (`joinWeak_ofProp_eq_one_eq_neg_one_iff`, `joinWeak_ofProp_eq_one_ne_zero`);
inserting it on one disjunct under Strong Kleene yields only a conditional presupposition
(`sup_ofProp_eq_one_ne_zero_iff`).

Flexible accommodation evaluates each disjunct in the input restricted by an accommodated
proposition (`flex`). The standard update is the case where the second disjunct's
proposition is the negation of the first (`flex_univ_eq_disj`), which gives the conditional
presupposition of *Either Bill has no child or all of Bill's children are bald*
(`admits_flex_univ_iff`, `bill`). With tautologies accommodated the update is never defined
under conflict (`not_admits_flex_univ_univ`) and is not genuine when a presupposition
contradicts the other disjunct (`not_genuine_flex_univ_univ`); accommodating each disjunct's
negated rival presupposition derives both observations (`mem_flex_rival_iff`,
`neg_flex_rival`, `buganda`), at the cost of demanding accommodation where the standard update
filters the presupposition away (`exists_admits_disj_not_admits_flex_univ_univ`).

## Implementation notes

The disjunctions in the tradition of Karttunen and Peters read a disjunct's at-issue content
where its presupposition fails, so they are two-dimensional meanings
(`ConventionalImplicature.TwoDim`), evaluated by `TwoDim.toTrivalent`; the other theories take
trivalent propositions. The designated undefined state of the update semantics is the undefined
value of `Part`, the updates being the substrate's partial context change potentials of trivalent
propositions. The meta-assertion operator is Bochvar's assertion operator applied pointwise,
`fun w ↦ SignType.ofProp (φ w = 1)`. The licensing constraint on the operator is not modelled.
The paper's examples are the rows of `Data.Examples.Yagi2025`; (1c) and (4) are modelled by the
Buganda input and (15a) by the Bill input.

## References

* [yagi-2025]
* [beaver-2001]
* [beaver-krahmer-2001]
* [geurts-2005]
* [heim-1982]
* [karttunen-peters-1979]
* [katzir-singh-2012]
* [schlenker-2009]
* [zimmermann-2000]
-/

@[expose] public section

namespace Yagi2025

open DynamicSemantics CCP.Partial ConventionalImplicature

variable {W : Type*} {φ ψ : W → SignType} {p q : TwoDim W (W → Prop)}

/-- Two trivalent propositions have conflicting presuppositions when at every world one of them
is undefined. -/
def Conflict (φ ψ : W → SignType) : Prop := ∀ w, φ w = 0 ∨ ψ w = 0

/-! ### Strong Kleene and two-dimensional disjunction -/

theorem sup_ne_neg_one (h : Conflict φ ψ) (w : W) : (φ ⊔ ψ) w ≠ -1 := by
  rcases h w with h | h <;> simp [h]

theorem neg_sup_ne_one (h : Conflict φ ψ) (w : W) : (-(φ ⊔ ψ)) w ≠ 1 := by
  simpa using sup_ne_neg_one h w

theorem orKPSymmetric_ne_neg_one (h : Conflict p.toTrivalent q.toTrivalent) (w : W) :
    (p.orKPSymmetric q).toTrivalent w ≠ -1 := fun hn ↦ by
  rw [TwoDim.toTrivalent_eq_neg_one_iff] at hn
  refine hn.2 (TwoDim.orKPSymmetric_atIssue_of_conflict p q (fun ⟨hp, hq⟩ ↦ ?_) hn.1)
  rcases h w with h | h <;> simp_all

/-- The two-dimensional disjunction whose presupposition is the disjunction of the
presuppositions, (7). -/
def orPresupOr (p q : TwoDim W (W → Prop)) : TwoDim W (W → Prop) :=
  ⟨fun w ↦ p.atIssue w ∨ q.atIssue w, fun w ↦ p.notAtIssue w ∨ q.notAtIssue w⟩

theorem orPresupOr_toTrivalent_eq_neg_one_iff (w : W) :
    (orPresupOr p q).toTrivalent w = -1 ↔
      (p.notAtIssue w ∨ q.notAtIssue w) ∧ ¬ p.atIssue w ∧ ¬ q.atIssue w := by
  simp [orPresupOr]

/-- With a presuppositionless first disjunct it presupposes nothing, (8). -/
theorem orPresupOr_notAtIssue_of_left (h : ∀ w, p.notAtIssue w) (w : W) :
    (orPresupOr p q).notAtIssue w :=
  Or.inl (h w)

/-! ### Update semantics with a designated undefined state -/

theorem mem_disj_iff (h : Conflict φ ψ) (s t : Set W) :
    t ∈ disj (ofTrivalent φ) (ofTrivalent ψ) s ↔ (∀ w ∈ s, φ w = 1) ∧ t = s := by
  simp only [disj, Part.mem_bind_iff, Part.mem_map_iff, mem_ofTrivalent]
  constructor
  · rintro ⟨a, ⟨hp, rfl⟩, b, ⟨hq, rfl⟩, rfl⟩
    have hφ : ∀ w ∈ s, φ w = 1 := fun w hw ↦
      by_contra fun hn ↦ (h w).elim (hp hw) (hq ⟨hw, fun ha ↦ hn ha.2⟩)
    refine ⟨hφ, ?_⟩
    ext w
    simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_sdiff]
    exact ⟨fun h ↦ h.elim (·.1) (·.1.1), fun hw ↦ .inl ⟨hw, hφ w hw⟩⟩
  · rintro ⟨hφ, rfl⟩
    refine ⟨_, ⟨fun w hw ↦ by simp [hφ w hw], rfl⟩, ∅,
      ⟨fun w hw ↦ absurd (hφ w hw.1) fun ha ↦ hw.2 ⟨hw.1, ha⟩, ?_⟩, ?_⟩
    · ext w; simp only [Set.mem_sep_iff, Set.mem_sdiff, Set.mem_empty_iff_false, false_iff]
      exact fun ⟨⟨hw, hn⟩, _⟩ ↦ hn ⟨hw, hφ w hw⟩
    · ext w; simp only [Set.union_empty, Set.mem_sep_iff]
      exact ⟨(·.1), fun hw ↦ ⟨hw, hφ w hw⟩⟩

/-! ### Local contexts -/

theorem local_contexts_force_truth (h : Conflict φ ψ) (s : Set W)
    (h₁ : ∀ w ∈ s, φ w ≠ 1 → ψ w ≠ 0) (h₂ : ∀ w ∈ s, ψ w ≠ 1 → φ w ≠ 0) :
    ∀ w ∈ s, φ w = 1 ∨ ψ w = 1 := fun w hw ↦ by
  by_contra hn
  rw [not_or] at hn
  exact (h w).elim (h₂ w hw hn.2) (h₁ w hw hn.1)

/-! ### The meta-assertion operator -/

theorem joinWeak_ofProp_eq_one_ne_zero (w : W) :
    (SignType.ofProp (φ w = 1)).joinWeak (SignType.ofProp (ψ w = 1)) ≠ 0 := by
  simp [SignType.joinWeak_eq_zero_iff]

theorem joinWeak_ofProp_eq_one_eq_neg_one_iff (w : W) :
    (SignType.ofProp (φ w = 1)).joinWeak (SignType.ofProp (ψ w = 1)) = -1 ↔
      φ w ≠ 1 ∧ ψ w ≠ 1 := by
  simp [SignType.joinWeak_eq_neg_one_iff]

theorem sup_ofProp_eq_one_ne_zero_iff (w : W) :
    φ w ⊔ SignType.ofProp (ψ w = 1) ≠ 0 ↔ (ψ w ≠ 1 → φ w ≠ 0) := by
  by_cases h : ψ w = 1 <;> simp [h]

/-! ### Flexible accommodation -/

/-- Under flexible accommodation, (13), each disjunct updates the input restricted by its
accommodated proposition, and the results join. -/
def flex (χ ω : Set W) (φ ψ : CCP.Partial W) : CCP.Partial W :=
  fun s ↦ (φ (s ∩ χ)).bind fun a ↦ (ψ (s ∩ ω)).map (a ∪ ·)

/-- (13) requires that the accommodated propositions cover the input. Under conflict each
disjunct's negated rival presupposition covers every input. -/
theorem gapExt_union_gapExt_of_conflict (h : Conflict φ ψ) :
    Trivalent.gapExt ψ ∪ Trivalent.gapExt φ = Set.univ :=
  Set.eq_univ_of_forall fun w ↦ (h w).symm

/-- Genuineness, Definition 8, requires each disjunct to be true at some world of the input
that survives the update. -/
def Genuine (u φ ψ : CCP.Partial W) (s : Set W) : Prop :=
  (∃ w ∈ s, {w} ∈ φ {w} ∧ ∃ t ∈ u s, w ∈ t) ∧ ∃ w ∈ s, {w} ∈ ψ {w} ∧ ∃ t ∈ u s, w ∈ t

theorem flex_univ_eq_disj (ψ : CCP.Partial W) :
    flex Set.univ (posSupport φ)ᶜ (ofTrivalent φ) ψ = disj (ofTrivalent φ) ψ := by
  funext s
  refine Part.ext fun t ↦ ?_
  simp only [flex, disj, Set.inter_univ, Part.mem_bind_iff, mem_ofTrivalent]
  refine exists_congr fun a ↦ and_congr_right fun ⟨_, ha⟩ ↦ ?_
  subst ha
  rw [show s \ {w ∈ s | φ w = 1} = s ∩ (posSupport φ)ᶜ by
    ext w; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff, mem_posSupport,
      Set.mem_sep_iff]; tauto]

/-- Accommodating the negated first disjunct for the second (15) yields Katzir and Singh's
conditional presupposition (fn. 6). -/
theorem admits_flex_univ_iff (s : Set W) :
    (flex Set.univ (posSupport φ)ᶜ (ofTrivalent φ) (ofTrivalent ψ)).Admits s ↔
      ∀ w ∈ s, φ w ≠ 0 ∧ (φ w ≠ 1 → ψ w ≠ 0) := by
  rw [flex_univ_eq_disj, admits_disj_ofTrivalent, Set.subset_def]
  refine forall₂_congr fun w _ ↦ ?_
  simp only [Function.mem_support, ne_eq, SignType.joinMiddle_eq_zero_iff]
  generalize φ w = a; generalize ψ w = b
  cases a <;> cases b <;> decide

theorem mem_flex_univ_univ_iff (s t : Set W) :
    t ∈ flex Set.univ Set.univ (ofTrivalent φ) (ofTrivalent ψ) s ↔
      (∀ w ∈ s, φ w ≠ 0) ∧ (∀ w ∈ s, ψ w ≠ 0) ∧
        t = {w ∈ s | φ w = 1} ∪ {w ∈ s | ψ w = 1} := by
  simp only [flex, Set.inter_univ, Part.mem_bind_iff, Part.mem_map_iff, mem_ofTrivalent]
  constructor
  · rintro ⟨_, ⟨hp, rfl⟩, _, ⟨hq, rfl⟩, rfl⟩
    exact ⟨hp, hq, rfl⟩
  · rintro ⟨hp, hq, rfl⟩
    exact ⟨_, ⟨hp, rfl⟩, _, ⟨hq, rfl⟩, rfl⟩

/-- Under conflict that update is never defined on a nonempty input, (16). -/
theorem not_admits_flex_univ_univ (h : Conflict φ ψ) {s : Set W} (hs : s.Nonempty) :
    ¬ (flex Set.univ Set.univ (ofTrivalent φ) (ofTrivalent ψ)).Admits s := fun hd ↦ by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨hp, hq, -⟩ := (mem_flex_univ_univ_iff s _).1 (Part.get_mem hd)
  exact (h w).elim (hp w hw) (hq w hw)

/-- When the first disjunct contradicts the second presupposition (15), the update with tautologies
accommodated is not genuine. -/
theorem not_genuine_flex_univ_univ (h : ∀ w, φ w = 1 → ψ w = 0) (s : Set W) :
    ¬ Genuine (flex Set.univ Set.univ (ofTrivalent φ) (ofTrivalent ψ))
      (ofTrivalent φ) (ofTrivalent ψ) s := by
  rintro ⟨⟨w, hw, hφ, t, ht, -⟩, -⟩
  exact ((mem_flex_univ_univ_iff s t).1 ht).2.1 w hw
    (h w ((mem_ofTrivalent_self _ _).1 hφ w rfl))

/-- With each disjunct's negated rival presupposition accommodated (17), the update is defined iff
each input world satisfies a presupposition, and keeps the worlds where a disjunct is true. -/
theorem mem_flex_rival_iff (h : Conflict φ ψ) (s t : Set W) :
    t ∈ flex (Trivalent.gapExt ψ) (Trivalent.gapExt φ) (ofTrivalent φ) (ofTrivalent ψ) s ↔
      (∀ w ∈ s, φ w ≠ 0 ∨ ψ w ≠ 0) ∧ t = {w ∈ s | φ w = 1 ∨ ψ w = 1} := by
  have hset : {w ∈ s ∩ Trivalent.gapExt ψ | φ w = 1} ∪ {w ∈ s ∩ Trivalent.gapExt φ | ψ w = 1} =
      {w ∈ s | φ w = 1 ∨ ψ w = 1} := by
    ext w
    simp only [Set.mem_union, Set.mem_sep_iff, Set.mem_inter_iff, Trivalent.mem_gapExt]
    refine ⟨fun h' ↦ h'.elim (fun ⟨⟨hw, _⟩, ha⟩ ↦ ⟨hw, .inl ha⟩) fun ⟨⟨hw, _⟩, ha⟩ ↦ ⟨hw, .inr ha⟩,
      fun ⟨hw, h'⟩ ↦ h'.elim (fun ha ↦ .inl ⟨⟨hw, (h w).resolve_left (by simp [ha])⟩, ha⟩)
        fun ha ↦ .inr ⟨⟨hw, (h w).resolve_right (by simp [ha])⟩, ha⟩⟩
  simp only [flex, Part.mem_bind_iff, Part.mem_map_iff, mem_ofTrivalent]
  constructor
  · rintro ⟨_, ⟨h₁, rfl⟩, _, ⟨-, rfl⟩, rfl⟩
    exact ⟨fun w hw ↦ (em (ψ w = 0)).elim (fun hq ↦ .inl (h₁ ⟨hw, hq⟩)) .inr, hset⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨_, ⟨fun w hw ↦ (hs w hw.1).resolve_right (not_not.2 hw.2), rfl⟩, _,
      ⟨fun w hw ↦ (hs w hw.1).resolve_left (not_not.2 hw.2), rfl⟩, hset⟩

theorem neg_flex_rival (h : Conflict φ ψ) {s : Set W} (hs : ∀ w ∈ s, φ w ≠ 0 ∨ ψ w ≠ 0) :
    neg (flex (Trivalent.gapExt ψ) (Trivalent.gapExt φ) (ofTrivalent φ) (ofTrivalent ψ)) s =
      Part.some {w ∈ s | φ w ≠ 1 ∧ ψ w ≠ 1} := by
  rw [CCP.Partial.neg, Part.eq_some_iff, Part.mem_map_iff]
  refine ⟨_, (mem_flex_rival_iff h s _).2 ⟨hs, rfl⟩, ?_⟩
  ext w
  simp only [Set.mem_sdiff, Set.mem_sep_iff]
  tauto

/-- At a world where the first disjunct holds and the second presupposition fails, the standard
update admits the disjunction but accommodating tautologies does not (18). -/
theorem exists_admits_disj_not_admits_flex_univ_univ (hφ : ∀ w, φ w ≠ 0)
    (hf : ∀ w, φ w ≠ 1 → ψ w ≠ 0) {w : W} (hq : ψ w = 0) :
    (disj (ofTrivalent φ) (ofTrivalent ψ)).Admits {w} ∧
      ¬ (flex Set.univ Set.univ (ofTrivalent φ) (ofTrivalent ψ)).Admits {w} := by
  refine ⟨?_, fun hd ↦ ((mem_flex_univ_univ_iff _ _).1 (Part.get_mem hd)).2.1 w rfl hq⟩
  rw [← flex_univ_eq_disj]
  exact (admits_flex_univ_iff _).2 fun v _ ↦ ⟨hφ v, hf v⟩

/-! ### The ideal inputs -/

/-- The Buganda input of (1c) has four worlds, in which the king opens parliament, the king does
not open it, the president conducts the ceremony, and the president does not conduct it. -/
abbrev Buganda := Fin 4

/-- *The King of Buganda is opening parliament*. -/
noncomputable def kingOpens : Buganda → SignType :=
  {w | w < 2}.indicator fun w ↦ SignType.ofProp (w = 0)

/-- *The President of Buganda is conducting the ceremony*. -/
noncomputable def presidentConducts : Buganda → SignType :=
  {w | 2 ≤ w}.indicator fun w ↦ SignType.ofProp (w = 2)

theorem conflict_buganda : Conflict kingOpens presidentConducts := by
  intro w; fin_cases w <;> simp [kingOpens, presidentConducts]

/-- On the Buganda input, the update accommodating rival presuppositions keeps the worlds where the
head of state performs the duty, and its negation (4) the others. -/
theorem buganda :
    flex (Trivalent.gapExt presidentConducts) (Trivalent.gapExt kingOpens)
        (ofTrivalent kingOpens) (ofTrivalent presidentConducts) Set.univ = Part.some {0, 2} ∧
      neg (flex (Trivalent.gapExt presidentConducts) (Trivalent.gapExt kingOpens)
        (ofTrivalent kingOpens) (ofTrivalent presidentConducts)) Set.univ =
        Part.some {1, 3} := by
  have hs : ∀ w ∈ (Set.univ : Set Buganda), kingOpens w ≠ 0 ∨ presidentConducts w ≠ 0 := by
    intro w _; fin_cases w <;> simp [kingOpens, presidentConducts]
  refine ⟨Part.eq_some_iff.2 ((mem_flex_rival_iff conflict_buganda _ _).2 ⟨hs, ?_⟩), ?_⟩
  · ext w
    fin_cases w <;> simp [kingOpens, presidentConducts]
  · rw [neg_flex_rival conflict_buganda hs]
    congr 1
    ext w
    fin_cases w <;> simp [kingOpens, presidentConducts]

/-- The Bill input of (15a) has three worlds, in which Bill has no child, has children who are
all bald, or has children who are not all bald. -/
abbrev Bill := Fin 3

/-- *Bill has no child*. -/
def noChild : Bill → SignType := fun w ↦ SignType.ofProp (w = 0)

/-- *All of Bill's children are bald*, presupposing that Bill has children. -/
noncomputable def allBald : Bill → SignType :=
  {w | w ≠ 0}.indicator fun w ↦ SignType.ofProp (w = 1)

/-- On the Bill input, accommodating tautologies leaves the update undefined, while accommodating
the negated first disjunct for the second (15) is defined and genuine. -/
theorem bill :
    ¬ (flex Set.univ Set.univ (ofTrivalent noChild) (ofTrivalent allBald)).Admits Set.univ ∧
      {0, 1} ∈ flex Set.univ (posSupport noChild)ᶜ (ofTrivalent noChild)
        (ofTrivalent allBald) Set.univ ∧
      Genuine (flex Set.univ (posSupport noChild)ᶜ (ofTrivalent noChild)
        (ofTrivalent allBald)) (ofTrivalent noChild) (ofTrivalent allBald) Set.univ := by
  have hd : {0, 1} ∈ flex Set.univ (posSupport noChild)ᶜ (ofTrivalent noChild)
      (ofTrivalent allBald) Set.univ := by
    simp only [flex, Set.inter_univ, Set.univ_inter, Part.mem_bind_iff, Part.mem_map_iff,
      mem_ofTrivalent]
    refine ⟨_, ⟨fun w _ ↦ by simp [noChild], rfl⟩, _, ⟨fun w hw ↦ ?_, rfl⟩, ?_⟩
    · fin_cases w <;> simp_all [noChild, allBald]
    · ext w
      fin_cases w <;> simp [noChild, allBald]
  refine ⟨fun h ↦ ?_, hd, ⟨0, trivial, ?_, _, hd, by simp⟩, ⟨1, trivial, ?_, _, hd, by simp⟩⟩
  · exact ((mem_flex_univ_univ_iff _ _).1 (Part.get_mem h)).2.1 0 trivial (by simp [allBald])
  · exact (mem_ofTrivalent_self _ _).2 fun v hv ↦ by simp_all [noChild]
  · exact (mem_ofTrivalent_self _ _).2 fun v hv ↦ by simp_all [allBald]

end Yagi2025
