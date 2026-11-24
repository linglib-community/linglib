module

public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Modality.ComparativePossibility
public import Linglib.Semantics.Degree.CresswellDegree
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Data.Examples.Villalta2008

/-!
# Villalta (2008): Mood and Gradability

Villalta argues that the predicates selecting the subjunctive in Spanish share a semantics of
comparison: each contributes an ordering of propositions and says that its complement stands above
the alternatives the context supplies. She starts from Heim's conditional semantics for desire
predicates, which compares the complement with its negation, and revises it twice.

First, the comparison is with the contextual alternatives, of which the complement and its
negation are the special case. In a scenario with three alternatives ranked by desirability, the
conditional semantics makes *wish* true of the middle one, which is judged false, because the
nearest worlds where it fails are the least desirable ones. Second, the comparison no longer
refers to the subject's beliefs. The conditional semantics depends on a proposition only through
the belief worlds where it holds, so it makes any two propositions the subject takes to be
equivalent wanted together; the revised relation between propositions, every world of the one
bettered by a world of the other and not conversely, does not. Beliefs return as definedness
conditions that tell *want*, *wish* and *be glad* apart. Finally the predicates get a degree
argument, the degrees being the classes of propositions the comparison cannot tell apart, and
the comparison of alternatives is a superlative over those degrees.

## Implementation notes

The comparison of alternatives is one predicate, `BeatsAlternatives R C p`, instantiated at the
conditional comparison of the substrate for the first revision and at the strict part of
`ComparativePossibility.Lewis` for the second. The first revision is formalized with the belief
worlds quantified as in the conditional semantics. In the scenario each alternative is one world,
and similarity ranks worlds by how likely Victoria takes them to be, the same from every belief
world, which is how the paper's discussion of the scenario reads the nearest worlds.
*Be disappointed* is the comparison with desirability reversed, as the paper assumes, and its
judgment is checked against the two alternatives of cake and pie.

The degree of wanting is formalized as a measure, the degree of a proposition being its class,
and not as a relation between propositions and degrees with a maximality operator.

## TODO

* The generalization about mood, that a complement takes the subjunctive exactly when its
  predicate compares it with contextual alternatives, and the Spanish predicate classes it is
  argued from.
* The predicates other than desire predicates: emotive factives, modals, predicates of likelihood
  and doubt, directives and causatives.
* The focus sensitivity of these predicates and the contribution of the subjunctive morpheme.
* The degree modification and comparative data.
* The requirement that what is wanted be desirable, which sets *want* apart from *prefer*.

## References

* [villalta-2008]
* [heim-1992]
* [kratzer-1991]
* [cresswell-1976]
-/

@[expose] public section

namespace Villalta2008

open Desire Desire.Conditional ComparativePossibility
open scoped CresswellDegree

variable {α W : Type*}

/-! ### Comparison of alternatives -/

/-- `p` beats its alternatives under the comparison `R` when it stands in `R` to every other
member of the set `C` of contextual alternatives. -/
def BeatsAlternatives (R : α → α → Prop) (C : Set α) (p : α) : Prop :=
  ∀ q ∈ C, q ≠ p → R p q

section BeatsAlternatives

variable {R : α → α → Prop} {C C' : Set α} {p q : α}

theorem BeatsAlternatives.anti (h : BeatsAlternatives R C p) (hC : C' ⊆ C) :
    BeatsAlternatives R C' p :=
  fun q hq ↦ h q (hC hq)

theorem beatsAlternatives_pair (h : q ≠ p) : BeatsAlternatives R {p, q} p ↔ R p q := by
  simp [BeatsAlternatives, h]

/-- The comparison of alternatives is the superlative over the degrees of the comparison, the
classes of things it cannot tell apart, compared by the relation the comparison induces between
them. -/
theorem beatsAlternatives_iff_absoluteSuperlative (hp : p ∈ C) :
    BeatsAlternatives R C p ↔
      letI : LT (CresswellDegree R) := ⟨fun x y ↦ y >[R] x⟩
      AbsoluteSuperlative (Quotient.mk (cresswellSetoid R)) C p := by
  simp only [AbsoluteSuperlative, hp, true_and, BeatsAlternatives]
  exact forall₃_congr fun q _ _ ↦ Iff.rfl

end BeatsAlternatives

/-- Over the alternatives `p` and `¬p` the comparison of alternatives is Heim's conditional
semantics. -/
theorem beatsAlternatives_better_pair_iff [Nonempty W] (F : Frame W) (dox : Set W) (w : W)
    (p : Set W) : BeatsAlternatives (Better F dox dox w) {p, pᶜ} p ↔ Want F dox dox w p :=
  beatsAlternatives_pair compl_ne_self

/-! ### Three alternatives -/

/-- The three ways the scenario of (28) may turn out. -/
inductive Dessert where
  | cake | pie | iceCream
  deriving DecidableEq

/-- Victoria ranks the chocolate cake above the apple pie and the apple pie above the ice cream in
desirability, and takes them to be likely in the reverse order. -/
def Dessert.rank : Dessert → ℕ
  | .iceCream => 0
  | .pie => 1
  | .cake => 2

/-- Victoria's frame: a world is nearer the more likely she takes it to be, and more desirable
the higher its dessert ranks. -/
def victoria : Frame Dessert where
  sim _ := Preorder.lift Dessert.rank
  pref _ x y := y.rank < x.rank

/-- The frame of *be disappointed*, with desirability reversed. -/
def disappointment : Frame Dessert where
  sim _ := Preorder.lift Dessert.rank
  pref _ x y := x.rank < y.rank

private theorem closest_compl_pie (F : Frame Dessert)
    (hF : F.sim = fun _ ↦ Preorder.lift Dessert.rank) (w' : Dessert) :
    F.closest Set.univ {.pie}ᶜ w' = {.iceCream} := by
  ext y
  simp only [Frame.closest, Preorder.mem_minimals_iff, Set.univ_inter, Set.mem_compl_iff,
    Set.mem_singleton_iff, hF]
  refine ⟨fun ⟨hy, h⟩ ↦ ?_, ?_⟩
  · have h0 : y.rank ≤ Dessert.rank .iceCream := h (b := .iceCream) (by simp) (Nat.zero_le _)
    cases y
    exacts [absurd h0 (by decide), absurd rfl hy, rfl]
  · rintro rfl
    exact ⟨by simp, fun _ _ _ ↦ Nat.zero_le _⟩

/-- In the scenario of (28) the conditional semantics holds of the apple pie, where (30) is
judged false: the nearest worlds without the pie are ice-cream worlds, which are less
desirable. -/
theorem want_pie (w : Dessert) :
    Want victoria Set.univ Set.univ w {.pie} ∧ Examples.ex_30.verdict = some false := by
  refine ⟨fun w' _ x hx y hy ↦ ?_, rfl⟩
  rw [Frame.closest_singleton (Set.mem_univ _)] at hx
  rw [closest_compl_pie _ rfl] at hy
  rw [hx, hy]
  exact (by decide : Dessert.rank .iceCream < Dessert.rank .pie)

/-- Compared with all three alternatives the apple pie does not come out on top, under the
conditional comparison and under the comparison of propositions alike, as (30) is judged. -/
theorem beatsAlternatives_pie_iff (w : Dessert) :
    (BeatsAlternatives (Better victoria Set.univ Set.univ w) {{.cake}, {.pie}, {.iceCream}}
        {.pie} ↔ Examples.ex_30.verdict = some true) ∧
      (BeatsAlternatives (AsymmRel (Lewis (victoria.pref w))) {{.cake}, {.pie}, {.iceCream}}
        {.pie} ↔ Examples.ex_30.verdict = some true) := by
  have hne : ({.cake} : Set Dessert) ≠ {.pie} := by simp
  refine ⟨iff_of_false (fun h ↦ ?_) (by decide), iff_of_false (fun h ↦ ?_) (by decide)⟩
  · have := (better_singleton_iff (Set.mem_univ _) (Set.mem_univ _)).1
      (h {.cake} (by simp) hne) ⟨w, trivial⟩
    exact absurd this (by decide : ¬ Dessert.rank .cake < Dessert.rank .pie)
  · obtain ⟨a, ha, hab⟩ := (h {.cake} (by simp) hne).1 (Set.mem_singleton Dessert.cake)
    rw [Set.mem_singleton_iff.1 ha] at hab
    exact absurd hab (by decide : ¬ Dessert.rank .cake < Dessert.rank .pie)

-- (31): the conditional semantics is false of *be disappointed* and the apple pie
theorem not_want_disappointment_pie (w : Dessert) :
    ¬ Want disappointment Set.univ Set.univ w {.pie} := fun h ↦
  absurd (h w trivial .pie (by rw [Frame.closest_singleton (Set.mem_univ _)]; rfl) .iceCream
    (by rw [closest_compl_pie _ rfl]; rfl))
    (by decide : ¬ Dessert.rank .pie < Dessert.rank .iceCream)

-- (31): compared with the chocolate cake, the apple pie is the disappointing alternative
theorem beatsAlternatives_disappointment_pie_iff (w : Dessert) :
    BeatsAlternatives (Better disappointment Set.univ Set.univ w) {{.cake}, {.pie}} {.pie} ↔
      Examples.ex_31.verdict = some true := by
  refine iff_of_true (fun q hq hne ↦ ?_) rfl
  rcases hq with rfl | rfl
  · exact (better_singleton_iff (Set.mem_univ _) (Set.mem_univ _)).2 fun _ ↦
      (by decide : Dessert.rank .pie < Dessert.rank .cake)
  · exact absurd rfl hne

/-! ### Reference to the doxastic alternatives -/

/-- The conditional semantics licenses the practical inference of (33): propositions that hold at
the same belief worlds are wanted together. -/
theorem want_iff_of_inter_eq (F : Frame W) {dox p q : Set W} (w : W)
    (h : dox ∩ p = dox ∩ q) : Want F dox dox w p ↔ Want F dox dox w q :=
  want_congr h

-- (38): the comparison of propositions does not license it, the alternatives being different
theorem exists_inter_eq_and_not_beatsAlternatives :
    ∃ (r : Fin 4 → Fin 4 → Prop) (dox p q : Set (Fin 4)) (C C' : Set (Set (Fin 4))),
      dox ∩ p = dox ∩ q ∧ (∀ s ∈ C ∪ C', (dox ∩ s).Nonempty) ∧ p ∈ C ∧ q ∈ C' ∧
        BeatsAlternatives (AsymmRel (Lewis r)) C p ∧
          ¬ BeatsAlternatives (AsymmRel (Lewis r)) C' q := by
  refine ⟨fun x y ↦ x = 0 ∧ y = 1, {0, 1}, {0}, {0, 2}, {{0}, {1}}, {{0, 2}, {1, 3}},
    ?_, ?_, by simp, by simp, ?_, ?_⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert x
    decide
  · rintro s ((rfl | rfl) | (rfl | rfl))
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨0, by simp⟩, ⟨1, by simp⟩]
  · rintro s (rfl | rfl) hne
    · exact absurd rfl hne
    · refine ⟨fun b hb ↦ ⟨0, rfl, rfl, hb⟩, fun h ↦ ?_⟩
      obtain ⟨a, ha, h10, -⟩ := h (Set.mem_singleton (0 : Fin 4))
      rw [Set.mem_singleton_iff.1 ha] at h10
      exact absurd h10 (by decide)
  · intro h
    have hne : ({1, 3} : Set (Fin 4)) ≠ {0, 2} := fun he ↦ by
      have : (1 : Fin 4) ∈ ({0, 2} : Set (Fin 4)) := he ▸ Set.mem_insert _ _
      simp at this
    obtain ⟨a, -, -, h31⟩ := (h {1, 3} (by simp) hne).1 (Set.mem_insert_of_mem _ rfl)
    exact absurd h31 (by decide : ¬ (3 : Fin 4) = 1)

/-! ### Definedness -/

section Definedness

variable (dox : W → Set W) (r : W → W → W → Prop) (C : Set (Set W)) (p : Set W)

open Classical in
/-- (37): *want* is defined where every contextual alternative is compatible with the subject's
beliefs, and then holds where the complement is more desirable than every other alternative. -/
noncomputable def want : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ ∀ q ∈ C, (dox w ∩ q).Nonempty)
    fun w ↦ BeatsAlternatives (AsymmRel (Lewis (r w))) C p

open Classical in
/-- (39): *wish* is defined where the subject's beliefs exclude the complement. -/
noncomputable def wish : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ p ∩ dox w = ∅)
    fun w ↦ BeatsAlternatives (AsymmRel (Lewis (r w))) C p

open Classical in
/-- (40): *be glad* is defined where the subject believes the complement. -/
noncomputable def beGlad : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ dox w ⊆ p)
    fun w ↦ BeatsAlternatives (AsymmRel (Lewis (r w))) C p

variable {dox r C p} {w : W}

open Classical in
-- (37), (39): where *want* is defined of an alternative, *wish* is not
theorem wish_eq_undefined_of_want_ne_undefined (hp : p ∈ C) (h : want dox r C p w ≠ .undefined) :
    wish dox r C p w = .undefined := by
  rw [want, ne_eq, Trivalent.condEvent_eq_undefined_iff, not_not] at h
  rw [wish, Trivalent.condEvent_eq_undefined_iff, Set.inter_comm]
  exact (h p hp).ne_empty

open Classical in
-- (37): over `p` and `¬p`, *want* is defined where the subject's beliefs are contingent on `p`
theorem want_pair_ne_undefined_iff :
    want dox r {p, pᶜ} p w ≠ .undefined ↔ IsContingent (dox w) p := by
  rw [want, ne_eq, Trivalent.condEvent_eq_undefined_iff, not_not, IsContingent, Set.sdiff_eq]
  simp

end Definedness

end Villalta2008
