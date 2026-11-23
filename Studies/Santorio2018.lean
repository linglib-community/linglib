module

public import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Studies.McKayVanInwagen1977

/-!
# Santorio (2018): Alternatives and Truthmakers in Conditional Semantics

For a sentence with prejacent `S : Set W` and alternatives `ALT : Set (Set W)`, a subset `σ` of
`ALT` is stable when some world of `S` verifies every member of `σ` and falsifies every other
alternative, that is, when `(S ∩ ⋂₀ σ) \ ⋃₀ (ALT \ σ)` is nonempty. The stable sets are the sets
`Preorder.satisfied (· ∈ ·) ALT w` of alternatives true at a world `w ∈ S`
(`stable_iff_exists_eq_satisfied`), so the minimal stable sets are those of the minimal worlds
`Exhaustification.exhMW ALT S` (`minimalStable_iff_exists_mem_exhMW`), and their complements in
`ALT` are the maximal consistent exclusions of innocent exclusion
(`minimalStable_iff_maximal_isConsistentExclusion`).

A truthmaker of `S` is the intersection `⋂₀ σ` of a minimal stable set that is included in `S`,
and an *if*-clause denotes the set `truthmakers ALT S`. No truthmaker is included in another
(`isAntichain_truthmakers`), and when `S` is one of finitely many alternatives the truthmakers
cover it (`sUnion_truthmakers`).

The conditional is read off this set by the operators of
`Semantics/Conditionals/Counterfactual/Alternatives.lean`. Without the distributivity operator
*would* takes the union of the truthmakers, so the conditional is the counterfactual of `S`
(`disjunctiveImp_truthmakers`). With it the counterfactual holds of each truthmaker. For a
disjunction of two propositions neither of which includes the other, with alternatives
`{A ∪ B, A, B, A ∩ B}`, the truthmakers are the disjuncts (`truthmakers_disjunction`), so the
distributive reading is the conjunction of the two simplifications
(`distributiveImp_truthmakers_disjunction`). On *every student read War and Peace or Anna
Karenina*, with the eight alternatives obtained by substituting for the quantifier and the
connective, there is a third truthmaker besides the two universal ones, on which some student
read each book (`karenina_truthmakers`).

On [mckay-vaninwagen-1977]'s model of *if Spain had fought with the Axis or the Allies, she
would have fought with the Axis*, the collective reading is true, the distributive reading is
false and its homogeneity presupposition fails (`spain_collective`, `spain_not_distributive`,
`spain_homogeneity`). With the prejacent as its only alternative the same antecedent has itself
as its only truthmaker and the distributive reading is true (`spain_distributive_singleton`), so
the reading depends on the alternatives and not only on the proposition.

## Implementation notes

The formalization follows the author's draft of August 2016. Stability is taken relative to the
worlds of the prejacent: the paper's definition asks that `σ` be consistent with the negations
of the alternatives outside it, and the stable sets it lists for its examples are those for which
this holds at a world of the prejacent. Alternatives are propositions rather than sentences
generated from a substitution source.

## TODO

* The paper's pair *if Anna came* and *if Anna, or Otto and Anna, came* is not formalized. A
  set containing both *Anna came* and *Otto and Anna came* is not a set of truthmakers, by
  `isAntichain_truthmakers`.
* The infelicitous sequences of conditionals that the third truthmaker of
  `karenina_truthmakers` accounts for are not formalized.

## References

* [santorio-2018]
* [alonso-ovalle-2009]
* [mckay-vaninwagen-1977]
* [fox-2007]
* [spector-2016]
-/

@[expose] public section

namespace Santorio2018

open Set Conditional Exhaustification
open Preorder (satisfied)

variable {W : Type*} (ALT : Set (Set W)) (S : Set W)

/-! ### Stability -/

/-- A set `σ` of alternatives is stable when some world of the prejacent verifies every member
of `σ` and falsifies every other alternative. -/
def Stable (σ : Set (Set W)) : Prop :=
  σ ⊆ ALT ∧ ((S ∩ ⋂₀ σ) \ ⋃₀ (ALT \ σ)).Nonempty

/-- A stable set of alternatives is minimal when it includes no other stable set. -/
def MinimalStable (σ : Set (Set W)) : Prop := Minimal (Stable ALT S) σ

/-- The truthmakers of `S` are the intersections of the minimal stable sets of alternatives
that are included in `S`. They are the denotation of an *if*-clause. -/
def truthmakers : Set (Set W) := {p | (∃ σ, MinimalStable ALT S σ ∧ ⋂₀ σ = p) ∧ p ⊆ S}

variable {ALT S} {σ : Set (Set W)} {M : Set W} {p A B : Set W} {u v : W}

theorem stable_iff_exists_eq_satisfied :
    Stable ALT S σ ↔ ∃ w ∈ S, σ = satisfied (· ∈ ·) ALT w := by
  refine ⟨fun ⟨hσ, w, ⟨hwS, hw⟩, hnw⟩ ↦ ⟨w, hwS, Subset.antisymm (fun A hA ↦ ⟨hσ hA, hw A hA⟩)
    fun A hA ↦ not_not.mp fun h ↦ hnw ⟨A, ⟨hA.left, h⟩, hA.right⟩⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨fun _ h ↦ h.left, w, ⟨hw, fun _ hA ↦ hA.right⟩, fun ⟨A, ⟨hA, hn⟩, hwA⟩ ↦ hn ⟨hA, hwA⟩⟩

theorem Stable.nonempty_sInter (h : Stable ALT S σ) : (⋂₀ σ).Nonempty :=
  h.right.mono (sdiff_subset.trans inter_subset_right)

theorem Stable.mem_of_subset (h : Stable ALT S σ) (hA : A ∈ σ) (hB : B ∈ ALT) (hAB : A ⊆ B) :
    B ∈ σ := by
  obtain ⟨w, -, rfl⟩ := stable_iff_exists_eq_satisfied.mp h
  exact ⟨hB, hAB hA.right⟩

theorem minimalStable_satisfied_iff (hu : u ∈ S) :
    MinimalStable ALT S (satisfied (· ∈ ·) ALT u) ↔ u ∈ exhMW ALT S := by
  refine ⟨fun h ↦ ⟨hu, fun v hv hvu ↦
      h.le_of_le (stable_iff_exists_eq_satisfied.mpr ⟨v, hv, rfl⟩) hvu⟩,
    fun h ↦ ⟨stable_iff_exists_eq_satisfied.mpr ⟨u, hu, rfl⟩, fun τ hτ hτu ↦ ?_⟩⟩
  obtain ⟨v, hv, rfl⟩ := stable_iff_exists_eq_satisfied.mp hτ
  exact (mem_exhMW.mp h).le_of_le hv hτu

theorem minimalStable_iff_exists_mem_exhMW :
    MinimalStable ALT S σ ↔ ∃ u ∈ exhMW ALT S, σ = satisfied (· ∈ ·) ALT u := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := stable_iff_exists_eq_satisfied.mp h.prop
    exact ⟨u, (minimalStable_satisfied_iff hu).mp h, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact (minimalStable_satisfied_iff (exhMW_subset hu)).mpr hu

/-- The minimal stable sets of alternatives are the complements of the maximal consistent
exclusions of [fox-2007]. -/
theorem minimalStable_iff_maximal_isConsistentExclusion :
    MinimalStable ALT S σ ↔ σ ⊆ ALT ∧ Maximal (IsConsistentExclusion ALT S) (ALT \ σ) := by
  refine ⟨fun h ↦ ?_, fun ⟨hσ, h⟩ ↦ ?_⟩
  · obtain ⟨u, hu, rfl⟩ := minimalStable_iff_exists_mem_exhMW.mp h
    exact ⟨fun _ h ↦ h.left, (maximal_sdiff_satisfied_iff (exhMW_subset hu)).mpr hu⟩
  · obtain ⟨u, hu, heq⟩ := Exhaustification.Maximal.exists_eq_sdiff_satisfied h
    have hu' : ALT ⊓ satisfied (· ∈ ·) ALT u = satisfied (· ∈ ·) ALT u :=
      inf_eq_right.mpr fun _ h ↦ h.left
    rw [sdiff_eq_sdiff_iff_inf_eq_inf, inf_eq_right.mpr hσ, hu'] at heq
    exact minimalStable_iff_exists_mem_exhMW.mpr ⟨u, hu, heq⟩

/-! ### Truthmakers -/

theorem satisfied_subset_satisfied :
    satisfied (· ∈ ·) ALT u ⊆ satisfied (· ∈ ·) ALT v ↔ ∀ A ∈ ALT, u ∈ A → v ∈ A :=
  Preorder.satisfied_subset_iff ..

theorem mem_sInter_satisfied :
    v ∈ ⋂₀ satisfied (· ∈ ·) ALT u ↔ satisfied (· ∈ ·) ALT u ⊆ satisfied (· ∈ ·) ALT v :=
  ⟨fun h A hA ↦ ⟨hA.left, h A hA⟩, fun h _ hA ↦ (h hA).right⟩

theorem mem_truthmakers_iff :
    p ∈ truthmakers ALT S ↔
      (∃ u ∈ exhMW ALT S, ⋂₀ satisfied (· ∈ ·) ALT u = p) ∧ p ⊆ S := by
  refine and_congr_left fun _ ↦ ⟨?_, fun ⟨u, hu, h⟩ ↦
    ⟨_, minimalStable_iff_exists_mem_exhMW.mpr ⟨u, hu, rfl⟩, h⟩⟩
  rintro ⟨σ, hσ, rfl⟩
  obtain ⟨u, hu, rfl⟩ := minimalStable_iff_exists_mem_exhMW.mp hσ
  exact ⟨u, hu, rfl⟩

theorem truthmakers_eq_image (hS : S ∈ ALT) :
    truthmakers ALT S = (fun u ↦ ⋂₀ satisfied (· ∈ ·) ALT u) '' exhMW ALT S := by
  ext p
  rw [mem_truthmakers_iff]
  exact ⟨fun h ↦ h.left,
    fun ⟨u, hu, e⟩ ↦ ⟨⟨u, hu, e⟩, e ▸ sInter_subset_of_mem ⟨hS, exhMW_subset hu⟩⟩⟩

theorem truthmakers_eq_image_of_isMinimalCover (hM : IsMinimalCover ALT S M) (hS : S ∈ ALT) :
    truthmakers ALT S = (fun u ↦ ⋂₀ satisfied (· ∈ ·) ALT u) '' M := by
  rw [truthmakers_eq_image hS, hM.exhMW_eq]
  ext p
  constructor
  · rintro ⟨u, ⟨-, v, hv, hvu⟩, rfl⟩
    exact ⟨v, hv, congrArg sInter hvu⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hM.mem v hv, v, hv, rfl⟩, rfl⟩

/-- No truthmaker of a sentence is included in another. -/
theorem isAntichain_truthmakers : IsAntichain (· ⊆ ·) (truthmakers ALT S) := by
  rintro p hp q hq hne hpq
  obtain ⟨⟨u, hu, rfl⟩, -⟩ := mem_truthmakers_iff.mp hp
  obtain ⟨⟨v, hv, rfl⟩, -⟩ := mem_truthmakers_iff.mp hq
  have hvu : satisfied (· ∈ ·) ALT v ⊆ satisfied (· ∈ ·) ALT u :=
    mem_sInter_satisfied.mp (hpq (mem_sInter_satisfied.mpr subset_rfl))
  exact hne (congrArg sInter (((mem_exhMW.mp hu).le_of_le (exhMW_subset hv) hvu).antisymm hvu))

theorem sUnion_truthmakers_subset : ⋃₀ truthmakers ALT S ⊆ S :=
  sUnion_subset fun _ h ↦ h.right

theorem sUnion_truthmakers (hfin : ALT.Finite) (hS : S ∈ ALT) : ⋃₀ truthmakers ALT S = S := by
  refine sUnion_truthmakers_subset.antisymm fun w hw ↦ ?_
  obtain ⟨u, hu, huw⟩ := exists_mem_exhMW_le hfin hw
  exact ⟨_, truthmakers_eq_image hS ▸ mem_image_of_mem _ hu, mem_sInter_satisfied.mpr huw⟩

theorem truthmakers_singleton (hS : S.Nonempty) : truthmakers {S} S = {S} := by
  obtain ⟨s, hs⟩ := hS
  have le (u v : W) : satisfied (· ∈ ·) {S} u ⊆ satisfied (· ∈ ·) {S} v ↔ (u ∈ S → v ∈ S) := by
    rw [satisfied_subset_satisfied, forall_mem_singleton]
  have hM : IsMinimalCover {S} S {s} :=
    ⟨fun _ hv ↦ hv ▸ hs, fun w hw ↦ ⟨s, rfl, (le s w).mpr fun _ ↦ hw⟩,
      by rintro v rfl u rfl h; exact h⟩
  have hs' : ⋂₀ satisfied (· ∈ ·) {S} s = S :=
    Set.ext fun v ↦ mem_sInter_satisfied.trans ((le s v).trans ⟨fun h ↦ h hs, fun h _ ↦ h⟩)
  rw [truthmakers_eq_image_of_isMinimalCover hM rfl, image_singleton, hs']

/-- The truthmakers of a disjunction of two propositions, neither of which includes the other,
are its disjuncts. -/
theorem truthmakers_disjunction (hA : ¬ A ⊆ B) (hB : ¬ B ⊆ A) :
    truthmakers {A ∪ B, A, B, A ∩ B} (A ∪ B) = {A, B} := by
  obtain ⟨a, haA, haB⟩ := not_subset.mp hA
  obtain ⟨b, hbB, hbA⟩ := not_subset.mp hB
  have le (u v : W) : satisfied (· ∈ ·) {A ∪ B, A, B, A ∩ B} u ⊆
      satisfied (· ∈ ·) {A ∪ B, A, B, A ∩ B} v ↔ (u ∈ A → v ∈ A) ∧ (u ∈ B → v ∈ B) := by
    rw [satisfied_subset_satisfied]
    simp only [forall_mem_insert, forall_mem_singleton, mem_union, mem_inter_iff]
    tauto
  have hM : IsMinimalCover {A ∪ B, A, B, A ∩ B} (A ∪ B) {a, b} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro v (rfl | rfl)
      exacts [.inl haA, .inr hbB]
    · rintro w (hw | hw)
      exacts [⟨a, .inl rfl, (le a w).mpr ⟨fun _ ↦ hw, fun h ↦ (haB h).elim⟩⟩,
        ⟨b, .inr rfl, (le b w).mpr ⟨fun h ↦ (hbA h).elim, fun _ ↦ hw⟩⟩]
    · rintro v (rfl | rfl) u (rfl | rfl) h
      exacts [h, (haB (((le _ _).mp h).right hbB)).elim,
        (hbA (((le _ _).mp h).left haA)).elim, h]
  have ha : ⋂₀ satisfied (· ∈ ·) {A ∪ B, A, B, A ∩ B} a = A :=
    Set.ext fun v ↦ mem_sInter_satisfied.trans ((le a v).trans
      ⟨fun h ↦ h.left haA, fun h ↦ ⟨fun _ ↦ h, fun h' ↦ (haB h').elim⟩⟩)
  have hb : ⋂₀ satisfied (· ∈ ·) {A ∪ B, A, B, A ∩ B} b = B :=
    Set.ext fun v ↦ mem_sInter_satisfied.trans ((le b v).trans
      ⟨fun h ↦ h.right hbB, fun h ↦ ⟨fun h' ↦ (hbA h').elim, fun _ ↦ h⟩⟩)
  rw [truthmakers_eq_image_of_isMinimalCover hM (mem_insert ..), image_pair, ha, hb]

/-! ### Conditionals as descriptions of truthmakers -/

variable (ord : W → Preorder W) (C : Set W)

/-- Without the distributivity operator, a conditional whose prejacent is one of finitely many
alternatives is the counterfactual of the prejacent. -/
theorem disjunctiveImp_truthmakers (hfin : ALT.Finite) (hS : S ∈ ALT) :
    disjunctiveImp ord (truthmakers ALT S) C = closestImp ord S C := by
  rw [disjunctiveImp, sUnion_truthmakers hfin hS]

-- (55)–(56)
theorem distributiveImp_truthmakers_disjunction (hA : ¬ A ⊆ B) (hB : ¬ B ⊆ A) :
    distributiveImp ord (truthmakers {A ∪ B, A, B, A ∩ B} (A ∪ B)) C =
      closestImp ord A C ∩ closestImp ord B C := by
  rw [truthmakers_disjunction hA hB, distributiveImp_pair]

/-! ### Every student read War and Peace or Anna Karenina (35) -/

/-- The books a student read. -/
inductive Shelf | neither | ak | wp | both
  deriving DecidableEq, Fintype

/-- The student read *Anna Karenina*. -/
abbrev Shelf.HasAK (s : Shelf) : Prop := s = .ak ∨ s = .both

/-- The student read *War and Peace*. -/
abbrev Shelf.HasWP (s : Shelf) : Prop := s = .wp ∨ s = .both

/-- A world fixes what each of two students read. -/
structure World where
  first : Shelf
  second : Shelf
  deriving DecidableEq

instance : Fintype World :=
  .ofEquiv (Shelf × Shelf) ⟨fun (a, b) ↦ ⟨a, b⟩, fun w ↦ (w.first, w.second), fun _ ↦ rfl,
    fun _ ↦ rfl⟩

/-- The predicates substituted for the disjunction in (48). -/
inductive Pred | both | ak | wp | either
  deriving DecidableEq, Fintype

/-- The quantifiers substituted for *every student* in (48). -/
inductive Quant | every | some
  deriving DecidableEq, Fintype

/-- A student with shelf `s` satisfies the predicate. -/
def Pred.Holds : Pred → Shelf → Prop
  | .both, s => s.HasAK ∧ s.HasWP
  | .ak, s => s.HasAK
  | .wp, s => s.HasWP
  | .either, s => s.HasAK ∨ s.HasWP

instance : ∀ P s, Decidable (Pred.Holds P s)
  | .both, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .ak, _ => inferInstanceAs (Decidable (_ ∨ _))
  | .wp, _ => inferInstanceAs (Decidable (_ ∨ _))
  | .either, _ => inferInstanceAs (Decidable (_ ∨ _))

/-- (48): the alternative with quantifier `q` and predicate `P`. -/
def alt : Quant → Pred → Set World
  | .every, P => {w | P.Holds w.first ∧ P.Holds w.second}
  | .some, P => {w | P.Holds w.first ∨ P.Holds w.second}

instance : ∀ q P, DecidablePred (· ∈ alt q P)
  | .every, _ => fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
  | .some, _ => fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- (48): the eight alternatives to (35). -/
def readingAlts : Set (Set World) := range (Function.uncurry alt)

/-- (35) has three truthmakers: every student read *Anna Karenina*, every student read *War and
Peace*, and every student read one of them while some read each. -/
theorem karenina_truthmakers :
    truthmakers readingAlts (alt .every .either) =
      {alt .every .ak, alt .every .wp,
        alt .every .either ∩ alt .some .ak ∩ alt .some .wp} := by
  have le (u v : World) : satisfied (· ∈ ·) readingAlts u ⊆ satisfied (· ∈ ·) readingAlts v ↔
      ∀ q P, u ∈ alt q P → v ∈ alt q P := by
    rw [satisfied_subset_satisfied, readingAlts, forall_mem_range, Prod.forall]
    rfl
  have hM : IsMinimalCover readingAlts (alt .every .either)
      {⟨.ak, .ak⟩, ⟨.wp, .wp⟩, ⟨.ak, .wp⟩} :=
    by
    refine ⟨by decide, by simp only [le]; decide, ?_⟩
    rintro v (rfl | rfl | rfl) u (rfl | rfl | rfl) <;> simp only [le] <;> decide
  have h₁ : ⋂₀ satisfied (· ∈ ·) readingAlts ⟨.ak, .ak⟩ = alt .every .ak := by
    ext v; rw [mem_sInter_satisfied, le]; revert v; decide
  have h₂ : ⋂₀ satisfied (· ∈ ·) readingAlts ⟨.wp, .wp⟩ = alt .every .wp := by
    ext v; rw [mem_sInter_satisfied, le]; revert v; decide
  have h₃ : ⋂₀ satisfied (· ∈ ·) readingAlts ⟨.ak, .wp⟩ =
      alt .every .either ∩ alt .some .ak ∩ alt .some .wp := by
    ext v; rw [mem_sInter_satisfied, le]; revert v; decide
  rw [truthmakers_eq_image_of_isMinimalCover hM ⟨(.every, .either), rfl⟩, image_insert_eq,
    image_pair, h₁, h₂, h₃]

/-! ### Spain (8), on [mckay-vaninwagen-1977] -/

section Spain

open McKayVanInwagen1977

/-- The alternatives to *Spain fought with the Axis or the Allies*. -/
abbrev spainAlts : Set (Set SpainWorld) :=
  {foughtAxis ∪ foughtAllies, foughtAxis, foughtAllies, foughtAxis ∩ foughtAllies}

private theorem closestImp_spainSim (p q : Set SpainWorld) :
    closestImp spainSim p q = variablyStrictImp (fun _ ↦ univ) spainSim p q :=
  (holds (fun _ ↦ spainRank) p q).symm

private theorem spain_truthmakers :
    truthmakers spainAlts (foughtAxis ∪ foughtAllies) = {foughtAxis, foughtAllies} :=
  truthmakers_disjunction (by simp) (by simp)

-- (8)
theorem spain_collective :
    .actual ∈ disjunctiveImp spainSim (truthmakers spainAlts (foughtAxis ∪ foughtAllies))
      foughtAxis := by
  rw [disjunctiveImp_truthmakers _ _ (toFinite _) (mem_insert ..), closestImp_spainSim]
  exact spain_lewis_true

theorem spain_not_distributive :
    .actual ∉ distributiveImp spainSim (truthmakers spainAlts (foughtAxis ∪ foughtAllies))
      foughtAxis := by
  rw [spain_truthmakers, mem_distributiveImp_pair, closestImp_spainSim _ foughtAxis,
    closestImp_spainSim foughtAllies]
  exact fun h ↦ allies_implies_axis_false h.right

theorem spain_homogeneity :
    homogeneousImp spainSim (truthmakers spainAlts (foughtAxis ∪ foughtAllies)) foughtAxis
      .actual = .undefined := by
  rw [spain_truthmakers, homogeneousImp_eq_undefined_iff]
  refine ⟨⟨foughtAxis, .inl rfl, ?_⟩, foughtAllies, .inr rfl, ?_⟩
  · rw [closestImp_eq_univ_of_subset subset_rfl]
    trivial
  · rw [closestImp_spainSim]
    exact allies_implies_axis_false

theorem spain_distributive_singleton :
    .actual ∈ distributiveImp spainSim
      (truthmakers {foughtAxis ∪ foughtAllies} (foughtAxis ∪ foughtAllies)) foughtAxis := by
  rw [truthmakers_singleton ⟨.axis, Or.inl rfl⟩, distributiveImp_singleton, closestImp_spainSim]
  exact spain_lewis_true

end Spain

end Santorio2018
