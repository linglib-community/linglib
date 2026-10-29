module

public import Linglib.Semantics.Conditionals.Counterfactual

/-!
# Stalnaker (1981): A Defense of Conditional Excluded Middle

This file formalizes Stalnaker's defense of the selection-function analysis of conditionals against
Lewis's comparative-similarity analysis. The two differ by the limit assumption, that every possible
antecedent has closest worlds, and the uniqueness assumption, that it has at most one; in the logic
of conditionals the first is the consequence condition and the second is conditional excluded
middle, which is equivalent to the distribution of a conditional over a disjunctive consequent
(`cem_iff_distribution`). Uniqueness is neutralized by supervaluation: the selection functions in
use correspond to orderings with ties, and a conditional is true when every completion makes it true
(`superCounterfactual`). Supervaluation is not truth-functional, so conditional excluded middle
stays super-true while Quine's two counterfactuals about Bizet and Verdi come out neither true nor
false rather than, as for Lewis, both false (`bizet_italian_indet`, `bizet_verdi_cem`,
`bizet_cem_fails_universal`); distribution
likewise separates the analyses (`distribution_needs_uniqueness`, `distribution_fails_bizetverdi`).
Because Lewis's antecedents are necessity operators, his analysis predicts a scope ambiguity between
a quantifier inside and outside a counterfactual, as with the woman President Carter would have
appointed to the Supreme Court; selection predicts none, the two scopes coinciding
(`selection_scope`), and indeterminacy rather than ambiguity explains why no particular woman would
have been appointed (`court_no_particular_woman`).

The limit assumption cannot be neutralized in the same way, and dropping it has bizarre
consequences: for Lewis's line a little less than an inch long, his analysis makes *if the line had
been more than one inch long, it would not have been x inches long* true for every length x, so that
there is no length the line might have had, and the consequence condition fails. Nothing turns on
lengths: the same holds of any antecedent without closest worlds (`lewisWould_ne`,
`not_lewisMight_eq`, `not_consequence_lewisWould`). Finally, Lewis's *might* as the dual of *would*
collapses into *would* under conditional excluded middle; reading *might* instead as a possibility
operator over the whole conditional keeps Lewis's formulation, *if A, might B* true exactly when *if
A, would not-B* is not true, for a possible antecedent (`selectionalMight_iff`), and separates
*might* from *would* through indeterminacy (`might_would_asymmetry`).

## Implementation notes

The conditional logic of the first section is abstract: a conditional operator on
propositions with right weakening, agglomeration and a valid tautological consequent, the
finite form of the consequence condition. The limit assumption is stated for an arbitrary
similarity ordering and antecedent without closest worlds, the situation of the line example,
rather than on a model of lengths. The selection-similarity
correspondence of the paper's opening, the Moore-paradoxical status of denying a *would* while
affirming a *might*, and the Kennedy example are not formalized.

## References

* [stalnaker-1981]
* [lewis-1973b]
* [quine-1950]
* [van-fraassen-1966]
-/

@[expose] public section

namespace Stalnaker1981

open Conditional

/-! ### Conditional excluded middle and distribution -/

section ConditionalLogic

variable {W : Type*} (cond : Set W → Set W → Set W)

/-- A conditional operator satisfies the finite consequence condition when it weakens its
consequent, agglomerates consequents, and has every tautological consequent. -/
structure ConsequenceCondition : Prop where
  mono : ∀ A B C, B ⊆ C → cond A B ⊆ cond A C
  agg : ∀ A B C, cond A B ∩ cond A C ⊆ cond A (B ∩ C)
  taut : ∀ A, cond A Set.univ = Set.univ

/-- Conditional excluded middle holds for an operator when a conditional or its opposite holds
everywhere. -/
def CEM : Prop := ∀ A B, cond A B ∪ cond A Bᶜ = Set.univ

/-- An operator distributes when a conditional with a disjunctive consequent yields one with a
disjunct. -/
def Distribution : Prop := ∀ A B C, cond A (B ∪ C) ⊆ cond A B ∪ cond A C

theorem cem_iff_distribution (h : ConsequenceCondition cond) :
    CEM cond ↔ Distribution cond := by
  constructor
  · intro hcem A B C w hw
    rcases (Set.eq_univ_iff_forall.1 (hcem A B) w) with hB | hB
    · exact Or.inl hB
    · refine Or.inr (h.mono A (Bᶜ ∩ (B ∪ C)) C ?_ (h.agg A _ _ ⟨hB, hw⟩))
      rintro x ⟨hx, hxB | hxC⟩
      · exact absurd hxB hx
      · exact hxC
  · intro hdist A B
    refine Set.eq_univ_of_forall fun w ↦ hdist A B Bᶜ ?_
    rw [Set.union_compl_self, h.taut]
    trivial

end ConditionalLogic

/-! ### Selection: excluded middle and scope -/

section Selection

variable {W : Type*} (s : SelectionFunction W)

theorem selection_cem (A B : Set W) (w : W) :
    w ∈ selectionConditional s A B ∨ w ∈ selectionConditional s A Bᶜ :=
  selectionConditional_cem s

theorem selection_scope {ι : Type*} {A : Set W} (hA : A.Nonempty) (F : ι → Set W) (w : W) :
    w ∈ selectionConditional s A (⋃ x, F x) ↔ ∃ x, w ∈ selectionConditional s A (F x) := by
  simp only [mem_selectionConditional_of_nonempty s hA, Set.mem_iUnion]

end Selection

/-! ### Bizet and Verdi -/

section BizetVerdi

/-- The worlds of the Bizet–Verdi example are the actual world and the two closest worlds in
which the composers are compatriots. -/
inductive BVWorld
  | actual | bothItalian | bothFrench
  deriving Repr, DecidableEq, Fintype

/-- Similarity to `w₀` puts `w₀` strictly closest, and from the actual world the two compatriot
worlds tie. -/
abbrev bvSim (w₀ : BVWorld) : Preorder BVWorld :=
  Preorder.ofLE (fun w₁ w₂ ↦ w₁ = w₀ ∨ w₁ = w₂ ∨ w₀ = .actual ∧ w₁ ≠ .actual ∧ w₂ ≠ .actual)
    (by revert w₀; decide) (by revert w₀; decide)

instance (w₀ : BVWorld) : DecidableRel (bvSim w₀).le :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem isCentered_bvSim : IsCentered bvSim := fun w w' h ↦
  ⟨.inl rfl, by revert w w' h; decide⟩

/-- Bizet and Verdi are compatriots. -/
abbrev compatriots : Set BVWorld := {.bothItalian, .bothFrench}

/-- Bizet is Italian. -/
abbrev bizetItalian : Set BVWorld := {.bothItalian}

/-- Verdi is French. -/
abbrev verdiFrench : Set BVWorld := {.bothFrench}

theorem bizet_italian_indet :
    superCounterfactual bvSim compatriots bizetItalian .actual = 0 := by
  rw [superCounterfactual_eq_selectionalCounterfactual isCentered_bvSim]; decide

theorem verdi_french_indet :
    superCounterfactual bvSim compatriots verdiFrench .actual = 0 := by
  rw [superCounterfactual_eq_selectionalCounterfactual isCentered_bvSim]; decide

theorem bizet_verdi_cem :
    (∀ s : SelectionFunction BVWorld, s.Compatible bvSim →
      .actual ∈ selectionConditional s compatriots bizetItalian ∪
        selectionConditional s compatriots bizetItalianᶜ) ∧
    superCounterfactual bvSim compatriots bizetItalian .actual = 0 ∧
    superCounterfactual bvSim compatriots bizetItalianᶜ .actual = 0 := by
  refine ⟨cem_supervaluation bvSim compatriots bizetItalian .actual, bizet_italian_indet, ?_⟩
  rw [superCounterfactual_eq_selectionalCounterfactual isCentered_bvSim]; decide

theorem bizet_cem_fails_universal :
    .actual ∉ closestImp bvSim compatriots bizetItalian ∧
    .actual ∉ closestImp bvSim compatriots bizetItalianᶜ :=
  not_mem_ofDomain_and_compl (v := .bothItalian) (v' := .bothFrench) (by decide) (by decide) rfl
    (by decide)

theorem distribution_fails_bizetverdi :
    .actual ∈ closestImp bvSim compatriots (bizetItalian ∪ verdiFrench) ∧
    .actual ∉ closestImp bvSim compatriots bizetItalian ∧
    .actual ∉ closestImp bvSim compatriots verdiFrench :=
  ⟨by decide, by decide, by decide⟩

theorem distribution_needs_uniqueness :
    selectionalCounterfactual bvSim compatriots (bizetItalian ∪ verdiFrench) .actual = 1 ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = 0 ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = 0 :=
  ⟨by decide, by decide, by decide⟩

end BizetVerdi

/-! ### The Supreme Court appointment -/

section Court

/-- The worlds of the appointment example are the actual world, with no vacancy, and two equally
close worlds in which a vacancy is filled by a different woman. -/
inductive CourtWorld
  | actual | w1 | w2
  deriving Repr, DecidableEq, Fintype

/-- Similarity to `w₀` puts `w₀` strictly closest, and from the actual world the two vacancy
worlds tie. -/
abbrev courtSim (w₀ : CourtWorld) : Preorder CourtWorld :=
  Preorder.ofLE (fun w₁ w₂ ↦ w₁ = w₀ ∨ w₁ = w₂ ∨ w₀ = .actual ∧ w₁ ≠ .actual ∧ w₂ ≠ .actual)
    (by revert w₀; decide) (by revert w₀; decide)

instance (w₀ : CourtWorld) : DecidableRel (courtSim w₀).le :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem isCentered_courtSim : IsCentered courtSim := fun w w' h ↦
  ⟨.inl rfl, by revert w w' h; decide⟩

/-- A vacancy occurs. -/
abbrev vacancy : Set CourtWorld := {.w1, .w2}

/-- The women who might be appointed. -/
inductive Woman
  | a | b
  deriving DecidableEq, Fintype

/-- Woman `a` is appointed in the first vacancy world, woman `b` in the second. -/
def appointed : Woman → Set CourtWorld
  | .a => {.w1}
  | .b => {.w2}

instance (x : Woman) : DecidablePred (· ∈ appointed x) := fun w ↦ by
  cases x <;> exact inferInstanceAs (Decidable (w = _))

instance : DecidablePred (· ∈ ⋃ x, appointed x) := fun w ↦
  decidable_of_iff (∃ x, w ∈ appointed x) Set.mem_iUnion.symm

theorem court_scope_universal :
    .actual ∈ closestImp courtSim vacancy (⋃ x, appointed x) ∧
    ¬ ∃ x, .actual ∈ closestImp courtSim vacancy (appointed x) :=
  ⟨by decide, by decide⟩

theorem court_no_particular_woman :
    superCounterfactual courtSim vacancy (⋃ x, appointed x) .actual = 1 ∧
    ∀ x, superCounterfactual courtSim vacancy (appointed x) .actual = 0 := by
  simp only [superCounterfactual_eq_selectionalCounterfactual isCentered_courtSim]
  exact ⟨by decide, by decide⟩

end Court

/-! ### The limit assumption -/

section Limit

variable {W : Type*} {ord : W → Preorder W} {A : Set W} {w : W}

theorem lewisWould_ne (h : (ord w).minimals A = ∅) (x : W) :
    w ∈ variablyStrictImp (fun _ ↦ .univ) ord A {x}ᶜ :=
  mem_variablyStrictImp_compl_singleton h x

theorem not_lewisMight_eq (h : (ord w).minimals A = ∅) (x : W) :
    w ∉ might (variablyStrictImp (fun _ ↦ .univ) ord) A {x} :=
  notMem_might_variablyStrictImp_singleton h x

theorem not_consequence_lewisWould (h : (ord w).minimals A = ∅) (hA : A.Nonempty) :
    (⋂ x ∈ A, ({x}ᶜ : Set W)) ⊆ Aᶜ ∧
      (∀ x ∈ A, w ∈ variablyStrictImp (fun _ ↦ .univ) ord A {x}ᶜ) ∧
      w ∉ variablyStrictImp (fun _ ↦ .univ) ord A Aᶜ := by
  refine ⟨fun v hv hvA ↦ Set.mem_iInter₂.1 hv v hvA rfl, fun x _ ↦ lewisWould_ne h x, fun hw ↦ ?_⟩
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv, -, hvc⟩ := hw u ⟨trivial, hu⟩
  exact hvc v hv ((ord w).le_refl v) hv.2

end Limit

/-! ### Might -/

section Might

variable {W : Type*} [Fintype W] (ord : W → Preorder W) [∀ w, DecidableRel (ord w).le] (A B : Set W)
  [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (w : W)

theorem selectionalMight_iff (h : ((ord w).minimals A).Nonempty) :
    selectionalMight ord A B w ↔ selectionalCounterfactual ord A Bᶜ w ≠ 1 := by
  rw [selectionalMight, selectionalCounterfactual_compl h]
  cases selectionalCounterfactual ord A B w <;> decide

theorem might_would_asymmetry :
    selectionalMight bvSim compatriots bizetItalian .actual ∧
    selectionalMight bvSim compatriots verdiFrench .actual ∧
    selectionalCounterfactual bvSim compatriots bizetItalian .actual = 0 ∧
    selectionalCounterfactual bvSim compatriots verdiFrench .actual = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

end Might

end Stalnaker1981
