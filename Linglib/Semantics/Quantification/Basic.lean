module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Quantification.Properties
public import Linglib.Logic.Aristotelian.Square

/-!
# Concrete propositional generalized quantifiers

This file defines the generalized quantifiers *every*, *some*, *no* and the Russellian *the*,
whose truth conditions need no counting, and proves their conservativity, monotonicity,
symmetry, duality and square-of-opposition properties. The properties checked are Barwise and
Cooper's universals of conservativity and scope monotonicity, Keenan and Stavi's Boolean
structure, and Peters and Westerståhl's left monotonicity and smoothness. The counting
quantifiers such as *most* and *few* are in `Quantification/Counting.lean`.

## Main definitions

* `every`, `GQ.some`, `no`, `the`: the propositional denotations.
* `SatisfiesUniversals`: conservativity together with monotonicity in the scope.
* `square`: the square of opposition of `every`, `no`, `some` and `not every` at a restrictor.

## Main results

* `every_eq_sInf_image`, `some_eq_sSup_image`, `no_eq_compl_sSup_image`: the three determiners
  are the infimum, the supremum and the complement of the supremum of the scope over the
  restrictor.
* `every_iff_le`, `no_iff_disjoint`: the universal determiners are the pointwise order and
  disjointness on predicates.
* `square_relations`: with a non-empty restrictor the four stand in all six relations of the
  square, so its cells (`Aristotelian.Square.cell`) divide the scopes into those covering all of
  the restrictor, some but not all of it, and none of it.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [russell-1905]
* [van-benthem-1984]
* [van-de-pol-etal-2023]
-/

@[expose] public section

namespace Quantifier.GQ

/-! ### Denotations -/

/-- The universal determiner is `λR λS. ∀x. R(x) → S(x)`. -/
def every {α : Type*} : GQ α := fun R S ↦ ∀ x : α, R x → S x

/-- The existential determiner is `λR λS. ∃x. R(x) ∧ S(x)`. -/
protected def some {α : Type*} : GQ α := fun R S ↦ ∃ x : α, R x ∧ S x

/-- The negative determiner is `λR λS. ∀x. R(x) → ¬S(x)`. -/
def no {α : Type*} : GQ α := fun R S ↦ ∀ x : α, R x → ¬ S x

/-- The singular definite of [russell-1905] in Montagovian form,
`λR λS. ∃x. ∀y. (R(y) ↔ y = x) ∧ S(x)`. -/
def the {α : Type*} : GQ α := fun R S ↦ ∃ x : α, (∀ y, R y ↔ y = x) ∧ S x

theorem the_iff {α : Type*} (R S : α → Prop) :
    the R S ↔ (∃! x, R x) ∧ ∀ x, R x → S x := by
  constructor
  · rintro ⟨x, hx, hS⟩
    exact ⟨⟨x, (hx x).2 rfl, fun y hy ↦ (hx y).1 hy⟩, fun y hy ↦ (hx y).1 hy ▸ hS⟩
  · rintro ⟨⟨x, hx, huniq⟩, hS⟩
    exact ⟨x, fun y ↦ ⟨huniq y, fun h ↦ h ▸ hx⟩, hS x hx⟩

/-! ### The order on predicates -/

theorem every_iff_le {α : Type*} {R S : α → Prop} : every R S ↔ R ≤ S := Iff.rfl

theorem no_iff_le_compl {α : Type*} {R S : α → Prop} : no R S ↔ R ≤ Sᶜ := Iff.rfl

theorem no_iff_disjoint {α : Type*} {R S : α → Prop} : no R S ↔ Disjoint R S :=
  no_iff_le_compl.trans le_compl_iff_disjoint_right

section Decidable

variable {α : Type*} [Fintype α] {R S : α → Prop} [DecidablePred R] [DecidablePred S]

instance : Decidable (every R S) := inferInstanceAs (Decidable (∀ _, _))

instance : Decidable (GQ.some R S) := inferInstanceAs (Decidable (∃ _, _))

instance : Decidable (no R S) := inferInstanceAs (Decidable (∀ _, _))

end Decidable

/-- A quantifier satisfies Barwise and Cooper's semantic universals when it is conservative and
either monotone or antitone in its scope. -/
def SatisfiesUniversals {α : Type*} (q : GQ α) : Prop :=
  Conservative q ∧ (ScopeMonotone q ∨ ScopeAntitone q)

variable {α : Type*}

/-! ### Infima and suprema

At a restrictor `R`, `every R S` is the infimum of the values the scope takes on `R`, `GQ.some R S`
their supremum, and `no R S` the complement of their supremum, so the three determiners are
conjunction, disjunction and negative coordination over the restrictor. -/

theorem every_eq_sInf_image (R S : α → Prop) : every R S = sInf (S '' {x | R x}) := by
  rw [sInf_Prop_eq, Set.forall_mem_image]; rfl

theorem some_eq_sSup_image (R S : α → Prop) : GQ.some R S = sSup (S '' {x | R x}) := by
  rw [sSup_Prop_eq, Set.exists_mem_image]; rfl

theorem no_eq_compl_sSup_image (R S : α → Prop) : no R S = (sSup (S '' {x | R x}))ᶜ := by
  rw [← some_eq_sSup_image]; exact propext (by simp [no, GQ.some])

/-! ### Conservativity -/

theorem conservative_every : Conservative (every : GQ α) := by
  intro R S; simp only [every]
  exact ⟨fun h x hR ↦ ⟨hR, h x hR⟩, fun h x hR ↦ (h x hR).2⟩

theorem conservative_some : Conservative (GQ.some : GQ α) := by
  intro R S; simp only [GQ.some]
  exact ⟨fun ⟨x, hR, hS⟩ ↦ ⟨x, hR, hR, hS⟩, fun ⟨x, hR, _, hS⟩ ↦ ⟨x, hR, hS⟩⟩

theorem conservative_no : Conservative (no : GQ α) := by
  intro R S; simp only [no]
  exact ⟨fun h x hR ⟨_, hS⟩ ↦ h x hR hS, fun h x hR hS ↦ h x hR ⟨hR, hS⟩⟩

/-! ### Quantity invariance -/

theorem quantityInvariant_every : QuantityInvariant (every : GQ α) := by
  intro A B A' B' f hBij hA hB
  simp only [every]
  rw [hBij.surjective.forall]
  exact forall_congr' fun x ↦ by
    rw [show A (f x) ↔ A' x from hA x, show B (f x) ↔ B' x from hB x]

/-! ### Scope monotonicity -/

theorem scopeMonotone_every : ScopeMonotone (every : GQ α) := by
  intro R S S' hSS' h x hR; exact hSS' x (h x hR)

theorem scopeMonotone_some : ScopeMonotone (GQ.some : GQ α) := by
  intro R S S' hSS' ⟨x, hR, hS⟩; exact ⟨x, hR, hSS' x hS⟩

theorem scopeAntitone_no : ScopeAntitone (no : GQ α) := by
  intro R S S' hSS' h x hR hS; exact h x hR (hSS' x hS)

theorem scopeMonotone_the : ScopeMonotone (the : GQ α) := by
  intro R S S' hSS' ⟨x, hR, hS⟩; exact ⟨x, hR, hSS' x hS⟩

theorem not_scopeAntitone_some [Nonempty α] : ¬ ScopeAntitone (GQ.some : GQ α) := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  let ⟨_, _, hb⟩ := h (fun _ ↦ True) (bot_le (a := fun _ ↦ True)) ⟨x, trivial, trivial⟩
  hb

theorem not_scopeAntitone_every [Nonempty α] : ¬ ScopeAntitone (every : GQ α) := fun h ↦
  let ⟨x⟩ := ‹Nonempty α›
  h (fun _ ↦ True) (bot_le (a := fun _ ↦ True)) (fun _ _ ↦ trivial) x trivial

theorem monotone_every (R : α → Prop) : Monotone (every R) :=
  scopeMonotone_every R

theorem monotone_some (R : α → Prop) : Monotone (GQ.some R) :=
  scopeMonotone_some R

theorem antitone_no (R : α → Prop) : Antitone (no R) :=
  scopeAntitone_no R

/-! ### Symmetry (P&W Ch.6) -/

instance symm_some : Std.Symm (GQ.some : GQ α) := ⟨fun _ _ ⟨x, hR, hS⟩ ↦ ⟨x, hS, hR⟩⟩

instance symm_no : Std.Symm (no : GQ α) := ⟨fun _ _ h x hS hR ↦ h x hR hS⟩

/-! ### Intersectivity (CONSERV + SYMM bridge) -/

theorem intersectionCondition_some : IntersectionCondition (GQ.some : GQ α) := by
  intro R S R' S' hInt
  simp only [GQ.some]
  exact ⟨fun ⟨x, hR, hS⟩ ↦ let ⟨hR', hS'⟩ := (hInt x).mp ⟨hR, hS⟩; ⟨x, hR', hS'⟩,
         fun ⟨x, hR', hS'⟩ ↦ let ⟨hR, hS⟩ := (hInt x).mpr ⟨hR', hS'⟩; ⟨x, hR, hS⟩⟩

theorem intersectionCondition_no : IntersectionCondition (no : GQ α) := by
  intro R S R' S' hInt
  simp only [no]
  refine ⟨fun h x hR' hS' ↦ h x ((hInt x).mpr ⟨hR', hS'⟩).1 ((hInt x).mpr ⟨hR', hS'⟩).2,
          fun h x hR hS ↦ h x ((hInt x).mp ⟨hR, hS⟩).1 ((hInt x).mp ⟨hR, hS⟩).2⟩

/-! ### Left/right anti-additivity (P&W §5.8) -/

theorem leftAntiAdditive_every : LeftAntiAdditive (every : GQ α) := by
  intro R R' S; simp only [every]
  refine ⟨fun h ↦ ⟨fun x hR ↦ h x (Or.inl hR), fun x hR' ↦ h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' ↦ hRR'.elim (h1 x) (h2 x)⟩

theorem leftAntiAdditive_no : LeftAntiAdditive (no : GQ α) := by
  intro R R' S; simp only [no]
  refine ⟨fun h ↦ ⟨fun x hR ↦ h x (Or.inl hR), fun x hR' ↦ h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' ↦ hRR'.elim (h1 x) (h2 x)⟩

theorem rightAntiAdditive_no : RightAntiAdditive (no : GQ α) := by
  intro R S S'; simp only [no]
  refine ⟨fun h ↦ ⟨fun x hR hS ↦ h x hR (Or.inl hS),
                    fun x hR hS' ↦ h x hR (Or.inr hS')⟩,
          fun ⟨h1, h2⟩ x hR hSS' ↦ hSS'.elim (h1 x hR) (h2 x hR)⟩

/-! ### Duality square (B&C §4.11) -/

theorem innerNeg_every :
    (innerNeg (every : GQ α) : GQ α) = (no : GQ α) := by
  funext R S; simp only [innerNeg, every, no]

theorem dual_every :
    (dual (every : GQ α) : GQ α) = (GQ.some : GQ α) := by
  funext R S; simp only [dual, compl_apply, innerNeg, every, GQ.some]
  exact propext ⟨fun h ↦ by push Not at h; exact h,
                 fun ⟨x, hR, hS⟩ h ↦ h x hR hS⟩

theorem compl_some :
    ((GQ.some : GQ α)ᶜ : GQ α) = (no : GQ α) := by
  funext R S; simp only [compl_apply, GQ.some, no]
  exact propext ⟨fun h x hR hS ↦ h ⟨x, hR, hS⟩,
                 fun h ⟨x, hR, hS⟩ ↦ h x hR hS⟩

/-! ### Positive/negative strong (P&W Ch.6) -/

theorem positiveStrong_every : PositiveStrong (every : GQ α) := by
  intro R x hR; exact hR

theorem no_negative_strong_nonempty (R : α → Prop)
    (hR : ∃ x : α, R x) :
    ¬ (no : GQ α) R R := by
  intro h; obtain ⟨x, hRx⟩ := hR; exact h x hRx hRx

/-! ### K&S existential det classification (§3.3, G3) -/

theorem existential_some : Existential (GQ.some : GQ α) := by
  intro R S; simp only [GQ.some]
  exact ⟨fun ⟨x, hR, hS⟩ ↦ ⟨x, ⟨hR, hS⟩, trivial⟩,
         fun ⟨x, ⟨hR, hS⟩, _⟩ ↦ ⟨x, hR, hS⟩⟩

theorem existential_no : Existential (no : GQ α) := by
  intro R S; simp only [no]
  exact ⟨fun h x ⟨hR, hS⟩ _ ↦ h x hR hS,
         fun h x hR hS ↦ h x ⟨hR, hS⟩ trivial⟩

/-! ### Relational properties ([van-benthem-1984]) -/

instance isTrans_every : IsTrans _ (every : GQ α) := ⟨fun _ _ _ hAB hBC x hA ↦ hBC x (hAB x hA)⟩

instance antisymm_every : Std.Antisymm (every : GQ α) :=
  ⟨fun _ _ hAB hBA ↦ funext fun x ↦ propext ⟨hAB x, hBA x⟩⟩

theorem quasiReflexive_some : QuasiReflexive (GQ.some : GQ α) := by
  intro A B ⟨x, hA, _⟩; exact ⟨x, hA, hA⟩

theorem quasiUniversal_no : QuasiUniversal (no : GQ α) := by
  intro A B hAA x hA; exact absurd hA (hAA x hA)

/-! ### Double monotonicity classification ([van-benthem-1984] §4.2) -/

theorem restrictorAntitone_every : RestrictorAntitone (every : GQ α) :=
  zwarts_refl_trans_restrictorDown _ conservative_every positiveStrong_every
    isTrans_every

theorem restrictorMonotone_some : RestrictorMonotone (GQ.some : GQ α) := by
  intro R R' S hRR' ⟨x, hR, hS⟩; exact ⟨x, hRR' x hR, hS⟩

theorem restrictorAntitone_no : RestrictorAntitone (no : GQ α) := by
  intro R R' S hRR' hQ x hR; exact hQ x (hRR' x hR)

theorem doubleMono_every :
    RestrictorAntitone (every : GQ α) ∧
    ScopeMonotone (every : GQ α) :=
  ⟨restrictorAntitone_every, scopeMonotone_every⟩

theorem doubleMono_some :
    RestrictorMonotone (GQ.some : GQ α) ∧
    ScopeMonotone (GQ.some : GQ α) :=
  ⟨restrictorMonotone_some, scopeMonotone_some⟩

theorem doubleMono_no :
    RestrictorAntitone (no : GQ α) ∧
    ScopeAntitone (no : GQ α) :=
  ⟨restrictorAntitone_no, scopeAntitone_no⟩

theorem doubleMono_compl_every :
    RestrictorMonotone ((every : GQ α)ᶜ) ∧
    ScopeAntitone ((every : GQ α)ᶜ) :=
  ⟨RestrictorAntitone.compl _ restrictorAntitone_every,
   ScopeMonotone.compl _ scopeMonotone_every⟩

theorem scopeIntersective_every : ScopeIntersective (every : GQ α) :=
  fun _ _ _ hAB hAC x hA ↦ ⟨hAB x hA, hAC x hA⟩

theorem filtrating_every : Filtrating (every : GQ α) :=
  ⟨scopeMonotone_every, scopeIntersective_every⟩

/-! ### Aristotelian square of opposition

At a restrictor `R`, the denotations `every R`, `no R`, `GQ.some R` and `everyᶜ R` are the corners
of a square in the Boolean algebra `(α → Prop) → Prop`. Outer negation is the Boolean complement,
so the diagonals are contradictory at every restrictor. Contrariety, and with it the
subalternations and subcontrariety, needs existential import: at an empty restrictor `every` and
`no` both hold vacuously (`a_e_contrary`), and `square_relations` assumes a non-empty one.
-/

/-- At a restrictor `R` the four determiners form a square of opposition. -/
def square (R : α → Prop) : Aristotelian.Square ((α → Prop) → Prop) where
  A := every R
  E := no R
  I := GQ.some R
  O := (every : GQ α)ᶜ R

theorem every_contradicts_notEvery (R S : α → Prop) :
    (every : GQ α) R S ↔ ¬ ((every : GQ α)ᶜ R S) := by
  simp [compl_apply, Classical.not_not]

theorem no_contradicts_some (R S : α → Prop) :
    (no : GQ α) R S ↔ ¬ ((GQ.some : GQ α) R S) := by
  simp only [no, GQ.some]; push Not; rfl

theorem a_e_contrary (R S : α → Prop) :
    (every : GQ α) R S → (no : GQ α) R S →
    ∀ x : α, ¬ R x := by
  intro hA hE x hR; exact hE x hR (hA x hR)

theorem square_relations {R : α → Prop} (hR : ∃ x : α, R x) :
    Aristotelian.SquareRelations (square R) :=
  .of_disjoint (funext fun S ↦ propext <| iff_not_comm.mp (no_contradicts_some R S)) rfl <|
    Pi.disjoint_iff.mpr fun S ↦ Prop.disjoint_iff.mpr fun ⟨hA, hE⟩ ↦
      let ⟨x, hx⟩ := hR; a_e_contrary R S hA hE x hx

theorem subalternation_a_i (R S : α → Prop) (hR : ∃ x : α, R x) :
    (every : GQ α) R S → (GQ.some : GQ α) R S :=
  (square_relations hR).subalternAI S

/-! ### Basic left monotonicities ([peters-westerstahl-2006] §5.5) -/

theorem upSE_some : UpSEMon (GQ.some : GQ α) :=
  RestrictorMonotone.upSE _ restrictorMonotone_some

theorem upSW_some : UpSWMon (GQ.some : GQ α) :=
  RestrictorMonotone.upSW _ restrictorMonotone_some

theorem downNW_every : DownNWMon (every : GQ α) :=
  RestrictorAntitone.downNW _ restrictorAntitone_every

theorem downNE_every : DownNEMon (every : GQ α) :=
  RestrictorAntitone.downNE _ restrictorAntitone_every

theorem downNW_no : DownNWMon (no : GQ α) :=
  RestrictorAntitone.downNW _ restrictorAntitone_no

theorem downNE_no : DownNEMon (no : GQ α) :=
  RestrictorAntitone.downNE _ restrictorAntitone_no

/-! ### Smooth quantifiers ([peters-westerstahl-2006] §5.6) -/

theorem downNE_some : DownNEMon (GQ.some : GQ α) := by
  intro R S R' _ hKeep ⟨x, hR, hS⟩
  exact ⟨x, hKeep x hR hS, hS⟩

theorem smooth_some : Smooth (GQ.some : GQ α) :=
  ⟨downNE_some, RestrictorMonotone.upSE _ restrictorMonotone_some⟩

theorem upSE_every : UpSEMon (every : GQ α) := by
  intro R S R' _ hDiff hQ x hR'
  by_cases hS : S x
  · exact hS
  · exact hQ x (hDiff x hR' hS)

theorem smooth_every : Smooth (every : GQ α) :=
  ⟨downNE_every, upSE_every⟩

theorem coSmooth_no : CoSmooth (no : GQ α) :=
  ⟨downNW_no, fun _ _ _ _ hInt hQ x hR' hS ↦ hQ x (hInt x hR' hS) hS⟩

/-! ### Satisfies universals: B&C's CONS + MON ([barwise-cooper-1981]; used as a
learnability/complexity target by [van-de-pol-etal-2023]) -/

theorem satisfiesUniversals_some : SatisfiesUniversals (GQ.some : GQ α) :=
  ⟨conservative_some, Or.inl scopeMonotone_some⟩

theorem satisfiesUniversals_every : SatisfiesUniversals (every : GQ α) :=
  ⟨conservative_every, Or.inl scopeMonotone_every⟩

theorem satisfiesUniversals_no : SatisfiesUniversals (no : GQ α) :=
  ⟨conservative_no, Or.inr scopeAntitone_no⟩

end Quantifier.GQ
