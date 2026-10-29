module

public import Linglib.Semantics.Quantification.Defs

/-!
# Properties of generalized quantifiers

This file proves the general theorems about the properties of generalized quantifiers defined
in `Quantification/Defs.lean`. The negations and the dual reverse monotonicity and preserve
quantity invariance; conservativity and monotonicity are closed under the Boolean operations
and under adjectival restriction, as Keenan and Stavi show; and conservativity together with
symmetry or with the left monotonicities yields the characterizations of van Benthem and of
Peters and Westerståhl. Barwise and Cooper's theorems on type ⟨1⟩ quantifiers close the file.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [van-benthem-1984]
* [van-benthem-1986]
-/

@[expose] public section

namespace Quantifier.GQ


open Quantifier.NP
variable {α : Type*}

/-! ### Duality Theorems -/

theorem ScopeMonotone.compl (q : GQ α)
    (h : ScopeMonotone q) : ScopeAntitone (qᶜ) := by
  intro R S S' hSS' hNeg hQS
  exact hNeg (h R hSS' hQS)

theorem ScopeAntitone.compl (q : GQ α)
    (h : ScopeAntitone q) : ScopeMonotone (qᶜ) := by
  intro R S S' hSS' hNeg hQS'
  exact hNeg (h R hSS' hQS')

theorem ScopeMonotone.innerNeg (q : GQ α)
    (h : ScopeMonotone q) : ScopeAntitone (innerNeg q) := by
  intro R S S' hSS' hInner
  exact h R (show (fun x => ¬ S' x) ≤ (fun x => ¬ S x) from fun x hNS' hSx => hNS' (hSS' x hSx))
    hInner

theorem ScopeAntitone.innerNeg (q : GQ α)
    (h : ScopeAntitone q) : ScopeMonotone (innerNeg q) := by
  intro R S S' hSS' hInner
  exact h R (show (fun x => ¬ S' x) ≤ (fun x => ¬ S x) from fun x hNS' hSx => hNS' (hSS' x hSx))
    hInner

theorem RestrictorMonotone.compl (q : GQ α)
    (h : RestrictorMonotone q) : RestrictorAntitone (qᶜ) := by
  intro S R R' hRR' hNeg hQR
  exact hNeg (h S hRR' hQR)

theorem RestrictorAntitone.compl (q : GQ α)
    (h : RestrictorAntitone q) : RestrictorMonotone (qᶜ) := by
  intro S R R' hRR' hNeg hQR'
  exact hNeg (h S hRR' hQR')

theorem innerNeg_innerNeg (q : GQ α) : innerNeg (innerNeg q) = q := by
  funext R S; simp [innerNeg]

theorem dual_dual (q : GQ α) : dual (dual q) = q := by
  funext R S; simp [dual, compl_apply, innerNeg]

/-! #### QuantityInvariant closure -/

theorem QuantityInvariant.compl (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (qᶜ) := by
  intro A B A' B' f hBij hA hB
  simp only [compl_apply, not_iff_not]
  exact h A B A' B' f hBij hA hB

theorem QuantityInvariant.innerNeg (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (innerNeg q) := by
  intro A B A' B' f hBij hA hB
  exact h A (fun x => ¬ B x) A' (fun x => ¬ B' x) f hBij hA (fun x => not_congr (hB x))

theorem QuantityInvariant.dual (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (dual q) :=
  QuantityInvariant.compl _ (QuantityInvariant.innerNeg _ h)

theorem QuantityInvariant.inf (f g : GQ α)
    (hf : QuantityInvariant f) (hg : QuantityInvariant g) :
    QuantityInvariant ((f ⊓ g)) := by
  intro A B A' B' σ hBij hA hB
  simp only [inf_apply]
  exact and_congr (hf A B A' B' σ hBij hA hB) (hg A B A' B' σ hBij hA hB)

theorem QuantityInvariant.sup (f g : GQ α)
    (hf : QuantityInvariant f) (hg : QuantityInvariant g) :
    QuantityInvariant ((f ⊔ g)) := by
  intro A B A' B' σ hBij hA hB
  simp only [sup_apply]
  exact or_congr (hf A B A' B' σ hBij hA hB) (hg A B A' B' σ hBij hA hB)

theorem intersection_conservative_symmetric (q : GQ α)
    (hCons : Conservative q) (hInt : IntersectionCondition q) :
    Std.Symm q :=
  ⟨fun R S h => by
    rw [hCons R S] at h
    rw [hCons S R]
    exact (hInt R (fun x => R x ∧ S x) S (fun x => S x ∧ R x) fun x =>
      ⟨fun ⟨_, hR, hS⟩ => ⟨hS, hS, hR⟩, fun ⟨_, hS, hR⟩ => ⟨hR, hR, hS⟩⟩).mp h⟩

/-- Scope-downward monotonicity is equivalent to scope-upward monotonicity of the inner negation,
the co-property characterization of [peters-westerstahl-2006] §3.2.3. -/
theorem co_property_mono (q : GQ α) :
    ScopeAntitone q ↔ ScopeMonotone (innerNeg q) := by
  constructor
  · exact ScopeAntitone.innerNeg q
  · intro h
    have h' := ScopeMonotone.innerNeg (innerNeg q) h
    rw [innerNeg_innerNeg] at h'
    exact h'

/-! ### Conservativity, Symmetry, and Strength -/

theorem Conservative.congr_scope {q : GQ α} (h : Conservative q) {X S S' : α → Prop}
    (hSS : ∀ x, X x → (S x ↔ S' x)) : q X S ↔ q X S' := by
  rw [h X S, h X S']
  exact iff_of_eq (congrArg _ (funext fun x => propext (and_congr_right (hSS x))))

/-- Under conservativity, symmetric ↔ intersective (P&W Ch.6 Fact 1).
    This is the single most important bridge theorem — it explains why
    weak determiners allow there-insertion. -/
theorem conserv_symm_iff_int (q : GQ α) (hCons : Conservative q) :
    Std.Symm q ↔ IntersectionCondition q := by
  constructor
  · intro hSym R S R' S' hEq
    have step_RS : q R S ↔ q (fun x => R x ∧ S x) (fun x => R x ∧ S x) := by
      calc q R S
          ↔ q R (fun x => R x ∧ S x) := hCons R S
        _ ↔ q (fun x => R x ∧ S x) R := ⟨hSym.symm _ _, hSym.symm _ _⟩
        _ ↔ q (fun x => R x ∧ S x) (fun x => (R x ∧ S x) ∧ R x) :=
            hCons (fun x => R x ∧ S x) R
        _ ↔ q (fun x => R x ∧ S x) (fun x => R x ∧ S x) := by
            congr! 2 with x; tauto
    have step_R'S' : q R' S' ↔ q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) := by
      calc q R' S'
          ↔ q R' (fun x => R' x ∧ S' x) := hCons R' S'
        _ ↔ q (fun x => R' x ∧ S' x) R' := ⟨hSym.symm _ _, hSym.symm _ _⟩
        _ ↔ q (fun x => R' x ∧ S' x) (fun x => (R' x ∧ S' x) ∧ R' x) :=
            hCons (fun x => R' x ∧ S' x) R'
        _ ↔ q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) := by
            congr! 2 with x; tauto
    rw [step_RS, step_R'S']
    have hFun : (fun x => R x ∧ S x) = (fun x => R' x ∧ S' x) :=
      funext fun x => propext (hEq x)
    rw [hFun]
  · exact intersection_conservative_symmetric q hCons

/-- Non-trivial symmetric quantifiers are not positive strong (P&W Ch.6 Fact 7). -/
theorem symm_not_positive_strong (q : GQ α) (hCons : Conservative q)
    (hSym : Std.Symm q)
    (hNontrivF : ∃ R S, ¬ q R S) :
    ¬ PositiveStrong q := by
  intro hPos
  obtain ⟨R', S', hF⟩ := hNontrivF
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have hSame : q (fun x => R' x ∧ S' x) (fun x => R' x ∧ S' x) ↔ q R' S' := by
    apply hInt; intro x; tauto
  exact hF (hSame.mp (hPos _))

/-- Conservativity of a GQ is equivalent to its restricted quantifiers
    living on their restrictors (P&W §3.2.2). -/
theorem conservative_iff_livesOn (q : GQ α) :
    Conservative q ↔ ∀ A, LivesOn (q A) A :=
  .rfl

theorem Conservative.iff_of_inf_eq {q : GQ α} (hq : Conservative q) {R S S' : α → Prop}
    (h : R ⊓ S = R ⊓ S') : q R S ↔ q R S' :=
  (hq R S).trans ((Iff.of_eq (congrArg (q R) h)).trans (hq R S').symm)

/-! ### Basic Left Monotonicity and Smoothness ([peters-westerstahl-2006] §5.5-5.6) -/

theorem RestrictorMonotone.upSE (q : GQ α)
    (h : RestrictorMonotone q) : UpSEMon q :=
  fun _ S _ hSub _ hQ => h S hSub hQ

theorem RestrictorMonotone.upSW (q : GQ α)
    (h : RestrictorMonotone q) : UpSWMon q :=
  fun _ S _ hSub _ hQ => h S hSub hQ

theorem restrictorMonotone_of_upSW_of_upSE (q : GQ α)
    (hSW : UpSWMon q) (hSE : UpSEMon q) : RestrictorMonotone q := by
  intro S R R' hSub hQ
  classical
  let R'' : α → Prop := fun x => R x ∨ (R' x ∧ ¬ S x)
  have step1 : q R'' S := by
    apply hSW R S R'' (fun x hRx => Or.inl hRx) ?_ hQ
    intro x hR''x hSx
    rcases hR''x with h | h
    · exact h
    · exact absurd hSx h.2
  apply hSE R'' S R' (fun x hR''x => ?_) (fun x hR'x hNS => ?_) step1
  · rcases hR''x with h | h
    · exact hSub x h
    · exact h.1
  · exact Or.inr ⟨hR'x, hNS⟩

theorem restrictorMonotone_iff_upSW_and_upSE (q : GQ α) :
    RestrictorMonotone q ↔ UpSWMon q ∧ UpSEMon q :=
  ⟨fun h => ⟨RestrictorMonotone.upSW q h, RestrictorMonotone.upSE q h⟩,
   fun ⟨hSW, hSE⟩ => restrictorMonotone_of_upSW_of_upSE q hSW hSE⟩

theorem RestrictorAntitone.downNW (q : GQ α)
    (h : RestrictorAntitone q) : DownNWMon q :=
  fun _ S _ hSub _ hQ => h S hSub hQ

theorem RestrictorAntitone.downNE (q : GQ α)
    (h : RestrictorAntitone q) : DownNEMon q :=
  fun _ S _ hSub _ hQ => h S hSub hQ

theorem restrictorAntitone_of_downNW_of_downNE (q : GQ α)
    (hNW : DownNWMon q) (hNE : DownNEMon q) : RestrictorAntitone q := by
  intro S R R' hSub hQ
  classical
  let R'' : α → Prop := fun x => R x ∨ (R' x ∧ S x)
  have step1 : q R'' S := by
    apply hNE R' S R'' (fun x hR''x => ?_) (fun x hR'x hSx => ?_) hQ
    · rcases hR''x with h | h
      · exact hSub x h
      · exact h.1
    · exact Or.inr ⟨hR'x, hSx⟩
  apply hNW R'' S R (fun x hRx => Or.inl hRx) ?_ step1
  intro x hR''x hNS
  rcases hR''x with h | h
  · exact h
  · exact absurd h.2 hNS

theorem restrictorAntitone_iff_downNW_and_downNE (q : GQ α) :
    RestrictorAntitone q ↔ DownNWMon q ∧ DownNEMon q :=
  ⟨fun h => ⟨RestrictorAntitone.downNW q h, RestrictorAntitone.downNE q h⟩,
   fun ⟨hNW, hNE⟩ => restrictorAntitone_of_downNW_of_downNE q hNW hNE⟩

-- Prop 8: Negation rotates basic monotonicities

theorem UpSEMon.compl (q : GQ α)
    (h : UpSEMon q) : DownNWMon (qᶜ) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

theorem DownNWMon.compl (q : GQ α)
    (h : DownNWMon q) : UpSEMon (qᶜ) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

theorem UpSWMon.compl (q : GQ α)
    (h : UpSWMon q) : DownNEMon (qᶜ) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

theorem DownNEMon.compl (q : GQ α)
    (h : DownNEMon q) : UpSWMon (qᶜ) := by
  intro R S R' hSub hDiff hNQ hQR'
  exact hNQ (h R' S R hSub hDiff hQR')

theorem DownNEMon.innerNeg (q : GQ α)
    (h : DownNEMon q) : DownNWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hRx hNS => hDiff x hRx (fun hSx => hNS hSx)) hQ

theorem DownNWMon.innerNeg (q : GQ α)
    (h : DownNWMon q) : DownNEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hRx hNNS => hDiff x hRx (Classical.not_not.mp hNNS)) hQ

theorem UpSEMon.innerNeg (q : GQ α)
    (h : UpSEMon q) : UpSWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hR'x hNNS => hDiff x hR'x (Classical.not_not.mp hNNS)) hQ

theorem UpSWMon.innerNeg (q : GQ α)
    (h : UpSWMon q) : UpSEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  exact h R (fun x => ¬ S x) R' hSub
    (fun x hR'x hNS => hDiff x hR'x (fun hSx => hNS hSx)) hQ

theorem smooth_iff_coSmooth_compl (q : GQ α) :
    Smooth q ↔ CoSmooth (qᶜ) :=
  ⟨fun ⟨hNE, hSE⟩ => ⟨UpSEMon.compl q hSE, DownNEMon.compl q hNE⟩,
   fun ⟨hNW, hSW⟩ => by
    rw [show q = qᶜᶜ from (compl_compl q).symm]
    exact ⟨UpSWMon.compl _ hSW, DownNWMon.compl _ hNW⟩⟩

theorem smooth_iff_coSmooth_innerNeg (q : GQ α) :
    Smooth q ↔ CoSmooth (innerNeg q) :=
  ⟨fun ⟨hNE, hSE⟩ => ⟨DownNEMon.innerNeg q hNE, UpSEMon.innerNeg q hSE⟩,
   fun ⟨hNW, hSW⟩ => by
    rw [show q = innerNeg (innerNeg q) from (innerNeg_innerNeg q).symm]
    exact ⟨DownNWMon.innerNeg _ hNW, UpSWMon.innerNeg _ hSW⟩⟩

-- Prop 9: Smooth → Mon↑

theorem scopeMonotone_of_smooth (q : GQ α)
    (hCons : Conservative q) (hSmooth : Smooth q) : ScopeMonotone q := by
  obtain ⟨hNE, hSE⟩ := hSmooth
  intro R S S' hSS' hQ
  classical
  let R' : α → Prop := fun x => R x ∧ (S x ∨ ¬ S' x)
  have hR'S : q R' S := by
    apply hNE R S R' (fun x hR'x => hR'x.1) (fun x hRx hSx => ⟨hRx, Or.inl hSx⟩) hQ
  have key : ∀ x, (R' x ∧ S' x) ↔ (R' x ∧ S x) := by
    intro x
    constructor
    · rintro ⟨hR'x, hS'x⟩
      refine ⟨hR'x, ?_⟩
      rcases hR'x.2 with hSx | hNS'x
      · exact hSx
      · exact absurd hS'x hNS'x
    · rintro ⟨hR'x, hSx⟩
      exact ⟨hR'x, hSS' x hSx⟩
  have hR'S' : q R' S' := by
    rw [hCons R' S']
    have : (fun x => R' x ∧ S' x) = (fun x => R' x ∧ S x) := funext fun x => propext (key x)
    rw [this]
    exact (hCons R' S).mp hR'S
  apply hSE R' S' R (fun x hR'x => hR'x.1) (fun x hRx hS'nS => ?_) hR'S'
  exact ⟨hRx, Or.inr hS'nS⟩

-- Prop 7: Symmetry ↔ ↑_SW + ↓_NE (under CONSERV)

theorem upSW_and_downNE_of_symm (q : GQ α)
    (hCons : Conservative q) (hSym : Std.Symm q) :
    UpSWMon q ∧ DownNEMon q := by
  have toIntersect : ∀ A B : α → Prop,
      q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    have h1 : q A B ↔ q A (fun x => A x ∧ B x) := hCons A B
    have h2 : q A (fun x => A x ∧ B x) ↔ q (fun x => A x ∧ B x) A :=
      ⟨hSym.symm _ _, hSym.symm _ _⟩
    have h3 : q (fun x => A x ∧ B x) A ↔
        q (fun x => A x ∧ B x) (fun x => (A x ∧ B x) ∧ A x) :=
      hCons (fun x => A x ∧ B x) A
    have h4 : (fun x => (A x ∧ B x) ∧ A x) = (fun x => A x ∧ B x) :=
      funext fun x => propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h.1⟩⟩
    rw [h1, h2, h3, h4]
  have intersect_eq (R S R' : α → Prop)
      (hFwd : ∀ x, R x → S x → R' x)
      (hBwd : ∀ x, R' x → S x → R x) :
      (fun x => R x ∧ S x) = (fun x => R' x ∧ S x) := by
    funext x
    apply propext
    exact ⟨fun ⟨hRx, hSx⟩ => ⟨hFwd x hRx hSx, hSx⟩,
           fun ⟨hR'x, hSx⟩ => ⟨hBwd x hR'x hSx, hSx⟩⟩
  refine ⟨?_, ?_⟩
  · intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' (fun x hRx _ => hSub x hRx) hInt] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ
  · intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' hInt (fun x hR'x _ => hSub x hR'x)] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ

theorem symm_of_upSW_of_downNE (q : GQ α)
    (hCons : Conservative q) (hUpSW : UpSWMon q) (hDownNE : DownNEMon q) :
    Std.Symm q := by
  refine ⟨fun A B hQ => ?_⟩
  rw [hCons A B] at hQ
  have hABint : q (fun x => A x ∨ B x) (fun x => A x ∧ B x) := by
    apply hUpSW A (fun x => A x ∧ B x) (fun x => A x ∨ B x)
      (fun x hAx => Or.inl hAx) (fun x _ hIntx => hIntx.1) hQ
  have hBint : q B (fun x => A x ∧ B x) := by
    apply hDownNE (fun x => A x ∨ B x) (fun x => A x ∧ B x) B
      (fun x hBx => Or.inr hBx) (fun x _ hIntx => hIntx.2) hABint
  rw [hCons B A]
  have hCommSwap : (fun x => B x ∧ A x) = (fun x => A x ∧ B x) :=
    funext fun x => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  rw [hCommSwap]
  exact hBint

theorem symm_iff_upSW_and_downNE (q : GQ α) (hCons : Conservative q) :
    Std.Symm q ↔ (UpSWMon q ∧ DownNEMon q) :=
  ⟨upSW_and_downNE_of_symm q hCons,
   fun ⟨h1, h2⟩ => symm_of_upSW_of_downNE q hCons h1 h2⟩

/-! ### Boolean Closure ([keenan-stavi-1986]) -/

theorem Conservative.compl (q : GQ α) (h : Conservative q) :
    Conservative (qᶜ) := by
  intro R S; simp only [compl_apply, not_iff_not]; exact h R S

theorem Conservative.inf (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative ((f ⊓ g)) := by
  intro R S; simp only [inf_apply]; exact and_congr (hf R S) (hg R S)

theorem Conservative.sup (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative ((f ⊔ g)) := by
  intro R S; simp only [sup_apply]; exact or_congr (hf R S) (hg R S)

theorem ScopeMonotone.inf (f g : GQ α)
    (hf : ScopeMonotone f) (hg : ScopeMonotone g) :
    ScopeMonotone ((f ⊓ g)) := by
  intro R S S' hSS' ⟨hfRS, hgRS⟩
  exact ⟨hf R hSS' hfRS, hg R hSS' hgRS⟩

theorem ScopeAntitone.inf (f g : GQ α)
    (hf : ScopeAntitone f) (hg : ScopeAntitone g) :
    ScopeAntitone ((f ⊓ g)) := by
  intro R S S' hSS' ⟨hfRS', hgRS'⟩
  exact ⟨hf R hSS' hfRS', hg R hSS' hgRS'⟩

theorem ScopeMonotone.sup (f g : GQ α)
    (hf : ScopeMonotone f) (hg : ScopeMonotone g) :
    ScopeMonotone ((f ⊔ g)) := by
  intro R S S' hSS' h
  rcases h with hfRS | hgRS
  · exact Or.inl (hf R hSS' hfRS)
  · exact Or.inr (hg R hSS' hgRS)

theorem Existential.conservative {q : GQ α} (h : Existential q) : Conservative q :=
  fun R T => by
    rw [h R T, h R (fun x => R x ∧ T x)]
    simp only [and_self_left]

theorem Existential.adjRestrict {q : GQ α} (h : Existential q) (adj : α → Prop) :
    Existential (adjRestrict q adj) := fun R T => by
  simp only [GQ.adjRestrict]
  rw [h (fun x => R x ∧ adj x) T]
  exact Iff.of_eq (congrArg (fun A => q A fun _ => True)
    (funext fun x => propext (by tauto)))

theorem Conservative.adjRestrict (q : GQ α) (adj : α → Prop)
    (h : Conservative q) : Conservative (adjRestrict q adj) := by
  intro R S
  simp only [GQ.adjRestrict]
  rw [h (fun x => R x ∧ adj x) S, h (fun x => R x ∧ adj x) (fun x => R x ∧ S x)]
  have heq : (fun x => (R x ∧ adj x) ∧ R x ∧ S x) = (fun x => (R x ∧ adj x) ∧ S x) := by
    funext x; apply propext
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, h1.1, h2⟩⟩
  rw [heq]

theorem ScopeMonotone.adjRestrict (q : GQ α) (adj : α → Prop)
    (h : ScopeMonotone q) : ScopeMonotone (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  exact h _ hSS' hAdj

theorem ScopeAntitone.adjRestrict (q : GQ α) (adj : α → Prop)
    (h : ScopeAntitone q) : ScopeAntitone (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  exact h _ hSS' hAdj

/-! ### Type ⟨1⟩ Theorems (P&W Ch.2-3) -/

theorem individual_upward_closed (a : α) (P P' : α → Prop)
    (h : ∀ x, P x → P' x) :
    individual a P → individual a P' := h a

theorem individual_meet_closed (a : α) (P Q : α → Prop) :
    individual a P → individual a Q →
    individual a (fun x => P x ∧ Q x) := fun hP hQ => ⟨hP, hQ⟩

/-! ### [van-benthem-1984] Characterization -/

/-- Under conservativity, inclusion is the only reflexive antisymmetric quantifier
([van-benthem-1984]'s Theorem 3.1.1). -/
theorem vanBenthem_refl_antisym_is_inclusion (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hAnti : Std.Antisymm q) :
    ∀ A B, q A B ↔ (∀ x, A x → B x) := by
  intro A B
  constructor
  · intro hQAB
    have h1 : q A (fun x => A x ∧ B x) := (hCons A B).mp hQAB
    have h2 : q (fun x => A x ∧ B x) A := by
      rw [hCons (fun x => A x ∧ B x) A]
      have hEq : (fun x => (A x ∧ B x) ∧ A x) = (fun x => A x ∧ B x) :=
        funext fun x => propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h.1⟩⟩
      rw [hEq]; exact hRefl _
    have hEq := hAnti.antisymm A (fun x => A x ∧ B x) h1 h2
    intro x hAx
    have hp : A x = (A x ∧ B x) := congr_fun hEq x
    exact ((iff_of_eq hp).mp hAx).2
  · intro hSub
    rw [hCons A B]
    have hEq : (fun x => A x ∧ B x) = A := by
      funext x; apply propext
      exact ⟨fun h => h.1, fun hAx => ⟨hAx, hSub x hAx⟩⟩
    rw [hEq]; exact hRefl A

theorem zwarts_refl_trans_scopeUp (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : IsTrans _ q) : ScopeMonotone q := by
  intro R S S' hSS' hQRS
  have hQSS' : q S S' := by
    rw [hCons S S']
    have : (fun x => S x ∧ S' x) = S :=
      funext fun x => propext ⟨fun h => h.1, fun hS => ⟨hS, hSS' x hS⟩⟩
    rw [this]; exact hRefl S
  exact hTrans.trans R S S' hQRS hQSS'

theorem zwarts_refl_trans_restrictorDown (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : IsTrans _ q) : RestrictorAntitone q := by
  intro S R R' hRR' hQR'S
  have hQRR' : q R R' := by
    rw [hCons R R']
    have : (fun x => R x ∧ R' x) = R :=
      funext fun x => propext ⟨fun h => h.1, fun hR => ⟨hR, hRR' x hR⟩⟩
    rw [this]; exact hRefl R
  exact hTrans.trans R R' S hQRR' hQR'S

theorem quasiReflexive_of_scopeUp (q : GQ α)
    (hCons : Conservative q) (hUp : ScopeMonotone q) : QuasiReflexive q := by
  intro A B hQAB
  have h1 : q A (fun x => A x ∧ B x) := (hCons A B).mp hQAB
  exact hUp A (show (fun x => A x ∧ B x) ≤ A from fun x hx => hx.1) h1

theorem quasiUniversal_of_scopeDown (q : GQ α)
    (hCons : Conservative q) (hDown : ScopeAntitone q) : QuasiUniversal q := by
  intro A B hQAA
  rw [hCons A B]
  exact hDown A (show (fun x => A x ∧ B x) ≤ A from fun x hx => hx.1) hQAA

theorem ScopeMonotone.rightContinuous (q : GQ α)
    (h : ScopeMonotone q) : RightContinuous q := by
  intro A B B₁ _ hB₁B _ hQ1 _
  exact h A hB₁B hQ1

theorem ScopeAntitone.rightContinuous (q : GQ α)
    (h : ScopeAntitone q) : RightContinuous q := by
  intro A B _ B₂ _ hBB₂ _ hQ2
  exact h A hBB₂ hQ2

/-- A conservative irreflexive almost-connected quantifier is scope-antitone
([van-benthem-1984]'s Theorem 4.1.2). -/
theorem irrefl_almostConn_scopeDown (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : ScopeAntitone q := by
  have hRefl : PositiveStrong (qᶜ) := fun R => hIrrefl R
  have hTrans : IsTrans _ (qᶜ) := ⟨fun A B C hNAB hNBC hQAC => (hAC A C B hQAC).elim hNAB hNBC⟩
  have hUp := zwarts_refl_trans_scopeUp (qᶜ)
    (Conservative.compl q hCons) hRefl hTrans
  rw [← compl_compl q]
  exact ScopeMonotone.compl (qᶜ) hUp

/-- A conservative irreflexive almost-connected quantifier is restrictor-monotone
([van-benthem-1984]'s Theorem 4.1.2). -/
theorem irrefl_almostConn_restrictorUp (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : RestrictorMonotone q := by
  have hRefl : PositiveStrong (qᶜ) := fun R => hIrrefl R
  have hTrans : IsTrans _ (qᶜ) := ⟨fun A B C hNAB hNBC hQAC => (hAC A C B hQAC).elim hNAB hNBC⟩
  have hDown := zwarts_refl_trans_restrictorDown (qᶜ)
    (Conservative.compl q hCons) hRefl hTrans
  intro S R R' hRR' hQ
  by_contra h
  exact hDown S hRR' h hQ

/-! ### Asymmetry and circularity

[peters-westerstahl-2006] Ch 6.4 -/

theorem asymmetric_negativeStrong (q : GQ α) (hAsym : Std.Asymm q) :
    NegativeStrong q := fun A hQAA => hAsym.asymm A A hQAA hQAA

theorem asymmetric_antisymmetric (q : GQ α) (hAsym : Std.Asymm q) :
    Std.Antisymm q := ⟨fun A B hAB hBA => absurd hBA (hAsym.asymm A B hAB)⟩

theorem circular_symmetric_quasiRefl (q : GQ α)
    (hSym : Std.Symm q) (hCirc : Circular q) :
    QuasiReflexive q := by
  intro A B hAB
  have hBA : q B A := hSym.symm A B hAB
  exact hCirc A B A hAB hBA

theorem circular_reflexive_symmetric (q : GQ α)
    (hCirc : Circular q) (hPS : PositiveStrong q) :
    Std.Symm q := ⟨fun A B hAB => hCirc A A B (hPS A) hAB⟩

/-- Piecewise involution swapping A\B ↔ B\A, fixing A∩B and the complement.
    Used to witness ISOM in the proof of `isom_asymmetric_eq_diff`. -/
private noncomputable def swapDiff [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}) :
    α → α := fun x =>
  if h : A x ∧ ¬ B x then (e ⟨x, h⟩).val
  else if h : B x ∧ ¬ A x then (e.symm ⟨x, h⟩).val
  else x

private lemma swapDiff_zone_AB [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h : A x ∧ ¬ B x) :
    swapDiff A B e x = (e ⟨x, h⟩).val := by
  simp only [swapDiff, dite_eq_left h]

private lemma swapDiff_zone_BA [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h : B x ∧ ¬ A x) :
    swapDiff A B e x = (e.symm ⟨x, h⟩).val := by
  unfold swapDiff; rw [dite_eq_right (fun hp => h.2 hp.1), dite_eq_left h]

private lemma swapDiff_zone_fix [Fintype α] [DecidableEq α]
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    {e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}}
    {x : α} (h1 : ¬ (A x ∧ ¬ B x))
    (h2 : ¬ (B x ∧ ¬ A x)) :
    swapDiff A B e x = x := by
  simp only [swapDiff, dite_eq_right h1, dite_eq_right h2]

private theorem swapDiff_involutive [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x}) :
    Function.Involutive (swapDiff A B e) := by
  intro x
  by_cases hA : A x <;> by_cases hB : B x
  · have hf := swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA) (e := e) (x := x)
    rw [hf, hf]
  · have hAB : A x ∧ ¬ B x := ⟨hA, hB⟩
    rw [swapDiff_zone_AB hAB]
    have hp := (e ⟨x, hAB⟩).prop
    rw [swapDiff_zone_BA hp]
    have : (⟨(e ⟨x, hAB⟩).val, hp⟩ : {x // B x ∧ ¬ A x}) = e ⟨x, hAB⟩ :=
      Subtype.ext rfl
    rw [this]; exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hAB⟩)
  · have hBA : B x ∧ ¬ A x := ⟨hB, hA⟩
    rw [swapDiff_zone_BA hBA]
    have hp := (e.symm ⟨x, hBA⟩).prop
    rw [swapDiff_zone_AB hp]
    have : (⟨(e.symm ⟨x, hBA⟩).val, hp⟩ : {x // A x ∧ ¬ B x}) =
      e.symm ⟨x, hBA⟩ := Subtype.ext rfl
    rw [this]; exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hBA⟩)
  · have hf := swapDiff_zone_fix (fun h => hA h.1) (fun h => hB h.1) (e := e) (x := x)
    rw [hf, hf]

private theorem swapDiff_swaps_A [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x})
    (x : α) : A (swapDiff A B e x) ↔ B x := by
  by_cases hA : A x <;> by_cases hB : B x
  · rw [swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA)]
    exact ⟨fun _ => hB, fun _ => hA⟩
  · rw [swapDiff_zone_AB ⟨hA, hB⟩]
    have hp := (e ⟨x, ⟨hA, hB⟩⟩).prop
    exact ⟨fun hAv => absurd hAv hp.2, fun hBx => absurd hBx hB⟩
  · rw [swapDiff_zone_BA ⟨hB, hA⟩]
    exact ⟨fun _ => hB, fun _ => (e.symm ⟨x, ⟨hB, hA⟩⟩).prop.1⟩
  · rw [swapDiff_zone_fix (fun h => hA h.1) (fun h => hB h.1)]
    exact ⟨fun hAv => absurd hAv hA, fun hBx => absurd hBx hB⟩

private theorem swapDiff_preserves_AB [Fintype α] [DecidableEq α]
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (e : {x // A x ∧ ¬ B x} ≃ {x // B x ∧ ¬ A x})
    (x : α) :
    (A (swapDiff A B e x) ∧ B (swapDiff A B e x)) ↔ (A x ∧ B x) := by
  rw [iff_iff_eq.mp (swapDiff_swaps_A A B e x)]
  -- Now goal: B x ∧ B (swapDiff A B e x) ↔ A x ∧ B x
  -- Equivalent claim using extensional case-analysis
  by_cases hA : A x <;> by_cases hB : B x
  · rw [swapDiff_zone_fix (fun h => h.2 hB) (fun h => h.2 hA)]
    exact ⟨fun ⟨_, h⟩ => ⟨hA, h⟩, fun ⟨_, h⟩ => ⟨hB, h⟩⟩
  · -- A x, ¬ B x: rhs A x ∧ B x is False; lhs B x is False
    exact ⟨fun ⟨hBx, _⟩ => absurd hBx hB, fun ⟨_, hBx⟩ => absurd hBx hB⟩
  · -- ¬ A x, B x: rhs A x ∧ B x is False; lhs B (swapDiff …) is False since e.symm lands in A∧¬B
    rw [swapDiff_zone_BA ⟨hB, hA⟩]
    exact ⟨fun ⟨_, hBv⟩ => absurd hBv (e.symm ⟨x, ⟨hB, hA⟩⟩).prop.2,
           fun ⟨hAx, _⟩ => absurd hAx hA⟩
  · exact ⟨fun ⟨hBx, _⟩ => absurd hBx hB, fun ⟨hAx, _⟩ => absurd hAx hA⟩

theorem isom_asymmetric_eq_diff [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hIsom : QuantityInvariant q)
    (hAsym : Std.Asymm q)
    {A B : α → Prop} [DecidablePred A] [DecidablePred B]
    (hCard : Fintype.card {x // A x ∧ ¬ B x} =
             Fintype.card {x // B x ∧ ¬ A x}) :
    ¬ q A B := by
  intro hQAB
  have hAB_eq_BA : q A B ↔ q B A := by
    rw [hCons A B, hCons B A]
    have hComm : (fun x => B x ∧ A x) = (fun x => A x ∧ B x) :=
      funext fun x => propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    rw [hComm]
    let e := Fintype.equivOfCardEq hCard
    let f := swapDiff A B e
    exact hIsom A (fun x => A x ∧ B x) B (fun x => A x ∧ B x) f
      (swapDiff_involutive A B e).bijective
      (swapDiff_swaps_A A B e)
      (swapDiff_preserves_AB A B e)
  exact hAsym.asymm A B hQAB (hAB_eq_BA.mp hQAB)

/-! ### "Aristotle reversed": square from inferential conditions

[van-benthem-1984] §3.3 -/

/-- Under conservativity the only symmetric quasi-reflexive quantifier is overlap, that is
*some* ([van-benthem-1984]'s Theorem 3.3.2). -/
theorem vanBenthem_symm_quasiRefl_is_overlap [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : Std.Symm q)
    (hQR : QuasiReflexive q)
    (hWitT : ∃ x, q (fun y => y = x) (fun y => y = x))
    (hWitF : ∃ A, ¬ q A A)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B ↔ (∃ x, A x ∧ B x) := by
  classical
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    exact hInt A B (fun x => A x ∧ B x) (fun x => A x ∧ B x)
      (fun _ => ⟨fun h => ⟨h, h⟩, And.left⟩)
  have upward : ∀ C D : α → Prop,
      (∀ x, C x → D x) → q C C → q D D := by
    intro C D hCD hCC
    have hDC : q D C ↔ q C C := by
      apply hInt; intro x
      exact ⟨fun ⟨hD, hC⟩ => ⟨hC, hC⟩, fun ⟨hC, _⟩ => ⟨hCD x hC, hC⟩⟩
    exact hQR D C (hDC.mpr hCC)
  obtain ⟨A₀, hA₀⟩ := hWitF
  have empty_false : ¬ q (fun _ => False) (fun _ => False) := by
    intro h
    exact hA₀ (upward (fun _ => False) A₀ (fun _ hF => hF.elim) h)
  intro A B
  constructor
  · intro hAB
    rw [qAB_eq] at hAB
    by_contra h
    have hAll : ∀ x, ¬ (A x ∧ B x) := fun x ⟨hAx, hBx⟩ => h ⟨x, hAx, hBx⟩
    have : (fun x => A x ∧ B x) = (fun _ => False) := by
      funext x; apply propext
      exact ⟨fun hAB => (hAll x hAB).elim, fun hF => hF.elim⟩
    rw [this] at hAB
    exact empty_false hAB
  · rintro ⟨a, hAa, hBa⟩
    rw [qAB_eq]
    obtain ⟨x, hx⟩ := hWitT
    have h_single : q (fun y => y = a) (fun y => y = a) := by
      let f : α → α := Equiv.swap x a
      have hf_bij : Function.Bijective f := (Equiv.swap x a).bijective
      have hf_prop : ∀ y, (f y = a) ↔ (y = x) := by
        intro y
        constructor
        · intro hy
          have h1 : (Equiv.swap x a).symm a = y :=
            (Equiv.symm_apply_eq (Equiv.swap x a)).mpr hy.symm
          have h2 : (Equiv.swap x a).symm a = x := Equiv.swap_apply_right x a
          rw [h2] at h1; exact h1.symm
        · intro hy
          rw [hy]; exact Equiv.swap_apply_left x a
      have h_eq : q (fun y => y = a) (fun y => y = a) ↔
          q (fun y => y = x) (fun y => y = x) :=
        hIso (fun y => y = a) (fun y => y = a) (fun y => y = x) (fun y => y = x) f hf_bij
          hf_prop hf_prop
      exact h_eq.mpr hx
    apply upward (fun y => y = a) (fun y => A y ∧ B y)
    · intro y hy; subst hy; exact ⟨hAa, hBa⟩
    · exact h_single

/-- Under conservativity the only symmetric quasi-universal quantifier is disjointness, that is
*no* ([van-benthem-1984]'s Corollary 3.3.3). -/
theorem vanBenthem_symm_quasiUniv_is_disjointness [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : Std.Symm q)
    (hQU : QuasiUniversal q)
    (hWitF : ∃ x, ¬ q (fun y => y = x) (fun y => y = x))
    (hWitT : ∃ A, q A A)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B ↔ (∀ x, ¬ (A x ∧ B x)) := by
  classical
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B ↔ q (fun x => A x ∧ B x) (fun x => A x ∧ B x) := by
    intro A B
    exact hInt A B _ _ (fun _ => ⟨fun h => ⟨h, h⟩, And.left⟩)
  have downward : ∀ C D : α → Prop,
      (∀ x, C x → D x) → q D D → q C C := by
    intro C D hCD hDD
    have h1 : q D C := hQU D C hDD
    have h2 : q C D := hSym.symm D C h1
    have h3 : q C D ↔ q C C := by
      rw [hCons C D]
      have : (fun x => C x ∧ D x) = C :=
        funext fun x => propext ⟨fun h => h.1, fun hC => ⟨hC, hCD x hC⟩⟩
      rw [this]
    exact h3.mp h2
  obtain ⟨A₀, hA₀⟩ := hWitT
  have empty_true : q (fun _ => False) (fun _ => False) :=
    downward (fun _ => False) A₀ (fun _ hF => hF.elim) hA₀
  intro A B
  constructor
  · intro hAB x ⟨hAx, hBx⟩
    rw [qAB_eq] at hAB
    obtain ⟨x₀, hx₀⟩ := hWitF
    have h_single_true : q (fun y => y = x) (fun y => y = x) :=
      downward (fun y => y = x) (fun y => A y ∧ B y)
        (fun y hy => by subst hy; exact ⟨hAx, hBx⟩) hAB
    have h_single_false : ¬ q (fun y => y = x) (fun y => y = x) := by
      let f : α → α := Equiv.swap x₀ x
      have hf_bij : Function.Bijective f := (Equiv.swap x₀ x).bijective
      have hf_prop : ∀ y, (f y = x) ↔ (y = x₀) := by
        intro y
        constructor
        · intro hy
          have h1 : (Equiv.swap x₀ x).symm x = y :=
            (Equiv.symm_apply_eq (Equiv.swap x₀ x)).mpr hy.symm
          have h2 : (Equiv.swap x₀ x).symm x = x₀ := Equiv.swap_apply_right x₀ x
          rw [h2] at h1; exact h1.symm
        · intro hy
          rw [hy]; exact Equiv.swap_apply_left x₀ x
      have h_eq : q (fun y => y = x) (fun y => y = x) ↔
          q (fun y => y = x₀) (fun y => y = x₀) :=
        hIso (fun y => y = x) (fun y => y = x) (fun y => y = x₀) (fun y => y = x₀) f hf_bij
          hf_prop hf_prop
      exact (fun h => hx₀ (h_eq.mp h))
    exact h_single_false h_single_true
  · intro hDisj
    rw [qAB_eq]
    have hEmpty : (fun x => A x ∧ B x) = (fun _ => False) :=
      funext fun x => propext
        ⟨fun ⟨hAx, hBx⟩ => hDisj x ⟨hAx, hBx⟩, fun hF => hF.elim⟩
    rw [hEmpty]
    exact empty_true

end Quantifier.GQ
