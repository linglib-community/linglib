module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Degree.Marginality
public import Studies.DinisJacinto2025
public import Mathlib.Order.Lattice.Nat

/-!
# Dinis and Jacinto (2026): Marginality Scales for Gradable Adjectives

Dinis and Jacinto give the degrees of a vague gradable adjective the structure of their theory
of marginal and large differences, ML theory, simplified to a linear order with one primitive,
*marginally smaller than*. A degree is largely smaller than another when it is smaller but not
marginally so. As in Kennedy's semantics, an adjective measures objects at circumstances of
evaluation by degrees, and the comparative compares degrees; as in Fara's, the positive form
holds of an object whose degree is largely greater than the standard of comparison. The positive
form then cannot tell apart degrees that differ at most marginally, so its extension is clustered
and tolerant, a Soritical sequence must contain a large step, and an object that leaves the
extension must have become smaller on the scale.

## Main statements

* `marginalScaleEquiv`: along a linear order, the five axioms with largely smaller than defined
  are the eleven of the 2025 paper.
* `comparative_of_positive_of_not_positive`: an object that leaves the positive form's extension
  has become smaller on the scale, which the two-scale alternative does not predict.
* `clustered_positive`: at most marginally different degrees are alike for the positive form,
  so its extension is clustered and tolerant.
* `exists_large_step_of_soritical`: a Soritical sequence for the positive form crosses into the
  extension at a large step.

## Implementation notes

* ML scales are `Degree.MarginalScale`, whose five axioms are those of Figure 1 with largely
  smaller than unfolded.
* A measure function takes a circumstance of evaluation and an object to a degree. The context
  enters only through the standard of comparison and the scale, which are held fixed.
* The text calls marginal difference transitive and large difference possibly intransitive
  (p. 106). Marginally smaller than and at most marginal difference are transitive, while
  marginal difference, being symmetric and irreflexive, is not, and large difference never is.

## References

* [dinis-jacinto-2026]
* [dinis-jacinto-2025]
* [fara-2000]
* [kennedy-1999]
* [kennedy-2007]
-/

@[expose] public section

namespace DinisJacinto2026

open Degree MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α}

/-! ### Marginal and large difference -/

theorem not_isTrans_symmGen_marginallyLT (ml : MarginalScale α) :
    ¬ IsTrans α (Relation.SymmGen ml.MarginallyLT) := fun ⟨htr⟩ ↦ by
  obtain ⟨x, y, h⟩ := ml.exists_large
  obtain ⟨z, hxz, -⟩ := (ml.decomposition h).1
  exact (htr x z x (.inl hxz) (.inr hxz)).elim (fun h ↦ h.lt.false) fun h ↦ h.lt.false

/-- Large difference is never transitive, strengthening the counterexample of fn. 9. By
Decomposition, a degree marginally above `x` and largely below `y` differs largely from `y`, as
`x` does, but not from `x`. -/
theorem not_isTrans_symmGen_largelyLT (ml : MarginalScale α) :
    ¬ IsTrans α (Relation.SymmGen ml.LargelyLT) := fun ⟨htr⟩ ↦ by
  obtain ⟨x, y, h⟩ := ml.exists_large
  obtain ⟨z, hxz, hzy⟩ := (ml.decomposition h).1
  exact (htr x y z (.inl h) (.inr hzy)).elim hxz.not_largelyLT fun h' ↦ h'.lt.asymm hxz.lt

/-- ML theory has no model on the naturals or the reals (fn. 7). -/
example : IsEmpty (MarginalScale ℕ) := inferInstance

/-! ### The simplified theory -/

/-- An ML scale satisfies the eleven axioms of [dinis-jacinto-2025], Theorem 2.2 among them. -/
theorem isMLModel (ml : MarginalScale α) :
    DinisJacinto2025.IsMLModel (· < ·) ml.MarginallyLT ml.LargelyLT where
  isStrictWeakOrder := isStrictWeakOrder_of_isOrderConnected
  exists_l := ml.exists_large
  r_of_m _ _ := MarginallyLT.lt
  r_of_l _ _ := LargelyLT.lt
  m_trans _ _ _ := MarginallyLT.trans
  not_l_of_m _ _ := MarginallyLT.not_largelyLT
  irrelevance _ _ z h := ml.irrelevance z h
  l_of_r_of_l _ _ _ := LargelyLT.of_lt_of_largelyLT
  l_of_l_of_r _ _ _ := LargelyLT.trans_lt
  m_or_l_of_r _ _ := marginallyLT_or_largelyLT_of_lt
  decomposition _ _ h := ml.decomposition h
  m_bounded _ _ _ := MarginallyLT.bounded

/-- Along a linear order, the five axioms are the eleven of [dinis-jacinto-2025], with largely
smaller than defined as smaller than but not marginally smaller than (§2). -/
def marginalScaleEquiv : MarginalScale α ≃
    {p : (α → α → Prop) × (α → α → Prop) // DinisJacinto2025.IsMLModel (· < ·) p.1 p.2} where
  toFun ml := ⟨(ml.MarginallyLT, ml.LargelyLT), isMLModel ml⟩
  invFun p :=
    { MarginallyLT := p.1.1
      exists_large := let ⟨x, y, h⟩ := p.2.exists_l; ⟨x, y, p.2.l_iff.1 h⟩
      lt_of_marginallyLT := p.2.r_of_m
      irrelevance _ _ z h := by simpa only [← p.2.l_iff] using p.2.irrelevance z h
      extends_lt _ _ _ h := by
        simp only [← p.2.l_iff]
        exact ⟨p.2.l_of_r_of_l h, (p.2.l_of_l_of_r · h)⟩
      decomposition _ _ h := by simpa only [← p.2.l_iff] using p.2.decomposition (p.2.l_iff.2 h) }
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl (funext₂ fun _ _ ↦ propext p.2.l_iff.symm))

/-! ### The marginality scales account -/

section Account

variable {C O : Type*} (ml) (μ : C → O → α)

/-- The comparative holds when the object `x` at circumstance `u` is greater on the scale
than the object `y` at circumstance `v`. -/
def Comparative (u : C) (x : O) (v : C) (y : O) : Prop := μ v y < μ u x

/-- The positive form, after Fara, holds when the standard of comparison is largely smaller
than the object's degree at the circumstance. -/
def Positive (norm : α) (w : C) (x : O) : Prop := ml.LargelyLT norm (μ w x)

variable {ml μ} {norm : α} {w u v : C} {a b : O}

theorem setOf_positive_subset_gt_over :
    {x | Positive ml μ norm w x} ⊆ (μ w) ⁻¹' Set.Ioi norm :=
  fun _ h ↦ h.lt

/-- An object whose degree exceeds the standard only marginally is not in the positive form's
extension (Figure 5). -/
theorem not_positive_of_marginallyLT (h : ml.MarginallyLT norm (μ w a)) :
    ¬ Positive ml μ norm w a :=
  h.not_largelyLT

/-- An object in the positive form's extension at one circumstance and out of it at another is
greater on the scale at the first, the case of Charles III (§5.4). -/
theorem comparative_of_positive_of_not_positive (h₁ : Positive ml μ norm u a)
    (h₂ : ¬ Positive ml μ norm v a) : Comparative μ u a v a :=
  lt_of_not_ge fun h ↦ h₂ (isUpperSet_setOf_largelyLT norm h h₁)

/-- Objects whose degrees differ at most marginally are both in the positive form's extension
or both out of it, Fara's similarity constraint (§6.1). -/
theorem positive_iff_of_atMostMarginal (h : ml.AtMostMarginal (μ w a) (μ w b)) :
    Positive ml μ norm w a ↔ Positive ml μ norm w b :=
  h.largelyLT_congr_right

/-- However many marginal steps separate two objects' degrees, the objects are alike for the
positive form (§6.1). -/
theorem positive_iff_of_reflTransGen (h : Relation.ReflTransGen ml.MarginallyLT (μ w a) (μ w b)) :
    Positive ml μ norm w a ↔ Positive ml μ norm w b := by
  rw [Relation.reflTransGen_eq_reflGen] at h
  exact positive_iff_of_atMostMarginal (h.mono fun _ _ ↦ .inl)

/-- In a Soritical sequence for the positive form, a chain of steps each raising the degree
from someone out of the extension to someone in it, some step is large, the nonstandard
primitivist solution to the Sorites (§3, §6.1). -/
theorem exists_large_step_of_soritical {R : O → O → Prop} (hR : ∀ ⦃x y⦄, R x y → μ w x < μ w y)
    (h : Relation.ReflTransGen R a b) (h₁ : ¬ Positive ml μ norm w a)
    (h₂ : Positive ml μ norm w b) :
    ∃ x y, R x y ∧ ¬ Positive ml μ norm w x ∧ Positive ml μ norm w y ∧
      ml.LargelyLT (μ w x) (μ w y) := by
  obtain ⟨x, y, hxy, hx, hy, -⟩ :=
    h.exists_boundary (S := {x | ¬ Positive ml μ norm w x}) h₁ (not_not.2 h₂)
  refine ⟨x, y, hxy, hx, not_not.1 hy,
    (marginallyLT_or_largelyLT_of_lt (hR hxy)).resolve_left fun hm ↦ hx ?_⟩
  exact (positive_iff_of_atMostMarginal (.single (.inl hm))).2 (not_not.1 hy)

variable (ml) in
/-- A property is clustered when something has it iff its degree differs at most marginally
from the degree of something that has it (§3). -/
def Clustered (B : O → Prop) (δ : O → α) : Prop :=
  ∀ x, B x ↔ ∃ y, B y ∧ ml.AtMostMarginal (δ y) (δ x)

/-- Clustered degrees imply degree tolerance. An object whose degree is marginally greater than
that of an object without the property lacks it, and an object whose degree is marginally
smaller than that of an object with the property has it (§3). The ML axioms are not needed. -/
theorem Clustered.tolerance {B : O → Prop} {δ : O → α} (h : Clustered ml B δ) :
    (¬ B a → ml.MarginallyLT (δ a) (δ b) → ¬ B b) ∧ (B a → ml.MarginallyLT (δ b) (δ a) → B b) :=
  ⟨fun ha hm hb ↦ ha ((h a).2 ⟨b, hb, .single (.inr hm)⟩),
    fun ha hm ↦ (h b).2 ⟨a, ha, .single (.inr hm)⟩⟩

/-- The positive form's extension is clustered, so the marginality scales account implies the
nonstandard primitivist principle of §3. -/
theorem clustered_positive : Clustered ml (Positive ml μ norm w) (μ w) := fun _ ↦
  ⟨fun h ↦ ⟨_, h, .refl _⟩, fun ⟨_, hy, hxy⟩ ↦ (positive_iff_of_atMostMarginal hxy).1 hy⟩

theorem setOf_positive_eq_gt_over {f : α → ℚ ×ₗ ℤ} (hf : ml.IsHom (lex ℚ ℤ) f) :
    {x | Positive ml μ norm w x} =
      (fun x ↦ (ofLex (f (μ w x))).1) ⁻¹' Set.Ioi (ofLex (f norm)).1 :=
  Set.ext fun _ ↦ hf.largelyLT_iff.symm.trans lex_largelyLT_iff

/-- Every countable, finitely marginal scale has a representation under which the positive form,
for every measure function, standard and circumstance, compares blocks, so reasoning about it can
be carried out in the representative model (§5.2). -/
theorem exists_isHom_setOf_positive_eq [Countable α] (hf : DinisJacinto2025.FinitelyMarginal ml) :
    ∃ f : α → ℚ ×ₗ ℤ, ml.IsHom (lex ℚ ℤ) f ∧ ∀ (μ : C → O → α) (norm : α) (w : C),
      {x | Positive ml μ norm w x} =
        (fun x ↦ (ofLex (f (μ w x))).1) ⁻¹' Set.Ioi (ofLex (f norm)).1 :=
  let ⟨f, hf⟩ := DinisJacinto2025.exists_isHom_lex_rat_int hf
  ⟨f, hf, fun _ _ _ ↦ setOf_positive_eq_gt_over hf⟩

/-- If a representation places the standard and Ronaldo in block `0` and Zidane in block `1`,
then Zidane is balder than Ronaldo, and Zidane is bald where Ronaldo, though balder than the
standard, is not (§5.2). -/
theorem zidane_ronaldo {f : α → ℚ ×ₗ ℤ} (hf : ml.IsHom (lex ℚ ℤ) f) {zidane ronaldo : O}
    (hz : (ofLex (f (μ w zidane))).1 = 1) (hr : (ofLex (f (μ w ronaldo))).1 = 0)
    (hn : (ofLex (f norm)).1 = 0) :
    Comparative μ w zidane w ronaldo ∧ Positive ml μ norm w zidane ∧
      ¬ Positive ml μ norm w ronaldo :=
  ⟨(hf.largelyLT_iff.1 (lex_largelyLT_iff.2 (by rw [hz, hr]; exact zero_lt_one))).lt,
    hf.largelyLT_iff.1 (lex_largelyLT_iff.2 (by rw [hz, hn]; exact zero_lt_one)),
    fun h ↦ (lex_largelyLT_iff.1 (hf.largelyLT_iff.2 h)).ne (hn.trans hr.symm)⟩

end Account

/-- The two-scale alternative of §5.4 reads the comparative off precise degrees `ρ` and the
positive form off vague degrees `τ w` of precise degrees. When the agent's interests change, it
lets an object leave the positive form's extension without having been greater on the precise
scale. -/
theorem exists_twoScale_not_comparative : ∃ (ρ : Bool → Unit → ℕ) (τ : Bool → ℕ → ℚ ×ₗ ℤ),
    Positive (lex ℚ ℤ) (fun w x ↦ τ w (ρ w x)) (toLex (0, 0)) true () ∧
      ¬ Positive (lex ℚ ℤ) (fun w x ↦ τ w (ρ w x)) (toLex (0, 0)) false () ∧
      ¬ Comparative ρ true () false () :=
  ⟨fun _ _ ↦ 0, fun w _ ↦ toLex (if w then 1 else 0, 0), lex_largelyLT_iff.2 zero_lt_one,
    fun h ↦ lt_irrefl (0 : ℚ) (lex_largelyLT_iff.1 h), lt_irrefl 0⟩

end DinisJacinto2026
