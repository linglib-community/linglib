module

public import Mathlib.ModelTheory.Complexity

/-!
# Quantifier rank of first-order formulas

`[UPSTREAM]` candidate. mathlib's `ModelTheory` has formula *complexity classes*
(`IsQF`, `IsPrenex`, `IsUniversal`) but no quantifier-*rank* function. `quantifierRank φ` is the
maximal nesting depth of quantifiers in `φ` ([libkin-2004] Definition 3.8; [hodges-1993]
§3.3), the measure indexing Ehrenfeucht–Fraïssé games and `≡ₙ` n-equivalence. It is bounded by
the number of quantifiers, and the gap can be exponential.

mathlib has the `∞`-rank apparatus (`ElementarilyEquivalent`, the unbounded
back-and-forth `IsExtensionPair`); `quantifierRank` is the bottom of the missing finite-rank
layer.

## Main definitions

* `FirstOrder.Language.BoundedFormula.quantifierRank`: quantifier rank (max quantifier nesting).

## References

* [libkin-2004]
* [hodges-1993]
-/

@[expose] public section

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α : Type*} {n : ℕ}

/-- The quantifier rank of a formula is the maximal nesting depth of its quantifiers. Atomic
formulas have rank `0`, an implication has the larger rank of its two sides, and `all` adds one. -/
def quantifierRank : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (quantifierRank f₁) (quantifierRank f₂)
  | _, .all f => quantifierRank f + 1

variable (φ ψ : L.BoundedFormula α n)

@[simp] theorem quantifierRank_falsum : (falsum : L.BoundedFormula α n).quantifierRank = 0 := rfl

@[simp] theorem quantifierRank_bot : (⊥ : L.BoundedFormula α n).quantifierRank = 0 := rfl

@[simp] theorem quantifierRank_equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (equal t₁ t₂ : L.BoundedFormula α n).quantifierRank = 0 := rfl

@[simp] theorem quantifierRank_rel {l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ (Fin n))) : (rel R ts).quantifierRank = 0 := rfl

@[simp] theorem quantifierRank_imp :
    (φ.imp ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := rfl

@[simp] theorem quantifierRank_all (φ : L.BoundedFormula α (n + 1)) :
    φ.all.quantifierRank = φ.quantifierRank + 1 := rfl

@[simp] theorem quantifierRank_not : φ.not.quantifierRank = φ.quantifierRank := by
  simp [BoundedFormula.not]

@[simp] theorem quantifierRank_top : (⊤ : L.BoundedFormula α n).quantifierRank = 0 := by
  simp [Top.top]

@[simp] theorem quantifierRank_inf :
    (φ ⊓ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change ((φ.imp ψ.not).not).quantifierRank = _; simp

@[simp] theorem quantifierRank_sup :
    (φ ⊔ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  change (φ.not.imp ψ).quantifierRank = _; simp

@[simp] theorem quantifierRank_iff :
    (φ.iff ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  simp only [BoundedFormula.iff, quantifierRank_inf, quantifierRank_imp,
    max_comm ψ.quantifierRank φ.quantifierRank, max_self]

@[simp] theorem quantifierRank_ex (φ : L.BoundedFormula α (n + 1)) :
    φ.ex.quantifierRank = φ.quantifierRank + 1 := by
  simp [BoundedFormula.ex]

@[simp] theorem quantifierRank_relabelEquiv {β : Type*} (g : α ≃ β) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), (relabelEquiv g φ).quantifierRank = φ.quantifierRank
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp f₁ f₂ => by
      have : relabelEquiv g (f₁.imp f₂) = (relabelEquiv g f₁).imp (relabelEquiv g f₂) := rfl
      rw [this, quantifierRank_imp, quantifierRank_imp, quantifierRank_relabelEquiv g f₁,
        quantifierRank_relabelEquiv g f₂]
  | _, .all f => by
      have : relabelEquiv g f.all = (relabelEquiv g f).all := rfl
      rw [this, quantifierRank_all, quantifierRank_all, quantifierRank_relabelEquiv g f]

variable {φ} {k : ℕ}

private theorem quantifierRank_foldr_le
    {f : L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n}
    {e : L.BoundedFormula α n}
    (hf : ∀ φ ψ, (f φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank)
    (he : e.quantifierRank = 0) : ∀ {l : List (L.BoundedFormula α n)},
      (∀ φ ∈ l, φ.quantifierRank ≤ k) → (l.foldr f e).quantifierRank ≤ k
  | [], _ => he ▸ k.zero_le
  | φ :: l, h => by
      rw [List.foldr_cons, hf, max_le_iff]
      exact ⟨h φ List.mem_cons_self, quantifierRank_foldr_le hf he fun ψ hψ ↦ h ψ (.tail _ hψ)⟩

theorem quantifierRank_iInf_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n}
    (h : ∀ b, (f b).quantifierRank ≤ k) : (iInf f).quantifierRank ≤ k :=
  quantifierRank_foldr_le quantifierRank_inf quantifierRank_top fun φ hφ ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ; exact h b

theorem quantifierRank_iSup_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n}
    (h : ∀ b, (f b).quantifierRank ≤ k) : (iSup f).quantifierRank ≤ k :=
  quantifierRank_foldr_le quantifierRank_sup quantifierRank_bot fun φ hφ ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ; exact h b

theorem IsAtomic.quantifierRank_eq_zero (h : φ.IsAtomic) : φ.quantifierRank = 0 := by
  cases h <;> rfl

theorem IsQF.quantifierRank_eq_zero (h : φ.IsQF) : φ.quantifierRank = 0 := by
  induction h with
  | falsum => rfl
  | of_isAtomic h => exact h.quantifierRank_eq_zero
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]

end FirstOrder.Language.BoundedFormula
