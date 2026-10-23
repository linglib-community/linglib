module

public import Mathlib.ModelTheory.Complexity

/-!
# Quantifier rank of first-order formulas

`[UPSTREAM]` candidate. mathlib's `ModelTheory` has formula *complexity classes*
(`IsQF`, `IsPrenex`, `IsUniversal`) but no quantifier-*rank* function. `qr φ` is the
maximal nesting depth of quantifiers in `φ` ([libkin-2004] Definition 3.8; [hodges-1993]
§3.3), the measure indexing Ehrenfeucht–Fraïssé games and `≡ₙ` n-equivalence. It is bounded by
the number of quantifiers, and the gap can be exponential.

mathlib has the `∞`-rank apparatus (`ElementarilyEquivalent`, the unbounded
back-and-forth `IsExtensionPair`); `qr` is the bottom of the missing finite-rank
layer.

## Main definitions

* `FirstOrder.Language.BoundedFormula.qr`: quantifier rank (max quantifier nesting).

## References

* [libkin-2004]
* [hodges-1993]
-/

@[expose] public section

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α : Type*} {n : ℕ}

/-- The quantifier rank of a formula is the maximal nesting depth of its quantifiers. Atomic
formulas have rank `0`, an implication has the larger rank of its two sides, and `all` adds one. -/
def qr : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qr f₁) (qr f₂)
  | _, .all f => qr f + 1

@[simp] theorem qr_falsum : (falsum : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_bot : (⊥ : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (equal t₁ t₂ : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    (rel R ts).qr = 0 := rfl

@[simp] theorem qr_imp (φ ψ : L.BoundedFormula α n) : (φ.imp ψ).qr = max φ.qr ψ.qr := rfl

@[simp] theorem qr_all (φ : L.BoundedFormula α (n + 1)) : φ.all.qr = φ.qr + 1 := rfl

@[simp] theorem qr_not (φ : L.BoundedFormula α n) : φ.not.qr = φ.qr := by
  simp [BoundedFormula.not]

@[simp] theorem qr_top : (⊤ : L.BoundedFormula α n).qr = 0 := by
  simp [Top.top]

@[simp] theorem qr_inf (φ ψ : L.BoundedFormula α n) : (φ ⊓ ψ).qr = max φ.qr ψ.qr := by
  change ((φ.imp ψ.not).not).qr = _; simp

@[simp] theorem qr_sup (φ ψ : L.BoundedFormula α n) : (φ ⊔ ψ).qr = max φ.qr ψ.qr := by
  change (φ.not.imp ψ).qr = _; simp

@[simp] theorem qr_iff (φ ψ : L.BoundedFormula α n) : (φ.iff ψ).qr = max φ.qr ψ.qr := by
  simp only [BoundedFormula.iff, qr_inf, qr_imp, max_comm ψ.qr φ.qr, max_self]

@[simp] theorem qr_ex (φ : L.BoundedFormula α (n + 1)) : φ.ex.qr = φ.qr + 1 := by
  simp [BoundedFormula.ex]

@[simp] theorem qr_relabelEquiv {β : Type*} (g : α ≃ β) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), (relabelEquiv g φ).qr = φ.qr
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp f₁ f₂ => by
      have : relabelEquiv g (f₁.imp f₂) = (relabelEquiv g f₁).imp (relabelEquiv g f₂) := rfl
      rw [this, qr_imp, qr_imp, qr_relabelEquiv g f₁, qr_relabelEquiv g f₂]
  | _, .all f => by
      have : relabelEquiv g f.all = (relabelEquiv g f).all := rfl
      rw [this, qr_all, qr_all, qr_relabelEquiv g f]

private theorem qr_foldr_le {f : L.BoundedFormula α n → L.BoundedFormula α n →
    L.BoundedFormula α n} {e : L.BoundedFormula α n} {k : ℕ}
    (hf : ∀ φ ψ, (f φ ψ).qr = max φ.qr ψ.qr) (he : e.qr = 0) :
    ∀ {l : List (L.BoundedFormula α n)}, (∀ φ ∈ l, φ.qr ≤ k) → (l.foldr f e).qr ≤ k
  | [], _ => he ▸ k.zero_le
  | φ :: l, h => by
      rw [List.foldr_cons, hf, max_le_iff]
      exact ⟨h φ List.mem_cons_self, qr_foldr_le hf he fun ψ hψ => h ψ (.tail _ hψ)⟩

theorem qr_iInf_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n} {k : ℕ}
    (h : ∀ b, (f b).qr ≤ k) : (iInf f).qr ≤ k :=
  qr_foldr_le qr_inf qr_top fun φ hφ => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ; exact h b

theorem qr_iSup_le {β : Type*} [Finite β] {f : β → L.BoundedFormula α n} {k : ℕ}
    (h : ∀ b, (f b).qr ≤ k) : (iSup f).qr ≤ k :=
  qr_foldr_le qr_sup qr_bot fun φ hφ => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ; exact h b

theorem IsAtomic.qr_eq_zero {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : φ.qr = 0 := by
  cases h <;> rfl

theorem IsQF.qr_eq_zero {φ : L.BoundedFormula α n} (h : φ.IsQF) : φ.qr = 0 := by
  induction h with
  | falsum => rfl
  | of_isAtomic h => exact h.qr_eq_zero
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]

end FirstOrder.Language.BoundedFormula
