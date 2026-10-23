module

public import Linglib.Semantics.Quantification.Properties
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# The conservative determiners as a Boolean algebra

Keenan and Stavi show that conservative generalized quantifiers are closed under the pointwise
Boolean operations, so they form a Boolean subalgebra `conservativeSubalgebra` of `GQ α`, whose
elements `ConsGQ α` carry mathlib's Boolean algebra structure. They are moreover closed under
arbitrary pointwise meets and joins, so the algebra is complete, and it is atomic because `GQ α`
is a power of `Prop`: `ConsGQ α` is a `CompleteAtomicBooleanAlgebra`, the structure Keenan and
Stavi's Appendix establishes on the way to the Conservativity Theorem. The atoms themselves and
the counting consequences are in `Studies/KeenanStavi1986.lean`. Elliott identifies this algebra
with the predicates of polarized groups.

## Implementation notes

The Boolean algebra on `GQ α` is mathlib's Pi instance (`Prop` is a Boolean algebra and
`(α → Prop) → (α → Prop) → Prop` lifts pointwise); closure under `⊔` and `⊓` is
`Conservative.sup` and `Conservative.inf`, and the complement of a conservative quantifier
is conservative because conservativity is an equivalence at every restrictor and scope.
The complete structure extends the `BooleanSubalgebra` coercion instance rather than being
pulled back along `Subtype.val`, so the finitary operations stay the coercion instances and
no second `BooleanAlgebra` path is introduced.

## References

* [keenan-stavi-1986]
* [elliott-2025]
-/

@[expose] public section

namespace Quantifier.GQ

variable {α : Type*}

/-! ### Infinitary closure -/

theorem Conservative.iSup {ι : Sort*} {f : ι → GQ α} (hf : ∀ i, Conservative (f i)) :
    Conservative (⨆ i, f i) := fun R T => by
  simp only [iSup_apply, iSup_Prop_eq]
  exact exists_congr fun i => hf i R T

theorem Conservative.iInf {ι : Sort*} {f : ι → GQ α} (hf : ∀ i, Conservative (f i)) :
    Conservative (⨅ i, f i) := fun R T => by
  simp only [iInf_apply, iInf_Prop_eq]
  exact forall_congr' fun i => hf i R T

/-! ### The Boolean subalgebra -/

/-- The conservative GQs, a Boolean subalgebra of `GQ α`. -/
def conservativeSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {q | Conservative q}
  supClosed' q₁ hq₁ q₂ hq₂ := Conservative.sup q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := Conservative.inf q₁ q₂ hq₁ hq₂
  compl_mem' hq R S := not_congr (hq R S)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_conservativeSubalgebra {q : GQ α} :
    q ∈ conservativeSubalgebra ↔ Conservative q :=
  Iff.rfl

/-- The conservative GQs form the subtype of `GQ α` satisfying conservativity, a Boolean algebra
under the pointwise propositional operations with pointwise implication as the order. -/
abbrev ConsGQ (α : Type*) := conservativeSubalgebra (α := α)

namespace ConsGQ

variable {α : Type*}

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S ∨ q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Prop) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S ∧ q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Prop) : (⊤ : ConsGQ α).1 R S = True := rfl

@[simp] theorem bot_val (R S : α → Prop) : (⊥ : ConsGQ α).1 R S = False := rfl

@[simp] theorem compl_val (q : ConsGQ α) (R S : α → Prop) : qᶜ.1 R S = ¬ q.1 R S := rfl

/-! ### The complete atomic structure

The Appendix of [keenan-stavi-1986] observes that `GQ α` is a complete atomic Boolean algebra
under the pointwise operations and that the conservative functions are a complete subalgebra,
hence themselves a complete atomic Boolean algebra. The instance extends the finitary coercion
instance with pointwise set suprema and infima. -/

noncomputable instance : SupSet (ConsGQ α) :=
  ⟨fun S => ⟨⨆ q ∈ S, q.1, Conservative.iSup fun q => Conservative.iSup fun _ => q.2⟩⟩

noncomputable instance : InfSet (ConsGQ α) :=
  ⟨fun S => ⟨⨅ q ∈ S, q.1, Conservative.iInf fun q => Conservative.iInf fun _ => q.2⟩⟩

@[simp] theorem sSup_val (S : Set (ConsGQ α)) : (sSup S).1 = ⨆ q ∈ S, q.1 := rfl

@[simp] theorem sInf_val (S : Set (ConsGQ α)) : (sInf S).1 = ⨅ q ∈ S, q.1 := rfl

@[simp] theorem iSup_val {ι : Sort*} (f : ι → ConsGQ α) : (⨆ i, f i).1 = ⨆ i, (f i).1 := by
  rw [iSup, sSup_val, iSup_range]

@[simp] theorem iInf_val {ι : Sort*} (f : ι → ConsGQ α) : (⨅ i, f i).1 = ⨅ i, (f i).1 := by
  rw [iInf, sInf_val, iInf_range]

noncomputable instance : CompleteAtomicBooleanAlgebra (ConsGQ α) where
  __ := (inferInstance : BooleanAlgebra (ConsGQ α))
  isLUB_sSup S := ⟨fun q hq => le_iSup₂ (f := fun (q : ConsGQ α) (_ : q ∈ S) => q.1) q hq,
    fun b hb => show (⨆ q ∈ S, (q : ConsGQ α).1) ≤ b.1 from iSup₂_le fun r hr => hb hr⟩
  isGLB_sInf S := ⟨fun q hq => iInf₂_le (f := fun (q : ConsGQ α) (_ : q ∈ S) => q.1) q hq,
    fun b hb => show b.1 ≤ ⨅ q ∈ S, (q : ConsGQ α).1 from le_iInf₂ fun r hr => hb hr⟩
  iInf_iSup_eq f := Subtype.ext (by
    simp only [iInf_val, iSup_val]
    exact iInf_iSup_eq)

end ConsGQ

end Quantifier.GQ
