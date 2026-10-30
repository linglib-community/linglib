module

public import Linglib.Semantics.Quantification.Properties
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# The conservative determiners as a Boolean algebra

Keenan and Stavi show that conservative generalized quantifiers are closed under the pointwise
Boolean operations, so they form a Boolean subalgebra `conservativeSubalgebra` of `Det α`, whose
elements `ConsDet α` carry mathlib's Boolean algebra structure. They are moreover closed under
arbitrary pointwise meets and joins, so the algebra is complete, and it is atomic because `Det α`
is a power of `Prop`: `ConsDet α` is a `CompleteAtomicBooleanAlgebra`, the structure Keenan and
Stavi's Appendix establishes on the way to the Conservativity Theorem. The atoms themselves and
the counting consequences are in `Studies/KeenanStavi1986.lean`. Elliott identifies this algebra
with the predicates of polarized groups.

## Implementation notes

The Boolean algebra on `Det α` is mathlib's Pi instance (`Prop` is a Boolean algebra and
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

namespace Quantifier.Det

variable {α : Type*}

/-! ### Infinitary closure -/

theorem Conservative.iSup {ι : Sort*} {f : ι → Det α} (hf : ∀ i, Conservative (f i)) :
    Conservative (⨆ i, f i) := fun R T => by
  simp only [iSup_apply, iSup_Prop_eq]
  exact exists_congr fun i => hf i R T

theorem Conservative.iInf {ι : Sort*} {f : ι → Det α} (hf : ∀ i, Conservative (f i)) :
    Conservative (⨅ i, f i) := fun R T => by
  simp only [iInf_apply, iInf_Prop_eq]
  exact forall_congr' fun i => hf i R T

/-! ### The Boolean subalgebra -/

/-- The conservative determiner denotations, a Boolean subalgebra of `Det α`. -/
def conservativeSubalgebra : BooleanSubalgebra (Det α) where
  carrier := {q | Conservative q}
  supClosed' _ hq₁ _ hq₂ := hq₁.sup hq₂
  infClosed' _ hq₁ _ hq₂ := hq₁.inf hq₂
  compl_mem' hq R S := not_congr (hq R S)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_conservativeSubalgebra {q : Det α} :
    q ∈ conservativeSubalgebra ↔ Conservative q :=
  Iff.rfl

/-- The conservative determiner denotations form the subtype of `Det α` satisfying
conservativity, a Boolean algebra under the pointwise propositional operations with pointwise
implication as the order. -/
abbrev ConsDet (α : Type*) := conservativeSubalgebra (α := α)

namespace ConsDet

variable {α : Type*}

@[simp] theorem sup_val (q₁ q₂ : ConsDet α) (A B : Set α) :
    (q₁ ⊔ q₂).1 A B = (q₁.1 A B ∨ q₂.1 A B) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsDet α) (A B : Set α) :
    (q₁ ⊓ q₂).1 A B = (q₁.1 A B ∧ q₂.1 A B) := rfl

@[simp] theorem top_val (A B : Set α) : (⊤ : ConsDet α).1 A B = True := rfl

@[simp] theorem bot_val (A B : Set α) : (⊥ : ConsDet α).1 A B = False := rfl

@[simp] theorem compl_val (q : ConsDet α) (A B : Set α) : qᶜ.1 A B = ¬ q.1 A B := rfl

/-! ### The complete atomic structure

The Appendix of [keenan-stavi-1986] observes that `Det α` is a complete atomic Boolean algebra
under the pointwise operations and that the conservative functions are a complete subalgebra,
hence themselves a complete atomic Boolean algebra. The instance extends the finitary coercion
instance with pointwise set suprema and infima. -/

noncomputable instance : SupSet (ConsDet α) :=
  ⟨fun S => ⟨⨆ q ∈ S, q.1, Conservative.iSup fun q => Conservative.iSup fun _ => q.2⟩⟩

noncomputable instance : InfSet (ConsDet α) :=
  ⟨fun S => ⟨⨅ q ∈ S, q.1, Conservative.iInf fun q => Conservative.iInf fun _ => q.2⟩⟩

@[simp] theorem sSup_val (S : Set (ConsDet α)) : (sSup S).1 = ⨆ q ∈ S, q.1 := rfl

@[simp] theorem sInf_val (S : Set (ConsDet α)) : (sInf S).1 = ⨅ q ∈ S, q.1 := rfl

@[simp] theorem iSup_val {ι : Sort*} (f : ι → ConsDet α) : (⨆ i, f i).1 = ⨆ i, (f i).1 := by
  rw [iSup, sSup_val, iSup_range]

@[simp] theorem iInf_val {ι : Sort*} (f : ι → ConsDet α) : (⨅ i, f i).1 = ⨅ i, (f i).1 := by
  rw [iInf, sInf_val, iInf_range]

noncomputable instance : CompleteAtomicBooleanAlgebra (ConsDet α) where
  __ := (inferInstance : BooleanAlgebra (ConsDet α))
  isLUB_sSup S := ⟨fun q hq => le_iSup₂ (f := fun (q : ConsDet α) (_ : q ∈ S) => q.1) q hq,
    fun b hb => show (⨆ q ∈ S, (q : ConsDet α).1) ≤ b.1 from iSup₂_le fun r hr => hb hr⟩
  isGLB_sInf S := ⟨fun q hq => iInf₂_le (f := fun (q : ConsDet α) (_ : q ∈ S) => q.1) q hq,
    fun b hb => show b.1 ≤ ⨅ q ∈ S, (q : ConsDet α).1 from le_iInf₂ fun r hr => hb hr⟩
  iInf_iSup_eq f := Subtype.ext (by
    simp only [iInf_val, iSup_val]
    exact iInf_iSup_eq)

end ConsDet

end Quantifier.Det
