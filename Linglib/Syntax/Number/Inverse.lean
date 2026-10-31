module

public import Mathlib.Data.Fintype.Basic
public import Linglib.Syntax.Number.Basic

/-!
# Inverse number

Kiowa-Tanoan verbal agreement distinguishes singular, dual, plural and *inverse*. Inverse is
not a number value alongside the others ([corbett-2000], §5.5: inverse systems "are a matter of
morphological arrangement and not of semantic values"); on [harbour-2011]'s analysis it is what
a D head shows when its `[±atomic]` and `[±minimal]` features are valued from two sources, the
noun's inherent number and its natural number, and one feature receives both values. A
`Valuation` records the values each feature has received, so D receives the join `⊔` of an
inherent and a natural valuation, and `Valuation.category` reads off the agreement category:
inverse iff some feature is valued both ways, otherwise the number the values spell.

## References

* [G. G. Corbett, *Number*][corbett-2000]
* [D. Harbour, *Valence and atomic number*][harbour-2011]
* [D. Harbour, *Paucity, abundance, and the theory of number*][harbour-2014]
-/

@[expose] public section

namespace Number.Inverse

/-- The values a D head has received in `[±atomic]` and `[±minimal]`. -/
structure Valuation where
  /-- The values received in `[±atomic]`. -/
  atomic : Finset Bool
  /-- The values received in `[±minimal]`. -/
  minimal : Finset Bool
  deriving DecidableEq

/-- The four categories of Kiowa-Tanoan verbal agreement. -/
inductive Category where
  | singular
  | dual
  | plural
  | inverse
  deriving DecidableEq, Repr, Fintype

namespace Valuation

/-- No values received. -/
instance : EmptyCollection Valuation := ⟨⟨∅, ∅⟩⟩

/-- A valuation as the pair of its value sets. -/
def toProd (v : Valuation) : Finset Bool × Finset Bool := (v.atomic, v.minimal)

theorem toProd_injective : Function.Injective toProd := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
  cases h; rfl

/-- One valuation is below another when each feature has received fewer values. -/
instance : LE Valuation := ⟨fun a b ↦ a.toProd ≤ b.toProd⟩

instance : LT Valuation := ⟨fun a b ↦ a.toProd < b.toProd⟩

instance : DecidableLE Valuation := fun a b ↦
  inferInstanceAs (Decidable (a.atomic ⊆ b.atomic ∧ a.minimal ⊆ b.minimal))

/-- The values received from either of two valuations. -/
instance : Max Valuation := ⟨fun a b ↦ ⟨a.atomic ∪ b.atomic, a.minimal ∪ b.minimal⟩⟩

instance : SemilatticeSup Valuation :=
  toProd_injective.semilatticeSup _ Iff.rfl Iff.rfl fun _ _ ↦ rfl

@[simp] theorem atomic_sup (a b : Valuation) : (a ⊔ b).atomic = a.atomic ∪ b.atomic := rfl
@[simp] theorem minimal_sup (a b : Valuation) : (a ⊔ b).minimal = a.minimal ∪ b.minimal := rfl

/-- The valuation a natural number contributes, [harbour-2014]'s decomposition. -/
def ofNumber : Number → Valuation
  | .singular => ⟨{true}, {true}⟩
  | .dual => ⟨{false}, {true}⟩
  | .plural => ⟨{false}, {false}⟩
  | _ => ∅

/-- Some feature has received both values. -/
def IsInverse (v : Valuation) : Prop := v.atomic = Finset.univ ∨ v.minimal = Finset.univ

instance : DecidablePred IsInverse := fun v ↦
  inferInstanceAs (Decidable (v.atomic = Finset.univ ∨ v.minimal = Finset.univ))

/-- The agreement category a valuation shows: inverse when a feature is valued both ways,
otherwise the number its values spell, if any. -/
def category (v : Valuation) : Option Category :=
  if v.IsInverse then some .inverse
  else if v = ofNumber .singular then some .singular
  else if v = ofNumber .dual then some .dual
  else if v = ofNumber .plural then some .plural
  else none

theorem category_ofNumber_singular : (ofNumber .singular).category = some .singular := by decide

theorem category_ofNumber_dual : (ofNumber .dual).category = some .dual := by decide

theorem category_ofNumber_plural : (ofNumber .plural).category = some .plural := by decide

end Valuation

end Number.Inverse
