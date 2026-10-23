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
`Valuation` records the values each feature has received, `Valuation.agree` merges an inherent
and a natural valuation, and `Valuation.category` reads off the agreement category: inverse iff
some feature is valued both ways, otherwise the number the values spell.

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

/-- The valuation a natural number contributes, [harbour-2014]'s decomposition. -/
def ofNumber : Number → Valuation
  | .singular => ⟨{true}, {true}⟩
  | .dual => ⟨{false}, {true}⟩
  | .plural => ⟨{false}, {false}⟩
  | _ => ∅

/-- D agrees with both the inherent and the natural number, receiving every value of each
feature even when they clash. -/
def agree (inherent natural : Valuation) : Valuation :=
  ⟨inherent.atomic ∪ natural.atomic, inherent.minimal ∪ natural.minimal⟩

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
