module

public import Linglib.Semantics.Negation.Polarity
public import Linglib.Core.Order.Flat

/-!
# Implication signatures

A complement-taking operator such as *manage*, *force* or *refuse* implies something about its
complement in a positive context, in a negative context, or in both. Its implication signature
gives the polarity of the complement that each context implies, if any: *manage* is `+/−`, since
*managed to leave* implies *left* and *didn't manage to leave* implies *didn't leave*; *force* is
`+/◦`, *refuse* `−/◦`, *hesitate* `◦/+`, and *want* `◦/◦`. Each slot is a flat value with `◦` as
`⊥`, so signatures are ordered by how much they imply.

## Main definitions

* `ImplicationSignature`: the polarity of the complement implied in a positive and in a negative
  context.

## References

* [nairn-condoravdi-karttunen-2006]
-/

@[expose] public section

namespace NaturalLogic

/-- The implication signature of a complement-taking operator gives the polarity of the complement
it implies in a positive context and in a negative context, `⊥` where it implies nothing. -/
@[ext]
structure ImplicationSignature where
  /-- The complement's implied polarity in a positive context. -/
  positive : Flat Polarity
  /-- The complement's implied polarity in a negative context. -/
  negative : Flat Polarity
  deriving DecidableEq, Repr

namespace ImplicationSignature

variable {s t : ImplicationSignature} {m q : Polarity}

/-- The polarity of the complement implied in a context of polarity `m`. -/
def implied (s : ImplicationSignature) : Polarity → Flat Polarity
  | .positive => s.positive
  | .negative => s.negative

@[simp] theorem implied_positive (s : ImplicationSignature) : s.implied .positive = s.positive :=
  rfl

@[simp] theorem implied_negative (s : ImplicationSignature) : s.implied .negative = s.negative :=
  rfl

theorem implied_injective : Function.Injective implied := fun _ _ h ↦
  ImplicationSignature.ext (congrFun h .positive) (congrFun h .negative)

/-- One signature is below another when every context implies less under it. -/
instance : PartialOrder ImplicationSignature :=
  PartialOrder.lift implied implied_injective

theorem le_iff : s ≤ t ↔ s.positive ≤ t.positive ∧ s.negative ≤ t.negative :=
  ⟨fun h ↦ ⟨h .positive, h .negative⟩, fun h m ↦ by cases m <;> simp [h.1, h.2]⟩

instance : DecidableLE ImplicationSignature := fun _ _ ↦ decidable_of_iff _ le_iff.symm

/-- The signature `◦/◦` implies nothing in either context. -/
instance : OrderBot ImplicationSignature where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := le_iff.2 ⟨bot_le, bot_le⟩

@[simp] theorem bot_positive : (⊥ : ImplicationSignature).positive = ⊥ := rfl

@[simp] theorem bot_negative : (⊥ : ImplicationSignature).negative = ⊥ := rfl

end ImplicationSignature

end NaturalLogic
