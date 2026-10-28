module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical number

`Number` is Corbett's inventory of number values, the vocabulary in which number systems,
agreement, resolution and the semantics of number are stated. A value is determinate when its
cardinality boundary is fixed, as for the singular, dual and trial, and the general, a form
noncommittal to cardinality, lies outside the number system. The Universal Dependencies tags
that corpora annotate (`Morphology/Word/UD.lean`) lack the general, minimal, augmented and unit
augmented values and add inverse, collective and count categories. The quadral is excluded,
Corbett reanalysing apparent quadrals (Sursurunga, Tangga) as paucals.

A number system is the set of values a language has. The implicational universals that
constrain which sets occur are claims of the papers that state them, proved there of the systems
each theory generates. The substrate keeps what cardinality decides, whether the determinate
values of a system form an initial segment, which number resolution needs.

## Main definitions

* `Number`: the number values.
* `Number.System`: a language's number values, which of them are facultative, and whether it
  has general number.
* `Number.System.DeterminateInitial`: the determinate values are an initial segment.
* `Number.System.value`: a value of a system, as an element of its values.
* `Number.System.elim`: a function on a system of the singular and the plural, by its values at
  the two.

## Implementation notes

Harbour's implicational universals and the order his features induce on the values are in
`Studies/Harbour2014.lean`, the feature decomposition of the singular, dual and plural is in
`Semantics/Plurality/NumberFeatures.lean`, and coordinate resolution in
`Syntax/Number/Resolve.lean`.

## References

* [corbett-2000]
* [harbour-2014]
* [grimm-2018]
-/

@[expose] public section

/-- The grammatical number values are those of [corbett-2000]'s typology. -/
inductive Number where
  /-- The general is noncommittal to cardinality and lies outside the number system (Bayso
      *lúban* 'lion(s)', Japanese *inu* 'dog(s)'). It is a form of a noun that has number,
      unlike a noncountable noun, which lacks the contrast ([grimm-2018],
      `Studies/Grimm2018.lean`). -/
  | general
  /-- The singular denotes exactly one individual, `[+atomic, +minimal]`. -/
  | singular
  /-- The dual denotes exactly two, `[−atomic, +minimal]`. -/
  | dual
  /-- The trial denotes exactly three, recursive `[+minimal]` on the plural region. -/
  | trial
  /-- The paucal denotes a few, with an indeterminate boundary, `[−additive]`. -/
  | paucal
  /-- The plural denotes more than one, the residual value, `[−atomic]` or `[+additive]`. -/
  | plural
  /-- The greater paucal is indeterminate and larger than the paucal, `[−additive +additive]`,
      a second bounded region above the paucal. -/
  | greaterPaucal
  /-- The greater plural denotes abundance, `[+additive]` above a high cut. -/
  | greaterPlural
  /-- The minimal is `[+minimal]` without `[±atomic]`, covering atoms and minimal non-atoms
      alike, unlike the singular. -/
  | minimal
  /-- The augmented is `[−minimal]` without `[±atomic]`, the complement of the minimal. -/
  | augmented
  /-- The unit augmented is recursive `[+minimal]` on the augmented region, the minimal
      non-minimal, unlike the dual. -/
  | unitAugmented
  /-- The global plural denotes every instance in the domain of discourse, the cut of
      `[±additive]` at the top of the lattice, tentative in [harbour-2014]. -/
  | globalPlural
  deriving DecidableEq, Repr, Fintype

namespace Number

/-! ### Classification predicates -/

/-- A number value is determinate when its cardinality boundary is fixed. The minimal and unit
augmented are not, since they depend on the composition of the group. -/
def IsDeterminate : Number → Prop
  | .singular | .dual | .trial => True
  | _ => False

instance : DecidablePred IsDeterminate := fun n => by
  cases n <;> unfold IsDeterminate <;> infer_instance

/-- A determinate value's referent has an exact cardinality, one for the singular, two for the
dual and three for the trial; the other values have none. -/
def exactCard : Number → Option Nat
  | .singular => some 1
  | .dual     => some 2
  | .trial    => some 3
  | _         => none

/-- `fromCard n` is the determinate value of cardinality `n`, and the residual plural from
four on, the greater plural being a value of abundance rather than of four or more. -/
def fromCard : Nat → Number
  | 1 => .singular
  | 2 => .dual
  | 3 => .trial
  | _ => .plural

/-! ### Number systems -/

/-- A number system records the values available in a language, which of them are
facultative, and whether the language has general number ([corbett-2000] §2.3). -/
structure System where
  /-- The values available within the number system. -/
  values : Finset Number
  /-- Whether the language has general number, a form outside the system. -/
  hasGeneral : Bool := false
  /-- The facultative values, whose use is optional. -/
  facultative : Finset Number := ∅
  deriving DecidableEq

namespace System

/-- The system of the singular and the plural alone. -/
def singularPlural : System := { values := {.singular, .plural} }

@[simp] theorem singularPlural_values : singularPlural.values = {.singular, .plural} := rfl

/-- A system's determinate values are an initial segment of the singular, dual and trial when,
with the value of a cardinality, it has the value of every smaller positive one, as the dual
requires the singular and the trial the dual ([harbour-2014] Table 1). -/
def DeterminateInitial (ns : System) : Prop :=
  ∀ v ∈ ns.values, ∀ m ∈ Finset.Icc 1 (v.exactCard.getD 0), fromCard m ∈ ns.values

instance : DecidablePred DeterminateInitial := fun _ ↦ by
  unfold DeterminateInitial; infer_instance

/-- The value `n` of a system that has it. -/
def value (ns : System) (n : Number) (h : n ∈ ns.values := by decide) : ns.values := ⟨n, h⟩

@[simp] theorem coe_value (ns : System) (n : Number) (h : n ∈ ns.values) :
    (ns.value n h : Number) = n :=
  rfl

/-- A function on the values of a system of the singular and the plural, by its value at
each. -/
def elim {β : Sort*} (ns : System) (sg pl : β)
    (_h : ns.values = {.singular, .plural} := by decide) (n : ns.values) : β :=
  if n.1 = .plural then pl else sg

variable {β : Sort*} {ns : System} {sg pl : β} {h : ns.values = {.singular, .plural}}

@[simp] theorem elim_value_singular (hs : .singular ∈ ns.values) :
    ns.elim sg pl h (ns.value .singular hs) = sg :=
  rfl

@[simp] theorem elim_value_plural (hp : .plural ∈ ns.values) :
    ns.elim sg pl h (ns.value .plural hp) = pl :=
  rfl

end System

end Number
