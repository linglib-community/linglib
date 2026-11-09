module

public import Mathlib.Data.PNat.Interval
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

A number system is the set of values a language has, a `Finset Number`. The implicational
universals that constrain which sets occur are claims of the papers that state them, proved there
of the systems each theory generates. The substrate keeps what cardinality decides, whether the
determinate values of a system form an initial segment, which number resolution needs.

## Main definitions

* `Number`: the number values.
* `Number.exactCard`, `Number.fromCard?`: the determinate values and their cardinalities, each
  the partial inverse of the other.
* `Number.DeterminateInitial`: a system's determinate values are an initial segment.
* `Number.elim`: a function on a system of the singular and the plural, by its values at the two.

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
  /-- The singular is for exactly one individual. -/
  | singular
  /-- The dual is for exactly two. -/
  | dual
  /-- The trial is for exactly three. -/
  | trial
  /-- The paucal is for a few, with no fixed upper boundary. -/
  | paucal
  /-- The plural is for more individuals than the system's other values cover, the residual
      value. -/
  | plural
  /-- The greater paucal is for more than the paucal, again with no fixed boundary. -/
  | greaterPaucal
  /-- The greater plural is for an abundance. -/
  | greaterPlural
  /-- The minimal is for the smallest group of its person: one individual, or the speaker and the
      addressee alone in the first person inclusive. -/
  | minimal
  /-- The augmented is for a group larger than the minimal of its person. -/
  | augmented
  /-- The unit augmented is for the minimal group of its person and one more. -/
  | unitAugmented
  /-- The global plural is for every instance in the domain of discourse, tentative in
      [harbour-2014]. -/
  | globalPlural
  deriving DecidableEq, Repr, Fintype

namespace Number

/-! ### Determinate values -/

/-- A determinate value's referent has an exact cardinality, one for the singular, two for the
dual and three for the trial; the other values have none. -/
def exactCard : Number → Option ℕ+
  | .singular => some 1
  | .dual     => some 2
  | .trial    => some 3
  | _         => none

/-- A number value is determinate when its cardinality boundary is fixed, when it has an exact
cardinality. The minimal and unit augmented are not, since they depend on the composition of the
group. -/
def IsDeterminate (v : Number) : Prop := v.exactCard.isSome

instance : DecidablePred IsDeterminate := fun v ↦
  inferInstanceAs (Decidable (v.exactCard.isSome = true))

/-- `fromCard? n` is the determinate value of cardinality `n`, if there is one; from four on there
is none, the greater plural being a value of abundance rather than of four or more. -/
def fromCard? (n : ℕ+) : Option Number :=
  match (n : ℕ) with
  | 1 => some .singular
  | 2 => some .dual
  | 3 => some .trial
  | _ => none

/-- `fromCard?` and `exactCard` are partial inverses. -/
theorem fromCard?_eq_some_iff {n : ℕ+} {v : Number} :
    fromCard? n = some v ↔ v.exactCard = some n := by
  constructor
  · unfold fromCard?
    split <;> rename_i heq <;> intro h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
      subst h <;> exact congrArg some (PNat.eq heq.symm)
  · intro h
    cases v <;> simp only [exactCard, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem fromCard?_eq_none_iff {n : ℕ+} : fromCard? n = none ↔ 3 < n := by
  have hn := n.pos
  rw [← PNat.coe_lt_coe]
  show _ ↔ 3 < (n : ℕ)
  unfold fromCard?
  split <;> simp only [reduceCtorEq, false_iff, true_iff, not_lt]
  iterate 3 omega
  rename_i h₁ h₂ h₃
  have : (n : ℕ) ≠ 1 := h₁
  have : (n : ℕ) ≠ 2 := h₂
  have : (n : ℕ) ≠ 3 := h₃
  omega

theorem le_three_of_exactCard_eq_some {v : Number} {n : ℕ+} (h : v.exactCard = some n) : n ≤ 3 :=
  not_lt.1 fun h3 ↦ by simp [← fromCard?_eq_some_iff, fromCard?_eq_none_iff.2 h3] at h

theorem exists_fromCard?_eq_some {n : ℕ+} (h : n ≤ 3) : ∃ v, fromCard? n = some v :=
  Option.ne_none_iff_exists'.1 fun h' ↦ (fromCard?_eq_none_iff.1 h').not_ge h

/-! ### Number systems -/

/-- A system's determinate values are an initial segment of the singular, dual and trial when,
with the value of a cardinality, it has the value of every smaller one, as the dual requires the
singular and the trial the dual ([harbour-2014] Table 1). -/
def DeterminateInitial (s : Finset Number) : Prop :=
  ∀ v ∈ s, ∀ n ∈ v.exactCard, ∀ m ∈ Finset.Icc 1 n, ∀ w ∈ fromCard? m, w ∈ s

instance : DecidablePred DeterminateInitial := fun _ ↦ by
  unfold DeterminateInitial; infer_instance

/-- A function on the values of a system of the singular and the plural, by its value at
each. -/
def elim {β : Sort*} (s : Finset Number) (sg pl : β)
    (_h : s = {.singular, .plural} := by decide) (n : s) : β :=
  if n.1 = .plural then pl else sg

variable {β : Sort*} {s : Finset Number} {sg pl : β} {h : s = {.singular, .plural}}

@[simp] theorem elim_singular (hs : .singular ∈ s) : elim s sg pl h ⟨.singular, hs⟩ = sg :=
  rfl

@[simp] theorem elim_plural (hp : .plural ∈ s) : elim s sg pl h ⟨.plural, hp⟩ = pl :=
  rfl

end Number
