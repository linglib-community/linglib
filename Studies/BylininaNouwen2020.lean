module

public import Mathlib.Data.Fintype.EquivFin
public import Studies.BylininaNouwen2018
public import Studies.Partee1987
public import Studies.Spector2013

/-!
# Bylinina and Nouwen (2020): Numeral semantics

This file formalizes the survey of numeral meanings by Bylinina and Nouwen. Once the determiner
view is set aside, a bare numeral has been taken to denote a predicate counting the atoms of a
plurality, `λx. #x = n`, a number `n`, or a quantifier over degree properties, Kennedy's
`λP. max(P) = n`, and operators relate the three: the counting operator `MANY` takes the number to
the predicate ((22), (23)), the survey's `CARD` takes the predicate back ((24), (25)), and Partee's
`BE` and `IOTA` lower the quantifier to the number ((47)–(50)). Lowering forgets the upper bound,
so the lowered numeral, interpreted in situ, has an at least reading.

The views differ in where the exactly reading comes from. On the predicate and number views a
numeral with a distributive predicate is lower-bounded ((29)) and an exhaustivity operator
strengthens it ((32), (34)); on Kennedy's view the numeral is doubly bounded and takes scope by QR
((43)–(46)). At each scope site the two coincide, as Bylinina and Nouwen (2018) observed for
*zero*: exhaustifying the lower bound against the higher numerals says that the numeral is the
greatest degree of the property abstracted there, which is what Kennedy's quantifier says of it.
Above a possibility modal both give the strong reading (36-b), Kennedy's (46), and above *some
students* both give (39), a reading the sentence is reported to lack (fn. 9 flags the judgement).
The accounts differ in which sites they reach: the Heim-Kennedy generalization (42) keeps degree
operators below nominal quantifiers, and nothing keeps a propositional `EXH` there.

The survey's proposal keeps the quantifier type and the lower bound: the numeral is the Montague
lift of the number ((52)), and an operator `MAX` turns it into Kennedy's quantifier ((53), (54)).
At the numeral's landing site `MAX` is exhaustification, so the strengthening moves with the
numeral and obeys (42). The lower bound has to be basic because of *zero* ((51)), the argument of
Bylinina and Nouwen (2018): Kennedy's *zero A B* is *no A B* and licenses the negative polarity
items that *zero* does not, while with `MAX` apart from the numeral *zero* is a tautology below
`MAX` and *no* above it, and licenses none.

## Main results

* `exhAgainst_poss_iff_highScope`: the exhaustified possibility reading of Spector is
  Kennedy's (46).
* `lowScope_some_not_highScope`: over *some students* the high reading (39) is strictly stronger.
* `MAX_individual_iff_exhAgainst`: `MAX` of the lifted number is exhaustification at its site.
* `not_licenses_zeroWithMAX`: with `MAX`, *zero* licenses no negative polarity item.

## Implementation notes

* Degrees are natural numbers, a degree property is a `Set ℕ` and a degree quantifier a predicate
  on them. Kennedy's numeral is the substrate's `Degree.MaxIn {n}`, and its scope relative to a
  modal or nominal quantifier `Q` over a count `μ` is `Degree.LowScope` or `Degree.HighScope`.
* Pluralities, degree properties and licensing are those of `BylininaNouwen2018`: the finite sets
  of atoms, with the empty plurality, so `plural Z` is the full lattice `×Z` and Link's `*Z` ((12))
  its nonempty part. The lower bound (29) is `isLowerSet_countDegrees_plural`, and its failure with
  a collective predicate (fn. 8) `countDegrees_singleton`.
* `EXH` is `Exhaustification.exhAgainst (· < ·)`, denying every higher numeral, which on those
  lower sets are the stronger alternatives of (32).

## TODO

The determiner view (Section 2) and the Dutch *hoeven* data (26)–(28) are not formalized.

## References

* [bylinina-nouwen-2020]
* [bylinina-nouwen-2018]
* [kennedy-2015]
* [partee-1987]
* [spector-2013]
* [heim-2000]
* [link-1983]
-/

@[expose] public section
namespace BylininaNouwen2020

open BylininaNouwen2018 Degree Exhaustification Quantifier Quantifier.GQ
  Quantifier.NP Set

variable {α : Type*}

/-! ### The modifier and number views

The modifier meaning of a numeral is the counting operator at its number, so the two views differ
only in whether the counting is built into the numeral or supplied by an operator. -/

/-- `MANY d` is the property of pluralities with `d` atoms, `λx. #x = d` ((22)). -/
def MANY (d : ℕ) : Set (Finset α) := Finset.card ⁻¹' {d}

theorem mem_MANY {d : ℕ} {x : Finset α} : x ∈ MANY d ↔ x.card = d := Iff.rfl

/-- `CARD P` is the number of atoms every plurality in `P` has, `ιd. ∀x[P(x) → #x = d]` ((24)). -/
noncomputable def CARD (P : Set (Finset α)) : Option ℕ := iota fun d ↦ ∀ x ∈ P, x.card = d

/-- `CARD` recovers the number a modifier meaning counts ((25)), given a plurality of that size. -/
theorem CARD_MANY {n : ℕ} (hn : ∃ x : Finset α, x.card = n) : CARD (MANY (α := α) n) = some n :=
  (iota_eq_some_iff _).2 ⟨fun _ hx ↦ hx, fun _ h ↦ let ⟨x, hx⟩ := hn; (h x hx).symm.trans hx⟩

/-- Numbers as classes of equinumerous pluralities ((17)) are faithful exactly when there are
pluralities of every size: on a finite domain every numeral beyond its size denotes the empty
property. -/
theorem MANY_injective_iff : Function.Injective (MANY (α := α)) ↔ Infinite α := by
  refine ⟨fun h ↦ not_finite_iff_infinite.1 fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := Fintype.ofFinite α
    have key : ∀ k, MANY (α := α) (Fintype.card α + 1 + k) = ∅ := fun k ↦
      eq_empty_of_forall_notMem fun x hx ↦ by
        have := Finset.card_le_univ x; have := mem_MANY.1 hx; omega
    exact absurd (h ((key 0).trans (key 1).symm)) (by omega)
  · exact (preimage_injective.2 (Infinite.exists_subset_card_eq α)).comp singleton_injective

/-! ### Exhaustification and degree quantifiers

Exhaustifying the lower bound at a site and raising Kennedy's quantifier there give the same reading
(`BylininaNouwen2018.exhAgainst_iff_highScope`, `BylininaNouwen2018.exhAgainst_iff_lowScope`), so
the accounts differ only in the sites available to them. -/

section Scope

variable {n : ℕ}

/-- Spector's wide-scope exhaustification over a possibility modal, the reading (36-b), is
Kennedy's numeral raised over the modal ((46)). -/
theorem exhAgainst_poss_iff_highScope {W : Type*} {R : W → Prop} {count : W → ℕ} :
    exhAgainst (· < ·) (fun m ↦ Spector2013.poss (count '' {w | R w})
      (Comparison.ge.interval m)) n ↔ HighScope (MaxIn {n}) (GQ.some R) (Iic ∘ count) := by
  simp only [Spector2013.poss, exists_mem_image, Comparison.interval_ge, mem_Ici, mem_ofPred_eq]
  exact exhAgainst_iff_highScope (Q := GQ.some R) (P := Iic ∘ count)

/-- The exactly reading under the possibility modal, (36-a), is Kennedy's numeral in situ. -/
theorem poss_eq_iff_lowScope {W : Type*} {R : W → Prop} {count : W → ℕ} :
    Spector2013.poss (count '' {w | R w}) (Comparison.eq.interval n) ↔
      LowScope (MaxIn {n}) (GQ.some R) (Iic ∘ count) := by
  simp only [Spector2013.poss, exists_mem_image, Comparison.interval_eq, lowScope_maxIn]
  rfl

/-- Over *some students* the high reading (39) is strictly stronger than the low one. It entails
the low one (`Degree.lowScope_some_of_highScope`), and a student answering `n` questions with
another answering `n + 1` makes the low reading true and (39) false. -/
theorem lowScope_some_not_highScope (n : ℕ) :
    LowScope (MaxIn {n}) (GQ.some fun _ ↦ True) (Iic ∘ fun i : Fin 2 ↦ n + i) ∧
      ¬ HighScope (MaxIn {n}) (GQ.some fun _ ↦ True) (Iic ∘ fun i : Fin 2 ↦ n + i) :=
  ⟨lowScope_maxIn.2 ⟨0, trivial, rfl⟩, fun h ↦ absurd
    ((highScope_maxIn_singleton_some.1 h).2 ⟨1, trivial, rfl⟩) (by simp)⟩

end Scope

/-! ### Lowering

`BE` and `IOTA` take Kennedy's quantifier to the number as they take the lift of an entity to the
entity ((48)–(50)), and send it where they send the lower-bound quantifier. -/

/-- `BE` lowers the exactly-reading quantifier to the singleton of its number ((49)). -/
theorem BE_maxIn_singleton (n : ℕ) : BE (MaxIn {n}) = ident n :=
  funext fun x ↦ propext (maxIn_singleton.trans
    ⟨fun h ↦ (h.1 : n = x).symm, fun h ↦ h ▸ isGreatest_singleton⟩)

theorem BE_maxIn_singleton_eq_BE_individual (n : ℕ) : BE (MaxIn {n}) = BE (individual n) := by
  rw [BE_maxIn_singleton, BE_individual]

/-- `IOTA(BE(twelve)) = 12` ((50)), as `IOTA(BE(λP.P(Mary))) = Mary` ((48)). -/
theorem iota_BE_maxIn_singleton (n : ℕ) : iota (BE (MaxIn {n})) = some n := by
  rw [BE_maxIn_singleton_eq_BE_individual]; exact Partee1987.iota_BE_lift n

theorem maxIn_singleton_injective : Function.Injective fun n : ℕ ↦ MaxIn {n} :=
  fun a b (h : MaxIn {a} = MaxIn {b}) ↦
    ident_injective (by rw [← BE_maxIn_singleton, ← BE_maxIn_singleton, h])

/-! ### The survey's proposal

The empty slot in the type landscape is a lower-bound degree quantifier, the Montague lift
`individual n` of the number ((52)), from which `MAX` derives the exactly reading ((53), (54)). -/

/-- `MAX D` holds of the degree properties whose maximum lies in every member of `D`, as in
`λD λP. max(P) ∈ ∩D` ((53)). -/
def MAX (D : Set (Set ℕ)) : Set ℕ → Prop := MaxIn (⋂₀ D)

/-- `MAX` takes the lower-bound quantifier to Kennedy's ((54)), since the properties containing
`n` intersect to `{n}`. -/
theorem MAX_individual (n : ℕ) : MAX (individual n) = MaxIn {n} :=
  congrArg MaxIn (sInter_individual n)

/-- At its landing site `MAX` of the lower-bound quantifier is its exhaustification against the
higher numerals, a strengthening that moves with the numeral. -/
theorem MAX_individual_iff_exhAgainst {n : ℕ} {P : Set ℕ} :
    MAX (individual n) P ↔ exhAgainst (· < ·) (individual · P) n := by
  rw [MAX_individual]; exact maxIn_singleton_iff_exhAgainst

/-- The exactly-reading quantifier is strictly stronger than the lower-bound one, so `MAX` does
work: `{n, n + 1}` contains `n` without `n` being its greatest element. -/
theorem maxIn_singleton_lt_individual (n : ℕ) : MaxIn {n} < (individual n : Set ℕ → Prop) :=
  lt_of_le_not_ge (fun _ h ↦ (maxIn_singleton.1 h).1) fun h ↦
    absurd ((maxIn_singleton.1 (h {n, n + 1} (Or.inl rfl))).2 (Or.inr rfl)) (by omega)

/-- `MAX` of the lower-bound *zero A B* is Kennedy's *zero A B*, which is *no A B* ((51)). -/
theorem MAX_individual_zero_iff [DecidableEq α] {A B : Set α} :
    MAX (individual 0) (countDegrees A (plural B)) ↔ GQ.no A B := by
  rw [MAX_individual]; exact maxIn_zero_countDegrees_iff

section Polarity

open PolarityItem (NonemptyPredicate)
open scoped Classical

/-- With `MAX` apart from the numeral, *zero* is a scalar licenser, the lower-bound numeral below
`MAX` and its `MAX` above it. -/
def zeroWithMAX : PolarityItem.Licenser :=
  .scalar ⟨⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
      fun p B ↦ individual 0 (countDegrees p.A (plural B))⟩,
    fun p B ↦ MAX (individual 0) (countDegrees p.A (plural B))⟩

theorem zeroWithMAX_eq_zero : zeroWithMAX = BylininaNouwen2018.zero := by
  simp only [zeroWithMAX, BylininaNouwen2018.zero]
  congr
  funext p B
  exact propext MAX_individual_iff_exhAgainst

/-- So it licenses no negative polarity item, where Kennedy's *zero* is *no* and licenses both
(`BylininaNouwen2018.kennedyZero_eq_nobody`). -/
theorem not_licenses_zeroWithMAX (e : PolarityItem) : ¬ zeroWithMAX.Licenses e :=
  zeroWithMAX_eq_zero ▸ not_licenses_zero e

end Polarity

end BylininaNouwen2020
