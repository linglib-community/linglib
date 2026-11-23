module

public import Linglib.Data.Examples.Buring2007
public import Linglib.Fragments.English.Adjectives
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.Extent

/-!
# Büring 2007: cross-polar nomalies

A degree interval is a set of degrees, and the positive extent of an object measuring `a` is
`Set.Iic a`. The degree modifiers MUCH and LITTLE are the two polarities acting on intervals, MUCH
as the identity and LITTLE as complement, so that a negative adjective such as *short*, LITTLE
*long*, has the extent `Polarity.negative • Set.Iic a`, the degrees above `a`. The comparative
morpheme takes the modifier `m` in its degree phrase and two intervals, and
`comparative m i j` says that `m • i ⊂ m • j` for the than-clause interval `i` and the matrix
interval `j`.

Two extents stand in a comparative only if they have the same polarity
(`polarity_eq_of_comparative`, from `Polarity.eq_of_smul_Iic_subset`), which is the cross-polar
anomaly of *John is shorter than Mary is
tall*. Since the polarities act, a modifier may be moved between the degree phrase and both
adjectives, `comparative m (q • i) (q • j) ↔ comparative (m * q) i j`.

A comparative with *-er* on a negative adjective has two logical forms, `Comparative.literal` with
MUCH in the degree phrase and LITTLE on the adjective, and `Comparative.reanalysis` with LITTLE in
the degree phrase, the form of a *less*-comparative. A logical form whose than-clause adjective is
its matrix adjective is pronounced with comparative deletion, so a comparative that pronounces
both adjectives is acceptable when one of its logical forms compares extents of one polarity and
does not license deletion. Among comparatives of opposite polarities those are the ones whose
matrix adjective is the negative one and is not the antonym of the other
(`Comparative.acceptable_iff_of_polarity_ne`).

A quantifier `Q` over worlds in the than-clause gives the interval `Quantifier.scopeDegrees Q P`
of the degrees that lie in the standard's extent `P v` at the worlds `Q` holds of.
`negationOutside` has LITTLE in the matrix degree phrase, outside `Q`, and `negationInside` has it
on both adjectives, inside `Q`. The second is the first for the dual quantifier
(`negationInside_iff_negationOutside_dual`): over the worlds `A` a necessity modal quantifies
over, `negationOutside (every A)` puts the subject's degree below the least degree the standard has
in `A` and `negationInside (every A)` puts it below the greatest, and for a possibility modal,
`Quantifier.Det.some A`, they exchange.

## Implementation notes

An adjective is a pole of an `AntonymPair` of the English fragment, the pair standing for the
positive adjective the paper decomposes both poles into; *short* is a pole of two pairs, with
*tall* and with *long*. Degree intervals are arbitrary sets, where the paper restricts them to
nonempty convex ones. The anomaly of a positive matrix adjective with a negative than-clause
needs a scale with no greatest degree, since the degrees above the greatest one are none.

## References

* [buring-2007]
* [heim-2006]
* [kennedy-2001]
* [rullmann-1995]
* [schwarzschild-wilkinson-2002]
* [takahashi-fox-2005]
-/

@[expose] public section

namespace Buring2007

open Polarity

/-! ### The comparative and the degree modifiers -/

section Comparative

variable {D : Type*} {i j : Set D}

/-- (21c): the comparative morpheme with the modifier `m` in its degree phrase, MUCH or LITTLE,
holds of the than-clause interval and the matrix interval when the first, modified, is properly
included in the second, modified. -/
def comparative (m : Polarity) (thanClause matrix : Set D) : Prop :=
  m • thanClause ⊂ m • matrix

-- LITTLE inverts both intervals, which makes a *less*-comparative of a *more*-comparative.
theorem comparative_negative : comparative .negative i j ↔ j ⊂ i :=
  compl_lt_compl_iff_lt

theorem comparative_smul (m q : Polarity) :
    comparative m (q • i) (q • j) ↔ comparative (m * q) i j := by
  simp only [comparative, mul_smul]

variable [LinearOrder D] {a b : D}

theorem comparative_positive_Iic : comparative .positive (Set.Iic b) (Set.Iic a) ↔ b < a :=
  Set.Iic_ssubset_Iic

theorem comparative_negative_Iic : comparative .negative (Set.Iic b) (Set.Iic a) ↔ a < b :=
  comparative_negative.trans Set.Iic_ssubset_Iic

/-- On a scale with no greatest degree, two extents that stand in a comparative have the same
polarity. -/
theorem polarity_eq_of_comparative [NoMaxOrder D] {m q₁ q₂ : Polarity}
    (h : comparative m (q₂ • Set.Iic b) (q₁ • Set.Iic a)) : q₁ = q₂ := by
  rcases m with _ | _
  · exact (eq_of_smul_Iic_subset h.subset).symm
  · exact eq_of_smul_Iic_subset (comparative_negative.mp h).subset

end Comparative

/-! ### Logical forms and comparative deletion -/

/-- An adjective is a pole of an antonym pair, the positive adjective of the pair or LITTLE with
it. -/
structure Pole where
  /-- The antonym pair. -/
  pair : AntonymPair
  /-- Positive for the bare adjective, negative for LITTLE with it. -/
  polarity : Polarity
  deriving DecidableEq

/-- (15)–(18): a logical form of a comparative has a modifier in the matrix degree phrase and an
adjective in each clause. -/
structure LF where
  /-- The modifier in the degree phrase, MUCH or LITTLE. -/
  deg : Polarity
  /-- The matrix adjective. -/
  matrix : Pole
  /-- The than-clause adjective. -/
  thanClause : Pole

namespace LF

variable {Entity D : Type*} [LinearOrder D] {lf : LF} {meas : AntonymPair → Entity → D}
  {x y : Entity}

/-- A logical form holds of a subject `x` and a standard `y`, on measure functions for the
positive adjectives, when the comparative holds of the extent of `y` and the extent of `x`. -/
def Holds (lf : LF) (meas : AntonymPair → Entity → D) (x y : Entity) : Prop :=
  comparative lf.deg (lf.thanClause.polarity • Set.Iic (meas lf.thanClause.pair y))
    (lf.matrix.polarity • Set.Iic (meas lf.matrix.pair x))

/-- A logical form is of one sort when its two adjectives have the same polarity. -/
def SameSort (lf : LF) : Prop := lf.matrix.polarity = lf.thanClause.polarity

/-- A logical form licenses comparative deletion when its than-clause adjective is its matrix
adjective. -/
def Deletable (lf : LF) : Prop := lf.thanClause = lf.matrix

instance : DecidablePred SameSort := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Deletable := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem Holds.sameSort [NoMaxOrder D] (h : lf.Holds meas x y) : lf.SameSort :=
  polarity_eq_of_comparative h

theorem sameSort_iff_exists_holds :
    lf.SameSort ↔ ∃ (meas : AntonymPair → Bool → ℕ) (x y : Bool), lf.Holds meas x y := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, _, h⟩ ↦ h.sameSort⟩
  obtain ⟨m, ⟨p₁, q⟩, ⟨p₂, q₂⟩⟩ := lf
  obtain rfl : q = q₂ := h
  rcases hmq : m * q with _ | _
  · refine ⟨fun _ e ↦ if e then 1 else 0, true, false, (comparative_smul m q).mpr ?_⟩
    rw [hmq]
    exact comparative_positive_Iic.mpr (by simp)
  · refine ⟨fun _ e ↦ if e then 1 else 0, false, true, (comparative_smul m q).mpr ?_⟩
    rw [hmq]
    exact comparative_negative_Iic.mpr (by simp)

end LF

/-- A comparative with *-er* on its matrix adjective and an adjective pronounced in its
than-clause. -/
structure Comparative where
  /-- The matrix adjective. -/
  matrix : Pole
  /-- The than-clause adjective. -/
  thanClause : Pole

namespace Comparative

variable (c : Comparative)

/-- (17): the logical form with MUCH in the degree phrase and the adjectives as pronounced. -/
def literal : LF := ⟨.positive, c.matrix, c.thanClause⟩

/-- (18): the logical form with the matrix adjective's LITTLE, if it has one, in the degree
phrase. -/
def reanalysis : LF := ⟨c.matrix.polarity, ⟨c.matrix.pair, .positive⟩, c.thanClause⟩

/-- A comparative is acceptable when one of its logical forms is of one sort and does not license
comparative deletion, which would leave the than-clause adjective unpronounced. -/
def Acceptable : Prop := ∃ lf ∈ [c.literal, c.reanalysis], lf.SameSort ∧ ¬ lf.Deletable

instance : Decidable c.Acceptable := inferInstanceAs (Decidable (∃ lf ∈ [_, _], _))

variable {c}

-- (6b): the reanalysis of *shorter than … high* is the subcomparative *less long than … high*.
theorem reanalysis_holds_iff {Entity D : Type*} [LinearOrder D] {meas : AntonymPair → Entity → D}
    {x y : Entity} (hm : c.matrix.polarity = .negative) (ht : c.thanClause.polarity = .positive) :
    c.reanalysis.Holds meas x y ↔ meas c.matrix.pair x < meas c.thanClause.pair y := by
  simp only [LF.Holds, reanalysis, hm, ht, positive_smul, comparative_negative_Iic]

/-- A comparative whose adjectives have opposite polarities is acceptable exactly when the matrix
adjective is the negative one and the two are not antonyms. -/
theorem acceptable_iff_of_polarity_ne (h : c.matrix.polarity ≠ c.thanClause.polarity) :
    c.Acceptable ↔ c.matrix.polarity = .negative ∧ c.matrix.pair ≠ c.thanClause.pair := by
  obtain ⟨⟨p₁, q₁⟩, ⟨p₂, q₂⟩⟩ := c
  rcases q₁ with _ | _ <;> rcases q₂ with _ | _ <;>
    simp_all [Acceptable, literal, reanalysis, LF.SameSort, LF.Deletable, eq_comm]

end Comparative

/-! ### The paper's comparatives -/

section Rows

open English.Adjectives Examples

/-- A comparative with the example it is the form of. -/
structure Compared where
  /-- The comparative. -/
  form : Comparative
  /-- The example. -/
  row : Datum

/-- The examples that pronounce an adjective in each clause. *short* is the antonym of *tall* of
a person and of *long* of a ladder, a hose or a boat. -/
def comparisons : List Compared :=
  [⟨⟨⟨height, .negative⟩, ⟨height, .positive⟩⟩, ex_1a⟩,
   ⟨⟨⟨height, .positive⟩, ⟨height, .negative⟩⟩, ex_1b⟩,
   ⟨⟨⟨length, .negative⟩, ⟨elevation, .positive⟩⟩, ex_2a⟩,
   ⟨⟨⟨length, .negative⟩, ⟨width, .positive⟩⟩, ex_2b⟩,
   ⟨⟨⟨length, .negative⟩, ⟨width, .positive⟩⟩, ex_2c⟩,
   ⟨⟨⟨width, .negative⟩, ⟨length, .positive⟩⟩, ex_3⟩,
   ⟨⟨⟨length, .negative⟩, ⟨length, .positive⟩⟩, ex_4⟩,
   ⟨⟨⟨elevation, .positive⟩, ⟨length, .negative⟩⟩, ex_5⟩]

/-- The comparatives the paper accepts are those with a logical form of one sort that does not
license comparative deletion. -/
theorem acceptable_iff_judgment :
    ∀ c ∈ comparisons, c.form.Acceptable ↔ c.row.judgment = .acceptable := by
  decide

end Rows

/-! ### A quantifier in the than-clause -/

section Scope

open Quantifier Quantifier.Det

variable {W D : Type*} [LinearOrder D] {Q : Quantifier W} {μ : W → D} {c : D} {A : Set W}

/-- (30): LITTLE in the matrix degree phrase, outside the than-clause quantifier, with a subject
measuring `c`. -/
def negationOutside (Q : Quantifier W) (μ : W → D) (c : D) : Prop :=
  comparative .negative (scopeDegrees Q (Set.Iic ∘ μ)) (Set.Iic c)

/-- (32): LITTLE on both adjectives, inside the than-clause quantifier, with a subject measuring
`c`. -/
def negationInside (Q : Quantifier W) (μ : W → D) (c : D) : Prop :=
  comparative .positive (scopeDegrees Q fun v ↦ Polarity.negative • Set.Iic (μ v))
    (Polarity.negative • Set.Iic c)

/-- LITTLE inside a than-clause quantifier is LITTLE outside its dual. -/
theorem negationInside_iff_negationOutside_dual (d : Det W) :
    negationInside (d A) μ c ↔ negationOutside (d.dual A) μ c := by
  have h : scopeDegrees (d A) (fun v ↦ Polarity.negative • Set.Iic (μ v)) =
      (scopeDegrees (d.dual A) (Set.Iic ∘ μ))ᶜ := by
    ext e
    simp [mem_scopeDegrees, dual, innerNeg, Set.compl_ofPred]
  rw [negationInside, h]
  rfl

theorem negationOutside_iff (hQ : Monotone Q) :
    negationOutside Q μ c ↔ ∃ e, c < e ∧ Q {v | e ≤ μ v} := by
  refine comparative_negative.trans ⟨fun h ↦ ?_, fun ⟨e, hce, he⟩ ↦ ⟨fun e' he' ↦ ?_, fun h ↦ ?_⟩⟩
  · obtain ⟨e, he, hec⟩ := Set.exists_of_ssubset h
    exact ⟨e, not_le.mp hec, he⟩
  · exact hQ (fun v hv ↦ (he'.trans hce.le).trans hv) he
  · exact hce.not_ge (h he)

-- Without a quantifier the two analyses are one: both say the subject is below the standard.
theorem negationInside_individual_iff_negationOutside {w : W} :
    negationInside (individual w) μ c ↔ negationOutside (individual w) μ c :=
  comparative_smul .positive .negative

theorem negationOutside_individual_iff {w : W} : negationOutside (individual w) μ c ↔ c < μ w :=
  comparative_negative_Iic

-- (31), with `A` the worlds the modal quantifies over.
theorem negationOutside_every :
    negationOutside (every A) μ c ↔ ∃ e, c < e ∧ e ∈ lowerBounds (μ '' A) :=
  (negationOutside_iff (monotone_every A)).trans <|
    exists_congr fun _ ↦ and_congr_right fun _ ↦ (mem_lowerBounds.trans Set.forall_mem_image).symm

theorem negationOutside_some : negationOutside (Det.some A) μ c ↔ ∃ v ∈ A, c < μ v :=
  (negationOutside_iff (monotone_some A)).trans
    ⟨fun ⟨_, hce, v, hv, he⟩ ↦ ⟨v, hv, hce.trans_le he⟩, fun ⟨v, hv, hc⟩ ↦ ⟨_, hc, v, hv, le_rfl⟩⟩

-- (33)
theorem negationInside_every : negationInside (every A) μ c ↔ ∃ v ∈ A, c < μ v := by
  rw [negationInside_iff_negationOutside_dual, dual_every, negationOutside_some]

theorem negationInside_some :
    negationInside (Det.some A) μ c ↔ ∃ e, c < e ∧ e ∈ lowerBounds (μ '' A) := by
  rw [negationInside_iff_negationOutside_dual, dual_some, negationOutside_every]

-- (31): the minimum required width of the moat is more than the length of the drawbridge.
theorem negationOutside_every_iff_of_isLeast {m : D} (h : IsLeast (μ '' A) m) :
    negationOutside (every A) μ c ↔ c < m :=
  negationOutside_every.trans
    ⟨fun ⟨_, hce, he⟩ ↦ hce.trans_le (he h.1), fun hc ↦ ⟨m, hc, h.2⟩⟩

-- (33): the maximum allowed width of the moat is more than the length of the drawbridge.
theorem negationInside_every_iff_of_isGreatest {m : D} (h : IsGreatest (μ '' A) m) :
    negationInside (every A) μ c ↔ c < m := by
  obtain ⟨⟨u, hu, rfl⟩, hm⟩ := h
  exact negationInside_every.trans
    ⟨fun ⟨v, hv, hc⟩ ↦ hc.trans_le (hm ⟨v, hv, rfl⟩), fun hc ↦ ⟨u, hu, hc⟩⟩

/-- Under a universal quantifier over a nonempty set, LITTLE outside the quantifier entails LITTLE
inside it. -/
theorem negationInside_every_of_negationOutside (hA : A.Nonempty)
    (h : negationOutside (every A) μ c) : negationInside (every A) μ c :=
  let ⟨_, hce, he⟩ := negationOutside_every.mp h
  let ⟨v, hv⟩ := hA
  negationInside_every.mpr ⟨v, hv, hce.trans_le (he ⟨v, hv, rfl⟩)⟩

theorem negationOutside_some_of_negationInside (hA : A.Nonempty)
    (h : negationInside (Det.some A) μ c) : negationOutside (Det.some A) μ c :=
  let ⟨_, hce, he⟩ := negationInside_some.mp h
  let ⟨v, hv⟩ := hA
  negationOutside_some.mpr ⟨v, hv, hce.trans_le (he ⟨v, hv, rfl⟩)⟩

-- A 35-foot drawbridge where moats of 30 and of 40 feet are permitted: shorter than a permitted
-- moat is wide, not shorter than every one. (29) has the second reading only.
theorem exists_negationInside_every_not_negationOutside :
    ∃ (μ : Bool → ℕ) (c : ℕ),
      negationInside (every .univ) μ c ∧ ¬ negationOutside (every .univ) μ c := by
  refine ⟨fun b ↦ if b then 40 else 30, 35, negationInside_every.mpr ⟨true, trivial, by decide⟩, ?_⟩
  rw [negationOutside_every]
  rintro ⟨e, hce, he⟩
  exact absurd (hce.trans_le (he ⟨false, trivial, rfl⟩)) (by decide)

end Scope

end Buring2007
