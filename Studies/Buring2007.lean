module

public import Linglib.Logic.Modal.Basic
public import Linglib.Core.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Polarity.Basic

/-!
# Büring 2007: cross-polar nomalies

Comparatives pairing a positive adjective with a negative one are anomalous — *John is shorter than
Mary is tall* — and yet *the ladder was shorter than the house was high* is perfectly acceptable.
This file formalizes the account of the contrast. A negative adjective is the degree negation of
its positive counterpart, and a comparative whose degree phrase carries that negation inverts both
intervals it compares, so *shorter than … high* can be read as *less long than … high*. Read that
way it compares two positive extents; read literally it compares a positive extent with a negative
one, which no scale makes true, while the reinterpretation is a subcomparative.

The reinterpretation needs the negation and the comparative morpheme in one clause, and it is
preempted where the than-clause adjective is the matrix one modulo the negation, since comparative
deletion then supplies a synonymous competitor. Those two conditions cut the cross-polar space into
the paper's three cases, and they block for different reasons: the anomaly has the reinterpretation
available and loses to its competitor, the inverse nomaly has no competitor and still fails.

A modal in the than-clause separates this account from the variant that puts the degree negation
with the than-clause adjective. The negation outside the modal and the negation inside it turn the
same comparison into the box and the diamond of one proposition, so the first is the stronger
reading under a universal modal and the weaker one under an existential; they coincide only when
the accessible worlds agree on the standard's degree.

## Main definitions

* `compareWith` — the comparative morpheme, relative to the modifier in its degree phrase
* `Comparative`, `Comparative.Acceptable` — a cross-polar comparative and the conditions on it
* `negationOutside`, `negationInside` — the two analyses of a modal than-clause

## Main results

* `compareWith_little` — the degree negation inverts both intervals compared
* `not_crossPolar`, `not_crossPolar'` — neither order of a literal cross-polar comparison is true
* `metamorphosis_iff_subcomparative` — the reinterpretation is a subcomparative
* `nomaly_acceptable`, `blocked_for_different_reasons` — the three-way pattern and its two sources
* `reading_of_deletion` — the deletion competitor is synonymous exactly on one dimension
* `negationOutside_box`, `negationInside_box` — the two analyses as box and diamond
* `outside_entails_inside_box`, `inside_not_entails_outside` — the entailment is strict
* `analyses_agree_of_uniform` — a degree-uniform modal base hides the difference

## References

* [buring-2007]
* [heim-2006]
* [kennedy-1999]
* [kennedy-2001]
* [rullmann-1995]
* [schwarzschild-wilkinson-2002]
* [takahashi-fox-2005]
-/

@[expose] public section

namespace Buring2007

open ModalLogic
open SetRel

/-! ### The comparative and the degree negation -/

section Comparative

variable {D : Type*} [LinearOrder D] {Entity : Type*}

/-- The comparative morpheme `compareWith m i j` holds when the than-clause interval `i` is properly
included in the matrix interval `j`, both read through the degree-phrase modifier `m`, the identity
for MUCH and complementation for LITTLE. -/
def compareWith (m : Set D → Set D) (thanClause matrix : Set D) : Prop :=
  m thanClause ⊂ m matrix

omit [LinearOrder D] in
/-- LITTLE turns a more-comparative into a less-comparative by inverting both intervals compared:
*less* is *LITTLE -er* ([heim-2006]). -/
theorem compareWith_little (i j : Set D) : compareWith compl i j ↔ j ⊂ i :=
  compl_lt_compl_iff_lt

/-- A positive extent is never properly included in a negative one, so the literal reading of *Mary
is taller than John is short* is true on no scale ([kennedy-2001]). -/
theorem not_crossPolar (a b : D) : ¬ compareWith id (Set.Iic a) (Set.Ioi b) :=
  fun h ↦ Set.not_Iic_subset_Ioi a b h.subset

/-- The other order fails too whenever the scale has no greatest degree: *John is shorter than Mary
is tall* read literally would need every degree above John's height to lie below Mary's. -/
theorem not_crossPolar' [NoMaxOrder D] (a b : D) :
    ¬ compareWith id (Set.Ioi a) (Set.Iic b) := by
  intro h
  obtain ⟨d, hd⟩ := exists_gt (max a b)
  exact absurd (h.subset ((le_max_left a b).trans_lt hd))
    (not_le.mpr ((le_max_right a b).trans_lt hd))

/-- Under the reinterpretation, with the negation in the degree phrase, both intervals compared are
positive extents, and the comparison is the subcomparative of [schwarzschild-wilkinson-2002], the
ladder's length against the house's height. -/
theorem metamorphosis_iff_subcomparative (μ₁ μ₂ : Entity → D) (a b : Entity) :
    compareWith compl (Set.Iic (μ₁ a)) (Set.Iic (μ₂ b)) ↔ μ₂ b < μ₁ a :=
  (compareWith_little _ _).trans Set.Iic_ssubset_Iic

end Comparative

/-! ### The three cross-polar configurations -/

/-- The paper's examples measure spatial dimensions, the one scale carrying measurements in more
than one dimension, which is why cross-polar nomalies are confined to it. -/
inductive Dimension where
  | length | height | width | depth
  deriving DecidableEq, Repr

/-- An adjective pairs a dimension with a polarity, measuring it positively (*long*) or negatively
(*short*). -/
structure Adjective where
  dimension : Dimension
  polarity : Polarity
  deriving DecidableEq, Repr

/-- A comparative pairing a matrix adjective with a than-clause adjective. -/
structure Comparative where
  matrix : Adjective
  thanClause : Adjective
  deriving DecidableEq, Repr

namespace Comparative

variable (c : Comparative)

/-- A comparative is cross-polar when its two adjectives are of opposite polarity. -/
def CrossPolar : Prop := c.matrix.polarity ≠ c.thanClause.polarity

/-- The reinterpretation is available only where the degree negation and the comparative morpheme
share a clause, that is where the negative adjective is the matrix one: a than-clause negation
cannot be recombined with the matrix comparative. -/
def Metamorphosis : Prop := c.matrix.polarity = .negative

/-- Comparative deletion is licensed where the than-clause adjective phrase is the matrix one
modulo the degree morphology, that is where the two adjectives measure the same dimension. -/
def Deletion : Prop := c.matrix.dimension = c.thanClause.dimension

/-- A cross-polar comparative survives when the reinterpretation is available and no comparative
deletion competes with it ([takahashi-fox-2005]'s MaxElide prefers the larger ellipsis). -/
def Acceptable : Prop := c.Metamorphosis ∧ ¬ c.Deletion

instance : Decidable c.CrossPolar := inferInstanceAs (Decidable ¬ _)
instance : Decidable c.Metamorphosis := inferInstanceAs (Decidable (_ = _))
instance : Decidable c.Deletion := inferInstanceAs (Decidable (_ = _))
instance : Decidable c.Acceptable := inferInstanceAs (Decidable (_ ∧ _))

/-- The reading a cross-polar comparative gets under the reinterpretation, on a model interpreting
each dimension as a measure function. -/
def reading {Entity D : Type*} [LinearOrder D] (m : Dimension → Entity → D) (c : Comparative)
    (subject standard : Entity) : Prop :=
  m c.matrix.dimension subject < m c.thanClause.dimension standard

end Comparative

/-- In *John is shorter than Mary is tall* the negative adjective is the matrix one and both measure
height. -/
def anomaly : Comparative := ⟨⟨.height, .negative⟩, ⟨.height, .positive⟩⟩

/-- In *Mary is taller than John is short* the negation sits in the than-clause. -/
def reverseAnomaly : Comparative := ⟨⟨.height, .positive⟩, ⟨.height, .negative⟩⟩

/-- In *The ladder was shorter than the house was high* the negative adjective is the matrix one and
the two dimensions differ. -/
def nomaly : Comparative := ⟨⟨.length, .negative⟩, ⟨.height, .positive⟩⟩

/-- In *The house is higher than the ladder is short* the dimensions differ, but the negation is in
the than-clause. -/
def inverseNomaly : Comparative := ⟨⟨.height, .positive⟩, ⟨.length, .negative⟩⟩

theorem configurations_crossPolar :
    anomaly.CrossPolar ∧ reverseAnomaly.CrossPolar ∧ nomaly.CrossPolar ∧
      inverseNomaly.CrossPolar := by decide

/-- The nomaly is reinterpretable and has no deletion competitor. -/
theorem nomaly_acceptable : nomaly.Acceptable := by decide

theorem others_unacceptable :
    ¬ anomaly.Acceptable ∧ ¬ reverseAnomaly.Acceptable ∧ ¬ inverseNomaly.Acceptable := by decide

/-- Neither condition derives the pattern alone: the anomaly is reinterpretable and blocked only by
its competitor, the inverse nomaly has no competitor and is blocked only by the position of the
negation. -/
theorem blocked_for_different_reasons :
    anomaly.Metamorphosis ∧ anomaly.Deletion ∧
      ¬ inverseNomaly.Metamorphosis ∧ ¬ inverseNomaly.Deletion := by decide

/-- Comparative deletion competes only where it is synonymous: on one dimension the reinterpreted
reading is exactly the plain comparative the deletion form expresses, which is why the anomaly
loses to it while the nomaly — whose deletion form makes a different claim — does not. -/
theorem reading_of_deletion {Entity D : Type*} [LinearOrder D] (m : Dimension → Entity → D)
    (c : Comparative) (h : c.Deletion) (subject standard : Entity) :
    c.reading m subject standard ↔
      m c.matrix.dimension subject < m c.matrix.dimension standard := by
  have h' : c.matrix.dimension = c.thanClause.dimension := h
  simp only [Comparative.reading, ← h']

theorem reading_not_synonymous :
    ∃ (m : Dimension → Bool → ℕ) (subject standard : Bool),
      nomaly.reading m subject standard ∧
        ¬ m .length subject < m .length standard := by
  refine ⟨fun d b => match d with | .length => if b then 12 else 10 | _ => 15,
    true, false, ?_, ?_⟩ <;>
    simp [Comparative.reading, nomaly]

/-! ### A modal in the than-clause -/

section Modal

variable {W D : Type*} [LinearOrder D] {Q : (W → Prop) → Prop} {μ : W → D} {c : D}
  {R : SetRel W W} {w : W}

/-- With the degree negation outside the modal, the than-clause denotes the degrees the standard
reaches under the modal, and the less-comparative asserts that the subject's positive extent is
included in it. -/
def negationOutside (Q : (W → Prop) → Prop) (μ : W → D) (c : D) : Prop :=
  Set.Iic c ⊆ {d | Q fun v => d ≤ μ v}

/-- With the degree negation inside the modal, the than-clause denotes the degrees exceeding the
standard under the modal, and the more-comparative asserts that they are among the degrees exceeding
the subject. -/
def negationInside (Q : (W → Prop) → Prop) (μ : W → D) (c : D) : Prop :=
  {d | Q fun v => μ v < d} ⊆ Set.Ioi c

theorem negationOutside_iff (hQ : Monotone Q) :
    negationOutside Q μ c ↔ Q fun v => c ≤ μ v := by
  refine ⟨fun h => h le_rfl, fun h d hd => hQ (fun v hv => hd.trans hv) h⟩

theorem negationInside_iff (hQ : Monotone Q) :
    negationInside Q μ c ↔ ¬ Q fun v => μ v < c := by
  refine ⟨fun h hc => absurd (h hc) (lt_irrefl c), fun h d hd => ?_⟩
  by_contra hdc
  exact h (hQ (fun v hv => hv.trans_le (not_lt.mp hdc)) hd)

theorem monotone_box (R : SetRel W W) (w : W) : Monotone fun p : W → Prop => □[R] p w :=
  fun _ _ h hp v hv => h v (hp v hv)

theorem monotone_diamond (R : SetRel W W) (w : W) :
    Monotone fun p : W → Prop => ◇[R] p w :=
  fun _ _ h hp => hp.imp fun _ hv => ⟨hv.1, h _ hv.2⟩

/-- Under a universal than-clause modal the outside reading is that the standard reaches the
subject's degree in every accessible world — the minimum required width of the moat exceeds the
drawbridge's length. -/
theorem negationOutside_box :
    negationOutside (fun p => □[R] p w) μ c ↔ □[R] (fun v => c ≤ μ v) w :=
  negationOutside_iff (monotone_box R w)

/-- The inside reading of the same sentence is that the standard reaches it in some accessible
world — the maximum permitted width does. -/
theorem negationInside_box :
    negationInside (fun p => □[R] p w) μ c ↔ ◇[R] (fun v => c ≤ μ v) w := by
  rw [negationInside_iff (monotone_box R w), not_box]
  simp [not_lt]

/-- With an existential modal the two readings exchange: the outside reading becomes the weaker
one, about the maximum permitted length of a drawbridge. -/
theorem negationOutside_diamond :
    negationOutside (fun p => ◇[R] p w) μ c ↔ ◇[R] (fun v => c ≤ μ v) w :=
  negationOutside_iff (monotone_diamond R w)

/-- And the inside reading becomes the stronger one, about the minimum permitted length. -/
theorem negationInside_diamond :
    negationInside (fun p => ◇[R] p w) μ c ↔ □[R] (fun v => c ≤ μ v) w := by
  rw [negationInside_iff (monotone_diamond R w), not_diamond]
  simp [not_lt]

/-- Under a universal modal the outside reading entails the inside one. -/
theorem outside_entails_inside_box [IsSerial R] :
    negationOutside (fun p => □[R] p w) μ c → negationInside (fun p => □[R] p w) μ c := by
  rw [negationOutside_box, negationInside_box]
  exact box_D

theorem inside_entails_outside_diamond [IsSerial R] :
    negationInside (fun p => ◇[R] p w) μ c → negationOutside (fun p => ◇[R] p w) μ c := by
  rw [negationOutside_diamond, negationInside_diamond]
  exact box_D

/-- The entailment is strict: where a regulation permits moats of 30 and of 40 feet, a 35-foot
drawbridge is shorter than a permitted moat is wide without being shorter than every one. -/
theorem inside_not_entails_outside :
    ∃ (μ : Bool → ℕ) (c : ℕ),
      negationInside (fun p => □[.univ] p true) μ c ∧
        ¬ negationOutside (fun p => □[.univ] p true) μ c := by
  refine ⟨fun b => if b then 40 else 30, 35, ?_, ?_⟩
  · rw [negationInside_box]
    exact ⟨true, trivial, by decide⟩
  · rw [negationOutside_box]
    exact fun h => absurd (h false trivial) (by decide)

/-- The two readings coincide when the accessible worlds agree on the standard's degree, which is
why a than-clause without a modal cannot tell the analyses apart. -/
theorem analyses_agree_of_uniform [IsSerial R] (h : ∀ v u, w ~[R] v → w ~[R] u → μ v = μ u) :
    negationOutside (fun p => □[R] p w) μ c ↔ negationInside (fun p => □[R] p w) μ c := by
  rw [negationOutside_box, negationInside_box]
  refine ⟨box_D, fun ⟨v, hv, hcv⟩ u hu => ?_⟩
  show c ≤ μ u
  rwa [h u v hu hv]

end Modal

end Buring2007
