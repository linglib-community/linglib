module

public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.Degree.Comparison
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Solt & Waldon (2019): Numerals under Negation

This file formalizes the felicity constraint on numerical assertions of Solt and Waldon.
A bare numeral in the scope of negation, *she doesn't have 40 sheep*, is infelicitous as an
answer to *how many sheep does Lisa have?* yet acceptable once the value is under
discussion, as the denial after *does Lisa have 40 sheep?*; negated *more than 40* is
acceptable in both contexts, negated *between 40 and 50* in neither. The paper's account
takes the question under discussion to be a partition (Groenendijk and Stokhof,
Roberts). A how-many question partitions the worlds by a count, so the number line
orders its cells, and the constraint requires the content of an assertion containing a
numerical expression to be the union of a convex set of cells, convexity in the sense of
Gärdenfors carried from lexical meanings to discourse. On the exact reading of the
numeral (Kennedy), *not 40* is the union of every cell but one, a disjoint region;
*40*, *between 40 and 50*, *more than 40* and *not more than 40* are convex. A polar
question has two cells, whose every subset is convex, so the denial is felicitous. At the
top of a bounded scale the negated endpoint is convex, which is why *not 100% certain* is
acceptable where *not 95% certain* is not.

`Felicitous f φ` states the constraint for a question that sorts the worlds by an ordered
value `f`, the how-many question by the count and the polar question by the indicator; a
felicitous assertion is one the question decides (`Felicitous.decides`), and for a polar
question the converse holds (`felicitous_of_polar`). Every numeral form is felicitous
(`felicitous_over`), and so is the negation of every form but the two-sided one
(`felicitous_compl_over`). `not_felicitous_compl` is the general form of the infelicity:
negating a bounded range leaves a disjoint region whenever the count reaches below, into, and
above it. The lower-bounded reading of the numeral would negate to a convex region, but the
paper argues it is unavailable in comment position, where a numeral answers the exact value
the question asks for.

## Implementation notes

The corpus study and the two acceptability experiments are reported in prose. The corpus
finds negated bare numerals in denials of assertions, in contexts where the value was
mentioned or implied, and in negations of a minimum significant value with the
lower-bounded reading. Experiment 1 finds negated bare numerals rated between licensed and
unlicensed polarity items, far better when the value was mentioned or implied than when it
was not inferable, and better than *about n* throughout. Experiment 2 finds bare numerals
under negation quite unacceptable as answers to a how-many question and almost fully
restored by prior mention, unlike *any* and *some*, whose unlicensed uses prior mention
does not improve, and unlike the positive polarity items *about n* and *at least n*, which
prior mention improves less; *more than n* is acceptable under negation in both contexts,
*between m and n* in neither. Modified numerals other than *between* are polarity-sensitive
for reasons beyond convexity, which the paper leaves open.

## References

* [solt-waldon-2019]
* [groenendijk-stokhof-1984]
* [roberts-1996]
* [gardenfors-2004]
* [kennedy-2015]
-/

@[expose] public section

namespace SoltWaldon2019

open Set Degree

variable {W ι : Type*} [Preorder ι]

/-! ### The felicity constraint -/

/-- The felicity constraint on numerical assertions, relative to the question that sorts
the worlds by the ordered value `f`, requires the content to be the union of a convex set of
cells. -/
def Felicitous (f : W → ι) (φ : Set W) : Prop :=
  ∃ I : Set ι, I.OrdConnected ∧ φ = f ⁻¹' I

theorem Felicitous.decides {f : W → ι} {φ : Set W} (h : Felicitous f φ) :
    (Setoid.ker f).Decides φ := by
  obtain ⟨I, -, rfl⟩ := h
  exact Setoid.decides_iff.2 fun w v hwv ↦ by simp [Setoid.ker_def.1 hwv]

theorem ordConnected_prop (I : Set Prop) : I.OrdConnected := by
  refine ⟨fun x hx y hy z ⟨hxz, hzy⟩ ↦ ?_⟩
  by_cases hz : z
  · exact (propext ⟨fun _ ↦ hzy hz, fun _ ↦ hz⟩ : z = y) ▸ hy
  · exact (propext ⟨fun h ↦ absurd h hz, fun h ↦ absurd (hxz h) hz⟩ : z = x) ▸ hx

theorem felicitous_of_polar {p φ : Set W} (h : (Setoid.polar p).Decides φ) :
    Felicitous (· ∈ p) φ := by
  refine ⟨(· ∈ p) '' φ, ordConnected_prop _, ?_⟩
  ext w
  constructor
  · exact fun hw ↦ ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    exact (Setoid.decides_iff.1 h v w (Setoid.polar_iff.2 (eq_iff_iff.1 hvw))).1 hv

/-! ### The how-many question

The assertion that the value satisfies a numerical meaning `I` is `f ⁻¹' I`, the union of the
question's cells over the values in `I`, and a numeral form with comparison `c` and number `m`
asserts `f ⁻¹' c.interval m`. -/

theorem felicitous_preimage (f : W → ι) (I : Set ι) [hI : I.OrdConnected] :
    Felicitous f (f ⁻¹' I) :=
  ⟨I, hI, rfl⟩

theorem felicitous_over {ι : Type*} [PartialOrder ι] (f : W → ι) (c : Comparison) (m : ι) :
    Felicitous f (f ⁻¹' c.interval m) :=
  felicitous_preimage f (c.interval m)

variable (count : W → ℕ)

theorem felicitous_between (m k : ℕ) : Felicitous count (count ⁻¹' Icc m k) :=
  felicitous_preimage count _

theorem felicitous_compl_over {ι : Type*} [LinearOrder ι] (f : W → ι) {c : Comparison}
    (hc : c ≠ .eq) (m : ι) : Felicitous f (f ⁻¹' c.interval m)ᶜ := by
  have h : ((c.interval m)ᶜ).OrdConnected := by
    cases c
    · exact absurd rfl hc
    all_goals
      simp only [Comparison.interval_ge, Comparison.interval_gt, Comparison.interval_le,
        Comparison.interval_lt, compl_Ici, compl_Ioi, compl_Iic, compl_Iio]
      infer_instance
  exact ⟨_, h, rfl⟩

theorem not_felicitous_compl {I : Set ℕ} {a b c : W} (ha : count a ∉ I) (hb : count b ∈ I)
    (hc : count c ∉ I) (hab : count a ≤ count b) (hbc : count b ≤ count c) :
    ¬ Felicitous count (count ⁻¹' I)ᶜ := by
  rintro ⟨J, hJ, hφ⟩
  have mem : ∀ w, count w ∉ I ↔ count w ∈ J := fun w ↦ by
    rw [← mem_preimage (s := J), ← hφ]; rfl
  exact (mem b).2 (hJ.out ((mem a).1 ha) ((mem c).1 hc) ⟨hab, hbc⟩) hb

theorem not_felicitous_not_bare {m : ℕ} {a b c : W} (ha : count a < m) (hb : count b = m)
    (hc : m < count c) : ¬ Felicitous count (count ⁻¹' {m})ᶜ :=
  not_felicitous_compl count (I := Comparison.eq.interval m) (a := a) (b := b) (c := c)
    (by simp; omega) (by simp [hb]) (by simp; omega) (by omega) (by omega)

theorem not_felicitous_not_between {m k : ℕ} {a b c : W} (ha : count a < m)
    (hb : count b ∈ Icc m k) (hc : k < count c) : ¬ Felicitous count (count ⁻¹' Icc m k)ᶜ :=
  not_felicitous_compl count (a := a) (b := b) (c := c) (by simp; omega) hb (by simp; omega)
    (by rw [mem_Icc] at hb; omega) (by rw [mem_Icc] at hb; omega)

theorem felicitous_not_bare_of_max {m : ℕ} (hmax : ∀ w, count w ≤ m) :
    Felicitous count (count ⁻¹' {m})ᶜ := by
  refine ⟨Iio m, inferInstance, ?_⟩
  ext w
  have := hmax w
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, mem_Iio]
  omega

theorem felicitous_denial (m : ℕ) :
    Felicitous (· ∈ count ⁻¹' {m}) (count ⁻¹' {m})ᶜ :=
  felicitous_of_polar Setoid.polar_decides.compl

end SoltWaldon2019
