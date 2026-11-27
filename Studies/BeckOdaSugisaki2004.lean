module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Reference.Iota

/-!
# Beck, Oda and Sugisaki 2004: comparison in Japanese without degree abstraction

On the standard analysis a *than*-clause denotes a set of degrees `S`, and the comparative says
that the degrees `T` of the main clause exceed its greatest degree, `MaxComparative .gt S T`. Beck,
Oda and Sugisaki analyse a Japanese *yori*-constituent as denoting an individual instead, the
unique individual of a contextual domain with a property, `theC`. That individual sets the
standard `c` of the positive form of the main clause, `μ ⁻¹' Set.Ioi c`, or of a comparative
that combines with the adjective directly, `Quantifier.MaxIn (Set.Ioi c)`, which is the same
predicate on an adjective with a measure (`Quantifier.maxIn_Iic`).

With the standard set by an individual `y`, the positive form is the comparative of the two
individuals' degrees, `mem_preimage_Ioi_iff_maxComparative`. The analyses come apart elsewhere.
The comparative over a negated *than*-clause never holds, since the clause has no greatest
degree, `not_maxComparative_no`, while a *yori*-clause over the unbought individuals presupposes
only that there is one, `yori_negative_entails_unbought`. A universally quantified *than*-clause
needs no single individual, `exists_maxComparative_every_not_exists`. A degree phrase can take
scope over a modal where the in-situ comparative cannot, `exists_highScope_not_lowScope`.

## Implementation notes

The paper's comparative morpheme takes the greatest degree of the main clause as well as of the
*than*-clause. `MaxComparative` asks only that some main-clause degree exceed the standard,
which is the same wherever the main clause has a greatest degree, as on every degree set here
(`maxComparative_gt_iff_maxIn`).

## References

* [beck-oda-sugisaki-2004]
* [von-stechow-1984]
* [heim-2000]
* [rullmann-1995]
* [heim-kratzer-1998]
* [jacobson-1995]
* [kennedy-1997]
* [ishii-1991]
* [snyder-wexler-das-1995]
-/

@[expose] public section

namespace BeckOdaSugisaki2004

open Quantifier Quantifier.Det Set

variable {Entity D : Type*} [LinearOrder D]

/-! ### The positive form and the comparative -/

/-- With the standard set by `y`, the positive form of `x` is the comparative of the degrees of
`x` over those of `y`. -/
theorem mem_preimage_Ioi_iff_maxComparative (μ : Entity → D) (x y : Entity) :
    x ∈ μ ⁻¹' Ioi (μ y) ↔ MaxComparative .gt (Iic (μ y)) (Iic (μ x)) :=
  maxComparative_gt_Iic_Iic.symm

/-! ### Yori-clauses denote individuals -/

/-- (54): `theC C P` is the unique `P`-individual of the contextual domain `C`. -/
noncomputable def theC (C : Set Entity) (P : Entity → Prop) : Part Entity :=
  iota {x | x ∈ C ∧ P x}

theorem mem_theC (C : Set Entity) (P : Entity → Prop) (y : Entity) :
    y ∈ theC C P ↔ (y ∈ C ∧ P y) ∧ ∀ z, z ∈ C → P z → z = y := by
  simp only [theC, mem_iota, Set.mem_ofPred_eq, and_imp]

-- (41a)
theorem isGreatest_card_of_isGreatest {Atom : Type*} {P : Finset Atom → Prop}
    {Y : Finset Atom} (h : IsGreatest {S | P S} Y) :
    IsGreatest {n | ∃ S, P S ∧ n ≤ S.card} Y.card :=
  ⟨⟨Y, h.1, le_rfl⟩, fun _ ⟨_, hS, hn⟩ ↦ hn.trans (Finset.card_le_card (h.2 hS))⟩

/-! ### Subcomparatives -/

-- (74), (79): an individual standard lies on the dimension of the main clause.
theorem exists_not_mem_preimage_Ioi :
    ∃ μ ν : Fin 2 → ℕ, ν 1 < μ 0 ∧ (0 : Fin 2) ∉ μ ⁻¹' Ioi (μ 1) :=
  ⟨![2, 3], ![0, 1], by decide, by simp⟩

/-! ### Negative islands -/

/-- The comparative over a negated *than*-clause never holds. -/
theorem not_maxComparative_no [NoMaxOrder D] (bought : Set Entity) (μ : Entity → D) (T : Set D) :
    ¬ MaxComparative .gt (scopeDegrees (no bought) (Iic ∘ μ)) T :=
  fun ⟨m, hm, _⟩ ↦
    not_isGreatest_scopeDegrees (antitone_no bought) (fun _ ↦ IsLowerSet.Iic _) ⟨m, hm⟩

/-- A *yori*-clause on the unbought individuals entails that some individual of the domain went
unbought. -/
theorem yori_negative_entails_unbought (C : Set Entity) (bought : Entity → Prop)
    (μ : Entity → D) (x : Entity)
    (h : ∃ y ∈ theC C (fun z ↦ ¬ bought z), x ∈ μ ⁻¹' Ioi (μ y)) :
    ∃ y ∈ C, ¬ bought y :=
  let ⟨y, hy, _⟩ := h; ⟨y, ((mem_theC _ _ _).1 hy).1⟩

/-- A comparative over a universally quantified *than*-clause can hold when no one individual is
shared, which a *yori*-clause would presuppose. -/
theorem exists_maxComparative_every_not_exists :
    ∃ (read : Fin 2 → Fin 3 → Prop) (μ : Fin 3 → ℕ),
      MaxComparative .gt (scopeDegrees (fun S ↦ ∀ b, Det.some {x | read b x} S) (Iic ∘ μ))
          (Iic (μ 2)) ∧ ¬ ∃ x, ∀ b, read b x := by
  refine ⟨fun b x ↦ x.val = b.val, ![1, 1, 2],
    (maxComparative_gt_iff_maxIn isGreatest_Iic).2 ⟨1, by simp, fun b ↦ ?_, fun d hd ↦ ?_⟩, ?_⟩
  · fin_cases b
    · exact ⟨0, rfl, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  · obtain ⟨x, hx, hle⟩ := hd 0
    obtain rfl : x = 0 := Fin.ext hx
    simpa using hle
  · rintro ⟨x, hx⟩
    have h0 := hx 0
    have h1 := hx 1
    simp at h0 h1
    omega

/-! ### Scope

The degree phrase *exactly `s`* of *need to be exactly `s` long* scopes over the modal,
`HighScope`, when the greatest length reached in every acceptable world is `s`, and stays in
situ, `LowScope`, when the length is `s` in every acceptable world. -/

-- (136)
theorem highScope_of_lowScope {W : Type*} {acc : Set W} {μ : W → D} {s : D}
    (hne : acc.Nonempty) (h : LowScope (MaxIn {s}) (every acc) (Iic ∘ μ)) :
    HighScope (MaxIn {s}) (every acc) (Iic ∘ μ) :=
  have h' : ∀ w ∈ acc, μ w = s := lowScope_maxIn.1 h
  let ⟨w₀, hw₀⟩ := hne
  highScope_every_of_lowScope ⟨w₀, hw₀, fun w hw ↦ ((h' w₀ hw₀).trans (h' w hw).symm).le⟩ h

/-- In some model the wide-scope reading of *needs to be exactly 5 pages longer* holds and the
in-situ reading fails. -/
theorem exists_highScope_not_lowScope :
    ∃ (acc : Set (Fin 2)) (μ : Fin 2 → ℕ), HighScope (MaxIn {10 + 5}) (every acc) (Iic ∘ μ) ∧
      ¬ LowScope (MaxIn {10 + 5}) (every acc) (Iic ∘ μ) := by
  refine ⟨Set.univ, ![15, 16], ⟨10 + 5, rfl, fun w _ ↦ ?_, fun d hd ↦ ?_⟩, ?_⟩
  · fin_cases w <;> simp
  · simpa using hd (Set.mem_univ 0)
  · rw [lowScope_maxIn]
    intro h
    simpa using h (Set.mem_univ (1 : Fin 2))

end BeckOdaSugisaki2004
