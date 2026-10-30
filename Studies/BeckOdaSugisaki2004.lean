module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Reference.Iota

/-!
# Beck, Oda and Sugisaki 2004: comparison in Japanese without degree abstraction

This file formalizes Beck, Oda and Sugisaki's analysis of Japanese *yori*-comparatives. A
*yori*-constituent denotes an individual — a free relative, or a definite built from a
relative clause — and fixes the standard `c` of a positive or contextual comparative in the
main clause, in place of the *than*-clause degree set of the standard analysis. The authors
attribute the difference to a Degree Abstraction Parameter: Japanese does not bind degree
variables in the syntax. We state both repertoires of denotations and derive from them the
paper's three empirical differences — variable acceptability, no subcomparatives of degree,
no degree-based negative islands — and its scope argument.

## Main definitions

* `er`: the comparative morpheme on degree sets, `max D₂ > max D₁`.
* `pos`: the positive form at a standard `c`; the contextual comparative is
  `Degree.MaxIn (Set.Ioi c)`.
* `theC`: the Fregean definite over a contextual domain, the denotation of a *yori*-clause.
* `erJ`: the comparative that combines directly with the adjective meaning.

Example numbers follow the journal article; the examples are typed in
`Data/Examples/BeckOdaSugisaki2004.json`.

## References

* [beck-oda-sugisaki-2004]
* [von-stechow-1984], [heim-2000]: the standard analysis and the scope argument from
  intensional verbs.
* [rullmann-1995]: negative islands as maximality failure.
* [heim-kratzer-1998]: the positive form and the Fregean definite.
* [jacobson-1995]: free relatives as maximal individuals.
* [kennedy-1997]: the comparative combining directly with the adjective.
* [ishii-1991], [snyder-wexler-das-1995]: the acceptability and subcomparative data.
-/

@[expose] public section

namespace BeckOdaSugisaki2004

open Degree Quantifier Quantifier.Det

variable {Entity D : Type*} [LinearOrder D]

/-! ### The standard analysis -/

/-- The comparative morpheme on degree sets, where `er D₁ D₂` holds iff `max D₂ > max D₁` (8). -/
def er (D₁ D₂ : Set D) : Prop :=
  ∃ m₁ m₂, IsGreatest D₁ m₁ ∧ IsGreatest D₂ m₂ ∧ m₁ < m₂

theorem er_Iic_Iic (d₁ d₂ : D) : er (Set.Iic d₁) (Set.Iic d₂) ↔ d₁ < d₂ := by
  refine ⟨fun ⟨_, _, h₁, h₂, h⟩ => ?_,
    fun h => ⟨_, _, isGreatest_Iic, isGreatest_Iic, h⟩⟩
  rwa [h₁.unique isGreatest_Iic, h₂.unique isGreatest_Iic] at h

/-! ### The contextual analysis -/

/-- The positive form at a contextual standard, where `pos μ c x` holds iff `x` is `d`-A for
some `d > c` (20). -/
def pos (μ : Entity → D) (c : D) (x : Entity) : Prop :=
  ∃ d, d ≤ μ x ∧ c < d

theorem pos_iff_lt (μ : Entity → D) (c : D) (x : Entity) : pos μ c x ↔ c < μ x :=
  ⟨fun ⟨_, hd, hc⟩ => hc.trans_le hd, fun h => ⟨_, le_rfl, h⟩⟩

theorem pos_iff_mem_over (μ : Entity → D) (c : D) (x : Entity) :
    pos μ c x ↔ x ∈ μ ⁻¹' Set.Ioi c := by
  simp only [pos_iff_lt, Set.mem_preimage, Set.mem_Ioi]

-- (23), footnote 7
theorem maxIn_Ioi_iff_of_isGreatest {S : Set D} {m : D} (h : IsGreatest S m) (c : D) :
    MaxIn (Set.Ioi c) S ↔ ∃ d ∈ S, c < d :=
  ⟨fun ⟨_, hc, h'⟩ => ⟨_, h'.1, hc⟩,
    fun ⟨_, hd, hc⟩ => ⟨m, hc.trans_le (h.2 hd), h⟩⟩

/-- On an adjective's own degree set the contextual comparative and the positive form
coincide ((24d), (21b)). -/
theorem maxIn_Ioi_Iic_iff (μ : Entity → D) (c : D) (x : Entity) :
    MaxIn (Set.Ioi c) (Set.Iic (μ x)) ↔ pos μ c x :=
  maxIn_Iic.trans (pos_iff_lt μ c x).symm

/-- A context setter supplying `y` sets `c := μ y`, and the positive form becomes the
comparison with `y` ((21), (25)). -/
theorem pos_comparedTo (μ : Entity → D) (x y : Entity) :
    pos μ (μ y) x ↔ μ y < μ x :=
  pos_iff_lt μ (μ y) x

/-! ### Yori-clauses denote individuals -/

/-- `theC C P` is the unique `P`-individual of the contextual domain `C` (54). -/
noncomputable def theC (C : Set Entity) (P : Entity → Prop) : Option Entity :=
  iota fun x => x ∈ C ∧ P x

theorem theC_eq_some_iff (C : Set Entity) (P : Entity → Prop) (y : Entity) :
    theC C P = some y ↔ (y ∈ C ∧ P y) ∧ ∀ z, z ∈ C → P z → z = y := by
  simp only [theC, iota_eq_some_iff, and_imp]

-- (41a)
theorem isGreatest_card_of_isGreatest {Atom : Type*} {P : Finset Atom → Prop}
    {Y : Finset Atom} (h : IsGreatest {S | P S} Y) :
    IsGreatest {n | ∃ S, P S ∧ n ≤ S.card} Y.card :=
  ⟨⟨Y, h.1, le_rfl⟩, fun _ ⟨_, hS, hn⟩ => hn.trans (Finset.card_le_card (h.2 hS))⟩

/-! ### Subcomparatives -/

/-- An individual standard lies on the matrix dimension, so the shelf–door sentence with the door as
standard differs from the subcomparative ((74), (79)). -/
theorem pos_ne_subcomparative :
    ∃ μ ν : Fin 2 → ℕ, ν 1 < μ 0 ∧ ¬ pos μ (μ 1) 0 :=
  ⟨![2, 3], ![0, 1], by decide, by simp [pos_iff_lt]⟩

/-! ### Negative islands -/

-- (11), (12)
theorem not_isGreatest_nobody [NoMaxOrder D] (bought : Set Entity) (μ : Entity → D) :
    ¬ ∃ m, IsGreatest (scopeDegrees (no bought) (Set.Iic ∘ μ)) m :=
  not_isGreatest_scopeDegrees (antitone_no bought) (fun _ ↦ isLowerSet_Iic _)

/-- `er` over a negated *than*-clause never holds, the negative island ((11), (87a)). -/
theorem not_er_nobody [NoMaxOrder D] (bought : Set Entity) (μ : Entity → D) (S : Set D) :
    ¬ er (scopeDegrees (no bought) (Set.Iic ∘ μ)) S :=
  fun ⟨m, _, hm, _, _⟩ => not_isGreatest_nobody bought μ ⟨m, hm⟩

/-- A *yori*-clause on the unbought individuals entails that some book in the domain went unbought
((86), (88c)). -/
theorem yori_negative_entails_unbought (C : Set Entity) (bought : Entity → Prop)
    (μ : Entity → D) (x : Entity)
    (h : ∃ y, theC C (fun z => ¬ bought z) = some y ∧ pos μ (μ y) x) :
    ∃ y ∈ C, ¬ bought y :=
  let ⟨y, hy, _⟩ := h; ⟨y, ((theC_eq_some_iff _ _ _).1 hy).1⟩

/-- A universally quantified comparative (95a) can hold when no book was read by every boy, lacking
the uniqueness presupposition of the *yori*-clause ((94), (95)). -/
theorem er_everyone_without_shared_book :
    ∃ (read : Fin 2 → Fin 3 → Prop) (μ : Fin 3 → ℕ),
      er (scopeDegrees (fun S => ∀ b, Det.some (read b) S) (Set.Iic ∘ μ)) (Set.Iic (μ 2)) ∧
        ¬ ∃ x, ∀ b, read b x := by
  refine ⟨fun b x => x.val = b.val, ![1, 1, 2],
    ⟨1, _, ⟨fun b => ?_, fun d hd => ?_⟩, isGreatest_Iic, by simp⟩, ?_⟩
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

/-! ### The main clause and scope -/

/-- The comparative on adjective meanings, where `erJ c P x` holds iff the greatest degree to
which `x` is `P` exceeds `c` (133). -/
def erJ (c : D) (P : D → Entity → Prop) (x : Entity) : Prop :=
  MaxIn (Set.Ioi c) {d | P d x}

/-- For a monotone adjective, `erJ` and the positive form have the same truth conditions
(footnote 15). -/
theorem erJ_iff_pos (μ : Entity → D) (c : D) (x : Entity) :
    erJ c (fun d x => d ≤ μ x) x ↔ pos μ c x :=
  maxIn_Ioi_Iic_iff μ c x

/-- The wide-scope reading of *need to be exactly s long*, the comparative over `need`, says
that the greatest degree reached in every acceptable world is the target `s` (136b). -/
def wideScope {W : Type*} (acc : Set W) (μ : W → D) (s : D) : Prop :=
  HighScope (MaxIn {s}) (every acc) (Set.Iic ∘ μ)

/-- The in-situ reading, which `erJ` with a differential yields, says that in every acceptable
world the greatest degree is the target `s`. -/
def inSitu {W : Type*} (acc : Set W) (μ : W → D) (s : D) : Prop :=
  LowScope (MaxIn {s}) (every acc) (Set.Iic ∘ μ)

theorem inSitu_iff {W : Type*} (acc : Set W) (μ : W → D) (s : D) :
    inSitu acc μ s ↔ ∀ w ∈ acc, μ w = s :=
  lowScope_maxIn

theorem wideScope_of_inSitu {W : Type*} {acc : Set W} {μ : W → D} {s : D}
    (hne : acc.Nonempty) (h : inSitu acc μ s) : wideScope acc μ s :=
  have h' := (inSitu_iff acc μ s).1 h
  let ⟨w₀, hw₀⟩ := hne
  highScope_every_of_lowScope ⟨w₀, hw₀, fun w hw => ((h' w₀ hw₀).trans (h' w hw).symm).le⟩ h

/-- In some model the wide-scope reading of *needs to be exactly 5 pages longer* holds and the
in-situ reading fails ((136), (138)). -/
theorem exists_wideScope_not_inSitu :
    ∃ (acc : Set (Fin 2)) (μ : Fin 2 → ℕ),
      wideScope acc μ (10 + 5) ∧ ¬ inSitu acc μ (10 + 5) := by
  refine ⟨Set.univ, ![15, 16], ⟨10 + 5, rfl, fun w _ => ?_, fun d hd => ?_⟩, ?_⟩
  · fin_cases w <;> simp
  · simpa using hd (Set.mem_univ 0)
  · rw [inSitu_iff]
    intro h
    simpa using h 1 (Set.mem_univ _)

end BeckOdaSugisaki2004
