module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Data.Examples.Wang2023

/-!
# Wang (2023): Honorifics without [HON]

Across Wang's survey the values recruited for honorific pronouns are plural number, third
person and indefiniteness, never singular, first or second person, or definites (Table 1, (28)).
These are the semantically unmarked values, the ones carrying the weakest presupposition (54)–(56),
which the feature bundles order by specification. Recruitment follows from the Taboo of
Directness (57), which in respect contexts demands the weakest presupposition, ranked above Heim's
Maximize Presupposition! (59), which demands the strongest. Number systems with a dual (80) also
need a weak taboo that avoids only the strongest presupposition (82), and the four attested
patterns of honorific nonsingulars are the rankings of (83).

## Main results

* `tod_mp_general`: Taboo » MP! selects the least specified cell alone, so no honorific singular,
  local person or definite arises.
* `stod_mp_wtod`, `wtod_mp_stod`, `wtod_alone`: the rankings of (83) give honorific plural only,
  dual only, and the non-escalating systems.

## Implementation notes

The cells are the number bundles `Number.Features`, singular, dual and plural being the most, the
intermediate and the least specified, the lower sets of the chain minimal < atomic; person and
definiteness bundles have the same shape. The constraints count violations by the size of a
bundle, the taboo as the size itself and MP! as its shortfall from the full bundle. The ternary
tableaux are decided by the kernel. The paper's examples are the rows of
`Data.Examples.Wang2023`.

## TODO

* MP! (59) chooses the strongest presupposition compatible with what is assumed, a condition at
  the context, while `mpConstraint` counts a bundle's shortfall from the full bundle. On the lower
  sets of the chain the two agree when every stronger bundle is compatible, the shortfall being
  the number of strictly stronger competitors; deriving the constraint from
  `Competition.unblocked` over `Number.dom` waits on the dual's minimality domain, which
  `Number.dom` does not yet restrict.

## References

* [wang-r-2023]
* [heim-1991]
* [harbour-2016]
* [sauerland-2003]
-/

@[expose] public section

namespace Wang2023

open OptimalityTheory

/-! ### The recruited values are the least specified cells (§4.1) -/

/-- The plural is the least specified number cell, the empty bundle (54). -/
theorem plural_eq_bot : Number.pluralF = ⊥ := rfl

/-- The third person is the least specified person cell, the empty bundle (55). -/
theorem third_eq_bot : Person.toFeatures .third = ⊥ := Person.toFeatures_third

/-! ### The Taboo of Directness and Maximize Presupposition! (§4.2) -/

/-- The Taboo of Directness (57) asks in respect contexts for the form with the weakest
presupposition; as a constraint it penalizes presuppositional strength. -/
def todConstraint : Constraint Number.Features := Finset.card

/-- Maximize Presupposition! (59) asks for the form with the strongest presupposition; as a
constraint it penalizes the shortfall from the maximal strength. -/
def mpConstraint : Constraint Number.Features :=
  fun c ↦ Fintype.card Number.Feature - c.card

/-- The two maxims order well-formed cells oppositely. -/
theorem todConstraint_lt_iff (c₁ c₂ : Number.Features) :
    todConstraint c₁ < todConstraint c₂ ↔ mpConstraint c₂ < mpConstraint c₁ := by
  have := Finset.card_le_univ c₁
  have := Finset.card_le_univ c₂
  simp only [todConstraint, mpConstraint]
  omega

/-- A candidate with violations of the top constraint loses to one without. -/
theorem not_mem_optimal_of_top_pos {C : Type*} [DecidableEq C] {candidates : List C}
    {top : Constraint C} {rest : List (Constraint C)} {h : candidates ≠ []} {c c₀ : C}
    (hc₀ : c₀ ∈ candidates) (h0 : top c₀ = 0) (hc : 0 < top c) :
    c ∉ (Tableau.ofRanking candidates (top :: rest) h).optimal :=
  fun hmem ↦ hc.ne' (Tableau.ofRanking_optimal_zero_first top rest ⟨c₀, hc₀, h0⟩ hmem)

/-- Under Taboo » MP! every optimal candidate is the least specified cell. -/
theorem tod_mp_only_minimal (candidates : List Number.Features)
    (hWF : ∀ c ∈ candidates, IsLowerSet (↑c : Set Number.Feature))
    (hMin : Number.pluralF ∈ candidates)
    (hNE : candidates ≠ []) :
    ∀ c ∈ (Tableau.ofRanking candidates [todConstraint, mpConstraint] hNE).optimal,
      c = Number.pluralF := by
  intro c hc
  have hZero := Tableau.ofRanking_optimal_zero_first todConstraint [mpConstraint]
    ⟨Number.pluralF, hMin, rfl⟩ hc
  have hcWF := hWF c (Tableau.ofRanking_optimal_mem hc)
  rcases hcWF.eq_empty_or_eq_Iic with rfl | ⟨a, rfl⟩
  · rfl
  · cases a <;> exact absurd hZero (by decide)

/-- The least specified cell is optimal under Taboo » MP!, its profile being lexicographically
least. -/
theorem tod_mp_minimal_mem_optimal (candidates : List Number.Features)
    (hMin : Number.pluralF ∈ candidates) (hNE : candidates ≠ []) :
    Number.pluralF ∈
      (Tableau.ofRanking candidates [todConstraint, mpConstraint] hNE).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hMin, fun c' _ ↦ ?_⟩
  simp only [Tableau.ofRanking]
  apply not_lt.mp
  intro ⟨i, hlt_eq, hlt⟩
  change ([todConstraint, mpConstraint].get i) c' <
    ([todConstraint, mpConstraint].get i) Number.pluralF at hlt
  match i with
  | ⟨0, _⟩ =>
    simp only [List.get, todConstraint] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | ⟨1, _⟩ =>
    have hc'_tod : todConstraint c' = 0 := by
      have := hlt_eq ⟨0, Nat.zero_lt_succ _⟩
        (show (⟨0, _⟩ : Fin 2) < ⟨1, _⟩ from Nat.zero_lt_one)
      exact this
    have hc'_mp : mpConstraint c' = 2 := by
      simp only [mpConstraint, todConstraint] at hc'_tod ⊢
      rw [hc'_tod]; rfl
    simp only [List.get] at hlt
    change mpConstraint c' < mpConstraint Number.pluralF at hlt
    rw [hc'_mp] at hlt
    exact lt_irrefl _ hlt

/-- Taboo » MP! selects the least specified cell alone from any well-formed candidate set
that contains it: the emergence of the semantically unmarked. -/
theorem tod_mp_general (candidates : List Number.Features)
    (hWF : ∀ c ∈ candidates, IsLowerSet (↑c : Set Number.Feature))
    (hMin : Number.pluralF ∈ candidates)
    (hNE : candidates ≠ []) :
    (Tableau.ofRanking candidates [todConstraint, mpConstraint] hNE).optimal =
      {Number.pluralF} := by
  ext c
  simp only [Finset.mem_singleton]
  exact ⟨tod_mp_only_minimal candidates hWF hMin hNE c,
    fun h ↦ h ▸ tod_mp_minimal_mem_optimal candidates hMin hNE⟩

/-- With the taboo on top, the most specified cell, singular, local person or definite, is never
optimal beside a less specified competitor, so these honorifics are unattested (28). -/
theorem maximal_not_optimal_of_tod_top (candidates : List Number.Features)
    (rest : List (Constraint Number.Features)) (hNE : candidates ≠ [])
    (hMin : Number.pluralF ∈ candidates) :
    Number.singularF ∉
      (Tableau.ofRanking candidates (todConstraint :: rest) hNE).optimal :=
  not_mem_optimal_of_top_pos hMin rfl (by decide)

/-! ### Articulated number systems (§5) -/

/-- The weak Taboo of Directness (82b) avoids the form with the strongest presupposition. -/
def wtodConstraint : Constraint Number.Features :=
  fun c ↦ if c.card = Fintype.card Number.Feature then 1 else 0

/-- The singular, dual and plural of an articulated number system (80). -/
def number : List Number.Features := [Number.singularF, Number.dualF, Number.pluralF]

/-- The weak taboo alone also excludes the most specified cell. -/
theorem maximal_not_optimal_of_wtod_top (candidates : List Number.Features)
    (rest : List (Constraint Number.Features)) (hNE : candidates ≠ [])
    (hMin : Number.pluralF ∈ candidates) :
    Number.singularF ∉
      (Tableau.ofRanking candidates (wtodConstraint :: rest) hNE).optimal :=
  not_mem_optimal_of_top_pos hMin rfl (by decide)

/-- Strong taboo » MP! » weak taboo recruits the plural only, as in Slovenian (83b). -/
theorem stod_mp_wtod :
    (Tableau.ofRanking number [todConstraint, mpConstraint, wtodConstraint]).optimal =
      {Number.pluralF} := by
  decide +kernel

/-- Weak taboo » MP! » strong taboo recruits the dual only, as in Mwotlap and Kharia (83a). -/
theorem wtod_mp_stod :
    (Tableau.ofRanking number [wtodConstraint, mpConstraint, todConstraint]).optimal =
      {Number.dualF} := by
  decide +kernel

/-- The weak taboo alone leaves dual and plural, the non-escalating system of Imere (83d). -/
theorem wtod_alone :
    (Tableau.ofRanking number [wtodConstraint]).optimal =
      {Number.dualF, Number.pluralF} := by
  decide +kernel

/-- Outside respect contexts MP! on top recruits the singular. -/
theorem mp_top :
    (Tableau.ofRanking number [mpConstraint, todConstraint, wtodConstraint]).optimal =
      {Number.singularF} := by
  decide +kernel

end Wang2023
