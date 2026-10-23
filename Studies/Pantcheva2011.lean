module

public import Linglib.Morphology.Paradigm.Contiguity
public import Linglib.Semantics.Events.Path

/-!
# Pantcheva (2011): Decomposing Path

This file formalizes the syncretism typology of the ninth chapter of Pantcheva's thesis. The
directional heads Place, Goal, Source, and Route form the containment sequence of
`Spatial.Path.Direction`, and a syncretism pattern over the four is a paradigm over that sequence
(`Pattern`). Two constraints restrict the patterns: the *ABA generalization of Bobaljik (then
circulating in manuscript), on which a syncretism targets only adjacent heads of the sequence,
the same contiguity that governs nominal case in Caha's analysis (`IsContiguous`);
and *A&¬A, on which Goal and Source never share a
marker, because the Source head is the locus of a reversal of the Goal path (§5.4), so one
marker for both would be contradictory (`GoalSourceMerged`, `goalSource_disjoint`).
Together they say exactly that no syncretism crosses the seam between Goal and Source
(`possible_iff_respectsSeam`), which cuts the fifteen set-partitions of the four roles to the
four attested patterns, Types 1 to 4 of Table 9.2: Place and Goal may merge, Source and Route
may merge, and nothing else (`possible_syncretisms`). Seven of the eleven excluded patterns
fall to *ABA and the other four to *A&¬A, Table 9.3 (`aba_excluded`, `ana_excluded`). The
containment itself is visible where the Source marker contains the Goal marker, as in
Imbabura Quechua *-man* against *-man-da* (Table 4.2, `source_contains_goal`), and Georgian
instantiates Type 3, with Location and Goal syncretic (Table 9.1, `georgian_loc_goal_possible`).

## Implementation notes

The patterns are restricted-growth strings over the four positions, one representative per
set-partition; the seam characterization is proved for every pattern, and the enumerations
are its corollaries. The attested lexicalization patterns of §9.3.1 are described in prose.

## References

* [pantcheva-2011]
* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Pantcheva2011

open Morphology

/-- A syncretism pattern assigns form-class indices to the four path roles, in containment order
Place, Goal, Source, Route, as the four-cell instance of `Morphology.Paradigm`. -/
abbrev Pattern := Paradigm 4 ℕ

/-- The fifteen syncretism patterns up to relabeling are the restricted-growth strings over four
positions, one per set-partition of the four roles. -/
def allPatterns : List Pattern :=
  [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2],
   ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1],
   ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]

/-- Goal and Source share a form class, which *A&¬A forbids. -/
def GoalSourceMerged (p : Pattern) : Prop := p 1 = p 2

instance (p : Pattern) : Decidable (GoalSourceMerged p) := inferInstanceAs (Decidable (_ = _))

/-- A pattern is possible iff it is contiguous, *ABA, and keeps Goal distinct from Source,
*A&¬A. -/
def Possible (p : Pattern) : Prop := IsContiguous p ∧ ¬ GoalSourceMerged p

instance (p : Pattern) : Decidable (Possible p) := inferInstanceAs (Decidable (_ ∧ _))

/-- A pattern respects the seam when no form class straddles Goal and Source: cells that share
a form lie on the same side of the seam. -/
def RespectsSeam (p : Pattern) : Prop := ∀ i j, p i = p j → (i ≤ 1 ↔ j ≤ 1)

private theorem ne_of_seam {p : Pattern} (hc : IsContiguous p) (hgs : ¬ GoalSourceMerged p)
    {i j : Fin 4} (hi : i ≤ 1) (hj : 2 ≤ j) : p i ≠ p j := λ h =>
  hgs ((hc hi (le_trans (by decide) hj) h).symm.trans (hc (le_trans hi (by decide)) hj h))

theorem possible_iff_respectsSeam (p : Pattern) : Possible p ↔ RespectsSeam p := by
  constructor
  · rintro ⟨hc, hgs⟩ i j h
    constructor
    · intro hi; by_contra hj
      exact ne_of_seam hc hgs hi (by omega) h
    · intro hj; by_contra hi
      exact ne_of_seam hc hgs hj (by omega) h.symm
  · intro hs
    refine ⟨λ i j k hij hjk hik => ?_, λ h => by simpa using hs 1 2 h⟩
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · have hs' := hs i k hik
      have hjk' : j = k := by
        by_cases hi : i ≤ 1
        · have := hs'.mp hi; omega
        · have : ¬ k ≤ 1 := λ hk => hi (hs'.mpr hk); omega
      subst hjk'; exact hik

/-- Of the fifteen patterns, exactly four respect the seam, Types 1 to 4 of Table 9.2, with all
roles distinct (English), Place=Goal (Georgian), Source=Route, and both. -/
theorem possible_syncretisms :
    allPatterns.filter (λ p => Possible p) =
      [![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 2, 2], ![0, 1, 2, 3]] := by
  decide

/-- *ABA excludes seven patterns, Types 5 to 11 of Table 9.3, each a syncretism spanning
non-adjacent roles. -/
theorem aba_excluded :
    allPatterns.filter (λ p => ¬ IsContiguous p) =
      [![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0],
       ![0, 1, 2, 0], ![0, 1, 2, 1]] := by
  decide

/-- *A&¬A alone, the constraint peculiar to the directional domain, excludes four contiguous
patterns, Types 12 to 15 of Table 9.3. -/
theorem ana_excluded :
    allPatterns.filter (λ p => IsContiguous p ∧ GoalSourceMerged p) =
      [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 1, 1, 1], ![0, 1, 1, 2]] := by
  decide

/-! ### Morphological containment (Table 4.2)

The Source structure contains the Goal structure, visible where the Source marker contains the
Goal marker, as in Quechua *-man* against *-man-da*, the shell containment of
`Spatial.Path.Direction`. -/

theorem source_contains_goal :
    Spatial.Path.Direction.place.shells ⊂ Spatial.Path.Direction.goal.shells ∧
      Spatial.Path.Direction.goal.shells ⊂ Spatial.Path.Direction.source.shells ∧
      Spatial.Path.Direction.source.shells ⊂ Spatial.Path.Direction.route.shells := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Georgian's Location=Goal syncretism (Table 9.1) is Type 3. -/
theorem georgian_loc_goal_possible : Possible ![0, 0, 1, 2] := by decide

/-! ### The semantic ground of *A&¬A (§5.4) -/

theorem goalSource_disjoint {ι α : Type*} [LinearOrder ι] [BoundedOrder ι] (R : Set α)
    (γ : ι → α) : Spatial.Path.IsCofinal R γ → ¬ Spatial.Path.IsCoinitial R γ :=
  Spatial.Path.IsCofinal.not_isCoinitial

/-- A path from outside a place into it is cofinal and not coinitial, and its reverse is
coinitial. -/
example : let p : Spatial.Path ℕ := ⟨0, [1]⟩
    Spatial.Path.IsCofinal {1} p ∧ ¬ Spatial.Path.IsCoinitial {1} p ∧
      Spatial.Path.IsCoinitial {1} p.reverse := by
  intro p
  have h : Spatial.Path.IsCofinal {1} p := by
    refine ⟨fun a b hab ha ↦ ?_, by decide, by decide⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    revert a b; decide
  exact ⟨h, h.not_isCoinitial,
    (Spatial.Path.hasShape_reverse p (d := (id : ℕ → ℕ)) (s := .coinitial)).2 h⟩

end Pantcheva2011
