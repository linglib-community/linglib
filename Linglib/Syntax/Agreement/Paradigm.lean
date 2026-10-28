module

public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Order.Comparable

/-!
# Agreement paradigms

This file defines the agreement paradigm of a target, a table pairing cells, which are feature
bundles, with the exponents realizing them, and realizes a bundle such as a controller's
`HasPhi.phi` by the exponent of the most specific cell it extends.

Since cells are partial, a target reads a controller only along the dimensions its cells
specify: a verb whose cells give person and number realizes a controller bearing gender and case
too by its person and number. Syncretism is two cells with one exponent, a bundle extending no
cell has no form, and a default form is an entry whose cell is `⊥`. Each entry is a rule of
exponence applying at the bundles that extend its cell, so realization is the Elsewhere selection
of a `Morphology.Exponence.RuleSet`, and on a table of incomparable cells it is
[looking the cell up](##realize_of_mem).

## Main definitions

* `Agreement.Paradigm`: a table of cells and exponents.
* `Agreement.Paradigm.realize`: the exponent of the most specific cell a bundle extends.

## Main statements

* `Agreement.Paradigm.realize_congr`: bundles agreeing wherever some cell is specified are
  realized alike.
* `Agreement.Paradigm.realize_of_mem`: a table of incomparable cells realizes each cell by its
  own exponent.

## References

* [corbett-1998]
* [kiparsky-1973]
-/

@[expose] public section

namespace Agreement

/-- An agreement paradigm, the table of a target's cells and the exponents realizing them. -/
abbrev Paradigm (Exp : Type*) := List (Bundle × Exp)

namespace Paradigm

open Morphology.Exponence

variable {Exp : Type*} {p q : Paradigm Exp} {x y c : Bundle} {e : Exp}

/-- An entry is a rule of exponence applying at the bundles that extend its cell. -/
instance : Rule (Bundle × Exp) Bundle Exp := ⟨Prod.snd, fun e x ↦ e.1 ≤ x⟩

@[simp] theorem applies_iff {e : Bundle × Exp} : Applies e x ↔ e.1 ≤ x := Iff.rfl

instance : DecidableRel (Applies : Bundle × Exp → Bundle → Prop) :=
  fun e x ↦ inferInstanceAs (Decidable (e.1 ≤ x))

/-- The exponent realizing a bundle, that of the first of the most specific cells it extends. -/
def realize (p : Paradigm Exp) (x : Bundle) : Option Exp :=
  RuleSet.realizeMinimal p (fun e ↦ OrderDual.toDual e.1) x

/-- The cells of the paradigm, in the order of its entries. -/
def cells (p : Paradigm Exp) : List Bundle := p.map (·.1)

/-- A bundle has no form when it extends no cell, the outcome in which missing agreement
morphology makes a construction ungrammatical rather than taking a default form
([corbett-1998] p. 199). -/
theorem realize_eq_none_iff : p.realize x = none ↔ ∀ e ∈ p, ¬ e.1 ≤ x := by
  simp [realize, RuleSet.realizeMinimal_eq_none_iff, RuleSet.applicable]

/-- The exponent realizing a bundle belongs to a cell the bundle extends, and no cell the bundle
extends is more specific. -/
theorem exists_mem_of_realize_eq_some (h : p.realize x = some e) :
    ∃ c, (c, e) ∈ p ∧ c ≤ x ∧ ∀ e' ∈ p, e'.1 ≤ x → ¬ c < e'.1 := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  have hw := RuleSet.selectMinimal_isElsewhereWinner hr
  exact ⟨r.1, hw.prop.1, hw.prop.2, fun e' he' hle hlt ↦
    hlt.not_ge (hw.le_of_le (j := e') ⟨he', hle⟩ hlt.le)⟩

/-- Bundles that agree wherever some cell is specified are realized alike, so that a target
reads a controller only along the dimensions its cells specify, as in Upper Sorbian *wón je
pisał* 'he wrote' the finite verb reads the person and number of its controller and the
participle its number and gender ([corbett-1998] p. 201). -/
theorem realize_congr (h : ∀ c ∈ p.cells, ∀ d, c d ≠ ⊥ → x d = y d) :
    p.realize x = p.realize y := by
  refine RuleSet.realizeMinimal_congr (List.filter_congr fun e he ↦ decide_eq_decide.2 ?_)
  refine forall_congr' fun d ↦ ?_
  by_cases hd : e.1 d = ⊥
  · simp [hd]
  · rw [h e.1 (List.mem_map_of_mem he) d hd]

/-- In a paradigm whose cells are pairwise incomparable, as in a table of fully specified cells,
each cell is realized by its own exponent. -/
theorem realize_of_mem (hp : p.cells.Pairwise (IncompRel (· ≤ ·))) (he : (c, e) ∈ p) :
    p.realize c = some e := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 fun h ↦ realize_eq_none_iff.1 h _ he le_rfl
  obtain ⟨c', hc', hle, -⟩ := exists_mem_of_realize_eq_some hr
  obtain rfl : c' = c := by
    by_contra hne
    exact (hp.forall (List.mem_map_of_mem hc') (List.mem_map_of_mem he) hne).1 hle
  have hnd : p.cells.Nodup := hp.imp fun h hcc ↦ h.1 hcc.le
  obtain rfl : r = e := (Prod.mk.inj (List.inj_on_of_nodup_map hnd hc' he rfl)).2
  exact hr

/-- Entries appended to a paradigm leave the realization of a bundle extending none of their
cells unchanged. -/
theorem realize_append_of_forall_not_le (h : ∀ e ∈ q, ¬ e.1 ≤ x) :
    (p ++ q).realize x = p.realize x := by
  have : RuleSet.applicable (p ++ q) x = RuleSet.applicable p x := by
    simpa [RuleSet.applicable, List.filter_append] using h
  simp only [realize, RuleSet.realizeMinimal, RuleSet.selectMinimal, this]

end Paradigm

end Agreement
