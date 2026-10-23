module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Cophonology theory

A *cophonology* is a morpheme-specific constraint ranking: in Cophonology Theory
([inkelas-zoll-2007]), individual triggers override parts of the default phonological
grammar, and the surface form is the optimal candidate under the trigger's ranking
rather than the default one. The constraint-merge mechanics are a single apparatus;
what varies across the theory family is the *trigger*:

* *per Vocabulary Item* ([sande-jenks-2017]; [rolle-2018] Ch 4): the inserted VI's
  R component is the subranking — the `subranking` argument to `cophonologicalEval`;
* *per ph(r)ase* ([sande-jenks-inkelas-2020]): a spell-out phase (vP, CP, DP) carries
  the subranking and activates it over its whole complement at spell-out, deriving
  cross-word morphologically conditioned effects.

## Main definitions

* `mergeRanking`: place a subranking's constraints above the default ranking,
  preserving the relative order of the rest.
* `cophonologicalEval`: OT evaluation under the merged ranking. With an empty
  subranking it is standard OT evaluation (`cophonologicalEval_empty_sub`): CPT
  properly generalizes OT.

## Implementation notes

Syntactic reference stays indirect: syntax selects which cophonology fires, but the
cophonology itself contains no syntactic vocabulary — [newell-2008]-style cyclic phase
phonology without violating modularity.

The substrate implements neither bracket erasure ([kiparsky-1982]) nor DM PF discharge
([embick-noyer-2007]) — rival theories of the syntax–phonology interface that
[sande-clem-dabkowski-2026] §6.2 argues against; it makes the CPT view expressible
without forcing it on consumers. The phasal trigger has no formalization yet;
`Studies/Rolle2018.lean` consumes the per-VI one (dominant grammatical tone).
-/

@[expose] public section

namespace OptimalityTheory.Cophonology

variable {L C : Type*}

section Eval

variable [DecidableEq L]

/-! ### Ranking merge -/

/-- Merge a morpheme-specific subranking with the default ranking: the subranking's
constraints first (in the order given), then the default constraints whose labels do
not appear in it — the trigger promotes its constraints without disturbing the
relative order of the rest. -/
def mergeRanking (default sub : List (L × Constraint C)) :
    List (L × Constraint C) :=
  let subLabels := sub.map (·.1)
  sub ++ default.filter (fun c ↦ !subLabels.contains c.1)

theorem mergeRanking_empty_sub (default : List (L × Constraint C)) :
    mergeRanking default [] = default := by
  simp [mergeRanking]

/-! ### Cophonological evaluation -/

/-- Cophonological evaluation takes the optimal candidates under the default ranking merged
with the trigger's subranking. -/
def cophonologicalEval
    (defaultRanking subranking : List (L × Constraint C)) (candidates : Finset C) : Finset C :=
  (Tableau.ofList candidates ((mergeRanking defaultRanking subranking).map (·.2))).optimal

/-- With an empty subranking, cophonological evaluation reduces to standard OT
evaluation: CPT is a proper generalization of OT. -/
theorem cophonologicalEval_empty_sub
    (defaultRanking : List (L × Constraint C)) (candidates : Finset C) :
    cophonologicalEval defaultRanking [] candidates
      = (Tableau.ofList candidates (defaultRanking.map (·.2))).optimal := by
  rw [cophonologicalEval, mergeRanking_empty_sub]

end Eval

end OptimalityTheory.Cophonology
