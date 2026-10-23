module

public import Linglib.Core.Order.Atoms
public import Linglib.Semantics.Focus.Marking

/-!
# Cartner et al. 2026: subject islands do not reduce to discourse function

Cartner et al. argue against information-structural accounts of the subject island. On the
Focus Background Constraint of Abeillé et al. a subject island is a clash between a focused
filler and a backgrounded extraction domain, so the effect should appear where the filler is
focused and not otherwise: in wh-questions but not in relative clauses or topicalization, whose
fillers are not focused. Three factorial acceptability experiments in Sprouse's design find the
effect in all three constructions and at comparable magnitude, which no reading of the
constraint accommodates. The constraint compares the filler and the extraction domain on one
scale, a backgrounded constituent being an unfocused one, so both statuses are a `Focus.Mark`.
Its gradient statement, (44) of Abeillé et al., makes focus monotone along containment: the more
focused an element, the more focused the constituent it is part of. The revision of Winckel et
al., the paper's (11), states it as the strict inequality, an extracted element being no more
focused than its governor (`FBCPredictsIsland`), and on binary marks the categorical constraint,
the paper's (10), is that inequality (`fbcViolation_iff_lt`).

The design holds the extraction domain constant and varies the filler, so it bears only on
accounts that read the filler. An account whose prediction is a function of the domain alone,
such as the direct backgroundedness of Cuneo and Goldberg or a structural constraint on the
configuration, predicts the same verdict in every construction and is untouched by the result, as
the paper notes (§8). Direct backgroundedness is not the constraint with a different filler: its
foregrounded constituents include topics, which the Focus Background Constraint counts as
backgrounded, and it assumes that every filler-gap construction foregrounds a constituent (p. 4),
so it reads the domain alone.

## Main definitions

* `FGDConstruction`, `fillerFocus`, `subjectFocus` — the three constructions, the filler's focus,
  which the design manipulates, and the subject's, which it holds fixed
* `FBCViolation` — the categorical constraint (10)
* `FBCPredictsIsland` — the constraint's prediction, the filler more focused than the subject

## Main results

* `fbcViolation_iff_lt` — on binary marks the categorical constraint is the strict inequality
* `fbc_predicts_construction_dependence` — the constraint makes the effect turn on construction
* `fbc_falsified` — an effect in relative clauses refutes it, in either formulation
* `domain_only_predicts_invariance` — an account reading only the domain predicts invariance, so
  the experiments leave it standing

## References

* [cartner-et-al-2026]
* [abeille-et-al-2020]
* [winckel-et-al-2025]
* [cuneo-goldberg-2023]
* [sprouse-2007]
* [sprouse-et-al-2012]
-/

@[expose] public section

namespace CartnerEtAl2026

open Focus (Mark)

/-! ### Filler-gap constructions and their information structure -/

/-- The three filler-gap constructions the experiments compare. They share the movement
mechanism and differ in the information-structural status of the filler. -/
inductive FGDConstruction where
  | whQuestion
  | relativeClause
  | topicalization
  deriving DecidableEq, Repr

/-- The focus marking of the filler. A wh-phrase is focused, a topicalized constituent is
already backgrounded in the discourse (§2), and relativization assigns its head no focus
([abeille-et-al-2020]). -/
def fillerFocus : FGDConstruction → Mark
  | .whQuestion => .focused
  | .relativeClause | .topicalization => .unfeatured

/-- Focus marking of the subject, the constituent containing the gap. Subjects are backgrounded,
that is unfocused, in all three constructions, which is what the design holds constant. -/
def subjectFocus : FGDConstruction → Mark
  | _ => .unfeatured

theorem subjectFocus_uniform (c c' : FGDConstruction) : subjectFocus c = subjectFocus c' := rfl

theorem fillerFocus_varies :
    fillerFocus .whQuestion ≠ fillerFocus .relativeClause ∧
      fillerFocus .whQuestion ≠ fillerFocus .topicalization := by
  decide

/-! ### The Focus Background Constraint -/

/-- The categorical Focus Background Constraint of [abeille-et-al-2020], the paper's (10): a
focused element should not be part of an unfocused, backgrounded constituent. -/
def FBCViolation (filler domain : Mark) : Prop :=
  filler = .focused ∧ domain = .unfeatured

instance : DecidableRel FBCViolation := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- On binary marks the categorical constraint is the strict inequality of (11). -/
theorem fbcViolation_iff_lt (filler domain : Mark) : FBCViolation filler domain ↔ domain < filler :=
  (IsSimpleOrder.lt_iff_eq_bot_and_eq_top.trans and_comm).symm

/-- The constraint predicts an island in a construction whose filler is strictly more focused
than the subject containing its gap, against the monotonicity of [abeille-et-al-2020]'s (44) and
the revision (11). -/
def FBCPredictsIsland (c : FGDConstruction) : Prop :=
  subjectFocus c < fillerFocus c

instance : DecidablePred FBCPredictsIsland :=
  fun _ ↦ inferInstanceAs (Decidable (_ < _))

theorem fbcPredictsIsland_iff (c : FGDConstruction) :
    FBCPredictsIsland c ↔ FBCViolation (fillerFocus c) (subjectFocus c) :=
  (fbcViolation_iff_lt _ _).symm

/-- The constraint makes the island effect turn on the construction: present in wh-questions,
absent in relative clauses and topicalization. -/
theorem fbc_predicts_construction_dependence :
    FBCPredictsIsland .whQuestion ∧ ¬ FBCPredictsIsland .relativeClause ∧
      ¬ FBCPredictsIsland .topicalization := by
  decide

/-! ### What the experiments show

All three experiments find a super-additive penalty for sub-extraction from a subject, and the
cross-constructional analysis puts the three penalties at comparable magnitude with overlapping
95% HPDIs (§7). Taking `Island` to be the effect's distribution over constructions, the finding is
that it holds of a construction whose filler is not focused. -/

/-- An island effect in relative clauses refutes the Focus Background Constraint, in either
formulation (`fbcPredictsIsland_iff`), which ties the effect to a focused filler. -/
theorem fbc_falsified (Island : FGDConstruction → Prop)
    (hfbc : ∀ c, Island c ↔ FBCPredictsIsland c) (h : Island .relativeClause) : False :=
  fbc_predicts_construction_dependence.2.1 ((hfbc _).1 h)

/-- The limit of the result. An account whose prediction reads only the extraction domain gives
the same verdict in every construction, since the design holds the domain fixed — so
construction-invariant effects are what it predicts, and the experiments do not bear on it. -/
theorem domain_only_predicts_invariance (P : Mark → Prop) (c c' : FGDConstruction) :
    P (subjectFocus c) ↔ P (subjectFocus c') := Iff.rfl

end CartnerEtAl2026
