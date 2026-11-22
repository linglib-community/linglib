module

public import Linglib.Data.Statistics.Schema

/-!
# Eckardt2006: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Eckardt2006.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The contexts in which the Old French negation particles are found in a positive sense without *ne*,
summarized from dictionaries, text collections and the secondary literature on Old French. A blank
cell records that the sources consulted have no such use, not that it was impossible.

## References

* [eckardt-2006]
-/

@[expose] public section

namespace Eckardt2006

open Data.Statistics

/-- The French negation particles. -/
inductive Particle where
  /-- mie: 'crumb' -/
  | mie
  /-- goutte: 'drop' -/
  | goutte
  /-- point: 'point' -/
  | point
  /-- rien: 'thing' -/
  | rien
  /-- personne: 'person' -/
  | personne
  /-- pas: 'step' -/
  | pas
  deriving DecidableEq, Repr, Fintype

/-- The contexts of Table 4. -/
inductive Context where
  /-- embedded under negation, under negative verbs: a clause embedded under a negation or a
  negative verb -/
  | negation
  /-- under sans (without): the complement of *sans* -/
  | sans
  /-- in rhetorical questions: a rhetorical question -/
  | rhetoricalQuestion
  /-- in questions: a question -/
  | question
  /-- in indirect questions: an indirect question -/
  | indirectQuestion
  /-- antecedent of a conditional: the antecedent of a conditional -/
  | conditional
  /-- comparatives: a comparative -/
  | comparative
  /-- various other 'downward-entailing' contexts: other downward-entailing contexts -/
  | other
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 4: the particles found in a positive sense in a context. -/
structure PositiveUse where
  /-- The particles the table lists for it. -/
  particles : List Particle
  deriving DecidableEq, Repr

/-- The cells of Table 4, by context; counted in a corpus; checked against the page images. -/
def positiveUses : Context → PositiveUse
  | .negation => ⟨[.mie, .goutte, .point, .rien, .personne, .pas]⟩
  | .sans => ⟨[.goutte, .point, .rien, .personne]⟩
  | .rhetoricalQuestion => ⟨[.mie, .point, .rien, .personne, .pas]⟩
  | .question => ⟨[.mie, .point, .rien, .personne]⟩
  | .indirectQuestion => ⟨[.mie, .goutte, .point, .rien, .personne]⟩
  | .conditional => ⟨[.mie, .point, .rien, .personne]⟩
  | .comparative => ⟨[.mie, .point, .personne]⟩
  | .other => ⟨[.goutte, .point, .rien, .personne]⟩

end Eckardt2006
