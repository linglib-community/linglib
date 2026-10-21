module

public import Linglib.Syntax.Category.Coordinator
public import Linglib.Fragments.Dargwa.Tanti.FocusParticles

/-!
# Tanti Dargwa coordinators

Clause coordination is not typical of Tanti Dargwa, which combines clauses mainly by
subordination with non-finite verb forms, as Sumbatova describes. Noun phrases are conjoined
with the additive enclitic *=ra* 'also, too' after each coordinand. Disjunction repeats the free
word *ja* before each alternative, which with negation gives 'neither … nor', and the enclitic
*=nu* marks contrast or cause.

## Main definitions

* `Dargwa.Tanti.Coordination.ra`, `Dargwa.Tanti.Coordination.ja`, `Dargwa.Tanti.Coordination.nu`:
  the additive enclitic that conjoins, the disjunctive coordinator and the contrastive enclitic.

## Main results

* `Dargwa.Tanti.Coordination.isAlsoAdditive_ra`: the coordinator *=ra* is the additive particle.

## References

* [sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.Tanti.Coordination

/-- *=ra* 'and', enclitic on each coordinand. -/
def ra : Coordinator :=
  { morph := .encl "ra", gloss := "and", role := .conjunctive }

/-- *ja* 'or', repeated before each alternative. -/
def ja : Coordinator :=
  { morph := .free "ja", gloss := "or", role := .disjunctive }

/-- *=nu* 'but; because', enclitic. -/
def nu : Coordinator :=
  { morph := .encl "nu", gloss := "but; because", role := .adversative }

/-- The coordinator *=ra* is the additive particle *=ra*. -/
theorem isAlsoAdditive_ra : ra.IsAlsoAdditive FocusParticles.ra := rfl

end Dargwa.Tanti.Coordination
