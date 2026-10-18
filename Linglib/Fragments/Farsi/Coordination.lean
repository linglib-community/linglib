module

public import Linglib.Syntax.Category.Coordinator

/-!
# Persian coordinators

Persian conjoins with the free word *va* 'and', an Arabic loan, before the second coordinand;
the colloquial form is the enclitic *o*. The additive particle *ham* 'also, too', repeated with
each coordinand, gives 'both … and'.

## Main definitions

* `Farsi.Coordination.va`, `Farsi.Coordination.ham`: the conjunctive coordinator and the
  additive particle that conjoins when repeated.

## TODO

The entries have not been checked against a grammar of Persian.
-/

@[expose] public section

namespace Farsi.Coordination

/-- *va* 'and', colloquially the enclitic *o*. -/
def va : Coordinator :=
  { morph := .free "va", gloss := "and", role := .conjunctive }

/-- *ham*, with each coordinand 'both … and', also the additive particle
`Farsi.FocusParticles.ham`. -/
def ham : Coordinator :=
  { morph := .free "ham", gloss := "and", role := .conjunctive }

end Farsi.Coordination
