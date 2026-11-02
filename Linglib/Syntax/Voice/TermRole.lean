module

public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Transitivity-related roles

This file defines the roles of nominal terms in Creissels' binary core-term system: S, A and P
for the core terms of intransitive and transitive constructions, and X for an oblique. A role is
a property of a term in a construction, so the coding slots of a voice's two constructions can
give one participant different roles. The map from the comparative coding slots reads recipients
and themes as P-like core terms.

## References

* [creissels-2024]
-/

@[expose] public section

namespace Voice

/-- The role of a nominal term in [creissels-2024]'s binary core-term system is one of the
core roles S, A and P, or X for an oblique. -/
inductive TermRole where
  /-- The sole core term of an intransitive clause. -/
  | S
  /-- The agent-like core term of a transitive clause. -/
  | A
  /-- The patient-like core term of a transitive clause. -/
  | P
  /-- An oblique. -/
  | X
  deriving DecidableEq, Repr

/-- The transitivity-related role of a comparative coding role, under which recipients and
themes are P-like core terms. -/
def TermRole.ofArgumentRole : ArgumentRole → TermRole
  | .S => .S
  | .A => .A
  | .P | .R | .T => .P

end Voice
