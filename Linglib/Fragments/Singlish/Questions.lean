module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Singlish questions

Colloquial Singapore English forms a content question three interchangeable ways: full
wh-movement (*What you think Natalie is baking at 3am ah?*), partial movement to an intermediate
Spec-CP (*You think what Natalie is baking at 3am ah?*), and wh-in-situ (*You think Natalie is
baking what at 3am ah?*), with do-support optional and the clause-final particle *ah* keeping an
in-situ question from an echo reading.

## References

* [sato-2013]
* [chan-shen-2026]
-/

@[expose] public section

namespace Singlish.Questions

/-- *ah*: the clause-final particle that blocks the echo reading of a wh-in-situ question. -/
def ah : Particle where
  form := "ah"
  position := some .clauseFinal
  distribution := fun c e ↦ match c, e with
    | .constituent, .matrix => some .optional
    | _, _ => none

end Singlish.Questions
