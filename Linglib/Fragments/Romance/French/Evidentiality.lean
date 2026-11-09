module

public import Linglib.Semantics.Evidential.Defs

/-!
# French evidentiality

French has no evidentials proper. Its conditional has an evidential extension, the conditional
of uncertain information frequent in newspaper reports, which marks information as taken from
another source that the speaker does not vouch for. The conditional's other meanings, future in
the past, hypothesis and counterfactual, make this use an evidentiality strategy.

## References

* [aikhenvald-2004]
-/

@[expose] public section

namespace French.Evidentiality

/-- French has no evidentials proper. -/
def evidentials : List Evidential := []

/-- The conditional in its reportative use, cited by its third singular ending, as in
*aurait*. -/
def conditional : Evidential := { morphs := [.suff "rait"], covers := {.hearsay, .quotative} }

/-- The evidentiality strategies. -/
def strategies : List Evidential := [conditional]

end French.Evidentiality
