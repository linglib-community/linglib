module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Catalan verbs

These are the Catalan verbs with a lexical reciprocal entry beside their transitive one, whose
reciprocal reading emerges without *es* in the environments of Palmieri's Table 2.2. They are
ordinary verb entries here, and Palmieri's list of them is `Studies/Palmieri2024.lean`.

## References

* [palmieri-2024]
-/

@[expose] public section

namespace Catalan.Verbs

/-- *abraçar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abracar : Verb where
  morphs := [.root "abraçar"]
  valency := .ofFrame ArgumentFrame.np

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  morphs := [.root "casar"]
  valency := .ofFrame ArgumentFrame.np

/-- *deixar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def deixar : Verb where
  morphs := [.root "deixar"]
  valency := .ofFrame ArgumentFrame.np

/-- *petonejar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def petonejar : Verb where
  morphs := [.root "petonejar"]
  valency := .ofFrame ArgumentFrame.np

/-- *topar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def topar : Verb where
  morphs := [.root "topar"]
  valency := .ofFrame ArgumentFrame.np

/-- *trobar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def trobar : Verb where
  morphs := [.root "trobar"]
  valency := .ofFrame ArgumentFrame.np

end Catalan.Verbs
