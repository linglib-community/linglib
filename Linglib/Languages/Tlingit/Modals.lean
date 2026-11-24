module

public import Linglib.Semantics.Modality.Typology

/-!
# Tlingit modals

The Tlingit (Athabaskan-Eyak-Tlingit, ISO 639-3 `tli`) expressions with a dedicated modal
meaning, as Cable describes them: the dubitative particles *gwál*, *gíwé* and *shákdé*,
expressing epistemic possibility, and two inflectional modes of the verb, the potential mode,
expressing circumstantial possibility, and the future mode, expressing circumstantial necessity.
Each mode is realized by a combination of prefixes and a stem suffix.

## Implementation notes

* An entry's meaning is the categories Cable finds positive evidence that it expresses. The
  *tlél aadé … yé* construction, which expresses the negation of circumstantial possibility,
  has no entry, nor do the expressions speakers use to convey deontic modality without
  encoding it.
* The modes' entries carry the mode's name as form.

## References

* [cable-2017]
-/

@[expose] public section

namespace Tlingit

open Modality

/-- The dubitative particle *gwál* 'perhaps', expressing epistemic possibility. -/
def gwál : ModalItem := { form := "gwál", meaning := {(.possibility, .epistemic)} }

/-- The dubitative particle *gíwé* 'perhaps, I guess', which does not imply likelihood,
expressing epistemic possibility. -/
def gíwé : ModalItem := { form := "gíwé", meaning := {(.possibility, .epistemic)} }

/-- The dubitative particle *shákdé* 'perhaps, probably', which implies likelihood, expressing
epistemic possibility. -/
def shákdé : ModalItem := { form := "shákdé", meaning := {(.possibility, .epistemic)} }

/-- The future mode of the verb, expressing circumstantial necessity. -/
def futureMode : ModalItem :=
  { form := "future mode", meaning := {(.necessity, .circumstantial)} }

/-- The potential mode of the verb, expressing circumstantial possibility. -/
def potentialMode : ModalItem :=
  { form := "potential mode", meaning := {(.possibility, .circumstantial)} }

/-- The expressions with a dedicated modal meaning. -/
def modals : List ModalItem := [gwál, gíwé, shákdé, futureMode, potentialMode]

end Tlingit
