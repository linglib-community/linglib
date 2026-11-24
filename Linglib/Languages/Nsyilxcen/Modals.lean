module

public import Linglib.Semantics.Modality.Typology

/-!
# Nsyilxcen modals

The epistemic modals of Nsyilxcen (Okanagan, Interior Salish, ISO 639-3 `oka`) as
[menzies-2013] describes them and [matthewson-2016] reports: *mat* is felicitous in possibility
and necessity contexts alike, while *cmay* is felicitous in possibility contexts only.

## References

* [menzies-2013]
* [matthewson-2016]
-/

@[expose] public section

namespace Nsyilxcen

open Modality

/-- The epistemic modal *mat*, felicitous in contexts supporting possibility and necessity
claims alike. -/
def mat : ModalItem := ⟨"mat", {.possibility, .necessity} ×ˢ {.epistemic}, .neutral⟩

/-- The epistemic modal *cmay*, felicitous in contexts supporting possibility claims only. -/
def cmay : ModalItem := ⟨"cmay", {.possibility} ×ˢ {.epistemic}, .neutral⟩

/-- The two epistemic modals. -/
def modals : List ModalItem := [mat, cmay]

end Nsyilxcen
