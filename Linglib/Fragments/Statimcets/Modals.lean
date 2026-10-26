module

public import Linglib.Semantics.Modality.Typology
public import Linglib.Semantics.Evidential.Defs

/-!
# St'át'imcets (Lillooet Salish) Modal Inventory

[rullmann-matthewson-davis-2008] [matthewson-2016]

St'át'imcets (ISO 639-3 `lil`, also known as Lillooet) modal system. The deontic enclitic
*=ka* expresses permission or obligation and the circumfix *ka-...-a* ability
([matthewson-2005]); the epistemic clitics are evidentials, *k'a* requiring indirect
inferential evidence, *ku7* a report, and *lákw7a* sensory non-visual evidence, and only
*lákw7a* is compatible with the speaker's disbelief of the prejacent ([matthewson-2016]
§18.2.4, (25)–(28)). The modals are variable in force ([rullmann-matthewson-davis-2008]).

| Form       | Type        | Flavour        | Force            | Source              |
|-----------|-------------|----------------|------------------|---------------------|
| =ka       | enclitic    | deontic        | poss + nec       |                     |
| ka-...-a  | circumfix   | circumstantial | possibility      |                     |
| k'a       | clitic      | epistemic      | poss + nec       | inference           |
| ku7       | clitic      | epistemic      | poss + nec       | report              |
| lákw7a    | clitic      | epistemic      | poss + nec       | sensory, non-visual |
-/

@[expose] public section

namespace Statimcets

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-! ## Modal expressions -/

/-- Deontic enclitic: variable force (permission or obligation).
    [matthewson-2016] example 1:
    - *wá7=ka s-lep' i=k'ún7=a ku=pála7 máqa7*
      'The eggs can/have to stay in the ground for a year.' -/
def ka : ModalItem := { form := "=ka", meaning := {pd, nd} }

/-- Ability circumfix: fixed possibility force, circumstantial flavour.
    [matthewson-2005]:
    - *ka-xílh-ts-tal'í-ha* 'could do it the fastest' -/
def kaCircumfix : ModalItem := { form := "ka-...-a", meaning := {pc} }

/-- The inferential evidential *k'a*, a variable-force epistemic modal requiring indirect
inferential evidence ([rullmann-matthewson-davis-2008]). -/
def kaInfer : ModalItem := { form := "k'a", meaning := {pe, ne} }

/-- The reportative evidential *ku7*, a variable-force epistemic modal requiring a report
([rullmann-matthewson-davis-2008]). -/
def ku7 : ModalItem := { form := "ku7", meaning := {pe, ne} }

/-- The sensory non-visual evidential *lákw7a*, an epistemic modal requiring sensory
non-visual evidence ([matthewson-2016] §18.2.4). -/
-- UNVERIFIED: its force; both forces are recorded on the pattern of the other clitics.
def lakw7a : ModalItem := { form := "lákw7a", meaning := {pe, ne} }

def modals : List ModalItem := [ka, kaCircumfix, kaInfer, ku7, lakw7a]

/-! ## Information source -/

/-- The information source an evidential modal requires; `none` for the non-evidentials. -/
def source (m : ModalItem) : Option Evidential.EvidenceType :=
  if m = kaInfer then some .inferring else if m = ku7 then some .reported
  else if m = lakw7a then some .attested else none

end Statimcets
