module

public import Linglib.Semantics.Modality.Typology

/-!
# Nez Perce modals

The modal vocabulary of Nez Perce (Sahaptian, ISO 639-3 `nez`) as [deal-2011] §2 surveys it,
divided into epistemic and nonepistemic expressions. The nonepistemic ones are the productive
verbal suffix *o'qa*, with deontic, pure circumstantial and counterfactual readings; the
participial construction in *-(n/t)e's* with a copula, expressing a circumstantial possibility
akin to English *-able* and teleological modality; and the unproductive suffix *'ax̂*, which the
speakers who have it judge equivalent to *o'qa*. The epistemic ones are particles, *o'qa* never
being epistemic.

## Implementation notes

* Counterfactual and teleological readings count as circumstantial, the library's flavours
  drawing no finer line.
* A modal's meaning records its uses in upward-entailing contexts, *o'qa*'s spanning both
  forces as Gitksan *ima('a)*'s do.
* Of the epistemic particles only *pay's* and *páalwit* 'maybe' are entered. *'éete* 'surely,
  I guess', glossed as inferential, co-occurs with *pay's* for 'maybe', and *ku'(nu) weet*
  'dunno whether' is an ignorance marker with the yes/no particle; neither has a settled force.

## References

* [deal-2011]
-/

@[expose] public section

namespace NezPerce

open Modality (ModalItem)

/-! ### Nonepistemic modals -/

/-- The suffix *o'qa* (allomorphs *yo'qa*, *no'qa*), read deontically, pure circumstantially
and counterfactually, never epistemically or teleologically ([deal-2011] §2.2–2.6). It is used
where English uses a possibility modal and where it uses a necessity modal ([deal-2011] §1),
though only as a possibility modal outside upward-entailing contexts ([deal-2011] §3). -/
def oqa : ModalItem :=
  { form := "o'qa", meaning := {.possibility, .necessity} ×ˢ {.deontic, .circumstantial} }

/-- The participial construction, the deverbalizing suffix *-(n/t)e's* with a copula: a
circumstantial possibility akin to English *-able*, and teleological modality, never deontic or
counterfactual ([deal-2011] §2.6). -/
def participialEs : ModalItem :=
  { form := "-(n/t)e's", meaning := {.possibility} ×ˢ {.circumstantial} }

/-- The suffix *'ax̂*, no longer productive, which the speakers who have it judge essentially
equivalent to *o'qa* in meaning ([deal-2011] §2.6). -/
def ax : ModalItem := { form := "'ax̂", meaning := oqa.meaning }

/-! ### Epistemic particles -/

/-- The particle *pay's* 'maybe' ([deal-2011] §2.5). -/
def pays : ModalItem := { form := "pay's", meaning := {.possibility} ×ˢ {.epistemic} }

/-- The particle *páalwit* 'maybe, perhaps' ([deal-2011] §2.5). -/
def paalwit : ModalItem := { form := "páalwit", meaning := {.possibility} ×ˢ {.epistemic} }

/-- The modals [deal-2011] §2 surveys. -/
def modals : List ModalItem := [oqa, participialEs, ax, pays, paalwit]

end NezPerce
