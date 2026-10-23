module

public import Linglib.Syntax.Minimalist.Ellipsis

/-!
# Benz and Salzmann 2025: N-stranding NP-ellipsis in German

This file formalizes the argument of [benz-salzmann-2025] that German has N-stranding
NP-ellipsis. [liptak-saab-2014] take the absence of such ellipsis in Spanish as evidence that the
noun does not leave NP: a postnominal PP cannot be recovered in *Juan habló con tres estudiantes de
física y yo hablé con dos*. Benz and Salzmann observe that in those examples the numeral is
contrastive and the noun is not; make the noun contrastive and recovery becomes possible in German,
English and Spanish alike. The [E] feature can then sit on n, deleting only NP while the noun
survives in its raised position — the nominal counterpart of V-stranding VP-ellipsis.

The nominal spine is `Minimalist.Ellipsis.nominalSpine`, N, n, Num and D, whose sites include the
adjunction site of NP for prenominal modifiers beside the heads: that distinction is what the
paper's evidence against deleting individual constituents turns on.

## Main definitions

* `nStrandingNPE`, `numPEllipsis`: [E] on n and on D, beside the substrate's
  `Minimalist.Ellipsis.nPEllipsis`, [E] on Num.
* `ePositionOfContrast`: the contrast condition on [E] placement.

## Main results

* `n_stranding_is_xStranding`: N-to-n movement instantiates X-stranding.
* `no_individual_prenominal_deletion`, `no_individual_numeral_deletion`: no [E] position deletes a
  prenominal modifier while sparing the noun.
* `postnominal_all_or_nothing`: the only [E] position recovering a postnominal dependent deletes
  every one of them.
* `contrast_governs_recovery`: a postnominal dependent is recoverable exactly when the noun is
  contrastive.
* `gender_parallels_voice`: the categorizer is external under N-stranding as Voice is under VPE.

## References

* [benz-salzmann-2025]
* [liptak-saab-2014]
* [merchant-2001]
* [merchant-2013]
-/

@[expose] public section

namespace BenzSalzmann2025

open Minimalist Minimalist.Ellipsis

/-! ### [E] positions on the nominal spine -/

/-- N-stranding NP-ellipsis: [E] on n, deleting NP alone. The noun survives in its raised
position, and prenominal modifiers, being outside n's complement, survive with it. -/
def nStrandingNPE : Ellipsis nominalSpine := ⟨.n⟩

/-- NumP-ellipsis: [E] on D, leaving only the determiner. -/
def numPEllipsis : Ellipsis nominalSpine := ⟨.D⟩

/-! ### N-stranding -/

/-- N-to-n movement is X-stranding, so [E] on n deletes NP and spares the moved noun (§1.1). -/
theorem n_stranding_is_xStranding :
    ¬ nominalSpine.Deletes .n (.head .n) ∧ nominalSpine.Deletes .n (.head .N) :=
  ⟨nominalSpine.not_deletes_head_self _, by decide⟩

theorem clausal_nominal_parallel :
    clausalSpine.Deletes .v (.head .V) ∧ nominalSpine.Deletes .n (.head .N) := by decide

/-- Under N-stranding the noun's dependents are deleted while n, the numeral and the determiner are
pronounced, as in *zwei Professoren* (6a). -/
theorem nStranding_domain :
    nStrandingNPE.Deletes (.head .N) ∧ nStrandingNPE.Spares (.adjunct .N) ∧
      nStrandingNPE.Spares (.head .n) ∧ nStrandingNPE.Spares (.head .Num) ∧
      nStrandingNPE.Spares (.head .D) := by decide

/-! ### Against deleting individual constituents -/

/-- No [E] position deletes a prenominal modifier while sparing the noun, so (25a) lacks the
elided-adjective reading. -/
theorem no_individual_prenominal_deletion {p : Cat} (h : nominalSpine.Deletes p (.adjunct .N)) :
    nominalSpine.Deletes p (.head .N) :=
  let ⟨_, he, hN⟩ := h
  (nominalSpine.below_prefix he).subset hN

/-- The same holds for numerals, since only [E] on D puts Num in the deletion domain, and that
deletes the noun too ((25b)). -/
theorem no_individual_numeral_deletion {p : Cat} (h : nominalSpine.Deletes p (.head .Num)) :
    nominalSpine.Deletes p (.head .N) :=
  (nominalSpine.below_prefix h).subset (by decide : .N ∈ nominalSpine.below .Num)

/-- Deleting the noun deletes its whole complement, so one postnominal modifier cannot be elided
while another is pronounced ((28a), (28b)). -/
theorem postnominal_all_or_nothing (e : Ellipsis nominalSpine) (h : e.Deletes (.head .N)) :
    ∀ d, d = .N ∨ d ∈ nominalSpine.below .N → e.Deletes (.head d) := by
  rintro d (rfl | hd)
  · exact h
  · simp [nominalSpine, ClauseSpine.below] at hd

/-! ### The contrast condition -/

/-- [E] sits on n when the noun is contrastive and higher when it is not (§2.1, motivated by
(27)). -/
def ePositionOfContrast (nounContrastive : Bool) : Ellipsis nominalSpine :=
  if nounContrastive then nStrandingNPE else nPEllipsis

/-- A postnominal dependent is recoverable iff the noun is contrastive, which distinguishes (6a)
from Spanish (5) and (26b) from (27). -/
theorem contrast_governs_recovery (b : Bool) :
    (ePositionOfContrast b).Deletes (.head .N) ∧
      ((ePositionOfContrast b).Spares (.head .n) ↔ b = true) := by
  cases b <;> exact ⟨by decide, by decide⟩

/-! ### Ellipsis height and mismatches -/

theorem german_smaller_domain_than_spanish :
    nStrandingNPE.Spares (.adjunct .N) ∧ nPEllipsis.Deletes (.adjunct .N) ∧
      nStrandingNPE.Spares (.head .n) ∧ nPEllipsis.Deletes (.head .n) := by decide

/-- Gender on n survives N-stranding but not nP-ellipsis, as Voice survives VP-ellipsis but not
sluicing (§3). -/
theorem gender_parallels_voice :
    nStrandingNPE.Spares (.head .n) ∧ nPEllipsis.Deletes (.head .n) ∧
      vpEllipsis.Tolerates .voice ∧ ¬ sluicing.Tolerates .voice := by decide

end BenzSalzmann2025
