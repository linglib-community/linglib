module

public import Linglib.Logic.Team.QBSML.Defs

/-!
# Pragmatic enrichment in QBSML

This file defines the pragmatic enrichment `[·]⁺` of a QBSML formula and proves that it
strengthens `NE`-free formulas in both polarities. Enrichment conjoins the non-emptiness atom
`NE` to every subformula, quantifiers included, so a state supports an enriched formula only
when each subformula is witnessed by a non-empty state. Aloni and van Ormondt extend Aloni's
propositional enrichment to the first-order language and derive from it the ignorance,
distribution and free-choice facts proved in `Logic/Team/QBSML/FreeChoice.lean`.

## Main definitions

* `QBSML.Formula.enrich`: the enrichment function `[·]⁺`.

## Main results

* `QBSML.eval_of_eval_enrich`: enrichment strengthens an `NE`-free formula in both
  polarities, the first-order form of Aloni's Fact 1.
* `QBSML.antiSupport_conj_ne`: anti-support of `φ ∧ NE` is anti-support of `φ`.
* `QBSML.support_enrich_nec_iff`: support of the enriched derived `□φ` is enriched support of
  `φ` at every accessible lift, on a non-empty state.

## Implementation notes

The paper defines `[·]⁺` on the `NE`-free fragment only; `enrich` is total and sends `NE` to
itself. `□` is the derived `¬◇¬`, so the paper's clause `[□φ]⁺ = □[φ]⁺ ∧ NE` has no
counterpart. `support_enrich_nec_iff` shows that the derived enrichment has the same support as
that clause; their anti-supports differ on the empty state, which anti-supports the paper's
form but not the derived one. The file parallels `Logic/Team/BSML/Enrichment.lean` over the
first-order formula type.

## References

* [aloni-vanormondt-2023] Aloni and van Ormondt, Modified Numerals and Split Disjunction: The
  First-Order Case
* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
-/

@[expose] public section

namespace QBSML

variable {Var Const Pred : Type*}

/-! ### Enrichment -/

/-- The pragmatic enrichment `[φ]⁺` conjoins `NE` to every subformula of `φ`. -/
def Formula.enrich : Formula Var Const Pred → Formula Var Const Pred
  | .pred P x => .conj (.pred P x) .ne
  | .predc P c => .conj (.predc P c) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg φ.enrich) .ne
  | .conj φ ψ => .conj (.conj φ.enrich ψ.enrich) .ne
  | .disj φ ψ => .conj (.disj φ.enrich ψ.enrich) .ne
  | .poss φ => .conj (.poss φ.enrich) .ne
  | .exi x φ => .conj (.exi x φ.enrich) .ne
  | .univ x φ => .conj (.univ x φ.enrich) .ne

variable {W Domain : Type*} [DecidableEq W] [DecidableEq Var] [Fintype Var]
  [DecidableEq Domain] [Fintype Domain] {M : Model W Domain Const Pred}
  {φ : Formula Var Const Pred} {s : Finset (Index W Var Domain)} {pol : Bool}

theorem nonempty_of_support_enrich (h : support M φ.enrich s) : s.Nonempty := by
  cases φ with
  | ne => exact h
  | _ => exact h.2

/-- Only the empty state anti-supports `NE`, so anti-support of `φ ∧ NE` reduces to
anti-support of `φ`. -/
theorem antiSupport_conj_ne (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) :
    antiSupport M (.conj φ .ne) s ↔ antiSupport M φ s where
  mp := fun ⟨_, h, _, h₂, hu⟩ ↦ by
    obtain rfl : _ = (∅ : Finset (Index W Var Domain)) := h₂
    simpa [← hu] using h
  mpr h := ⟨s, h, ∅, rfl, sup_bot_eq s⟩

/-! ### Enrichment strengthens -/

/-- Enrichment strengthens an `NE`-free formula in both polarities, the first-order form of
Aloni's Fact 1. -/
theorem eval_of_eval_enrich (hNE : φ.NEFree) (h : eval M pol φ.enrich s) : eval M pol φ s := by
  induction hNE generalizing pol s with
  | pred P x =>
    cases pol
    · exact (antiSupport_conj_ne M _ s).mp h
    · exact h.1
  | predc P c =>
    cases pol
    · exact (antiSupport_conj_ne M _ s).mp h
    · exact h.1
  | neg _ ih =>
    cases pol
    · exact ih (pol := true) ((antiSupport_conj_ne M _ s).mp h)
    · exact ih (pol := false) h.1
  | conj _ _ ih₁ ih₂ =>
    cases pol
    · obtain ⟨t₁, h₁, t₂, h₂, ht⟩ := (antiSupport_conj_ne M _ s).mp h
      exact ⟨t₁, ih₁ h₁, t₂, ih₂ h₂, ht⟩
    · exact ⟨ih₁ h.1.1, ih₂ h.1.2⟩
  | disj _ _ ih₁ ih₂ =>
    cases pol
    · obtain ⟨h₁, h₂⟩ := (antiSupport_conj_ne M _ s).mp h
      exact ⟨ih₁ h₁, ih₂ h₂⟩
    · obtain ⟨t₁, h₁, t₂, h₂, ht⟩ := h.1
      exact ⟨t₁, ih₁ h₁, t₂, ih₂ h₂, ht⟩
  | poss _ ih =>
    cases pol
    · exact fun i hi ↦ ih ((antiSupport_conj_ne M _ s).mp h i hi)
    · exact fun i hi ↦ (h.1 i hi).imp fun _ ⟨hX, hne, h'⟩ ↦ ⟨hX, hne, ih h'⟩
  | exi x _ ih =>
    cases pol
    · exact ih ((antiSupport_conj_ne M _ s).mp h)
    · exact h.1.imp fun _ ⟨hS, hcov, h'⟩ ↦ ⟨hS, hcov, ih h'⟩
  | univ x _ ih =>
    cases pol
    · exact ((antiSupport_conj_ne M _ s).mp h).imp fun _ ⟨hS, hcov, h'⟩ ↦ ⟨hS, hcov, ih h'⟩
    · exact ih h.1

theorem support_of_support_enrich (hNE : φ.NEFree) (h : support M φ.enrich s) :
    support M φ s :=
  eval_of_eval_enrich hNE h

theorem antiSupport_of_antiSupport_enrich (hNE : φ.NEFree) (h : antiSupport M φ.enrich s) :
    antiSupport M φ s :=
  eval_of_eval_enrich hNE h

/-! ### The enriched derived `□` -/

/-- Support of the enriched derived `□φ` is enriched support of `φ` at every index's full
accessible lift `R(wᵢ)[gᵢ]`, on a non-empty state. -/
theorem support_enrich_nec_iff (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) :
    support M φ.nec.enrich s ↔
      (∀ i ∈ s, support M φ.enrich (State.modalLift (M.access i.world) i.assign)) ∧
        s.Nonempty :=
  and_congr_left fun _ ↦ (antiSupport_conj_ne M _ s).trans <|
    forall₂_congr fun _ _ ↦ antiSupport_conj_ne M _ _

end QBSML
