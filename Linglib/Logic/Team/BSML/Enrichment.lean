module

public import Linglib.Logic.Team.BSML.Properties

/-!
# Pragmatic enrichment in BSML

This file defines the pragmatic enrichment `[·]⁺` of a BSML formula and proves how it
interacts with support, negation and the variant BSML*. Enrichment conjoins the
non-emptiness atom `NE` to every subformula, so a team supports an enriched formula only
when each subformula is witnessed by a non-empty team. Aloni introduces it to model the
neglect-zero tendency, the disposition of language users to disregard models that verify a
sentence through an empty witness, and derives the free-choice inferences of
`Studies/Aloni2022.lean` from it. BSML⁺ is BSML with enrichment applied globally, and
BSML* is BSML with the empty team removed from the possible states.

## Main definitions

* `BSML.enrich`: the enrichment function `[·]⁺`.
* `BSML.ConsequencePlus`: BSML⁺ consequence, consequence between the enriched formulas.

## Main results

* `BSML.eval_of_eval_enrich`: on `NE`-free formulas enrichment strengthens in both
  polarities (Fact 1); `BSML.support_conj_ne_of_support_enrich` is `[α]⁺ ⊨ α ∧ NE`
  (Fact 2).
* `BSML.antiSupport_enrich_iff`: on positive formulas enrichment is vacuous under a single
  negation (Fact 9).
* `BSML.support_neg_enrich_neg_iff`, `BSML.not_equivalent_neg_neg_enrich`: under a
  double negation it is not (Fact 10).
* `BSML.consequenceStar_iff_consequencePlus`: BSML* and BSML⁺ consequence coincide on
  classical positive formulas (Fact 13).
* `BSML.negativeFC_star_poss`, `BSML.negativeFC_star_nec`: BSML* validates negative free
  choice (Fact 14); its failure in BSML⁺ is proved in the study.

## Implementation notes

Aloni defines `[·]⁺` on the `NE`-free fragment only. `enrich` is total and sends `NE` to
itself, and `□` abbreviates `¬◇¬`, so it has no clause of its own. Fact 1 is one induction over
the polarity parameter of `BSML.eval`, which is the paper's double induction.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

variable {W : Type*} [DecidableEq W] {Atom : Type*} {M : KripkeModel W Atom}
  {φ ψ : Formula Atom} {t : Finset W} {pol : Bool}

/-! ### Enrichment -/

/-- The pragmatic enrichment `[φ]⁺` conjoins `NE` to every subformula of `φ`. -/
def enrich : Formula Atom → Formula Atom
  | .atom p => .conj (.atom p) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg (enrich φ)) .ne
  | .conj φ ψ => .conj (.conj (enrich φ) (enrich ψ)) .ne
  | .disj φ ψ => .conj (.disj (enrich φ) (enrich ψ)) .ne
  | .poss φ => .conj (.poss (enrich φ)) .ne

theorem nonempty_of_support_enrich (h : support M (enrich φ) t) : t.Nonempty := by
  cases φ with
  | ne => exact h
  | _ => exact h.2

theorem antiSupport_conj_ne (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.conj φ .ne) t ↔ antiSupport M φ t where
  mp := fun ⟨_, h, _, h₂, hu⟩ ↦ by
    obtain rfl : _ = (∅ : Finset W) := h₂
    simpa [← hu] using h
  mpr h := ⟨t, h, ∅, rfl, Finset.union_empty t⟩

theorem support_enrich_neg_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (enrich (.neg (.neg φ))) t ↔ support M (enrich φ) t where
  mp h := (antiSupport_conj_ne M _ t).mp h.1
  mpr h := ⟨(antiSupport_conj_ne M _ t).mpr h, nonempty_of_support_enrich h⟩

/-! ### Enrichment strengthens (Facts 1 and 2) -/

/-- Enrichment strengthens an `NE`-free formula in both polarities (Fact 1). -/
theorem eval_of_eval_enrich (hNE : φ.NEFree) (h : eval M pol (enrich φ) t) :
    eval M pol φ t := by
  induction φ generalizing pol t with
  | ne => exact hNE.elim
  | atom p =>
    cases pol
    · exact (antiSupport_conj_ne M _ t).mp h
    · exact h.1
  | neg ψ ih =>
    cases pol
    · exact ih (pol := true) hNE ((antiSupport_conj_ne M _ t).mp h)
    · exact ih (pol := false) hNE h.1
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases pol
    · obtain ⟨s₁, h₁, s₂, h₂, hs⟩ := (antiSupport_conj_ne M _ t).mp h
      exact ⟨s₁, ih₁ hNE.1 h₁, s₂, ih₂ hNE.2 h₂, hs⟩
    · exact ⟨ih₁ hNE.1 h.1.1, ih₂ hNE.2 h.1.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases pol
    · obtain ⟨h₁, h₂⟩ := (antiSupport_conj_ne M _ t).mp h
      exact ⟨ih₁ hNE.1 h₁, ih₂ hNE.2 h₂⟩
    · obtain ⟨s₁, h₁, s₂, h₂, hs⟩ := h.1
      exact ⟨s₁, ih₁ hNE.1 h₁, s₂, ih₂ hNE.2 h₂, hs⟩
  | poss ψ ih =>
    cases pol
    · exact fun w hw ↦ ih hNE ((antiSupport_conj_ne M _ t).mp h w hw)
    · exact fun w hw ↦ (h.1 w hw).imp fun _ ⟨hs, hne, h'⟩ ↦ ⟨hs, hne, ih hNE h'⟩

/-- `[α]⁺ ⊨ α` for `NE`-free `α`, the support half of Fact 1. -/
theorem support_of_support_enrich (hNE : φ.NEFree) (h : support M (enrich φ) t) :
    support M φ t :=
  eval_of_eval_enrich hNE h

/-- The anti-support half of Fact 1. -/
theorem antiSupport_of_antiSupport_enrich (hNE : φ.NEFree) (h : antiSupport M (enrich φ) t) :
    antiSupport M φ t :=
  eval_of_eval_enrich hNE h

/-- `[α]⁺ ⊨ α ∧ NE` for `NE`-free `α` (Fact 2). -/
theorem support_conj_ne_of_support_enrich (hNE : φ.NEFree) (h : support M (enrich φ) t) :
    support M (.conj φ .ne) t :=
  ⟨support_of_support_enrich hNE h, nonempty_of_support_enrich h⟩

/-! ### Enrichment under negation (Facts 9 and 10) -/

/-- Enrichment is vacuous under a single negation, `¬[α]⁺ ≡ ¬α`, for positive `α`
(Fact 9). -/
theorem antiSupport_enrich_iff (hPos : φ.Positive) :
    antiSupport M (enrich φ) t ↔ antiSupport M φ t := by
  induction φ generalizing t with
  | atom p => exact antiSupport_conj_ne M _ t
  | ne => exact Iff.rfl
  | neg _ => exact hPos.elim
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    rw [enrich, antiSupport_conj_ne]
    exact exists_congr fun _ ↦ and_congr (ih₁ hPos.1)
      (exists_congr fun _ ↦ and_congr_left fun _ ↦ ih₂ hPos.2)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    rw [enrich, antiSupport_conj_ne]
    exact and_congr (ih₁ hPos.1) (ih₂ hPos.2)
  | poss ψ ih =>
    rw [enrich, antiSupport_conj_ne]
    exact forall₂_congr fun _ _ ↦ ih hPos

/-- `¬[¬φ]⁺ ≡ ¬¬[φ]⁺`, the equivalence half of Fact 10. -/
theorem support_neg_enrich_neg_iff (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg (enrich (.neg φ))) t ↔ support M (.neg (.neg (enrich φ))) t :=
  antiSupport_conj_ne M _ t

/-- Enrichment is not vacuous under a double negation, `¬¬[α]⁺ ≢ ¬¬α` for `NE`-free `α`
(Fact 10). The empty team supports `¬¬α` but not `¬¬[α]⁺`. -/
theorem not_equivalent_neg_neg_enrich (hNE : φ.NEFree) :
    ¬ Equivalent (W := W) (.neg (.neg (enrich φ))) (.neg (.neg φ)) := fun h ↦
  have h₀ := (h ⟨fun _ ↦ ∅, fun _ _ ↦ false⟩ ∅).mpr
    (support_empty_of_neFree (φ := .neg (.neg φ)) hNE _)
  (nonempty_of_support_enrich (φ := φ) h₀).ne_empty rfl

/-! ### BSML⁺ and BSML* (Facts 13 and 14) -/

/-- BSML⁺ consequence is consequence between the enriched formulas,
`α ⊨⁺ β iff [α]⁺ ⊨ [β]⁺`. -/
def ConsequencePlus (φ ψ : Formula Atom) : Prop :=
  Consequence (W := W) (enrich φ) (enrich ψ)

theorem support_enrich_iff_supportStar (hNE : φ.NEFree) (hPos : φ.Positive) :
    support M (enrich φ) t ↔ supportStar M φ t ∧ t.Nonempty := by
  induction φ generalizing t with
  | ne => exact hNE.elim
  | neg _ => exact hPos.elim
  | atom _ => exact Iff.rfl
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have ih₁ := ih₁ (t := t) hNE.1 hPos.1
    have ih₂ := ih₂ (t := t) hNE.2 hPos.2
    exact ⟨fun ⟨⟨h₁, h₂⟩, hne⟩ ↦ ⟨⟨(ih₁.mp h₁).1, (ih₂.mp h₂).1⟩, hne⟩,
      fun ⟨⟨h₁, h₂⟩, hne⟩ ↦ ⟨⟨ih₁.mpr ⟨h₁, hne⟩, ih₂.mpr ⟨h₂, hne⟩⟩, hne⟩⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have e₁ : {s | support M (enrich ψ₁) s} = {s | supportStar M ψ₁ s} ∩ Team.ne :=
      Set.ext fun _ ↦ ih₁ hNE.1 hPos.1
    have e₂ : {s | support M (enrich ψ₂) s} = {s | supportStar M ψ₂ s} ∩ Team.ne :=
      Set.ext fun _ ↦ ih₂ hNE.2 hPos.2
    change t ∈ Team.tensor _ _ ∧ t.Nonempty ↔ _
    rw [e₁, e₂]
    exact Iff.rfl
  | poss ψ ih =>
    have ih := fun s ↦ ih (t := s) hNE hPos
    exact ⟨fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨hs, hs', h'⟩ ↦
          ⟨hs, hs', ((ih _).mp h').1⟩, hne⟩,
      fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨hs, hs', h'⟩ ↦
          ⟨hs, hs', (ih _).mpr ⟨h', hs'⟩⟩, hne⟩⟩

/-- BSML* and BSML⁺ consequence coincide on classical positive formulas (Fact 13). Excluding
the empty team from the states and excluding it syntactically through `[·]⁺` agree. -/
theorem consequenceStar_iff_consequencePlus (hφ : φ.NEFree) (hφ' : φ.Positive)
    (hψ : ψ.NEFree) (hψ' : ψ.Positive) :
    ConsequenceStar (W := W) φ ψ ↔ ConsequencePlus (W := W) φ ψ where
  mp h M t h' :=
    have ⟨hs, hne⟩ := (support_enrich_iff_supportStar hφ hφ').mp h'
    (support_enrich_iff_supportStar hψ hψ').mpr ⟨h M t hne hs, hne⟩
  mpr h M t hne hs :=
    ((support_enrich_iff_supportStar hψ hψ').mp
      (h M t ((support_enrich_iff_supportStar hφ hφ').mpr ⟨hs, hne⟩))).1

/-- Negative free choice holds in BSML*, `◇¬(α ∧ β) ⊨* ◇¬α` (Fact 14). A BSML* anti-support
split of `α ∧ β` has two non-empty parts, and the part anti-supporting `α` is the witness. -/
theorem negativeFC_star_poss (α β : Formula Atom) :
    ConsequenceStar (W := W) (.poss (.neg (.conj α β))) (.poss (.neg α)) :=
  fun _ _ _ h w hw ↦
    have ⟨_, hs, _, s₁, ⟨h₁, hne₁⟩, _, _, hu⟩ := h w hw
    ⟨s₁, (hu ▸ Finset.subset_union_left).trans hs, hne₁, h₁⟩

/-- The `□` form of negative free choice in BSML*, `¬□(α ∧ β) ⊨* ¬□α` (Fact 14), by the
duality `□φ := ¬◇¬φ`. -/
theorem negativeFC_star_nec (α β : Formula Atom) :
    ConsequenceStar (W := W) (.neg (Formula.nec (.conj α β))) (.neg (Formula.nec α)) :=
  negativeFC_star_poss α β

end BSML
