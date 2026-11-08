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
* `BSML.Formula.denStar`, `BSML.ConsequenceStar`: meaning and consequence in BSML*.

## Main results

* `BSML.den_enrich_subset`: on `NE`-free formulas enrichment strengthens in both
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
both components of the meaning, which is the paper's double induction. Aloni defines BSML* only
by removing `∅` from the possible states; `Formula.denStar` reads this as non-empty splits and
keeps the modal clauses of BSML, under which `R[w]` may still be empty.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
-/

@[expose] public section

open scoped SetFamily

namespace BSML

open ModalLogic (KripkeModel PointedTeam)
open Team (TeamProperty)
open scoped Bilattice

variable {W : Type*} [DecidableEq W] {Atom : Type*} {M : KripkeModel W Atom}
  {φ ψ : Formula Atom} {t : Finset W}

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

/-- Enrichment strengthens an `NE`-free formula in both polarities: every team that supports or
anti-supports `[φ]⁺` supports or anti-supports `φ` (Fact 1). -/
theorem den_enrich_subset (hNE : φ.NEFree) :
    ((enrich φ).den M).pro ⊆ (φ.den M).pro ∧ ((enrich φ).den M).con ⊆ (φ.den M).con := by
  induction φ with
  | ne => exact hNE.elim
  | atom p => exact ⟨fun _ h ↦ h.1, fun t h ↦ (antiSupport_conj_ne M _ t).mp h⟩
  | neg ψ ih =>
    exact ⟨fun _ h ↦ (ih hNE).2 h.1, fun t h ↦ (ih hNE).1 ((antiSupport_conj_ne M _ t).mp h)⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    refine ⟨fun _ h ↦ ⟨(ih₁ hNE.1).1 h.1.1, (ih₂ hNE.2).1 h.1.2⟩, fun t h ↦ ?_⟩
    obtain ⟨s₁, h₁, s₂, h₂, hs⟩ := (antiSupport_conj_ne M _ t).mp h
    exact ⟨s₁, (ih₁ hNE.1).2 h₁, s₂, (ih₂ hNE.2).2 h₂, hs⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    refine ⟨fun _ h ↦ ?_, fun t h ↦ ?_⟩
    · obtain ⟨s₁, h₁, s₂, h₂, hs⟩ := h.1
      exact ⟨s₁, (ih₁ hNE.1).1 h₁, s₂, (ih₂ hNE.2).1 h₂, hs⟩
    · obtain ⟨h₁, h₂⟩ := (antiSupport_conj_ne M _ t).mp h
      exact ⟨(ih₁ hNE.1).2 h₁, (ih₂ hNE.2).2 h₂⟩
  | poss ψ ih =>
    exact ⟨fun _ h w hw ↦ (h.1 w hw).imp fun _ ⟨⟨h', hne⟩, hs⟩ ↦ ⟨⟨(ih hNE).1 h', hne⟩, hs⟩,
      fun t h w hw ↦ (ih hNE).2 ((antiSupport_conj_ne M _ t).mp h w hw)⟩

/-- `[α]⁺ ⊨ α` for `NE`-free `α`, the support half of Fact 1. -/
theorem support_of_support_enrich (hNE : φ.NEFree) (h : support M (enrich φ) t) :
    support M φ t :=
  (den_enrich_subset hNE).1 h

/-- The anti-support half of Fact 1. -/
theorem antiSupport_of_antiSupport_enrich (hNE : φ.NEFree) (h : antiSupport M (enrich φ) t) :
    antiSupport M φ t :=
  (den_enrich_subset hNE).2 h

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
    ¬ Equivalent (.neg (.neg (enrich φ))) (.neg (.neg φ)) := fun h ↦
  have h₀ := (h ⟨Unit, ⟨fun _ ↦ ∅, fun _ _ ↦ False⟩, ∅⟩).mpr
    (support_empty_of_neFree (φ := .neg (.neg φ)) hNE _)
  (nonempty_of_support_enrich (φ := φ) h₀).ne_empty rfl

/-! ### BSML⁺ and BSML* (Facts 13 and 14) -/

/-- BSML⁺ consequence is consequence between the enriched formulas,
`α ⊨⁺ β iff [α]⁺ ⊨ [β]⁺`. -/
def ConsequencePlus (φ ψ : Formula Atom) : Prop :=
  {enrich φ} ⊨ enrich ψ

/-- The meaning of a formula in BSML*, where `∅` is not among the possible states
([aloni-2022] §6.3.1): each part of a split is non-empty, and the other clauses are those of
`Formula.den`. -/
def Formula.denStar (M : KripkeModel W Atom) : Formula Atom → TeamProperty W ⊙ TeamProperty W
  | .atom p => Team.flatPair (M.val p)
  | .ne => .mk Team.ne {∅}
  | .neg φ => (φ.denStar M)ᶜ
  | .conj φ ψ => .mk ((φ.denStar M).pro ∩ (ψ.denStar M).pro)
      (((φ.denStar M).con ∩ Team.ne) ⊻ ((ψ.denStar M).con ∩ Team.ne))
  | .disj φ ψ => .mk (((φ.denStar M).pro ∩ Team.ne) ⊻ ((ψ.denStar M).pro ∩ Team.ne))
      ((φ.denStar M).con ∩ (ψ.denStar M).con)
  | .poss φ => (φ.denStar M).map (Team.poss M.access) (Team.nec M.access)

/-- BSML* support. -/
abbrev supportStar (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.denStar M).pro

/-- In BSML*, `ψ` is a consequence of `φ` when every pointed team model with a non-empty team
supporting `φ` supports `ψ`. -/
def ConsequenceStar (φ ψ : Formula Atom) : Prop :=
  ∀ p : PointedTeam.{0} Atom, p.team.Nonempty → supportStar p.model φ p.team →
    supportStar p.model ψ p.team

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
    have e₁ : ((enrich ψ₁).den M).pro = (ψ₁.denStar M).pro ∩ Team.ne :=
      Set.ext fun _ ↦ ih₁ hNE.1 hPos.1
    have e₂ : ((enrich ψ₂).den M).pro = (ψ₂.denStar M).pro ∩ Team.ne :=
      Set.ext fun _ ↦ ih₂ hNE.2 hPos.2
    change t ∈ (Team.disj _ _).pro ∧ t.Nonempty ↔ _
    rw [Team.pro_disj, e₁, e₂]
    exact Iff.rfl
  | poss ψ ih =>
    have ih := fun s ↦ ih (t := s) hNE hPos
    exact ⟨fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨⟨h', hs'⟩, hs⟩ ↦
          ⟨⟨((ih _).mp h').1, hs'⟩, hs⟩, hne⟩,
      fun ⟨h, hne⟩ ↦ ⟨fun w hw ↦ (h w hw).imp fun _ ⟨⟨h', hs'⟩, hs⟩ ↦
          ⟨⟨(ih _).mpr ⟨h', hs'⟩, hs'⟩, hs⟩, hne⟩⟩

/-- BSML* and BSML⁺ consequence coincide on classical positive formulas (Fact 13). Excluding
the empty team from the states and excluding it syntactically through `[·]⁺` agree. -/
theorem consequenceStar_iff_consequencePlus (hφ : φ.NEFree) (hφ' : φ.Positive)
    (hψ : ψ.NEFree) (hψ' : ψ.Positive) :
    ConsequenceStar φ ψ ↔ ConsequencePlus φ ψ := by
  rw [ConsequencePlus, consequence_singleton_iff]
  exact ⟨fun h p h' ↦
      have ⟨hs, hne⟩ := (support_enrich_iff_supportStar hφ hφ').mp h'
      (support_enrich_iff_supportStar hψ hψ').mpr ⟨h p hne hs, hne⟩,
    fun h p hne hs ↦ ((support_enrich_iff_supportStar hψ hψ').mp
      (h p ((support_enrich_iff_supportStar hφ hφ').mpr ⟨hs, hne⟩))).1⟩

/-- Negative free choice holds in BSML*, `◇¬(α ∧ β) ⊨* ◇¬α` (Fact 14). -/
theorem negativeFC_star_poss (α β : Formula Atom) :
    ConsequenceStar (Atom := Atom) (.poss (.neg (.conj α β))) (.poss (.neg α)) :=
  fun _ _ h w hw ↦
    have ⟨_, ⟨⟨s₁, ⟨h₁, hne₁⟩, _, _, hu⟩, _⟩, hs⟩ := h w hw
    ⟨s₁, ⟨h₁, hne₁⟩, (le_sup_left.trans_eq hu).trans hs⟩

/-- The `□` form of negative free choice in BSML*, `¬□(α ∧ β) ⊨* ¬□α` (Fact 14), by the
duality `□φ := ¬◇¬φ`. -/
theorem negativeFC_star_nec (α β : Formula Atom) :
    ConsequenceStar (Atom := Atom) (.neg (Formula.nec (.conj α β))) (.neg (Formula.nec α)) :=
  negativeFC_star_poss α β

end BSML
