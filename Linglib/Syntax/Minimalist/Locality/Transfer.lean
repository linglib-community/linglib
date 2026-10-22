/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Locality.Chain

/-!
# Transfer and the Phase Impenetrability Condition

Transfer seals the domain of a phase head, so that an operation at a later stage cannot inspect it:
the Phase Impenetrability Condition is the effect of Transfer on the search space. A stage is the
root of the object built so far, a position of the finished object, and a cut assigns to each stage
the positions sealed by then. A phase head's domain is its complement, or the whole phase short of
its root, transferred once the phase is complete or once the next phase head merges; a deleted
phase head passes its phasehood to the head of its complement. A position reaches its phase level
when the phase of the lowest phase head whose complement contains it is complete.

## Main definitions

* `Minimalist.Cut`: the positions sealed at each stage.
* `Minimalist.complementDomain`, `Minimalist.wholePhaseDomain`: transfer domains.
* `Minimalist.Pic1`, `Minimalist.Pic2`: when a phase head's domain is transferred.
* `Minimalist.sealed`: the positions the transferred domains seal.
* `Minimalist.phaseLevel`: the stage at which a position reaches its phase level.
* `Minimalist.LinkLeaves`: a link of a chain leaves the positions a cut seals.

## Main results

* `Minimalist.isUpperSet_sealed`, `Minimalist.sealed_anti`: sealed sets are closed under dominance
  and grow as the derivation proceeds.
* `Minimalist.sealed_pic2_subset_pic1`: the next-phase condition seals less.
* `Minimalist.escapes_iff`, `Minimalist.crosses_iff`: islands and the condition on chain links are
  cuts.

## Implementation notes

* A stage is a position of the finished object, so the derivation is taken to be cyclic.
* The phase heads, and the deleted ones, are supplied by the analysis.

## References

* [chomsky-2000]
* [chomsky-2001]
* [chomsky-2015]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

/-- A cut assigns to each stage, the root of the object built so far, the positions an operation
at that stage cannot inspect. -/
abbrev Cut := TreePath → Set TreePath

/-- A schedule says, given the phase heads, whether the domain of `h` is transferred by stage `s`.
-/
abbrev Schedule := Finset TreePath → TreePath → TreePath → Prop

variable (t : LinearizedSyntacticObject)

/-- The head whose complement a phase head transfers: the phase head itself, or, where it has
deleted, the lexical head of its complement, which inherits its phasehood. -/
def transferHead (deleted : Finset TreePath) (h : TreePath) : TreePath :=
  if h ∈ deleted then lexicalHeadAt t (complement h) else h

/-- The complement of the head that transfers, [chomsky-2000]'s transfer domain. -/
def complementDomain (deleted : Finset TreePath) (h : TreePath) : Set TreePath :=
  Set.Ici (complement (transferHead t deleted h))

/-- The phase short of its root, transferred whole. -/
def wholePhaseDomain (h : TreePath) : Set TreePath := Set.Ioi (projectionAt t h)

/-- [chomsky-2000]'s schedule: the domain of `h` is transferred once its phase is complete, at every
stage above it. -/
def Pic1 : Schedule := fun _ h s ↦ s < projectionAt t h

/-- [chomsky-2001]'s schedule: the domain of `h` is transferred once a phase head whose complement
contains the phase of `h` has merged. -/
def Pic2 : Schedule := fun Φ h s ↦ ∃ z ∈ Φ, s ≤ z.parent ∧ complement z ≤ projectionAt t h

/-- The positions sealed at stage `s`: the domains of the phase heads transferred by then. -/
def sealed (Φ : Finset TreePath) (D : TreePath → Set TreePath) (σ : Schedule) : Cut :=
  fun s ↦ {q | ∃ h ∈ Φ, σ Φ h s ∧ q ∈ D h}

instance (deleted : Finset TreePath) (h : TreePath) :
    DecidablePred (· ∈ complementDomain t deleted h) :=
  fun q ↦ decidable_of_iff (complement (transferHead t deleted h) ≤ q) Iff.rfl

instance (h : TreePath) : DecidablePred (· ∈ wholePhaseDomain t h) :=
  fun q ↦ decidable_of_iff (projectionAt t h < q) Iff.rfl

instance (Φ : Finset TreePath) (h s : TreePath) : Decidable (Pic1 t Φ h s) :=
  inferInstanceAs (Decidable (_ < _))

instance (Φ : Finset TreePath) (h s : TreePath) : Decidable (Pic2 t Φ h s) :=
  inferInstanceAs (Decidable (∃ _ ∈ Φ, _))

instance (Φ : Finset TreePath) (D : TreePath → Set TreePath) (σ : Schedule)
    [∀ h, DecidablePred (· ∈ D h)] [∀ h s, Decidable (σ Φ h s)] (s : TreePath) :
    DecidablePred (· ∈ sealed Φ D σ s) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ Φ, _))

variable {t} {Φ : Finset TreePath} {D : TreePath → Set TreePath} {σ : Schedule}
  {deleted : Finset TreePath} {h s : TreePath}

theorem isUpperSet_complementDomain : IsUpperSet (complementDomain t deleted h) := isUpperSet_Ici _

theorem isUpperSet_wholePhaseDomain : IsUpperSet (wholePhaseDomain t h) := isUpperSet_Ioi _

/-- Sealed positions dominate only sealed positions. -/
theorem isUpperSet_sealed (hD : ∀ h, IsUpperSet (D h)) : IsUpperSet (sealed Φ D σ s) :=
  fun _ _ hab ⟨h, hΦ, hσ, hq⟩ ↦ ⟨h, hΦ, hσ, hD h hab hq⟩

/-- A schedule under which a domain stays transferred seals more at every later stage. -/
theorem sealed_anti (hσ : ∀ h, Antitone (σ Φ h)) : Antitone (sealed Φ D σ) :=
  fun _ _ hs _ ⟨h, hΦ, hσh, hq⟩ ↦ ⟨h, hΦ, hσ h hs hσh, hq⟩

theorem antitone_pic1 : Antitone (Pic1 t Φ h) := fun _ _ hs h ↦ lt_of_le_of_lt hs h

theorem antitone_pic2 : Antitone (Pic2 t Φ h) :=
  fun _ _ hs ⟨z, hz, hzs, hc⟩ ↦ ⟨z, hz, hs.trans hzs, hc⟩

/-- What is transferred once the next phase head merges is transferred once its phase is complete.
-/
theorem pic1_of_pic2 (hp : Pic2 t Φ h s) : Pic1 t Φ h s :=
  let ⟨z, _, hs, hc⟩ := hp
  hs.trans_lt ((parent_covBy_complement z).lt.trans_le hc)

/-- [chomsky-2001]'s condition seals less than [chomsky-2000]'s. -/
theorem sealed_pic2_subset_pic1 : sealed Φ D (Pic2 t) s ⊆ sealed Φ D (Pic1 t) s :=
  fun _ ⟨h, hΦ, hσ, hq⟩ ↦ ⟨h, hΦ, pic1_of_pic2 hσ, hq⟩

/-! ### The phase level -/

variable (t) in
/-- The phase level of a position: the phase of the lowest phase head whose complement contains it,
or the root where there is none. [chomsky-2015] computes labels there. -/
def phaseLevel (Φ : Finset TreePath) (q : t.val.Positions) : t.val.Positions :=
  ⟨⟨q.val.toList.take ((Φ.filter (complement · ≤ q.val)).sup (projectionAt t · |>.toList.length))⟩,
    isLowerSet_validPaths _ (TreePath.le_def.2 (List.take_prefix _ _)) q.2⟩

theorem phaseLevel_le (q : t.val.Positions) : phaseLevel t Φ q ≤ q :=
  Subtype.coe_le_coe.1 (TreePath.le_def.2 (List.take_prefix _ _))

/-- The phase of a phase head whose complement contains a position lies above its phase level. -/
theorem projectionAt_le_phaseLevel {q : t.val.Positions} (hΦ : h ∈ Φ) (hc : complement h ≤ q.val)
    (hp : projectionAt t h ≤ h.parent) : projectionAt t h ≤ (phaseLevel t Φ q).val := by
  have hq := hp.trans ((parent_covBy_complement h).le.trans hc)
  exact TreePath.le_def.2 (List.prefix_take_iff.2 ⟨TreePath.le_def.1 hq,
    Finset.le_sup (f := (projectionAt t · |>.toList.length)) (Finset.mem_filter.2 ⟨hΦ, hc⟩)⟩)

/-- A position no phase head's complement contains reaches its phase level at the root. -/
theorem phaseLevel_eq_bot {q : t.val.Positions} (hq : ∀ h ∈ Φ, ¬ complement h ≤ q.val) :
    phaseLevel t Φ q = ⊥ := by
  have : Φ.filter (complement · ≤ q.val) = ∅ := Finset.filter_eq_empty_iff.2 hq
  exact Subtype.ext (TreePath.ext (by simp [phaseLevel, this]))

/-! ### Chain links that leave a cut -/

variable (t) in
/-- A link of the chain of `tok` leaves the positions `cut` seals at the stage of its landing site,
the mother of the phrase that lands. -/
def LinkLeaves (tok : LexicalItem.Token) (cut : Cut) : Prop :=
  ∃ x ∈ links t tok, x.2 ∈ cut x.1.parent

instance (tok : LexicalItem.Token) (cut : Cut) [∀ s, DecidablePred (· ∈ cut s)] :
    Decidable (LinkLeaves t tok cut) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem mem_links {tok : LexicalItem.Token} {x : TreePath × TreePath} :
    x ∈ links t tok ↔ ∃ q ∈ chain t tok, ∃ p ∈ chain t tok, IsLink t tok p q ∧
      x = (projectionAt t p, q) := by
  simp only [links, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, p, ⟨hp, hl⟩, rfl⟩
    exact ⟨q, hq, p, hp, hl, rfl⟩
  · rintro ⟨q, hq, p, hp, hl, rfl⟩
    exact ⟨q, hq, p, ⟨hp, hl⟩, rfl⟩

theorem mem_validPaths_of_mem_chain {tok : LexicalItem.Token} {p : TreePath}
    (hp : p ∈ chain t tok) : p ∈ t.val.validPaths := by
  simp only [chain, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq] at hp
  obtain ⟨⟨p', b⟩, hpb, -, rfl⟩ := hp
  obtain ⟨s, hs, -⟩ := mem_positions_iff.1 hpb
  simp [validPaths, hs]

/-- A link lands above the mother of the phrase that lands, and outside the copy it links. -/
theorem parent_lt_of_mem_links {tok : LexicalItem.Token} {x : TreePath × TreePath}
    (hx : x ∈ links t tok) : x.1.parent < x.2 ∧ ¬ x.1 ≤ x.2 := by
  obtain ⟨q, -, p, hp, hl, rfl⟩ := mem_links.1 hx
  have hv : projectionAt t p ∈ t.val.validPaths :=
    isLowerSet_validPaths _ (projectionAt_le t p) (mem_validPaths_of_mem_chain hp)
  have h0 : projectionAt t p ≠ ⊥ := fun h ↦ hl.1.2.1 (h ▸ bot_le)
  have hb := LinearizedSyntacticObject.isBranchingAt_parent (t := t)
    (a := ⟨projectionAt t p, hv⟩) fun h ↦ h0 (congrArg Subtype.val h)
  exact (cCommands_iff_parent_lt h0 hb).1 hl.1

/-- Above a link's landed phrase and below its lower copy, a position lies outside the landed
phrase exactly when it lies strictly below the landing stage. -/
theorem not_le_fst_iff {tok : LexicalItem.Token} {x : TreePath × TreePath} {D : TreePath}
    (hx : x ∈ links t tok) (hD : D ≤ x.2) : ¬ D ≤ x.1 ↔ x.1.parent < D := by
  obtain ⟨hpx, hnx⟩ := parent_lt_of_mem_links hx
  have h0 : x.1 ≠ ⊥ := fun h ↦ hnx (h ▸ bot_le)
  have hcov : x.1.parent ⋖ x.1 := by
    rw [← TreePath.pred_eq_parent]
    exact Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using h0)
  constructor
  · intro hDx
    rcases IsLeftLinear.comparable_of_le_common hD hpx.le with h | h
    · exact absurd (h.trans hcov.le) hDx
    · exact lt_of_le_of_ne h fun he ↦ hDx (he ▸ hcov.le)
  · intro hlt hDx
    exact hnx (((hcov.eq_or_eq hlt.le hDx).resolve_left hlt.ne') ▸ hD)

/-- An island is a cut: a link escapes the domain at `D` exactly when it leaves the positions `D`
dominates, sealed at every stage above `D`. -/
theorem escapes_iff {tok : LexicalItem.Token} {D : TreePath} :
    Escapes t tok D ↔ LinkLeaves t tok (sealed {D} Set.Ici fun _ h s ↦ s < h) := by
  unfold Escapes LinkLeaves
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  simp only [sealed, Finset.mem_singleton, exists_eq_left, Set.mem_Ici, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hD, hDx⟩ ↦ ⟨(not_le_fst_iff hx hD).1 hDx, hD⟩,
    fun ⟨hlt, hD⟩ ↦ ⟨hD, (not_le_fst_iff hx hD).2 hlt⟩⟩

/-- The condition on chain links is a cut: a link leaves the phase of `h` exactly when it leaves the
complement of `h`, sealed at every stage above the phase. -/
theorem crosses_iff {tok : LexicalItem.Token} {h : TreePath} (hh : h ∈ t.val.validPaths)
    (h0 : h ≠ ⊥) (hproj : projectionAt t h ≤ h.parent) :
    Crosses t tok h ↔ LinkLeaves t tok (sealed {h} (complementDomain t ∅) (Pic1 t)) := by
  unfold Crosses LinkLeaves
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  obtain ⟨q, hq, p, -, -, rfl⟩ := mem_links.1 hx
  simp only [sealed, Finset.mem_singleton, exists_eq_left, Pic1, complementDomain, transferHead,
    Finset.notMem_empty, ↓reduceIte, Set.mem_Ici, Set.mem_ofPred_eq]
  rw [mem_cCommandDomain_iff_complement_le hh h0 (mem_validPaths_of_mem_chain hq)]
  have hle : ∀ hc : complement h ≤ q, projectionAt t h ≤ q := fun hc ↦
    hproj.trans ((parent_covBy_complement h).le.trans hc)
  exact ⟨fun ⟨hc, hn⟩ ↦ ⟨(not_le_fst_iff hx (hle hc)).1 hn, hc⟩,
    fun ⟨hlt, hc⟩ ↦ ⟨hc, (not_le_fst_iff hx (hle hc)).2 hlt⟩⟩

end Minimalist
