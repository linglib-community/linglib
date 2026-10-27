module

public import Linglib.Logic.Orthologic.EpistemicFrame
public import Linglib.Logic.Orthologic.EpistemicOrthologic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# Holliday and Mandelkern (2024): The orthologic of epistemic modals

This file formalizes Holliday and Mandelkern's possibility semantics for epistemic modals on their
running example, the Epistemic Scale. The Scale is the epistemic frame of the two-world Boolean
algebra of a coin flip, whose five possibilities run from knowing `p` through full uncertainty to
knowing `¬p`. The frame comes from the general construction `Orthologic.epistemicFrame`, so its
compatibility and accessibility relations are derived rather than stipulated, and the paper's
truth-value table follows by decision. On this model Wittgenstein sentences are contradictions
while `◇¬p` does not entail `¬p`, and the classical laws the paper gives up fail at the point of
full uncertainty.

## Main results

* `compat_iff`, `access_iff`: the compatibility and accessibility relations of the Scale.
* `wittgenstein`, `diamond_neg_not_entail_neg`, `not_entail_box`: Wittgenstein sentences are
  contradictions, yet `◇¬p` does not entail `¬p` and `p` does not entail `□p`.
* `not_derivable_dia_neg_neg`, `not_derivable_box`: so neither entailment is derivable in the
  epistemic orthologic EO.
* `distributivity_fails`, `disjunctive_syllogism_fails`: the classical inferences of (10) and
  (13) fail at the point of full uncertainty.
* `orthomodularity_fails`, `not_isModularLattice`, `pseudocomplementation_fails`: the regular
  propositions form an ortholattice that is not orthomodular, not modular, and whose
  orthonegation is not a pseudocomplement.
* `deMorgan`, `not_known_either`: the contrasts with state-based semantics.
* `stratified_level1`, `not_stratified_across_levels`: classicality within each level of
  modal iteration, but not across levels.

## Implementation notes

The Boolean algebra is `Finset (Fin 2)`, so every claim about the Scale is decidable; the
general truth conditions of embedded propositions are `Orthologic.mem_core_embed` and
`Orthologic.mem_diamond_embed`. The paper contrasts its symmetric Wittgenstein's Law with the
order asymmetry of dynamic semantics, whose side is `Veltman1996.consistent_might_neg` beside
`Veltman1996.not_consistent_up_might_neg`; no theorem here conjoins the two.

## TODO

The Epistemic Grid (Example 4.34), the logic EO+ with its completeness theorem, and the
remaining principles of Proposition 5.12 are not formalized.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace HollidayMandelkern2024

open Orthologic Orthologic.Possibility

/-- `Coin` is the two-world Boolean algebra of the coin flip (Example 5.3). -/
abbrev Coin := Finset (Fin 2)

/-- `Poss` is the type of possibilities of the epistemic frame of `Coin`. -/
abbrev Poss := Possibility Coin

/-- `frame` is the Epistemic Scale's compatibility frame, with accessibility `access`. -/
abbrev frame : CompatFrame Poss := epistemicFrame Coin

instance : DecidableRel frame.compat := inferInstanceAs (DecidableRel (compat (B := Coin)))

/-- The possibility `x1 = ({0}, {0})` knows `p`. -/
def x1 : Poss := ⟨({0}, {0}), by decide⟩

/-- The possibility `x2 = ({0}, {0, 1})` settles `p` without knowing it. -/
def x2 : Poss := ⟨({0}, {0, 1}), by decide⟩

/-- The possibility `x3 = ({0, 1}, {0, 1})` is fully uncertain. -/
def x3 : Poss := ⟨({0, 1}, {0, 1}), by decide⟩

/-- The possibility `x4 = ({1}, {0, 1})` settles `¬p` without knowing it. -/
def x4 : Poss := ⟨({1}, {0, 1}), by decide⟩

/-- The possibility `x5 = ({1}, {1})` knows `¬p`. -/
def x5 : Poss := ⟨({1}, {1}), by decide⟩

-- Table 1
theorem card_poss : Fintype.card Poss = 5 := by decide

/-- Compatibility is the path `x1 — x2 — x3 — x4 — x5` (Figure 7 and Example 5.3). -/
theorem compat_iff : ∀ x y : Poss, frame.compat x y ↔ x = y ∨
    (x, y) ∈ [(x1, x2), (x2, x1), (x2, x3), (x3, x2), (x3, x4), (x4, x3), (x4, x5), (x5, x4)] := by
  decide

/-- `x2` accesses `x1` and `x3`, `x4` accesses `x3` and `x5`, and every possibility accesses
itself (Figure 12 and Example 5.3). -/
theorem access_iff : ∀ x y : Poss, (x, y) ∈ access ↔ x = y ∨
    (x, y) ∈ [(x2, x1), (x2, x3), (x4, x3), (x4, x5)] := by
  decide

/-- `P` is the proposition that the coin lands `0`, the embedding of `{0}`. -/
abbrev P : Set Poss := embed ({0} : Coin)

/-- `nP` is `¬p`. -/
abbrev nP : Set Poss := orthoNeg frame P

/-- `bP` is `□p`. -/
abbrev bP : Set Poss := access.core P

/-- `bnP` is `□¬p`. -/
abbrev bnP : Set Poss := access.core nP

/-- `dP` is `◇p`. -/
abbrev dP : Set Poss := diamond frame access P

/-- `dnP` is `◇¬p`. -/
abbrev dnP : Set Poss := diamond frame access nP

instance : DecidablePred (· ∈ P) := inferInstance
instance : DecidablePred (· ∈ nP) := inferInstance
instance : DecidablePred (· ∈ bP) := inferInstance
instance : DecidablePred (· ∈ bnP) := inferInstance
instance : DecidablePred (· ∈ dP) := inferInstance
instance : DecidablePred (· ∈ dnP) := inferInstance

/-! ### Example 4.33: the truth values of Figure 13 -/

theorem mem_P : ∀ x : Poss, x ∈ P ↔ x = x1 ∨ x = x2 := by decide

theorem mem_nP : ∀ x : Poss, x ∈ nP ↔ x = x4 ∨ x = x5 := by decide

theorem mem_bP : ∀ x : Poss, x ∈ bP ↔ x = x1 := by decide

theorem mem_bnP : ∀ x : Poss, x ∈ bnP ↔ x = x5 := by decide

theorem mem_dP : ∀ x : Poss, x ∈ dP ↔ x = x1 ∨ x = x2 ∨ x = x3 := by decide

theorem mem_dnP : ∀ x : Poss, x ∈ dnP ↔ x = x3 ∨ x = x4 ∨ x = x5 := by decide

theorem mem_dP_inter_dnP : ∀ x : Poss, x ∈ dP ∩ dnP ↔ x = x3 := by decide

theorem mem_bP_disj_bnP : ∀ x : Poss, x ∈ disj frame bP bnP ↔ x = x1 ∨ x = x5 := by decide

instance (s : Finset Poss) : DecidablePred (· ∈ (↑s : Set Poss)) :=
  fun x ↦ inferInstanceAs (Decidable (x ∈ s))

-- Example 4.11
theorem card_regular :
    ((Finset.univ : Finset (Finset Poss)).filter
      fun s : Finset Poss ↦ IsRegular frame (↑s : Set Poss)).card = 10 := by
  decide

/-! ### The desiderata of §2 on the Scale -/

/-- Wittgenstein sentences of both orders are contradictions ((2) and (3)), by Proposition 4.27. -/
theorem wittgenstein : nP ∩ dP = ∅ ∧ P ∩ dnP = ∅ :=
  ⟨Set.disjoint_iff_inter_eq_empty.mp (disjoint_orthoNeg_diamond frame access P),
    by simpa only [orthoNeg_orthoNeg_of_isRegular frame (embed_isRegular _),
      Set.disjoint_iff_inter_eq_empty] using disjoint_orthoNeg_diamond frame access nP⟩

/-- At the coin with unknown outcome, `◇¬p` does not entail `¬p` (§1) and `p` does not entail `□p`
(§2). -/
theorem diamond_neg_not_entail_neg : x3 ∈ dnP ∧ x3 ∉ nP := by decide

theorem not_entail_box : x2 ∈ P ∧ x2 ∉ bP := by decide

/-- EO does not derive `◇¬p ⊢ ¬p` (§1), by soundness (Theorem 3.26) for the Scale's epistemic
ortholattice (Proposition 4.27). -/
theorem not_derivable_dia_neg_neg :
    ¬ EDerivable (ModalFormula.dia (.neg (.var ()))) (.neg (.var ()) : ModalFormula Unit) := by
  intro h
  have hle := Concept.extent_subset_extent_iff.mpr <| ModalFormula.sound
    (CompatFrame.necHom_le access) (CompatFrame.wittgensteinLaw_necHom frame access) h
    fun _ ↦ eB ({0} : Coin)
  change ((ModalFormula.eval _ _ _ : frame.Regular) : Set Poss) ⊆
    ((ModalFormula.eval _ _ _ : frame.Regular) : Set Poss) at hle
  simp only [ModalFormula.eval_dia, CompatFrame.coe_diamondHom_necHom, ModalFormula.eval,
    CompatFrame.Regular.coe_compl, coe_eB] at hle
  exact diamond_neg_not_entail_neg.2 (hle diamond_neg_not_entail_neg.1)

/-- EO does not derive `p ⊢ □p`: at `x2`, which settles `p` without knowing it (§2). -/
theorem not_derivable_box :
    ¬ EDerivable (.var ()) (ModalFormula.box (.var ()) : ModalFormula Unit) := by
  intro h
  have hle := Concept.extent_subset_extent_iff.mpr <| ModalFormula.sound
    (CompatFrame.necHom_le access) (CompatFrame.wittgensteinLaw_necHom frame access) h
    fun _ ↦ eB ({0} : Coin)
  change ((ModalFormula.eval _ _ _ : frame.Regular) : Set Poss) ⊆
    ((ModalFormula.eval _ _ _ : frame.Regular) : Set Poss) at hle
  simp only [ModalFormula.eval, CompatFrame.coe_necHom, coe_eB] at hle
  exact not_entail_box.2 (hle not_entail_box.1)

/-- At `x3`, `(p ∨ ¬p) ∧ (◇p ∧ ◇¬p)` holds but its distributed form does not ((10) and Example
4.33). -/
theorem distributivity_fails :
    x3 ∈ disj frame P nP ∩ (dP ∩ dnP) ∧ x3 ∉ disj frame (P ∩ dnP) (nP ∩ dP) := by
  decide

/-- Disjunctive syllogism fails (13), since `p ∨ □¬p` is a logical truth and `¬□¬p` holds at
`x3` while `p` does not. -/
theorem disjunctive_syllogism_fails :
    (∀ x : Poss, x ∈ disj frame P bnP) ∧ x3 ∈ orthoNeg frame bnP ∧ x3 ∉ P := by
  decide

/-- The regular propositions of the Scale are not orthomodular ((21) and Example 3.20). -/
theorem orthomodularity_fails : ¬ IsOrthomodularLattice frame.Regular := by
  intro
  let p : frame.Regular := eB ({0} : Coin)
  have coe_dp : (diamondHom (frame.necHom access) p : Set Poss) = dP :=
    CompatFrame.coe_diamondHom_necHom access p
  have hle : p ≤ diamondHom (frame.necHom access) p := Concept.extent_subset_extent_iff.mp <| by
    change (p : Set Poss) ⊆ (diamondHom (frame.necHom access) p : Set Poss)
    rw [coe_dp]
    exact (by decide : ∀ x : Poss, x ∈ P → x ∈ dP)
  have hx3 : x3 ∈ ((p ⊔ pᶜ ⊓ diamondHom (frame.necHom access) p : frame.Regular) : Set Poss) := by
    rw [sup_compl_inf_of_le hle, coe_dp]
    decide
  simp only [CompatFrame.Regular.coe_sup, CompatFrame.Regular.coe_inf,
    CompatFrame.Regular.coe_compl, coe_dp] at hx3
  exact (by decide : x3 ∉ disj frame P (nP ∩ dP)) hx3

/-- Nor are they modular, since a modular ortholattice is orthomodular ([holliday-mandelkern-2024]
footnote 4), and so they are not distributive. -/
theorem not_isModularLattice : ¬ IsModularLattice frame.Regular := fun _ ↦
  orthomodularity_fails inferInstance

/-- Orthonegation is not pseudocomplementation (Example 3.20), since `p ∧ ◇¬p = ⊥` although
`◇¬p ≰ ¬p`. -/
theorem pseudocomplementation_fails : ¬ ∀ a b : frame.Regular, Disjoint a b → b ≤ aᶜ := by
  intro h
  let p : frame.Regular := eB ({0} : Coin)
  have coe_dnp : (diamondHom (frame.necHom access) pᶜ : Set Poss) = dnP := by
    rw [CompatFrame.coe_diamondHom_necHom, CompatFrame.Regular.coe_compl, coe_eB]
  have hd : Disjoint p (diamondHom (frame.necHom access) pᶜ) := disjoint_iff.2 <|
    CompatFrame.Regular.coe_eq_empty.1 <| by
      rw [CompatFrame.Regular.coe_inf, coe_dnp, coe_eB]
      exact wittgenstein.2
  have hle := Concept.extent_subset_extent_iff.mpr (h _ _ hd)
  change (diamondHom (frame.necHom access) pᶜ : Set Poss) ⊆ ((pᶜ : frame.Regular) : Set Poss)
    at hle
  rw [coe_dnp, CompatFrame.Regular.coe_compl, coe_eB] at hle
  exact diamond_neg_not_entail_neg.2 (hle diamond_neg_not_entail_neg.1)

/-- De Morgan's law makes `◇p ∧ ◇¬p` equivalent to `¬(□¬p ∨ □p)` (29). -/
theorem deMorgan : ∀ x : Poss, x ∈ dP ∩ dnP ↔ x ∈ orthoNeg frame (disj frame bnP bP) := by
  decide

/-- The disjunction `□¬p ∨ □p` is not a logical truth (30). -/
theorem not_known_either : x3 ∉ disj frame bnP bP := by decide

-- Theorem 5.7.4
theorem diamond_P_not_subset : ¬ dP ⊆ P :=
  not_diamond_embed_subset (by decide) (by decide)

/-! ### Example 4.42: levelwise classicality -/

/-- `Level0` indexes the Boolean level `B0 = {∅, p, ¬p, ⊤}`. -/
inductive Level0
  | bot
  | p
  | np
  | top
  deriving DecidableEq, Fintype

/-- `Level0.set` sends each index to its proposition in `B0`. -/
def Level0.set : Level0 → Set Poss
  | .bot => ∅
  | .p => P
  | .np => nP
  | .top => Set.univ

instance : ∀ l : Level0, DecidablePred (· ∈ l.set)
  | .bot => inferInstanceAs (DecidablePred (· ∈ (∅ : Set Poss)))
  | .p => inferInstanceAs (DecidablePred (· ∈ P))
  | .np => inferInstanceAs (DecidablePred (· ∈ nP))
  | .top => inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set Poss)))

/-- `Level1` indexes the modal level `B1`, the eight propositions of Example 3.33. -/
inductive Level1
  | bot
  | bp
  | dnp
  | dp
  | bnp
  | knownEither
  | uncertain
  | top
  deriving DecidableEq, Fintype

/-- `Level1.set` sends each index to its proposition in `B1`. -/
def Level1.set : Level1 → Set Poss
  | .bot => ∅
  | .bp => bP
  | .dnp => dnP
  | .dp => dP
  | .bnp => bnP
  | .knownEither => disj frame bP bnP
  | .uncertain => dP ∩ dnP
  | .top => Set.univ

instance : ∀ l : Level1, DecidablePred (· ∈ l.set)
  | .bot => inferInstanceAs (DecidablePred (· ∈ (∅ : Set Poss)))
  | .bp => inferInstanceAs (DecidablePred (· ∈ bP))
  | .dnp => inferInstanceAs (DecidablePred (· ∈ dnP))
  | .dp => inferInstanceAs (DecidablePred (· ∈ dP))
  | .bnp => inferInstanceAs (DecidablePred (· ∈ bnP))
  | .knownEither => inferInstanceAs (DecidablePred (· ∈ disj frame bP bnP))
  | .uncertain => inferInstanceAs (DecidablePred (· ∈ dP ∩ dnP))
  | .top => inferInstanceAs (DecidablePred (· ∈ (Set.univ : Set Poss)))

theorem level1_closed :
    (∀ l : Level1, IsRegular frame l.set) ∧
    (∀ l : Level1, ∃ m : Level1, ∀ x, x ∈ orthoNeg frame l.set ↔ x ∈ m.set) ∧
    (∀ l m : Level1, ∃ n : Level1, ∀ x, x ∈ l.set ∩ m.set ↔ x ∈ n.set) := by
  refine ⟨by decide, by decide, by decide⟩

-- Proposition 4.39
theorem stratified_level0 :
    ∀ l m : Level0, (∃ x ∈ l.set, ∃ y ∈ m.set, frame.compat x y) →
      ∃ z, z ∈ l.set ∧ z ∈ m.set := by
  decide

/-- Within `B1` the criterion of Proposition 4.39 holds too, so `B1` is an eight-element
Boolean algebra. -/
theorem stratified_level1 :
    ∀ l m : Level1, (∃ x ∈ l.set, ∃ y ∈ m.set, frame.compat x y) →
      ∃ z, z ∈ l.set ∧ z ∈ m.set := by
  decide

/-- Across levels the criterion fails, since `x2` settles `p`, `x3` settles `◇¬p`, the two
are compatible, and nothing settles both. -/
theorem not_stratified_across_levels :
    x2 ∈ P ∧ x3 ∈ dnP ∧ frame.compat x2 x3 ∧ ∀ z : Poss, z ∉ P ∩ dnP := by
  decide

end HollidayMandelkern2024
