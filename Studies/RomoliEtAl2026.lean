module

public import Studies.AugurzkyEtAl2023
public import Studies.GuerriniWehbe2025
public import Linglib.Data.Statistics.RomoliEtAl2026

/-!
# Romoli et al. (2026): Putting plural definites into context

Romoli et al. ask whether a context that makes a non-maximal reading relevant affects a plural
definite bound by *every*, *no*, *not every* and *exactly two*, reanalysing the two experiments of
Augurzky et al. (2023) and adding a third on *exactly two boys opened their presents*. On the
symmetric approach, a truth-value gap projected by Strong Kleene and resolved by the question the
context raises, the context affects positive and negative environments alike. On the asymmetric
approach, Guerrini and Wehbe's presuppositional exhaustification below the quantifier with its
presupposition accommodated globally, it affects positive ones only, including the positive part
of *exactly two*. The third experiment found the negative part affected as much as the positive.

* `pointwise_exactlyTwo_ne_zero_iff` and its siblings: the definedness conditions (25).

## Implementation notes

A picture is the number of presents each boy opened. The contexts' questions are Augurzky et
al.'s, lifted boy by boy, and `pex` applies at the lowest scope site only, as footnote 7 restricts
it. The verdicts are bivalent, so they do not register effect sizes.

## TODO

* The differences in effect size across quantifiers (Table 12) need graded predictions, and with
  them the prior bias of §4.2 and the cost of local accommodation of §4.3.

## References

* [romoli-etal-2026]
* [augurzky-etal-2023]
* [guerrini-wehbe-2025]
* [kriz-2016]
* [kriz-chemla-2015]
* [bar-lev-2021]
-/

open Quantifier (NumberTree)

@[expose] public section

namespace RomoliEtAl2026

open KrizChemla2015 (Display cell resolve reading someReading allReading supervaluation pointwise
  holds resolutions)
open AugurzkyEtAl2023 (nine)
open Exhaustification (subDisjsOfCard)
open BarLev2021 (atom)
open GuerriniWehbe2025 (pexPlural)

/-! ### Sentences and contexts -/

/-- The number tree each quantifier denotes. -/
def Quantifier.tree : Quantifier → NumberTree
  | .every => NumberTree.all
  | .no => NumberTree.no
  | .notEvery => NumberTree.notAll
  | .exactlyTwo => NumberTree.cardinal {2}

instance : (q : Quantifier) → DecidableRel q.tree
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => inferInstanceAs (DecidableRel NumberTree.notAll)
  | .exactlyTwo => inferInstanceAs (DecidableRel (NumberTree.cardinal {2}))

/-- *no* and *not every* are downward entailing; *every* and *exactly two* are not. -/
instance : (q : Quantifier) → Decidable q.tree.ScopeAntitone
  | .every => isFalse fun h ↦ Nat.one_ne_zero (h 0 0 rfl)
  | .no => isTrue NumberTree.scopeAntitone_no
  | .notEvery => isTrue NumberTree.scopeAntitone_notAll
  | .exactlyTwo => isFalse fun h ↦ by simpa [Quantifier.tree] using h 0 1

/-- The sentences of Experiments 1 and 2 are those of [augurzky-etal-2023]. -/
def Quantifier.ofAugurzky : AugurzkyEtAl2023.Quantifier → Quantifier
  | .every => .every
  | .no => .no
  | .notEvery => .notEvery

theorem tree_ofAugurzky (q : AugurzkyEtAl2023.Quantifier) :
    (Quantifier.ofAugurzky q).tree = q.tree := by
  cases q <;> rfl

/-- The sentence of [augurzky-etal-2023] a quantifier's sentence is, where it is one of theirs. -/
def Quantifier.toAugurzky : Quantifier → Option AugurzkyEtAl2023.Quantifier
  | .every => some .every
  | .no => some .no
  | .notEvery => some .notEvery
  | .exactlyTwo => none

theorem toAugurzky_ofAugurzky (q : AugurzkyEtAl2023.Quantifier) :
    (Quantifier.ofAugurzky q).toAugurzky = some q := by
  cases q <;> rfl

/-- The question a context raises, whether any boy opened any of his presents or whether every
boy opened all of them, which [augurzky-etal-2023] code as the context itself. -/
def Context.raises : Context → AugurzkyEtAl2023.Context
  | .prohibited => .existential
  | .required => .universal

/-- The context a recoded level names for a level of POLARITY. The lax context of the positive
condition is the prohibition and that of the negative condition the requirement (§3.3.3). -/
def Recoding.context : Recoding → Polarity → Context
  | .lax, .positive | .strict, .negative => .prohibited
  | .lax, .negative | .strict, .positive => .required

/-- The trivalent display of a picture, one cell per boy. -/
def Item.display (p : Item) : Display := p.opened.map cell

private theorem cell_eq_neg_one_iff (n : ℕ) : cell n = -1 ↔ n = 0 := by
  rw [← not_iff_not, ← Ne, ← SignType.nonneg_iff_ne_neg_one, KrizChemla2015.designated_lp_cell]
  omega

/-! ### Strong Kleene projection (25) -/

section StrongKleene

variable {d : Display}

-- (25a)
theorem pointwise_all_ne_zero_iff :
    pointwise NumberTree.all d ≠ 0 ↔ (∀ v ∈ d, v = 1) ∨ -1 ∈ d := by
  rw [KrizChemla2015.pointwise_eq_supervaluation_of_scopeMonotone NumberTree.scopeMonotone_all,
    Ne, KrizChemla2015.supervaluation_eq_zero_iff, not_not, someReading, allReading,
    KrizChemla2015.reading_all, KrizChemla2015.reading_all]
  simp only [Trivalent.Designation.threshold_lp, Trivalent.Designation.threshold_k3,
    SignType.nonneg_iff_ne_neg_one, SignType.one_le_iff]
  refine ⟨fun h ↦ (em (-1 ∈ d)).symm.imp (fun hm ↦ h.1 fun v hv hv' ↦ hm (hv' ▸ hv)) id, ?_⟩
  rintro (h | h)
  · exact iff_of_true (fun v hv ↦ by simp [h v hv]) h
  · exact iff_of_false (fun h' ↦ h' _ h rfl) fun h' ↦ by simpa using h' _ h

-- (25b)
theorem pointwise_no_ne_zero_iff :
    pointwise NumberTree.no d ≠ 0 ↔ (∀ v ∈ d, v = -1) ∨ 1 ∈ d := by
  rw [KrizChemla2015.pointwise_eq_supervaluation_of_scopeAntitone NumberTree.scopeAntitone_no,
    Ne, KrizChemla2015.supervaluation_eq_zero_iff, not_not, someReading, allReading,
    KrizChemla2015.reading_no, KrizChemla2015.reading_no]
  simp only [Trivalent.Designation.threshold_lp, Trivalent.Designation.threshold_k3,
    SignType.nonneg_iff_ne_neg_one, SignType.one_le_iff, not_not]
  refine ⟨fun h ↦ (em (1 ∈ d)).symm.imp (fun hm ↦ h.2 fun v hv hv' ↦ hm (hv' ▸ hv)) id, ?_⟩
  rintro (h | h)
  · exact iff_of_true h fun v hv ↦ by simp [h v hv]
  · exact iff_of_false (fun h' ↦ by simpa using h' _ h) fun h' ↦ h' _ h rfl

-- (25c)
theorem pointwise_notAll_ne_zero_iff :
    pointwise NumberTree.notAll d ≠ 0 ↔ -1 ∈ d ∨ ∀ v ∈ d, v = 1 := by
  have h : pointwise NumberTree.notAll d = pointwise NumberTree.allᶜ d := rfl
  rw [h, KrizChemla2015.pointwise_compl, show ∀ v : SignType, -v ≠ 0 ↔ v ≠ 0 by decide,
    pointwise_all_ne_zero_iff, or_comm]

theorem pointwise_exactlyTwo_eq_one_iff :
    pointwise (NumberTree.cardinal {2}) d = 1 ↔ d.count 1 = 2 ∧ d.count 0 = 0 := by
  rw [KrizChemla2015.pointwise_cardinal_eq_one_iff]
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h ↦ by have := h _ le_rfl (by omega); have := h _ (by omega) le_rfl; omega,
    fun h k h₁ h₂ ↦ by omega⟩

theorem pointwise_exactlyTwo_eq_neg_one_iff :
    pointwise (NumberTree.cardinal {2}) d = -1 ↔ 2 < d.count 1 ∨ d.count 1 + d.count 0 < 2 := by
  rw [KrizChemla2015.pointwise_cardinal_eq_neg_one_iff]
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h ↦ by by_contra hc; exact h 2 (by omega) (by omega) rfl,
    fun h k h₁ h₂ ↦ by omega⟩

/-- *Exactly two* is defined where two boys opened all presents and the rest none, more than two
opened all, or fewer than two any (25d). -/
theorem pointwise_exactlyTwo_ne_zero_iff :
    pointwise (NumberTree.cardinal {2}) d ≠ 0 ↔
      (d.count 1 = 2 ∧ d.count 0 = 0) ∨ 2 < d.count 1 ∨ d.count 1 + d.count 0 < 2 := by
  rw [← pointwise_exactlyTwo_eq_one_iff, ← pointwise_exactlyTwo_eq_neg_one_iff]
  generalize pointwise (NumberTree.cardinal {2}) d = v
  decide +revert

end StrongKleene

/-! ### The symmetric approach (§2.1, §3.2.1) -/

section Symmetric

variable (q : NumberTree) [DecidableRel q]

/-- The symmetric verdict is [kriz-2016]'s usability of the Strong Kleene sentence relative to
the question the context raises. -/
def symmetric (ctx : AugurzkyEtAl2023.Context) (d : Display) : Prop :=
  Homogeneity.usable ctx.issue (pointwise q) d

theorem symmetric_iff (ctx : AugurzkyEtAl2023.Context) (d : Display) :
    symmetric q ctx d ↔ reading q d ctx.designation := by
  refine AugurzkyEtAl2023.usable_iff_reading_of q (fun d h ↦ ?_) (fun d h ↦ ?_) (fun c h ↦ ?_)
    le_rfl (fun _ _ h ↦ Setoid.polar_iff.2 <| show reading q _ _ ↔ reading q _ _ by
      rw [reading, reading, Setoid.ker_def.1 h]) d
  · rw [pointwise, SignType.supervaluation_eq_one_iff] at h
    exact h _ (List.mem_toFinset.2 (KrizChemla2015.resolve_mem_resolutions _ d))
  · rw [pointwise, SignType.supervaluation_eq_neg_one_iff] at h
    exact h.2 _ (List.mem_toFinset.2 (KrizChemla2015.resolve_mem_resolutions _ d))
  · rw [KrizChemla2015.pointwise_map_ofProp]
    simp [h]

instance (ctx : AugurzkyEtAl2023.Context) (d : Display) : Decidable (symmetric q ctx d) :=
  decidable_of_iff _ (symmetric_iff q ctx d).symm

/-- Over Strong Kleene and over Spector's supervaluation the symmetric verdict is the same, so the
difference between them is immaterial (§3.2.1). -/
theorem symmetric_iff_nonImplicature (ctx : AugurzkyEtAl2023.Context) (d : Display) :
    symmetric q ctx d ↔ AugurzkyEtAl2023.nonImplicature q ctx d := by
  rw [symmetric_iff, AugurzkyEtAl2023.nonImplicature_iff]

end Symmetric

/-! ### The asymmetric approach (§2.2, §3.2.2) -/

/-- The alternatives a context leaves `pex` on a boy's definite are the disjunctions over as many
of his nine presents as keep the reading the context's question selects. -/
def alternatives (ctx : AugurzkyEtAl2023.Context) : Set (Set (Finset ℕ)) :=
  subDisjsOfCard nine (atom BarLev2021.holds) (nine.card + 1 - ctx.threshold nine)

private theorem threshold_nine (ctx : AugurzkyEtAl2023.Context) :
    0 < ctx.threshold nine ∧ ctx.threshold nine ≤ nine.card := by
  cases ctx <;> simp [AugurzkyEtAl2023.Context.threshold, nine]

theorem isReading_alternatives (ctx : AugurzkyEtAl2023.Context) :
    BarLev2021.IsReading nine nine BarLev2021.holds (ctx.question nine)
      (Exhaustification.exhIEII (alternatives ctx) (⋃ b ∈ nine, atom BarLev2021.holds b)) := by
  have hk := threshold_nine ctx
  have h := BarLev2021.exhIEII_pruned_eq_atLeast (BarLev2021.separating_holds nine nine)
    (m := nine.card + 1 - ctx.threshold nine) (by omega) (by rw [Finset.inter_self]; omega)
  rw [Finset.inter_self] at h
  rw [alternatives, h, show nine.card + 1 - (nine.card + 1 - ctx.threshold nine) =
    ctx.threshold nine by omega]
  exact AugurzkyEtAl2023.isReading_question ⟨0, by simp [nine]⟩ ctx

/-- The value `pex` gives the definite of a boy who opened `n` of his presents is false if `n` is
zero, true if `n` reaches the number the context's question asks about, and a gap otherwise. -/
def pexCell (ctx : AugurzkyEtAl2023.Context) (n : ℕ) : SignType :=
  if n = 0 then -1 else if ctx.threshold nine ≤ n then 1 else 0

theorem pexCell_eq_one_iff {ctx : AugurzkyEtAl2023.Context} {n : ℕ} :
    pexCell ctx n = 1 ↔ ctx.threshold nine ≤ n := by
  have := (threshold_nine ctx).1
  unfold pexCell
  split_ifs <;> simp_all
  omega

theorem zero_le_pexCell_iff {ctx : AugurzkyEtAl2023.Context} {n : ℕ} :
    0 ≤ pexCell ctx n ↔ 1 ≤ n := by
  unfold pexCell
  split_ifs <;> simp_all <;> omega

/-- [guerrini-wehbe-2025]'s `pex` on a boy's *he opened his presents*, over the alternatives the
context leaves, is the value `pexCell` gives the number of his presents he opened. -/
theorem pexPlural_alternatives (ctx : AugurzkyEtAl2023.Context) (w : Finset ℕ) :
    pexPlural nine nine BarLev2021.holds (alternatives ctx) w = pexCell ctx (nine ∩ w).card := by
  have hk := threshold_nine ctx
  have h1 := GuerriniWehbe2025.pexPlural_subDisjsOfCard_eq_one_iff (w := w)
    (BarLev2021.separating_holds nine nine) (m := nine.card + 1 - ctx.threshold nine) (by omega)
    (by rw [Finset.inter_self]; omega)
  simp only [Finset.inter_self, BarLev2021.mem_atLeast, BarLev2021.count_holds] at h1
  rw [show nine.card + 1 - (nine.card + 1 - ctx.threshold nine) = ctx.threshold nine by omega]
    at h1
  have h2 : pexPlural nine nine BarLev2021.holds (alternatives ctx) w = -1 ↔
      (nine ∩ w).card = 0 := by
    rw [GuerriniWehbe2025.pexPlural_eq_neg_one_iff, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    simp
  unfold pexCell
  split_ifs with h0 hn
  · exact h2.2 h0
  · exact h1.2 hn
  · rcases (by decide : ∀ v : SignType, v = 0 ∨ v = -1 ∨ v = 1)
      (pexPlural nine nine BarLev2021.holds (alternatives ctx) w) with h | h | h
    · exact h
    · exact absurd (h2.1 h) h0
    · exact absurd (h1.1 h) hn

theorem pexCell_universal (n : ℕ) : pexCell .universal n = cell n := by
  have h1 := KrizChemla2015.designated_k3_cell n
  have h0 := KrizChemla2015.designated_lp_cell n
  have hk : AugurzkyEtAl2023.Context.universal.threshold nine = 9 := by
    simp [AugurzkyEtAl2023.Context.threshold, nine]
  unfold pexCell
  rw [hk]
  rcases (by decide : ∀ v : SignType, v = 0 ∨ v = -1 ∨ v = 1) (cell n) with h | h | h <;>
    rw [h] at h0 h1 ⊢ <;> split_ifs <;> simp_all

section Asymmetric

variable (q : NumberTree) [DecidableRel q]

/-- The asymmetric verdict applies `pex` below the quantifier to each boy's definite over the
alternatives the context leaves, projects its presupposition by Strong Kleene and accommodates it
globally, accepting the sentence where it is true. -/
def asymmetric (ctx : AugurzkyEtAl2023.Context) (opened : List ℕ) : Prop :=
  pointwise q (opened.map (pexCell ctx)) = 1

instance (ctx : AugurzkyEtAl2023.Context) (opened : List ℕ) :
    Decidable (asymmetric q ctx opened) :=
  inferInstanceAs (Decidable (_ = _))

/-- Accommodating each boy's presupposition below the quantifier, as (35) does under *no*, the
quantifier ranges over the boys of whom the accommodated reading holds. -/
def localAccommodation (ctx : AugurzkyEtAl2023.Context) (opened : List ℕ) : Prop :=
  holds q (opened.map fun n ↦ decide (pexCell ctx n = 1))

instance (ctx : AugurzkyEtAl2023.Context) (opened : List ℕ) :
    Decidable (localAccommodation q ctx opened) :=
  inferInstanceAs (Decidable (holds q _))

variable {q} (ctx : AugurzkyEtAl2023.Context) (opened : List ℕ)

private theorem resolve_lp_pexCell :
    resolve .lp (opened.map (pexCell ctx)) = resolve .lp (opened.map cell) := by
  simp only [resolve, List.map_map]
  refine List.map_congr_left fun n _ ↦ decide_eq_decide.2 ?_
  rw [Trivalent.Designation.threshold_lp, zero_le_pexCell_iff, KrizChemla2015.designated_lp_cell]

private theorem resolve_k3_pexCell :
    resolve .k3 (opened.map (pexCell ctx)) = resolve ctx.designation (opened.map cell) := by
  simp only [resolve, List.map_map]
  refine List.map_congr_left fun n _ ↦ ?_
  simp [SignType.one_le_iff, pexCell_eq_one_iff, AugurzkyEtAl2023.designated_cell]

theorem asymmetric_iff_of_scopeMonotone (hq : q.ScopeMonotone) :
    asymmetric q ctx opened ↔ reading q (opened.map cell) ctx.designation := by
  rw [asymmetric, KrizChemla2015.pointwise_eq_supervaluation_of_scopeMonotone hq,
    KrizChemla2015.supervaluation_eq_one_iff,
    and_iff_right_of_imp (KrizChemla2015.allReading_imp_someReading hq), allReading, reading,
    resolve_k3_pexCell]
  rfl

/-- In a scope-antitone environment, the asymmetric approach gives the existential reading in every
context ((26), (27)). -/
theorem asymmetric_iff_of_scopeAntitone (hq : q.ScopeAntitone) :
    asymmetric q ctx opened ↔ someReading q (opened.map cell) := by
  rw [asymmetric, KrizChemla2015.pointwise_eq_supervaluation_of_scopeAntitone hq,
    KrizChemla2015.supervaluation_eq_one_iff,
    and_iff_left_of_imp (KrizChemla2015.someReading_imp_allReading hq), someReading, reading,
    resolve_lp_pexCell]
  rfl

-- [augurzky-etal-2023]
theorem asymmetric_iff_implicature [Decidable q.ScopeAntitone]
    (hq : q.ScopeMonotone ∨ q.ScopeAntitone) :
    asymmetric q ctx opened ↔ AugurzkyEtAl2023.implicature q ctx (opened.map cell) := by
  unfold AugurzkyEtAl2023.implicature
  split_ifs with ha
  · exact asymmetric_iff_of_scopeAntitone ctx opened ha
  · exact asymmetric_iff_of_scopeMonotone ctx opened (hq.resolve_right ha)

/-- Accommodated below the quantifier, the asymmetric approach gives the symmetric verdict, so
only a cost of local accommodation keeps its asymmetry (§4.3) ((35)). -/
theorem localAccommodation_iff_symmetric :
    localAccommodation q ctx opened ↔ symmetric q ctx (opened.map cell) := by
  rw [symmetric_iff, reading, localAccommodation, resolve, List.map_map]
  refine iff_of_eq (congrArg _ (List.map_congr_left fun n _ ↦ ?_))
  simp [pexCell_eq_one_iff, AugurzkyEtAl2023.designated_cell]

-- (26)
theorem asymmetric_no_iff : asymmetric NumberTree.no ctx opened ↔ ∀ n ∈ opened, n = 0 := by
  rw [asymmetric_iff_of_scopeAntitone ctx opened NumberTree.scopeAntitone_no, someReading,
    KrizChemla2015.reading_no]
  simp [cell_eq_neg_one_iff]

-- (27)
theorem asymmetric_notAll_iff : asymmetric NumberTree.notAll ctx opened ↔ 0 ∈ opened := by
  rw [asymmetric_iff_of_scopeAntitone ctx opened NumberTree.scopeAntitone_notAll, someReading,
    ← NumberTree.compl_all]
  change ¬ reading NumberTree.all _ _ ↔ _
  rw [KrizChemla2015.reading_all]
  simp [cell_eq_neg_one_iff]

variable {ctx}

-- (28)
theorem asymmetric_all_universal_iff :
    asymmetric NumberTree.all .universal opened ↔ ∀ n ∈ opened, 9 ≤ n := by
  rw [asymmetric_iff_of_scopeMonotone _ opened NumberTree.scopeMonotone_all,
    KrizChemla2015.reading_all]
  simp [AugurzkyEtAl2023.Context.designation, KrizChemla2015.designated_k3_cell]

/-- Without pruning, *exactly two boys opened their presents* says after accommodation that two boys
opened all of theirs and every other boy none (30). -/
theorem asymmetric_exactlyTwo_universal_iff :
    asymmetric (NumberTree.cardinal {2}) .universal opened ↔
      (opened.map cell).count 1 = 2 ∧ (opened.map cell).count 0 = 0 := by
  rw [asymmetric, List.map_congr_left fun n _ ↦ pexCell_universal n]
  exact pointwise_exactlyTwo_eq_one_iff

-- (35)
theorem localAccommodation_no_universal_iff :
    localAccommodation NumberTree.no .universal opened ↔ ∀ n ∈ opened, n < 9 := by
  have hk : AugurzkyEtAl2023.Context.universal.threshold nine = 9 := by
    simp [AugurzkyEtAl2023.Context.threshold, nine]
  simp [localAccommodation, holds, NumberTree.no, List.count_eq_zero, pexCell_eq_one_iff, hk]

end Asymmetric

/-! ### The experiments -/

-- §3.2.1
theorem targets_gap : ∀ p ∈ pictures, ∀ pol ∈ p.targetFor,
    pointwise (sentences p.experiment pol).quantifier.tree p.display = 0 := by
  decide

-- §3.3.1
theorem targets_unanalysed : ∀ p ∈ pictures, p.experiment = .one → p.picture = .target →
    ∀ pol, pol ∉ p.targetFor →
    pointwise (sentences p.experiment pol).quantifier.tree p.display = -1 := by
  decide

theorem controls_bivalent : ∀ p ∈ pictures, p.picture ≠ .target → ∀ pol,
    pointwise (sentences p.experiment pol).quantifier.tree p.display ≠ 0 ∧
      (p.picture = .trueControl →
        pointwise (sentences p.experiment pol).quantifier.tree p.display = 1) ∧
      (p.picture = .falseControl →
        pointwise (sentences p.experiment pol).quantifier.tree p.display = -1) := by
  decide

theorem targets_exactlyTwo : ∀ p ∈ pictures, p.experiment = .three →
    (.positive ∈ p.targetFor → p.display.count 0 = 2 ∧ 1 ∉ p.display) ∧
      (.negative ∈ p.targetFor → p.display.count 1 = 2 ∧ 0 ∈ p.display) := by
  decide

/-- On the symmetric approach every sentence is accepted on its target pictures exactly in its
lax context, Tables 1, 3, 6 and 9. -/
theorem predictions_symmetric : ∀ p ∈ pictures, ∀ pol ∈ p.targetFor, ∀ c : Context,
    symmetric (sentences p.experiment pol).quantifier.tree c.raises p.display ↔
      c = Recoding.lax.context pol := by
  decide

/-- On the asymmetric approach, target pictures are accepted only for the positive sentence in the
prohibiting context (Tables 2, 4, 7 and 10). -/
theorem predictions_asymmetric : ∀ p ∈ pictures, ∀ pol ∈ p.targetFor, ∀ c : Context,
    asymmetric (sentences p.experiment pol).quantifier.tree c.raises p.opened ↔
      pol = .positive ∧ c = .prohibited := by
  decide

/-- The implicature approach as [augurzky-etal-2023] state it treats *exactly two* as it treats
*every*, accepting the negative target of Experiment 3 where the presents are required to be
opened, which the asymmetric approach rejects. -/
theorem implicature_negativeTarget : ∀ p ∈ pictures, p.experiment = .three →
    .negative ∈ p.targetFor →
      AugurzkyEtAl2023.implicature Quantifier.exactlyTwo.tree .universal p.display ∧
        ¬ asymmetric Quantifier.exactlyTwo.tree .universal p.opened := by
  decide

/-! ### The reanalysis and Table 12 -/

/-- Experiments 1 and 2 are those of [augurzky-etal-2023]. -/
def Experiment.ofAugurzky : AugurzkyEtAl2023.Experiment → Experiment
  | .one => .one
  | .two => .two

/-- The terms of the target conditions' models that both papers test. -/
def Effect.ofAugurzky : AugurzkyEtAl2023.Effect → Option Effect
  | .context => some .context
  | .polarity => some .polarity
  | .interaction => some .interaction
  | .contextTerms => none

/-- The reanalysis of Experiments 1 and 2 excludes 4 and 6 participants where
[augurzky-etal-2023] excluded 7 and 10, and changes every χ², but no test's significance at the
.05 level. -/
theorem significant_iff_augurzky : ∀ t ∈ AugurzkyEtAl2023.tests, t.model = .mixed →
    ∀ e ∈ Effect.ofAugurzky t.effect,
      ((tests (.ofAugurzky t.experiment) e).p.Significant (1 / 20) ↔ t.p.Significant (1 / 20)) := by
  decide +kernel

/-- The mean rating of a target condition in a recoded context, from Figures 4 and 6 as recoded
and from Figure 8 at the context the recoding names. -/
def targetMean (x : Experiment) (pol : Polarity) (r : Recoding) : Option ℚ :=
  match x with
  | .three => (meansExactlyTwo.find? fun m ↦
      m.truth = .target ∧ m.polarity = some pol ∧ m.context = r.context pol).map (·.mean.toRat)
  | x => (means.find? fun m ↦
      m.experiment = x ∧ m.polarity = pol ∧ m.recoding = r ∧ m.truth = .target).map
        (·.mean.toRat)

/-- The Likert effect sizes of Table 12 are the lax-minus-strict differences of the target means of
Figures 4, 6 and 8. -/
theorem effectSizes_likert : ∀ x pol, ∃ l ∈ targetMean x pol .lax, ∃ s ∈ targetMean x pol .strict,
    l - s = (effectSizes x pol).likert.toRat := by
  decide +kernel

/-- The log-odds effect sizes of Table 12 are the CONTEXT estimate, plus the interaction for the
positive condition, up to rounding (Tables 5, 8 and 11). -/
theorem effectSizes_logOdds : ∀ x pol,
    |(estimates x .context).beta.toRat +
        (if pol = .positive then (estimates x .interaction).beta.toRat else 0) -
      (effectSizes x pol).logOdds.toRat| ≤ 1 / 100 := by
  decide +kernel

end RomoliEtAl2026
