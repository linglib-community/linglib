module

public import Studies.KrizChemla2015
public import Studies.BarLev2021
public import Linglib.Semantics.Homogeneity.Usable
public import Linglib.Data.Experiments.AugurzkyEtAl2023

/-!
# Augurzky et al. (2023): Putting plural definites into context

A plural definite is homogeneous, *every boy opened his presents* being understood of all his
presents and *no boy opened his presents* of none, and non-maximal: if all that matters is whether
any present was opened, the first sentence passes though some stayed closed. The implicature
approach strengthens an existential definite by an implicature, absent in downward-entailing
scopes, so that pruning yields non-maximality in positive sentences only; the non-implicature
approach gives the sentence a truth-value gap that the question the context raises resolves, for
positive and negative sentences alike. Two picture-verification experiments put the definite under
*every* and *no* (Experiment 1) or *not every* (Experiment 2) while a family rule made it relevant
whether any or whether all presents were opened. Experiment 1 found the context affecting *every*
more than *no*, and Experiment 2 found it affecting *every* and *not every* alike, so each approach
is challenged by one experiment.

## Main results

* `pictures_truth`: the TRUTH VALUE of each picture of Figures 1 and 4 is its sentence's
  supervaluation.
* `nonImplicature_iff`: Križ's usability relative to the context's question is truth at the
  context's resolution; `not_addressesIssue_respected`: the question as §3 states it does not
  serve.
* `mem_reading_iff_designated_cell`: the reading Bar-Lev's pruning selects is that resolution.
* `nonImplicature_nonmaximal_iff`, `implicature_nonmaximal_iff`, `table1`: Tables 1 and 2 on every
  mixed display.
* `implicature_existential_iff`, `krizChemla_asymmetry_of_existential`: in an existential context
  the approaches agree, which yields Križ and Chemla's asymmetry between *every* and *no*.
* `enriched_nonmaximal_iff`: the amendment of §4.2 accepts *every* and *not every* in their lax
  contexts and *no* in neither.
* `exactlyTwo_positive`, `exactlyTwo_negative`: the non-implicature prediction for the test (20).

## Implementation notes

A picture is a display of Križ and Chemla, one trivalent cell per boy. The question §3 states,
whether the family rule was respected, is lifted boy by boy (`Context.issue`). Table 1 is stated
for one boy's nine presents, the model of Bar-Lev's pruning being identified with the cell
(`barePlural_holds_eq_cell`). The verdicts are bivalent, so they register whether the context
changes a judgment and not by how much; the printed tests are reported in docstrings, not
re-thresholded. The text of §3.2.1 describes the true control of *not every* as its mixed picture.

## TODO

* Bar-Lev's cover-based route to non-maximality under negation (footnote 6) is not formalized.
* The test sentences (18) and (19) of §4.2 need disjunctive alternatives and are not modelled.

## References

* [augurzky-etal-2023]
* [kriz-chemla-2015]
* [bar-lev-2021]
* [kriz-2016]
* [kriz-spector-2021]
* [magri-2014]
-/

open Quantifier (NumberTree)

@[expose] public section

namespace AugurzkyEtAl2023

open Trivalent (Designation)
open KrizChemla2015 (Display cell resolve reading someReading allReading supervaluation
  supervaluation_eq_zero_iff supervaluation_eq_designations reading_no)

/-! ### Quantifiers and pictures -/

/-- The number tree each quantifier denotes. -/
def Quantifier.tree : Quantifier → NumberTree
  | .every => NumberTree.all
  | .no => NumberTree.no
  | .notEvery => NumberTree.notAll

instance : (q : Quantifier) → DecidableRel q.tree
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => inferInstanceAs (DecidableRel NumberTree.notAll)

instance : Decidable NumberTree.all.ScopeAntitone := isFalse fun h ↦ Nat.one_ne_zero (h 0 0 rfl)
instance : Decidable NumberTree.no.ScopeAntitone := isTrue NumberTree.scopeAntitone_no
instance : Decidable NumberTree.notAll.ScopeAntitone := isTrue NumberTree.scopeAntitone_notAll

/-- *no* and *not every* are downward entailing; *every* is not. -/
instance : (q : Quantifier) → Decidable q.tree.ScopeAntitone
  | .every => inferInstanceAs (Decidable NumberTree.all.ScopeAntitone)
  | .no => inferInstanceAs (Decidable NumberTree.no.ScopeAntitone)
  | .notEvery => inferInstanceAs (Decidable NumberTree.notAll.ScopeAntitone)

/-- A picture is the display giving each boy *he opened his presents* over his nine. -/
def Picture.display (p : Picture) : Display := p.opened.map cell

/-- The trivalent value a level of TRUTH VALUE names, a mixed picture being one on which the
sentence's two resolutions disagree. -/
def Truth.value : Truth → SignType
  | .trueControl => 1
  | .falseControl => (-1)
  | .mixed => 0

/-- The TRUTH VALUE of every picture of Figures 1 and 4 is the supervaluation of its sentence. -/
theorem pictures_truth :
    ∀ p ∈ pictures, supervaluation p.quantifier.tree p.display = p.truth.value := by
  decide

/-! ### Contexts -/

/-- The resolution of a boy's partially opened presents that each context makes. -/
def Context.designation : Context → Designation
  | .existential => .lp
  | .universal => .k3

/-- The question the context raises about the boys, which of them opened any of their presents
or which of them opened all. -/
def Context.issue (ctx : Context) : Setoid Display := Setoid.ker (resolve ctx.designation)

/-- Over one boy the issue is the partition of (12) or (13). -/
theorem issue_singleton (ctx : Context) (v v' : SignType) :
    ctx.issue [v] [v'] ↔ (ctx.designation.threshold ≤ v ↔ ctx.designation.threshold ≤ v') := by
  simp [Setoid.ker_def, resolve]

/-- A resolution, read back as a display, resolves to itself at every standard. -/
private theorem resolve_map_ofProp (δ : Designation) (c : List Bool) :
    resolve δ (c.map (fun b : Bool ↦ SignType.ofProp b)) = c := by
  simp [resolve, List.map_map, Function.comp_def, Trivalent.Designation.threshold_le_ofProp_iff]

/-! ### The non-implicature approach -/

section NonImplicature

variable (q : NumberTree)

/-- Under any question at least as fine as the polar question on the reading at `δ` and at most
as fine as the resolution at `δ`, a trivalent sentence true only where that reading holds, false
only where it fails, and true on a resolution read back as a display where the quantifier holds
of it, is usable exactly where that reading holds. -/
theorem usable_iff_reading_of {S : Display → SignType} {δ : Designation}
    (htrue : ∀ d, S d = 1 → reading q d δ) (hfalse : ∀ d, S d = -1 → ¬ reading q d δ)
    (hres : ∀ c, KrizChemla2015.holds q c → S (c.map fun b : Bool ↦ SignType.ofProp b) = 1)
    {Q : Setoid Display} (h₁ : Setoid.ker (resolve δ) ≤ Q) (h₂ : Q.Decides {d | reading q d δ})
    (d : Display) : Homogeneity.usable Q S d ↔ reading q d δ := by
  have hcell : ∀ {d d'}, Q d d' → (reading q d δ ↔ reading q d' δ) := fun h ↦ h₂.iff h
  exact ⟨fun ⟨_, ⟨d', hd', h'⟩, _⟩ ↦ (hcell hd').2 (htrue d' h'), fun h ↦
    ⟨fun hf ↦ hfalse d hf h, ⟨(resolve δ d).map (fun b : Bool ↦ SignType.ofProp b),
      h₁ (Setoid.ker_def.2 (resolve_map_ofProp δ _).symm), hres _ h⟩,
      fun ⟨d₁, d₂, h₁₂, ht, hf⟩ ↦ hfalse d₂ hf ((hcell h₁₂).1 (htrue d₁ ht))⟩⟩

variable [DecidableRel q]

/-- Under any question at least as fine as the polar question on the reading at `δ` and at most
as fine as the resolution at `δ`, the trivalent sentence is usable exactly where that reading
holds. -/
theorem usable_iff_reading {Q : Setoid Display} {δ : Designation}
    (h₁ : Setoid.ker (resolve δ) ≤ Q) (h₂ : Q.Decides {d | reading q d δ}) (d : Display) :
    Homogeneity.usable Q (supervaluation q) d ↔ reading q d δ := by
  refine usable_iff_reading_of q (fun d' h ↦ ?_) (fun d' h ↦ ?_) (fun c h ↦ ?_) h₁ h₂ d
  · rw [supervaluation_eq_designations, SignType.supervaluation_eq_one_iff] at h
    exact h δ (Finset.mem_univ δ)
  · rw [supervaluation_eq_designations, SignType.supervaluation_eq_neg_one_iff] at h
    exact h.2 δ (Finset.mem_univ δ)
  · rw [supervaluation_eq_designations, SignType.supervaluation_eq_one_iff]
    intro δ' _
    rw [reading, resolve_map_ofProp]
    exact h

/-- The non-implicature verdict is the usability of the trivalent sentence at the display relative
to the question the context raises. -/
def nonImplicature (ctx : Context) (d : Display) : Prop :=
  Homogeneity.usable ctx.issue (supervaluation q) d

/-- The non-implicature verdict is truth at the resolution the context makes. -/
theorem nonImplicature_iff (ctx : Context) (d : Display) :
    nonImplicature q ctx d ↔ reading q d ctx.designation :=
  usable_iff_reading q le_rfl (fun _ _ h ↦ Setoid.polar_iff.2 <|
    show reading q _ _ ↔ reading q _ _ by rw [reading, reading, Setoid.ker_def.1 h]) d

instance (ctx : Context) (d : Display) : Decidable (nonImplicature q ctx d) :=
  decidable_of_iff _ (nonImplicature_iff q ctx d).symm

/-- Under the outer negation of a quantifier the verdict is negated in every context. -/
theorem nonImplicature_compl (ctx : Context) (d : Display) :
    nonImplicature qᶜ ctx d ↔ ¬ nonImplicature q ctx d := by
  rw [nonImplicature_iff, nonImplicature_iff]
  rfl

variable {q} {d : Display}

/-- A mixed picture for a scope-monotone quantifier is accepted exactly in the existential
context. -/
theorem nonImplicature_existential_of_scopeMonotone (hq : q.ScopeMonotone)
    (hd : supervaluation q d = 0) (ctx : Context) :
    nonImplicature q ctx d ↔ ctx = .existential := by
  have h := supervaluation_eq_zero_iff.1 hd
  have h' := KrizChemla2015.allReading_imp_someReading (d := d) hq
  rw [nonImplicature_iff]
  cases ctx <;> simp only [Context.designation, reduceCtorEq, iff_true, iff_false] <;> tauto

/-- A mixed picture for a scope-antitone quantifier is accepted exactly in the universal
context. -/
theorem nonImplicature_universal_of_scopeAntitone (hq : q.ScopeAntitone)
    (hd : supervaluation q d = 0) (ctx : Context) :
    nonImplicature q ctx d ↔ ctx = .universal := by
  have h := supervaluation_eq_zero_iff.1 hd
  have h' := KrizChemla2015.someReading_imp_allReading (d := d) hq
  rw [nonImplicature_iff]
  cases ctx <;> simp only [Context.designation, reduceCtorEq, iff_true, iff_false] <;> tauto

end NonImplicature

/-- The family rule is respected where no present was opened, or where all were; the question
whether it was is the question §3 states. -/
def Context.respected : Context → Set Display
  | .existential => {d | ∀ v ∈ d, v = -1}
  | .universal => {d | ∀ v ∈ d, v = 1}

/-- Under the question whether the rule was respected, *every boy opened his presents* does not
address the existential issue, nor *no boy opened his presents* the universal one, so neither is
usable anywhere and the question that yields Table 2 is the boy-by-boy one. -/
theorem not_addressesIssue_respected :
    ¬ Homogeneity.addressesIssue (Setoid.polar Context.existential.respected)
        (supervaluation NumberTree.all) ∧
      ¬ Homogeneity.addressesIssue (Setoid.polar Context.universal.respected)
        (supervaluation NumberTree.no) := by
  refine ⟨fun h ↦ h ⟨[1, 1], [-1, 1], ?_, by decide, by decide⟩,
    fun h ↦ h ⟨[-1, -1], [1, -1], ?_, by decide, by decide⟩⟩ <;>
  exact Setoid.polar_iff.2 (by simp [Context.respected])

/-! ### The implicature approach -/

section Implicature

variable (q : NumberTree) [Decidable q.ScopeAntitone]

/-- The implicature verdict. In a downward-entailing scope exhaustification is vacuous and the
definite keeps its existential literal meaning; elsewhere each boy's definite is exhaustified
over the alternatives the context leaves, to the threshold reading the context's question
selects, which is its resolution at the context's standard (`mem_reading_iff_designated_cell`). -/
def implicature (ctx : Context) (d : Display) : Prop :=
  if q.ScopeAntitone then someReading q d else reading q d ctx.designation

section

variable [DecidableRel q]

instance (ctx : Context) (d : Display) : Decidable (implicature q ctx d) := by
  unfold implicature; infer_instance

variable {q} {d : Display}

/-- Wherever implicatures arise the two approaches agree. -/
theorem implicature_iff_nonImplicature (h : ¬ q.ScopeAntitone) (ctx : Context) :
    implicature q ctx d ↔ nonImplicature q ctx d := by
  rw [nonImplicature_iff]; simp [implicature, h]

end

variable {q} {d : Display}

/-- Under a downward-entailing quantifier the implicature verdict ignores the context. -/
theorem implicature_context_free (h : q.ScopeAntitone) (ctx ctx' : Context) :
    implicature q ctx d ↔ implicature q ctx' d := by
  simp [implicature, h]

variable [DecidableRel q]

/-- In the existential context the two verdicts agree on every quantifier, both being the
existential resolution, so an experiment that does not control the context cannot separate the
approaches (§2). -/
theorem implicature_existential_iff :
    implicature q .existential d ↔ nonImplicature q .existential d := by
  rw [nonImplicature_iff]
  by_cases h : q.ScopeAntitone <;> simp [implicature, h, Context.designation]

/-- The implicature approach rejects every mixed picture of a downward-entailing quantifier. -/
theorem not_implicature_of_scopeAntitone (hq : q.ScopeAntitone)
    (hd : supervaluation q d = 0) (ctx : Context) : ¬ implicature q ctx d := by
  have h := supervaluation_eq_zero_iff.1 hd
  have h' := KrizChemla2015.someReading_imp_allReading (d := d) hq
  simp only [implicature, hq, ite_true]
  tauto

/-- The implicature approach accepts a mixed picture of a scope-monotone quantifier exactly in
the existential context. -/
theorem implicature_existential_of_scopeMonotone (hq : q.ScopeMonotone)
    (hd : supervaluation q d = 0) (ctx : Context) :
    implicature q ctx d ↔ ctx = .existential := by
  have h := supervaluation_eq_zero_iff.1 hd
  have h' := KrizChemla2015.allReading_imp_someReading (d := d) hq
  have hq' : ¬ q.ScopeAntitone := fun ha ↦
    h (iff_of_true (by tauto) (KrizChemla2015.someReading_imp_allReading ha (by tauto)))
  rw [implicature_iff_nonImplicature hq']
  exact nonImplicature_existential_of_scopeMonotone hq hd ctx

end Implicature

/-! ### Table 2 and the recoding of Figures 3 and 5 -/

/-- The context favouring a non-maximal reading, as Figures 3 and 5 recode CONTEXT, is the
existential one for *every* and the universal one for the negative quantifiers. -/
def Quantifier.lax : Quantifier → Context
  | .every => .existential
  | _ => .universal

variable {d : Display}

/-- On the non-implicature approach every quantifier's mixed picture is accepted exactly in its lax
context (Table 2), so the context affects every quantifier alike and no interaction of context
and polarity is predicted. Experiment 2 found none (χ²(1) = 2.1, p = .15, §3.2.2), but Experiment
1 found one (χ²(1) = 11, p < .001, §3.1.2). -/
theorem nonImplicature_nonmaximal_iff (q : Quantifier) (hd : supervaluation q.tree d = 0)
    (ctx : Context) : nonImplicature q.tree ctx d ↔ ctx = q.lax := by
  cases q
  · exact nonImplicature_existential_of_scopeMonotone NumberTree.scopeMonotone_all hd ctx
  · exact nonImplicature_universal_of_scopeAntitone NumberTree.scopeAntitone_no hd ctx
  · exact nonImplicature_universal_of_scopeAntitone NumberTree.scopeAntitone_notAll hd ctx

/-- On the implicature approach only *every*'s mixed picture is accepted, in its lax context
(Table 2), so an interaction of context and polarity is predicted in both experiments. Experiment 1
found it (χ²(1) = 11, p < .001, §3.1.2), though with a context effect on *no* that the approach
does not predict, and Experiment 2 did not (χ²(1) = 2.1, p = .15, §3.2.2). -/
theorem implicature_nonmaximal_iff (q : Quantifier) (hd : supervaluation q.tree d = 0)
    (ctx : Context) : implicature q.tree ctx d ↔ q = .every ∧ ctx = q.lax := by
  cases q
  · exact (implicature_existential_of_scopeMonotone (q := Quantifier.every.tree)
      NumberTree.scopeMonotone_all hd ctx).trans (by simp [Quantifier.lax])
  · exact iff_of_false (not_implicature_of_scopeAntitone (q := Quantifier.no.tree)
      NumberTree.scopeAntitone_no hd ctx) (by simp)
  · exact iff_of_false (not_implicature_of_scopeAntitone (q := Quantifier.notEvery.tree)
      NumberTree.scopeAntitone_notAll hd ctx) (by simp)

/-- Table 1 is Table 2 over one boy. In a mixed scenario the positive sentence is accepted exactly
in the existential context on both approaches, and the negative one is rejected in both contexts
on the implicature approach and accepted exactly in the universal one on the other. -/
theorem table1 (ctx : Context) :
    (implicature NumberTree.all ctx [0] ↔ ctx = .existential) ∧
      ¬ implicature NumberTree.notAll ctx [0] ∧
      (nonImplicature NumberTree.all ctx [0] ↔ ctx = .existential) ∧
      (nonImplicature NumberTree.notAll ctx [0] ↔ ctx = .universal) :=
  ⟨(implicature_nonmaximal_iff (d := [0]) .every (by decide) ctx).trans
      (by simp [Quantifier.lax]),
    fun h ↦ by
      simpa using (implicature_nonmaximal_iff (d := [0]) .notEvery (by decide) ctx).1 h,
    nonImplicature_nonmaximal_iff (d := [0]) .every (by decide) ctx,
    nonImplicature_nonmaximal_iff (d := [0]) .notEvery (by decide) ctx⟩

/-! ### Križ and Chemla's asymmetry under an accommodated existential context (§2) -/

/-- The faulty items of Križ and Chemla were coded FALSE. -/
private theorem krizChemla_faulty_clearlyFalse :
    ∀ i ∈ KrizChemla2015.items, i.status = .faulty → i.condition = .clearlyFalse := by
  decide

/-- With an existential context accommodated throughout, the non-implicature approach accepts
every GAP item of *every* and rejects every GAP item of *no* in Križ and Chemla's experiments,
the asymmetry they found. -/
theorem krizChemla_asymmetry_of_existential :
    ∀ i ∈ KrizChemla2015.items, i.condition = .gap → i.embedding = .all ∨ i.embedding = .no →
      (nonImplicature i.embedding.tree .existential i.display ↔ i.embedding = .all) := by
  intro i hi hc he
  have hm : i ≠ KrizChemla2015.misprinted := fun h ↦ by
    rcases he with he | he <;> simp [h, KrizChemla2015.misprinted] at he
  have hs : i.status ≠ .faulty := fun h ↦ by
    simp [krizChemla_faulty_clearlyFalse i hi h] at hc
  obtain ⟨hw, hst⟩ := KrizChemla2015.items_variants i (List.mem_append_left _ hi) hs hm
  have hgap : supervaluation i.embedding.tree i.display = 0 :=
    (KrizChemla2015.supervaluation_eq_zero_iff_weak _ _).2 (by rw [hw, hst]; simp [hc])
  rcases he with he | he <;> rw [he] at hgap ⊢
  · exact iff_of_true ((nonImplicature_existential_of_scopeMonotone (q := NumberTree.all)
      NumberTree.scopeMonotone_all hgap _).2 rfl) rfl
  · exact iff_of_false (fun h ↦ by simpa using (nonImplicature_universal_of_scopeAntitone
      (q := NumberTree.no) NumberTree.scopeAntitone_no hgap _).1 h) (by decide)

/-! ### The boy-wise strengthening is the reading pruning selects -/

section BarLev

open BarLev2021 (atLeast IsReading)

variable {α : Type*} (x : Finset α)

/-- The number of presents the context's question asks about is one, or all of them. -/
def Context.threshold : Context → ℕ
  | .existential => 1
  | .universal => x.card

section

variable [DecidableEq α]

/-- The questions (12) and (13) in the model whose worlds are the sets of presents opened. -/
def Context.question (ctx : Context) : Setoid (Finset α) :=
  Setoid.polar (atLeast x x BarLev2021.holds (ctx.threshold x))

end

variable {x}

private theorem threshold_pos (hx : x.Nonempty) (ctx : Context) : 0 < ctx.threshold x := by
  cases ctx
  · exact Nat.one_pos
  · exact Finset.card_pos.2 hx

private theorem threshold_le (hx : x.Nonempty) (ctx : Context) : ctx.threshold x ≤ x.card := by
  cases ctx
  · exact Finset.card_pos.2 hx
  · exact le_rfl

variable [DecidableEq α]

/-- The context's question selects, in the sense of pruning, the threshold reading at the
number of presents it asks about. -/
theorem isReading_question (hx : x.Nonempty) (ctx : Context) :
    IsReading x x BarLev2021.holds (ctx.question x)
      (atLeast x x BarLev2021.holds (ctx.threshold x)) :=
  BarLev2021.isReading_polar_atLeast_holds x x (threshold_pos hx ctx) (by
    rw [Finset.inter_self]; exact threshold_le hx ctx)

/-- A boy's nine presents, the objects of a cell. -/
def nine : Finset ℕ := Finset.range 9

/-- The resolution a context makes of a boy's cell is the threshold its question selects for his
nine presents. -/
theorem designated_cell (ctx : Context) (n : ℕ) :
    ctx.designation.threshold ≤ cell n ↔ ctx.threshold nine ≤ n := by
  cases ctx
  · exact KrizChemla2015.designated_lp_cell n
  · rw [Context.threshold, nine, Finset.card_range]
    exact SignType.one_le_iff.trans (KrizChemla2015.designated_k3_cell n)

/-- The reading pruning selects for a boy's presents under the context's question holds of the
presents he opened exactly when the context's standard designates his cell. -/
theorem mem_reading_iff_designated_cell (ctx : Context) {r : Set (Finset ℕ)}
    (hr : IsReading nine nine BarLev2021.holds (ctx.question nine) r) (w : Finset ℕ) :
    w ∈ r ↔ ctx.designation.threshold ≤ (cell (nine ∩ w).card) := by
  rw [hr.unique (isReading_question ⟨0, by simp [nine]⟩ ctx), BarLev2021.mem_atLeast,
    BarLev2021.count_holds, Finset.inter_self, designated_cell]

/-- A boy's trivalent value in the model whose worlds are the sets of presents opened is his
cell at the number he opened. -/
theorem barePlural_holds_eq_cell (w : Finset ℕ) :
    Homogeneity.barePlural BarLev2021.holds nine w = cell (nine ∩ w).card := by
  have h1 : Homogeneity.barePlural BarLev2021.holds nine w = 1 ↔
      cell (nine ∩ w).card = 1 := by
    rw [KrizChemla2015.designated_k3_cell, Homogeneity.barePlural,
      SignType.supervaluation_eq_one_iff]
    constructor
    · intro h
      rw [Finset.inter_eq_left.2 fun a ha ↦ h a ha]
      simp [nine]
    · intro h a ha
      have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : nine ∩ w ⊆ nine)
        (by simpa [nine] using h)
      rw [← this] at ha
      exact (Finset.mem_inter.1 ha).2
  have h2 : Homogeneity.barePlural BarLev2021.holds nine w = -1 ↔
      cell (nine ∩ w).card = -1 := by
    rw [← not_iff_not, ← Ne, ← Ne, ← SignType.nonneg_iff_ne_neg_one (a := cell _),
      KrizChemla2015.designated_lp_cell, Homogeneity.barePlural, Ne,
      SignType.supervaluation_eq_neg_one_iff, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
      ← Ne, ← Finset.nonempty_iff_ne_empty]
    simp only [nine, BarLev2021.holds, Finset.Nonempty, Finset.mem_inter, Finset.mem_range,
      not_and, not_forall, not_not, exists_prop]
    exact ⟨fun h ↦ h ⟨0, by omega⟩, fun h _ ↦ h⟩
  rcases h₁ : Homogeneity.barePlural BarLev2021.holds nine w with _ | _ | _ <;>
    rcases h₂ : cell (nine ∩ w).card with _ | _ | _ <;> simp_all

end BarLev

/-! ### The implicature approach amended (§4.2) -/

/-- The quantifier together with its own scalar implicature (16) strengthens *not every* by the
denial of its stronger alternative *no*. The other quantifiers have no stronger alternative to
deny. -/
def Quantifier.enriched : Quantifier → NumberTree
  | .notEvery => NumberTree.notAll ⊓ NumberTree.some
  | q => q.tree

instance : (q : Quantifier) → DecidableRel q.enriched
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => fun a b ↦ inferInstanceAs (Decidable (a ≠ 0 ∧ b ≠ 0))

/-- Together with its implicature *not every* is non-monotonic, the observation of §4.2. -/
theorem enriched_notEvery_nonmonotone :
    ¬ Quantifier.notEvery.enriched.ScopeMonotone ∧ ¬ Quantifier.notEvery.enriched.ScopeAntitone :=
  ⟨fun h ↦ (h 0 1 ⟨one_ne_zero, one_ne_zero⟩).1 rfl,
    fun h ↦ (h 1 0 ⟨one_ne_zero, one_ne_zero⟩).2 rfl⟩

instance : (q : Quantifier) → Decidable q.enriched.ScopeAntitone
  | .every => isFalse fun h ↦ Nat.one_ne_zero (h 0 0 rfl)
  | .no => isTrue NumberTree.scopeAntitone_no
  | .notEvery => isFalse enriched_notEvery_nonmonotone.2

private theorem reading_inf {p q : NumberTree} (d : Display) (δ : Designation) :
    reading (p ⊓ q) d δ ↔ reading p d δ ∧ reading q d δ := Iff.rfl

private theorem reading_some (d : Display) (δ : Designation) :
    reading NumberTree.some d δ ↔ ∃ v ∈ d, δ.threshold ≤ v := by
  rw [← NumberTree.compl_no, show reading NumberTree.noᶜ d δ ↔ ¬ reading NumberTree.no d δ from
    Iff.rfl, reading_no]
  simp

/-- On the mixed pictures of the experiments, where some boy opened all of his presents, the amended
implicature approach accepts *every* and *not every* exactly in their lax contexts and *no* in
neither. It thus predicts an interaction of context and polarity in Experiment 1 and none in
Experiment 2, the outcome of both (§4.2). -/
theorem enriched_nonmaximal_iff (q : Quantifier) (hd : supervaluation q.tree d = 0)
    (ht : 1 ∈ d) (ctx : Context) :
    implicature q.enriched ctx d ↔ q ≠ .no ∧ ctx = q.lax := by
  cases q
  · exact (implicature_existential_of_scopeMonotone (q := Quantifier.every.enriched)
      NumberTree.scopeMonotone_all hd ctx).trans (by simp [Quantifier.lax])
  · exact iff_of_false (not_implicature_of_scopeAntitone (q := Quantifier.no.enriched)
      NumberTree.scopeAntitone_no hd ctx) (by simp)
  · have h := supervaluation_eq_zero_iff.1 hd
    have h' := KrizChemla2015.someReading_imp_allReading (d := d) NumberTree.scopeAntitone_notAll
    have hk3 : reading NumberTree.some d .k3 := (reading_some d .k3).2 ⟨_, ht, by simp⟩
    have hne : ¬ (NumberTree.notAll ⊓ NumberTree.some).ScopeAntitone :=
      enriched_notEvery_nonmonotone.2
    simp only [Quantifier.tree] at h
    simp only [implicature, Quantifier.enriched, hne, ite_false, reading_inf]
    cases ctx <;> simp only [Context.designation, Quantifier.lax, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and, iff_false, iff_true] <;> tauto

/-! ### The proposed test (§4.3) -/

private theorem count_resolve_lp (d : Display) :
    (resolve .lp d).count true = d.count 1 + d.count 0 := by
  induction d with
  | nil => rfl
  | cons v d ih => cases v <;> simp [resolve] at ih ⊢ <;> omega

private theorem count_resolve_k3 (d : Display) : (resolve .k3 d).count true = d.count 1 := by
  induction d with
  | nil => rfl
  | cons v d ih => cases v <;> simp [resolve] at ih ⊢ <;> omega

private theorem reading_cardinal {s : Set ℕ} [DecidablePred (· ∈ s)] (d : Display)
    (δ : Designation) : reading (NumberTree.cardinal s) d δ ↔ (resolve δ d).count true ∈ s :=
  Iff.rfl

/-- (20) in a mixed scenario for its positive part, where two boys opened some but not all of
their presents and the others none, is accepted exactly in the existential context. -/
theorem exactlyTwo_positive (h₂ : d.count 0 = 2) (ht : 1 ∉ d) (ctx : Context) :
    nonImplicature (NumberTree.cardinal {2}) ctx d ↔ ctx = .existential := by
  have h0 := List.count_eq_zero.2 ht
  rw [nonImplicature_iff]
  cases ctx <;>
    simp [Context.designation, reading_cardinal, count_resolve_lp, count_resolve_k3, h₂, h0]

/-- (20) in a mixed scenario for its negative part, where two boys opened all of their presents
and some opened some but not all, is accepted exactly in the universal context. -/
theorem exactlyTwo_negative (h₂ : d.count 1 = 2) (hi : 0 ∈ d) (ctx : Context) :
    nonImplicature (NumberTree.cardinal {2}) ctx d ↔ ctx = .universal := by
  have h0 := List.count_pos_iff.2 hi
  rw [nonImplicature_iff]
  cases ctx <;> simp [Context.designation, reading_cardinal, count_resolve_lp, count_resolve_k3, h₂]
  omega

end AugurzkyEtAl2023
