module

public import Eval.Projection.Chemla2009a
public import Eval.Projection.ChemlaSchlenker2012

/-!
# Limited Symmetry in quantified sentences

Kalomoiros states Limited Symmetry for the propositional fragment. Schlenker's comments on it apply
the constraint to quantified sentences, and the case studies accompanying Chemla, Spector,
Kalomoiros and Schlenker's Co-Linguistics paper derive the predictions by machine for more
quantifiers. Neither result is published, so this file records them as theory under development.

A trigger in the restrictor of `(Q _ . R)` is followed by two parsing points: the end of the
restrictor, where every scope is a good final, and the end of the sentence, where the only good
final is the sentence itself. Limited Symmetry requires the presupposition to be stably
transparent at both (`RestrictorLS`). It is therefore implied by incremental Transparency, which
consults every scope at once, and it implies symmetric Transparency, which consults the sentence
alone. With the restrictor negated, `(Q not _ . R)`, both Transparencies are unchanged, since
transparency is invariant under negating the gap (`Presupposition.transparent_image_compl_iff`).

In the restrictor's own position Limited Symmetry coincides with incremental Transparency for
every quantifier whose first row is not constant: both require every individual to satisfy the
presupposition (`restrictorLS_iff`). In a negated restrictor it coincides with symmetric
Transparency for every quantifier constant on no row above the first, since a nonempty negated
restriction is then never stable at the end of the restrictor (`restrictorLS_neg_iff`). For
*some*, *no* and *every* this is the summary table of Schlenker's comments
(`some_table`, `no_table`, `every_table`): local negation is where Limited Symmetry regains the
symmetric predictions, and where it departs from incremental Transparency.

The constraint extends to a trigger anywhere in a quantified clause as Kalomoiros's constraint on
the clause's occurrences (`Kalomoiros2023.LimitedSymmetry`, `QuantifiedClause.occurrences`). The
parsing points after the trigger are those of the string of the argument that holds it, each
followed by every good final of the clause, and then the end of the sentence
(`QuantifiedClause.Env.continuations`). For a trigger that is the restrictor, or its negation, these
are the two parsing points above (`limitedSymmetry_trigger_iff`, `limitedSymmetry_not_trigger_iff`).
With Kalomoiros's constraint on formulas, this makes a theory that `Eval` scores like a registered
account (`limitedSymmetry`). It is right on every tested cell of Chemla and Schlenker's inferential
experiments, and on Chemla's first experiment it shares Transparency's verdicts: wrong with every
presupposition accommodated in the context, right by Chemla's stipulations and by his one-step rule
(`verdict_chemla2009a`).

## Main statements

* `restrictorLS_iff`, `restrictorLS_neg_iff`: in a restrictor Limited Symmetry is incremental
  Transparency, in a negated restrictor symmetric Transparency.
* `some_table`, `no_table`, `every_table`: the predictions for *some*, *no* and *every*.
* `verdict_chemlaSchlenker2012`, `verdict_chemla2009a`: the verdicts on the recorded experiments.

## Implementation notes

* Provenance. The table's predictions are Schlenker's, derived by hand. The case studies of the
  Co-Linguistics paper report them confirmed by machine for these and further quantifiers, and
  state the relations between the theories as theorems for the quantifiers they consider. Here the
  two coincidences are proved for every quantifier on van Benthem's tree whose rows satisfy the
  stated non-constancy conditions.
* The domain is a finite type, the same at every world, and the gap of a restrictor denotes a set
  of world–individual pairs, as in `Presupposition.restrictorTruth`.
* The constraint on quantified clauses is this file's generalization of the two parsing points of
  Schlenker's comments, checked against them for the triggers those comments consider.

## References

* [kalomoiros-2023]
* [schlenker-2025]
* [chemla-spector-kalomoiros-schlenker-2026]
* [schlenker-2009]
-/

@[expose] public section

namespace Lab.Colinguistics

open Presupposition Quantifier

variable {W E : Type*}

/-- The truth set of `(Q not _ . R)` as a function of the denotation of the negated restrictor. -/
def negRestrictorTruth (q : NumberTree) (R : W → E → Prop) (d : Set (W × E)) : Set W :=
  restrictorTruth q R dᶜ

/-- Limited Symmetry for a trigger in a restrictor, with `r R` the truth set of the sentence as a
function of the restrictor when the scope is `R`. The presupposition is stably transparent at the
end of the restrictor, where every scope is a good final, and at the end of the sentence, where
the only good final is the sentence itself. -/
def RestrictorLS (r : (W → E → Prop) → Set (W × E) → Set W) (R : W → E → Prop) (C : Set W)
    (π : Set (W × E)) : Prop :=
  StablyTransparent C (Set.range r) π ∧ StablyTransparent C {r R} π

variable {r : (W → E → Prop) → Set (W × E) → Set W} {R : W → E → Prop} {C : Set W}
  {π : Set (W × E)}

/-! ### Between the two Transparencies -/

/-- Incremental Transparency implies Limited Symmetry, as Schlenker's comments observe. -/
theorem RestrictorLS.of_transparent (h : Transparent C (Set.range r) π) : RestrictorLS r R C π :=
  ⟨h.stablyTransparent,
    (h.anti (Set.singleton_subset_iff.2 (Set.mem_range_self R))).stablyTransparent⟩

/-- Limited Symmetry implies symmetric Transparency. -/
theorem RestrictorLS.transparent (h : RestrictorLS r R C π) : Transparent C {r R} π :=
  stablyTransparent_singleton_iff.1 h.2

/-- Negating the restrictor leaves incremental Transparency unchanged. -/
theorem transparent_range_neg_iff {q : NumberTree} :
    Transparent C (Set.range (negRestrictorTruth q)) π ↔
      Transparent C (Set.range (restrictorTruth q)) π := by
  rw [← transparent_image_compl_iff (env := Set.range (restrictorTruth q)), ← Set.range_comp]
  rfl

/-- Negating the restrictor leaves symmetric Transparency unchanged. -/
theorem transparent_neg_iff {q : NumberTree} :
    Transparent C {negRestrictorTruth q R} π ↔ Transparent C {restrictorTruth q R} π := by
  rw [← transparent_image_compl_iff (env := {restrictorTruth q R}), Set.image_singleton]
  rfl

/-! ### Stability of a restrictor -/

/-- A restrictor with no individual gives the quantifier its value at the origin of the tree. -/
private theorem toGQ_of_forall_not {q : NumberTree} {X : E → Prop} (hX : ∀ e, ¬ X e)
    (B : E → Prop) :
    q.toGQ X B ↔ q 0 0 := by
  have h₁ : {x | X x ∧ ¬ B x} = ∅ := Set.eq_empty_of_forall_notMem fun e h ↦ hX e h.1
  have h₂ : {x | X x ∧ B x} = ∅ := Set.eq_empty_of_forall_notMem fun e h ↦ hX e h.1
  rw [NumberTree.toGQ_apply, h₁, h₂, Set.ncard_empty]

section Stable

variable [Finite E] {q : NumberTree}

/-- A restrictor with an individual on whose row the quantifier is not constant gives values that
depend on the scope, so it is stable for no truth value. -/
private theorem not_stable {X : E → Prop} {e : E} (he : X e)
    (hc : ¬ q.ConstantOnRow {x | X x}.ncard) {c : Prop} (h : ∀ B, q.toGQ X B ↔ c) : False :=
  hc ((NumberTree.dependsOn_toGQ_compl_singleton_iff X e).1
    (fun B B' _ ↦ propext ((h B).trans (h B').symm)) he)

/-- In a restrictor, incremental Transparency requires every individual to satisfy the
presupposition, for a quantifier whose first row is not constant. -/
theorem transparent_range_restrictorTruth_iff (h1 : ¬ q.ConstantOnRow 1) :
    Transparent C (Set.range (restrictorTruth q)) π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π := by
  rw [transparent_restrictorTruth_iff]
  refine ⟨fun h w hw e ↦ h (fun hc ↦ h1 fun a b a' b' hab hab' ↦
    hc a b a' b' ?_ ?_) w hw e, fun h _ ↦ h⟩ <;>
  · have := Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨e⟩, inferInstance⟩); omega

/-- In a restrictor, Limited Symmetry coincides with incremental Transparency, for a quantifier
whose first row is not constant: both require every individual to satisfy the presupposition. -/
theorem restrictorLS_iff (h1 : ¬ q.ConstantOnRow 1) :
    RestrictorLS (restrictorTruth q) R C π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π := by
  refine ⟨fun h w hw e ↦ by_contra fun he ↦ ?_, fun h ↦
    .of_transparent ((transparent_range_restrictorTruth_iff h1).2 h)⟩
  have hX : ∀ e', ¬ (w, e') ∈ π ⊓ {(w, e)} := fun e' ⟨hπ, he'⟩ ↦ by
    rw [Set.mem_singleton_iff] at he'
    obtain rfl := (Prod.ext_iff.1 he').2
    exact he hπ
  have h0 (B : W → E → Prop) : w ∈ restrictorTruth q B (π ⊓ {(w, e)}) ↔ q 0 0 :=
    toGQ_of_forall_not hX (B w)
  have hrow : ¬ q.ConstantOnRow {x | (w, x) ∈ ({(w, e)} : Set (W × E))}.ncard := by
    rwa [show {x | (w, x) ∈ ({(w, e)} : Set (W × E))} = {e} from Set.ext fun x ↦ by simp,
      Set.ncard_singleton]
  have hrange : ∀ c : Prop, (∀ B : E → Prop,
      w ∈ restrictorTruth q (fun _ ↦ B) {(w, e)} ↔ c) → False := fun c hc ↦
    not_stable (X := fun x ↦ (w, x) ∈ ({(w, e)} : Set (W × E))) rfl hrow hc
  obtain ⟨ht, hf⟩ := h.1 {(w, e)} w hw
  by_cases hq : q 0 0
  · have := ht (Set.forall_mem_range.2 fun B ↦ (h0 B).2 hq)
    exact hrange True fun B ↦ iff_true_intro (this _ (Set.mem_range_self _))
  · have := hf (Set.forall_mem_range.2 fun B hB ↦ hq ((h0 B).1 hB))
    exact hrange False fun B ↦ iff_false_intro (this _ (Set.mem_range_self _))

/-- In a negated restrictor, Limited Symmetry coincides with symmetric Transparency, for a
quantifier constant on no row above the first: a negated restriction with an individual is then
stable at the end of the restrictor for no truth value, so that check is vacuous. -/
theorem restrictorLS_neg_iff (hrow : ∀ n, 0 < n → ¬ q.ConstantOnRow n) :
    RestrictorLS (negRestrictorTruth q) R C π ↔ Transparent C {negRestrictorTruth q R} π := by
  refine ⟨RestrictorLS.transparent, fun h ↦ ⟨fun d w _ ↦ ?_, h.stablyTransparent⟩⟩
  -- A stable negated restriction has no individual at `w`, so neither has the unrestricted one.
  have key (c : Prop) (hc : ∀ B : W → E → Prop, w ∈ negRestrictorTruth q B (π ⊓ d) ↔ c) :
      ∀ B : W → E → Prop, w ∈ negRestrictorTruth q B d ↔ c := by
    have hX : ∀ e, ¬ (w, e) ∈ (π ⊓ d)ᶜ := fun e he ↦
      not_stable (X := fun x ↦ (w, x) ∈ (π ⊓ d)ᶜ) he
        (hrow _ ((Set.ncard_pos (Set.toFinite _)).2 ⟨e, he⟩)) fun B ↦ hc fun _ ↦ B
    intro B
    rw [← hc B]
    refine iff_of_eq (congrArg (q.toGQ · (B w)) (funext fun e ↦ propext ?_))
    exact ⟨fun hd ↦ (hX e fun h ↦ hd h.2).elim, fun hd ↦ (hX e hd).elim⟩
  refine ⟨fun ht f hf ↦ ?_, fun hf' f hf ↦ ?_⟩
  · obtain ⟨B, rfl⟩ := hf
    exact ((key True fun B ↦ iff_true_intro (ht _ (Set.mem_range_self B))) B).2 trivial
  · obtain ⟨B, rfl⟩ := hf
    exact ((key False fun B ↦ iff_false_intro (hf' _ (Set.mem_range_self B))) B).1

end Stable

/-! ### *Some*, *no* and *every* -/

section Table

variable [Finite E]

private theorem some_not_constantOnRow {n : ℕ} (hn : 0 < n) :
    ¬ NumberTree.some.ConstantOnRow n := fun h ↦ by
  have := h n 0 0 n (by omega) (by omega); simp [NumberTree.some] at this; omega

private theorem no_not_constantOnRow {n : ℕ} (hn : 0 < n) : ¬ NumberTree.no.ConstantOnRow n :=
  fun h ↦ by have := h n 0 0 n (by omega) (by omega); simp [NumberTree.no] at this; omega

private theorem all_not_constantOnRow {n : ℕ} (hn : 0 < n) : ¬ NumberTree.all.ConstantOnRow n :=
  fun h ↦ by have := h n 0 0 n (by omega) (by omega); simp [NumberTree.all] at this; omega

/-- With the scope `R`, symmetric Transparency for a trigger in the restrictor of *some* requires
every individual in the scope to satisfy the presupposition. -/
theorem transparent_some_iff :
    Transparent C {restrictorTruth NumberTree.some R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π := by
  simp only [Transparent, Set.mem_singleton_iff, forall_eq, restrictorTruth, Set.mem_ofPred_eq,
    NumberTree.toGQ_some_iff]
  refine ⟨fun h w hw e he ↦ ?_, fun h d w hw ↦ ⟨fun ⟨e, h₁, h₂⟩ ↦ ⟨e, h₁.2, h₂⟩,
    fun ⟨e, h₁, h₂⟩ ↦ ⟨e, ⟨h w hw e h₂, h₁⟩, h₂⟩⟩⟩
  obtain ⟨e', ⟨hπ, he'⟩, -⟩ := (h {(w, e)} w hw).2 ⟨e, rfl, he⟩
  rw [Set.mem_singleton_iff] at he'
  obtain rfl : e' = e := (Prod.ext_iff.1 he').2
  exact hπ

/-- With the scope `R`, symmetric Transparency for a trigger in the restrictor of *no* requires
every individual in the scope to satisfy the presupposition. -/
theorem transparent_no_iff :
    Transparent C {restrictorTruth NumberTree.no R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π := by
  rw [← transparent_some_iff]
  simp only [Transparent, Set.mem_singleton_iff, forall_eq, restrictorTruth, Set.mem_ofPred_eq,
    NumberTree.toGQ_no_iff, NumberTree.toGQ_some_iff, not_iff_not]

/-- With the scope `R`, symmetric Transparency for a trigger in the restrictor of *every* requires
every individual outside the scope to satisfy the presupposition. -/
theorem transparent_every_iff :
    Transparent C {restrictorTruth NumberTree.all R} π ↔ ∀ w ∈ C, ∀ e, ¬ R w e → (w, e) ∈ π := by
  simp only [Transparent, Set.mem_singleton_iff, forall_eq, restrictorTruth, Set.mem_ofPred_eq,
    NumberTree.toGQ_all_iff]
  refine ⟨fun h w hw e he ↦ by_contra fun hπ ↦ he ((h {(w, e)} w hw).1 ?_ e rfl), fun h d w hw ↦
    ⟨fun h' e hd ↦ by_contra fun hR ↦ hR (h' e ⟨h w hw e hR, hd⟩), fun h' e hd ↦ h' e hd.2⟩⟩
  rintro e' ⟨hπ', he'⟩
  rw [Set.mem_singleton_iff, Prod.mk.injEq] at he'
  exact absurd (he'.2 ▸ hπ') hπ

/-- With the trigger in the restrictor of *some*, incremental Transparency and Limited Symmetry
require everything to satisfy the presupposition and symmetric Transparency every individual in
the scope; with the restrictor negated, Limited Symmetry falls with symmetric Transparency. -/
theorem some_table :
    (Transparent C (Set.range (restrictorTruth NumberTree.some)) π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (restrictorTruth NumberTree.some) R C π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (Transparent C {restrictorTruth NumberTree.some R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) ∧
    (Transparent C (Set.range (negRestrictorTruth NumberTree.some)) π ↔
      ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (negRestrictorTruth NumberTree.some) R C π ↔
      ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) ∧
    (Transparent C {negRestrictorTruth NumberTree.some R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) :=
  ⟨transparent_range_restrictorTruth_iff (some_not_constantOnRow one_pos),
    restrictorLS_iff (some_not_constantOnRow one_pos), transparent_some_iff,
    transparent_range_neg_iff.trans (transparent_range_restrictorTruth_iff
      (some_not_constantOnRow one_pos)),
    (restrictorLS_neg_iff fun _ ↦ some_not_constantOnRow).trans
      (transparent_neg_iff.trans transparent_some_iff),
    transparent_neg_iff.trans transparent_some_iff⟩

/-- *No* makes the same predictions as *some*. -/
theorem no_table :
    (Transparent C (Set.range (restrictorTruth NumberTree.no)) π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (restrictorTruth NumberTree.no) R C π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (Transparent C {restrictorTruth NumberTree.no R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) ∧
    (Transparent C (Set.range (negRestrictorTruth NumberTree.no)) π ↔
      ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (negRestrictorTruth NumberTree.no) R C π ↔
      ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) ∧
    (Transparent C {negRestrictorTruth NumberTree.no R} π ↔ ∀ w ∈ C, ∀ e, R w e → (w, e) ∈ π) :=
  ⟨transparent_range_restrictorTruth_iff (no_not_constantOnRow one_pos),
    restrictorLS_iff (no_not_constantOnRow one_pos), transparent_no_iff,
    transparent_range_neg_iff.trans (transparent_range_restrictorTruth_iff
      (no_not_constantOnRow one_pos)),
    (restrictorLS_neg_iff fun _ ↦ no_not_constantOnRow).trans
      (transparent_neg_iff.trans transparent_no_iff),
    transparent_neg_iff.trans transparent_no_iff⟩

/-- *Every* makes the predictions of *some*, except that symmetric Transparency, and with the
restrictor negated Limited Symmetry, require every individual outside the scope to satisfy the
presupposition. -/
theorem every_table :
    (Transparent C (Set.range (restrictorTruth NumberTree.all)) π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (restrictorTruth NumberTree.all) R C π ↔ ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (Transparent C {restrictorTruth NumberTree.all R} π ↔
      ∀ w ∈ C, ∀ e, ¬ R w e → (w, e) ∈ π) ∧
    (Transparent C (Set.range (negRestrictorTruth NumberTree.all)) π ↔
      ∀ w ∈ C, ∀ e, (w, e) ∈ π) ∧
    (RestrictorLS (negRestrictorTruth NumberTree.all) R C π ↔
      ∀ w ∈ C, ∀ e, ¬ R w e → (w, e) ∈ π) ∧
    (Transparent C {negRestrictorTruth NumberTree.all R} π ↔
      ∀ w ∈ C, ∀ e, ¬ R w e → (w, e) ∈ π) :=
  ⟨transparent_range_restrictorTruth_iff (all_not_constantOnRow one_pos),
    restrictorLS_iff (all_not_constantOnRow one_pos), transparent_every_iff,
    transparent_range_neg_iff.trans (transparent_range_restrictorTruth_iff
      (all_not_constantOnRow one_pos)),
    (restrictorLS_neg_iff fun _ ↦ all_not_constantOnRow).trans
      (transparent_neg_iff.trans transparent_every_iff),
    transparent_neg_iff.trans transparent_every_iff⟩

/-- In a negated restrictor of *some*, the theories make a crucial prediction. A context where
every individual in the scope satisfies the presupposition but another individual does not is
accepted by Limited Symmetry and rejected by incremental Transparency. No experiment recorded in
the library tests a negated restrictor; Chemla's restrictor items are positive. -/
theorem restrictorLS_neg_not_transparent_some :
    RestrictorLS (negRestrictorTruth NumberTree.some) (fun (_ : Unit) (e : Bool) ↦ e = true) {()}
        {p | p.2 = true} ∧
      ¬ Transparent {()} (Set.range (negRestrictorTruth NumberTree.some))
        {p : Unit × Bool | p.2 = true} := by
  have t := some_table (R := fun (_ : Unit) (e : Bool) ↦ e = true) (C := {()})
    (π := {p : Unit × Bool | p.2 = true})
  exact ⟨t.2.2.2.2.1.2 fun _ _ _ he ↦ he, fun h ↦ absurd (t.2.2.2.1.1 h () rfl false) (by simp)⟩

end Table

/-! ### Quantified clauses -/

section Clause

variable {Atom : Type*} (J : Atom → Set (W × E))

/-- With nothing after the gap inside the restrictor, the parsing points of a restrictor trigger are
those of the restrictor: every scope at the first, the clause's own scope from then on. -/
private theorem continuations_restrictor {q : NumberTree} {S : Formula Atom}
    {K : SyntacticEnvironment Atom} (hK : K.rightItems = 0) (n : ℕ∞) :
    QuantifiedClause.Env.continuations J ⟨q, .restrictor S, K⟩ n =
      (· ∘ K.truth J) '' QuantifiedClause.Arg.continuations J q (.restrictor S) n := by
  have hK' : K.continuations J n = {K.truth J} := by
    induction n using ENat.recTopCoe with
    | top => rfl
    | coe n => exact SyntacticEnvironment.continuations_eq_top_of_le J (hK ▸ Nat.zero_le n)
  simp only [QuantifiedClause.Env.continuations, hK, Nat.cast_zero, tsub_zero, hK',
    Set.image2_singleton_right]

/-- Stable transparency at every parsing point of a restrictor trigger is stable transparency at the
end of the restrictor and at the end of the sentence. -/
private theorem forall_stablyTransparent_restrictor_iff {q : NumberTree} {S : Formula Atom}
    {g : (Set (W × E) → Set W) → Set (W × E) → Set W} {π : Set (W × E)} :
    (∀ n : ℕ∞, StablyTransparent C
      (g '' QuantifiedClause.Arg.continuations J q (.restrictor S) n) π) ↔
      StablyTransparent C (g '' Set.range (restrictorTruth q)) π ∧
        StablyTransparent C {g (restrictorTruth q fun w e ↦ (w, e) ∈ S.truth J)} π := by
  simp only [QuantifiedClause.Arg.continuations]
  refine ⟨fun h ↦ ⟨by simpa using h 0, by simpa using h ⊤⟩, fun h n ↦ ?_⟩
  split_ifs
  · exact h.1
  · simpa using h.2

/-- A trigger that is the restrictor has the two parsing points of `RestrictorLS`. -/
theorem limitedSymmetry_trigger_iff {q : NumberTree} {p a : Atom} {S : Formula Atom}
    (hS : S.triggers = []) :
    Kalomoiros2023.LimitedSymmetry C (QuantifiedClause.occurrences J ⟨q, .trigger p a, S⟩) ↔
      RestrictorLS (restrictorTruth q) (fun w e ↦ (w, e) ∈ S.truth J) C (J p) := by
  simp only [Kalomoiros2023.LimitedSymmetry, QuantifiedClause.forall_mem_occurrences,
    QuantifiedClause.triggers, hS, Formula.triggers, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_singleton, forall_eq]
  change (∀ n : ℕ∞, StablyTransparent C
    (QuantifiedClause.Env.continuations J ⟨q, .restrictor S, []⟩ n) (J p)) ↔ _
  simp only [continuations_restrictor J (K := []) rfl]
  have h : SyntacticEnvironment.truth J ([] : SyntacticEnvironment Atom) = id := rfl
  exact (forall_stablyTransparent_restrictor_iff J).trans (by
    simp only [h, Function.comp_id, Set.image_id', RestrictorLS])

/-- A trigger that is the negated restrictor has the two parsing points of `RestrictorLS` for the
negated restrictor. -/
theorem limitedSymmetry_not_trigger_iff {q : NumberTree} {p a : Atom} {S : Formula Atom}
    (hS : S.triggers = []) :
    Kalomoiros2023.LimitedSymmetry C (QuantifiedClause.occurrences J ⟨q, .not (.trigger p a), S⟩) ↔
      RestrictorLS (negRestrictorTruth q) (fun w e ↦ (w, e) ∈ S.truth J) C (J p) := by
  simp only [Kalomoiros2023.LimitedSymmetry, QuantifiedClause.forall_mem_occurrences,
    QuantifiedClause.triggers, hS, Formula.triggers, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_singleton, forall_eq]
  change (∀ n : ℕ∞, StablyTransparent C
    (QuantifiedClause.Env.continuations J ⟨q, .restrictor S, [.not]⟩ n) (J p)) ↔ _
  simp only [continuations_restrictor J (K := [.not]) rfl]
  refine (forall_stablyTransparent_restrictor_iff J).trans ?_
  rw [RestrictorLS, ← Set.range_comp]
  rfl

end Clause

/-! ### Scoring -/

open Eval.Projection

/-- Limited Symmetry as a theory to score: Kalomoiros's constraint on formulas, and the constraint
at the parsing points of each argument on quantified clauses. -/
def limitedSymmetry : Theory :=
  ⟨fun I C F ↦ Kalomoiros2023.LimitedSymmetry C (Formula.occurrences I F),
    some fun _ _ _ J C c ↦ Kalomoiros2023.LimitedSymmetry C (QuantifiedClause.occurrences J c)⟩

/-- On Chemla and Schlenker's inferential experiments, Limited Symmetry is right on every tested
cell, as the registered account is. -/
theorem verdict_chemlaSchlenker2012 (k : _root_.ChemlaSchlenker2012.Construction)
    (o : _root_.ChemlaSchlenker2012.Order) :
    ChemlaSchlenker2012.experiment1.verdict limitedSymmetry (k, o) =
        (if k = .unlessSentence ∧ o = .canonical then .silent else .correct) ∧
      ChemlaSchlenker2012.experiment4.verdict limitedSymmetry (k, o) =
        if k = .unlessSentence ∧ o = .canonical then .silent else .correct := by
  -- Limited Symmetry accepts a formula as the registered account does.
  have h1 : ChemlaSchlenker2012.experiment1.verdict limitedSymmetry (k, o) =
      ChemlaSchlenker2012.experiment1.verdict Account.limitedSymmetry.theory (k, o) := rfl
  have h4 : ChemlaSchlenker2012.experiment4.verdict limitedSymmetry (k, o) =
      ChemlaSchlenker2012.experiment4.verdict Account.limitedSymmetry.theory (k, o) := rfl
  rw [h1, h4, ChemlaSchlenker2012.verdict_experiment1, ChemlaSchlenker2012.verdict_experiment4]
  simp [ChemlaSchlenker2012.incremental]

/-- On Chemla's first experiment, Limited Symmetry is wrong with every presupposition accommodated
in the context, and right by §4.1.2's stipulations and by the one-step rule. -/
theorem verdict_chemla2009a (p : Chemla2009a.Accommodation) :
    Chemla2009a.experiment1.verdict (limitedSymmetry, p) () =
      if p = .global then .wrong else .correct := by
  have hT : ∀ (Atom W E : Type) (I : Atom → Set (W × E)) C c,
      Kalomoiros2023.LimitedSymmetry C (QuantifiedClause.occurrences I c) →
        Schlenker2009.Transparency .symmetric C (QuantifiedClause.occurrences I c) :=
    fun _ _ _ _ _ _ h ↦ Kalomoiros2023.LimitedSymmetry.transparency h
  have h := Chemla2009a.verdict_oneStep_of (T := limitedSymmetry) rfl hT
    fun _ _ _ _ _ _ hc o ho ↦ by simp [QuantifiedClause.occurrences, hc] at ho
  rw [Chemla2009a.verdict_experiment1_eq]
  cases p
  · exact Chemla2009a.verdict_global_of rfl hT
  · exact (Chemla2009a.verdict_stipulated_eq _).trans h
  · exact h

end Lab.Colinguistics
