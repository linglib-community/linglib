module

public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Presupposition.TwoDimensional
public import Linglib.Semantics.Homogeneity.Plural
public import Studies.BarLevFox2020

/-!
# Del Pinal, Bassi and Sauerland (2024): Free choice and presuppositional exhaustification

Del Pinal, Bassi and Sauerland's operator `pex^{IE+II}` asserts its prejacent and presupposes
that the relevant includable alternatives are homogeneous. On `◇(p ∨ q)` it presupposes
`◇p ↔ ◇q`, so free choice is the presupposition and the assertion together, while negation
denies only the assertion and leaves double prohibition. The flat `exh^{IE+II}` of Bar-Lev and
Fox yields the same overall content without the split, and the paper's puzzles about free choice
under negative factives, in disjunctions and under quantifiers all turn on the split.

## Implementation notes

Each `pex` uses the paper's relevance set, which leaves out the conjunctive alternative of
`◇(p ∨ q)` and the disjunctive one of `□(p ∧ q)`; with every alternative relevant,
`¬pex[□(T ∧ B)]` would entail `¬□(T ∨ B)`. `¬□(p ∧ q)` is rendered as `◇(¬p ∨ ¬q)`. The witness
hypotheses supply the worlds that make the alternatives independent, which the paper assumes
implicitly. Negation is `ᶜ` on trivalent propositions and the filtering disjunction (45) is
Middle Kleene `Trivalent.joinMiddle`. Negative factives use the transparent projection rule (30b),
as `ConventionalImplicature.TwoDim.negFactive` does, on `pex` read as a two-dimensional meaning,
since the factive denies belief in the at-issue prejacent. Quantifiers over `S` project the
presupposition universally, as the Weak Kleene quantifiers over the subtype of `S`, and
*exactly one* is `∃!` with the same projection.

## References

* [delpinal-bassi-sauerland-2024]
* [bassi-delpinal-sauerland-2021]
* [bar-lev-fox-2020]
* [gotzner-romoli-santorio-2020]
* [goldstein-2019]
* [kriz-2016]
* [fox-2013]
* [karttunen-1973]
-/

@[expose] public section

namespace DelPinalBassiSauerland2024

open Exhaustification Homogeneity BarLevFox2020 ModalLogic SetRel ConventionalImplicature
open scoped ModalLogic

variable {W : Type*}

/-! ### Basic scalar sentences, §2.1 -/

/-- On a prejacent with one other alternative, which it does not entail, as *some* has *all*,
`pex^{IE+II}` presupposes that the alternative is false, (10)–(11a). -/
theorem basic_scalar {φ ψ : Set W} (h : ¬ φ ⊆ ψ) {w : W} :
    pexIEII {φ, ψ} φ {φ, ψ} w ≠ .undefined ↔ w ∉ ψ := by
  obtain ⟨w₀, hw₀, hw₀ψ⟩ := Set.not_subset.1 h
  have hM : IsMinimalCover {φ, ψ} φ {w₀} :=
    .singleton hw₀ (by rintro q (rfl | rfl) hq; exacts [le_rfl, absurd hq hw₀ψ])
  have hII : {q ∈ ({φ, ψ} : Set (Set W)) | IsInnocentlyIncludable {φ, ψ} φ q ∧ q ≠ φ} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun q ⟨hq, hIIq, hne⟩ ↦ ?_
    obtain ⟨-, v, rfl, hv⟩ := (hM.isInnocentlyIncludable_iff ⟨w₀, hw₀, by simp⟩).1 hIIq
    rcases hq with rfl | rfl
    exacts [hne rfl, hw₀ψ hv]
  rw [pexIEII_ne_undefined_iff_of_inter_eq_empty hII]
  grind [hM.isInnocentlyExcludable_iff]

/-! ### `pex^{IE+II}` on `◇(p ∨ q)`, §2.2 -/

section FreeChoice

variable (R : SetRel W W) (a b : Set W)

/-- `pexPossOr R a b` is `pex^{IE+II}[◇(a ∨ b)]` with the conjunctive alternative irrelevant,
as in (12) and (14). -/
noncomputable def pexPossOr : W → Trivalent :=
  pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) {R.preimage (a ∪ b), R.preimage a, R.preimage b}

variable {R a b} {w : W}

/-- `pex^{IE+II}[◇(a ∨ b)]` is false, and its negation true, exactly where double prohibition holds
(16). -/
theorem double_prohibition :
    pexPossOr R a b w = .false ↔ w ∉ R.preimage a ∧ w ∉ R.preimage b := by
  simp only [pexPossOr, pexIEII_eq_false_iff, pexIEII_ne_undefined_iff, preimage_union, Homogeneous,
    Set.mem_sep_iff]
  grind

variable (hF : FreeChoiceWitnesses R a b)
include hF

-- (12d)
theorem isInnocentlyIncludable_fcAlts_ne_iff {q : Set W} :
    IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) q ∧ q ≠ R.preimage (a ∪ b) ↔
      q = R.preimage a ∨ q = R.preimage b := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  obtain ⟨w₂, hw₂b, hw₂a⟩ := hF.only_right
  have ha : R.preimage a ≠ R.preimage (a ∪ b) := fun he ↦
    hw₂a (he ▸ preimage_mono Set.subset_union_right hw₂b)
  have hb : R.preimage b ≠ R.preimage (a ∪ b) := fun he ↦
    hw₁b (he ▸ preimage_mono Set.subset_union_left hw₁a)
  rw [isInnocentlyIncludable_fcAlts_iff hF]
  refine ⟨fun ⟨h, hne⟩ ↦ h.resolve_left hne, fun h ↦ ⟨.inr h, ?_⟩⟩
  rcases h with rfl | rfl
  exacts [ha, hb]

private theorem relevant_fcAlts :
    {q ∈ ({R.preimage (a ∪ b), R.preimage a, R.preimage b} : Set (Set W)) |
      IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) q ∧ q ≠ R.preimage (a ∪ b)} =
        {R.preimage a, R.preimage b} := by
  ext q
  rw [Set.mem_sep_iff, isInnocentlyIncludable_fcAlts_ne_iff hF]
  exact ⟨And.right, fun h ↦ ⟨.inr h, h⟩⟩

-- (14), (12c)
theorem pexPossOr_ne_undefined_iff :
    pexPossOr R a b w ≠ .undefined ↔ (w ∈ R.preimage a ↔ w ∈ R.preimage b) := by
  refine pexIEII_ne_undefined_iff.trans <| (and_iff_right fun ψ hψ hR ↦ ?_).trans
    (by rw [relevant_fcAlts hF, homogeneous_pair])
  obtain rfl := (isInnocentlyExcludable_fcAlts_iff hF).1 hψ
  obtain ⟨w₀, ⟨hw₀a, hw₀b⟩, hw₀⟩ := hF.not_both
  grind [preimage_mono Set.subset_union_left hw₀a]

/-- `pex^{IE+II}[◇(a ∨ b)]` is true exactly where free choice holds, (14), since `◇(a ∨ b)` lies
between `◇a ∧ ◇b` and `◇a ∨ ◇b`. -/
theorem free_choice : pexPossOr R a b w = .true ↔ w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  have hl : ⋂₀ {q ∈ ({R.preimage (a ∪ b), R.preimage a, R.preimage b} : Set (Set W)) |
      IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) q ∧ q ≠ R.preimage (a ∪ b)} ⊆
        R.preimage (a ∪ b) := by
    rw [relevant_fcAlts hF, Set.sInter_pair, preimage_union]
    exact inf_le_sup
  have hu : R.preimage (a ∪ b) ⊆
      ⋃₀ {q ∈ ({R.preimage (a ∪ b), R.preimage a, R.preimage b} : Set (Set W)) |
        IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) q ∧ q ≠ R.preimage (a ∪ b)} := by
    rw [relevant_fcAlts hF, Set.sUnion_pair, preimage_union]
  rw [pexPossOr, pexIEII_eq_true_iff_forall_mem hl hu, ← pexPossOr, pexPossOr_ne_undefined_iff hF,
    relevant_fcAlts hF]
  grind

open Classical in
/-- `pex^{IE+II}[◇(a ∨ b)]` is the plural predication that `a` and `b` are permitted, true where
both are, false where neither is, and undefined in between. -/
theorem pexPossOr_eq_barePlural :
    pexPossOr R a b = barePlural (fun x w ↦ w ∈ R.preimage x) {a, b} := by
  funext w
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · have := pexPossOr_ne_undefined_iff (w := w) hF
    simp only [barePlural, Trivalent.supervaluation_eq_undefined_iff, Finset.mem_insert,
      Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
    tauto
  · simp only [free_choice hF, barePlural, Trivalent.supervaluation_eq_true_iff, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- `pex^{IE+II}[◇(a ∨ b)]` is undefined exactly where one of `◇a` and `◇b` holds without the
other, the presupposition failure fn. 2 predicts. -/
theorem homogeneity_gap :
    Trivalent.gapExt (pexPossOr R a b) = symmDiff (R.preimage a) (R.preimage b) := by
  ext w
  have := pexPossOr_ne_undefined_iff (w := w) hF
  simp only [Trivalent.mem_gapExt, Set.mem_symmDiff]
  tauto

-- fn. 2
theorem homogeneity_gap_compl :
    Trivalent.gapExt ((pexPossOr R a b)ᶜ) = symmDiff (R.preimage a) (R.preimage b) := by
  rw [← homogeneity_gap hF]
  ext w
  simp

theorem gapExt_pexPossOr_nonempty : (Trivalent.gapExt (pexPossOr R a b)).Nonempty := by
  obtain ⟨w, hwa, hwb⟩ := hF.only_left
  exact ⟨w, by rw [homogeneity_gap hF]; exact .inl ⟨hwa, hwb⟩⟩

/-- With every alternative relevant, `pex^{IE+II}[◇(a ∨ b)]` is true exactly where `exh^{IE+II}[◇(a
∨ b)]` is ((12e), (13)). -/
theorem pex_and_exh_agree :
    pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) (fcAlts R a b) w = .true ↔
      w ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) := by
  have hII : {q ∈ fcAlts R a b | IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) q ∧
      q ≠ R.preimage (a ∪ b)} = {R.preimage a, R.preimage b} := by
    ext q
    rw [Set.mem_sep_iff, isInnocentlyIncludable_fcAlts_ne_iff hF]
    exact ⟨And.right, fun h ↦ ⟨by rcases h with rfl | rfl <;> simp [fcAlts], h⟩⟩
  have hc : R.preimage (a ∩ b) ∈ fcAlts R a b := by simp [fcAlts]
  rw [freeChoice hF, pexIEII_eq_true_iff, pexIEII_ne_undefined_iff, hII, homogeneous_pair]
  grind [isInnocentlyExcludable_fcAlts_iff hF, preimage_union]

end FreeChoice

section NegatedFreeChoice

variable {R : SetRel W W} {w : W}

-- (18b)
theorem fcAlts_compl (R : SetRel W W) (T B : Set W) :
    fcAlts R Tᶜ Bᶜ = {(R.core (T ∩ B))ᶜ, (R.core T)ᶜ, (R.core B)ᶜ, (R.core (T ∪ B))ᶜ} := by
  simp only [fcAlts, preimage_compl, ← Set.compl_inter, ← Set.compl_union]

/-- `pex^{IE+II}[¬□(T ∧ B)]` is true exactly where negative free choice holds, (18) and (19a). -/
theorem negative_free_choice {T B : Set W} (hF : FreeChoiceWitnesses R Tᶜ Bᶜ) :
    pexPossOr R Tᶜ Bᶜ w = .true ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  simpa only [preimage_compl, Set.mem_compl_iff] using free_choice hF

end NegatedFreeChoice

/-- Where world `4` permits both `0` and `1`, world `2` only `0`, world `3` only `1`, and world
`0` neither, `pex^{IE+II}[◇(p ∨ q)]` is true at `4`, suffers presupposition failure at `2` as
fn. 2 predicts, and is false at `0`. -/
example :
    let R : SetRel (Fin 5) (Fin 5) := {(2, 0), (3, 1), (4, 0), (4, 1)}
    pexPossOr R {0} {1} 4 = .true ∧ pexPossOr R {0} {1} 2 = .undefined ∧
      pexPossOr R {0} {1} 0 = .false := by
  intro R
  have hF : FreeChoiceWitnesses R {0} {1} :=
    ⟨⟨2, by simp [R], by simp [R]⟩, ⟨3, by simp [R], by simp [R]⟩, ⟨4, by simp [R], by simp [R]⟩⟩
  refine ⟨(free_choice hF).2 (by simp [R]), not_not.1 fun hp ↦ ?_,
    double_prohibition.2 (by simp [R])⟩
  simpa [R] using (pexPossOr_ne_undefined_iff hF).1 hp

/-! ### `pex^{IE+II}` on `□(p ∧ q)`, §2.2 -/

section NegativeFreeChoice

variable (R : SetRel W W) (T B : Set W)

/-- The alternatives of `□(T ∧ B)` replace the conjunction by its conjuncts and their
disjunction. -/
def necAlts : Set (Set W) := {R.core (T ∩ B), R.core T, R.core B, R.core (T ∪ B)}

/-- `pexNecAnd R T B` is `pex^{IE+II}[□(T ∧ B)]` with the disjunctive alternative irrelevant, as
in (20) and (57). -/
noncomputable def pexNecAnd : W → Trivalent :=
  pexIEII (necAlts R T B) (R.core (T ∩ B)) {R.core (T ∩ B), R.core T, R.core B}

variable {R T B}

theorem subset_of_mem_necAlts {q : Set W} (hq : q ∈ necAlts R T B) : R.core (T ∩ B) ⊆ q := by
  simp only [necAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  exacts [le_rfl, core_mono Set.inter_subset_left, core_mono Set.inter_subset_right,
    core_mono (Set.inter_subset_left.trans Set.subset_union_left)]

-- (56)
theorem exhIEII_necAlts (h : (R.core (T ∩ B)).Nonempty) :
    exhIEII (necAlts R T B) (R.core (T ∩ B)) = R.core (T ∩ B) :=
  exhIEII_eq_self_of_forall_subset (fun _ ↦ subset_of_mem_necAlts) h

theorem not_isInnocentlyExcludable_necAlts (h : (R.core (T ∩ B)).Nonempty) (q : Set W) :
    ¬ IsInnocentlyExcludable (necAlts R T B) (R.core (T ∩ B)) q := fun hq ↦
  not_isInnocentlyExcludable_of_phi_subset
    (((Set.finite_singleton _).insert _).insert _ |>.insert _) h (subset_of_mem_necAlts hq.1) hq

variable (h₁ : ∃ w ∈ R.core T, w ∉ R.core B) (h₂ : ∃ w ∈ R.core B, w ∉ R.core T)
  (h : (R.core (T ∩ B)).Nonempty) {w : W}
include h₁ h₂ h

-- (20)
theorem isInnocentlyIncludable_necAlts_ne_iff {q : Set W} :
    IsInnocentlyIncludable (necAlts R T B) (R.core (T ∩ B)) q ∧ q ≠ R.core (T ∩ B) ↔
      q = R.core T ∨ q = R.core B ∨ q = R.core (T ∪ B) := by
  obtain ⟨w₀, hw₀⟩ := id h
  have hcell : w₀ ∈ cell (necAlts R T B) (R.core (T ∩ B)) :=
    ⟨hw₀, fun q hq ↦ absurd hq (not_isInnocentlyExcludable_necAlts h q),
      fun r hr _ ↦ subset_of_mem_necAlts hr hw₀⟩
  have hII (q : Set W) : IsInnocentlyIncludable (necAlts R T B) (R.core (T ∩ B)) q ↔
      q ∈ necAlts R T B :=
    ⟨And.left, fun hq ↦ isInnocentlyIncludable_of_mem_cell hq hcell (subset_of_mem_necAlts hq hw₀)⟩
  obtain ⟨wT, hwT, hwTB⟩ := h₁
  obtain ⟨wB, hwB, hwBT⟩ := h₂
  have hT : R.core T ≠ R.core (T ∩ B) := fun he ↦
    hwTB (core_mono Set.inter_subset_right (he ▸ hwT))
  have hB : R.core B ≠ R.core (T ∩ B) := fun he ↦
    hwBT (core_mono Set.inter_subset_left (he ▸ hwB))
  have hTB : R.core (T ∪ B) ≠ R.core (T ∩ B) := fun he ↦
    hwTB (core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT))
  rw [hII, necAlts]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨h, hne⟩ ↦ h.resolve_left hne, fun h ↦ ⟨.inr h, ?_⟩⟩
  rcases h with rfl | rfl | rfl
  exacts [hT, hB, hTB]

private theorem relevant_necAlts :
    {q ∈ ({R.core (T ∩ B), R.core T, R.core B} : Set (Set W)) |
      IsInnocentlyIncludable (necAlts R T B) (R.core (T ∩ B)) q ∧ q ≠ R.core (T ∩ B)} =
        {R.core T, R.core B} := by
  have hne : R.core (T ∪ B) ≠ R.core (T ∩ B) := fun he ↦ by
    obtain ⟨wT, hwT, hwTB⟩ := h₁
    exact hwTB (core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT))
  ext q
  rw [Set.mem_sep_iff, isInnocentlyIncludable_necAlts_ne_iff h₁ h₂ h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

-- (20)
theorem pexNecAnd_ne_undefined_iff :
    pexNecAnd R T B w ≠ .undefined ↔ (w ∈ R.core T ↔ w ∈ R.core B) :=
  pexIEII_ne_undefined_iff.trans <|
    (and_iff_right fun ψ hψ _ ↦ absurd hψ (not_isInnocentlyExcludable_necAlts h ψ)).trans
      (by rw [relevant_necAlts h₁ h₂ h, homogeneous_pair])

/-- `pex^{IE+II}[□(T ∧ B)]` is false, and its negation true, exactly where negative free choice
holds (20). -/
theorem negative_free_choice_under_negation :
    pexNecAnd R T B w = .false ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  have hl : ⋂₀ {q ∈ ({R.core (T ∩ B), R.core T, R.core B} : Set (Set W)) |
      IsInnocentlyIncludable (necAlts R T B) (R.core (T ∩ B)) q ∧ q ≠ R.core (T ∩ B)} ⊆
        R.core (T ∩ B) := by
    rw [relevant_necAlts h₁ h₂ h, Set.sInter_pair, core_inter]
  have hu : R.core (T ∩ B) ⊆ ⋃₀ {q ∈ ({R.core (T ∩ B), R.core T, R.core B} : Set (Set W)) |
      IsInnocentlyIncludable (necAlts R T B) (R.core (T ∩ B)) q ∧ q ≠ R.core (T ∩ B)} := by
    rw [relevant_necAlts h₁ h₂ h, Set.sUnion_pair, core_inter]
    exact inf_le_sup
  rw [pexNecAnd, pexIEII_eq_false_iff_forall_notMem hl hu, ← pexNecAnd,
    pexNecAnd_ne_undefined_iff h₁ h₂ h, relevant_necAlts h₁ h₂ h]
  grind

end NegativeFreeChoice

/-! ### Free choice under negative factives, §3 -/

section NegativeFactive

variable {R : SetRel W W} {a b : Set W} {w : W}

variable (R a b) in
/-- `pex^{IE+II}[◇(a ∨ b)]` as a two-dimensional meaning, with the prejacent `◇(a ∨ b)` at issue
and the presupposition of `pexPossOr` not at issue. A negative factive denies belief in the
at-issue content, which it reads apart from the presupposition. -/
def pexPossOrTwoDim : TwoDim W (W → Prop) :=
  ⟨(· ∈ R.preimage (a ∪ b)), (pexPossOr R a b · ≠ .undefined)⟩

theorem toTrivalent_pexPossOrTwoDim : (pexPossOrTwoDim R a b).toTrivalent = pexPossOr R a b := by
  funext w
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_ <;>
    simp [pexPossOrTwoDim, pexPossOr, pexIEII_eq_true_iff]

/-- Under a negative factive the whole output of `pex` is presupposed, and that is free choice,
(21a) and (31c). -/
theorem free_choice_presupposed (hF : FreeChoiceWitnesses R a b)
    (believes : (W → Prop) → W → Prop) :
    (TwoDim.negFactive (pexPossOrTwoDim R a b) believes).notAtIssue w ↔
      w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  rw [← free_choice hF, ← toTrivalent_pexPossOrTwoDim, TwoDim.toTrivalent_eq_true_iff,
    TwoDim.negFactive_notAtIssue]

-- (33a), (34c)
theorem negative_free_choice_presupposed {T B : Set W} (hF : FreeChoiceWitnesses R Tᶜ Bᶜ)
    (believes : (W → Prop) → W → Prop) :
    (TwoDim.negFactive (pexPossOrTwoDim R Tᶜ Bᶜ) believes).notAtIssue w ↔
      w ∉ R.core T ∧ w ∉ R.core B := by
  rw [← negative_free_choice hF, ← toTrivalent_pexPossOrTwoDim, TwoDim.toTrivalent_eq_true_iff,
    TwoDim.negFactive_notAtIssue]

/-- A negative factive over `◇(a ∨ b)` asserts disbelief in each disjunct ((21b), (31d′); at `Tᶜ`
and `Bᶜ`, (33b) and (34d)). -/
theorem unaware_disbelieves_each_disjunct (R' : SetRel W W)
    (hw : (TwoDim.negFactive (pexPossOrTwoDim R a b) (Box R')).atIssue w) :
    ¬ □[R'] (· ∈ R.preimage a) w ∧ ¬ □[R'] (· ∈ R.preimage b) w :=
  ⟨fun hA ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inl hv)) w hA),
   fun hB ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inr hv)) w hB)⟩

-- (24a)
theorem exh_unaware_too_weak (hF : FreeChoiceWitnesses R a b) :
    ∃ R' : SetRel W W, □[R'] (· ∈ R.preimage a) w ∧
      ¬ □[R'] (· ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b))) w := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  refine ⟨.ofSuccessors fun _ ↦ {w₁}, fun v (hv : v = w₁) ↦ hv ▸ hw₁a, fun hbox ↦ ?_⟩
  have := hbox w₁ (Set.mem_singleton w₁)
  rw [freeChoice hF] at this
  exact hw₁b this.1.2

end NegativeFactive

/-! ### Filtering free choice, §4 -/

section Filtering

variable {R : SetRel W W} {a b A B : Set W} {C : W → Trivalent}

/-- In `¬pex[◇(a ∨ b)] ∨ C`, the filtering disjunction (45) filters the free-choice presupposition,
and only homogeneity projects ((53), §4.4). -/
theorem free_choice_filtered (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b)
    (hC : (Trivalent.gapExt C)ᶜ = R.preimage A ∩ R.preimage B) :
    (Trivalent.gapExt (fun w ↦ ((pexPossOr R a b w)ᶜ).joinMiddle (C w)))ᶜ =
      (Trivalent.gapExt (pexPossOr R a b))ᶜ := by
  ext w
  have h₁ := (free_choice (w := w) hF).1
  have h₂ : w ∈ R.preimage A ∩ R.preimage B → C w ≠ .undefined :=
    fun h ↦ Trivalent.mem_compl_gapExt.1 (hC ▸ h)
  simp only [Trivalent.mem_compl_gapExt, ne_eq, Trivalent.joinMiddle_eq_undefined_iff,
    Trivalent.compl_eq_undefined_iff, Trivalent.compl_eq_false_iff]
  grind [preimage_mono hA, preimage_mono hB]

open Classical in
-- (46c)
theorem no_filtering_without_pex (hC : (Trivalent.gapExt C)ᶜ = R.preimage A ∩ R.preimage B)
    (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, ((Trivalent.ofProp (w ∈ R.preimage (a ∪ b)))ᶜ).joinMiddle (C w) = .undefined := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = .undefined := not_not.1 fun h ↦ hwB (hC ▸ Trivalent.mem_compl_gapExt.2 h).2
  exact ⟨w, by simp [this, preimage_mono Set.subset_union_left hwa]⟩

open Classical in
-- (47c)
theorem exh_filters (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b)
    (hC : (Trivalent.gapExt C)ᶜ = R.preimage A ∩ R.preimage B) (w : W) :
    ((Trivalent.ofProp (w ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b))))ᶜ).joinMiddle (C w) ≠
      .undefined := by
  have h₂ : w ∈ R.preimage A ∩ R.preimage B → C w ≠ .undefined :=
    fun h ↦ Trivalent.mem_compl_gapExt.1 (hC ▸ h)
  have := @preimage_mono _ _ R _ _ hA
  have := @preimage_mono _ _ R _ _ hB
  simp only [freeChoice hF, ne_eq, Trivalent.joinMiddle_eq_undefined_iff,
    Trivalent.compl_eq_undefined_iff, Trivalent.ofProp_ne_undefined, Trivalent.compl_eq_false_iff,
    Trivalent.ofProp_eq_true_iff]
  grind

-- (47b)
theorem exh_loses_double_prohibition (hF : FreeChoiceWitnesses R a b) :
    ∃ w, w ∉ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) ∧ w ∈ R.preimage a := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  exact ⟨w₁, by grind [freeChoice hF], hw₁a⟩

/-- In `pex[□(A ∧ B)] ∨ C`, negative free choice filters the presupposition `¬□a ∧ ¬□b`, and only
homogeneity projects (57c). -/
theorem negative_free_choice_filtered (hA : a ⊆ A) (hB : b ⊆ B)
    (h₁ : ∃ w ∈ R.core A, w ∉ R.core B) (h₂ : ∃ w ∈ R.core B, w ∉ R.core A)
    (h : (R.core (A ∩ B)).Nonempty) (hC : (Trivalent.gapExt C)ᶜ = (R.core a)ᶜ ∩ (R.core b)ᶜ) :
    (Trivalent.gapExt (fun w ↦ (pexNecAnd R A B w).joinMiddle (C w)))ᶜ =
      (Trivalent.gapExt (pexNecAnd R A B))ᶜ := by
  ext w
  have := (negative_free_choice_under_negation (w := w) h₁ h₂ h).1
  have h₃ : w ∈ (R.core a)ᶜ ∩ (R.core b)ᶜ → C w ≠ .undefined :=
    fun h ↦ Trivalent.mem_compl_gapExt.1 (hC ▸ h)
  have := @core_mono _ _ R _ _ hA
  have := @core_mono _ _ R _ _ hB
  simp only [Trivalent.mem_compl_gapExt, ne_eq, Trivalent.joinMiddle_eq_undefined_iff]
  grind

open Classical in
-- (56c)
theorem no_negative_filtering_with_exh (h : (R.core (A ∩ B)).Nonempty)
    (hC : (Trivalent.gapExt C)ᶜ = (R.core a)ᶜ ∩ (R.core b)ᶜ) (hw : ∃ w ∈ R.core a, w ∉ R.core B) :
    ∃ w, (Trivalent.ofProp (w ∈ exhIEII (necAlts R A B) (R.core (A ∩ B)))).joinMiddle (C w) =
      .undefined := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = .undefined := not_not.1 fun h ↦ (hC ▸ Trivalent.mem_compl_gapExt.2 h).1 hwa
  have hn : w ∉ exhIEII (necAlts R A B) (R.core (A ∩ B)) := by
    rw [exhIEII_necAlts h]
    exact fun hAB ↦ hwB (core_mono Set.inter_subset_right hAB)
  exact ⟨w, by simp [this, hn]⟩

-- (59c)
theorem double_prohibition_accommodated {w : W} :
    Trivalent.ofProp ((pexPossOr R a b w)ᶜ = .true) = .true ↔
      w ∉ R.preimage a ∧ w ∉ R.preimage b := by
  rw [Trivalent.ofProp_eq_true_iff, Trivalent.compl_eq_true_iff, double_prohibition]

-- (59b)
theorem no_filtering_with_accommodation (hC : (Trivalent.gapExt C)ᶜ = R.preimage A ∩ R.preimage B)
    (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, (Trivalent.ofProp ((pexPossOr R a b w)ᶜ = .true)).joinMiddle (C w) = .undefined := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = .undefined := not_not.1 fun h ↦ hwB (hC ▸ Trivalent.mem_compl_gapExt.2 h).2
  have hne : pexPossOr R a b w ≠ .false := fun h ↦
    (pexIEII_eq_false_iff.1 h).2 (preimage_mono Set.subset_union_left hwa)
  exact ⟨w, by simp [this, hne]⟩

end Filtering

/-! ### Free choice under quantifiers, §5 -/

open Classical in
/-- *Exactly one* `x` in `S` satisfies `φ x`, with universal projection. The sentence is defined
where every instance in `S` is, and true where exactly one of them is true. -/
noncomputable def exactlyOne {D : Type*} (S : D → Prop) (φ : D → W → Trivalent) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ ∀ x, S x → φ x w ≠ .undefined) (fun w ↦ ∃! x, S x ∧ φ x w = .true)

section Quantified

variable {R : SetRel W W} {D : Type*} {S : D → Prop} {p q : D → Set W} {w : W}

/-- With universal projection, `¬∃x ∈ S[pex[◇(px ∨ qx)]]` is true exactly where universal double
prohibition holds ((70b), (71)), as (69) requires. -/
theorem universal_double_prohibition :
    (Trivalent.existsWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w))ᶜ = .true ↔
      (¬ ∃ x, S x ∧ w ∈ R.preimage (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.preimage (q x) := by
  simp only [Trivalent.compl_eq_true_iff, Trivalent.existsWeak_eq_false_iff, Subtype.forall,
    double_prohibition, not_exists, not_and, ← forall₂_and]

variable (hF : ∀ x, S x → FreeChoiceWitnesses R (p x) (q x))
include hF

/-- With universal projection, `∀x ∈ S[pex[◇(px ∨ qx)]]` is true exactly where universal free
choice holds, (66a) and (67). -/
theorem universal_free_choice :
    Trivalent.forallWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = .true ↔
      (∀ x, S x → w ∈ R.preimage (p x)) ∧ ∀ x, S x → w ∈ R.preimage (q x) := by
  simp only [Trivalent.forallWeak_eq_true_iff, Subtype.forall, ← forall₂_and]
  exact forall₂_congr fun x hx ↦ free_choice (hF x hx)

-- (73), (74)
theorem existential_free_choice
    (hw : Trivalent.existsWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = .true) :
    ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) :=
  let ⟨_, ⟨x, hx⟩, ha⟩ := Trivalent.existsWeak_eq_true_iff.1 hw
  ⟨x, hx, (free_choice (hF x hx)).1 ha⟩

/-- With the presupposition bound by the existential, `∃x ∈ S[pex[◇(px ∨ qx)]]` is true exactly
where existential free choice holds (75). -/
theorem existential_free_choice_bound :
    Trivalent.existsStrong (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = .true ↔
      ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) := by
  simp only [Trivalent.existsStrong_eq_true_iff, Subtype.exists, exists_prop]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦ free_choice (hF x hx)

/-- *Exactly one student can take Logic or Calculus* says that one student has free choice and
every other has double prohibition, (81), (83) and (76a). -/
theorem exactly_one_free_choice
    (hw : exactlyOne S (fun x ↦ pexPossOr R (p x) (q x)) w = .true) :
    ∃ x, S x ∧ (w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∉ R.preimage (p y) ∧ w ∉ R.preimage (q y) := by
  simp only [exactlyOne, Trivalent.condEvent_eq_true_iff] at hw
  obtain ⟨hpre, x, ⟨hx, ha⟩, huniq⟩ := hw
  refine ⟨x, hx, (free_choice (hF x hx)).1 ha, fun y hy hyx ↦ double_prohibition.1 ?_⟩
  have := hpre y hy
  have := fun ha' ↦ hyx (huniq y ⟨hy, ha'⟩)
  cases h : pexPossOr R (p y) (q y) w <;> simp_all

-- (82), (84), (77a)
theorem exactly_one_double_prohibition
    (hw : exactlyOne S (fun x ↦ (pexPossOr R (p x) (q x))ᶜ) w = .true) :
    ∃ x, S x ∧ (w ∉ R.preimage (p x) ∧ w ∉ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∈ R.preimage (p y) ∧ w ∈ R.preimage (q y) := by
  simp only [exactlyOne, Trivalent.condEvent_eq_true_iff, Pi.compl_apply, ne_eq,
    Trivalent.compl_eq_undefined_iff, Trivalent.compl_eq_true_iff] at hw
  obtain ⟨hpre, x, ⟨hx, ha⟩, huniq⟩ := hw
  refine ⟨x, hx, double_prohibition.1 ha, fun y hy hyx ↦ (free_choice (hF y hy)).1 ?_⟩
  have := hpre y hy
  have := fun ha' ↦ hyx (huniq y ⟨hy, ha'⟩)
  cases h : pexPossOr R (p y) (q y) w <;> simp_all

end Quantified

-- (66b), (68)
theorem universal_negative_free_choice {R : SetRel W W} {D : Type*} {S : D → Prop}
    {p q : D → Set W} {w : W} (h₁ : ∀ x, S x → ∃ w ∈ R.core (p x), w ∉ R.core (q x))
    (h₂ : ∀ x, S x → ∃ w ∈ R.core (q x), w ∉ R.core (p x))
    (h : ∀ x, S x → (R.core (p x ∩ q x)).Nonempty) :
    (Trivalent.existsWeak (fun x : {x // S x} ↦ pexNecAnd R (p x) (q x) w))ᶜ = .true ↔
      (¬ ∃ x, S x ∧ w ∈ R.core (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.core (q x) := by
  simp only [Trivalent.compl_eq_true_iff, Trivalent.existsWeak_eq_false_iff, Subtype.forall,
    not_exists, not_and, ← forall₂_and]
  exact forall₂_congr fun x hx ↦
    negative_free_choice_under_negation (h₁ x hx) (h₂ x hx) (h x hx)

end DelPinalBassiSauerland2024
