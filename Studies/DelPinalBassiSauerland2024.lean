module

public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.ConventionalImplicature
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
implicitly. Negation is `-` on trivalent propositions and the filtering disjunction (45) is
Middle Kleene `SignType.joinMiddle`. Negative factives use the transparent projection rule (30b),
as `ConventionalImplicature.TwoDim.negFactive` does, on `pex` read as a two-dimensional meaning,
since the factive denies belief in the at-issue prejacent. Quantifiers over `S` project the
presupposition universally, as the Weak Kleene quantifiers over the subtype of `S`, and
*exactly one* is `∃!` with the same projection.

## Errata

* The paper says after (9) that, other than the includable alternatives, it follows Bassi, Del
  Pinal and Sauerland (2021), whose trivalent entry (14) leaves the falsity conditions of the
  prejacent unchanged. But (20) has the presupposition of `pex^{IE+II}[□(T ∧ B)]` project from
  under negation, which needs the analogue for includable alternatives of the entry the earlier
  paper sets aside in its footnote 15. With the falsity conditions of the prejacent
  (`Exhaustification.pexIE`), `¬pex^{IE+II}[□(T ∧ B)]` would be true wherever `¬□T ∨ ¬□B` is. The
  paper does not discuss trivalent falsity conditions, so this is an undisclosed departure.

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
    pexIEII {φ, ψ} φ {φ, ψ} w ≠ 0 ↔ w ∉ ψ := by
  obtain ⟨w₀, hw₀, hw₀ψ⟩ := Set.not_subset.1 h
  have hM : IsMinimalCover {φ, ψ} φ {w₀} :=
    .singleton hw₀ (by rintro q (rfl | rfl) hq; exacts [le_rfl, absurd hq hw₀ψ])
  rw [pexIEII_ne_zero_iff_of_inter_eq_empty (by rw [hM.II_eq ⟨w₀, hw₀, by simp⟩]; grind)]
  grind [hM.isInnocentlyExcludable_iff]

/-! ### `pex^{IE+II}` on `◇(p ∨ q)`, §2.2 -/

section FreeChoice

variable (R : SetRel W W) (a b : Set W)

/-- `pexPossOr R a b` is `pex^{IE+II}[◇(a ∨ b)]` with the conjunctive alternative irrelevant,
as in (12) and (14). -/
noncomputable def pexPossOr : W → SignType :=
  pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) {R.preimage (a ∪ b), R.preimage a, R.preimage b}

variable {R a b} {w : W}

/-- `pex^{IE+II}[◇(a ∨ b)]` is false, and its negation true, exactly where double prohibition holds
(16). -/
theorem double_prohibition :
    pexPossOr R a b w = -1 ↔ w ∉ R.preimage a ∧ w ∉ R.preimage b := by
  simp only [pexPossOr, pexIEII_eq_neg_one_iff, pexIEII_ne_zero_iff, preimage_union]
  grind [Homogeneous]

variable (hF : FreeChoiceWitnesses R a b)
include hF

-- (12d)
theorem II_fcAlts_sdiff :
    II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} =
      {R.preimage a, R.preimage b} := by
  rw [II_fcAlts hF, Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
    Set.sdiff_singleton_eq_self]
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  obtain ⟨w₂, hw₂b, hw₂a⟩ := hF.only_right
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun he ↦ hw₂a (he ▸ preimage_mono Set.subset_union_right hw₂b),
    fun he ↦ hw₁b (he ▸ preimage_mono Set.subset_union_left hw₁a)⟩

private theorem II_fcAlts_sdiff_inter :
    II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
      {R.preimage (a ∪ b), R.preimage a, R.preimage b} = {R.preimage a, R.preimage b} := by
  rw [II_fcAlts_sdiff hF, Set.inter_eq_left]
  exact Set.subset_insert _ _

-- (14), (12c)
theorem pexPossOr_ne_zero_iff :
    pexPossOr R a b w ≠ 0 ↔ (w ∈ R.preimage a ↔ w ∈ R.preimage b) := by
  refine pexIEII_ne_zero_iff.trans <| (and_iff_right fun ψ hψ hR ↦ ?_).trans
    (by rw [II_fcAlts_sdiff_inter hF, homogeneous_pair])
  obtain rfl := (isInnocentlyExcludable_fcAlts_iff hF).1 hψ
  obtain ⟨w₀, ⟨hw₀a, hw₀b⟩, hw₀⟩ := hF.not_both
  grind [preimage_mono Set.subset_union_left hw₀a]

/-- `pex^{IE+II}[◇(a ∨ b)]` is true exactly where free choice holds, (14), since `◇(a ∨ b)` lies
between `◇a ∧ ◇b` and `◇a ∨ ◇b`. -/
theorem free_choice : pexPossOr R a b w = 1 ↔ w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  have hl : ⋂₀ (II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
      {R.preimage (a ∪ b), R.preimage a, R.preimage b}) ⊆ R.preimage (a ∪ b) := by
    rw [II_fcAlts_sdiff_inter hF, Set.sInter_pair, preimage_union]
    exact inf_le_sup
  have hu : R.preimage (a ∪ b) ⊆
      ⋃₀ (II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
        {R.preimage (a ∪ b), R.preimage a, R.preimage b}) := by
    rw [II_fcAlts_sdiff_inter hF, Set.sUnion_pair, preimage_union]
  rw [pexPossOr, pexIEII_eq_one_iff_forall_mem hl hu, ← pexPossOr, pexPossOr_ne_zero_iff hF,
    II_fcAlts_sdiff_inter hF]
  grind

open Classical in
/-- `pex^{IE+II}[◇(a ∨ b)]` is the plural predication that `a` and `b` are permitted, true where
both are, false where neither is, and undefined in between. -/
theorem pexPossOr_eq_barePlural :
    pexPossOr R a b = barePlural (fun x w ↦ w ∈ R.preimage x) {a, b} := by
  funext w
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · have := pexPossOr_ne_zero_iff (w := w) hF
    simp only [barePlural, SignType.supervaluation_eq_zero_iff, Finset.mem_insert,
      Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
    tauto
  · simp only [free_choice hF, barePlural, SignType.supervaluation_eq_one_iff, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- `pex^{IE+II}[◇(a ∨ b)]` is undefined exactly where one of `◇a` and `◇b` holds without the
other, the presupposition failure fn. 2 predicts. -/
theorem homogeneity_gap :
    Trivalent.gapExt (pexPossOr R a b) = symmDiff (R.preimage a) (R.preimage b) := by
  ext w
  have := pexPossOr_ne_zero_iff (w := w) hF
  simp only [Trivalent.mem_gapExt, Set.mem_symmDiff]
  tauto

-- fn. 2
theorem homogeneity_gap_neg :
    Trivalent.gapExt (-pexPossOr R a b) = symmDiff (R.preimage a) (R.preimage b) := by
  rw [← homogeneity_gap hF]
  ext w
  simp

theorem gapExt_pexPossOr_nonempty : (Trivalent.gapExt (pexPossOr R a b)).Nonempty := by
  obtain ⟨w, hwa, hwb⟩ := hF.only_left
  exact ⟨w, by rw [homogeneity_gap hF]; exact .inl ⟨hwa, hwb⟩⟩

/-- With every alternative relevant, `pex^{IE+II}[◇(a ∨ b)]` is true exactly where `exh^{IE+II}[◇(a
∨ b)]` is ((12e), (13)). -/
theorem pex_and_exh_agree :
    pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) (fcAlts R a b) w = 1 ↔
      w ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) := by
  have hII : II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩ fcAlts R a b =
      {R.preimage a, R.preimage b} := by
    rw [Set.inter_eq_left.2 fun _ h ↦ h.1.1, II_fcAlts_sdiff hF]
  have hc : R.preimage (a ∩ b) ∈ fcAlts R a b := by simp [fcAlts]
  rw [freeChoice hF, pexIEII_eq_one_iff, pexIEII_ne_zero_iff, hII, homogeneous_pair]
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
    pexPossOr R Tᶜ Bᶜ w = 1 ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  simpa only [preimage_compl, Set.mem_compl_iff] using free_choice hF

end NegatedFreeChoice

/-- Where world `4` permits both `0` and `1`, world `2` only `0`, world `3` only `1`, and world
`0` neither, `pex^{IE+II}[◇(p ∨ q)]` is true at `4`, suffers presupposition failure at `2` as
fn. 2 predicts, and is false at `0`. -/
example :
    let R : SetRel (Fin 5) (Fin 5) := {(2, 0), (3, 1), (4, 0), (4, 1)}
    pexPossOr R {0} {1} 4 = 1 ∧ pexPossOr R {0} {1} 2 = 0 ∧ pexPossOr R {0} {1} 0 = -1 := by
  intro R
  have hF : FreeChoiceWitnesses R {0} {1} :=
    ⟨⟨2, by simp [R], by simp [R]⟩, ⟨3, by simp [R], by simp [R]⟩, ⟨4, by simp [R], by simp [R]⟩⟩
  refine ⟨(free_choice hF).2 (by simp [R]), not_not.1 fun hp ↦ ?_,
    double_prohibition.2 (by simp [R])⟩
  simpa [R] using (pexPossOr_ne_zero_iff hF).1 hp

/-! ### `pex^{IE+II}` on `□(p ∧ q)`, §2.2 -/

section NegativeFreeChoice

variable (R : SetRel W W) (T B : Set W)

/-- The alternatives of `□(T ∧ B)` replace the conjunction by its conjuncts and their
disjunction. -/
def necAlts : Set (Set W) := {R.core (T ∩ B), R.core T, R.core B, R.core (T ∪ B)}

/-- `pexNecAnd R T B` is `pex^{IE+II}[□(T ∧ B)]` with the disjunctive alternative irrelevant, as
in (20) and (57). -/
noncomputable def pexNecAnd : W → SignType :=
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
theorem II_necAlts_sdiff :
    II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} =
      {R.core T, R.core B, R.core (T ∪ B)} := by
  obtain ⟨w₀, hw₀⟩ := id h
  have hII : II (necAlts R T B) (R.core (T ∩ B)) = necAlts R T B :=
    (Set.sep_subset _ _).antisymm fun q hq ↦ mem_II_of_cell_witness _ _ hq w₀
      ⟨hw₀, fun q hq ↦ absurd hq (not_isInnocentlyExcludable_necAlts h q),
        fun r hr ↦ subset_of_mem_necAlts hr.1 hw₀⟩ (subset_of_mem_necAlts hq hw₀)
  rw [hII, necAlts, Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
    Set.sdiff_singleton_eq_self]
  obtain ⟨wT, hwT, hwTB⟩ := h₁
  obtain ⟨wB, hwB, hwBT⟩ := h₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun he ↦ hwTB ?_, fun he ↦ hwBT ?_, fun he ↦ hwTB ?_⟩
  · exact core_mono Set.inter_subset_right (he ▸ hwT)
  · exact core_mono Set.inter_subset_left (he ▸ hwB)
  · exact core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT)

private theorem II_necAlts_sdiff_inter :
    II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩ {R.core (T ∩ B), R.core T, R.core B} =
      {R.core T, R.core B} := by
  have hne : R.core (T ∪ B) ≠ R.core (T ∩ B) := fun he ↦ by
    obtain ⟨wT, hwT, hwTB⟩ := h₁
    exact hwTB (core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT))
  rw [II_necAlts_sdiff h₁ h₂ h]
  ext α
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

-- (20)
theorem pexNecAnd_ne_zero_iff : pexNecAnd R T B w ≠ 0 ↔ (w ∈ R.core T ↔ w ∈ R.core B) :=
  pexIEII_ne_zero_iff.trans <|
    (and_iff_right fun ψ hψ _ ↦ absurd hψ (not_isInnocentlyExcludable_necAlts h ψ)).trans
      (by rw [II_necAlts_sdiff_inter h₁ h₂ h, homogeneous_pair])

/-- `pex^{IE+II}[□(T ∧ B)]` is false, and its negation true, exactly where negative free choice
holds (20). -/
theorem negative_free_choice_under_negation :
    pexNecAnd R T B w = -1 ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  have hl : ⋂₀ (II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩
      {R.core (T ∩ B), R.core T, R.core B}) ⊆ R.core (T ∩ B) := by
    rw [II_necAlts_sdiff_inter h₁ h₂ h, Set.sInter_pair, core_inter]
  have hu : R.core (T ∩ B) ⊆ ⋃₀ (II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩
      {R.core (T ∩ B), R.core T, R.core B}) := by
    rw [II_necAlts_sdiff_inter h₁ h₂ h, Set.sUnion_pair, core_inter]
    exact inf_le_sup
  rw [pexNecAnd, pexIEII_eq_neg_one_iff_forall_notMem hl hu, ← pexNecAnd,
    pexNecAnd_ne_zero_iff h₁ h₂ h, II_necAlts_sdiff_inter h₁ h₂ h]
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
  ⟨(· ∈ R.preimage (a ∪ b)), (pexPossOr R a b · ≠ 0)⟩

theorem toTrivalent_pexPossOrTwoDim : (pexPossOrTwoDim R a b).toTrivalent = pexPossOr R a b := by
  funext w
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_ <;>
    simp [pexPossOrTwoDim, pexPossOr, pexIEII_eq_one_iff]

/-- Under a negative factive the whole output of `pex` is presupposed, and that is free choice,
(21a) and (31c). -/
theorem free_choice_presupposed (hF : FreeChoiceWitnesses R a b)
    (believes : (W → Prop) → W → Prop) :
    (TwoDim.negFactive (pexPossOrTwoDim R a b) believes).notAtIssue w ↔
      w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  rw [← free_choice hF, ← toTrivalent_pexPossOrTwoDim, TwoDim.toTrivalent_eq_one_iff]
  rfl

-- (33a), (34c)
theorem negative_free_choice_presupposed {T B : Set W} (hF : FreeChoiceWitnesses R Tᶜ Bᶜ)
    (believes : (W → Prop) → W → Prop) :
    (TwoDim.negFactive (pexPossOrTwoDim R Tᶜ Bᶜ) believes).notAtIssue w ↔
      w ∉ R.core T ∧ w ∉ R.core B := by
  rw [← negative_free_choice hF, ← toTrivalent_pexPossOrTwoDim, TwoDim.toTrivalent_eq_one_iff]
  rfl

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

variable {R : SetRel W W} {a b A B : Set W} {C : W → SignType}

/-- In `¬pex[◇(a ∨ b)] ∨ C`, the filtering disjunction (45) filters the free-choice presupposition,
and only homogeneity projects ((53), §4.4). -/
theorem free_choice_filtered (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b)
    (hC : Function.support C = R.preimage A ∩ R.preimage B) :
    Function.support (fun w ↦ (-pexPossOr R a b w).joinMiddle (C w)) =
      Function.support (pexPossOr R a b) := by
  ext w
  have h₁ := (free_choice (w := w) hF).1
  have h₂ : w ∈ R.preimage A ∩ R.preimage B → C w ≠ 0 := fun h ↦ Function.mem_support.1 (hC ▸ h)
  simp only [Function.mem_support, ne_eq, SignType.joinMiddle_eq_zero_iff, SignType.neg_eq_zero_iff,
    SignType.neg_eq_neg_one_iff]
  grind [preimage_mono hA, preimage_mono hB]

open Classical in
-- (46c)
theorem no_filtering_without_pex (hC : Function.support C = R.preimage A ∩ R.preimage B)
    (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, (-SignType.ofProp (w ∈ R.preimage (a ∪ b))).joinMiddle (C w) = 0 := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = 0 := Function.notMem_support.1 (hC ▸ fun h ↦ hwB h.2)
  exact ⟨w, by simp [this, preimage_mono Set.subset_union_left hwa]⟩

open Classical in
-- (47c)
theorem exh_filters (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b)
    (hC : Function.support C = R.preimage A ∩ R.preimage B) (w : W) :
    (-SignType.ofProp (w ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)))).joinMiddle (C w) ≠ 0 := by
  have h₂ : w ∈ R.preimage A ∩ R.preimage B → C w ≠ 0 := fun h ↦ Function.mem_support.1 (hC ▸ h)
  have := @preimage_mono _ _ R _ _ hA
  have := @preimage_mono _ _ R _ _ hB
  simp only [freeChoice hF, ne_eq, SignType.joinMiddle_eq_zero_iff, SignType.neg_eq_zero_iff,
    SignType.ofProp_ne_zero, SignType.neg_eq_neg_one_iff, SignType.ofProp_eq_one_iff]
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
    (h : (R.core (A ∩ B)).Nonempty) (hC : Function.support C = (R.core a)ᶜ ∩ (R.core b)ᶜ) :
    Function.support (fun w ↦ (pexNecAnd R A B w).joinMiddle (C w)) =
      Function.support (pexNecAnd R A B) := by
  ext w
  have := (negative_free_choice_under_negation (w := w) h₁ h₂ h).1
  have h₃ : w ∈ (R.core a)ᶜ ∩ (R.core b)ᶜ → C w ≠ 0 := fun h ↦ Function.mem_support.1 (hC ▸ h)
  have := @core_mono _ _ R _ _ hA
  have := @core_mono _ _ R _ _ hB
  simp only [Function.mem_support, ne_eq, SignType.joinMiddle_eq_zero_iff]
  grind

open Classical in
-- (56c)
theorem no_negative_filtering_with_exh (h : (R.core (A ∩ B)).Nonempty)
    (hC : Function.support C = (R.core a)ᶜ ∩ (R.core b)ᶜ) (hw : ∃ w ∈ R.core a, w ∉ R.core B) :
    ∃ w, (SignType.ofProp (w ∈ exhIEII (necAlts R A B) (R.core (A ∩ B)))).joinMiddle (C w) = 0 := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = 0 := Function.notMem_support.1 (hC ▸ fun h ↦ h.1 hwa)
  have hn : w ∉ exhIEII (necAlts R A B) (R.core (A ∩ B)) := by
    rw [exhIEII_necAlts h]
    exact fun hAB ↦ hwB (core_mono Set.inter_subset_right hAB)
  exact ⟨w, by simp [this, hn]⟩

-- (59c)
theorem double_prohibition_accommodated {w : W} :
    SignType.ofProp (-pexPossOr R a b w = 1) = 1 ↔ w ∉ R.preimage a ∧ w ∉ R.preimage b := by
  rw [SignType.ofProp_eq_one_iff, SignType.neg_eq_one_iff, double_prohibition]

-- (59b)
theorem no_filtering_with_accommodation (hC : Function.support C = R.preimage A ∩ R.preimage B)
    (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, (SignType.ofProp (-pexPossOr R a b w = 1)).joinMiddle (C w) = 0 := by
  obtain ⟨w, hwa, hwB⟩ := hw
  have : C w = 0 := Function.notMem_support.1 (hC ▸ fun h ↦ hwB h.2)
  have hne : pexPossOr R a b w ≠ -1 := fun h ↦
    (pexIEII_eq_neg_one_iff.1 h).2 (preimage_mono Set.subset_union_left hwa)
  exact ⟨w, by simp [this, hne]⟩

end Filtering

/-! ### Free choice under quantifiers, §5 -/

open Classical in
/-- *Exactly one* `x` in `S` satisfies `φ x`, with universal projection. The sentence is defined
where every instance in `S` is, and true where exactly one of them is true. -/
noncomputable def exactlyOne {D : Type*} (S : D → Prop) (φ : D → W → SignType) : W → SignType :=
  {w | ∀ x, S x → φ x w ≠ 0}.indicator fun w ↦ SignType.ofProp (∃! x, S x ∧ φ x w = 1)

section Quantified

variable {R : SetRel W W} {D : Type*} {S : D → Prop} {p q : D → Set W} {w : W}

/-- With universal projection, `¬∃x ∈ S[pex[◇(px ∨ qx)]]` is true exactly where universal double
prohibition holds ((70b), (71)), as (69) requires. -/
theorem universal_double_prohibition :
    -Trivalent.existsWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = 1 ↔
      (¬ ∃ x, S x ∧ w ∈ R.preimage (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.preimage (q x) := by
  simp only [SignType.neg_eq_one_iff, Trivalent.existsWeak_eq_neg_one_iff, Subtype.forall,
    double_prohibition, not_exists, not_and, ← forall₂_and]

variable (hF : ∀ x, S x → FreeChoiceWitnesses R (p x) (q x))
include hF

/-- With universal projection, `∀x ∈ S[pex[◇(px ∨ qx)]]` is true exactly where universal free
choice holds, (66a) and (67). -/
theorem universal_free_choice :
    Trivalent.forallWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = 1 ↔
      (∀ x, S x → w ∈ R.preimage (p x)) ∧ ∀ x, S x → w ∈ R.preimage (q x) := by
  simp only [Trivalent.forallWeak_eq_one_iff, Subtype.forall, ← forall₂_and]
  exact forall₂_congr fun x hx ↦ free_choice (hF x hx)

-- (73), (74)
theorem existential_free_choice
    (hw : Trivalent.existsWeak (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = 1) :
    ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) :=
  let ⟨_, ⟨x, hx⟩, ha⟩ := Trivalent.existsWeak_eq_one_iff.1 hw
  ⟨x, hx, (free_choice (hF x hx)).1 ha⟩

/-- With the presupposition bound by the existential, `∃x ∈ S[pex[◇(px ∨ qx)]]` is true exactly
where existential free choice holds (75). -/
theorem existential_free_choice_bound :
    Trivalent.existsStrong (fun x : {x // S x} ↦ pexPossOr R (p x) (q x) w) = 1 ↔
      ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) := by
  simp only [Trivalent.existsStrong_eq_one_iff, Subtype.exists, exists_prop]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦ free_choice (hF x hx)

/-- *Exactly one student can take Logic or Calculus* says that one student has free choice and
every other has double prohibition, (81), (83) and (76a). -/
theorem exactly_one_free_choice
    (hw : exactlyOne S (fun x ↦ pexPossOr R (p x) (q x)) w = 1) :
    ∃ x, S x ∧ (w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∉ R.preimage (p y) ∧ w ∉ R.preimage (q y) := by
  simp only [exactlyOne, Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq,
    SignType.ofProp_eq_one_iff] at hw
  obtain ⟨hpre, x, ⟨hx, ha⟩, huniq⟩ := hw
  refine ⟨x, hx, (free_choice (hF x hx)).1 ha, fun y hy hyx ↦ double_prohibition.1 ?_⟩
  have := hpre y hy
  have := fun ha' ↦ hyx (huniq y ⟨hy, ha'⟩)
  cases h : pexPossOr R (p y) (q y) w <;> simp_all

-- (82), (84), (77a)
theorem exactly_one_double_prohibition
    (hw : exactlyOne S (fun x ↦ -pexPossOr R (p x) (q x)) w = 1) :
    ∃ x, S x ∧ (w ∉ R.preimage (p x) ∧ w ∉ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∈ R.preimage (p y) ∧ w ∈ R.preimage (q y) := by
  simp only [exactlyOne, Trivalent.indicator_apply_eq_one_iff, Set.mem_ofPred_eq,
    SignType.ofProp_eq_one_iff, Pi.neg_apply, ne_eq, SignType.neg_eq_zero_iff,
    SignType.neg_eq_one_iff] at hw
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
    -Trivalent.existsWeak (fun x : {x // S x} ↦ pexNecAnd R (p x) (q x) w) = 1 ↔
      (¬ ∃ x, S x ∧ w ∈ R.core (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.core (q x) := by
  simp only [SignType.neg_eq_one_iff, Trivalent.existsWeak_eq_neg_one_iff, Subtype.forall,
    not_exists, not_and, ← forall₂_and]
  exact forall₂_congr fun x hx ↦
    negative_free_choice_under_negation (h₁ x hx) (h₂ x hx) (h x hx)

end DelPinalBassiSauerland2024
