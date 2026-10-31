module

public import Studies.Booth2022a
public import Mathlib.Tactic.FinCases

/-!
# Booth (2022b): Necessity modals, disjunctions, and collectivity

[booth-2022b] resolves Ross's Puzzle in the bilateral minimal covering semantics of [booth-2022a],
the theory-layer `MinimalCovering`: the alternatives of a necessity modal's prejacent must form a
minimal cover of the relevant worlds, so `□(p ∨ q)` licenses the Independence inferences and the
Ross inference from `□p` to `□(p ∨ q)` is strongly invalid. The results on atoms restate those of
[booth-2022a]. The new content generalizes the Ross and Independence facts from atoms to every
disjunction whose disjuncts share no alternatives ([Ross](##Formula.ross_strongly_invalid),
[Independence](##Formula.independence)), resting on the [compactness of
alternatives](##Formula.fg_eval). The closing reading of `□` as a collective predicate of the
plurality of propositions a disjunction denotes is not formalized.

## Implementation notes

* The semantics is `MinimalCovering`: `Question W` supplies Def 10's subset-closed families
  (`Question.ofSet` is `↓{·}` of Def 11, `Question.info` is `info` of Def 12, `Question.alt` is
  `alt` of Def 13), Def 10's bilateral propositions are `Kalman (Question W)`, whose
  third bullet `P⁺ ∩ P⁻ = {∅}` is disjointness in `Question W`, and Def 14's ¬-, ∧- and ∨-clauses
  are its `ᶜ`, `⊓` and `⊔`. Def 14 defines `◇φ` as `¬□¬φ`, which is
  `MinimalCovering.possibility_eq_compl_necessity_compl`.
* Def 14's □⁺ clause adds the conjunct `R(w) ≠ ∅`, which [booth-2022a]'s clause lacks. The two
  differ only on propositions without alternatives, and every sentence has one (Fact 5), so they
  agree on sentences (`Formula.truth_necessity_eq`) and this file uses the substrate's clause.
* Def 8's language is the `!`-free fragment of `MinimalCovering.Formula`; Fact 5 is proved for
  the whole language.
* Def 17 writes `w ∈ ⟦φ⟧⁺` for a world `w` and a set of states; it is read as
  `w ∈ info ⟦φ⟧⁺`, equivalently `{w} ∈ ⟦φ⟧⁺` (`MinimalCovering.mem_truth_iff`).
* Def 22 is mathlib's `IncompRel` for the positive interpretations; for atoms it is
  [booth-2022a]'s admissibility (`nonHurford_atom_iff`).
* Entailment over a model (Def 18) is the `⊨[V, R]` of `MinimalCovering`, inclusion of truth sets,
  and strong invalidity (Def 21) is disjointness of the premises' truth set from the
  conclusion's.
* Facts 12 and 13 need no non-Hurford hypothesis.
* Figures 1 and 2 reprint those of [booth-2022a] and are formalized there
  (`Booth2022a.Figures`).

## Errata

* The meta-language Facts 6 and 7 are stated for every non-Hurford disjunction (Def 22), but their
  proofs assume that no alternative of either disjunct is a state of the other,
  `Disjoint (alt ⟦φ⟧⁺) ⟦ψ⟧⁺`, which is strictly stronger. Under Def 22 both facts fail on
  three-world models ([Fact 7](##not_forall_disjoint_of_nonHurford),
  [Fact 6](##not_forall_independence_of_nonHurford)); under the alternative-wise condition the
  proofs go through. For atoms the two conditions coincide, so the object-language Facts 7–13
  stand.

## References

* [booth-2022b]
* [booth-2022a]
* [simons-2005], the super covers of the Diversity analysis.
* [aloni-2022], Aloni's bilateral state-based modal logic; Booth cites her 2018 manuscript
  "FC disjunction in state-based semantics" (fn. 9).
* [ciardelli-groenendijk-roelofsen-2018], standard inquisitive semantics, in which `¬¬φ` and `φ`
  differ (§3.1).
-/

@[expose] public section

namespace Booth2022b

open MinimalCovering Question

variable {W : Type*}

/-! ### Kratzer's semantics (Def 1) -/

-- Fact 1
theorem kratzer_monotone (R : W → Set W) : Monotone fun A : Set W ↦ {w | R w ⊆ A} :=
  fun _ _ hAB _ hw ↦ hw.trans hAB

theorem truth_necessity_subset (R : W → Set W) (φ : Kalman (Question W)) :
    truth (necessity R φ) ⊆ {w | R w ⊆ truth φ} := by
  rw [truth_necessity]
  exact fun _ h ↦ h.subset_sUnion.trans φ.pro.sUnion_alt_subset_info

-- Figure 1
theorem not_monotone_necessity :
    ¬ ∀ φ ψ : Kalman (Question Booth2022a.Figures.W4), truth φ ⊆ truth ψ →
      truth (necessity Booth2022a.Figures.rP φ) ⊆ truth (necessity Booth2022a.Figures.rP ψ) :=
  fun h ↦ (Booth2022a.ross_gap Booth2022a.Figures.incomp_val Booth2022a.Figures.box_p).1
    (h (atom Booth2022a.Figures.vp) (atom Booth2022a.Figures.vp ⊔ atom Booth2022a.Figures.vq)
      (by simp) Booth2022a.Figures.box_p)

/-! ### Non-Hurford disjunctions (Def 22) -/

/-- **Booth Def 22**: `φ ∨ ψ` is non-Hurford when the positive interpretations of the disjuncts
are incomparable. -/
def NonHurford (φ ψ : Kalman (Question W)) : Prop :=
  IncompRel (· ≤ ·) φ.pro ψ.pro

theorem NonHurford.symm {φ ψ : Kalman (Question W)} (h : NonHurford φ ψ) : NonHurford ψ φ :=
  IncompRel.symm h

theorem nonHurford_atom_iff {Vp Vq : Set W} :
    NonHurford (atom Vp) (atom Vq) ↔ IncompRel (· ⊆ ·) Vp Vq :=
  and_congr (not_congr ofSet_le_ofSet_iff) (not_congr ofSet_le_ofSet_iff)

theorem alt_sup_pro_eq_union {φ ψ : Kalman (Question W)}
    (hφψ : Disjoint (alt φ.pro) ψ.pro) (hψφ : Disjoint (alt ψ.pro) φ.pro) :
    alt (φ ⊔ ψ).pro = alt φ.pro ∪ alt ψ.pro := by
  refine (alt_sup_subset_union φ.pro ψ.pro).antisymm ?_
  rintro q (hq | hq)
  · exact mem_alt_sup_of_alt_left hq fun r hr hqr ↦
      (Set.disjoint_left.1 hφψ hq (ψ.pro.downward_closed r hr q hqr)).elim
  · exact mem_alt_sup_of_alt_right hq fun r hr hqr ↦
      (Set.disjoint_left.1 hψφ hq (φ.pro.downward_closed r hr q hqr)).elim

/-! ### The language (Def 8) and compactness (Fact 5) -/

namespace Formula

variable {At : Type*}

-- Fact 3
theorem eval_neg_neg (V : At → Set W) (R : W → Set W) (φ : MinimalCovering.Formula At) :
    Formula.eval V R (∼∼φ) = Formula.eval V R φ :=
  rfl

/-- Both interpretations of a sentence are finitely generated, so each is generated by its finitely
many alternatives (Booth Fact 5). -/
theorem fg_eval (V : At → Set W) (R : W → Set W) (φ : MinimalCovering.Formula At) :
    (Formula.eval V R φ).pro.FG ∧ (Formula.eval V R φ).con.FG := by
  induction φ generalizing R with
  | atom p => exact ⟨fg_ofSet _, fg_ofSet _⟩
  | neg φ ih => exact (ih R).symm
  | conj φ ψ ihφ ihψ => exact ⟨(ihφ R).1.inf (ihψ R).1, (ihφ R).2.sup (ihψ R).2⟩
  | disj φ ψ ihφ ihψ => exact ⟨(ihφ R).1.sup (ihψ R).1, (ihφ R).2.inf (ihψ R).2⟩
  | bang φ _ => exact ⟨fg_ofSet _, fg_ofSet _⟩
  | cond φ ψ _ ihψ => exact ihψ _
  | box φ _ => exact ⟨fg_ofSet _, fg_ofSet _⟩
  | diamond φ _ => exact ⟨fg_ofSet _, fg_ofSet _⟩

-- Fact 5 [booth-2022a]
theorem truth_necessity_eq (V : At → Set W) (R : W → Set W) (φ : MinimalCovering.Formula At) :
    truth (Formula.eval V R (□φ)) =
      {w | (R w).Nonempty ∧ IsMinCover (alt (Formula.eval V R φ).pro) (R w)} := by
  change truth (necessity R (Formula.eval V R φ)) = _
  rw [truth_necessity]
  ext w
  exact ⟨fun h ↦ ⟨h.nonempty (fg_eval V R φ).1.isNormal.alt_nonempty, h⟩, And.right⟩

end Formula

/-! ### The meta-language Facts 6 and 7

Booth states both facts for every non-Hurford disjunction (Def 22). Their proofs use that no
alternative of either disjunct is a state of the other, which is strictly stronger; the facts hold
under that condition and fail under Def 22. -/

-- Fact 7
theorem ross_strongly_invalid_of_alt {φ ψ : Kalman (Question W)}
    (hφψ : Disjoint (alt φ.pro) ψ.pro) (hψφ : Disjoint (alt ψ.pro) φ.pro)
    (hψ : (alt ψ.pro).Nonempty) (R : W → Set W) :
    Disjoint (truth (necessity R φ)) (truth (necessity R (φ ⊔ ψ))) := by
  refine Set.disjoint_left.2 fun w h₁ h₂ ↦ ?_
  rw [truth_necessity, Set.mem_ofPred_eq] at h₁ h₂
  rw [alt_sup_pro_eq_union hφψ hψφ] at h₂
  obtain ⟨b, hb⟩ := hψ
  exact Set.disjoint_left.1 hψφ hb (mem_of_mem_alt
    (h₂.le_of_le h₁.subset_sUnion Set.subset_union_left (Set.mem_union_right _ hb)))

-- Fact 6
theorem inter_diff_truth_nonempty_of_alt {φ ψ : Kalman (Question W)}
    (hφψ : Disjoint (alt φ.pro) ψ.pro) (hψφ : Disjoint (alt ψ.pro) φ.pro)
    (hφ : (alt φ.pro).Nonempty) (hψ : ψ.pro.IsNormal) {R : W → Set W} {w : W}
    (h : w ∈ truth (necessity R (φ ⊔ ψ))) : (R w ∩ (truth φ \ truth ψ)).Nonempty := by
  rw [truth_necessity, Set.mem_ofPred_eq, alt_sup_pro_eq_union hφψ hψφ] at h
  obtain ⟨a, ha⟩ := hφ
  obtain ⟨v, hvR, hva, hv⟩ := (isMinCover_iff_inter_sdiff.1 h).2 a (.inl ha)
  refine ⟨v, hvR, subset_info_of_mem (mem_of_mem_alt ha) hva, ?_⟩
  rintro ⟨s, hs, hvs⟩
  obtain ⟨b, hb, hsb⟩ := hψ s hs
  exact hv ⟨b, ⟨.inr hb, fun hba ↦
    Set.disjoint_left.1 hφψ ha (hba ▸ mem_of_mem_alt hb)⟩, hsb hvs⟩

namespace Formula

variable {At : Type*} {V : At → Set W} {R : W → Set W} {φ ψ : MinimalCovering.Formula At}

/-- **Booth Fact 7** for sentences under the alternative-wise non-Hurford condition; Fact 5
supplies the alternative of `ψ`. -/
theorem ross_strongly_invalid
    (hφψ : Disjoint (alt (Formula.eval V R φ).pro) (Formula.eval V R ψ).pro)
    (hψφ : Disjoint (alt (Formula.eval V R ψ).pro) (Formula.eval V R φ).pro) :
    Disjoint (truth (Formula.eval V R (□φ))) (truth (Formula.eval V R (□(φ ⋎ ψ)))) :=
  ross_strongly_invalid_of_alt hφψ hψφ (fg_eval V R ψ).1.isNormal.alt_nonempty R

/-- **Booth Fact 6** for sentences under the alternative-wise non-Hurford condition; Fact 5
supplies the alternatives and the normality of the disjuncts. -/
theorem independence
    (hφψ : Disjoint (alt (Formula.eval V R φ).pro) (Formula.eval V R ψ).pro)
    (hψφ : Disjoint (alt (Formula.eval V R ψ).pro) (Formula.eval V R φ).pro) {w : W}
    (h : w ∈ truth (Formula.eval V R (□(φ ⋎ ψ)))) :
    (R w ∩ (truth (Formula.eval V R φ) \ truth (Formula.eval V R ψ))).Nonempty ∧
      (R w ∩ (truth (Formula.eval V R ψ) \ truth (Formula.eval V R φ))).Nonempty := by
  have hφ := (fg_eval V R φ).1.isNormal
  have hψ := (fg_eval V R ψ).1.isNormal
  refine ⟨inter_diff_truth_nonempty_of_alt hφψ hψφ hφ.alt_nonempty hψ h,
    inter_diff_truth_nonempty_of_alt hψφ hφψ hψ.alt_nonempty hφ ?_⟩
  rw [sup_comm]
  exact h

end Formula

/-- Booth Fact 7 as printed, for every non-Hurford disjunction of Def 22, fails on a three-world
model with `R(0) = {0, 1}`. -/
theorem not_forall_disjoint_of_nonHurford :
    ¬ ∀ (W : Type) (R : W → Set W) (φ ψ : Kalman (Question W)), NonHurford φ ψ →
      Disjoint (truth (necessity R φ)) (truth (necessity R (φ ⊔ ψ))) := by
  intro hall
  have h01 : IncompRel (· ⊆ ·) ({0} : Set (Fin 3)) {1} :=
    ⟨fun h ↦ by simpa using h (Set.mem_singleton 0), fun h ↦ by simpa using h (Set.mem_singleton 1)⟩
  have hNH : NonHurford (atom ({0} : Set (Fin 3)) ⊔ atom {1}) (atom {0, 2}) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ({1} : Set (Fin 3)) ∈ (atom ({0, 2} : Set (Fin 3))).pro := h (by simp)
      simp at this
    · have : ({0, 2} : Set (Fin 3)) ∈ (atom {0} ⊔ atom ({1} : Set (Fin 3))).pro := h (by simp)
      simp at this
  have hpos : (atom ({0} : Set (Fin 3)) ⊔ atom {1} ⊔ atom {0, 2}).pro =
      ofSet {0, 2} ⊔ ofSet {1} := by
    simp only [Kalman.pro_sup, pro_atom]
    rw [sup_right_comm, sup_eq_right.2 (ofSet_le_ofSet_iff.2 (by simp))]
  have hne : ({0, 2} : Set (Fin 3)) ≠ {1} := fun h ↦
    absurd (h ▸ (show (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)) (by simp)
  refine Set.disjoint_left.1 (hall (Fin 3) (fun _ ↦ {0, 1}) _ _ hNH)
    (show (0 : Fin 3) ∈ _ from ?_) ?_
  · rw [truth_necessity, Set.mem_ofPred_eq, alt_sup_atom h01, isMinCover_pair_iff h01.ne]
    refine ⟨?_, ?_, ?_⟩ <;> simp [Set.insert_subset_iff]
  · rw [truth_necessity, Set.mem_ofPred_eq, hpos, alt_ofSet_sup_ofSet (by simp) (by simp),
      isMinCover_pair_iff hne]
    refine ⟨?_, ?_, ?_⟩ <;> simp [Set.insert_subset_iff]

/-- Booth Fact 6 as printed, for every non-Hurford disjunction of Def 22, fails on a three-world
model with `R(0) = W`. -/
theorem not_forall_independence_of_nonHurford :
    ¬ ∀ (W : Type) (R : W → Set W) (φ ψ : Kalman (Question W)), NonHurford φ ψ →
      ∀ w ∈ truth (necessity R (φ ⊔ ψ)),
        (R w ∩ (truth φ \ truth ψ)).Nonempty ∧ (R w ∩ (truth ψ \ truth φ)).Nonempty := by
  intro hall
  have hNH : NonHurford (atom ({0, 1} : Set (Fin 3))) (atom {0} ⊔ atom {1, 2}) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ({0, 1} : Set (Fin 3)) ∈ (atom {0} ⊔ atom ({1, 2} : Set (Fin 3))).pro := h (by simp)
      simp [Set.insert_subset_iff] at this
    · have : ({1, 2} : Set (Fin 3)) ∈ (atom ({0, 1} : Set (Fin 3))).pro := h (by simp)
      simp [Set.insert_subset_iff] at this
  have hpos : (atom ({0, 1} : Set (Fin 3)) ⊔ (atom {0} ⊔ atom {1, 2})).pro =
      ofSet {0, 1} ⊔ ofSet {1, 2} := by
    simp only [Kalman.pro_sup, pro_atom]
    rw [← sup_assoc, sup_eq_left.2 (ofSet_le_ofSet_iff.2 (by simp))]
  have hne : ({0, 1} : Set (Fin 3)) ≠ {1, 2} := fun h ↦
    absurd (h ▸ (show (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) by simp)) (by simp)
  have hbox : (0 : Fin 3) ∈ truth (necessity (fun _ ↦ Set.univ)
      (atom ({0, 1} : Set (Fin 3)) ⊔ (atom {0} ⊔ atom {1, 2}))) := by
    rw [truth_necessity, Set.mem_ofPred_eq, hpos, alt_ofSet_sup_ofSet
      (by simp [Set.insert_subset_iff]) (by simp [Set.insert_subset_iff]), isMinCover_pair_iff hne]
    refine ⟨fun x _ ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
    · fin_cases x <;> simp
    · simpa using h (Set.mem_univ 2)
    · simpa using h (Set.mem_univ 0)
  obtain ⟨x, hx⟩ := (hall (Fin 3) (fun _ ↦ Set.univ) _ _ hNH 0 hbox).1
  fin_cases x <;> simp at hx

/-! ### The object-language Facts 7–13

Facts 9–13 are [booth-2022a]'s Facts 1, 4, 2, 7 and 6, stated here under Def 22's hypothesis. -/

section Atomic

variable {At : Type*} (V : At → Set W) (R : W → Set W) {p q : At}

-- Fact 7
theorem ross_strongly_invalid (h : NonHurford (atom (V p)) (atom (V q))) :
    Disjoint (truth (Formula.eval V R (□.atom p)))
      (truth (Formula.eval V R (□(.atom p ⋎ .atom q)))) :=
  Set.disjoint_left.2 fun _ hw ↦ (Booth2022a.ross_gap (nonHurford_atom_iff.1 h) hw).1

-- Fact 8
theorem extended_ross_strongly_invalid (h : NonHurford (atom (V p)) (atom (V q))) :
    Disjoint (truth (Formula.eval V R (□.atom p)) ∩
        truth (Formula.eval V R (◇.atom q)))
      (truth (Formula.eval V R (□(.atom p ⋎ .atom q)))) :=
  (ross_strongly_invalid V R h).mono_left Set.inter_subset_left

-- Fact 9
theorem independence_left (h : NonHurford (atom (V p)) (atom (V q))) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom p ⋏ ∼.atom q) :=
  Booth2022a.box_independence_left (nonHurford_atom_iff.1 h)

-- Fact 9
theorem independence_right (h : NonHurford (atom (V p)) (atom (V q))) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom q ⋏ ∼.atom p) :=
  Booth2022a.box_independence_right (nonHurford_atom_iff.1 h)

-- Fact 10
theorem free_choice_left (h : NonHurford (atom (V p)) (atom (V q))) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇.atom p :=
  Booth2022a.free_choice (nonHurford_atom_iff.1 h)

-- Fact 10
theorem free_choice_right (h : NonHurford (atom (V p)) (atom (V q))) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇.atom q :=
  Booth2022a.free_choice_right (nonHurford_atom_iff.1 h)

-- Fact 11
theorem independence_conditional_left (h : NonHurford (atom (V p)) (atom (V q))) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom p ⇒ □.atom q :=
  Booth2022a.box_conditional_left (nonHurford_atom_iff.1 h)

-- Fact 11
theorem independence_conditional_right (h : NonHurford (atom (V p)) (atom (V q))) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom q ⇒ □.atom p :=
  Booth2022a.box_conditional_right (nonHurford_atom_iff.1 h)

-- Fact 12
theorem unnecessity_distribution_left (p q : At) :
    ∼□(.atom p ⋎ .atom q) ⊨[V, R] ∼□.atom p :=
  Booth2022a.unnecessity_distribution_left V R p q

-- Fact 12
theorem unnecessity_distribution_right (p q : At) :
    ∼□(.atom p ⋎ .atom q) ⊨[V, R] ∼□.atom q :=
  Booth2022a.unnecessity_distribution_right V R p q

-- Fact 13
theorem impossibility_distribution_left (p q : At) :
    ∼◇(.atom p ⋎ .atom q) ⊨[V, R] ∼◇.atom p :=
  Booth2022a.impossibility_distribution_left V R p q

-- Fact 13
theorem impossibility_distribution_right (p q : At) :
    ∼◇(.atom p ⋎ .atom q) ⊨[V, R] ∼◇.atom q :=
  Booth2022a.impossibility_distribution_right V R p q

end Atomic

end Booth2022b
