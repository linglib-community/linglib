module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Team.Operations
public import Linglib.Semantics.Questions.Basic
public import Linglib.Core.Order.UpperLower.CompleteLattice

/-!
# Inquisitive logic

Inquisitive logic interprets formulas by support at information states, sets of possible worlds,
rather than by truth at worlds, so that questions and statements share one language: the
inquisitive disjunction `φ \\/ ψ` is supported by a state that supports either disjunct. The
propositional system InqB has `⊥`, `∧`, `→` and `\\/` over atoms, and inquisitive modal logic adds
the modalities `□` and `⊞`, interpreted over a model that relates each world to a set of states.
This file develops basic results about support, including the empty state property,
truth-conditionality, the proposition a formula expresses, and the validities of the two
modalities.

## Main definitions

* `Inquisitive.Model`: a valuation and a map from worlds to sets of information states.
* `Inquisitive.Formula`: formulas with `\\/`, `□` and `⊞`; the modal-free ones
  (`Inquisitive.Formula.IsModalFree`) are those of InqB.
* `Inquisitive.support`: the lower set of states supporting a formula.
* `Inquisitive.TruthConditional`: the formulas whose support in a model is truth at every world.
* `Inquisitive.proposition`: the proposition a formula expresses, as a `Question`.

## Implementation notes

The support of a modal-free formula depends only on the valuation
(`Inquisitive.support_eq_of_isModalFree`), so InqB is the modal-free fragment of the modal
language rather than a language of its own. States are finite sets of worlds, as teams are in the
other team logics, so that support is decidable; over finitely many worlds this loses nothing,
and `Inquisitive.proposition` carries a support set along `Finset W ≃o Set W`. The states related
to a world need not form a downward-closed set, since, as Ciardelli notes after Meißner and Otto,
dropping this requirement yields the same logic.

## References

* [I. Ciardelli, *Inquisitive Logic: Consequence and Inference in the Realm of Questions*
  (2022)][ciardelli-2022]
* [I. Ciardelli, *Modalities in the realm of questions: Axiomatizing inquisitive epistemic
  logic* (2014)][ciardelli-2014]
* [I. Ciardelli and F. Roelofsen, *Inquisitive dynamic epistemic logic*
  (2015)][ciardelli-roelofsen-2015]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Inquisitive Semantics*
  (2018)][ciardelli-groenendijk-roelofsen-2018]
* [A. Anttila, *Not Nothing: Nonemptiness in Team Semantics* (2025)][anttila-2025]
-/

@[expose] public section

namespace Inquisitive

variable {W Atom : Type*}

/-! ### Models (§8.3) -/

/-- An inquisitive model has a valuation and relates each world `w` to a set `Σ(w)` of
information states, under the epistemic reading the states in which the agent's issues are
settled. -/
structure Model (W Atom : Type*) where
  /-- `inq w` is the set `Σ(w)` of states related to `w`. -/
  inq : W → Finset (Finset W)
  /-- `val p w` says that the atom `p` is true at the world `w`. -/
  val : Atom → W → Prop

namespace Model

variable [DecidableEq W] (M : Model W Atom)

/-- The induced accessibility `σ(w) = ⋃ Σ(w)`, the agent's epistemic state at `w`. -/
def access (w : W) : Finset W := (M.inq w).sup id

@[simp] theorem mem_access {w v : W} : v ∈ M.access w ↔ ∃ t ∈ M.inq w, v ∈ t := by
  simp [access]

theorem subset_access {w : W} {t : Finset W} (ht : t ∈ M.inq w) : t ⊆ M.access w :=
  Finset.le_sup (f := id) ht

end Model

/-- A Kripke model as the inquisitive modal model relating each world to the single state `R[w]`
of its successors. -/
def _root_.ModalLogic.KripkeModel.toInquisitive (M : ModalLogic.KripkeModel W Atom) :
    Model W Atom :=
  ⟨fun w ↦ {M.access w}, M.val⟩

@[simp] theorem _root_.ModalLogic.KripkeModel.access_toInquisitive [DecidableEq W]
    (M : ModalLogic.KripkeModel W Atom) (w : W) : M.toInquisitive.access w = M.access w :=
  Finset.sup_singleton

/-! ### Syntax (Definition 3.2.1; §8.2, §8.3) -/

/-- A formula is built from atoms and `⊥` by `∧`, `→`, inquisitive disjunction `\\/` and the two
modalities. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | bot
  | conj (φ ψ : Formula Atom)
  | impl (φ ψ : Formula Atom)
  /-- Inquisitive disjunction `φ \\/ ψ`. -/
  | inqDisj (φ ψ : Formula Atom)
  /-- The Kripke modality `□φ` (§8.2). -/
  | nec (φ : Formula Atom)
  /-- The properly inquisitive modality `⊞φ` (§8.3), the entertain modality of
  [ciardelli-roelofsen-2015]. -/
  | ent (φ : Formula Atom)
  deriving Repr, DecidableEq

namespace Formula

variable (φ ψ : Formula Atom)

/-- `¬φ := φ → ⊥` (Definition 3.1.2). -/
abbrev neg : Formula Atom := impl φ bot

/-- Classical disjunction `φ ∨ ψ := ¬(¬φ ∧ ¬ψ)` (Definition 3.1.2). -/
abbrev disj : Formula Atom := (conj φ.neg ψ.neg).neg

/-- The polar question `?φ := φ \\/ ¬φ` (Definition 3.2.2). -/
abbrev polarQ : Formula Atom := inqDisj φ φ.neg

/-- The modal-free formulas are those of the propositional system InqB (Definition 3.2.1). -/
def IsModalFree : Formula Atom → Prop
  | atom _ => True
  | bot => True
  | conj φ ψ => φ.IsModalFree ∧ ψ.IsModalFree
  | impl φ ψ => φ.IsModalFree ∧ ψ.IsModalFree
  | inqDisj φ ψ => φ.IsModalFree ∧ ψ.IsModalFree
  | nec _ => False
  | ent _ => False

/-- The classical formulas, those without inquisitive disjunction (§3.1, §8.2). -/
def IsClassical : Formula Atom → Prop
  | atom _ => True
  | bot => True
  | conj φ ψ => φ.IsClassical ∧ ψ.IsClassical
  | impl φ ψ => φ.IsClassical ∧ ψ.IsClassical
  | inqDisj _ _ => False
  | nec φ => φ.IsClassical
  | ent φ => φ.IsClassical

end Formula

/-! ### Support (Definitions 3.1.3 and 3.2.3; §8.2, §8.3) -/

variable [DecidableEq W]

/-- The **support set** of `φ` in `M` is the set of information states that settle it. Support is
persistent (Proposition 3.3.1), so the support set is a lower set of states, and conjunction,
implication and inquisitive disjunction are the operations `⊓`, `⇨`, `⊔` of the Heyting algebra
of lower sets ([ciardelli-groenendijk-roelofsen-2018]); `⊥` is supported by the empty state
alone. -/
def support (M : Model W Atom) : Formula Atom → LowerSet (Finset W)
  | .atom p => ⟨Team.flat (M.val p), Team.isLowerSet_flat _⟩
  | .bot => LowerSet.Iic ∅
  | .conj φ ψ => support M φ ⊓ support M ψ
  | .impl φ ψ => support M φ ⇨ support M ψ
  | .inqDisj φ ψ => support M φ ⊔ support M ψ
  | .nec φ => ⟨Team.nec M.access (support M φ : Set (Finset W)), Team.isLowerSet_flat _⟩
  | .ent φ => ⟨Team.flat fun w ↦ ∀ t ∈ M.inq w, t ∈ support M φ, Team.isLowerSet_flat _⟩

variable (M : Model W Atom) (φ ψ : Formula Atom) (s : Finset W) (w : W)

@[simp] theorem mem_support_atom (p : Atom) :
    s ∈ support M (.atom p) ↔ ∀ w ∈ s, M.val p w := Iff.rfl

@[simp] theorem mem_support_bot : s ∈ support M (.bot : Formula Atom) ↔ s = ∅ :=
  LowerSet.mem_Iic_iff.trans Finset.subset_empty

@[simp] theorem mem_support_conj :
    s ∈ support M (.conj φ ψ) ↔ s ∈ support M φ ∧ s ∈ support M ψ := Iff.rfl

@[simp] theorem mem_support_impl :
    s ∈ support M (.impl φ ψ) ↔ ∀ t ⊆ s, t ∈ support M φ → t ∈ support M ψ :=
  LowerSet.mem_himp

@[simp] theorem mem_support_inqDisj :
    s ∈ support M (.inqDisj φ ψ) ↔ s ∈ support M φ ∨ s ∈ support M ψ := Iff.rfl

@[simp] theorem mem_support_nec :
    s ∈ support M (.nec φ) ↔ ∀ w ∈ s, M.access w ∈ support M φ := Iff.rfl

@[simp] theorem mem_support_ent :
    s ∈ support M (.ent φ) ↔ ∀ w ∈ s, ∀ t ∈ M.inq w, t ∈ support M φ := Iff.rfl

/-- Support at a finite state is decidable, by structural recursion. -/
instance decidableMemSupport [DecidableRel M.val] :
    (φ : Formula Atom) → (s : Finset W) → Decidable (s ∈ support M φ)
  | .atom p, s => decidable_of_iff _ (mem_support_atom M s p).symm
  | .bot, s => decidable_of_iff _ (mem_support_bot M s).symm
  | .conj φ ψ, s =>
    have := decidableMemSupport φ s; have := decidableMemSupport ψ s
    decidable_of_iff _ (mem_support_conj M φ ψ s).symm
  | .impl φ ψ, s =>
    have := decidableMemSupport φ; have := decidableMemSupport ψ
    decidable_of_iff _ (mem_support_impl M φ ψ s).symm
  | .inqDisj φ ψ, s =>
    have := decidableMemSupport φ s; have := decidableMemSupport ψ s
    decidable_of_iff _ (mem_support_inqDisj M φ ψ s).symm
  | .nec φ, s =>
    have := decidableMemSupport φ
    decidable_of_iff _ (mem_support_nec M φ s).symm
  | .ent φ, s =>
    have := decidableMemSupport φ
    decidable_of_iff _ (mem_support_ent M φ s).symm

/-- The support of a modal-free formula depends only on the valuation. -/
theorem support_eq_of_isModalFree {M M' : Model W Atom} (hval : M.val = M'.val) :
    ∀ {φ : Formula Atom}, φ.IsModalFree → support M φ = support M' φ
  | .atom p, _ => by simp only [support, hval]
  | .bot, _ => rfl
  | .conj φ ψ, h => by
    simp only [support, support_eq_of_isModalFree hval h.1, support_eq_of_isModalFree hval h.2]
  | .impl φ ψ, h => by
    simp only [support, support_eq_of_isModalFree hval h.1, support_eq_of_isModalFree hval h.2]
  | .inqDisj φ ψ, h => by
    simp only [support, support_eq_of_isModalFree hval h.1, support_eq_of_isModalFree hval h.2]
  | .nec _, h => h.elim
  | .ent _, h => h.elim

/-! ### The empty state (Proposition 3.3.1) -/

/-- By **the empty state property**, the inconsistent state supports every formula. -/
theorem empty_mem_support : ∅ ∈ support M φ := by
  induction φ with
  | atom p => exact Team.empty_mem_flat _
  | bot => exact (mem_support_bot M ∅).2 rfl
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | impl φ ψ _ ihψ =>
    exact (mem_support_impl M φ ψ ∅).2 fun t ht _ ↦ Finset.subset_empty.1 ht ▸ ihψ
  | inqDisj φ ψ ihφ _ => exact Or.inl ihφ
  | nec φ _ => exact Team.empty_mem_flat _
  | ent φ _ => exact Team.empty_mem_flat _

/-! ### Truth (Proposition 3.1.7) -/

/-- A state supports `¬φ` iff it rules `φ` out, no consistent substate supporting `φ`
(Proposition 3.1.6). -/
theorem mem_support_neg : s ∈ support M φ.neg ↔ ∀ t ⊆ s, t ∈ support M φ → t = ∅ := by
  simp [Formula.neg]

theorem singleton_mem_support_impl :
    {w} ∈ support M (.impl φ ψ) ↔ ({w} ∈ support M φ → {w} ∈ support M ψ) := by
  rw [mem_support_impl]
  refine ⟨fun h ↦ h _ subset_rfl, fun h t ht hφ ↦ ?_⟩
  rcases Finset.subset_singleton_iff.1 ht with rfl | rfl
  · exact empty_mem_support M ψ
  · exact h hφ

theorem singleton_mem_support_neg : {w} ∈ support M φ.neg ↔ {w} ∉ support M φ := by
  simp only [Formula.neg, singleton_mem_support_impl, mem_support_bot, Finset.singleton_ne_empty,
    imp_false]

theorem singleton_mem_support_disj :
    {w} ∈ support M (φ.disj ψ) ↔ {w} ∈ support M φ ∨ {w} ∈ support M ψ := by
  simp only [Formula.disj, singleton_mem_support_neg, mem_support_conj, not_and_or, not_not]

/-! ### Truth-conditional formulas (§3.4) -/

/-- The truth set `|φ|_M` (§3.1) is the set of worlds at which `φ` is true, truth being support
at the singleton state. -/
def truthSet : Set W := {w | {w} ∈ support M φ}

/-- `φ` is **truth-conditional** in `M` when a state supports it iff it is true at each of its
worlds: flatness (`Team.IsFlat`) of the support set. Definitions 2.6.3 and 3.4.1 call a formula
truth-conditional, a statement, when it is truth-conditional in every model. -/
def TruthConditional : Prop := Team.IsFlat (support M φ : Set (Finset W))

theorem truthConditional_atom (p : Atom) : TruthConditional M (.atom p) := Team.isFlat_flat _

theorem truthConditional_bot : TruthConditional M (.bot : Formula Atom) := fun s ↦ by
  simp [Finset.eq_empty_iff_forall_notMem]

theorem truthConditional_nec : TruthConditional M (.nec φ) := Team.isFlat_flat _

theorem truthConditional_ent : TruthConditional M (.ent φ) := Team.isFlat_flat _

variable {M φ ψ}

theorem TruthConditional.mem_support_iff (h : TruthConditional M φ) :
    s ∈ support M φ ↔ ∀ w ∈ s, {w} ∈ support M φ :=
  h s

/-- Two statements that agree at every world have the same support. -/
theorem TruthConditional.support_eq (hφ : TruthConditional M φ) (hψ : TruthConditional M ψ)
    (h : ∀ w, {w} ∈ support M φ ↔ {w} ∈ support M ψ) : support M φ = support M ψ :=
  SetLike.ext fun _ ↦ by
    rw [hφ.mem_support_iff, hψ.mem_support_iff]; exact forall₂_congr fun w _ ↦ h w

theorem TruthConditional.conj (hφ : TruthConditional M φ) (hψ : TruthConditional M ψ) :
    TruthConditional M (.conj φ ψ) := fun s ↦ by
  show s ∈ support M (.conj φ ψ) ↔ ∀ w ∈ s, {w} ∈ support M (.conj φ ψ)
  rw [mem_support_conj, hφ.mem_support_iff, hψ.mem_support_iff]
  simp only [mem_support_conj, forall₂_and]

/-- An implication with a truth-conditional consequent is truth-conditional, whatever its
antecedent (Proposition 3.4.7). -/
theorem TruthConditional.impl (hψ : TruthConditional M ψ) (φ : Formula Atom) :
    TruthConditional M (.impl φ ψ) := fun s ↦ by
  refine ⟨fun h w hw ↦ (support M _).lower (Finset.singleton_subset_iff.2 hw) h,
    fun h ↦ (mem_support_impl M φ ψ s).2 fun t hts hφ ↦ (hψ t).2 fun w hw ↦ ?_⟩
  exact (singleton_mem_support_impl M φ ψ w).1 (h w (hts hw))
    ((support M φ).lower (Finset.singleton_subset_iff.2 hw) hφ)

variable (M φ ψ)

/-- Every negation is truth-conditional (Proposition 3.4.8). -/
theorem truthConditional_neg : TruthConditional M φ.neg := (truthConditional_bot M).impl φ

theorem truthConditional_disj : TruthConditional M (φ.disj ψ) := truthConditional_neg M _

/-- Classical formulas are truth-conditional (Proposition 3.1.8). -/
theorem truthConditional_of_isClassical (h : φ.IsClassical) : TruthConditional M φ := by
  induction φ with
  | atom p => exact truthConditional_atom M p
  | bot => exact truthConditional_bot M
  | conj φ ψ ihφ ihψ => exact (ihφ h.1).conj (ihψ h.2)
  | impl φ ψ _ ihψ => exact (ihψ h.2).impl φ
  | inqDisj φ ψ _ _ => exact h.elim
  | nec φ _ => exact truthConditional_nec M φ
  | ent φ _ => exact truthConditional_ent M φ

/-- `¬¬φ` is supported exactly where `φ` is true at every world, as the classical variant of `φ`
is (Proposition 3.4.9). -/
theorem mem_support_neg_neg : s ∈ support M φ.neg.neg ↔ ∀ w ∈ s, {w} ∈ support M φ := by
  rw [(truthConditional_neg M φ.neg).mem_support_iff]
  simp only [singleton_mem_support_neg, not_not]

theorem truthSet_neg_neg : truthSet M φ.neg.neg = truthSet M φ :=
  Set.ext fun w ↦ (mem_support_neg_neg M φ {w}).trans (by simp [truthSet])

/-- The double negation law holds exactly for statements (Proposition 3.4.10). -/
theorem truthConditional_iff_support_neg_neg :
    TruthConditional M φ ↔ support M φ.neg.neg = support M φ := by
  simp only [TruthConditional, SetLike.ext_iff, mem_support_neg_neg]
  exact forall_congr' fun s ↦ Iff.comm

/-- For a statement `α`, `α → ψ` is supported at `s` iff `ψ` is supported at the `α`-worlds of `s`
(Proposition 2.5.2). -/
theorem mem_support_impl_iff_of_truthConditional [DecidableRel M.val] {α : Formula Atom}
    (hα : TruthConditional M α) :
    s ∈ support M (.impl α ψ) ↔ s.filter (fun w ↦ {w} ∈ support M α) ∈ support M ψ := by
  rw [mem_support_impl]
  refine ⟨fun h ↦ h _ (Finset.filter_subset _ _) ((hα _).2 fun _ hw ↦ (Finset.mem_filter.1 hw).2),
    fun h t hts hαt ↦ (support M ψ).lower ?_ h⟩
  exact fun w hw ↦ Finset.mem_filter.2 ⟨hts hw, (hα t).1 hαt w hw⟩

/-! ### The proposition expressed (§3.3) -/

section Proposition

variable [Fintype W]

/-- The inquisitive proposition `[φ]_M` expressed by `φ` is the support set carried along
`Finset W ≃o Set W`, as a `Question`. -/
def proposition : Question W :=
  .ofLowerSet (Fintype.finsetOrderIsoSet '' (support M φ : Set (Finset W)))
    ⟨∅, empty_mem_support M φ, Finset.coe_empty⟩ ((support M φ).lower.image _)

@[simp] theorem coe_mem_proposition : (↑s : Set W) ∈ proposition M φ ↔ s ∈ support M φ :=
  Fintype.finsetOrderIsoSet.injective.mem_set_image

/-- Conjunction is the meet of propositions. -/
theorem proposition_conj : proposition M (.conj φ ψ) = proposition M φ ⊓ proposition M ψ :=
  Question.ext <| Fintype.finsetEquivSet.symm.forall_congr_left.2 fun _ ↦ by simp

/-- Inquisitive disjunction is the join. -/
theorem proposition_inqDisj :
    proposition M (.inqDisj φ ψ) = proposition M φ ⊔ proposition M ψ :=
  Question.ext <| Fintype.finsetEquivSet.symm.forall_congr_left.2 fun _ ↦ by simp

/-- Implication is the Heyting arrow. -/
theorem proposition_impl : proposition M (.impl φ ψ) = proposition M φ ⇨ proposition M ψ :=
  Question.ext <| Fintype.finsetEquivSet.symm.forall_congr_left.2 fun _ ↦ by
    rw [Question.mem_himp, Fintype.finsetEquivSet.symm.forall_congr_left]; simp

/-- `⊥` is the bottom. -/
theorem proposition_bot : proposition M (.bot : Formula Atom) = ⊥ :=
  Question.ext <| Fintype.finsetEquivSet.symm.forall_congr_left.2 fun _ ↦ by simp

/-- The truth set is the union of the proposition (Proposition 3.3.5). -/
theorem info_proposition : (proposition M φ).info = truthSet M φ :=
  Set.ext fun w ↦ by
    rw [Question.mem_info_iff_singleton_mem, ← Finset.coe_singleton, coe_mem_proposition]; rfl

/-- `φ` is truth-conditional in `M` iff `[φ]_M` is the declarative of its truth set, generated by
the single state `|φ|_M` (Proposition 2.6.4, in one model). -/
theorem truthConditional_iff_proposition_eq :
    TruthConditional M φ ↔ proposition M φ = Question.ofSet (truthSet M φ) := by
  rw [Question.ext_iff, Fintype.finsetEquivSet.symm.forall_congr_left]
  simp [TruthConditional, Team.IsFlat, Set.subset_def, truthSet]

/-- So `φ` is truth-conditional in `M` iff the proposition it expresses is not inquisitive. -/
theorem truthConditional_iff_not_isInquisitive :
    TruthConditional M φ ↔ ¬ (proposition M φ).IsInquisitive := by
  rw [truthConditional_iff_proposition_eq, ← info_proposition,
    ← Question.info_mem_iff_eq_ofSet_info, Question.info_mem_iff_not_isInquisitive]

/-- `¬¬φ` expresses the non-inquisitive projection of `[φ]_M`, its double complement
(Proposition 3.4.9). -/
theorem proposition_neg_neg : proposition M φ.neg.neg = (proposition M φ)ᶜᶜ := by
  simp only [Formula.neg, proposition_impl, proposition_bot, himp_bot]

end Proposition

/-! ### Modalities (§8.2, §8.3) -/

/-- `□` commutes with `∧` (§8.2). -/
theorem support_nec_conj : support M (.nec (.conj φ ψ)) = support M (.conj (.nec φ) (.nec ψ)) :=
  SetLike.ext fun _ ↦ by simp [imp_and, forall_and]

/-- The K axiom for `□` (§8.2). -/
theorem support_nec_impl_nec :
    support M (.impl (.nec (.impl φ ψ)) (.impl (.nec φ) (.nec ψ))) = ⊤ :=
  top_unique fun _ _ ↦ by
    simp only [SetLike.mem_coe, mem_support_impl, mem_support_nec]
    exact fun _ _ ht _ hut hu w hw ↦ ht w (hut hw) _ subset_rfl (hu w hw)

/-- Necessitation for `□` (§8.2). -/
theorem support_nec_of_eq_top (h : support M φ = ⊤) : support M (.nec φ) = ⊤ :=
  top_unique fun _ _ _ _ ↦ h ▸ trivial

/-- `□` pseudo-commutes with inquisitive disjunction, `□(φ \\/ ψ) ≡ □φ ∨ □ψ` (§8.2). -/
theorem support_nec_inqDisj :
    support M (.nec (.inqDisj φ ψ)) = support M ((Formula.nec φ).disj (.nec ψ)) :=
  (truthConditional_nec M _).support_eq (truthConditional_disj M _ _) fun w ↦ by
    rw [singleton_mem_support_disj]; simp

/-- `⊞` commutes with `∧` (§8.3). -/
theorem support_ent_conj : support M (.ent (.conj φ ψ)) = support M (.conj (.ent φ) (.ent ψ)) :=
  SetLike.ext fun _ ↦ by simp [imp_and, forall_and]

/-- The K axiom for `⊞` (§8.3). -/
theorem support_ent_impl_ent :
    support M (.impl (.ent (.impl φ ψ)) (.impl (.ent φ) (.ent ψ))) = ⊤ :=
  top_unique fun _ _ ↦ by
    simp only [SetLike.mem_coe, mem_support_impl, mem_support_ent]
    exact fun _ _ ht _ hut hu w hw v hv ↦ ht w (hut hw) v hv _ subset_rfl (hu w hw v hv)

/-- Necessitation for `⊞` (§8.3). -/
theorem support_ent_of_eq_top (h : support M φ = ⊤) : support M (.ent φ) = ⊤ :=
  top_unique fun _ _ _ _ _ _ ↦ h ▸ trivial

/-- `□φ` entails `⊞φ`, since each related state lies in the epistemic state and support is
persistent (§8.3). -/
theorem support_nec_le_ent : support M (.nec φ) ≤ support M (.ent φ) :=
  fun _ h w hw _ ht ↦ (support M φ).lower (M.subset_access ht) (h w hw)

/-- On statements the two modalities coincide (§8.3). -/
theorem support_ent_eq_nec_of_truthConditional (h : TruthConditional M φ) :
    support M (.ent φ) = support M (.nec φ) :=
  le_antisymm (fun _ hent w hw ↦ (h _).2 fun v hv ↦ by
      obtain ⟨t, ht, hvt⟩ := M.mem_access.1 hv
      exact (h t).1 (hent w hw t ht) v hvt)
    (support_nec_le_ent M φ)

/-- On a Kripke model `⊞` is `□`, the only related state being `R[w]`. -/
theorem support_ent_toInquisitive (M : ModalLogic.KripkeModel W Atom) :
    support M.toInquisitive (.ent φ) = support M.toInquisitive (.nec φ) :=
  SetLike.ext fun _ ↦ by simp [ModalLogic.KripkeModel.toInquisitive, Model.access]

/-! ### The closure cell -/

/-- Inquisitive disjunction breaks union closure. With `p` true only at `w₁` and `q` only at
`w₂`, the singletons support `p \\/ q` but their union supports neither disjunct. -/
theorem not_supClosed_support_inqDisj {p q : Atom} {w₁ w₂ : W}
    (hp₁ : M.val p w₁) (hq₁ : ¬ M.val q w₁) (hp₂ : ¬ M.val p w₂) (hq₂ : M.val q w₂) :
    ¬ SupClosed (support M (.inqDisj (.atom p) (.atom q)) : Set (Finset W)) := fun h ↦ by
  have := h (a := {w₁}) (b := {w₂}) (by simp [hp₁]) (by simp [hq₂])
  simp [hp₂, hq₁] at this

open Team in
/-- Inquisitive modal logic is sound for the downward-closed, empty-team cell of
[anttila-2025]'s programme, which it shares with dependence logic. -/
theorem definableClass_support_subset :
    definableClass (fun φ t ↦ t ∈ support M φ) ⊆ {P | IsLowerSet P ∧ ∅ ∈ P} :=
  definableClass_subset fun φ ↦ ⟨(support M φ).lower, empty_mem_support M φ⟩

end Inquisitive
