module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Bisimulation
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Atoms
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability

/-!
# Modal dependence logic

Väänänen's modal dependence logic (MDL) extends classical modal logic with the dependence atom
`=(p₁, …, pₙ; q)`, supported by a team when the value of `q` is a function of the values of
`p₁, …, pₙ` across the team. Like BSML it evaluates formulas bilaterally against teams of worlds
of a Kripke model, and negation swaps support and anti-support. A team supports `◇φ` when one team
supporting `φ` supplies a successor to each of its worlds, and anti-supports it when the union of
the successor sets anti-supports `φ`. MDL formulas are downward closed and supported by the empty
team, but the dependence atom breaks union closure.

## Main definitions

* `Formula`: atoms, dependence atoms, `¬`, `∧`, split `∨` and `◇`.
* `eval`: bilateral evaluation, with `support` and `antiSupport`.
* `Formula.modalDepth`: the nesting depth of `◇`.
* `Formula.DepFree`, `Realize`: the fragment without dependence atoms, and classical truth.

## Main results

* `isLowerSet_support`, `support_empty`: support is downward closed and contains `∅`.
* `not_supClosed_dep_of_witness`: the dependence atom is not union-closed.
* `support_iff_forall_realize`: without dependence atoms, support is pointwise classical truth.
* `invariant_eval`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.

## Implementation notes

`eval` is a fold over the operations of `Team/Operations.lean` and the dependence atom
`Team.dep`, with Väänänen's single-witness and image modalities. The disjunction clause is the
split `t₁ ∪ t₂ = t`, which is equivalent to Väänänen's `t ⊆ t₁ ∪ t₂` under downward closure.

## TODO

* The classical disjunction and the satisfiability complexity results of
  [lohmann-vollmer-2013].
* Modal independence logic, with the independence atom beside `Team.dep`.

## References

* [vaananen-2007] Väänänen, Dependence Logic: A New Approach to Independence Friendly Logic
* [vaananen-2008] Väänänen, Modal Dependence Logic
* [lohmann-vollmer-2013] Lohmann and Vollmer, Complexity Results for Modal Dependence Logic
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
-/

@[expose] public section

namespace ModalLogic.Dependence

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)

/-! ### Syntax (Definition 1.1) -/

/-- The formulas of MDL ([vaananen-2008] Definition 1.1, p. 238) extend classical modal logic
    with the dependence atom `=(p₁,...,pₙ; q)`. Väänänen defines `□A` as `¬◇¬A` and `A ∧ B` as
    `¬(¬A ∨ ¬B)`; `conj` is primitive here, with the clauses that abbreviation yields. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- The dependence atom `=(x⃗; y)` says that the values of `y` in the team are a function
      of the values of `x⃗`. -/
  | dep (xs : List Atom) (y : Atom)
  /-- Negation, which swaps support and anti-support. -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction (team-split form under downward closure). -/
  | disj (φ ψ : Formula Atom)
  /-- Possibility modal `◇`. -/
  | poss (φ : Formula Atom)
  deriving Repr

/-! ### Classical truth

Without dependence atoms MDL is classical modal logic ([anttila-2021]'s Proposition 2.2.16
for Väänänen's modalities, `support_iff_forall_realize` below). -/

/-- `Formula.DepFree φ` holds when `φ` contains no dependence atom. -/
def Formula.DepFree : Formula Atom → Prop
  | .atom _ => True
  | .dep _ _ => False
  | .neg φ | .poss φ => φ.DepFree
  | .conj φ ψ | .disj φ ψ => φ.DepFree ∧ ψ.DepFree

open scoped ModalLogic in
/-- Classical Kripke truth of an MDL formula at a world, with `◇` the shared
    `ModalLogic.Diamond`; a dependence atom is true at every world. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w
  | .dep _ _, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.accessible] (Realize M ψ) w

theorem realize_poss {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

variable [DecidableEq W]

/-! ### Semantics (Definition 4.1) -/

/-- Bilateral evaluation for MDL (Definition 4.1 of [vaananen-2008], p. 245).
    `eval M true φ t` is support (Player II); `eval M false φ t` is
    anti-support (Player I). Negation flips polarity (clause (T5)).

    The ◇ clauses (T8), (T9) use Väänänen's single-witness form, not
    BSML's per-world form; the two formulations diverge for non-union-
    closed logics like MDL. -/
def eval (M : KripkeModel W Atom) : Bool → Formula Atom → Finset W → Prop
  | true,  .atom p,        t => t ∈ Team.flat (M.val p)
  | false, .atom p,        t => t ∈ Team.flat fun w ↦ ¬ M.val p w
  | true,  .dep xs y,      t => (t : Set W) ∈ Team.dep (fun w ↦ xs.map (M.val · w)) (M.val y)
  | false, .dep _ _,       t => t ∈ ({∅} : Team.TeamProperty W)
  | true,  .neg ψ,         t => eval M false ψ t
  | false, .neg ψ,         t => eval M true ψ t
  | true,  .conj ψ₁ ψ₂,    t => eval M true ψ₁ t ∧ eval M true ψ₂ t
  | false, .conj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M false ψ₁ s} {s | eval M false ψ₂ s}
  | true,  .disj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M true ψ₁ s} {s | eval M true ψ₂ s}
  | false, .disj ψ₁ ψ₂,    t => eval M false ψ₁ t ∧ eval M false ψ₂ t
  | true,  .poss ψ,        t => t ∈ Team.possWitness M.access {s | eval M true ψ s}
  | false, .poss ψ,        t => t ∈ Team.necImage M.access {s | eval M false ψ s}

/-- Support is evaluation in the positive polarity. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M true φ t

/-- Anti-support is evaluation in the negative polarity. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M false φ t

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w := Iff.rfl

@[simp] lemma antiSupport_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    antiSupport M (.atom p) t ↔ ∀ w ∈ t, ¬ M.val p w := Iff.rfl

@[simp] lemma support_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    support M (.dep xs y) t ↔
      ∀ w₁ ∈ t, ∀ w₂ ∈ t,
        (∀ x ∈ xs, M.val x w₁ ↔ M.val x w₂) → (M.val y w₁ ↔ M.val y w₂) := by
  simp only [support, eval, Team.mem_dep, Finset.mem_coe, List.map_inj_left, eq_iff_iff]

@[simp] lemma antiSupport_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    antiSupport M (.dep xs y) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ antiSupport M φ t := Iff.rfl

@[simp] lemma antiSupport_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.neg φ) t ↔ support M φ t := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma antiSupport_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.conj φ ψ) t ↔
      ∃ t₁, antiSupport M φ t₁ ∧ ∃ t₂, antiSupport M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁, support M φ t₁ ∧ ∃ t₂, support M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma antiSupport_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    antiSupport M (.disj φ ψ) t ↔ antiSupport M φ t ∧ antiSupport M ψ t := Iff.rfl

@[simp] lemma support_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.poss φ) t ↔
      ∃ Y : Finset W, (∀ w ∈ t, ∃ y ∈ Y, y ∈ M.access w) ∧ support M φ Y :=
  Iff.rfl

@[simp] lemma antiSupport_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    antiSupport M (.poss φ) t ↔ antiSupport M φ (t.biUnion M.access) := Iff.rfl

/-! ### Modal depth -/

/-- The modal depth of a formula is the greatest number of nested `◇`s in it. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .dep _ _ => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Lemma 4.2: Downward closure -/

/-- Support and anti-support are downward closed together. Each case is the closure lemma of
    its connective in `Team/Operations.lean`, and subteams inherit the dependence atom. -/
private theorem support_and_antiSupport_isLowerSet (φ : Formula Atom)
    (M : KripkeModel W Atom) :
    IsLowerSet {t | support M φ t} ∧ IsLowerSet {t | antiSupport M φ t} := by
  induction φ with
  | atom p => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩
  | dep xs y =>
    exact ⟨(Team.isLowerSet_dep _ _).preimage fun _ _ ↦ Finset.coe_subset.2,
      Team.isLowerSet_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.tensor ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.tensor ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss ψ ih => exact ⟨Team.isLowerSet_possWitness _ _, ih.2.necImage⟩

/-- The support of every MDL formula is downward closed ([vaananen-2008] Lemma 4.2, p. 245). -/
theorem isLowerSet_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (support_and_antiSupport_isLowerSet φ M).1

/-! ### Empty team property -/

/-- Every MDL formula is supported and anti-supported by the empty team. -/
private theorem support_and_antiSupport_empty
    (φ : Formula Atom) (M : KripkeModel W Atom) :
    support M φ ∅ ∧ antiSupport M φ ∅ := by
  induction φ with
  | atom p => exact ⟨Team.empty_mem_flat _, Team.empty_mem_flat _⟩
  | dep xs y =>
    refine ⟨?_, rfl⟩
    simp only [support, eval, Finset.coe_empty]
    exact Team.empty_mem_dep
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, Team.empty_mem_tensor ih₁.2 ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Team.empty_mem_tensor ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss ψ ih => exact ⟨Team.empty_mem_possWitness ih.1, Team.empty_mem_necImage ih.2⟩

/-- Every MDL formula is supported on the empty team. -/
theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ :=
  (support_and_antiSupport_empty φ M).1

/-! ### Dep breaks union closure (the defining feature) -/

/-- The dependence atom is not union-closed. When two worlds agree on `p` but not on `q`,
    each of their singleton teams supports `=(p; q)` but the team of both does not. -/
theorem not_supClosed_dep_of_witness {p q : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom} (hp : M.val p w₁ ↔ M.val p w₂) (hq : ¬ (M.val q w₁ ↔ M.val q w₂)) :
    ¬ SupClosed { t : Finset W | support M (.dep [p] q) t } := fun h ↦ by
  have hs (w : W) : support M (.dep [p] q) {w} := by
    simp only [support, eval, Finset.coe_singleton]
    exact Team.singleton_mem_dep w
  exact hq <| (support_dep M [p] q _).1 (h (hs w₁) (hs w₂)) w₁ (by simp) w₂ (by simp)
    (by simpa using hp)

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team in
/-- Every MDL-definable team property is downward closed and contains the empty team. The
    converse, that every such property is MDL-definable, is not proved here. -/
theorem definableClass_support_subset (M : KripkeModel W Atom) :
    definableClass (support M) ⊆ {P | IsLowerSet P ∧ ∅ ∈ P} :=
  definableClass_subset fun φ ↦ ⟨isLowerSet_support M φ, support_empty M φ⟩

/-! ### Bisimulation invariance -/

section Bisimulation

open ModalLogic (WorldBisim)

variable {W' : Type*} [DecidableEq W'] {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}

/-- Teams that are `k`-bisimilar agree on every MDL formula of modal depth at most `k`, in both
    polarities, by the argument of [aloni-anttila-yang-2024] Theorem 3.8. -/
theorem invariant_eval {k : ℕ} (φ : Formula Atom) (hd : φ.modalDepth ≤ k) (b : Bool) :
    Team.Invariant (WorldBisim k M · M' ·) {t | eval M b φ t} {t | eval M' b φ t} := by
  induction φ generalizing k b with
  | atom p =>
    cases b
    · exact Team.invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)
    · exact Team.invariant_flat fun _ _ h ↦ h.val_iff p
  | dep xs y =>
    cases b
    · exact Team.invariant_singleton_empty
    · exact Team.invariant_dep (fun _ _ h ↦ List.map_congr_left fun x _ ↦ propext (h.val_iff x))
        fun _ _ h ↦ propext (h.val_iff y)
  | neg ψ ih => cases b <;> exact ih hd _
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).tensor (ih₂ hd₂ _), (ih₁ hd₁ _).inter (ih₂ hd₂ _)]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    cases b; exacts [(ih₁ hd₁ _).inter (ih₂ hd₂ _), (ih₁ hd₁ _).tensor (ih₂ hd₂ _)]
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    cases b
    · exact (ih _).necImage fun _ _ h ↦ h.2
    · exact (ih _).possWitness (fun _ _ h ↦ h.2) (isLowerSet_support M ψ)
        (isLowerSet_support M' ψ)

end Bisimulation

/-! ### The classical fragment

On `dep`-free formulas support is pointwise classical truth and anti-support pointwise
classical falsity: Väänänen's single-witness and image modalities agree with the flat ones
on flat properties (`Team.possWitness_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- On `dep`-free formulas, support is pointwise classical truth and anti-support pointwise
    classical falsity. -/
theorem eval_iff_forall_realize (hD : φ.DepFree) (b : Bool) (t : Finset W) :
    eval M b φ t ↔ ∀ w ∈ t, (Realize M φ w ↔ b) := by
  induction φ generalizing b t with
  | atom p => cases b <;> simp [eval, Realize]
  | dep xs y => exact hD.elim
  | neg ψ ih =>
    cases b
    · simpa [eval, Realize] using ih hD true t
    · simpa [eval, Realize] using ih hD false t
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp only [eval, ih₁ hD.1, ih₂ hD.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize, imp_iff_not_or]
    · simp [eval, ih₁ hD.1, ih₂ hD.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    cases b
    · simp [eval, ih₁ hD.1, ih₂ hD.2, Realize, forall_and, not_or]
    · simp only [eval, ih₁ hD.1, ih₂ hD.2]
      refine Team.mem_tensor_flat.trans ?_
      simp [Realize]
  | poss ψ ih =>
    cases b
    · simp only [eval, ih hD false]
      refine Team.mem_necImage_flat.trans ?_
      simp [realize_poss]
    · simp only [eval, ih hD true]
      refine Team.mem_possWitness_flat.trans ?_
      simp [realize_poss]

theorem support_iff_forall_realize (hD : φ.DepFree) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  simpa using eval_iff_forall_realize hD true t

theorem antiSupport_iff_forall_not_realize (hD : φ.DepFree) :
    antiSupport M φ t ↔ ∀ w ∈ t, ¬ Realize M φ w := by
  simpa using eval_iff_forall_realize hD false t

theorem support_singleton_iff_realize (hD : φ.DepFree) : support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hD]

end Classical

end ModalLogic.Dependence
