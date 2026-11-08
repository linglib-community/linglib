module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Bisimulation
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Atoms
public import Linglib.Logic.Team.Closure

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
* `Formula.den`: the pair of supporting and anti-supporting teams, with `support` and
  `antiSupport`.
* `Formula.modalDepth`: the nesting depth of `◇`.
* `Formula.DepFree`, `Realize`: the fragment without dependence atoms, and classical truth.

## Main results

* `isLowerSet_support`, `support_empty`: support is downward closed and contains `∅`.
* `not_supClosed_dep_of_witness`: the dependence atom is not union-closed.
* `den_of_depFree`: without dependence atoms, a formula means the flat pair of its classical
  truth.
* `invariant_den`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.
* `range_support_subset`: the classes of pointed team models MDL expresses are downward closed,
  contain the empty team and are invariant under bounded bisimulation.

## Implementation notes

`Formula.den` is a fold over the bilateral connectives of `Team/Operations.lean` and the
dependence atom `Team.dep`, with Väänänen's single-witness and image modalities. The disjunction
clause is the split `t₁ ∪ t₂ = t`, which is equivalent to Väänänen's `t ⊆ t₁ ∪ t₂` under downward
closure.

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

open scoped SetFamily

namespace ModalLogic.Dependence

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)
open Team (TeamProperty)
open scoped Bilattice

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

/-- The meaning of an MDL formula in a model is the pair of the teams that support it and the
teams that anti-support it ([vaananen-2008] Definition 4.1, p. 245). Negation swaps the two
(clause (T5)). The `◇` clauses (T8) and (T9) are Väänänen's single-witness and image modalities,
which diverge from BSML's per-world ones on properties that are not union-closed. -/
def Formula.den (M : KripkeModel W Atom) : Formula Atom → TeamProperty W ⊙ TeamProperty W
  | .atom p => Team.flatPair (M.val p)
  | .dep xs y => .mk ((↑) ⁻¹' Team.dep (fun w ↦ xs.map (M.val · w)) (M.val y)) {∅}
  | .neg ψ => (ψ.den M)ᶜ
  | .conj ψ₁ ψ₂ => Team.conj (ψ₁.den M) (ψ₂.den M)
  | .disj ψ₁ ψ₂ => Team.disj (ψ₁.den M) (ψ₂.den M)
  | .poss ψ => (ψ.den M).map (Team.possWitness M.access) (Team.necImage M.access)

/-- A team supports `φ` when it is in the support coordinate of the meaning of `φ`. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).pro

/-- A team anti-supports `φ` when it is in the anti-support coordinate of the meaning of `φ`. -/
abbrev antiSupport (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  t ∈ (φ.den M).con

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w := Iff.rfl

@[simp] lemma antiSupport_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    antiSupport M (.atom p) t ↔ ∀ w ∈ t, ¬ M.val p w := Iff.rfl

@[simp] lemma support_dep (M : KripkeModel W Atom) (xs : List Atom) (y : Atom)
    (t : Finset W) :
    support M (.dep xs y) t ↔
      ∀ w₁ ∈ t, ∀ w₂ ∈ t,
        (∀ x ∈ xs, M.val x w₁ ↔ M.val x w₂) → (M.val y w₁ ↔ M.val y w₂) := by
  simp only [support, Formula.den, Bilattice.Product.pro_mk, Set.mem_preimage, Team.mem_dep,
    Finset.mem_coe, List.map_inj_left, eq_iff_iff]

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

/-- Support and anti-support are downward closed. -/
theorem isLowerSet_den (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet (φ.den M).pro ∧ IsLowerSet (φ.den M).con := by
  induction φ with
  | atom p => exact ⟨Team.isLowerSet_flat _, Team.isLowerSet_flat _⟩
  | dep xs y =>
    exact ⟨(Team.isLowerSet_dep _ _).preimage fun _ _ ↦ Finset.coe_subset.2,
      Team.isLowerSet_singleton_empty⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.inter ih₂.1, ih₁.2.sups ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁.1.sups ih₂.1, ih₁.2.inter ih₂.2⟩
  | poss ψ ih => exact ⟨Team.isLowerSet_possWitness _ _, ih.2.necImage⟩

/-- The support of every MDL formula is downward closed ([vaananen-2008] Lemma 4.2, p. 245). -/
theorem isLowerSet_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    IsLowerSet { t : Finset W | support M φ t } :=
  (isLowerSet_den M φ).1

/-! ### Empty team property -/

/-- The empty team supports and anti-supports every formula. -/
theorem empty_mem_den (M : KripkeModel W Atom) (φ : Formula Atom) :
    ∅ ∈ (φ.den M).pro ∧ ∅ ∈ (φ.den M).con := by
  induction φ with
  | atom p => exact ⟨Team.empty_mem_flat _, Team.empty_mem_flat _⟩
  | dep xs y => exact ⟨by simp, rfl⟩
  | neg ψ ih => exact ih.symm
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨⟨ih₁.1, ih₂.1⟩, Set.bot_mem_sups ih₁.2 ih₂.2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨Set.bot_mem_sups ih₁.1 ih₂.1, ⟨ih₁.2, ih₂.2⟩⟩
  | poss ψ ih => exact ⟨Team.empty_mem_possWitness ih.1, Team.empty_mem_necImage ih.2⟩

/-- Every MDL formula is supported on the empty team. -/
theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ :=
  (empty_mem_den M φ).1

/-! ### Dep breaks union closure (the defining feature) -/

/-- The dependence atom is not union-closed. When two worlds agree on `p` but not on `q`,
each of their singleton teams supports `=(p; q)` but the team of both does not. -/
theorem not_supClosed_dep_of_witness {p q : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom} (hp : M.val p w₁ ↔ M.val p w₂) (hq : ¬ (M.val q w₁ ↔ M.val q w₂)) :
    ¬ SupClosed { t : Finset W | support M (.dep [p] q) t } := fun h ↦ by
  have hs (w : W) : support M (.dep [p] q) {w} := by
    simp only [support, Formula.den, Bilattice.Product.pro_mk, Set.mem_preimage,
      Finset.coe_singleton]
    exact Team.singleton_mem_dep w
  exact hq <| (support_dep M [p] q _).1 (h (hs w₁) (hs w₂)) w₁ (by simp) w₂ (by simp)
    (by simpa using hp)

/-! ### Bisimulation invariance -/

section Bisimulation

open ModalLogic (WorldBisim)

variable {W' : Type*} [DecidableEq W'] {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}

/-- Teams that are `k`-bisimilar agree on every MDL formula of modal depth at most `k`, in both
polarities, by the argument of [aloni-anttila-yang-2024] Theorem 3.8. -/
theorem invariant_den {k : ℕ} (φ : Formula Atom) (hd : φ.modalDepth ≤ k) :
    Team.Invariant (WorldBisim k M · M' ·) (φ.den M).pro (φ.den M').pro ∧
      Team.Invariant (WorldBisim k M · M' ·) (φ.den M).con (φ.den M').con := by
  induction φ generalizing k with
  | atom p => exact ⟨Team.invariant_flat fun _ _ h ↦ h.val_iff p,
      Team.invariant_flat fun _ _ h ↦ not_congr (h.val_iff p)⟩
  | dep xs y =>
    exact ⟨Team.invariant_dep (fun _ _ h ↦ List.map_congr_left fun x _ ↦ propext (h.val_iff x))
      fun _ _ h ↦ propext (h.val_iff y), Team.invariant_singleton_empty⟩
  | neg ψ ih => exact (ih hd).symm
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.inter (ih₂ hd₂).1, (ih₁ hd₁).2.sups (ih₂ hd₂).2⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact ⟨(ih₁ hd₁).1.sups (ih₂ hd₂).1, (ih₁ hd₁).2.inter (ih₂ hd₂).2⟩
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    have ih := ih (Nat.le_of_succ_le_succ hd)
    exact ⟨ih.1.possWitness (fun _ _ h ↦ h.2) (isLowerSet_support M ψ) (isLowerSet_support M' ψ),
      ih.2.necImage fun _ _ h ↦ h.2⟩

end Bisimulation

/-! ### Expressive power -/

section ExpressivePower

universe u

/-- The class a formula expresses is invariant under bounded bisimulation, at the formula's modal
depth. -/
theorem boundedBisimInvariant_support (φ : Formula Atom) :
    BoundedBisimInvariant {p : PointedTeam.{u} Atom | support p.model φ p.team} :=
  ⟨φ.modalDepth, fun _ hp _ hb ↦ ((invariant_den φ le_rfl).1 hb).1 hp⟩

/-- MDL expresses only classes of pointed team models that are downward closed, contain the empty
team and are invariant under bounded bisimulation. -/
theorem range_support_subset :
    (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) ⊆
      {P | Fiberwise (fun T ↦ IsLowerSet T ∧ ∅ ∈ T) P ∧ BoundedBisimInvariant P} :=
  Set.range_subset_iff.2 fun φ ↦ ⟨fun M ↦ ⟨isLowerSet_support M φ, support_empty M φ⟩,
    boundedBisimInvariant_support φ⟩

end ExpressivePower

/-! ### The classical fragment

On `dep`-free formulas support is pointwise classical truth and anti-support pointwise
classical falsity: Väänänen's single-witness and image modalities agree with the flat ones
on flat properties (`Team.possWitness_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- The meaning of a `dep`-free formula is the flat pair of its classical truth. Each case is the
commutation of a connective with `Team.flatPair`. -/
theorem den_of_depFree (hD : φ.DepFree) : φ.den M = Team.flatPair (Realize M φ) := by
  induction φ with
  | atom p => rfl
  | dep xs y => exact hD.elim
  | neg ψ ih => exact (congrArg (·ᶜ) (ih hD)).trans (Team.compl_flatPair _)
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact (congrArg₂ Team.conj (ih₁ hD.1) (ih₂ hD.2)).trans (Team.conj_flatPair _ _)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact (congrArg₂ Team.disj (ih₁ hD.1) (ih₂ hD.2)).trans (Team.disj_flatPair _ _)
  | poss ψ ih =>
    exact (congrArg (·.map (Team.possWitness M.access) (Team.necImage M.access)) (ih hD)).trans
      (Team.map_possWitness_necImage_flatPair _ _)

theorem support_iff_forall_realize (hD : φ.DepFree) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w :=
  .of_eq (congrArg (t ∈ ·.pro) (den_of_depFree hD))

theorem antiSupport_iff_forall_not_realize (hD : φ.DepFree) :
    antiSupport M φ t ↔ ∀ w ∈ t, ¬ Realize M φ w :=
  .of_eq (congrArg (t ∈ ·.con) (den_of_depFree hD))

theorem support_singleton_iff_realize (hD : φ.DepFree) : support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hD]

end Classical

end ModalLogic.Dependence
