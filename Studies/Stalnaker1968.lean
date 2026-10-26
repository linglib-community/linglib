module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Stalnaker (1968): A Theory of Conditionals

Stalnaker evaluates *if A, B* at the world a selection function picks for `A`: a world where `A`
holds, the base world when `A` holds there, and an absurd world, where every sentence holds, when
no possible world verifies `A`. This file takes as primitive the conditional of the closest
accessible antecedent-worlds (`Conditional.orderingImp`) and reads the absurd world as an empty
domain. Under Stalnaker's assumption, that each world's similarity ordering is linear and
well-founded, the closest accessible antecedent-world satisfies the paper's four conditions on a
selection function (`IsSelectionFunction`), and conditions (3) and (4) in turn make the priority a
selection establishes a total ordering of the selected worlds. The logic C2 adds the corner `>` to
classical propositional logic and defines necessity as `¬A > A`.

## Main statements

* `isSelectionFunction_minimals`: under Stalnaker's assumption the closest accessible
  antecedent-world is a selection function.
* `IsSelectionFunction.isLinearOrder_prior`, `IsSelectionFunction.prior_iff_mem_pair`: priority
  totally orders the selected worlds, and is the order that choices from pairs reveal.
* `Provable.sound`: every theorem of C2 is valid.
* `provable_neg_corner`: a denied conditional is the conditional of the opposite consequent.
* `not_valid_trans`, `not_valid_strengthening`, `not_valid_contraposition`: the three inferences
  the corner does not support.

## Errata

Footnote 7 makes the modal logic of C2 S4 when relative possibility is transitive and S5 when it
is also symmetric. As Mandelkern observes, condition (2) lets a selection function reach worlds
not possible relative to the base world, and defined necessity is necessity over the worlds
selected (`IsSelectionFunction.mem_ofDomain_compl_iff`). With relative possibility the identity,
`□A ⊃ □□A` fails (`exists_not_box_imp_box_box`). Under Stalnaker's assumption the selected worlds
are the possible ones and footnote 7 holds (`box_imp_box_box_minimals`).

## TODO

The completeness of C2, proved by Stalnaker and Thomason.

## References

* [stalnaker-1968]
* [stalnaker-thomason-1970]
* [mandelkern-2018]
-/

@[expose] public section

namespace Stalnaker1968

open Conditional

universe u

variable {W : Type*} {R : W → Set W} {D : W → Set W → Set W} {w v : W} {p : Set W}

/-! ### Selection functions -/

/-- A selection function for a model structure with relative possibility `R` (§II), its value for
an antecedent at a base world read as a domain: the selected world, or no world when the absurd
world is selected. -/
structure IsSelectionFunction (R : W → Set W) (D : W → Set W → Set W) : Prop where
  /-- Every world is possible relative to itself. -/
  refl : ∀ w, w ∈ R w
  /-- At most one world is selected. -/
  subsingleton : ∀ w A, (D w A).Subsingleton
  /-- Condition (1): the antecedent holds at the selected world. -/
  subset : ∀ w A, D w A ⊆ A
  /-- Condition (2): the absurd world is selected only when no world possible relative to the
  base world verifies the antecedent. -/
  absurdity : ∀ w A, D w A = ∅ → R w ∩ A = ∅
  /-- Condition (3): an antecedent true at the base world selects the base world. -/
  centering : ∀ w A, w ∈ A → D w A = {w}
  /-- Condition (4): antecedents each true at the world selected for the other select the same
  world. -/
  cso : ∀ w A B, D w B ⊆ A → D w A ⊆ B → D w A = D w B

/-- Under Stalnaker's assumption, a centered similarity ordering that is linear and well-founded,
the closest accessible antecedent-world is a selection function. -/
theorem isSelectionFunction_minimals {ord : W → Preorder W} (hR : ∀ w, w ∈ R w)
    (hc : IsCentered ord) (htot : ∀ w, Std.Total (ord w).le)
    (hanti : ∀ w, Std.Antisymm (ord w).le) (hwf : ∀ w, WellFounded (ord w).lt) :
    IsSelectionFunction R fun w A ↦ (ord w).minimals (R w ∩ A) where
  refl := hR
  subsingleton w _ := Preorder.minimals_subsingleton (htot w) (hanti w)
  subset w _ := ((ord w).minimals_subset _).trans Set.inter_subset_right
  absurdity w _ h := Set.not_nonempty_iff_eq_empty.1 fun hA ↦
    ((Preorder.minimals_nonempty_iff (hwf w)).2 hA).ne_empty h
  centering w _ h := hc.minimals_eq_singleton ⟨hR w, h⟩
  cso w _ _ h₁ h₂ := Preorder.minimals_eq_of_subset_of_subset (hwf w) (htot w)
    (Set.subset_inter (((ord w).minimals_subset _).trans Set.inter_subset_left) h₂)
    (Set.subset_inter (((ord w).minimals_subset _).trans Set.inter_subset_left) h₁)

theorem isSelectionFunction_domain {s : SelectionFunction W} (hs : s.IsCSO) :
    IsSelectionFunction (fun _ ↦ Set.univ) s.domain := by
  have h := isSelectionFunction_minimals (R := fun _ ↦ Set.univ) (fun _ ↦ trivial) hs.isCentered
    (fun w ↦ ⟨@le_total W (hs.linearOrder w)⟩)
    (fun w ↦ ⟨@le_antisymm W (hs.linearOrder w).toPartialOrder⟩) hs.wellFounded
  have hD : (fun w A ↦ (hs.linearOrder w).toPreorder.minimals (Set.univ ∩ A)) = s.domain := by
    funext w A
    rw [Set.univ_inter, hs.minimals_eq_domain]
  exact hD ▸ h

/-! ### Priority

A selection establishes an ordering of the worlds it selects (fn. 8): selecting `v` for an
antecedent makes `v` prior to every world of the antecedent. When each domain is a set of
antecedent-worlds with at most one member, condition (4) says that priority is antisymmetric, and
priority is then a total ordering of the selected worlds. -/

section Priority

variable {A : Set W} {u x : W}

/-- `v` is prior to `u` at `w` when some antecedent true at `u` has the domain `{v}`. -/
def Prior (D : W → Set W → Set W) (w v u : W) : Prop := ∃ A, D w A = {v} ∧ u ∈ A

theorem Prior.of_mem (hD : (D w A).Subsingleton) (hv : v ∈ D w A) (hu : u ∈ A) :
    Prior D w v u :=
  ⟨A, hD.eq_singleton_of_mem hv, hu⟩

section CSO

variable (hcso : ∀ A B, D w B ⊆ A → D w A ⊆ B → D w A = D w B)
include hcso

theorem Prior.antisymm (h : Prior D w v u) (h' : Prior D w u v) : v = u := by
  obtain ⟨A, hA, huA⟩ := h
  obtain ⟨B, hB, hvB⟩ := h'
  have := hcso A B (by simpa [hB] using huA) (by simpa [hA] using hvB)
  rwa [hA, hB, Set.singleton_eq_singleton_iff] at this

theorem Prior.nonempty (h : Prior D w v u) (hv : v ∈ A) : (D w A).Nonempty := by
  obtain ⟨B, hB, -⟩ := h
  refine Set.nonempty_iff_ne_empty.2 fun hA ↦ ?_
  have := hcso A B (by simpa [hB] using hv) (by simp [hA])
  simp [hA, hB] at this

variable (hss : ∀ A, (D w A).Subsingleton) (hsub : ∀ A, D w A ⊆ A)
include hss hsub

theorem Prior.trans (h : Prior D w v u) (h' : Prior D w u x) : Prior D w v x := by
  obtain ⟨y, hy⟩ := h.nonempty hcso (A := {v, u, x}) (by simp)
  have hle : ∀ z ∈ ({v, u, x} : Set W), Prior D w y z := fun _ hz ↦ .of_mem (hss _) hy hz
  rcases hsub _ hy with rfl | rfl | rfl
  · exact hle x (by simp)
  · exact (Prior.antisymm hcso h (hle v (by simp))) ▸ h'
  · exact (Prior.antisymm hcso h' (hle u (by simp))) ▸ h

theorem Prior.total (hv : Prior D w v v) : Prior D w v u ∨ Prior D w u v := by
  obtain ⟨y, hy⟩ := hv.nonempty hcso (A := {v, u}) (by simp)
  rcases hsub _ hy with rfl | rfl
  exacts [.inl (.of_mem (hss _) hy (by simp)), .inr (.of_mem (hss _) hy (by simp))]

end CSO

end Priority

namespace IsSelectionFunction

variable (hM : IsSelectionFunction R D)
include hM

/-- Conditions (3) and (4) make priority a total ordering of the selected worlds (§II). -/
theorem isLinearOrder_prior (w : W) : IsLinearOrder {v // Prior D w v v} (Prior D w · ·) where
  refl v := v.2
  trans _ _ _ := Prior.trans (hM.cso w) (hM.subsingleton w) (hM.subset w)
  antisymm _ _ h h' := Subtype.ext (Prior.antisymm (hM.cso w) h h')
  total v _ := Prior.total (hM.cso w) (hM.subsingleton w) (hM.subset w) v.2

/-- Priority is the order that choices from pairs reveal: `v` is prior to `u` exactly when `v` is
the world selected from `{v, u}`, the ordering of `SelectionFunction.IsCSO.linearOrder`. -/
theorem prior_iff_mem_pair {u : W} : Prior D w v u ↔ v ∈ D w {v, u} := by
  refine ⟨fun ⟨A, hA, huA⟩ ↦ ?_, fun h ↦ .of_mem (hM.subsingleton w _) h (by simp)⟩
  have hvA : v ∈ A := hM.subset w A (by rw [hA]; rfl)
  rw [hM.cso w {v, u} A (by rw [hA]; simp) ((hM.subset w _).trans (Set.pair_subset hvA huA)), hA]
  rfl

/-- Condition (3) puts the base world first in priority. -/
theorem prior_base (w u : W) : Prior D w w u :=
  ⟨{w, u}, hM.centering w _ (by simp), by simp⟩

theorem prior_self_of_mem (hv : v ∈ R w) : Prior D w v v := by
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 fun h ↦
    Set.eq_empty_iff_forall_notMem.1 (hM.absurdity w {v} h) v ⟨hv, rfl⟩
  obtain rfl := Set.mem_singleton_iff.1 (hM.subset w {v} hy)
  exact .of_mem (hM.subsingleton w _) hy rfl

/-- Defined necessity, `¬A > A`, is necessity over the selected worlds. -/
theorem mem_ofDomain_compl_iff : w ∈ ofDomain D pᶜ p ↔ ∀ v, Prior D w v v → v ∈ p := by
  refine ⟨fun h v hv ↦ by_contra fun hvp ↦ ?_, fun h y hy ↦
    h y (.of_mem (hM.subsingleton w _) hy (hM.subset w _ hy))⟩
  obtain ⟨y, hy⟩ := Prior.nonempty (hM.cso w) (A := pᶜ) hv hvp
  exact hM.subset w _ hy (h hy)

end IsSelectionFunction

/-! ### The formal system C2 -/

/-- The formulas of C2, built from propositional letters by negation, material implication and the
corner. -/
inductive Formula (α : Type*) where
  | atom (a : α)
  | neg (A : Formula α)
  | imp (A B : Formula α)
  | corner (A B : Formula α)

namespace Formula

variable {α : Type*} {V : α → Set W}

/-- Disjunction, `A ∨ B = ¬A ⊃ B`. -/
def or (A B : Formula α) : Formula α := imp (neg A) B

/-- Conjunction, `A & B = ¬(A ⊃ ¬B)`. -/
def and (A B : Formula α) : Formula α := neg (imp A (neg B))

/-- Material equivalence. -/
def iff (A B : Formula α) : Formula α := and (imp A B) (imp B A)

/-- Necessity, `□A = ¬A > A`. -/
def box (A : Formula α) : Formula α := corner (neg A) A

/-- Possibility, `◇A = ¬(A > ¬A)`. -/
def dia (A : Formula α) : Formula α := neg (corner A (neg A))

/-- The biconditional, `(A > B) & (B > A)`. -/
def bicond (A B : Formula α) : Formula α := and (corner A B) (corner B A)

/-- The proposition a formula expresses, given the domains of the corner and a valuation of the
letters. -/
def eval (D : W → Set W → Set W) (V : α → Set W) : Formula α → Set W
  | atom a => V a
  | neg A => (A.eval D V)ᶜ
  | imp A B => materialImp (A.eval D V) (B.eval D V)
  | corner A B => ofDomain D (A.eval D V) (B.eval D V)

@[simp] theorem eval_atom {a : α} : (atom a).eval D V = V a := rfl

@[simp] theorem eval_neg {A : Formula α} : A.neg.eval D V = (A.eval D V)ᶜ := rfl

theorem mem_eval_neg {A : Formula α} : w ∈ A.neg.eval D V ↔ w ∉ A.eval D V := Iff.rfl

@[simp] theorem mem_eval_imp {A B : Formula α} :
    w ∈ (A.imp B).eval D V ↔ (w ∈ A.eval D V → w ∈ B.eval D V) := Iff.rfl

@[simp] theorem mem_eval_corner {A B : Formula α} :
    w ∈ (A.corner B).eval D V ↔ D w (A.eval D V) ⊆ B.eval D V := Iff.rfl

@[simp] theorem mem_eval_and {A B : Formula α} :
    w ∈ (A.and B).eval D V ↔ w ∈ A.eval D V ∧ w ∈ B.eval D V := by
  simp [and, eval]

@[simp] theorem eval_and {A B : Formula α} : (A.and B).eval D V = A.eval D V ∩ B.eval D V :=
  Set.ext fun _ ↦ mem_eval_and

theorem eval_box (A : Formula α) : A.box.eval D V = ofDomain D (A.eval D V)ᶜ (A.eval D V) := rfl

/-- A tautology is true under every valuation of the formulas that respects negation and material
implication, the conditional formulas valued freely. -/
def IsTautology (A : Formula α) : Prop :=
  ∀ val : Formula α → Prop, (∀ B, val B.neg ↔ ¬ val B) →
    (∀ B C, val (B.imp C) ↔ (val B → val C)) → val A

end Formula

open Formula

variable {α : Type*}

/-- The theorems of C2: the axiom schemata (a1)–(a7), closed under modus ponens and
necessitation. -/
inductive Provable : Formula α → Prop
  | taut {A : Formula α} : A.IsTautology → Provable A
  | a2 (A B : Formula α) : Provable ((A.imp B).box.imp (A.box.imp B.box))
  | a3 (A B : Formula α) : Provable ((A.imp B).box.imp (A.corner B))
  | a4 (A B : Formula α) : Provable (A.dia.imp ((A.corner B).imp (A.corner B.neg).neg))
  | a5 (A B C : Formula α) : Provable ((A.corner (B.or C)).imp ((A.corner B).or (A.corner C)))
  | a6 (A B : Formula α) : Provable ((A.corner B).imp (A.imp B))
  | a7 (A B C : Formula α) : Provable ((A.bicond B).imp ((A.corner C).imp (B.corner C)))
  | mp {A B : Formula α} : Provable (A.imp B) → Provable A → Provable B
  | nec {A : Formula α} : Provable A → Provable A.box

/-- A formula is valid when it holds at every world of every model. -/
def Valid (A : Formula α) : Prop :=
  ∀ {W : Type u} {R : W → Set W} {D : W → Set W → Set W}, IsSelectionFunction R D →
    ∀ V : α → Set W, A.eval D V = Set.univ

/-- Every theorem of C2 is valid. -/
theorem Provable.sound {A : Formula α} (h : Provable A) : Valid.{u} A := by
  intro W R D hM V
  refine Set.eq_univ_of_forall fun w ↦ ?_
  induction h generalizing w with
  | taut h => exact h (fun B ↦ w ∈ B.eval D V) (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl
  | a2 A B =>
    simp only [mem_eval_imp, eval_box, hM.mem_ofDomain_compl_iff]
    exact fun h hA v hv ↦ h v hv (hA v hv)
  | a3 A B =>
    simp only [mem_eval_imp, eval_box, hM.mem_ofDomain_compl_iff, mem_eval_corner]
    exact fun h y hy ↦ h y (.of_mem (hM.subsingleton w _) hy (hM.subset w _ hy)) (hM.subset w _ hy)
  | a4 A B =>
    simp only [dia, mem_eval_imp, mem_eval_neg, mem_eval_corner]
    exact fun hdia hAB hAnB ↦ hdia fun y hy ↦ absurd (hAB hy) (hAnB hy)
  | a5 A B C =>
    simp only [Formula.or, mem_eval_imp, mem_eval_neg, mem_eval_corner]
    intro h hnB y hy
    have hD := (hM.subsingleton w _).eq_singleton_of_mem hy
    exact h hy fun hyB ↦ hnB fun z hz ↦ (Set.mem_singleton_iff.1 (hD ▸ hz)) ▸ hyB
  | a6 A B =>
    simp only [mem_eval_imp, mem_eval_corner]
    exact fun h hA ↦ h ((hM.centering w _ hA).symm ▸ rfl)
  | a7 A B C =>
    simp only [bicond, mem_eval_imp, mem_eval_and, mem_eval_corner]
    exact fun ⟨hAB, hBA⟩ hAC ↦ hM.cso w _ _ hBA hAB ▸ hAC
  | mp _ _ ihab iha => exact ihab w (iha w)
  | nec _ ih => exact fun y _ ↦ ih y

theorem provable_cem (A B : Formula α) : Provable ((A.corner B).or (A.corner B.neg)) :=
  .mp (.a5 A B B.neg) <| .mp (.a3 A (B.or B.neg)) <| .nec <| .taut fun _ _ hi ↦ by
    simp only [Formula.or, hi]; exact fun _ h ↦ h

/-- When the antecedent is possible, a denied conditional is equivalent to the conditional with
the opposite consequent (§III, (2)). -/
theorem provable_neg_corner (A B : Formula α) :
    Provable (A.dia.imp ((A.corner B).neg.iff (A.corner B.neg))) := by
  refine .mp (.mp (.taut fun val hn hi ↦ ?_) (provable_cem A B)) (.a4 A B)
  simp only [Formula.or, Formula.iff, Formula.and, hi, hn]
  tauto

/-! ### Invalid inferences

The countermodels order three worlds cyclically, `0` closest to itself, then `1`, then `2`. -/

/-- The closest antecedent-world when the worlds of `Fin 3` are ordered by distance ahead. -/
def cyclicSelection (w : Fin 3) (A : Set (Fin 3)) : Set (Fin 3) :=
  (Preorder.lift (· - w)).minimals (Set.univ ∩ A)

theorem cyclicSelection_subset_iff {w : Fin 3} {A B : Set (Fin 3)} :
    cyclicSelection w A ⊆ B ↔ ∀ v ∈ A, (∀ b ∈ A, v - w ≤ b - w) → v ∈ B := by
  simp only [Set.subset_def, cyclicSelection, Preorder.mem_minimals_lift, Set.univ_inter]
  exact ⟨fun h v hv hl ↦ h v ⟨hv, hl⟩, fun h v hv ↦ h v hv.1 hv.2⟩

theorem isSelectionFunction_cyclicSelection :
    IsSelectionFunction (fun _ ↦ Set.univ) cyclicSelection :=
  isSelectionFunction_minimals (fun _ ↦ trivial)
    (fun w w' ↦ (by decide : ∀ w w' : Fin 3, w ≠ w' → w - w < w' - w) w w')
    (fun _ ↦ Preorder.total_lift _)
    (fun w ↦ ⟨(by decide : ∀ w a b : Fin 3, a - w ≤ b - w → b - w ≤ a - w → a = b) w⟩)
    fun _ ↦ Preorder.wellFounded_lt_lift _

theorem not_valid_of_cyclicSelection {β : Type} {A : Formula β} (V : β → Set (Fin 3))
    (h : (0 : Fin 3) ∉ A.eval cyclicSelection V) : ¬ Valid.{0} A := fun hA ↦
  h (by rw [hA isSelectionFunction_cyclicSelection V]; trivial)

/-- The corner is not transitive: if Hoover were a communist he would be a traitor, and if he had
been born a Russian he would be a communist, but not: if he had been born a Russian he would be a
traitor. -/
theorem not_valid_trans :
    ¬ Valid.{0} ((((atom 0 : Formula (Fin 3)).corner (atom 1)).and ((atom 1).corner (atom 2))).imp
      ((atom 0).corner (atom 2))) :=
  not_valid_of_cyclicSelection ![{v | v = 2}, {v | v ≠ 0}, {v | v = 1}] <| by
    simp only [mem_eval_imp, mem_eval_corner, eval_atom, eval_and, cyclicSelection_subset_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Set.mem_ofPred_eq, Set.mem_inter_iff]
    decide

/-- Strengthening the antecedent fails: if the match were struck it would light, but not if it
had been soaked overnight and were struck. -/
theorem not_valid_strengthening :
    ¬ Valid.{0} (((atom 0 : Formula (Fin 3)).corner (atom 2)).imp
      (((atom 0).and (atom 1)).corner (atom 2))) :=
  not_valid_of_cyclicSelection ![{v | v ≠ 0}, {v | v = 2}, {v | v = 1}] <| by
    simp only [mem_eval_imp, mem_eval_corner, eval_atom, eval_and, cyclicSelection_subset_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Set.mem_ofPred_eq, Set.mem_inter_iff]
    decide

/-- Contraposition fails: if the bombing were halted North Vietnam would not negotiate, but not:
if North Vietnam negotiated the bombing would not have been halted. -/
theorem not_valid_contraposition :
    ¬ Valid.{0} (((atom 0 : Formula (Fin 2)).corner (atom 1)).imp
      ((atom 1).neg.corner (atom 0).neg)) :=
  not_valid_of_cyclicSelection ![{v | v ≠ 1}, {v | v ≠ 2}] <| by
    simp only [mem_eval_imp, mem_eval_corner, eval_atom, eval_neg, cyclicSelection_subset_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_ofPred_eq, Set.mem_compl_iff]
    decide

/-! ### Valid inferences

Footnote 10 notes that `C` follows from `A > B`, `B > C` and `A`, and that the biconditional is
transitive; footnote 11 that modus tollens is valid. -/

theorem valid_corner_trans_of_mem (A B C : Formula α) :
    Valid.{u} ((((A.corner B).and (B.corner C)).and A).imp C) := fun hM _ ↦
  Set.eq_univ_of_forall fun w ↦ by
    simp only [mem_eval_imp, mem_eval_and, mem_eval_corner]
    rintro ⟨⟨hAB, hBC⟩, hA⟩
    rw [hM.centering w _ hA, Set.singleton_subset_iff] at hAB
    rwa [hM.centering w _ hAB, Set.singleton_subset_iff] at hBC

theorem valid_bicond_trans (A B C : Formula α) :
    Valid.{u} (((A.bicond B).and (B.bicond C)).imp (A.bicond C)) := fun hM _ ↦
  Set.eq_univ_of_forall fun w ↦ by
    simp only [bicond, mem_eval_imp, mem_eval_and, mem_eval_corner]
    rintro ⟨⟨hAB, hBA⟩, hBC, hCB⟩
    rw [hM.cso w _ _ hBA hAB, ← hM.cso w _ _ hCB hBC]
    exact ⟨hBC, hBA⟩

theorem valid_modus_tollens (A B : Formula α) :
    Valid.{u} (((A.corner B).and B.neg).imp A.neg) := fun hM _ ↦
  Set.eq_univ_of_forall fun w ↦ by
    simp only [mem_eval_imp, mem_eval_and, mem_eval_corner, mem_eval_neg]
    exact fun ⟨hAB, hnB⟩ hA ↦ hnB (hAB ((hM.centering w _ hA).symm ▸ rfl))

/-! ### Defined necessity -/

theorem mem_ofDomain_compl_minimals_iff {ord : W → Preorder W}
    (hM : IsSelectionFunction R fun w A ↦ (ord w).minimals (R w ∩ A)) :
    w ∈ ofDomain (fun w A ↦ (ord w).minimals (R w ∩ A)) pᶜ p ↔ R w ⊆ p := by
  rw [hM.mem_ofDomain_compl_iff]
  exact ⟨fun h v hv ↦ h v (hM.prior_self_of_mem hv),
    fun h v ⟨A, hA, _⟩ ↦ by
      have hv : v ∈ (ord w).minimals (R w ∩ A) := by simp only at hA; rw [hA]; rfl
      exact h ((ord w).minimals_subset _ hv).1⟩

/-- Under Stalnaker's assumption, `□A ⊃ □□A` holds when relative possibility is transitive. -/
theorem box_imp_box_box_minimals {ord : W → Preorder W}
    (hM : IsSelectionFunction R fun w A ↦ (ord w).minimals (R w ∩ A))
    (htrans : ∀ w v, v ∈ R w → R v ⊆ R w) (A : Formula α) (V : α → Set W) :
    (A.box.imp A.box.box).eval (fun w A ↦ (ord w).minimals (R w ∩ A)) V = Set.univ :=
  Set.eq_univ_of_forall fun w h ↦ by
    rw [eval_box, mem_ofDomain_compl_minimals_iff hM] at h ⊢
    exact fun v hv ↦ (mem_ofDomain_compl_minimals_iff hM).2 ((htrans w v hv).trans h)

open Classical in
/-- A selection function on three worlds, each possible only relative to itself, that selects an
inaccessible world: `1` at `0` and `2` at `1`, for antecedents false at the base world. -/
noncomputable def inaccessibleSelection (w : Fin 3) (A : Set (Fin 3)) : Set (Fin 3) :=
  if w ∈ A then {w} else A ∩ {v | v = w + 1 ∧ w ≠ 2}

theorem inaccessibleSelection_subset_iff {w : Fin 3} {A B : Set (Fin 3)} :
    inaccessibleSelection w A ⊆ B ↔
      (w ∈ A → w ∈ B) ∧ (w ∉ A → w ≠ 2 → w + 1 ∈ A → w + 1 ∈ B) := by
  unfold inaccessibleSelection
  split_ifs with h
  · simp [h]
  · simp only [h, Set.subset_def, Set.mem_inter_iff, Set.mem_ofPred_eq, false_imp_iff,
      not_false_eq_true, forall_const, true_and]
    exact ⟨fun h' hw hA ↦ h' _ ⟨hA, rfl, hw⟩, fun h' x ⟨hx, hxw, hw⟩ ↦ hxw ▸ h' hw (hxw ▸ hx)⟩

theorem isSelectionFunction_inaccessibleSelection :
    IsSelectionFunction (fun w ↦ {w}) inaccessibleSelection where
  refl _ := rfl
  subsingleton w A := by
    unfold inaccessibleSelection; split_ifs
    · exact Set.subsingleton_singleton
    · exact Set.subsingleton_singleton.anti fun v hv ↦ hv.2.1
  subset w A := by
    unfold inaccessibleSelection; split_ifs with h
    exacts [Set.singleton_subset_iff.2 h, Set.inter_subset_left]
  absurdity w A h := by
    by_cases hw : w ∈ A
    · simp [inaccessibleSelection, hw] at h
    · simpa using hw
  centering w A h := by simp [inaccessibleSelection, h]
  cso w A B h₁ h₂ := by
    unfold inaccessibleSelection at *
    by_cases hA : w ∈ A <;> by_cases hB : w ∈ B <;> simp only [hA, hB, ite_true, ite_false]
      at h₁ h₂ ⊢
    · exact absurd (h₂ rfl) hB
    · exact absurd (h₁ rfl) hA
    · exact subset_antisymm (Set.subset_inter h₂ Set.inter_subset_right)
        (Set.subset_inter h₁ Set.inter_subset_right)

/-- Footnote 7 fails: with relative possibility the identity, transitive and symmetric, a
selection function can make `□A` true and `□□A` false. -/
theorem exists_not_box_imp_box_box :
    ∃ (R : Fin 3 → Set (Fin 3)) (D : Fin 3 → Set (Fin 3) → Set (Fin 3)),
      IsSelectionFunction R D ∧ (∀ w, R w = {w}) ∧
        ((atom () : Formula Unit).box.imp (atom ()).box.box).eval D (fun _ ↦ {v | v ≠ 2}) ≠
          Set.univ := by
  refine ⟨_, _, isSelectionFunction_inaccessibleSelection, fun _ ↦ rfl, fun h ↦ ?_⟩
  have := Set.eq_univ_iff_forall.1 h 0
  revert this
  simp only [mem_eval_imp, box, mem_eval_corner, eval_atom, eval_neg,
    inaccessibleSelection_subset_iff, Set.mem_ofPred_eq, Set.mem_compl_iff]
  simp

end Stalnaker1968
