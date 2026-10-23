module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability
public import Linglib.Logic.Team.Atoms
public import Linglib.Logic.Team.Bisimulation

/-!
# Modal inclusion logic

Modal inclusion logic ML(⊆) extends classical modal logic with inclusion atoms `a ⊆ b`, supported
by a team when every tuple of truth values that `a` takes at a world of the team is taken by `b`
at some world of the team. It has support only, no anti-support. Its `◇` is lax: a team supports
`◇φ` when some team of successors supporting `φ` reaches every world of the team. ML(⊆) formulas
are union closed and supported by the empty team, but the inclusion atom breaks downward
closure. Anttila, Häggblom and Yang axiomatize the logic and characterize its expressive power.

## Main definitions

* `Formula`: atoms, `⊥`, inclusion atoms, `¬`, `∧`, split `∨`, `◇` and `□`.
* `eval`, `support`: support of a formula by a team.
* `Formula.modalDepth`: the nesting depth of `◇` and `□`.
* `Formula.InclFree`, `Realize`: the fragment without inclusion atoms, and classical truth.

## Main results

* `supClosed_support`, `support_empty`: support is union closed and contains `∅`.
* `not_isLowerSet_incl_of_witness`: the inclusion atom is not downward closed.
* `invariant_eval`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.
* `definableClass_support_subset`: every definable team property is union closed, contains `∅`
  and is closed under bounded bisimulation.
* `support_iff_forall_realize`: without inclusion atoms, support is pointwise classical truth.

## Implementation notes

`eval` is a fold over the operations of `Team/Operations.lean` and the inclusion atom
`Team.incl`. It departs from the source in two ways. Inclusion atoms relate lists of atoms,
where the source allows classical formulas. Negation applies to any formula, with the source's
pointwise clause, where the source restricts it to classical formulas.

## TODO

* The converse of `definableClass_support_subset`. The source's normal form uses inclusion atoms
  `⊤ ⊆ α` over classical formulas, which the atom-only encoding lacks.
* The natural-deduction axiomatization and its completeness.
* The might operator and the singular might operator, which have the same expressive power.

## References

* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
-/

@[expose] public section

namespace ModalLogic.Inclusion

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)

/-! ### Syntax -/

/-- The formulas of ML(⊆) ([anttila-haggblom-yang-2025] Definition 2.1), with `◇` and `□` both
    primitive. An inclusion atom `α₁...αₙ ⊆ β₁...βₙ` is the list of pairs
    `[(α₁, β₁), ..., (αₙ, βₙ)]`. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Weak contradiction `⊥`. -/
  | bot
  /-- Inclusion atom `x⃗ ⊆ y⃗`. -/
  | incl (xys : List (Atom × Atom))
  /-- Classical negation (restricted to classical formulas in the paper;
      we allow on any formula for uniform recursion). -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction. -/
  | disj (φ ψ : Formula Atom)
  /-- Possibility modal `◇` (lax semantics). -/
  | poss (φ : Formula Atom)
  /-- Necessity modal `□`. -/
  | nec (φ : Formula Atom)
  deriving Repr

/-! ### Classical truth

Without inclusion atoms MIL is classical modal logic ([anttila-2021]'s Proposition 2.2.16
for the lax and image modalities, `support_iff_forall_realize` below). -/

/-- `Formula.InclFree φ` holds when `φ` contains no inclusion atom. -/
def Formula.InclFree : Formula Atom → Prop
  | .atom _ | .bot => True
  | .incl _ => False
  | .neg φ | .poss φ | .nec φ => φ.InclFree
  | .conj φ ψ | .disj φ ψ => φ.InclFree ∧ ψ.InclFree

open scoped ModalLogic in
/-- Classical Kripke truth of a MIL formula at a world, with `◇` and `□` the shared
    `ModalLogic.Diamond` and `ModalLogic.Box`; an inclusion atom is true at every world. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w
  | .bot, _ => False
  | .incl _, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.accessible] (Realize M ψ) w
  | .nec ψ, w => □[M.accessible] (Realize M ψ) w

theorem realize_poss {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

theorem realize_nec {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.nec ψ) w ↔ ∀ v ∈ M.access w, Realize M ψ v := Iff.rfl

variable [DecidableEq W]

/-! ### Semantics -/

/-- A team supports a formula ([anttila-haggblom-yang-2025] Definition 2.2). -/
def eval (M : KripkeModel W Atom) : Formula Atom → Finset W → Prop
  | .atom p,        t => t ∈ Team.flat (M.val p)
  | .bot,           t => t ∈ ({∅} : Team.TeamProperty W)
  | .incl xys,      t =>
      (t : Set W) ∈ Team.incl (fun w ↦ xys.map (M.val ·.1 w)) (fun w ↦ xys.map (M.val ·.2 w))
  | .neg ψ,         t => t ∈ Team.flat fun w ↦ ¬ eval M ψ {w}
  | .conj ψ₁ ψ₂,    t => eval M ψ₁ t ∧ eval M ψ₂ t
  | .disj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M ψ₁ s} {s | eval M ψ₂ s}
  | .poss ψ,        t => t ∈ Team.possLax M.access {s | eval M ψ s}
  | .nec ψ,         t => t ∈ Team.necImage M.access {s | eval M ψ s}

/-- Support is `eval`, under its conventional name; ML(⊆) has no anti-support. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M φ t

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w := Iff.rfl

@[simp] lemma support_bot (M : KripkeModel W Atom) (t : Finset W) :
    support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_incl (M : KripkeModel W Atom) (xys : List (Atom × Atom))
    (t : Finset W) :
    support M (.incl xys) t ↔
      ∀ w₁ ∈ t, ∃ w₂ ∈ t, ∀ xy ∈ xys, (M.val xy.1 w₁ ↔ M.val xy.2 w₂) := by
  simp only [support, eval, Team.mem_incl, Finset.mem_coe, List.map_inj_left, eq_iff_iff]

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ ∀ w ∈ t, ¬ support M φ {w} := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁, support M φ t₁ ∧ ∃ t₂, support M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma support_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.poss φ) t ↔
      ∃ S : Finset W, S ⊆ t.biUnion M.access ∧
        (∀ w ∈ t, ∃ s ∈ S, s ∈ M.access w) ∧ support M φ S := Iff.rfl

@[simp] lemma support_nec (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.nec φ) t ↔ support M φ (t.biUnion M.access) := Iff.rfl

/-! ### Modal depth -/

/-- The modal depth of a formula is the greatest number of nested modalities in it. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ | .bot | .incl _ => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ | .nec ψ => ψ.modalDepth + 1

/-! ### Union closure -/

/-- Every MIL formula has union-closed support. Each case is the closure lemma of its connective
    in `Team/Operations.lean`, and an inclusion witness in either team is one in the union. -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } := by
  induction φ with
  | atom p => exact Team.supClosed_flat _
  | bot => exact Team.supClosed_singleton_empty
  | incl xys =>
    intro s hs t ht
    simp only [Set.mem_setOf_eq, support, eval, Finset.sup_eq_union, Finset.coe_union]
    exact Team.supClosed_incl _ _ hs ht
  | neg ψ _ => exact Team.supClosed_flat _
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.tensor ih₂
  | poss ψ ih => exact ih.possLax
  | nec ψ ih => exact ih.necImage

/-! ### Empty team property -/

theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ := by
  induction φ with
  | atom p => exact Team.empty_mem_flat _
  | bot => rfl
  | incl xys =>
    simp only [support, eval, Finset.coe_empty]
    exact Team.empty_mem_incl _ _
  | neg ψ _ => exact Team.empty_mem_flat _
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact Team.empty_mem_tensor ih₁ ih₂
  | poss ψ ih => exact Team.empty_mem_possLax ih
  | nec ψ ih => exact Team.empty_mem_necImage ih

/-! ### Inclusion breaks downward closure (the defining feature) -/

/-- The inclusion atom is not downward closed. If `w₂` supplies the `b`-value matching both its
    own and `w₁`'s `a`-value but `w₁` does not match itself, then `{w₁, w₂}` supports `a ⊆ b`
    and `{w₁}` does not. -/
theorem not_isLowerSet_incl_of_witness {a b : Atom} {w₁ w₂ : W} {M : KripkeModel W Atom}
    (hpair : M.val a w₁ ↔ M.val b w₂) (hself : M.val a w₂ ↔ M.val b w₂)
    (hwit : ¬ (M.val a w₁ ↔ M.val b w₁)) :
    ¬ IsLowerSet { t : Finset W | support M (.incl [(a, b)]) t } := fun h ↦ by
  have hs : support M (.incl [(a, b)]) {w₁, w₂} := (support_incl M _ _).2 fun w hw ↦
    ⟨w₂, by simp, by rcases Finset.mem_insert.1 hw with rfl | hw <;> simp_all⟩
  obtain ⟨w, hw, hw'⟩ := (support_incl M _ _).1
    (h (by simp : ({w₁} : Finset W) ⊆ {w₁, w₂}) hs) w₁ (by simp)
  rw [Finset.mem_singleton.1 hw] at hw'
  exact hwit (by simpa using hw')

/-! ### Bisimulation invariance -/

section Bisimulation

open ModalLogic (WorldBisim BisimClosed)

variable {W' : Type*} [DecidableEq W'] {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}

/-- Teams that are `k`-bisimilar agree on every formula of modal depth at most `k`
    ([anttila-haggblom-yang-2025] Theorem 3.6). -/
theorem invariant_eval {k : ℕ} (φ : Formula Atom) (hd : φ.modalDepth ≤ k) :
    Team.Invariant (WorldBisim k M · M' ·) {t | eval M φ t} {t | eval M' φ t} := by
  induction φ generalizing k with
  | atom p => exact Team.invariant_flat fun _ _ h ↦ h.val_iff p
  | bot => exact Team.invariant_singleton_empty
  | incl xys =>
    exact Team.invariant_incl (fun _ _ h ↦ List.map_congr_left fun x _ ↦ propext (h.val_iff x.1))
      fun _ _ h ↦ List.map_congr_left fun x _ ↦ propext (h.val_iff x.2)
  | neg ψ ih => exact Team.invariant_flat fun _ _ h ↦ not_congr ((ih hd).singleton h)
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact (ih₁ hd₁).inter (ih₂ hd₂)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    obtain ⟨hd₁, hd₂⟩ := max_le_iff.mp hd
    exact (ih₁ hd₁).tensor (ih₂ hd₂)
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    exact (ih (Nat.le_of_succ_le_succ hd)).possLax fun _ _ h ↦ h.2
  | nec ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    exact (ih (Nat.le_of_succ_le_succ hd)).necImage fun _ _ h ↦ h.2

theorem bisimClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    BisimClosed M {t | support M φ t} :=
  ⟨φ.modalDepth, invariant_eval φ le_rfl⟩

end Bisimulation

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team ModalLogic in
/-- Every MIL-definable team property is union closed, contains the empty team and is closed
    under bounded bisimulation. This is the easy inclusion of the expressive completeness of
    ML(⊆) ([anttila-haggblom-yang-2025] §3). -/
theorem definableClass_support_subset (M : KripkeModel W Atom) :
    definableClass (support M) ⊆ {P | SupClosed P ∧ ∅ ∈ P ∧ BisimClosed M P} :=
  definableClass_subset fun φ ↦ ⟨supClosed_support M φ, support_empty M φ, bisimClosed_support M φ⟩

/-! ### The classical fragment

On `incl`-free formulas support is pointwise classical truth: the lax and image modalities
agree with the flat ones on flat properties (`Team.possLax_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- On `incl`-free formulas, support is pointwise classical truth. -/
theorem support_iff_forall_realize (hI : φ.InclFree) (t : Finset W) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  induction φ generalizing t with
  | atom p => simp [support, eval, Realize]
  | bot => simp [support, eval, Realize, Finset.eq_empty_iff_forall_notMem]
  | incl xys => exact hI.elim
  | neg ψ ih =>
    simp only [support, eval, Team.mem_flat, Realize]
    exact forall₂_congr fun w _ ↦ not_congr ((ih hI {w}).trans (by simp))
  | conj ψ₁ ψ₂ ih₁ ih₂ => simp [support, eval, ih₁ hI.1, ih₂ hI.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [support, eval, ih₁ hI.1, ih₂ hI.2]
    exact Team.mem_tensor_flat.trans (by simp [Realize])
  | poss ψ ih =>
    simp only [support, eval, ih hI]
    exact Team.mem_possLax_flat.trans (by simp [realize_poss])
  | nec ψ ih =>
    simp only [support, eval, ih hI]
    exact Team.mem_necImage_flat.trans (by simp [realize_nec])

theorem support_singleton_iff_realize (hI : φ.InclFree) : support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hI]

end Classical

end ModalLogic.Inclusion
