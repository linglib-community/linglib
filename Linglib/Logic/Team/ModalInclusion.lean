module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Atoms
public import Linglib.Logic.Team.Bisimulation

/-!
# Modal inclusion logic

Modal inclusion logic ML(⊆) extends classical modal logic with inclusion atoms `a ⊆ b`, supported
by a team when every tuple of truth values that `a` takes at a world of the team is taken by `b`
at some world of the team. It has support only, no anti-support. Its `◇` is lax: a team supports
`◇φ` when some team of successors supporting `φ` reaches every world of the team. ML(⊆) formulas
are union closed and supported by the empty team, but the inclusion atom breaks downward
closure. This file develops the variant whose inclusion atoms relate propositional symbols,
modal inclusion logic simpliciter in the terms of Anttila, Häggblom and Yang, who axiomatize the
extended variant, with atoms over classical formulas, and characterize its expressive power. The
simple variant is [strictly less
expressive](##ModalLogic.Inclusion.range_support_ssubset_of_subsingleton): in one propositional
symbol its only inclusion atoms are trivial, so every formula is flat.

## Main definitions

* `Formula`: atoms, `⊥`, inclusion atoms, `¬`, `∧`, split `∨`, `◇` and `□`.
* `eval`, `support`: support of a formula by a team.
* `Formula.modalDepth`: the nesting depth of `◇` and `□`.
* `Formula.InclFree`, `Formula.InclTrivial`, `Realize`: the formulas without inclusion atoms and
  those whose inclusion atoms are trivial, and classical truth.

## Main results

* `supClosed_support`, `support_empty`: support is union closed and contains `∅`.
* `not_isLowerSet_incl_of_witness`: the inclusion atom is not downward closed.
* `invariant_eval`: `k`-bisimilar teams agree on every formula of modal depth at most `k`.
* `range_support_subset`: the classes of pointed team models the logic expresses are union closed,
  contain the empty team and are invariant under bounded bisimulation.
* `setOf_support_of_inclTrivial`, `support_iff_forall_realize`: when every inclusion atom is
  trivial, support is pointwise classical truth.
* `range_support_ssubset_of_subsingleton`: in one propositional symbol that inclusion is strict.

## Implementation notes

`eval` is a fold over the operations of `Team/Operations.lean` and the inclusion atom
`Team.incl`. It departs from the source in two ways. Inclusion atoms relate lists of atoms,
where the source allows classical formulas. Negation applies to any formula, with the source's
pointwise clause, where the source restricts it to classical formulas.

## TODO

* The extended variant, with inclusion atoms over classical formulas, and for it the converse of
  `range_support_subset`, whose normal form in the source uses atoms `⊤ ⊆ α`.
* The natural-deduction axiomatization and its completeness.
* The might operator and the singular might operator, which have the same expressive power.

## References

* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal Logics
-/

@[expose] public section

open scoped SetFamily

namespace ModalLogic.Inclusion

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)

/-! ### Syntax -/

/-- The formulas of modal inclusion logic simpliciter, with `◇` and `□` both primitive. An
inclusion atom `p₁...pₙ ⊆ q₁...qₙ` over propositional symbols is the list of pairs
`[(p₁, q₁), ..., (pₙ, qₙ)]`; [anttila-haggblom-yang-2025] Definition 2.1 allows classical
formulas in the atoms. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Weak contradiction `⊥`. -/
  | bot
  /-- Inclusion atom `p⃗ ⊆ q⃗`. -/
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

/-- `Formula.InclTrivial φ` holds when every inclusion atom of `φ` includes each symbol in itself, a
trivial atom `p ⊆ p` that every team supports. -/
def Formula.InclTrivial : Formula Atom → Prop
  | .atom _ | .bot => True
  | .incl xys => ∀ xy ∈ xys, xy.1 = xy.2
  | .neg φ | .poss φ | .nec φ => φ.InclTrivial
  | .conj φ ψ | .disj φ ψ => φ.InclTrivial ∧ ψ.InclTrivial

theorem Formula.InclFree.inclTrivial {φ : Formula Atom} (h : φ.InclFree) : φ.InclTrivial := by
  induction φ with
  | atom | bot => trivial
  | incl => exact h.elim
  | neg _ ih | poss _ ih | nec _ ih => exact ih h
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

/-- In one propositional symbol every inclusion atom is trivial. -/
theorem Formula.inclTrivial_of_subsingleton [Subsingleton Atom] (φ : Formula Atom) :
    φ.InclTrivial := by
  induction φ with
  | atom | bot => trivial
  | incl => exact fun _ _ ↦ Subsingleton.elim _ _
  | neg _ ih | poss _ ih | nec _ ih => exact ih
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

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
  | .disj ψ₁ ψ₂,    t => t ∈ {s | eval M ψ₁ s} ⊻ {s | eval M ψ₂ s}
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
    simp only [Set.mem_ofPred_eq, support, eval, Finset.sup_eq_union, Finset.coe_union]
    exact Team.supClosed_incl _ _ hs ht
  | neg ψ _ => exact Team.supClosed_flat _
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.sups ih₂
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
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact Set.bot_mem_sups ih₁ ih₂
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

open ModalLogic (WorldBisim)

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
    exact (ih₁ hd₁).sups (ih₂ hd₂)
  | poss ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    exact (ih (Nat.le_of_succ_le_succ hd)).possLax fun _ _ h ↦ h.2
  | nec ψ ih =>
    obtain _ | k := k
    · exact absurd hd (Nat.not_succ_le_zero _)
    exact (ih (Nat.le_of_succ_le_succ hd)).necImage fun _ _ h ↦ h.2

end Bisimulation

/-! ### The classical fragment

On formulas whose inclusion atoms are trivial, `incl`-free ones among them, support is pointwise
classical truth: the lax and image modalities agree with the flat ones on flat properties
(`Team.possLax_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- On formulas whose inclusion atoms are trivial, the teams supporting a formula are the flat
property of its classical truth. Each case is the commutation of a connective with `Team.flat`. -/
theorem setOf_support_of_inclTrivial (hI : φ.InclTrivial) :
    {t | support M φ t} = Team.flat (Realize M φ) := by
  induction φ with
  | atom p => rfl
  | bot => exact Set.ext fun t ↦ Finset.eq_empty_iff_forall_notMem
  | incl xys =>
    exact Set.ext fun t ↦ iff_of_true ((support_incl M _ _).2 fun w hw ↦
      ⟨w, hw, fun xy hxy ↦ by rw [hI xy hxy]⟩) fun _ _ ↦ trivial
  | neg ψ ih =>
    exact congrArg Team.flat <| funext fun w ↦ propext <| not_congr <|
      (Set.ext_iff.1 (ih hI) {w}).trans <| by simp
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    exact (congrArg₂ (· ∩ ·) (ih₁ hI.1) (ih₂ hI.2)).trans (Team.flat_inter _ _)
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    exact (congrArg₂ (· ⊻ ·) (ih₁ hI.1) (ih₂ hI.2)).trans (Team.flat_sups_flat _ _)
  | poss ψ ih => exact (congrArg (Team.possLax M.access) (ih hI)).trans (Team.possLax_flat _ _)
  | nec ψ ih => exact (congrArg (Team.necImage M.access) (ih hI)).trans (Team.necImage_flat _ _)

/-- On formulas whose inclusion atoms are trivial, support is pointwise classical truth. -/
theorem support_iff_forall_realize (hI : φ.InclTrivial) (t : Finset W) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w :=
  Set.ext_iff.1 (setOf_support_of_inclTrivial hI) t

theorem support_singleton_iff_realize (hI : φ.InclTrivial) :
    support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hI]

end Classical

/-! ### Expressive power -/

section ExpressivePower

universe u

/-- The class a formula expresses is invariant under bounded bisimulation, at the formula's modal
depth ([anttila-haggblom-yang-2025] p. 766, by Theorem 3.6). -/
theorem boundedBisimInvariant_support (φ : Formula Atom) :
    BoundedBisimInvariant {p : PointedTeam.{u} Atom | support p.model φ p.team} :=
  ⟨φ.modalDepth, fun _ hp _ hb ↦ (invariant_eval φ le_rfl hb).1 hp⟩

/-- The logic expresses only classes of pointed team models that are union closed, contain the
empty team and are invariant under bounded bisimulation ([anttila-haggblom-yang-2025] p. 766).
-/
theorem range_support_subset :
    (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) ⊆
      {P | Fiberwise (fun T ↦ SupClosed T ∧ ∅ ∈ T) P ∧ BoundedBisimInvariant P} :=
  Set.range_subset_iff.2 fun φ ↦ ⟨fun M ↦ ⟨supClosed_support M φ, support_empty M φ⟩,
    boundedBisimInvariant_support φ⟩

/-- In one propositional symbol every formula is flat, so the inclusion is strict: the teams that
are empty or hold a world where the symbol is true form such a class that no formula expresses.
The extended variant of [anttila-haggblom-yang-2025] expresses it by the atom `⊤ ⊆ p` (p. 768).
-/
theorem range_support_ssubset_of_subsingleton [Subsingleton Atom] [Nonempty Atom] :
    (Set.range fun φ : Formula Atom ↦ {p : PointedTeam.{u} Atom | support p.model φ p.team}) ⊂
      {P | Fiberwise (fun T ↦ SupClosed T ∧ ∅ ∈ T) P ∧ BoundedBisimInvariant P} := by
  refine ⟨range_support_subset, fun h ↦ ?_⟩
  inhabit Atom
  let Q : Set (PointedTeam.{u} Atom) := {q | q.team = ∅ ∨ ∃ w ∈ q.team, q.model.val default w}
  have hsup {W : Type u} [DecidableEq W] (M : KripkeModel W Atom) :
      SupClosed (PointedTeam.mk W M ⁻¹' Q) := by
    rintro s (hs | ⟨w, hw, hv⟩) t ht
    · have hs : s = ∅ := hs
      subst hs
      simpa using ht
    · exact .inr ⟨w, Finset.mem_union_left _ hw, hv⟩
  have hinv : BoundedBisimInvariant Q := ⟨0, by
    rintro ⟨W, M, s⟩ (hs | ⟨w, hw, hv⟩) ⟨W', M', s'⟩ ⟨hf, hb⟩
    · refine .inl (Finset.eq_empty_of_forall_notMem fun w' hw' ↦ ?_)
      obtain ⟨w, hw, -⟩ := hb w' hw'
      have hs : s = ∅ := hs
      exact Finset.notMem_empty w (hs ▸ hw)
    · obtain ⟨w', hw', hb'⟩ := hf w hw
      exact .inr ⟨w', hw', (hb'.val_iff default).1 hv⟩⟩
  obtain ⟨φ, hφ⟩ := h ⟨fun M ↦ ⟨hsup M, .inl rfl⟩, hinv⟩
  let M : KripkeModel (ULift.{u} Bool) Atom := ⟨fun _ ↦ ∅, fun _ w ↦ w.down = true⟩
  let a : ULift.{u} Bool := ⟨true⟩
  let b : ULift.{u} Bool := ⟨false⟩
  have hiff (t : Finset (ULift.{u} Bool)) : support M φ t ↔ t ∈ PointedTeam.mk _ M ⁻¹' Q :=
    Set.ext_iff.1 hφ (.mk _ M t)
  have hflat := support_iff_forall_realize (M := M) (φ := φ) φ.inclTrivial_of_subsingleton
  have htop : support M φ {a, b} := (hiff _).2 (.inr ⟨a, by simp, rfl⟩)
  have hb : support M φ {b} :=
    (hflat _).2 fun w hw ↦ (hflat _).1 htop w (by simp [Finset.mem_singleton.1 hw])
  rcases (hiff _).1 hb with h' | ⟨w, hw, hv⟩
  · exact Finset.singleton_ne_empty b h'
  · have hw : w = b := Finset.mem_singleton.1 hw
    subst hw
    exact Bool.false_ne_true hv

end ExpressivePower

end ModalLogic.Inclusion
