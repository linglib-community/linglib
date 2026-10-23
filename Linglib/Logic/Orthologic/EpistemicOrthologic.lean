module

public import Linglib.Logic.Orthologic.Basic
public import Linglib.Logic.Orthologic.Epistemic

/-!
# The epistemic orthologic

This file defines Holliday and Mandelkern's epistemic orthologics and proves the least one, EO,
sound and complete for epistemic ortholattices. The modal language adds a necessity modal `□` to
the language of orthologic, with `◇φ := ¬□¬φ`. An epistemic orthologic is an orthologic under
which `□` is monotone, preserves `∧` and `⊤`, and is factive, and which satisfies Wittgenstein's
Law `¬φ ∧ ◇φ ⊢ ⊥`. Its Lindenbaum–Tarski algebra is an epistemic ortholattice, so the algebraic
consequences of the law hold in every epistemic orthologic, and a consequence holding in every
epistemic ortholattice is derivable in EO.

## Main definitions

* `Orthologic.IsEpistemicOrthologic F box`: the rules for `□` on an orthologic.
* `Orthologic.LindenbaumTarski.boxHom`: `□` on the Lindenbaum–Tarski algebra.
* `Orthologic.ModalFormula`, `Orthologic.EDerivable`: the modal language and the least
  epistemic orthologic EO.
* `Orthologic.ModalFormula.eval`: the value of a formula in an ortholattice with a necessity
  operator.

## Main results

* `Orthologic.IsEpistemicOrthologic.le_bot_of_box_le_bot`: if `□φ ⊢ ⊥` then `φ ⊢ ⊥`.
* `Orthologic.IsEpistemicOrthologic.inf_dia_iterate_compl_le`: `φ ∧ ◇ⁿ¬φ ⊢ ⊥` for every `n`.
* `Orthologic.ModalFormula.derivable_iff`: EO is sound and complete for epistemic ortholattices.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

namespace Orthologic

/-! ### Epistemic orthologics -/

/-- An orthologic with a necessity operator `box` is an *epistemic orthologic* when `box` is
    monotone, preserves `∧` and `⊤`, and is factive, and `¬φ ∧ ◇φ ⊢ ⊥` holds with
    `◇φ = ¬□¬φ` and `⊥ = ¬⊤` ([holliday-mandelkern-2024] Definition 3.24). -/
class IsEpistemicOrthologic (F : Type*) [Preorder F] [Top F] [Min F] [Compl F] (box : F → F) :
    Prop where
  protected box_mono {φ ψ : F} : φ ≤ ψ → box φ ≤ box ψ
  protected box_inf_le (φ ψ : F) : box φ ⊓ box ψ ≤ box (φ ⊓ ψ)
  protected le_box_top (φ : F) : φ ≤ box ⊤
  protected box_le (φ : F) : box φ ≤ φ
  protected wittgenstein (φ : F) : φᶜ ⊓ (box φᶜ)ᶜ ≤ ⊤ᶜ

namespace LindenbaumTarski

variable {F : Type*} [Preorder F] [Top F] [Min F] [Compl F] [IsOrthologic F]
  (box : F → F) [IsEpistemicOrthologic F box]

/-- `□` on the Lindenbaum–Tarski algebra of an epistemic orthologic, which preserves `⊓`
    and `⊤`. -/
def boxHom : InfTopHom (LindenbaumTarski F) (LindenbaumTarski F) where
  toFun := Quotient.map box fun _ _ h ↦
    ⟨IsEpistemicOrthologic.box_mono h.1, IsEpistemicOrthologic.box_mono h.2⟩
  map_inf' a b := Quotient.inductionOn₂ a b fun φ ψ ↦ Quotient.sound
    ⟨IsOrthologic.le_inf (IsEpistemicOrthologic.box_mono (IsOrthologic.inf_le_left φ ψ))
      (IsEpistemicOrthologic.box_mono (IsOrthologic.inf_le_right φ ψ)),
      IsEpistemicOrthologic.box_inf_le φ ψ⟩
  map_top' := Quotient.sound ⟨IsOrthologic.le_top _, IsEpistemicOrthologic.le_box_top _⟩

theorem boxHom_mk (φ : F) :
    boxHom box (toAntisymmetrization (· ≤ ·) φ) = toAntisymmetrization (· ≤ ·) (box φ) := rfl

theorem boxHom_le (a : LindenbaumTarski F) : boxHom box a ≤ a :=
  Quotient.inductionOn a fun φ ↦ mk_le_mk.mpr (IsEpistemicOrthologic.box_le φ)

theorem wittgensteinLaw_boxHom : WittgensteinLaw (boxHom box) := fun a ↦
  disjoint_iff_inf_le.mpr <| Quotient.inductionOn a fun φ ↦
    mk_le_mk.mpr (IsEpistemicOrthologic.wittgenstein (box := box) φ)

theorem mk_dia_iterate (n : ℕ) (φ : F) :
    toAntisymmetrization (· ≤ ·) ((fun ψ ↦ (box ψᶜ)ᶜ)^[n] φ) =
      (diamondHom (boxHom box))^[n] (toAntisymmetrization (· ≤ ·) φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

end LindenbaumTarski

namespace IsEpistemicOrthologic

open LindenbaumTarski

variable {F : Type*} [Preorder F] [Top F] [Min F] [Compl F] [IsOrthologic F]
  {box : F → F} [IsEpistemicOrthologic F box]

/-- In an epistemic orthologic a proposition whose necessity is contradictory is itself
    contradictory ([holliday-mandelkern-2024] Lemma 3.25). -/
theorem le_bot_of_box_le_bot {φ : F} (h : box φ ≤ ⊤ᶜ) : φ ≤ ⊤ᶜ :=
  mk_le_mk.mp ((wittgensteinLaw_boxHom box).eq_bot_of_box_eq_bot
    (le_bot_iff.mp (mk_le_mk.mpr h))).le

/-- In an epistemic orthologic generalized Wittgenstein sentences are contradictions,
    `φ ∧ ◇ⁿ¬φ ⊢ ⊥` for every `n` ([holliday-mandelkern-2024] Fact 3.28). -/
theorem inf_dia_iterate_compl_le (n : ℕ) (φ : F) : φ ⊓ (fun ψ ↦ (box ψᶜ)ᶜ)^[n] φᶜ ≤ ⊤ᶜ := by
  have h := (wittgensteinLaw_boxHom box).disjoint_diamondHom_iterate (boxHom_le box) n
    (toAntisymmetrization (· ≤ ·) φ)
  rw [← mk_compl, ← mk_dia_iterate] at h
  exact mk_le_mk.mp (disjoint_iff_inf_le.mp h)

end IsEpistemicOrthologic

/-! ### The least epistemic orthologic -/

/-- Formulas of the modal language over a variable type `Var`, with `⊥` and `◇` defined
    ([holliday-mandelkern-2024] Definition 3.21). -/
inductive ModalFormula (Var : Type*) where
  | top : ModalFormula Var
  | var (p : Var) : ModalFormula Var
  | neg (φ : ModalFormula Var) : ModalFormula Var
  | and (φ ψ : ModalFormula Var) : ModalFormula Var
  | box (φ : ModalFormula Var) : ModalFormula Var

namespace ModalFormula

variable {Var : Type*}

/-- Falsum is `¬⊤`. -/
def bot : ModalFormula Var := neg top

/-- Possibility is `◇φ := ¬□¬φ`. -/
def dia (φ : ModalFormula Var) : ModalFormula Var := neg (box (neg φ))

end ModalFormula

/-- Consequence in the least epistemic orthologic EO is generated by Goldblatt's ten rules for
    orthologic, rules making `□` monotone, preserve `∧` and `⊤`, and factive, and Wittgenstein's
    Law ([holliday-mandelkern-2024] Definition 3.24). -/
inductive EDerivable {Var : Type*} : ModalFormula Var → ModalFormula Var → Prop where
  | top_intro (φ) : EDerivable φ .top
  | refl (φ) : EDerivable φ φ
  | and_le_left (φ ψ) : EDerivable (.and φ ψ) φ
  | and_le_right (φ ψ) : EDerivable (.and φ ψ) ψ
  | le_negNeg (φ) : EDerivable φ (.neg (.neg φ))
  | negNeg_le (φ) : EDerivable (.neg (.neg φ)) φ
  | contradiction (φ ψ) : EDerivable (.and φ (.neg φ)) ψ
  | trans {φ ψ χ} : EDerivable φ ψ → EDerivable ψ χ → EDerivable φ χ
  | le_and {φ ψ χ} : EDerivable φ ψ → EDerivable φ χ → EDerivable φ (.and ψ χ)
  | neg_le_neg {φ ψ} : EDerivable φ ψ → EDerivable (.neg ψ) (.neg φ)
  | box_mono {φ ψ} : EDerivable φ ψ → EDerivable (.box φ) (.box ψ)
  | box_and (φ ψ) : EDerivable (.and (.box φ) (.box ψ)) (.box (.and φ ψ))
  | le_box_top (φ) : EDerivable φ (.box .top)
  | box_le (φ) : EDerivable (.box φ) φ
  | wittgenstein (φ) : EDerivable (.and (.neg φ) (.dia φ)) .bot

namespace ModalFormula

variable {Var : Type*}

/-- The connectives of the modal language share the symbols of the lattice operations, as in
    [holliday-mandelkern-2024]. -/
instance : Top (ModalFormula Var) := ⟨top⟩

instance : Min (ModalFormula Var) := ⟨and⟩

instance : Compl (ModalFormula Var) := ⟨neg⟩

/-- Consequence in EO is a preorder, reflexivity and cut. -/
instance : Preorder (ModalFormula Var) where
  le := EDerivable
  le_refl := EDerivable.refl
  le_trans _ _ _ h := h.trans

instance : IsOrthologic (ModalFormula Var) where
  le_top := EDerivable.top_intro
  inf_le_left := EDerivable.and_le_left
  inf_le_right := EDerivable.and_le_right
  le_compl_compl := EDerivable.le_negNeg
  compl_compl_le := EDerivable.negNeg_le
  inf_compl_le := EDerivable.contradiction
  le_inf := EDerivable.le_and
  compl_le_compl := EDerivable.neg_le_neg

instance : IsEpistemicOrthologic (ModalFormula Var) box where
  box_mono := EDerivable.box_mono
  box_inf_le := EDerivable.box_and
  le_box_top := EDerivable.le_box_top
  box_le := EDerivable.box_le
  wittgenstein := EDerivable.wittgenstein

/-! ### Evaluation, soundness and completeness -/

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]

/-- The value of a formula in an ortholattice with a necessity operator under a valuation
    ([holliday-mandelkern-2024] Definition 3.22). -/
def eval (bx : InfTopHom L L) (v : Var → L) : ModalFormula Var → L
  | .top => ⊤
  | .var p => v p
  | .neg φ => (eval bx v φ)ᶜ
  | .and φ ψ => eval bx v φ ⊓ eval bx v ψ
  | .box φ => bx (eval bx v φ)

section eval

variable (bx : InfTopHom L L) (v : Var → L)

@[simp] theorem eval_top : eval bx v ⊤ = ⊤ := rfl

@[simp] theorem eval_var (p : Var) : eval bx v (var p) = v p := rfl

@[simp] theorem eval_compl (φ : ModalFormula Var) : eval bx v φᶜ = (eval bx v φ)ᶜ := rfl

@[simp] theorem eval_inf (φ ψ : ModalFormula Var) :
    eval bx v (φ ⊓ ψ) = eval bx v φ ⊓ eval bx v ψ := rfl

@[simp] theorem eval_box (φ : ModalFormula Var) : eval bx v (box φ) = bx (eval bx v φ) := rfl

@[simp] theorem eval_dia (φ : ModalFormula Var) :
    eval bx v (dia φ) = diamondHom bx (eval bx v φ) := rfl

end eval

/-- EO-consequences hold in every epistemic ortholattice under every valuation
    ([holliday-mandelkern-2024] Theorem 3.26, soundness). -/
theorem sound [IsOrtholattice L] {bx : InfTopHom L L} (hT : ∀ a, bx a ≤ a)
    (hW : WittgensteinLaw bx) {φ ψ : ModalFormula Var} (h : EDerivable φ ψ) (v : Var → L) :
    eval bx v φ ≤ eval bx v ψ := by
  induction h with
  | top_intro φ => exact le_top
  | refl φ => exact le_rfl
  | and_le_left φ ψ => exact inf_le_left
  | and_le_right φ ψ => exact inf_le_right
  | le_negNeg φ => exact (InvolutiveCompl.compl_compl _).ge
  | negNeg_le φ => exact (InvolutiveCompl.compl_compl _).le
  | contradiction φ ψ => exact (IsOrtholattice.inf_compl_eq_bot _).le.trans bot_le
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | le_and _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | neg_le_neg _ ih => exact InvolutiveCompl.compl_le_compl ih
  | box_mono _ ih => exact OrderHomClass.mono bx ih
  | box_and φ ψ => exact (map_inf bx _ _).ge
  | le_box_top φ => exact le_top.trans (map_top bx).ge
  | box_le φ => exact hT _
  | wittgenstein φ => exact (hW _).le_bot.trans InvolutiveCompl.compl_top.ge

open LindenbaumTarski

/-- The canonical valuation into the Lindenbaum–Tarski algebra sends `p` to its class. -/
def canonicalVal : Var → LindenbaumTarski (ModalFormula Var) :=
  fun p ↦ toAntisymmetrization (· ≤ ·) (var p)

theorem eval_canonicalVal (φ : ModalFormula Var) :
    eval (boxHom box) canonicalVal φ = toAntisymmetrization (· ≤ ·) φ := by
  induction φ with
  | top => rfl
  | var p => rfl
  | neg φ ih => rw [eval, ih]; rfl
  | and φ ψ ihφ ihψ => rw [eval, ihφ, ihψ]; rfl
  | box φ ih => rw [eval, ih]; rfl

universe u

/-- EO is sound and complete for epistemic ortholattices: `φ ⊢ ψ` iff the inequality holds in
    every epistemic ortholattice under every valuation ([holliday-mandelkern-2024]
    Theorem 3.26). Epistemic ortholattices in `Var`'s universe suffice. -/
theorem derivable_iff {Var : Type u} {φ ψ : ModalFormula Var} :
    EDerivable φ ψ ↔ ∀ {L : Type u} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]
      [IsOrtholattice L] (bx : InfTopHom L L), (∀ a, bx a ≤ a) →
        WittgensteinLaw bx → ∀ v : Var → L, eval bx v φ ≤ eval bx v ψ := by
  refine ⟨fun h _ _ _ _ _ _ hT hW v ↦ sound hT hW h v, fun h ↦ ?_⟩
  have key := h (boxHom box) (boxHom_le box) (wittgensteinLaw_boxHom box) canonicalVal
  rwa [eval_canonicalVal, eval_canonicalVal, mk_le_mk] at key

end ModalFormula

end Orthologic
