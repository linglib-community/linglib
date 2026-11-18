module

public import Linglib.Logic.Orthologic.Basic
public import Linglib.Logic.Orthologic.Epistemic.Ortholattice

/-!
# The epistemic orthologic

This file defines Holliday and Mandelkern's epistemic orthologics and proves the least one, EO,
[sound and complete for epistemic ortholattices](##Orthologic.ModalFormula.derivable_iff). The
modal language adds a necessity modal `□` to the language of orthologic, with `◇φ := ¬□¬φ`. An
epistemic orthologic is an orthologic under which `□` is monotone, preserves `∧` and `⊤`, and is
factive, and which satisfies Wittgenstein's Law `¬φ ∧ ◇φ ⊢ ⊥`. Over monotonicity and factivity
the law [is the principle that `φ ⊢ ⊥` whenever
`□φ ⊢ ⊥`](##Orthologic.wittgenstein_iff_le_bot_of_box_le_bot). The Lindenbaum–Tarski algebra of
an epistemic orthologic is an epistemic ortholattice, so the algebraic consequences of the law
hold in every epistemic orthologic, among them [`φ ∧ ◇ⁿ¬φ ⊢ ⊥` for every
`n`](##Orthologic.IsEpistemicOrthologic.inf_diamond_iterate_compl_le).

## Implementation notes

`IsEpistemicOrthologic F box` is a class on any consequence preorder, so Lemma 3.25 and Fact 3.28
hold, as the paper states them, for every epistemic orthologic and not only for EO, whose instance
is on `ModalFormula`.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

universe u

namespace Orthologic

/-! ### Epistemic orthologics -/

/-- Possibility `◇φ := ¬□¬φ` for a necessity operator `box` ([holliday-mandelkern-2024]
Definition 3.21). -/
def IsEpistemicOrthologic.diamond {F : Type*} [Compl F] (box : F → F) (φ : F) : F := (box φᶜ)ᶜ

/-- An orthologic with a necessity operator `box` is an *epistemic orthologic* when `box` is
monotone, preserves `∧` and `⊤`, and is factive, and `¬φ ∧ ◇φ ⊢ ⊥` holds with `⊥ = ¬⊤`
([holliday-mandelkern-2024] Definition 3.24). -/
class IsEpistemicOrthologic (F : Type*) [Preorder F] [Top F] [Min F] [Compl F] (box : F → F) :
    Prop extends IsOrthologic F where
  protected box_mono : Monotone box
  protected le_box_inf (φ ψ : F) : box φ ⊓ box ψ ≤ box (φ ⊓ ψ)
  protected le_box_top (φ : F) : φ ≤ box ⊤
  protected box_le (φ : F) : box φ ≤ φ
  protected wittgenstein (φ : F) : φᶜ ⊓ IsEpistemicOrthologic.diamond box φ ≤ ⊤ᶜ

section

variable {F : Type*} [Preorder F] [Top F] [Min F] [Compl F] [IsOrthologic F] {box : F → F}

/-- Over an orthologic in which `□` is monotone and factive, Wittgenstein's Law holds iff `φ ⊢ ⊥`
whenever `□φ ⊢ ⊥`. The forward direction is [holliday-mandelkern-2024] Lemma 3.25, and the
converse is the remark after it, carried out in the proof of Fact 3.28. -/
theorem wittgenstein_iff_le_bot_of_box_le_bot (hmono : Monotone box) (hT : ∀ φ, box φ ≤ φ) :
    (∀ φ, φᶜ ⊓ IsEpistemicOrthologic.diamond box φ ≤ ⊤ᶜ) ↔ ∀ φ, box φ ≤ ⊤ᶜ → φ ≤ ⊤ᶜ := by
  refine ⟨fun hW φ h ↦ ?_, fun h φ ↦ h _ ?_⟩
  · refine (IsOrthologic.le_inf (IsOrthologic.le_compl_compl φ) ?_).trans (hW φᶜ)
    exact (IsOrthologic.le_top φ).trans <| (IsOrthologic.le_compl_compl ⊤).trans <|
      IsOrthologic.compl_le_compl <| (hmono (IsOrthologic.compl_compl_le φ)).trans h
  · exact (IsOrthologic.le_inf (hmono (IsOrthologic.inf_le_left _ _))
      (hmono (IsOrthologic.inf_le_right _ _))).trans <|
        (IsOrthologic.inf_mono le_rfl (hT _)).trans (IsOrthologic.inf_compl_le _ _)

end

namespace LindenbaumTarski

variable {F : Type*} [Preorder F] [Top F] [Min F] [Compl F] (box : F → F)
  [IsEpistemicOrthologic F box]

/-- `□` on the Lindenbaum–Tarski algebra of an epistemic orthologic, which preserves `⊓`
and `⊤`. -/
def boxHom : InfTopHom (LindenbaumTarski F) (LindenbaumTarski F) where
  toFun := (⟨box, IsEpistemicOrthologic.box_mono⟩ : F →o F).antisymmetrization
  map_inf' a b := ((OrderHom.monotone _).map_inf_le a b).antisymm <|
    Quotient.inductionOn₂ a b fun φ ψ ↦ mk_le_mk.mpr (IsEpistemicOrthologic.le_box_inf φ ψ)
  map_top' := le_top.antisymm (mk_le_mk.mpr (IsEpistemicOrthologic.le_box_top _))

@[simp] theorem boxHom_mk (φ : F) :
    boxHom box (toAntisymmetrization (· ≤ ·) φ) = toAntisymmetrization (· ≤ ·) (box φ) := rfl

/-- The Lindenbaum–Tarski algebra of an epistemic orthologic is an epistemic ortholattice
([holliday-mandelkern-2024] proof of Theorem 3.26). -/
theorem isEpistemic_boxHom : IsEpistemic (boxHom box) where
  apply_le a := Quotient.inductionOn a fun φ ↦ mk_le_mk.mpr (IsEpistemicOrthologic.box_le φ)
  wittgensteinLaw a := disjoint_iff_inf_le.mpr <| Quotient.inductionOn a fun φ ↦
    mk_le_mk.mpr (IsEpistemicOrthologic.wittgenstein (box := box) φ)

end LindenbaumTarski

namespace IsEpistemicOrthologic

open LindenbaumTarski

variable {F : Type*} [Preorder F] [Top F] [Min F] [Compl F] {box : F → F}
  [IsEpistemicOrthologic F box]

/-- In an epistemic orthologic a proposition whose necessity is contradictory is itself
contradictory ([holliday-mandelkern-2024] Lemma 3.25). -/
theorem le_bot_of_box_le_bot {φ : F} (h : box φ ≤ ⊤ᶜ) : φ ≤ ⊤ᶜ :=
  (wittgenstein_iff_le_bot_of_box_le_bot IsEpistemicOrthologic.box_mono
    IsEpistemicOrthologic.box_le).mp IsEpistemicOrthologic.wittgenstein φ h

/-- In an epistemic orthologic generalized Wittgenstein sentences are contradictions,
`φ ∧ ◇ⁿ¬φ ⊢ ⊥` for every `n` ([holliday-mandelkern-2024] Fact 3.28). -/
theorem inf_diamond_iterate_compl_le (n : ℕ) (φ : F) : φ ⊓ (diamond box)^[n] φᶜ ≤ ⊤ᶜ := by
  have hs : Function.Semiconj (toAntisymmetrization (· ≤ ·)) (diamond box)
      (diamondHom (boxHom box)) := fun _ ↦ rfl
  have h := (isEpistemic_boxHom box).disjoint_diamondHom_iterate n (toAntisymmetrization (· ≤ ·) φ)
  rw [← mk_compl, ← hs.iterate_right n φᶜ] at h
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
def diamond (φ : ModalFormula Var) : ModalFormula Var := neg (box (neg φ))

end ModalFormula

/-- Consequence in the least epistemic orthologic EO is generated by Goldblatt's ten rules for
orthologic, rules making `□` monotone, preserve `∧` and `⊤`, and factive, and Wittgenstein's Law
([holliday-mandelkern-2024] Definition 3.24). -/
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
  | le_box_and (φ ψ) : EDerivable (.and (.box φ) (.box ψ)) (.box (.and φ ψ))
  | le_box_top (φ) : EDerivable φ (.box .top)
  | box_le (φ) : EDerivable (.box φ) φ
  | wittgenstein (φ) : EDerivable (.and (.neg φ) (.diamond φ)) .bot

namespace ModalFormula

variable {Var : Type u} {φ ψ : ModalFormula Var}

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

instance : IsEpistemicOrthologic (ModalFormula Var) box where
  le_top := EDerivable.top_intro
  inf_le_left := EDerivable.and_le_left
  inf_le_right := EDerivable.and_le_right
  le_compl_compl := EDerivable.le_negNeg
  compl_compl_le := EDerivable.negNeg_le
  inf_compl_le := EDerivable.contradiction
  le_inf := EDerivable.le_and
  compl_le_compl := EDerivable.neg_le_neg
  box_mono _ _ := EDerivable.box_mono
  le_box_inf := EDerivable.le_box_and
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

@[simp] theorem eval_diamond (φ : ModalFormula Var) :
    eval bx v (diamond φ) = diamondHom bx (eval bx v φ) := rfl

end eval

/-- An ortholattice homomorphism that commutes with the necessity operators commutes with
evaluation. -/
theorem map_eval {M F : Type*} [Lattice M] [BoundedOrder M] [InvolutiveCompl M] [FunLike F L M]
    [OrtholatticeHomClass F L M] (f : F) {bx : InfTopHom L L} {bx' : InfTopHom M M}
    (hbox : ∀ a, f (bx a) = bx' (f a)) (v : Var → L) (φ : ModalFormula Var) :
    f (eval bx v φ) = eval bx' (fun p ↦ f (v p)) φ := by
  induction φ with
  | top => exact map_top f
  | var p => rfl
  | neg φ ih => rw [eval, eval, OrtholatticeHomClass.map_compl, ih]
  | and φ ψ ihφ ihψ => rw [eval, eval, map_inf, ihφ, ihψ]
  | box φ ih => rw [eval, eval, hbox, ih]

/-- EO-consequences hold in every epistemic ortholattice under every valuation
([holliday-mandelkern-2024] Theorem 3.26, soundness). -/
theorem sound [IsOrtholattice L] {bx : InfTopHom L L} (hE : IsEpistemic bx) (h : EDerivable φ ψ)
    (v : Var → L) :
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
  | le_box_and φ ψ => exact (map_inf bx _ _).ge
  | le_box_top φ => exact le_top.trans (map_top bx).ge
  | box_le φ => exact hE.apply_le _
  | wittgenstein φ => exact (hE.wittgensteinLaw _).le_bot.trans InvolutiveCompl.compl_top.ge

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

/-- A consequence holding in every epistemic ortholattice under every valuation is derivable in EO
([holliday-mandelkern-2024] Theorem 3.26, completeness). -/
theorem complete
    (h : ∀ {L : Type u} [Lattice L] [BoundedOrder L] [InvolutiveCompl L] [IsOrtholattice L]
      (bx : InfTopHom L L), IsEpistemic bx → ∀ v : Var → L, eval bx v φ ≤ eval bx v ψ) :
    EDerivable φ ψ := by
  have key := h (boxHom box) (isEpistemic_boxHom box) canonicalVal
  rwa [eval_canonicalVal, eval_canonicalVal, mk_le_mk] at key

/-- EO is sound and complete for epistemic ortholattices ([holliday-mandelkern-2024]
Theorem 3.26). -/
theorem derivable_iff :
    EDerivable φ ψ ↔ ∀ {L : Type u} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]
      [IsOrtholattice L] (bx : InfTopHom L L), IsEpistemic bx →
        ∀ v : Var → L, eval bx v φ ≤ eval bx v ψ :=
  ⟨fun h _ _ _ _ _ _ hE v ↦ sound hE h v, complete⟩

end ModalFormula

end Orthologic
