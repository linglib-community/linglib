module

public import Mathlib.ModelTheory.Basic
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.Nat

/-!
# The positions of a word

A word model is a word as a first-order structure: its positions, each carrying the labels of its
symbol. This file defines the type of positions and what every reading of it shares. The positions
of `u` are those of `Fin u.length` with its linear order. The relational signature
`Subregular.wordLanguage` names the labels and one ordering of the positions, and the functional
signature of `Subregular.StringModel` names the successor and predecessor of the order, which fix
the last and the first position.

## Main definitions

* `Subregular.wordLanguage`: the signature of labels and one binary ordering.
* `Subregular.WordModel`: the positions of a word, under a labelling of its symbols and an ordering.
* `Subregular.WordModel.succ`, `Subregular.WordModel.pred`: the next and the previous position,
  the last being its own successor and the first its own predecessor.

## Main results

* `Subregular.WordModel.succ_eq_orderSucc`, `Subregular.WordModel.pred_eq_orderPred`: the two steps
  are the successor and predecessor of the order of positions.
* `Subregular.WordModel.covBy_iff_succ_eq`: one position covers another exactly when the second is
  the successor of the first and differs from it.

## Implementation notes

* A labelling is a function `ℓ : β → Set P` passed to `WordModel`, the labels each symbol carries:
  `({·})` in the conventional model, where a symbol is its own one label, and the feature values of
  a segment for words of segments.
* An ordering is a relation on the positions passed to `WordModel`, so precedence is
  `WordModel ℓ w (· < ·)` and successor `WordModel ℓ w (· ⋖ ·)`.
* `succ` and `pred` are defined by arithmetic on the index, so that statements about them are
  decided by evaluation, and proved equal to `Order.succ` and `Order.pred`.

## References

* [rogers-lambert-2019]
* [chandlee-jardine-2019]
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language

namespace Subregular

variable {α : Type u}

/-- The relation symbols of word models, a unary label for each symbol and a binary
ordering. -/
inductive WordRel (α : Type u) : ℕ → Type u
  | label (a : α) : WordRel α 1
  | ord : WordRel α 2

/-- The signature of word models over `α`. -/
def wordLanguage (α : Type u) : FirstOrder.Language := ⟨fun _ ↦ Empty, WordRel α⟩

instance : (wordLanguage α).IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The word model of `u` under a labelling `ℓ` of its symbols and an ordering `R` of its
positions: a position carries the labels `ℓ` gives its symbol. In the conventional model a
symbol is its own one label, `ℓ = ({·})`. -/
def WordModel {β P : Type*} (_ : β → Set P) (u : List β)
    (_ : Fin u.length → Fin u.length → Prop) : Type :=
  Fin u.length

namespace WordModel

variable {β P : Type*} {ℓ : β → Set P} {u : List β} {R : Fin u.length → Fin u.length → Prop}

instance : LinearOrder (WordModel ℓ u R) := inferInstanceAs (LinearOrder (Fin u.length))

instance : SuccOrder (WordModel ℓ u R) := inferInstanceAs (SuccOrder (Fin u.length))

instance : PredOrder (WordModel ℓ u R) := inferInstanceAs (PredOrder (Fin u.length))

instance : Fintype (WordModel ℓ u R) := inferInstanceAs (Fintype (Fin u.length))

/-- A position, as an index into the word. -/
def toFin (i : WordModel ℓ u R) : Fin u.length := i

/-- The symbol at a position. -/
def label (i : WordModel ℓ u R) : β := u.get i

/-- A position satisfies the unary relations of the labels its symbol carries. -/
instance : (wordLanguage P).Structure (WordModel ℓ u R) where
  RelMap
    | .label p, x => p ∈ ℓ (x 0).label
    | .ord, x => R (x 0) (x 1)

@[simp] theorem relMap_label (p : P) (x : Fin 1 → WordModel ℓ u R) :
    Structure.RelMap (L := wordLanguage P) (WordRel.label p) x ↔
      p ∈ ℓ (x 0).label := .rfl

@[simp] theorem relMap_ord (x : Fin 2 → WordModel ℓ u R) :
    Structure.RelMap (L := wordLanguage P) WordRel.ord x ↔ R (x 0) (x 1) := .rfl

/-! ### Positions by index -/

/-- Position `n` of `u`. -/
def mk (n : ℕ) (h : n < u.length) : WordModel ℓ u R := ⟨n, h⟩

/-- The index of a position. -/
def val (i : WordModel ℓ u R) : ℕ := Fin.val (n := u.length) i

theorem val_lt (i : WordModel ℓ u R) : i.val < u.length := Fin.isLt (n := u.length) i

@[simp] theorem val_mk {n : ℕ} (h : n < u.length) : (mk n h : WordModel ℓ u R).val = n := rfl

theorem ext {i j : WordModel ℓ u R} (h : i.val = j.val) : i = j := Fin.ext (n := u.length) h

theorem le_iff_val_le {i j : WordModel ℓ u R} : i ≤ j ↔ i.val ≤ j.val := .rfl

theorem getElem?_val (i : WordModel ℓ u R) : u[i.val]? = some i.label :=
  List.getElem?_eq_getElem i.val_lt

theorem label_eq_iff {i : WordModel ℓ u R} {a : β} : i.label = a ↔ u[i.val]? = some a := by
  rw [getElem?_val, Option.some_inj]

/-! ### Successor and predecessor -/

/-- The successor of a position, the last position being its own. -/
def succ (i : WordModel ℓ u R) : WordModel ℓ u R :=
  if h : i.val + 1 < u.length then mk (i.val + 1) h else i

/-- The predecessor of a position, the first position being its own. -/
def pred (i : WordModel ℓ u R) : WordModel ℓ u R :=
  mk (i.val - 1) (by have := i.val_lt; omega)

theorem val_succ (i : WordModel ℓ u R) :
    i.succ.val = if i.val + 1 < u.length then i.val + 1 else i.val := by
  unfold succ; split_ifs <;> rfl

@[simp] theorem val_pred (i : WordModel ℓ u R) : i.pred.val = i.val - 1 := rfl

/-- The successor of a position is that of the order of positions. -/
theorem succ_eq_orderSucc (i : WordModel ℓ u R) : i.succ = Order.succ i := by
  unfold succ
  split_ifs with h
  · exact (CovBy.succ_eq (Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 rfl))).symm
  · exact (Order.succ_eq_iff_isMax.2 fun j _ ↦ le_iff_val_le.2 (by have := j.val_lt; omega)).symm

/-- The predecessor of a position is that of the order of positions. -/
theorem pred_eq_orderPred (i : WordModel ℓ u R) : i.pred = Order.pred i := by
  by_cases h : i.val = 0
  · rw [Order.pred_eq_iff_isMin.2 fun j _ ↦ le_iff_val_le.2 (by omega)]
    exact ext (by simp [h])
  · have hc : i.pred ⋖ i :=
      Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 (by change i.val - 1 + 1 = i.val; omega))
    exact hc.pred_eq.symm

/-- One position covers another exactly when the second is the successor of the first and
differs from it. -/
theorem covBy_iff_succ_eq {i j : WordModel ℓ u R} : i ⋖ j ↔ i.succ = j ∧ i ≠ j := by
  rw [succ_eq_orderSucc]
  exact ⟨fun h ↦ ⟨h.succ_eq, h.lt.ne⟩, fun ⟨h, hne⟩ ↦ h ▸ Order.covBy_succ_of_not_isMax
    fun hmax ↦ hne ((Order.succ_eq_iff_isMax.2 hmax).symm.trans h)⟩

/-- In a successor word model the ordering holds of two positions exactly when the second is the
successor of the first and differs from it. -/
theorem relMap_ord_covBy_iff (x : Fin 2 → WordModel ℓ u (· ⋖ ·)) :
    Structure.RelMap (L := wordLanguage P) WordRel.ord x ↔ (x 0).succ = x 1 ∧ x 0 ≠ x 1 :=
  covBy_iff_succ_eq

end WordModel

end Subregular
