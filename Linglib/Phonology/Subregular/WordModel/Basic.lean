module

public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# The positions of a word

A word model is a word as a first-order structure: its positions, each carrying the labels of its
symbol. This file defines the type of positions and what every reading of it shares. The positions
of `u` are those of `Fin u.length` with its linear order, which has two orderings a signature may
name: successor, its covering relation, and precedence, its strict order. The relational signature
`Subregular.wordLanguage P S` names the labels and the orderings in `S`, and the functional
signature of `Subregular.StringModel` names the successor and predecessor of the order, which fix
the last and the first position.

## Main definitions

* `Subregular.WordOrd`: the orderings of positions, successor and precedence.
* `Subregular.wordLanguage`: the signature of labels and a set of orderings.
* `Subregular.wordLHom`: the inclusion of a signature naming fewer orderings in one naming more,
  along which word models are expansions.
* `Subregular.WordModel`: the positions of a word, under a labelling of its symbols.
* `Subregular.WordModel.succ`, `Subregular.WordModel.pred`: the next and the previous position,
  the last being its own successor and the first its own predecessor.

## Main results

* `Subregular.WordModel.succ_eq_orderSucc`, `Subregular.WordModel.pred_eq_orderPred`: the two steps
  are the successor and predecessor of the order of positions.
* `Subregular.WordModel.covBy_iff_succ_eq`, `Subregular.WordModel.relMap_ord_succ_iff`: one
  position covers another, which is the successor ordering, exactly when the second is the
  successor of the first and differs from it.

## Implementation notes

* A labelling is a function `ℓ : β → Set P` passed to `WordModel`, the labels each symbol carries:
  `({·})` in the conventional model, where a symbol is its own one label, and the feature values of
  a segment for words of segments.
* The orderings belong to the signature and not to the type of positions: the successor models
  are the structures of `wordLanguage P {.succ}` and the precedence models those of
  `wordLanguage P {.prec}`, on the same positions, and `wordLanguage P Set.univ` names both
  orderings, as the word models of Rogers and Lambert do.
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

/-- The orderings of the positions of a word that a signature may name. -/
inductive WordOrd
  /-- Successor: one position immediately precedes the other. -/
  | succ
  /-- Precedence: one position precedes the other. -/
  | prec
  deriving DecidableEq, Fintype

/-- The relation symbols of word models, a unary label for each symbol and a binary relation for
each ordering in `S`. -/
inductive WordRel (α : Type u) (S : Set WordOrd) : ℕ → Type u
  | label (a : α) : WordRel α S 1
  | ord (o : S) : WordRel α S 2

/-- The signature of word models over `α` naming the orderings in `S`. -/
def wordLanguage (α : Type u) (S : Set WordOrd) : FirstOrder.Language :=
  ⟨fun _ ↦ Empty, WordRel α S⟩

instance {S : Set WordOrd} : (wordLanguage α S).IsRelational :=
  fun _ ↦ inferInstanceAs (IsEmpty Empty)

variable (α) in
/-- A signature naming fewer orderings maps into one naming more. -/
def wordLHom {S T : Set WordOrd} (h : S ⊆ T) : wordLanguage α S →ᴸ wordLanguage α T where
  onFunction := fun _ f ↦ (f : Empty).elim
  onRelation := fun _ r ↦ match r with
    | .label a => .label a
    | .ord o => .ord ⟨o, h o.2⟩

/-- The word model of `u` under a labelling `ℓ` of its symbols: a position carries the labels `ℓ`
gives its symbol. In the conventional model a symbol is its own one label, `ℓ = ({·})`. -/
def WordModel {β P : Type*} (_ : β → Set P) (u : List β) : Type :=
  Fin u.length

namespace WordModel

variable {β P : Type*} {ℓ : β → Set P} {u : List β} {S : Set WordOrd}

instance : LinearOrder (WordModel ℓ u) := inferInstanceAs (LinearOrder (Fin u.length))

instance : SuccOrder (WordModel ℓ u) := inferInstanceAs (SuccOrder (Fin u.length))

instance : PredOrder (WordModel ℓ u) := inferInstanceAs (PredOrder (Fin u.length))

instance : Fintype (WordModel ℓ u) := inferInstanceAs (Fintype (Fin u.length))

/-- A position, as an index into the word. -/
def toFin (i : WordModel ℓ u) : Fin u.length := i

/-- The symbol at a position. -/
def label (i : WordModel ℓ u) : β := u.get i

/-- The relation on positions an ordering names: the covering relation for successor and the strict
order for precedence. -/
def Rel : WordOrd → WordModel ℓ u → WordModel ℓ u → Prop
  | .succ => (· ⋖ ·)
  | .prec => (· < ·)

@[simp] theorem rel_succ {i j : WordModel ℓ u} : Rel .succ i j ↔ i ⋖ j := .rfl

@[simp] theorem rel_prec {i j : WordModel ℓ u} : Rel .prec i j ↔ i < j := .rfl

/-- A position satisfies the unary relations of the labels its symbol carries, and two positions
the binary relation of an ordering when the ordering relates them. -/
instance : (wordLanguage P S).Structure (WordModel ℓ u) where
  RelMap
    | .label p, x => p ∈ ℓ (x 0).label
    | .ord o, x => Rel o (x 0) (x 1)

@[simp] theorem relMap_label (p : P) (x : Fin 1 → WordModel ℓ u) :
    Structure.RelMap (L := wordLanguage P S) (WordRel.label p) x ↔
      p ∈ ℓ (x 0).label := .rfl

@[simp] theorem relMap_ord (o : S) (x : Fin 2 → WordModel ℓ u) :
    Structure.RelMap (L := wordLanguage P S) (WordRel.ord o) x ↔ Rel o (x 0) (x 1) := .rfl

/-- The word models of a signature naming more orderings expand those of one naming fewer, on the
same positions. -/
instance {T : Set WordOrd} (h : S ⊆ T) : (wordLHom P h).IsExpansionOn (WordModel ℓ u) where
  map_onFunction := fun f ↦ (f : Empty).elim
  map_onRelation := fun r _ ↦ by cases r <;> rfl

/-! ### Positions by index -/

/-- Position `n` of `u`. -/
def mk (n : ℕ) (h : n < u.length) : WordModel ℓ u := ⟨n, h⟩

/-- The index of a position. -/
def val (i : WordModel ℓ u) : ℕ := Fin.val (n := u.length) i

theorem val_lt (i : WordModel ℓ u) : i.val < u.length := Fin.isLt (n := u.length) i

@[simp] theorem val_mk {n : ℕ} (h : n < u.length) : (mk n h : WordModel ℓ u).val = n := rfl

theorem ext {i j : WordModel ℓ u} (h : i.val = j.val) : i = j := Fin.ext (n := u.length) h

theorem le_iff_val_le {i j : WordModel ℓ u} : i ≤ j ↔ i.val ≤ j.val := .rfl

theorem getElem?_val (i : WordModel ℓ u) : u[i.val]? = some i.label :=
  List.getElem?_eq_getElem i.val_lt

theorem label_eq_iff {i : WordModel ℓ u} {a : β} : i.label = a ↔ u[i.val]? = some a := by
  rw [getElem?_val, Option.some_inj]

/-! ### Successor and predecessor -/

/-- The successor of a position, the last position being its own. -/
def succ (i : WordModel ℓ u) : WordModel ℓ u :=
  if h : i.val + 1 < u.length then mk (i.val + 1) h else i

/-- The predecessor of a position, the first position being its own. -/
def pred (i : WordModel ℓ u) : WordModel ℓ u :=
  mk (i.val - 1) (by have := i.val_lt; omega)

theorem val_succ (i : WordModel ℓ u) :
    i.succ.val = if i.val + 1 < u.length then i.val + 1 else i.val := by
  unfold succ; split_ifs <;> rfl

@[simp] theorem val_pred (i : WordModel ℓ u) : i.pred.val = i.val - 1 := rfl

/-- The successor of a position is that of the order of positions. -/
theorem succ_eq_orderSucc (i : WordModel ℓ u) : i.succ = Order.succ i := by
  unfold succ
  split_ifs with h
  · exact (CovBy.succ_eq (Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 rfl))).symm
  · exact (Order.succ_eq_iff_isMax.2 fun j _ ↦ le_iff_val_le.2 (by have := j.val_lt; omega)).symm

/-- The predecessor of a position is that of the order of positions. -/
theorem pred_eq_orderPred (i : WordModel ℓ u) : i.pred = Order.pred i := by
  by_cases h : i.val = 0
  · rw [Order.pred_eq_iff_isMin.2 fun j _ ↦ le_iff_val_le.2 (by omega)]
    exact ext (by simp [h])
  · have hc : i.pred ⋖ i :=
      Fin.covBy_iff.2 (Nat.covBy_iff_add_one_eq.2 (by change i.val - 1 + 1 = i.val; omega))
    exact hc.pred_eq.symm

/-- One position covers another exactly when the second is the successor of the first and
differs from it. -/
theorem covBy_iff_succ_eq {i j : WordModel ℓ u} : i ⋖ j ↔ i.succ = j ∧ i ≠ j := by
  rw [succ_eq_orderSucc]
  exact ⟨fun h ↦ ⟨h.succ_eq, h.lt.ne⟩, fun ⟨h, hne⟩ ↦ h ▸ Order.covBy_succ_of_not_isMax
    fun hmax ↦ hne ((Order.succ_eq_iff_isMax.2 hmax).symm.trans h)⟩

/-- The successor ordering holds of two positions exactly when the second is the successor of the
first and differs from it. -/
theorem relMap_ord_succ_iff (h : WordOrd.succ ∈ S) (x : Fin 2 → WordModel ℓ u) :
    Structure.RelMap (L := wordLanguage P S) (WordRel.ord ⟨.succ, h⟩) x ↔
      (x 0).succ = x 1 ∧ x 0 ≠ x 1 :=
  covBy_iff_succ_eq

end WordModel

end Subregular
