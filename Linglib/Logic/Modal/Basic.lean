module

public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Aristotelian.Square
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice

/-!
# Modal logic over accessibility relations

This file proves the order theory of `□` and `◇` beyond their Galois connection
(`diamond_box_gc`): antitonicity in the relation (conversational backgrounds
strengthen necessity by shrinking accessibility), necessity along the transitive closure as the
infinite conjunction of iterated necessity, and the modal square of opposition. It also defines
the bundled frame classes `IsS5Frame`, `IsKD45Frame`, `IsK45Frame`, `IsKTBFrame`, and the
indicial operators, with Montague's S5 `□`/`◇` as the universal-accessibility case
`R = .univ`. On propositions as sets necessity along the transitive closure is mathlib's
`SetRel.core_transGen`.

## References

* [kratzer-1981] — necessity strengthened by restricting accessibility
* [carnielli-pizzi-2008] — the modal square of opposition
* [gallin-1975] — the indicial operator hierarchy
* [dowty-wall-peters-1981] — Montague's S5 operators
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W : Type*}

/-! ### Modal square of opposition -/

variable {R : SetRel W W} {p : W → Prop}

theorem box_disjoint_compl [IsSerial R] : Disjoint (□[R] p) (□[R] pᶜ) :=
  Pi.disjoint_iff.mpr fun _ ↦ Prop.disjoint_iff.mpr fun ⟨hp, hnp⟩ ↦
    let ⟨v, hwv, hv⟩ := box_D hp; hnp v hwv hv

theorem compl_box_compl (R : SetRel W W) (p : W → Prop) : (□[R] pᶜ)ᶜ = ◇[R] p := by
  funext w
  simp [not_box]

/-- The **modal square of opposition** over `R`: `A = □p`, `E = □¬p`, `I = ◇p`, `O = ¬□p`. -/
def modalSquare (R : SetRel W W) (p : W → Prop) : Aristotelian.Square (W → Prop) where
  A := □[R] p
  E := □[R] pᶜ
  I := ◇[R] p
  O := (□[R] p)ᶜ

theorem modalSquare_relations (R : SetRel W W) [IsSerial R] (p : W → Prop) :
    Aristotelian.SquareRelations (modalSquare R p) :=
  .of_disjoint (compl_box_compl R p).symm rfl box_disjoint_compl

variable (R) {q : W → Prop}

/-! ### Accessibility restriction -/

theorem box_restrict (p : W → Prop) : Antitone fun R : SetRel W W ↦ □[R] p :=
  fun _ _ h _ hb v hwv ↦ hb v (h hwv)

theorem diamond_restrict (p : W → Prop) : Monotone fun R : SetRel W W ↦ ◇[R] p :=
  fun _ _ h _ ⟨v, hwv, hpv⟩ ↦ ⟨v, h hwv, hpv⟩

/-! ### Transitive closure

Necessity along the transitive closure of `R` is the infinite conjunction of iterated
necessity along `R`: `□[R⁺] p = □[R] p ∧ □[R] (□[R] p) ∧ ⋯`. -/

theorem box_iterate_succ_of_box_transGen :
    ∀ (n : ℕ) {p : W → Prop} {w : W}, □[R.transGen] p w → (□[R])^[n + 1] p w
  | 0, _, _, h => fun v hv ↦ h v (.single hv)
  | n + 1, _, _, h => by
    rw [Function.iterate_succ_apply']
    exact fun v hv ↦
      box_iterate_succ_of_box_transGen n fun u hu ↦ h u (Relation.TransGen.head hv hu)

theorem exists_box_iterate_imp_of_transGen {w v : W} (h : Relation.TransGen (· ~[R] ·) w v) :
    ∃ n, ∀ q : W → Prop, (□[R])^[n + 1] q w → q v := by
  induction h with
  | single hwv => exact ⟨0, fun _ hq ↦ hq _ hwv⟩
  | tail _ huv ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun q hq ↦ hn (□[R] q) (by rwa [Function.iterate_succ_apply] at hq) _ huv⟩

theorem box_transGen_iff {p : W → Prop} {w : W} :
    □[R.transGen] p w ↔ ∀ n, (□[R])^[n + 1] p w :=
  ⟨fun h n ↦ box_iterate_succ_of_box_transGen R n h,
   fun h _ hv ↦ let ⟨n, hn⟩ := exists_box_iterate_imp_of_transGen R (mem_transGen.1 hv); hn p (h n)⟩

/-! ### Bundled frame classes -/

/-- `R` is an **S5 frame** if it is reflexive and Euclidean. -/
class IsS5Frame : Prop extends R.IsRefl, IsEuclidean R

/-- `R` is a **KD45 frame**, the doxastic frame, if it is serial, transitive, and Euclidean. -/
class IsKD45Frame : Prop extends IsSerial R, R.IsTrans, IsEuclidean R

/-- `R` is a **K45 frame** if it is transitive and Euclidean. -/
class IsK45Frame : Prop extends R.IsTrans, IsEuclidean R

/-- `R` is a **KTB frame** if it is reflexive and symmetric. -/
class IsKTBFrame : Prop extends R.IsRefl, R.IsSymm

theorem diamond_box_iff [IsKD45Frame R] {p : W → Prop} {w : W} :
    ◇[R] (□[R] p) w ↔ □[R] p w :=
  ⟨box_of_diamond_box, diamond_box_of_box⟩

/-! ### The Gallin hierarchy

Operators `(W → Prop) → W → Prop` form a three-level hierarchy ([gallin-1975]): arbitrary
operators, the **indicial** (Kripke-definable) ones, `□[R]` for some accessibility relation,
and S5, the indicial case `R = .univ`. Tense and other non-Kripke operators live outside
`IsIndicial`. -/

/-- An operator on world-propositions is **indicial** (Kripke-definable) if it is `□[R]` for
some accessibility relation `R`. -/
def IsIndicial (N : (W → Prop) → W → Prop) : Prop := ∃ R : SetRel W W, N = □[R]

theorem box_isIndicial : IsIndicial □[R] := ⟨R, rfl⟩

/-! ### Decidability over finite worlds -/

instance {W' : Type*} [Fintype W] (R : SetRel W' W) (p : W → Prop) (w : W')
    [∀ v, Decidable (w ~[R] v)] [DecidablePred p] : Decidable (□[R] p w) :=
  inferInstanceAs (Decidable (∀ v, w ~[R] v → p v))

instance {W' : Type*} [Fintype W] (R : SetRel W' W) (p : W → Prop) (w : W')
    [∀ v, Decidable (w ~[R] v)] [DecidablePred p] : Decidable (◇[R] p w) :=
  inferInstanceAs (Decidable (∃ v, w ~[R] v ∧ p v))

end ModalLogic
