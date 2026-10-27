module

public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Aristotelian.Square
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice

/-!
# Accessibility and the strength of modals

Necessity grows stronger as accessibility shrinks:
[necessity is antitone in the accessibility relation](##box_restrict) and possibility is
monotone, so a conversational background that rules out more worlds yields a stronger necessity
modal. Necessity along the transitive closure of a relation
[is the infinite conjunction](##box_transGen_iff) $\Box p \land \Box \Box p \land \cdots$, which
is the shape of common knowledge. Along a serial relation $\Box p$, $\Box \neg p$, $\Diamond p$
and $\neg \Box p$ [form a square of opposition](##modalSquare_relations).

The standard modal systems are named by the axioms their frames validate. An S5 frame is
reflexive and Euclidean, a K45 frame transitive and Euclidean, a KD45 frame, the frame of belief,
serial, transitive and Euclidean, and a KTB frame reflexive and symmetric. An operator on
propositions is *indicial* when it is necessity along some accessibility relation. Montague's
necessity, true of a proposition true at every world, is the indicial operator of the universal
relation. Not every operator is indicial: Gallin's example is Scott's present progressive.

## Main definitions

* `ModalLogic.modalSquare`: the modal square of opposition along a relation.
* `ModalLogic.IsS5Frame`, `ModalLogic.IsKD45Frame`, `ModalLogic.IsK45Frame`,
  `ModalLogic.IsKTBFrame`: the frames of the standard systems.
* `ModalLogic.IsIndicial`: necessity along some relation.

## Implementation notes

On propositions as sets, necessity along the transitive closure is mathlib's
`SetRel.core_transGen`.

## References

* [kratzer-1981] — necessity strengthened by restricting accessibility
* [carnielli-pizzi-2008] — the modal square of opposition
* [gallin-1975] — indicial operators
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

/-- The modal square of opposition along `R`, with corners $\Box p$, $\Box \neg p$, $\Diamond p$
and $\neg \Box p$. -/
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

/-- `R` is an *S5 frame* when it is reflexive and Euclidean. -/
class IsS5Frame : Prop extends R.IsRefl, IsEuclidean R

/-- `R` is a *KD45 frame*, the frame of belief, when it is serial, transitive and Euclidean. -/
class IsKD45Frame : Prop extends IsSerial R, R.IsTrans, IsEuclidean R

/-- `R` is a *K45 frame* when it is transitive and Euclidean. -/
class IsK45Frame : Prop extends R.IsTrans, IsEuclidean R

/-- `R` is a *KTB frame* when it is reflexive and symmetric. -/
class IsKTBFrame : Prop extends R.IsRefl, R.IsSymm

theorem diamond_box_iff [IsKD45Frame R] {p : W → Prop} {w : W} :
    ◇[R] (□[R] p) w ↔ □[R] p w :=
  ⟨box_of_diamond_box, diamond_box_of_box⟩

/-! ### Indicial operators -/

/-- An operator on propositions is *indicial* when it is necessity along some accessibility
relation [gallin-1975]. -/
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
