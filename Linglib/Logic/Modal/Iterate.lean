module

public import Linglib.Logic.Modal.Basic

/-!
# Necessity along the transitive closure

Necessity along the transitive closure of a relation `R` is the infinite conjunction of iterated
necessity along `R`, $\Box p \land \Box \Box p \land \cdots$. This is the shape of common
knowledge: what everyone knows, and everyone knows that everyone knows, and so on.

## Main results

* `ModalLogic.box_transGen_iff`: `□[R.transGen] p w` holds iff `(□[R])^[n + 1] p w` for every `n`.

## Implementation notes

On propositions as sets this is `SetRel.core_transGen`.

## References

* [fagin-halpern-moses-vardi-1995]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W : Type*} (R : SetRel W W)

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

end ModalLogic
