/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Functor
import all Init.Control.State  -- for unfolding `StateT.orElse`

/-!
# The set monad under the state and reader transformers

With `Set.monad` as the monad, a computation of `StateT σ Set α` run at an input state is a set of
value–state pairs, and one of `ReaderT σ Set α` a set of values. This file evaluates `pure`,
`<$>`, `>>=`, `<*>` and `<|>` of both transformers at an input, as a singleton, an image, an
indexed union and a union, and identifies a `StateT σ Set α` computation with a family of
relations on `σ` indexed by `α`.

## Main definitions

* `StateT.rel`: the relation on states a computation induces at a value.
* `StateT.relEquiv`: `StateT σ Set α ≃ (α → SetRel σ σ)`.

## Main statements

* `Set.stateT_bind_apply`: `(m >>= f) s = ⋃ q ∈ m s, f q.1 q.2`.
* `Set.mk_mem_stateT_map_seq`: `f <$> m <*> n` runs `m` and then `n` from its output state.
* `StateT.rel_bind`: `(m >>= f).rel b = ⋃ a, m.rel a ○ (f a).rel b`.
* `StateT.rel_bind_subset`, `StateT.rel_map_seq_subset`: a transitive relation containing every
  step of the parts contains every step of the whole.

## Implementation notes

The statements are about the local instance `Set.monad`, so they apply wherever a file enables it.
A computation is applied to its input directly, `m s`, as the files using these lemmas define
their computations by `fun s ↦ _`; core's `StateT.run_bind` and its siblings are stated for
`m.run s` and do not fire on that form.

`pure`, `>>=` and `<|>` are evaluated as equations of sets. `<$>` and `<*>` are evaluated by
membership, `r ∈ (f <$> m) s ↔ ∃ q ∈ m s, r = (f q.1, q.2)`, with the equation oriented as in
`Set.mem_singleton_iff`, so that `f <$> m` and `m >>= fun a ↦ pure (f a)` have the same `simp`
normal form; `Set.mem_image` has the opposite orientation.
-/

@[expose] public section

attribute [local instance] Set.monad

universe u

namespace Set

/-! ### `StateT σ Set` -/

section StateT

variable {σ α β γ : Type u}

@[simp] theorem stateT_pure_apply (a : α) (s : σ) : (pure a : StateT σ Set α) s = {(a, s)} := rfl

@[simp] theorem stateT_bind_apply (m : StateT σ Set α) (f : α → StateT σ Set β) (s : σ) :
    (m >>= f) s = ⋃ q ∈ m s, f q.1 q.2 := by
  show StateT.bind m f s = _
  simp [StateT.bind, Set.bind_def]

@[simp] theorem stateT_orElse_apply (m n : StateT σ Set α) (s : σ) :
    (m <|> n) s = m s ∪ n s := by
  show StateT.orElse m (fun _ ↦ n) s = _
  simp [StateT.orElse, Set.orElse_def]

theorem mem_stateT_bind {m : StateT σ Set α} {f : α → StateT σ Set β} {s : σ} {r : β × σ} :
    r ∈ (m >>= f) s ↔ ∃ q ∈ m s, r ∈ f q.1 q.2 := by simp

@[simp] theorem mem_stateT_map (f : α → β) (m : StateT σ Set α) (s : σ) (r : β × σ) :
    r ∈ (f <$> m) s ↔ ∃ q ∈ m s, r = (f q.1, q.2) := by
  simp [← bind_pure_comp]

@[simp] theorem mem_stateT_seq (m : StateT σ Set (α → β)) (n : StateT σ Set α) (s : σ)
    (r : β × σ) : r ∈ (m <*> n) s ↔ ∃ q ∈ m s, ∃ q' ∈ n q.2, r = (q.1 q'.1, q'.2) := by
  simp [seq_eq_bind_map]

theorem mk_mem_stateT_map {f : α → β} {m : StateT σ Set α} {s s' : σ} {b : β} :
    (b, s') ∈ (f <$> m) s ↔ ∃ a, (a, s') ∈ m s ∧ b = f a := by
  simp only [mem_stateT_map, Prod.mk.injEq]
  exact ⟨fun ⟨⟨a, t⟩, hm, hb, ht⟩ ↦ ⟨a, ht ▸ hm, hb⟩, fun ⟨a, hm, hb⟩ ↦ ⟨(a, s'), hm, hb, rfl⟩⟩

theorem mk_mem_stateT_map_seq {f : α → β → γ} {m : StateT σ Set α} {n : StateT σ Set β}
    {s s'' : σ} {c : γ} :
    (c, s'') ∈ (f <$> m <*> n) s ↔ ∃ a s', (a, s') ∈ m s ∧ ∃ b, (b, s'') ∈ n s' ∧ c = f a b := by
  simp only [mem_stateT_seq, mem_stateT_map]
  constructor
  · rintro ⟨_, ⟨⟨a, s'⟩, hm, rfl⟩, ⟨b, _⟩, hn, ⟨⟩⟩
    exact ⟨a, s', hm, b, hn, rfl⟩
  · rintro ⟨a, s', hm, b, hn, rfl⟩
    exact ⟨(f a, s'), ⟨(a, s'), hm, rfl⟩, (b, s''), hn, rfl⟩

end StateT

/-! ### `ReaderT σ Set` -/

section ReaderT

variable {σ α β : Type u}

@[simp] theorem readerT_pure_apply (a : α) (s : σ) : (pure a : ReaderT σ Set α) s = {a} := rfl

@[simp] theorem readerT_bind_apply (m : ReaderT σ Set α) (f : α → ReaderT σ Set β) (s : σ) :
    (m >>= f) s = ⋃ x ∈ m s, f x s := by
  show ReaderT.bind m f s = _
  simp [ReaderT.bind, Set.bind_def]

theorem mem_readerT_bind {m : ReaderT σ Set α} {f : α → ReaderT σ Set β} {s : σ} {r : β} :
    r ∈ (m >>= f) s ↔ ∃ x ∈ m s, r ∈ f x s := by simp

@[simp] theorem mem_readerT_map (f : α → β) (m : ReaderT σ Set α) (s : σ) (r : β) :
    r ∈ (f <$> m) s ↔ ∃ x ∈ m s, r = f x := by
  simp [← bind_pure_comp]

end ReaderT

end Set

/-! ### Graded relations -/

namespace StateT

open scoped SetRel

variable {σ α β γ : Type u}

/-- The relation `m` induces at the value `a`, from each state to the states `m` reaches from it
with the value `a`. -/
def rel (m : StateT σ Set α) (a : α) : SetRel σ σ := {p | (a, p.2) ∈ m p.1}

@[simp] theorem mem_rel {m : StateT σ Set α} {a : α} {s s' : σ} :
    s ~[m.rel a] s' ↔ (a, s') ∈ m s := Iff.rfl

/-- A `StateT σ Set α` computation is the family of relations it induces at its values. -/
def relEquiv : StateT σ Set α ≃ (α → SetRel σ σ) where
  toFun := rel
  invFun R s := {q | s ~[R q.1] q.2}
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_relEquiv : ⇑(relEquiv : StateT σ Set α ≃ (α → SetRel σ σ)) = rel := rfl

@[simp] theorem mem_relEquiv_symm_apply {R : α → SetRel σ σ} {s : σ} {q : α × σ} :
    q ∈ relEquiv.symm R s ↔ s ~[R q.1] q.2 := Iff.rfl

theorem rel_pure_self (a : α) : (pure a : StateT σ Set α).rel a = SetRel.id := by
  ext ⟨s, s'⟩
  simp [eq_comm]

theorem rel_pure_of_ne {a b : α} (h : a ≠ b) : (pure a : StateT σ Set α).rel b = ∅ := by
  ext ⟨s, s'⟩
  simp [Ne.symm h]

theorem rel_bind (m : StateT σ Set α) (f : α → StateT σ Set β) (b : β) :
    (m >>= f).rel b = ⋃ a, m.rel a ○ (f a).rel b := by
  ext ⟨s, s'⟩
  simp only [mem_rel, Set.mem_stateT_bind, Set.mem_iUnion, SetRel.mem_comp]
  exact ⟨fun ⟨⟨a, t⟩, hm, hf⟩ ↦ ⟨a, t, hm, hf⟩, fun ⟨a, t, hm, hf⟩ ↦ ⟨(a, t), hm, hf⟩⟩

theorem rel_map (f : α → β) (m : StateT σ Set α) (b : β) :
    (f <$> m).rel b = ⋃ (a) (_ : f a = b), m.rel a := by
  ext ⟨s, s'⟩
  simp only [mem_rel, Set.mk_mem_stateT_map, Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨a, hm, hb⟩ ↦ ⟨a, hb.symm, hm⟩, fun ⟨a, hb, hm⟩ ↦ ⟨a, hm, hb.symm⟩⟩

theorem rel_map_seq (f : α → β → γ) (m : StateT σ Set α) (n : StateT σ Set β) (c : γ) :
    (f <$> m <*> n).rel c = ⋃ (a) (b) (_ : f a b = c), m.rel a ○ n.rel b := by
  ext ⟨s, s'⟩
  simp only [mem_rel, Set.mk_mem_stateT_map_seq, Set.mem_iUnion, SetRel.mem_comp, exists_prop]
  exact ⟨fun ⟨a, t, hm, b, hn, hc⟩ ↦ ⟨a, b, hc.symm, t, hm, hn⟩,
    fun ⟨a, b, hc, t, hm, hn⟩ ↦ ⟨a, t, hm, b, hn, hc.symm⟩⟩

variable {R : SetRel σ σ}

theorem rel_pure_subset [R.IsRefl] (a b : α) : (pure a : StateT σ Set α).rel b ⊆ R := by
  obtain rfl | h := eq_or_ne a b
  · rw [rel_pure_self]; exact SetRel.id_subset
  · rw [rel_pure_of_ne h]; exact Set.empty_subset _

theorem rel_bind_subset [R.IsTrans] {m : StateT σ Set α} {f : α → StateT σ Set β}
    (hm : ∀ a, m.rel a ⊆ R) (hf : ∀ a b, (f a).rel b ⊆ R) (b : β) : (m >>= f).rel b ⊆ R := by
  rw [rel_bind]
  exact Set.iUnion_subset fun a ↦ (SetRel.comp_subset_comp (hm a) (hf a b)).trans
    SetRel.comp_subset_self

theorem rel_map_subset {m : StateT σ Set α} (hm : ∀ a, m.rel a ⊆ R) (f : α → β) (b : β) :
    (f <$> m).rel b ⊆ R := by
  rw [rel_map]
  exact Set.iUnion₂_subset fun a _ ↦ hm a

theorem rel_map_seq_subset [R.IsTrans] {m : StateT σ Set α} {n : StateT σ Set β}
    (hm : ∀ a, m.rel a ⊆ R) (hn : ∀ b, n.rel b ⊆ R) (f : α → β → γ) (c : γ) :
    (f <$> m <*> n).rel c ⊆ R := by
  rw [rel_map_seq]
  exact Set.iUnion_subset fun a ↦ Set.iUnion_subset fun b ↦ Set.iUnion_subset fun _ ↦
    (SetRel.comp_subset_comp (hm a) (hn b)).trans SetRel.comp_subset_self

end StateT
