/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar

/-!
# A partial fold simulating a total one

When every successful step of a partial step function `f` maps, under a projection `π`, to the
step of a total function `g`, every successful `foldlM f` maps to the `foldl g` from the projected
start. [UPSTREAM] candidate for `Init/Data/List/Monadic.lean`.

## Main results

* `List.foldl_eq_of_foldlM_eq_some`: a successful partial fold projects to the total fold.
* `List.map_foldlM`: a partial fold whose steps commute with a projection maps to the projected
  partial fold.
-/

@[expose] public section

namespace List

variable {α β γ : Type*} {f : β → α → Option β} {g : γ → α → γ} {π : β → γ}

theorem foldl_eq_of_foldlM_eq_some (hf : ∀ b a b', f b a = some b' → π b' = g (π b) a) :
    ∀ {l : List α} {b b' : β}, l.foldlM f b = some b' → π b' = l.foldl g (π b)
  | [], _, _, h => by obtain rfl := Option.some.inj h; rfl
  | a :: l, b, _, h => by
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
    rw [foldl_cons, ← hf b a c hc]
    exact foldl_eq_of_foldlM_eq_some hf h

theorem map_foldlM {f : β → α → Option β} {g : γ → α → Option γ}
    (hf : ∀ b a, (f b a).map π = g (π b) a) :
    ∀ (l : List α) (b : β), (l.foldlM f b).map π = l.foldlM g (π b)
  | [], _ => rfl
  | a :: l, b => by
    rw [foldlM_cons, foldlM_cons, ← hf b a]
    cases f b a with
    | none => rfl
    | some b' => exact map_foldlM hf l b'

end List
