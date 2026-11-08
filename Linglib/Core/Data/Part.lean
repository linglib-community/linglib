/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Part

/-!
# Values of partial values

Mirror of `Mathlib/Data/Part.lean`: the domain and the value of `Part.restrict p o h`, the partial
value `o` defined exactly where `p` holds, and the value of a `Part.bind`, as `simp` lemmas. The
value of a restriction does not depend on the proof of `p`, so `simp` rewrites under it, where it
cannot under an anonymous `⟨p, fun h ↦ …⟩`. [UPSTREAM]
-/

@[expose] public section

namespace Part

variable {α : Type*} {p : Prop} {o : Part α} {H : p → o.Dom}

@[simp] theorem restrict_dom : (restrict p o H).Dom ↔ p := .rfl

@[simp] theorem get_restrict (h : p) : (restrict p o H).get h = o.get (H h) := rfl

@[simp] theorem get_bind {β : Type*} {f : Part α} {g : α → Part β} (h : (f.bind g).Dom) :
    (f.bind g).get h = (g (f.get (bind_dom.1 h).fst)).get (bind_dom.1 h).snd :=
  rfl

end Part
