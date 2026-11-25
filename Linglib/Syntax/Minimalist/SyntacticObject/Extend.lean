/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Extending a phrase by a sequence of heads

Given a phrase `t` of category `below` and categories `cs`, listed from the lowest,
`t.extend below id spec cs` is the tree in which a head of each category merges in turn over what
is built so far, and the phrase `spec i`, when there is one, then merges as the specifier of the
`i`th head. The heads are `headTokens below id cs`: each selects the category beneath it, and they
are numbered from `id`. Without specifiers the tree is the heads merged one after another
(`extend_none`), and extending by one more head merges that head and its specifier over the
extension by the others (`extend_concat`).
-/

@[expose] public section

namespace Minimalist

variable {below c : Cat} {id : ℕ} {cs ds : List Cat}

/-- The heads of the categories `cs`, from the lowest: the first selects `below` and each other one
the category before it, and they are numbered from `id`. -/
def headTokens (below : Cat) (id : ℕ) : List Cat → List LexicalItem.Token
  | [] => []
  | c :: cs => ⟨.of c [below], id⟩ :: headTokens c (id + 1) cs

@[simp] theorem headTokens_nil : headTokens below id [] = [] := rfl

@[simp] theorem headTokens_cons :
    headTokens below id (c :: cs) = ⟨.of c [below], id⟩ :: headTokens c (id + 1) cs :=
  rfl

@[simp] theorem length_headTokens (cs : List Cat) :
    (headTokens below id cs).length = cs.length := by
  induction cs generalizing below id with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem headTokens_append (cs : List Cat) :
    headTokens below id (cs ++ ds) =
      headTokens below id cs ++ headTokens (cs.getLast?.getD below) (id + cs.length) ds := by
  induction cs generalizing below id with
  | nil => simp
  | cons c cs ih => simp [ih, List.getLast?_cons, Nat.add_assoc, Nat.add_comm 1]

namespace PlanarSyntacticObject

variable {t : PlanarSyntacticObject TokenLeaf} {spec : ℕ → Option (PlanarSyntacticObject TokenLeaf)}

/-- The phrase `t`, of category `below`, extended by heads of the categories `cs` from the lowest:
each head merges over what is built so far, and `spec i`, when present, merges as the specifier of
the `i`th head. -/
def extend (t : PlanarSyntacticObject TokenLeaf) (below : Cat) (id : ℕ)
    (spec : ℕ → Option (PlanarSyntacticObject TokenLeaf)) : List Cat → PlanarSyntacticObject
        TokenLeaf
  | [] => t
  | c :: cs =>
    let hp : PlanarSyntacticObject TokenLeaf := .leaf ⟨.of c [below], id⟩ * t
    extend ((spec 0).elim hp (· * hp)) c (id + 1) (fun i ↦ spec (i + 1)) cs

@[simp] theorem extend_nil : t.extend below id spec [] = t := rfl

@[simp] theorem extend_cons :
    t.extend below id spec (c :: cs) =
      extend ((spec 0).elim (.leaf ⟨.of c [below], id⟩ * t) (· * (.leaf ⟨.of c [below], id⟩ * t)))
        c (id + 1) (fun i ↦ spec (i + 1)) cs :=
  rfl

theorem extend_append (cs : List Cat) :
    t.extend below id spec (cs ++ ds) =
      (t.extend below id spec cs).extend (cs.getLast?.getD below) (id + cs.length)
        (fun i ↦ spec (cs.length + i)) ds := by
  induction cs generalizing t below id spec with
  | nil => simp
  | cons c cs ih =>
    simp [ih, List.getLast?_cons, Nat.add_assoc, Nat.add_comm 1]

/-- Extending by one more head merges that head, and then its specifier, over the extension by
the heads below it. -/
theorem extend_concat (cs : List Cat) (c : Cat) :
    t.extend below id spec (cs ++ [c]) =
      let hp : PlanarSyntacticObject TokenLeaf :=
        .leaf ⟨.of c [cs.getLast?.getD below], id + cs.length⟩ * t.extend below id spec cs
      (spec cs.length).elim hp (· * hp) := by
  rw [extend_append]; simp

/-- Without specifiers, the extension merges the heads one after another. -/
theorem extend_none (cs : List Cat) :
    t.extend below id (fun _ ↦ none) cs =
      (headTokens below id cs).foldl (fun t h ↦ .leaf h * t) t := by
  induction cs generalizing t below id with
  | nil => rfl
  | cons c cs ih => simp [ih]

end PlanarSyntacticObject

end Minimalist
