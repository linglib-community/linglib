/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.Label.Projection
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection

/-!
# The raising head

Marcolli, Chomsky and Berwick state labeling over a partial head function and require that
function to be raising: the object Internal Merge forms is headed by the head of what it raised out
of, so the landing site of a wh-phrase beside a C is headed by C. The raising head reads this off
the finished object. Where selection decides between two merged objects the selecting one
projects; where it does not and one of the two is a term of the other, that one has raised out of
the other, which projects. A planar embedding is a total head function extending it, and
`HeadDaughter.raising` takes the daughter that projects, and the embedding's head where neither
does.

## Main definitions

* `Minimalist.SyntacticObject.RaisingProjects`: which of two merged objects projects under
  raising.
* `Minimalist.SyntacticObject.raisingState`, `Minimalist.SyntacticObject.raisingHead`: the
  selection state a raised object keeps, and the raising head of a syntactic object.
* `Minimalist.headIndex?`, `Minimalist.HeadDaughter.raising`: the head daughter of a planar
  object, the daughter that projects, and the head daughters it gives at the positions of an
  object.

## Main results

* `Minimalist.SyntacticObject.raisingHead_eq_headLeaf`: the raising head is the head the raising
  projection relation gives.
* `Minimalist.SyntacticObject.raisingHead_merge`: the raising head of a Merge is a daughter's.
* `Minimalist.exists_headIndex?_of_raisingHead`: the head daughter carries the raising head
  wherever there is one.

## Implementation notes

* A raised term is a copy, the same object merged again, so that it has raised out of its sister
  is read as containment. The object formed keeps the selection state of the sister, which a
  higher head goes on to select.
* The drawing convention puts specifiers to the left of their heads and heads to the left of their
  complements: a left leaf that selects nothing is a specifier and the right daughter heads, a left
  leaf that selects is the head, and otherwise the right daughter heads. It decides only where the
  raising head is undefined, at a phrase merged in place beside another phrase, which the labeling
  algorithm leaves unlabeled until one of the two moves on.

## TODO

* The positions at or below the maximal projection of a head occurring once carry exactly the
  terms within its projection, where the raising head is defined along the projection line.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject SelectionRule

namespace SyntacticObject

/-- The selection state of an object under raising: the product of the daughters' states where
one selects the other, and otherwise the state of the daughter the other has raised out of. -/
def raisingState : SyntacticObject TokenLeaf → SelectionRule.stack.State :=
  FreeCommMagma.elim (fun tok ↦ .of tok tok.item.sel)
    (fun l r a b ↦ if a.Projects b ∨ b.Projects a then a * b
      else if Contains l r then a else if Contains r l then b else 0)
    fun l r a b ↦ by
      have hlr : Contains l r → ¬ Contains r l := fun h h' ↦ contains_irrefl l (h.trans h')
      by_cases h : a.Projects b ∨ b.Projects a
      · have h' : b.Projects a ∨ a.Projects b := h.symm
        simp only [h, h', ↓reduceIte]
        exact mul_comm a b
      · have h' : ¬ (b.Projects a ∨ a.Projects b) := fun x ↦ h x.symm
        by_cases h1 : Contains l r
        · simp only [h, h', h1, hlr h1, ↓reduceIte]
        · simp only [h, h', h1, ↓reduceIte]

@[simp] theorem raisingState_leaf (tok : LexicalItem.Token) :
    raisingState (leaf tok) = .of tok tok.item.sel := rfl

theorem raisingState_mul (l r : SyntacticObject TokenLeaf) :
    raisingState (l * r) =
      if (raisingState l).Projects (raisingState r) ∨ (raisingState r).Projects (raisingState l)
      then raisingState l * raisingState r
      else if Contains l r then raisingState l else if Contains r l then raisingState r else 0 :=
  FreeCommMagma.elim_mul ..

/-- `x` projects over `y` under raising: it projects by selection, or `y` does not and `y` has
raised out of `x`, being a term of it. -/
def RaisingProjects (x y : SyntacticObject TokenLeaf) : Prop :=
  (raisingState x).Projects (raisingState y) ∨
    (¬ (raisingState y).Projects (raisingState x) ∧ Contains x y)

instance : DecidableRel RaisingProjects := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem RaisingProjects.asymm {x y : SyntacticObject TokenLeaf} (h : RaisingProjects x y) :
    ¬ RaisingProjects y x := by
  rintro (h' | ⟨h', hc'⟩)
  · rcases h with h | ⟨h, -⟩
    · exact h.asymm h'
    · exact h h'
  · rcases h with h | ⟨-, hc⟩
    · exact h' h
    · exact contains_irrefl x (hc.trans hc')

instance : Std.Asymm RaisingProjects := ⟨fun _ _ ↦ RaisingProjects.asymm⟩

/-- The raising head of a syntactic object, after [marcolli-chomsky-berwick-2025]'s raising head
function: the selection head where there is one, and at a landing site the head of the phrase
moved out of. -/
def raisingHead (s : SyntacticObject TokenLeaf) : Option LexicalItem.Token := (raisingState s).head

@[simp] theorem raisingHead_leaf (tok : LexicalItem.Token) :
    (leaf tok).raisingHead = some tok := rfl

/-- The raising head of a Merge is the raising head of the daughter that projects. -/
theorem raisingHead_merge_eq (l r : SyntacticObject TokenLeaf) :
    (l * r).raisingHead =
      if RaisingProjects l r then l.raisingHead
      else if RaisingProjects r l then r.raisingHead else none := by
  rw [raisingHead, raisingState_mul]
  by_cases h1 : (raisingState l).Projects (raisingState r)
  · have hlr : RaisingProjects l r := .inl h1
    simp [h1, hlr, raisingHead, State.head_mul_eq]
  · by_cases h2 : (raisingState r).Projects (raisingState l)
    · have hrl : RaisingProjects r l := .inl h2
      simp [h1, h2, hrl, hrl.asymm, raisingHead, State.head_mul_eq]
    · by_cases h3 : Contains l r
      · have hlr : RaisingProjects l r := .inr ⟨h2, h3⟩
        simp [h1, h2, h3, hlr, raisingHead]
      · have hlr : ¬ RaisingProjects l r := by rintro (h | ⟨-, h⟩) <;> contradiction
        by_cases h4 : Contains r l
        · have hrl : RaisingProjects r l := .inr ⟨h1, h4⟩
          simp [h1, h2, h3, h4, hlr, hrl, raisingHead]
        · have hrl : ¬ RaisingProjects r l := by rintro (h | ⟨-, h⟩) <;> contradiction
          simp [h1, h2, h3, h4, hlr, hrl]

/-- The raising head is the head the raising projection relation gives. -/
theorem raisingHead_eq_headLeaf : raisingHead = headLeaf RaisingProjects := by
  funext s
  induction s using FreeCommMagma.inductionOn with
  | of a => rfl
  | mul l r ihl ihr => rw [raisingHead_merge_eq, headLeaf_mul, ihl, ihr]

/-- The raising head is a head function. -/
theorem isHeadFunction_raisingHead :
    IsHeadFunction (raisingHead : SyntacticObject TokenLeaf → Option LexicalItem.Token) :=
  raisingHead_eq_headLeaf ▸ isHeadFunction_headLeaf _

/-- The raising head of a Merge is a daughter's raising head
([marcolli-chomsky-berwick-2025] Lemma 1.13.7). -/
theorem raisingHead_merge {l r : SyntacticObject TokenLeaf} {h : LexicalItem.Token}
    (hlr : (l * r).raisingHead = some h) : l.raisingHead = some h ∨ r.raisingHead = some h :=
  isHeadFunction_raisingHead.mem_or_mem hlr

@[simp] theorem raisingHead_merge_self (x : SyntacticObject TokenLeaf) :
    (x * x).raisingHead = none := by
  rw [raisingHead_eq_headLeaf, headLeaf_mul_self]

end SyntacticObject

/-! ### Head daughters -/

/-- The drawing convention makes a leaf its own head; at a Merge it takes a left leaf that selects
nothing for a specifier and looks for the head in the right daughter, takes a left leaf that
selects for the head, and otherwise looks in the right daughter. This is the head path it
assigns. -/
def conventionHeadPos? : PlanarSyntacticObject TokenLeaf → Option (List ℕ)
  | .of _ => some []
  | .mul (.of tok) r =>
      if tok.item.sel = [] then (conventionHeadPos? r).map (1 :: ·) else some [0]
  | .mul _ r => (conventionHeadPos? r).map (1 :: ·)

/-- The head daughter of a planar object is the daughter that projects under raising, and where
neither does, the first step of the drawing convention's head path. -/
def headIndex? (s : PlanarSyntacticObject TokenLeaf) : Option ℕ :=
  headDaughter SyntacticObject.RaisingProjects s <|> (conventionHeadPos? s).bind List.head?

/-- The head daughters under [marcolli-chomsky-berwick-2025]'s raising head, extended by the
drawing convention where an object has no raising head: the head daughter of the planar object at
each address, `none` off the object. -/
def HeadDaughter.raising : HeadDaughter TokenLeaf := fun t q ↦ (t.subAt? q.toList).bind headIndex?

/-- Where a Merge has a raising head, its head daughter carries it. -/
theorem exists_headIndex?_of_raisingHead {l r : PlanarSyntacticObject TokenLeaf}
    {ℓ : LexicalItem.Token} (h : (l * r).toSyntacticObject.raisingHead = some ℓ) :
    ∃ i c, headIndex? (l * r) = some i ∧ (l * r).daughters[i]? = some c ∧
      c.toSyntacticObject.raisingHead = some ℓ := by
  have hm : (l.toSyntacticObject * r.toSyntacticObject).raisingHead = some ℓ := h
  rw [raisingHead_merge_eq] at hm
  split_ifs at hm with h1 h2
  · exact ⟨0, l, by simp [headIndex?, headDaughter_mul, h1], rfl, hm⟩
  · exact ⟨1, r, by simp [headIndex?, headDaughter_mul, h1, h2], rfl, hm⟩

end Minimalist
