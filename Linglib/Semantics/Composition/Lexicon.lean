module

public import Linglib.Semantics.Composition.Interpret

/-!
# Maps and sums of lexica

A lexicon gives each word the typed items it may be, and a second function gives the items their
values. A map of lexica renames the words and the items. Where a renamed word has exactly the
renamed items, a tree over the renamed words has the values of the tree it renames, the items
valued through the renaming. The sum of two lexica has the words and the items of both, and a
tree over the words of one has in the sum the meanings it had: none is lost and none is gained.
Lexica written in separate files therefore combine without changing what either gives its own
trees.

## Main definitions

* `Interpreter.Leaf.map`: a leaf with its item renamed.
* `Interpreter.sumLex`: the sum of two lexica.

## Main results

* `PhraseStructure.Tree.values_map`: the values of a tree over renamed words.
* `PhraseStructure.Tree.interpret_map`: its meanings by Heim and Kratzer's interpretation.
* `PhraseStructure.Tree.interpret_sumLex_inl`, `PhraseStructure.Tree.interpret_sumLex_inr`: a
  tree over the words of one lexicon has, in its sum with another, the meanings it had.

## Implementation notes

A larger lexicon over the same items keeps every value a tree had and may add more. Here the
items change too, and the statement is an equality: it needs each renamed word to have no item
beyond the renamed ones, which the sum of two lexica satisfies because its words are disjoint.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open ManySorted ManySorted.Language Interpreter

namespace PhraseStructure.Tree

variable {C L L' : Type} {T : Type} {G : Language T} {W W' D : T → Type}
  (I : Interpreter G ℕ) (M : G.Structure D) (ρ' : ∀ {a : T}, W' a → D a) (g : L → L')
  (f : ∀ {a : T}, W a → W' a) {lex : L ⊕ ℕ → List (Sigma W)}
  {lex' : L' ⊕ ℕ → List (Sigma W')}

theorem nodeValues_mapWord (h : ∀ x, lex' (x.map g id) = (lex x).map fun ⟨a, w⟩ ↦ ⟨a, f w⟩)
    (l : Label C L) (Xs : List (List (Sigma D))) :
    nodeValues I M ρ' lex' (l.mapWord g) Xs = nodeValues I M (fun x ↦ ρ' (f x)) lex l Xs := by
  match l, Xs with
  | .terminal _ w, [] =>
    simpa [nodeValues, Label.mapWord, Function.comp_def] using
      congrArg (List.map fun d : Sigma W' ↦ (⟨d.1, ρ' d.2⟩ : Sigma D)) (h (.inl w))
  | .trace n _, [] =>
    simpa [nodeValues, Label.mapWord, Function.comp_def] using
      congrArg (List.map fun d : Sigma W' ↦ (⟨d.1, ρ' d.2⟩ : Sigma D)) (h (.inr n))
  | .bind _ _, [_] | .phrase _ _, [_] | .phrase _ _, [_, _] => rfl
  | .terminal _ _, _ :: _ | .trace _ _, _ :: _ | .bind _ _, [] | .bind _ _, _ :: _ :: _
  | .phrase _ _, [] | .phrase _ _, _ :: _ :: _ :: _ => rfl

/-- Where a renamed word has exactly the renamed items, a tree over the renamed words has the
values of the tree it renames, the items valued through the renaming. -/
theorem values_map (h : ∀ x, lex' (x.map g id) = (lex x).map fun ⟨a, w⟩ ↦ ⟨a, f w⟩)
    (t : Tree C L) :
    (t.map g).values I M ρ' lex' = t.values I M (fun x ↦ ρ' (f x)) lex := by
  rw [values_eq_fold, values_eq_fold, Tree.map, RoseTree.fold_map]
  exact congrArg (RoseTree.fold · t)
    (funext fun l ↦ funext fun Xs ↦ nodeValues_mapWord I M ρ' g f h l Xs)

end PhraseStructure.Tree

namespace Interpreter

variable {B : Type} {W W' : Ty B → Type} {Γ : ℕ → Ty B} {D : B → Type}

/-- A leaf with its item renamed. A trace is itself. -/
def Leaf.map (f : ∀ {a : Ty B}, W a → W' a) : {a : Ty B} → Leaf W Γ a → Leaf W' Γ a
  | _, .word x => .word (f x)
  | _, .trace n => .trace n

theorem Leaf.val_map (ρ' : ∀ {a : Ty B}, W' a → (∀ n, (Γ n).Dom D) → a.Dom D)
    (f : ∀ {a : Ty B}, W a → W' a) {a : Ty B} (x : Leaf W Γ a) :
    Leaf.val ρ' (x.map f) = Leaf.val (fun y ↦ ρ' (f y)) x := by
  cases x <;> rfl

theorem Leaf.lex_map {Lx Lx' : Type} (g : Lx → Lx') (f : ∀ {a : Ty B}, W a → W' a)
    {lex : Lx → List (Sigma W)} {lex' : Lx' → List (Sigma W')}
    (h : ∀ w, lex' (g w) = (lex w).map fun ⟨a, x⟩ ↦ ⟨a, f x⟩) (x : Lx ⊕ ℕ) :
    Leaf.lex lex' Γ (x.map g id) =
      (Leaf.lex lex Γ x).map fun ⟨a, y⟩ ↦ (⟨a, y.map f⟩ : Σ a, Leaf W' Γ a) := by
  cases x with
  | inl w => simp [Leaf.lex, h, Leaf.map, Function.comp_def]
  | inr n => rfl

variable {Lx₁ Lx₂ : Type} {W₁ W₂ : Ty B → Type}

/-- The sum of two lexica: a word of either has its items there. -/
def sumLex (lex₁ : Lx₁ → List (Sigma W₁)) (lex₂ : Lx₂ → List (Sigma W₂)) :
    Lx₁ ⊕ Lx₂ → List (Σ a, W₁ a ⊕ W₂ a)
  | .inl w => (lex₁ w).map fun ⟨a, x⟩ ↦ ⟨a, .inl x⟩
  | .inr w => (lex₂ w).map fun ⟨a, x⟩ ↦ ⟨a, .inr x⟩

end Interpreter

namespace PhraseStructure.Tree

variable {C Lx Lx' : Type} {B : Type} {D : B → Type} {W W' : Ty B → Type}
  (L : Language.{0, 0} (Ty B)) (D) [L.LocallyFinite] [M : L.Structure (Ty.Dom D)]
  (Γ : ℕ → Ty B)

/-- Where a renamed word has exactly the renamed items, a tree over the renamed words has the
meanings of the tree it renames. -/
theorem interpret_map (ρ' : ∀ {a : Ty B}, W' a → (∀ n, (Γ n).Dom D) → a.Dom D) (g : Lx → Lx')
    (f : ∀ {a : Ty B}, W a → W' a) {lex : Lx → List (Sigma W)} {lex' : Lx' → List (Sigma W')}
    (h : ∀ w, lex' (g w) = (lex w).map fun ⟨a, x⟩ ↦ ⟨a, f x⟩) (t : Tree C Lx) :
    (t.map g).interpret L D Γ ρ' lex' = t.interpret L D Γ (fun x ↦ ρ' (f x)) lex := by
  unfold interpret
  rw [values_map _ _ (Leaf.val ρ') g (Leaf.map f) (Leaf.lex_map g f h)]
  exact congrArg (fun ρ : ∀ {a : Ty B}, Leaf W Γ a → (∀ n, (Γ n).Dom D) → a.Dom D ↦
    t.values _ _ ρ (Leaf.lex lex Γ)) (by funext a x; exact Leaf.val_map ρ' f x)

variable {Lx₁ Lx₂ : Type} {W₁ W₂ : Ty B → Type}
  (ρ₁ : ∀ {a : Ty B}, W₁ a → (∀ n, (Γ n).Dom D) → a.Dom D)
  (ρ₂ : ∀ {a : Ty B}, W₂ a → (∀ n, (Γ n).Dom D) → a.Dom D) (lex₁ : Lx₁ → List (Sigma W₁))
  (lex₂ : Lx₂ → List (Sigma W₂))

/-- A tree over the words of the first of two lexica has, in their sum, the meanings it had. -/
theorem interpret_sumLex_inl (t : Tree C Lx₁) :
    (t.map Sum.inl).interpret L D Γ (fun {a} (x : W₁ a ⊕ W₂ a) ↦ Sum.elim ρ₁ ρ₂ x)
      (sumLex lex₁ lex₂) = t.interpret L D Γ ρ₁ lex₁ :=
  interpret_map L D Γ (W' := fun a ↦ W₁ a ⊕ W₂ a) (fun x ↦ Sum.elim ρ₁ ρ₂ x) Sum.inl
    (fun x ↦ Sum.inl x) (lex := lex₁) (lex' := sumLex lex₁ lex₂) (fun _ ↦ rfl) t

/-- A tree over the words of the second of two lexica has, in their sum, the meanings it had. -/
theorem interpret_sumLex_inr (t : Tree C Lx₂) :
    (t.map Sum.inr).interpret L D Γ (fun {a} (x : W₁ a ⊕ W₂ a) ↦ Sum.elim ρ₁ ρ₂ x)
      (sumLex lex₁ lex₂) = t.interpret L D Γ ρ₂ lex₂ :=
  interpret_map L D Γ (W' := fun a ↦ W₁ a ⊕ W₂ a) (fun x ↦ Sum.elim ρ₁ ρ₂ x) Sum.inr
    (fun x ↦ Sum.inr x) (lex := lex₂) (lex' := sumLex lex₁ lex₂) (fun _ ↦ rfl) t

end PhraseStructure.Tree
