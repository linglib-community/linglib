module

public import Linglib.Semantics.Composition.Constituency
public import Mathlib.Data.List.Sigma

/-!
# The value of a tree with one derivation

An interpreter gives a tree a list of typed values, one for each derivation it admits. Where it
admits exactly one derivation of a type, the tree has a value at that type, and where the grammar
admits at most one rule at a node and a word is at most one item, [a value of the tree is its
value](##PhraseStructure.Tree.value?_eq_some_of_mem).

## Main definitions

* `PhraseStructure.Tree.value?`: the value of a tree at a type, where it has exactly one
  derivation of the type.
-/

@[expose] public section

namespace PhraseStructure.Tree

open ManySorted ManySorted.Language Interpreter

variable {C L : Type} {T : Type} [DecidableEq T] {G : Language T} {W D : T → Type}

/-- The value of a tree at a type, if the interpreter admits exactly one derivation of that type
over it. -/
def value? (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Sigma W)) (t : Tree C L) (a : T) : Option (D a) :=
  match (t.values I M ρ lex).lookupAll a with
  | [x] => some x
  | _ => none

variable {I : Interpreter G ℕ} {M : G.Structure D} {ρ : ∀ {a : T}, W a → D a}
  {lex : L ⊕ ℕ → List (Sigma W)} {t : Tree C L} {a : T} {x : D a}

theorem value?_eq_some_iff :
    t.value? I M ρ lex a = some x ↔ (t.values I M ρ lex).lookupAll a = [x] := by
  unfold value?
  split
  · next h => simp [h]
  · next h => simpa using fun h' ↦ h x h'

theorem value?_eq_some_of_values_eq (h : t.values I M ρ lex = [⟨a, x⟩]) :
    t.value? I M ρ lex a = some x :=
  value?_eq_some_iff.2 (by rw [h, List.lookupAll_cons_eq, List.lookupAll_nil])

/-- Where a node admits at most one rule for given daughters and a word is at most one item, a
value of a tree is its value. -/
theorem value?_eq_some_of_mem (hu : ∀ n a, (I.bind n a).length ≤ 1)
    (hb : ∀ a b, (I.binary a b).length ≤ 1) (hl : ∀ x, (lex x).length ≤ 1)
    (h : (⟨a, x⟩ : Sigma D) ∈ t.values I M ρ lex) : t.value? I M ρ lex a = some x := by
  have hlen := length_values_le_one (M := M) (ρ := ρ) hu hb hl t
  refine value?_eq_some_of_values_eq ?_
  generalize t.values I M ρ lex = vs at h hlen
  match vs, h, hlen with
  | [d], hd, _ => rw [List.mem_singleton.1 hd]

end PhraseStructure.Tree
