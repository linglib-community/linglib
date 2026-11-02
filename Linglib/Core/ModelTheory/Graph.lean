module

public import Mathlib.Logic.Equiv.Pairwise
public import Mathlib.ModelTheory.Graph
public import Mathlib.Tactic.FinCases
public import Linglib.Core.ModelTheory.Lindstrom

/-!
# Relations as structures in the language of graphs

`[UPSTREAM]` candidate. Mathlib makes a simple graph a structure in the language of graphs; any
binary relation is one as well, with its pairs as the adjacency relation (`graphStructure`). A
Lindström quantifier over the language of graphs, a quantifier of type `⟨2⟩`, is then a graph
property, an isomorphism-invariant class of binary relations, built from any property of
relations that relabelling along a bijection preserves (`LindstromQuantifier.ofGraphProperty`).
Its relativization to a set `A` asks it of `A` with the relation restricted to `A`
(`inducedGraph`).

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

universe u

namespace FirstOrder.Language

open Structure

variable {M N : Type u}

/-- The structure in the language of graphs whose adjacency relation is `r`. -/
@[instance_reducible]
def graphStructure (r : M → M → Prop) : Language.graph.Structure M where
  RelMap | .adj => fun x ↦ r (x 0) (x 1)

@[simp] theorem relMap_graphStructure (r : M → M → Prop) (x y : M) :
    @RelMap _ M (graphStructure r) 2 adj ![x, y] ↔ r x y := Iff.rfl

/-- A bijection carrying `r` to `s` is an isomorphism of the structures they define. -/
def graphStructureEquiv {r : M → M → Prop} {s : N → N → Prop} (e : M ≃ N)
    (h : ∀ x y, s (e x) (e y) ↔ r x y) :
    @Language.Equiv Language.graph M N (graphStructure r) (graphStructure s) :=
  @Language.Equiv.mk _ M N (graphStructure r) (graphStructure s) e
    (fun f ↦ isEmptyElim f) (fun | .adj => fun x ↦ h (x 0) (x 1))

/-- The set `A` with `r` restricted to it, as a structure in the language of graphs. -/
abbrev inducedGraph (r : M → M → Prop) (A : Set M) :
    CategoryTheory.Bundled.{u} Language.graph.Structure :=
  ⟨A, graphStructure fun a b : A ↦ r a b⟩

namespace LindstromQuantifier

/-- The type `⟨2⟩` quantifier of a graph property `P`, holding of a structure whose adjacency
relation has `P`; relabelling along a bijection preserves `P`. -/
def ofGraphProperty (P : ∀ {M : Type u}, (M → M → Prop) → Prop)
    (hP : ∀ {M N : Type u} (e : M ≃ N) (s : N → N → Prop), P (fun x y ↦ s (e x) (e y)) ↔ P s) :
    LindstromQuantifier.{0, 0, u} Language.graph :=
  {q | q.liftOn (fun M ↦ P fun x y : M ↦ RelMap adj ![x, y]) fun M N ⟨e⟩ ↦ propext <| by
    have hv (x y : M) : ⇑e ∘ ![x, y] = ![e x, e y] := by
      ext i
      fin_cases i <;> rfl
    have : (fun x y : M ↦ RelMap adj ![x, y]) = fun x y ↦ RelMap adj ![e x, e y] :=
      funext₂ fun x y ↦ propext (by rw [← hv]; exact (e.map_rel adj ![x, y]).symm)
    show @P M _ ↔ @P N _
    rw [this]
    exact hP e.toEquiv fun x y : N ↦ RelMap adj ![x, y]}

end LindstromQuantifier

end FirstOrder.Language
