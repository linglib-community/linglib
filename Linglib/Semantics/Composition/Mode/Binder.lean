module

public import Linglib.Semantics.Composition.Mode.Pointwise
public import Linglib.Semantics.Composition.Mode.EffectFree
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Core.ModelTheory.ManySorted.Comap

/-!
# Predicate abstraction as an operator on readers

Heim and Kratzer evaluate every constituent at an assignment, and abstract over an index on the
values that depend on one. Where the assignment is a datum every word reads, such a value is a
computation, sisters combine by Structured App, and abstraction is an operator on computations:
the binder of an index takes a computation to the computation of a function of the value the
assignment is modified to give the index. A grammar with abstraction maps into the grammar with
the binder, and [a derivation keeps its
value](##ManySorted.Language.withAbstraction.realize_toBinding).

## Main definitions

* `Interpreter.Binder`, `Interpreter.binding`: the binder of an index, an operator on the
  computations that read an assignment.
* `ManySorted.Language.withAbstraction.toBinding`: the map of a grammar with abstraction into
  the grammar with the binder, at the types of readers.

## Implementation notes

The binder is a rule of the grammar, as Heim and Kratzer's abstraction is, where the book has a
word of type `V β → V (e → β)` that combines by application: a word of the library's lexicon has
finitely many types. The map into the grammar with the binder is for grammars all of whose rules
take two arguments, since a rule of one argument has no mode that lifts it through reading. The
book keeps the assignments that bind traces apart from those that bind pronouns by giving them
effects of different names. Reading is here one effect for each type of datum, so the two are
apart only where traces and pronouns read data of different types, and the binder binds every
reader of its assignment's type.

## TODO

* An effect of reading for traces that is distinct from the one for pronouns at the same type of
  datum.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type} {g : Ty B} {Γ : ℕ → Ty B}

/-- The binder of an index, for assignments of type `g` and indices typed by `Γ`: from a
computation that reads an assignment, the computation of a function of the values of the index's
type. -/
inductive Binder (g : Ty B) (Γ : ℕ → Ty B) : Ty B → Ty B → Type
  /-- The binder of the index `n`. -/
  | index (n : ℕ) (b : Ty B) : Binder g Γ (.comp (.R g) b) (.comp (.R g) (Γ n ⇒ b))

/-- The binders of indices typed by `Γ`, as a language over the types. -/
@[reducible] def binding (g : Ty B) (Γ : ℕ → Ty B) : Language.{0, 0} (Ty B) :=
  .mk₂ (Binder g Γ) fun _ _ _ ↦ PEmpty

/-- The binder of an index applies to a computation that reads an assignment of type `g`, and
to nothing else. -/
def Binder.rules [DecidableEq B] (g : Ty B) (Γ : ℕ → Ty B) (n : ℕ) :
    (a : Ty B) → List (Sigma (Binder g Γ a))
  | .comp (.R i) b =>
    if h : i = g then [⟨.comp (.R g) (Γ n ⇒ b), by subst h; exact .index n b⟩] else []
  | _ => []

@[simp] theorem Binder.rules_comp [DecidableEq B] (n : ℕ) (b : Ty B) :
    Binder.rules g Γ n (.comp (.R g) b) = [⟨.comp (.R g) (Γ n ⇒ b), .index n b⟩] := by
  simp [Binder.rules]

variable {D : B → Type}

/-- The meaning of the binder of an index is that of abstraction over the index, a value that
depends on an assignment being a computation that reads one. -/
@[instance_reducible] def binding.structure (E : Assignments (g.Dom D) (Ty.Dom D) Γ) :
    (binding g Γ).Structure (Ty.Dom D) :=
  .mk₂ (fun
    | .index n b, body =>
      (abstraction.structure E).funMap (σ := .of b) (PredicateAbstraction.index n b) body) nofun

@[simp] theorem binding.funMap_index (E : Assignments (g.Dom D) (Ty.Dom D) Γ) (n : ℕ) (b : Ty B)
    (body : (Ty.comp (.R g) b).Dom D) :
    (binding.structure E).funMap (σ := .of (.comp (.R g) b)) (t := .comp (.R g) (Γ n ⇒ b))
        (Binder.index n b) body =
      fun i ↦ E.lam fun v ↦ body (E.set i n v) := rfl

end Interpreter

/-! ### The grammar relative to assignments, at the types of readers

A grammar of binary rules with abstraction maps into the effect-driven grammar with the binder,
along the map that takes a type to the type of the computations of it that read an assignment.
The map keeps the value of every derivation, so the two grammars differ only in where the
assignment is: a parameter of every domain, or a datum in the types. -/

namespace ManySorted.Language.withAbstraction

open Interpreter

variable {B : Type} {L : Language.{0, 0} (Ty B)} [L.IsBinary] {g : Ty B} {Γ : ℕ → Ty B}

/-- The map of a grammar with abstraction into the effect-driven grammar with the binder, at the
types of the computations that read an assignment: a rule is its Structured App, and abstraction
over an index is the binder of the index. -/
def toBinding (L : Language.{0, 0} (Ty B)) [L.IsBinary] (g : Ty B) (Γ : ℕ → Ty B) :
    L.withAbstraction Γ →ᴸ ((effectGrammar L).sum (binding g Γ)).comap (Ty.comp (.R g)) :=
  (LHom.ofBinary (L'' := ((effectGrammar L).sum (binding g Γ)).comap (Ty.comp (.R g)))
      fun f ↦ Language.Sum.inl (Mode.ap (.basic f))).sumElim
    (LHom.ofMk₂ (fun | .index n b => Language.Sum.inr (Binder.index n b)) nofun)

variable {D : B → Type} [M : L.Structure (Ty.Dom D)]

/-- The effect-driven grammar with the binder, at the types of readers, expands the grammar
relative to assignments: Structured App of a rule at reading is the rule at one assignment, and
the binder of an index is abstraction over it. -/
theorem toBinding_isExpansionOn (E : Assignments (g.Dom D) (Ty.Dom D) Γ) :
    (toBinding L g Γ).IsExpansionOn (withAbstraction.structure E)
      ((effectGrammar.structure.sum (binding.structure E)).comap (Ty.comp (.R g))) :=
  LHom.sumElim_isExpansionOn (LHom.ofBinary_isExpansionOn fun _ _ _ ↦ rfl)
    (LHom.ofMk₂_isExpansionOn (fun | .index _ _, _ => rfl) nofun)

/-- **Assignments are an effect, for derivations.** A derivation of a grammar of binary rules
with abstraction has, read in the effect-driven grammar with the binder at the types of readers,
the value it has relative to assignments. The value is taken in the structure pulled back along
the map of types, and the statement is of values: at reading, Structured App of a rule has the
value of any other mode that merges the two readers. -/
theorem realize_toBinding (E : Assignments (g.Dom D) (Ty.Dom D) Γ) {W : Ty B → Type}
    (ρ : ∀ {a : Ty B}, W a → g.Dom D → a.Dom D) {a : Ty B}
    (d : (L.withAbstraction Γ).Deriv W a) :
    ((toBinding L g Γ).onTerm d).realize
        ((effectGrammar.structure.sum (binding.structure E)).comap (Ty.comp (.R g))) ρ =
      d.realize (withAbstraction.structure E) ρ :=
  LHom.realize_onTerm (toBinding_isExpansionOn E) ρ d

end ManySorted.Language.withAbstraction
