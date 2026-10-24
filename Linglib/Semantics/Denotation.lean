module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Util.Superscript

/-!
# Denotation

This file defines `Denotes`, the class of objects that have a denotation, and the
bracket notation `⟦x⟧` for it, Heim and Kratzer's. A lexical item, a reading, or a whole
sentence denotes in whatever domain its instance names, so the class gives the library one name
for the map from a semantic object to its meaning, whether that map is compositional or
stipulated per object. An object that denotes in the Montague type system denotes in
`Montague.Denotation E W M S`, a semantic type paired with a value in its domain, and is
thereby a terminal for the composition engine.

## Implementation notes

The class has one field, like `FunLike`: the parameters an interpretation is relativized to,
the model, context, index and assignment of Montague and of Kaplan, are not slots of
the class but Reader arguments of the domain `D`, in that order, so a Kaplanian expression
denotes a `Kaplan.Character`, an assignment-sensitive one an `Assignment E → _`, and an
intension a `W → _`. Instance resolution requires every type parameter of `D` to be fixed by
`α`. An object interpreted relative to data its type does not mention denotes the family over
that data, `D` quantifying over the model's types with the model's data as Reader arguments, as
a lexical quantifier denotes a `Quantifier.GQ.Family` and an article its readings on every model;
a tree relative to a lexicon keeps an explicit interpretation function (`Composition.Tree.interp`,
mathlib's `Term.realize`) and gains an instance once its type is indexed by that data.

## Main definitions

* `Denotes α D`: every object of `α` denotes in `D`; `⟦x⟧` is `Denotes.denote x`.
* `⟦x⟧ᴹ`, in the scope `Denotes.Superscript`: the denotation of `x` at the parameter `M`.

## References

* [heim-kratzer-1998]
* [montague-1973]
* [kaplan-1989]
-/

@[expose] public section

/-- `Denotes α D` says that every object of `α` denotes in `D`. -/
class Denotes (α : Type*) (D : outParam Type*) where
  /-- The denotation of `x`, written `⟦x⟧`. -/
  denote : α → D

namespace Denotes

/-- `⟦x⟧` is the denotation of `x`. -/
scoped notation:max (priority := high) "⟦" x "⟧" => Denotes.denote x

namespace Superscript

/-- `⟦x⟧ᴹ` is the denotation of `x` at the parameter `M`, the first Reader argument written
as a superscript. The parameter is a name in superscript letters. The notation has its own
scope because it would otherwise capture a superscript operator applied to a denotation, such
as the complement `⟦x⟧ᶜ`. -/
scoped macro:max "⟦" x:term "⟧" noWs m:superscript(term) : term =>
  `(⟦$x⟧ $(⟨m.raw[0]⟩))

end Superscript

end Denotes
