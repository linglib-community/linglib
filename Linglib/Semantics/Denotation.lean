module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Util.Superscript

/-!
# Denotation

This file defines the bracket notation `⟦x⟧` for the denotation of `x`, Heim and Kratzer's, and
the class that gives a type of objects its denotations. A lexical entry, a reading or a sentence
denotes in the domain its instance names: a tense denotes a relation between times, and a
determiner the set of the quantifiers it may be.

## Main definitions

* `Denotes α D`: every object of `α` denotes in `D`.

## Notation

* `⟦x⟧`, in the scope `Denotes`: the denotation of `x`.
* `⟦x⟧ᴹ`, in the scope `Denotes.Superscript`: the denotation of `x` at the parameter `M`.

## Implementation notes

The class is a notation class, with one field and no law. A class of functions with an injective
coercion carries extensionality, and denotation is not injective, since two expressions may mean
the same.

The parameters an interpretation is relativized to, the model, context, index and assignment of
Montague and of Kaplan, are not slots of the class. They are arguments of the domain, in that
order, so an expression that depends on the context denotes a function of contexts, and one that
depends on the assignment a function of assignments. Instance resolution requires every type
parameter of the domain to be fixed by the type of objects, so an object interpreted relative to
data its type does not mention denotes the family over that data.

The class does not feed the composition of meanings in a tree. A tree is interpreted relative to
a lexicon of typed items and a function that values them, both arguments of the interpretation,
and lexica from separate files combine by their sum.

In a file that opens the scope, the brackets are these and not those of a quotient.

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
