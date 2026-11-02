module

public import Linglib.Core.ModelTheory.LanguageMap
public import Mathlib.ModelTheory.Bundled

/-!
# Lindström generalized quantifiers

`[UPSTREAM]` candidate. A generalized quantifier over a language `L`, in Lindström's sense, is a
class of `L`-structures closed under isomorphism, which is the same thing as a set of isomorphism
types. Taking it to be `Set (Quotient equivSetoid)` makes the invariance Mostowski imposed on
quantifiers hold by construction, and makes the Boolean operations he defines on quantifiers those
of `Set`: the complement is outer negation. Each sentence defines a quantifier,
[its class of models](##FirstOrder.Language.LindstromQuantifier.ofSentence); these classes are the
ones Lindström writes `EC`. Over a monadic language, isomorphism types [are the functions from
unary types to cardinals](##FirstOrder.Language.LindstromQuantifier.typeCountEquiv), so that
quantifiers are the relations between cardinals, along `Equiv.toOrderIsoSet`.

## Implementation notes

Lindström takes classes of relational structures of a finite type; here `L` may have function
symbols and infinitely many symbols, which costs nothing since isomorphism invariance is the only
condition. His type `⟨1, 1⟩` is `Language.monadic (Fin 2)` and his type `⟨2⟩` is `Language.graph`.
Structures may be empty, as throughout mathlib's model theory, while his satisfaction relation runs
over assignments in `|𝔄|^ω`, which presupposes a nonempty domain.

## References

* [lindstrom-1966]
* [mostowski-1957]
* [peters-westerstahl-2006]
-/

@[expose] public section

universe u v w

namespace FirstOrder.Language

open CategoryTheory
open scoped FirstOrder

/-- A Lindström quantifier over `L` is a class of `L`-structures closed under `L`-isomorphism, given
as the set of isomorphism types of its members. -/
abbrev LindstromQuantifier (L : Language.{u, v}) : Type (max u v (w + 1)) :=
  Set (Quotient (equivSetoid.{u, v, w} (L := L)))

namespace LindstromQuantifier

variable {L : Language.{u, v}} {M N : Bundled.{w} L.Structure}

theorem is_equiv_invariant (Q : LindstromQuantifier.{u, v, w} L) (h : Nonempty (M ≃[L] N)) :
    ⟦M⟧ ∈ Q ↔ ⟦N⟧ ∈ Q := by
  rw [Quotient.sound h]

/-- The quantifier defined by a sentence holds of exactly the models of the sentence. -/
def ofSentence (φ : L.Sentence) : LindstromQuantifier.{u, v, w} L :=
  {q | q.liftOn (· ⊨ φ) fun _ _ ⟨e⟩ ↦ propext (StrongHomClass.realize_sentence e φ)}

@[simp] theorem mem_ofSentence {φ : L.Sentence} : ⟦M⟧ ∈ ofSentence φ ↔ M ⊨ φ := .rfl

/-! ### Monadic quantifiers as relations between cardinals -/

section Monadic

open Cardinal

variable {ι : Type v}

/-- The number of elements of each unary type of a structure. -/
def typeCount (M : Bundled.{w} L.Structure) (S : L.Relations 1 → Prop) : Cardinal.{w} :=
  #(L.unaryType ⁻¹' {S} : Set M)

theorem typeCount_eq_iff [L.IsMonadic] : typeCount M = typeCount N ↔ Nonempty (M ≃[L] N) :=
  funext_iff.trans nonempty_equiv_iff_mk_eq.symm

/-- Any number of elements of each unary type makes up a structure. -/
theorem typeCount_surjective :
    Function.Surjective (typeCount.{0, v, max v w} (L := Language.monadic ι)) := fun c => by
  let : (Language.monadic ι).Structure (Σ S, (c S).out) :=
    monadic.structure fun i a => a.1 (.pred i)
  have hu (a : Σ S, (c S).out) : (Language.monadic ι).unaryType a = a.1 :=
    funext fun | .pred _ => rfl
  refine ⟨⟨_, this⟩, funext fun S => ?_⟩
  conv_rhs => rw [← mk_out (c S)]
  exact mk_congr ((_root_.Equiv.subtypeEquivRight fun a => by
    rw [Set.mem_preimage, hu, Set.mem_singleton_iff]).trans (_root_.Equiv.sigmaSubtype S))

/-- The isomorphism types of structures for a monadic language are the functions from unary types
to cardinals. Along `Equiv.toOrderIsoSet`, a monadic quantifier is a unique relation between
cardinals: on a fixed universe with one predicate this is Theorem 1 of [mostowski-1957]; for
several predicates the relation is the `R_Q` of [lindstrom-1966] §3, and
[peters-westerstahl-2006] Ch. 3 Fact 4 is the type `⟨1⟩` case. -/
noncomputable def typeCountEquiv :
    Quotient (equivSetoid.{0, v, max v w} (L := Language.monadic ι)) ≃
      (((Language.monadic ι).Relations 1 → Prop) → Cardinal.{max v w}) :=
  .ofBijective (Quotient.lift typeCount fun _ _ h => typeCount_eq_iff.2 h)
    ⟨Quotient.ind₂ fun _ _ h => Quotient.sound (typeCount_eq_iff.1 h),
      fun c => let ⟨M, hM⟩ := typeCount_surjective c; ⟨⟦M⟧, hM⟩⟩

end Monadic

end LindstromQuantifier

end FirstOrder.Language
