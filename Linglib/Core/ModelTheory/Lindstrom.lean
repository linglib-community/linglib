module

public import Linglib.Core.ModelTheory.LanguageMap
public import Mathlib.ModelTheory.Bundled

/-!
# Lindström generalized quantifiers

`[UPSTREAM]` candidate. A generalized quantifier over a language `L`, in Lindström's sense, is a
class of `L`-structures closed under isomorphism, so the invariance Mostowski imposed on
quantifiers is part of the type rather than a side condition on a denotation. Like
`TopologicalSpace.Clopens` and `FirstOrder.Language.DefinableSet`, these classes are `SetLike` with
the Boolean operations of sets, which are the operations Mostowski defines on quantifiers: the
complement is outer negation. Each sentence defines a quantifier,
[its class of models](##FirstOrder.Language.LindstromQuantifier.ofSentence); these classes are the
ones Lindström writes `EC`. Over a monadic language, quantifiers
[are the relations between cardinals](##FirstOrder.Language.LindstromQuantifier.ofTypeCount), since
a monadic structure is determined up to isomorphism by how many elements have each unary type.

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

/-- A Lindström quantifier over `L` is a class of `L`-structures closed under `L`-isomorphism. -/
structure LindstromQuantifier (L : Language.{u, v}) where
  /-- The structures the quantifier holds of. -/
  carrier : Set (Bundled.{w} L.Structure)
  /-- The class is closed under `L`-isomorphism. -/
  is_equiv_invariant' : ∀ {M N : Bundled.{w} L.Structure}, Nonempty (M ≃[L] N) →
    (M ∈ carrier ↔ N ∈ carrier)

namespace LindstromQuantifier

variable {L : Language.{u, v}} {Q R : LindstromQuantifier.{u, v, w} L}
  {M N : Bundled.{w} L.Structure}

instance : SetLike (LindstromQuantifier.{u, v, w} L) (Bundled.{w} L.Structure) where
  coe := carrier
  coe_injective Q R h := by cases Q; cases R; congr

instance : PartialOrder (LindstromQuantifier.{u, v, w} L) :=
  .ofSetLike (LindstromQuantifier.{u, v, w} L)

theorem is_equiv_invariant (Q : LindstromQuantifier.{u, v, w} L) (h : Nonempty (M ≃[L] N)) :
    M ∈ Q ↔ N ∈ Q :=
  Q.is_equiv_invariant' h

@[ext] protected theorem ext (h : ∀ M, M ∈ Q ↔ M ∈ R) : Q = R := SetLike.ext h

/-! ### Boolean-algebra structure -/

instance : Max (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R ↦ ⟨Q ∪ R, fun h ↦ or_congr (Q.is_equiv_invariant h) (R.is_equiv_invariant h)⟩⟩
instance : Min (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R ↦ ⟨Q ∩ R, fun h ↦ and_congr (Q.is_equiv_invariant h) (R.is_equiv_invariant h)⟩⟩
instance : Top (LindstromQuantifier.{u, v, w} L) := ⟨⟨Set.univ, fun _ ↦ Iff.rfl⟩⟩
instance : Bot (LindstromQuantifier.{u, v, w} L) := ⟨⟨∅, fun _ ↦ Iff.rfl⟩⟩
instance : SDiff (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R ↦ ⟨Q \ R, fun h ↦ and_congr (Q.is_equiv_invariant h)
    (not_congr (R.is_equiv_invariant h))⟩⟩
instance : HImp (LindstromQuantifier.{u, v, w} L) where
  himp Q R := ⟨(Q : Set _) ⇨ R, fun h ↦ by
    simp only [himp_eq]
    exact or_congr (R.is_equiv_invariant h) (not_congr (Q.is_equiv_invariant h))⟩
instance : Compl (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q ↦ ⟨(Q : Set _)ᶜ, fun h ↦ not_congr (Q.is_equiv_invariant h)⟩⟩

variable (Q R) in
@[simp, norm_cast] theorem coe_sup : ↑(Q ⊔ R) = (Q ∪ R : Set (Bundled.{w} L.Structure)) := rfl
variable (Q R) in
@[simp, norm_cast] theorem coe_inf : ↑(Q ⊓ R) = (Q ∩ R : Set (Bundled.{w} L.Structure)) := rfl
@[simp, norm_cast] theorem coe_top :
    (↑(⊤ : LindstromQuantifier.{u, v, w} L) : Set (Bundled.{w} L.Structure)) = Set.univ := rfl
@[simp, norm_cast] theorem coe_bot :
    (↑(⊥ : LindstromQuantifier.{u, v, w} L) : Set (Bundled.{w} L.Structure)) = ∅ := rfl
variable (Q R) in
@[simp, norm_cast] theorem coe_sdiff : ↑(Q \ R) = (Q \ R : Set (Bundled.{w} L.Structure)) := rfl
variable (Q R) in
@[simp, norm_cast] theorem coe_himp : ↑(Q ⇨ R) = (Q ⇨ R : Set (Bundled.{w} L.Structure)) := rfl
variable (Q) in
@[simp, norm_cast] theorem coe_compl : (↑Qᶜ : Set (Bundled.{w} L.Structure)) = (↑Q)ᶜ := rfl

instance : BooleanAlgebra (LindstromQuantifier.{u, v, w} L) := fast_instance%
  SetLike.coe_injective.booleanAlgebra _ .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl
    coe_sdiff coe_himp

@[simp] theorem mem_compl : M ∈ Qᶜ ↔ M ∉ Q := .rfl

/-! ### The quantifier of a sentence -/

/-- The quantifier defined by a sentence holds of exactly the models of the sentence. -/
def ofSentence (φ : L.Sentence) : LindstromQuantifier.{u, v, w} L where
  carrier := {M | M ⊨ φ}
  is_equiv_invariant' := fun ⟨e⟩ ↦ StrongHomClass.realize_sentence e φ

@[simp] theorem mem_ofSentence {φ : L.Sentence} : M ∈ ofSentence φ ↔ M ⊨ φ := .rfl

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

/-- A relation between cardinals determines a monadic quantifier, each monadic quantifier arises
from exactly one, and the correspondence preserves the Boolean structure. On a fixed universe with
one predicate this is Theorem 1 of [mostowski-1957]; for several predicates the relation is the
`R_Q` of [lindstrom-1966] §3, and [peters-westerstahl-2006] Ch. 3 Fact 4 is the type `⟨1⟩` case. -/
noncomputable def ofTypeCount :
    Set (((Language.monadic ι).Relations 1 → Prop) → Cardinal.{max v w}) ≃o
      LindstromQuantifier.{0, v, max v w} (Language.monadic ι) where
  toFun T := ⟨typeCount ⁻¹' T, fun h => by
    rw [Set.mem_preimage, Set.mem_preimage, typeCount_eq_iff.2 h]⟩
  invFun Q := typeCount '' Q
  left_inv T := typeCount_surjective.image_preimage T
  right_inv Q := LindstromQuantifier.ext fun _ =>
    ⟨fun ⟨_, hN, h⟩ => (Q.is_equiv_invariant (typeCount_eq_iff.1 h)).1 hN,
      fun h => ⟨_, h, rfl⟩⟩
  map_rel_iff' := typeCount_surjective.preimage_subset_preimage_iff

@[simp] theorem mem_ofTypeCount
    {T : Set (((Language.monadic ι).Relations 1 → Prop) → Cardinal.{max v w})}
    {M : Bundled.{max v w} (Language.monadic ι).Structure} :
    M ∈ ofTypeCount T ↔ typeCount M ∈ T := .rfl

end Monadic

end LindstromQuantifier

end FirstOrder.Language
