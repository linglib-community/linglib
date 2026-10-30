module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Quantifiers and determiner denotations

This file defines quantifiers and determiner denotations. A quantifier on a universe `α` is a
property of its subsets, `Quantifier α := Set α → Prop`, the denotation of a noun phrase. A
determiner denotation `Det α := Set α → Quantifier α` maps a restrictor `A` to the quantifier
`d A` of the noun phrase it heads, as in Barwise and Cooper. These are the quantifiers of type ⟨1⟩
that Mostowski introduced and their type ⟨1,1⟩ generalization, and both inherit the Boolean
algebra of the Pi type, whose `ᶜ`, `⊓` and `⊔` are outer negation, conjunction and disjunction.

The properties are stated in the lattice of sets: conservativity `d A B ↔ d A (A ∩ B)`, the
monotonicities as `Monotone` and `Antitone` of the sections, Peters and Westerståhl's left
monotonicities, van Benthem's relational properties, and invariance under the permutations of
the universe. A determiner, though, denotes a global quantifier, a `Det.Family` with a value on
every finite universe. Two conditions tie the values together:
[isomorphism closure](##Quantifier.Det.Family.Isom), that equivalent universes carry the same
quantifier, and [extension](##Quantifier.Det.Family.Ext), that enlarging the universe changes
nothing.

## Main definitions

* `Quantifier`, `Quantifier.Det`, `Quantifier.Det.Family`: quantifiers, determiner
  denotations, and determiner denotations on every finite universe.
* `Det.Conservative`, `Det.ScopeMonotone`, `Det.RestrictorMonotone`, `Det.Intersective`,
  `Det.Existential`, `Det.PositiveStrong`: the properties of determiner denotations.
* `Det.UpSEMon`, `Det.Smooth`, `Det.LeftAntiAdditive`: the left monotonicities.
* `Det.QuasiReflexive`, `Det.Filtrating`, `Det.QuantityInvariant`: relational properties and
  permutation invariance.
* `Det.innerNeg`, `Det.dual`, `Det.adjRestrict`: inner negation, the dual and restriction.
* `Det.Family.Isom`, `Det.Family.Ext`, `Det.Family.Constant`: isomorphism closure, extension,
  and constancy, the two together.
* `Quantifier.LivesOn`, `Quantifier.QuantityInvariant`, `Quantifier.individual`: the live-on
  property, invariance under the permutations of the universe, and the Montague lift.
* `Quantifier.Family`, `Quantifier.Family.Isom`, `Quantifier.Family.rel`: global quantifiers,
  their isomorphism closure, and relativization, which turns one into a global determiner
  denotation.

## Implementation notes

A type is not a subset of another type, so extension is stated for a subset `M` of a universe
`β` and the universe `↥M`. Extension therefore relates a universe only to its subtypes; it is
isomorphism closure that relates universes presented by unrelated types. The two together are
invariance along every embedding of universes, `Det.Family.Constant`, which is the condition the
theorems about global quantifiers assume.

Relativization evaluates a quantifier on the universe `↥A`, so relativizing on a subset of a
subset reaches a subtype of a subtype rather than the subset itself. Peters and Westerståhl's
identification of the relativizations with the conservative extensional determiner denotations
therefore holds here for isomorphism-closed quantifiers. Elements of one type are not elements of
another, so the global quantifiers that set theory allows to single out an element across
universes, such as the Montague lift of a fixed individual, have no counterpart among these.

## References

* [barwise-cooper-1981]
* [keenan-1987]
* [keenan-stavi-1986]
* [montague-1973]
* [mostowski-1957]
* [partee-1987]
* [peters-westerstahl-2006]
* [van-benthem-1984]
* [van-benthem-1986]
* [westerstahl-2024]
* [zwarts-1998]
-/

@[expose] public section

universe u

/-- A quantifier on `α` is a property of subsets of `α`, the denotation of a noun phrase, true of
the sets that are its scopes. It is a quantifier of type ⟨1⟩, the kind Mostowski introduced. -/
abbrev Quantifier (α : Type*) := Set α → Prop

namespace Quantifier

/-- A determiner denotation on `α` is a relation between a restrictor and a scope. Applied to a
restrictor it is the quantifier of the noun phrase the determiner heads. It is a quantifier of
type ⟨1,1⟩. -/
abbrev Det (α : Type*) := Set α → Quantifier α

/-- A global determiner denotation gives a determiner denotation on every finite universe. The
readings of a lexicon entry are drawn from these. -/
abbrev Det.Family : Type (u + 1) := ∀ (α : Type u) [Finite α], Det α

/-- The global determiner denotations form a Boolean algebra, pointwise on universes. -/
instance : BooleanAlgebra Det.Family.{u} :=
  Equiv.booleanAlgebra <|
    Equiv.piCongrRight fun α ↦ Equiv.arrowCongr Equiv.plift.symm (.refl (Det α))

variable {α : Type*}

namespace Det

/-! ### Conservativity and monotonicity -/

/-- A determiner denotation is conservative when `d A B ↔ d A (A ∩ B)`, so that only the part of
the scope inside the restrictor matters. -/
def Conservative (d : Det α) : Prop := ∀ A B, d A B ↔ d A (A ∩ B)

/-- A determiner denotation is scope monotone when every section `d A` is `Monotone`, so that
`d A B` and `B ⊆ B'` give `d A B'`. -/
def ScopeMonotone (d : Det α) : Prop := ∀ A, Monotone (d A)

/-- A determiner denotation is scope antitone when every section `d A` is `Antitone`. -/
def ScopeAntitone (d : Det α) : Prop := ∀ A, Antitone (d A)

/-- A determiner denotation is restrictor monotone, or persistent, when `d · B` is `Monotone`
for every scope `B`. -/
def RestrictorMonotone (d : Det α) : Prop := ∀ B, Monotone (d · B)

/-- A determiner denotation is restrictor antitone, or anti-persistent, when `d · B` is
`Antitone` for every scope `B`. -/
def RestrictorAntitone (d : Det α) : Prop := ∀ B, Antitone (d · B)

/-- A determiner denotation is intersective when `d A B` depends only on `A ∩ B`. -/
def Intersective (d : Det α) : Prop :=
  ∀ A B A' B' : Set α, A ∩ B = A' ∩ B' → (d A B ↔ d A' B')

/-! ### Strength -/

/-- A determiner denotation is positive strong when `d A A` holds for every `A`, as for
*every*. -/
def PositiveStrong (d : Det α) : Prop := ∀ A, d A A

/-- A determiner denotation is negative strong when `d A A` fails for every `A`, as for
*neither*. -/
def NegativeStrong (d : Det α) : Prop := ∀ A, ¬ d A A

/-- A determiner denotation is existential when `d A B ↔ d (A ∩ B) univ`, [keenan-1987]'s
characterization of the determiners that occur in *there*-sentences. -/
def Existential (d : Det α) : Prop := ∀ A B, d A B ↔ d (A ∩ B) Set.univ

/-! ### Left monotonicity and smoothness

Peters and Westerståhl's four left monotonicities enlarge or shrink the restrictor by elements
inside or outside the scope. On the number triangle, with `k = |A \ B|` and `m = |A ∩ B|`,
`UpSEMon` moves `(k, m)` to `(k, m + 1)`, `UpSWMon` to `(k + 1, m)`, `DownNWMon` moves
`(k, m + 1)` to `(k, m)` and `DownNEMon` moves `(k + 1, m)` to `(k, m)`. -/

/-- A determiner denotation is ↑SE monotone when enlarging the restrictor by elements of the scope
preserves it: `A ⊆ A'`, `A' \ B = A \ B` and `d A B` give `d A' B`. -/
def UpSEMon (d : Det α) : Prop := ∀ A B A', A ⊆ A' → A' \ B ⊆ A → d A B → d A' B

/-- A determiner denotation is ↑SW monotone when enlarging the restrictor by elements outside the
scope preserves it: `A ⊆ A'`, `A' ∩ B = A ∩ B` and `d A B` give `d A' B`. -/
def UpSWMon (d : Det α) : Prop := ∀ A B A', A ⊆ A' → A' ∩ B ⊆ A → d A B → d A' B

/-- A determiner denotation is ↓NW monotone when shrinking the restrictor by elements of the scope
preserves it: `A' ⊆ A`, `A' \ B = A \ B` and `d A B` give `d A' B`. -/
def DownNWMon (d : Det α) : Prop := ∀ A B A', A' ⊆ A → A \ B ⊆ A' → d A B → d A' B

/-- A determiner denotation is ↓NE monotone when shrinking the restrictor by elements outside the
scope preserves it: `A' ⊆ A`, `A' ∩ B = A ∩ B` and `d A B` give `d A' B`. -/
def DownNEMon (d : Det α) : Prop := ∀ A B A', A' ⊆ A → A ∩ B ⊆ A' → d A B → d A' B

/-- A determiner denotation is smooth when it is ↓NE and ↑SE monotone; smooth determiner
denotations are scope monotone. -/
def Smooth (d : Det α) : Prop := DownNEMon d ∧ UpSEMon d

/-- A determiner denotation is co-smooth when its inner negation is smooth, that is, when it is
↓NW and ↑SW monotone. -/
def CoSmooth (d : Det α) : Prop := DownNWMon d ∧ UpSWMon d

/-- A determiner denotation is left anti-additive when `d (A ∪ A') B ↔ d A B ∧ d A' B`, the
restrictor version of [zwarts-1998]'s anti-additivity. -/
def LeftAntiAdditive (d : Det α) : Prop := ∀ A A' B, d (A ∪ A') B ↔ d A B ∧ d A' B

/-- A determiner denotation is right anti-additive when `d A (B ∪ B') ↔ d A B ∧ d A B'`, so
that its scope is an anti-additive context in the sense of [zwarts-1998]. -/
def RightAntiAdditive (d : Det α) : Prop := ∀ A B B', d A (B ∪ B') ↔ d A B ∧ d A B'

/-! ### Relational properties

A determiner denotation is a binary relation between sets, so the classical relational
properties are the core relation classes: *all* is `IsTrans` and `Std.Antisymm`, *some* and *no*
are `Std.Symm`, and *not all* is `Std.Trichotomous`. The properties below are the ones the
theory of quantifiers adds. -/

/-- A determiner denotation is quasi-reflexive when `d A B` gives `d A A`, as for *some*. -/
def QuasiReflexive (d : Det α) : Prop := ∀ A B, d A B → d A A

/-- A determiner denotation is quasi-universal when `d A A` gives `d A B` for every `B`, as for
*no*. -/
def QuasiUniversal (d : Det α) : Prop := ∀ A B, d A A → d A B

/-- A determiner denotation is almost connected when `d A B` gives `d A C` or `d C B` for every
`C`, which is the transitivity of its complement. -/
def AlmostConnected (d : Det α) : Prop := ∀ A B C, d A B → d A C ∨ d C B

/-- A determiner denotation is circular when `d A B` and `d B C` give `d C A`. -/
def Circular (d : Det α) : Prop := ∀ A B C, d A B → d B C → d C A

/-- A determiner denotation is right continuous when `d A B₁`, `d A B₂` and `B₁ ⊆ B ⊆ B₂` give
`d A B`, so that every set of scopes `{B | d A B}` is order-connected. -/
def RightContinuous (d : Det α) : Prop :=
  ∀ A B B₁ B₂, B₁ ⊆ B → B ⊆ B₂ → d A B₁ → d A B₂ → d A B

/-- A determiner denotation is scope-intersective when `d A B` and `d A C` give `d A (B ∩ C)`. -/
def ScopeIntersective (d : Det α) : Prop := ∀ A B C, d A B → d A C → d A (B ∩ C)

/-- A determiner denotation is filtrating when it is scope monotone and scope-intersective, so
that its scopes at a fixed restrictor form a filter. -/
def Filtrating (d : Det α) : Prop := ScopeMonotone d ∧ ScopeIntersective d

/-! ### Invariance -/

/-- A determiner denotation is quantity invariant when no permutation of the universe changes it,
`d (σ ⁻¹' A) (σ ⁻¹' B) ↔ d A B`. This is [mostowski-1957]'s requirement that a quantifier not
distinguish the elements of the universe, permutation closure on a single universe; on a finite
universe it makes `d A B` depend only on the sizes of the four cells of the Venn diagram of `A`
and `B`. -/
def QuantityInvariant (d : Det α) : Prop :=
  ∀ (σ : Equiv.Perm α) (A B : Set α), d (σ ⁻¹' A) (σ ⁻¹' B) ↔ d A B

/-! ### The Boolean algebra, the negations and the dual

The outer negation of a determiner denotation is its complement `dᶜ`, and determiner conjunction
and disjunction are the meet `d ⊓ d'` and join `d ⊔ d'` of the Boolean algebra `Det α`. -/

@[simp] theorem compl_apply (d : Det α) (A B : Set α) : dᶜ A B = ¬ d A B := rfl

@[simp] theorem inf_apply (d d' : Det α) (A B : Set α) : (d ⊓ d') A B = (d A B ∧ d' A B) := rfl

@[simp] theorem sup_apply (d d' : Det α) (A B : Set α) : (d ⊔ d') A B = (d A B ∨ d' A B) := rfl

/-- The inner negation of a determiner denotation negates the scope, `(d~) A B = d A Bᶜ`. -/
def innerNeg (d : Det α) : Det α := fun A B ↦ d A Bᶜ

/-- The dual of a determiner denotation is the complement of its inner negation, so that the dual
of *every* is *some*. -/
def dual (d : Det α) : Det α := (innerNeg d)ᶜ

/-- The restriction of a determiner denotation by an adjective or relative clause `C` narrows the
restrictor, so that *tall student* is *student* and *tall*. -/
def adjRestrict (d : Det α) (C : Set α) : Det α := fun A B ↦ d (A ∩ C) B

/-! ### Global quantifiers -/

namespace Family

variable (Q : Det.Family.{u})

/-- A global determiner denotation is conservative when it is conservative on every universe. -/
def Conservative : Prop := ∀ (α : Type u) [Finite α], (Q α).Conservative

/-- A global determiner denotation is closed under isomorphism (ISOM) when an equivalence of
universes `e : α ≃ β` carries its quantifier on `β` to its quantifier on `α`. -/
def Isom : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (e : α ≃ β) (A B : Set β),
    Q α (e ⁻¹' A) (e ⁻¹' B) ↔ Q β A B

/-- A global determiner denotation satisfies extension (EXT) when enlarging the universe does not
change it: for `A` and `B` inside `M ⊆ β`, it holds on the universe `M` exactly when it holds on
`β`. That determiner denotations satisfy it is [van-benthem-1986]'s observation. -/
def Ext : Prop :=
  ∀ ⦃β : Type u⦄ [Finite β] (M A B : Set β), A ⊆ M → B ⊆ M →
    (Q M (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) ↔ Q β A B)

/-- A global determiner denotation is constant when it is invariant along every embedding of
universes: for `A` and `B` inside the range of `f : α ↪ β`, it holds of their preimages on `α`
exactly when it holds of them on `β`. Constancy is extension together with isomorphism closure,
an embedding being an isomorphism onto its range followed by an inclusion, and it is
[westerstahl-2024]'s explication of a quantifier meaning the same on every universe. -/
def Constant : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (f : α ↪ β) (A B : Set β),
    A ⊆ Set.range f → B ⊆ Set.range f → (Q α (f ⁻¹' A) (f ⁻¹' B) ↔ Q β A B)

variable {Q}

@[simp] theorem compl_apply (α : Type u) [Finite α] : Qᶜ α = (Q α)ᶜ := rfl

@[simp] theorem inf_apply (Q' : Det.Family.{u}) (α : Type u) [Finite α] :
    (Q ⊓ Q') α = Q α ⊓ Q' α := rfl

@[simp] theorem sup_apply (Q' : Det.Family.{u}) (α : Type u) [Finite α] :
    (Q ⊔ Q') α = Q α ⊔ Q' α := rfl

theorem le_def {Q' : Det.Family.{u}} :
    Q ≤ Q' ↔ ∀ (α : Type u) [Finite α] (A B : Set α), Q α A B → Q' α A B :=
  ⟨fun h α _ A B ↦ h α ⟨inferInstance⟩ A B, fun h α p A B ↦ @h α p.down A B⟩

/-- On a single universe, isomorphism closure is permutation invariance. -/
theorem Isom.quantityInvariant (h : Q.Isom) (α : Type u) [Finite α] :
    (Q α).QuantityInvariant :=
  fun σ ↦ h σ

end Family

end Det

/-! ### Type ⟨1⟩ quantifiers -/

/-- A quantifier lives on `A` when `Q B ↔ Q (A ∩ B)` for every `B`. -/
def LivesOn (Q : Quantifier α) (A : Set α) : Prop := ∀ B, Q B ↔ Q (A ∩ B)

theorem _root_.Quantifier.Det.Conservative.livesOn {d : Det α} (h : d.Conservative)
    (A : Set α) : (d A).LivesOn A :=
  h A

/-- A quantifier is quantity invariant when no permutation of the universe changes it,
`Q (σ ⁻¹' B) ↔ Q B`: [mostowski-1957]'s invariance condition on a quantifier limited to a universe,
of which `Det.QuantityInvariant` is the counterpart for determiner denotations. -/
def QuantityInvariant (Q : Quantifier α) : Prop :=
  ∀ (σ : Equiv.Perm α) (B : Set α), Q (σ ⁻¹' B) ↔ Q B

/-- The Montague lift of an entity is the principal ultrafilter it generates, the quantifier of
the sets it belongs to, as [montague-1973] translates a proper name; it is Partee's LIFT and the
continuation `pure`. -/
def individual (a : α) : Quantifier α := fun B ↦ a ∈ B

theorem individual_injective : Function.Injective (individual (α := α)) :=
  fun a b h ↦ (show b = a from (congrFun h {a}).mp rfl).symm

theorem individual_livesOn {A : Set α} {a : α} (ha : a ∈ A) : (individual a).LivesOn A :=
  fun _ ↦ ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

/-! ### Global quantifiers and relativization -/

/-- A global quantifier gives a quantifier on every finite universe. -/
abbrev Family : Type (u + 1) := ∀ (α : Type u) [Finite α], Quantifier α

/-- The global quantifiers form a Boolean algebra, pointwise on universes. -/
instance : BooleanAlgebra Family.{u} :=
  Equiv.booleanAlgebra <|
    Equiv.piCongrRight fun α ↦ Equiv.arrowCongr Equiv.plift.symm (.refl (Quantifier α))

namespace Family

variable (Q : Family.{u})

/-- A global quantifier is closed under isomorphism when an equivalence of universes
`e : α ≃ β` carries its value on `β` to its value on `α`. -/
def Isom : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (e : α ≃ β) (B : Set β), Q α (e ⁻¹' B) ↔ Q β B

/-- The relativization of a global quantifier evaluates it on the restrictor as the universe:
`Q.rel A B` holds when `Q` holds, on the universe `A`, of the part of `B` inside `A`. -/
def rel : Det.Family.{u} := fun _ _ A B ↦ Q A (Subtype.val ⁻¹' B)

variable {Q}

theorem le_def {Q' : Family.{u}} :
    Q ≤ Q' ↔ ∀ (α : Type u) [Finite α] (B : Set α), Q α B → Q' α B :=
  ⟨fun h α _ B ↦ h α ⟨inferInstance⟩ B, fun h α p B ↦ @h α p.down B⟩

end Family

end Quantifier
