module

public import Mathlib.Algebra.Group.Action.Defs
public import Linglib.Logic.Natural.Signature

/-!
# The projectivity calculus

This file defines the seven natural-logic relations between denotations (≡, ⊑, ⊒, ^, |, ⌣, #) and
the operations of Icard's projectivity calculus on them: chaining two relations, and projecting a
relation through a map of known signature, which is an action of the signature monoid on the
relations. A relation is a conjunction of atomic constraints, so `≡` also satisfies `⊑`; the
mutually exclusive relations of MacCartney and Manning are their strict versions. Each operation is
a rule on single atoms or properties lifted to the conjunctions, and Icard's tables are what the
rules give, cell by cell, except that every map carries `≡` to `≡`.

## Implementation notes

The monoid law of the relations and the action law follow from the rules: the atom rule is
associative, and the property rule for projection is compatible with the one for composition. Each
rule is proved sound in `Logic/Natural/Soundness.lean`, and the lifted operations are proved
optimal in `Logic/Natural/Completeness.lean`, which also shows that the seven relations are the
nondegenerately realizable constraint sets.

## References

* [icard-2012]
* [maccartney-manning-2009]
-/

@[expose] public section

namespace NaturalLogic

/-! ### The seven relations -/

/-- The seven natural-logic relations between denotations. -/
inductive Relation where
  /-- Equivalence `≡` holds when the denotations coincide (*couch* / *sofa*). -/
  | equiv
  /-- Forward entailment `⊑` holds when `A ⊆ B` (*dog* / *animal*). -/
  | forward
  /-- Reverse entailment `⊒` holds when `A ⊇ B` (*animal* / *dog*). -/
  | reverse
  /-- Negation `^` holds when the denotations are disjoint and exhaustive
      (*happy* / *unhappy*). -/
  | negation
  /-- Alternation `|` holds when the denotations are disjoint (*cat* / *dog*). -/
  | alternation
  /-- Cover `⌣` holds when the denotations are exhaustive (*animal* / *nondog*). -/
  | cover
  /-- Independence `#` imposes no constraint (*hungry* / *tall*). -/
  | independent
  deriving DecidableEq, Fintype, Repr

namespace Relation

/-- The atomic lattice constraints a relation can impose
([icard-2012] Definition 1.2). -/
inductive Atom where
  /-- `x ≤ y`. -/
  | le
  /-- `y ≤ x`. -/
  | ge
  /-- `x ⊓ y = ⊥`. -/
  | disjoint
  /-- `x ⊔ y = ⊤`. -/
  | codisjoint
  deriving DecidableEq, Fintype, Repr

/-- The atomic constraints a relation asserts, `{le, ge}` for `≡`, `{disjoint, codisjoint}` for `^`
and `∅` for `#`. A relation holds iff all its constraints do (`Relation.holds_iff` in
`Logic/Natural/Soundness.lean`), and of the sixteen constraint sets exactly these seven are
nondegenerately realizable (`Relation.mem_range_constraints_iff` in
`Logic/Natural/Completeness.lean`). -/
def constraints : Relation → Finset Atom
  | .equiv => {.le, .ge}
  | .forward => {.le}
  | .reverse => {.ge}
  | .negation => {.disjoint, .codisjoint}
  | .alternation => {.disjoint}
  | .cover => {.codisjoint}
  | .independent => ∅

theorem constraints_injective : Function.Injective constraints := by decide

/-- The strongest relation all of whose constraints satisfy `P`, found by trying the relations
from the strongest down to `#`, which has none. When the atoms satisfying `P` are the constraints
of a relation, it is that relation. -/
def ofAtoms (P : Atom → Prop) [DecidablePred P] : Relation :=
  ([equiv, negation, forward, reverse, alternation, cover].find?
    (fun R ↦ ∀ a ∈ R.constraints, P a)).getD independent

/-- In the implication order ([icard-2012]'s ≪), `R ≤ R'` iff `xRy` entails `xR'y`, i.e. iff the
constraints of `R'` are among those of `R` (`Relation.Holds.of_le`). It consists of two diamonds
sharing only the top `#`, one with `≡` below `⊑` and `⊒`, the other with `^` below `|` and `⌣`;
there is no bottom, since `x = y` makes `x` and `y` neither disjoint nor exhaustive. The most
informative relation, which [icard-2012] calls ≪-maximal, is the least one in this order. -/
instance : PartialOrder Relation :=
  .lift (fun R ↦ OrderDual.toDual (constraints R))
    (OrderDual.toDual.injective.comp constraints_injective)

theorem le_iff {R R' : Relation} :
    R ≤ R' ↔ constraints R' ⊆ constraints R := Iff.rfl

instance : DecidableLE Relation := fun _ _ ↦
  decidable_of_iff _ le_iff.symm

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/-- The constraint between `x` and `z` that a constraint between `x` and `y` and one between `y`
and `z` guarantee, when there is one (`Relation.Atom.Holds.join` in `Logic/Natural/Soundness.lean`):
`≤` and `≥` are transitive, disjointness is inherited downward and codisjointness upward, and,
in a distributive lattice, `x` disjoint from `y` and `y` codisjoint with `z` give `x ≤ z`. -/
def Atom.join : Atom → Atom → Option Atom
  | .le, .le => some .le
  | .ge, .ge => some .ge
  | .le, .disjoint => some .disjoint
  | .disjoint, .ge => some .disjoint
  | .ge, .codisjoint => some .codisjoint
  | .codisjoint, .le => some .codisjoint
  | .disjoint, .codisjoint => some .le
  | .codisjoint, .disjoint => some .ge
  | _, _ => none

private theorem Atom.join_assoc :
    ∀ a b c : Atom, (a.join b).bind (·.join c) = (b.join c).bind (a.join ·) := by
  decide

/-- The join `R ⋈ R'` ([icard-2012], Lemma 1.5) is the strongest relation guaranteed between `x`
and `z` given `xRy` and `yR'z`, the relation asserting what the atom rule gives for each pair of
constraints of `R` and `R'` (`Relation.mem_constraints_mul`). It approximates relational
composition, which [maccartney-manning-2009] call join after the database operation; it is not the
lattice join.
Each cell is sound (`Relation.Holds.join` in `Logic/Natural/Soundness.lean`) and is the least
sound relation (`Relation.isLeast_join` in `Logic/Natural/Completeness.lean`), as [icard-2012]'s
Definition 1.4 requires. Exact composition is a union of the seven relations on 17 of the 49 cells
([maccartney-manning-2009] §3), and this gives the best single relation there. -/
def join (R S : Relation) : Relation :=
  ofAtoms fun c ↦ ∃ a ∈ R.constraints, ∃ b ∈ S.constraints, a.join b = some c

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

theorem mem_constraints_mul {R S : Relation} {c : Atom} :
    c ∈ (R * S).constraints ↔ ∃ a ∈ R.constraints, ∃ b ∈ S.constraints, a.join b = some c := by
  revert R S c
  decide

/-- The relations form a monoid under ⋈ with identity `≡`. The identity and absorption laws are
printed in [icard-2012] (p. 710); associativity, printed in neither [icard-2012] nor
[maccartney-manning-2009], is that of the atom rule. The monoid is not commutative, since `^ ⋈ ⌣ =
⊑` but `⌣ ⋈ ^ = ⊒`. -/
instance : Monoid Relation where
  mul_assoc R S T := constraints_injective <| Finset.ext fun _ ↦ by
    simp only [mem_constraints_mul]
    exact exists_bind_comm Atom.join_assoc
  one_mul r := by cases r <;> rfl
  mul_one r := by cases r <;> rfl

/-- `#` absorbs on the left ([icard-2012] p. 710). -/
@[simp] theorem top_mul (r : Relation) : ⊤ * r = ⊤ := by cases r <;> rfl

/-- `#` absorbs on the right ([icard-2012] p. 710). -/
@[simp] theorem mul_top (r : Relation) : r * ⊤ = ⊤ := by cases r <;> rfl

end Relation

/-! ### Projection -/

namespace Signature

/-- The constraint between the values of a function with property `p` that a constraint `a`
between its arguments guarantees, when there is one (`Signature.Property.HoldsFor.project` in
`Logic/Natural/Soundness.lean`): a monotone function keeps `≤` and `≥` and an antitone one swaps
them, an additive function keeps codisjointness and a multiplicative one disjointness, an
anti-additive function turns codisjointness into disjointness and an anti-multiplicative one the
reverse. -/
def Property.project : Relation.Atom → Property → Option Relation.Atom
  | .le, .monotone => some .le
  | .ge, .monotone => some .ge
  | .le, .antitone => some .ge
  | .ge, .antitone => some .le
  | .codisjoint, .additive => some .codisjoint
  | .disjoint, .multiplicative => some .disjoint
  | .codisjoint, .antiAdditive => some .disjoint
  | .disjoint, .antiMultiplicative => some .codisjoint
  | _, _ => none

private theorem Property.compose_project : ∀ (p q : Property) (a : Relation.Atom),
    (p.compose q).bind (Property.project a ·) =
      (Property.project a q).bind (Property.project · p) := by
  decide

/-- The projection of a relation through a function of the given signature is the strongest relation
guaranteed between `f x` and `f y` when `x R y` and `f` has signature `σ` ([icard-2012] Definition
2.3, computed by his Lemma 2.4): `≡`, since every function preserves equality, and otherwise the
relation asserting what the property rule gives for each property of `σ` and constraint of `R`
(`Signature.mem_constraints_project`). Each row is sound (`Signature.soundFor_of_holdsFor` in
`Logic/Natural/Soundness.lean`) and least (`Signature.isLeast_project` in
`Logic/Natural/Completeness.lean`). [icard-2012] remarks under the table that `[R]^• = #` for all
`R` (p. 715), which is what the property rule alone gives for `≡` too. -/
def project (R : Relation) (σ : Signature) : Relation :=
  if R = .equiv then .equiv else
    Relation.ofAtoms fun b ↦ ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b

@[simp] theorem project_equiv (φ : Signature) : project .equiv φ = .equiv := rfl

@[simp] theorem project_independent (φ : Signature) : project .independent φ = .independent := by
  cases φ <;> rfl

theorem mem_constraints_project {R : Relation} (hR : R ≠ .equiv) {σ : Signature}
    {b : Relation.Atom} : b ∈ (project R σ).constraints ↔
      ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b := by
  revert R σ b
  decide

/-- Projection through a less specific signature gives a weaker relation. -/
theorem project_mono (R : Relation) : Monotone (project R) := by
  intro σ τ h
  by_cases hR : R = .equiv
  · subst hR
    exact le_rfl
  refine Relation.le_iff.2 fun _ hb ↦ ?_
  obtain ⟨p, hp, a, ha, hab⟩ := (mem_constraints_project hR).1 hb
  exact (mem_constraints_project hR).2 ⟨p, le_iff.1 h hp, a, ha, hab⟩

private theorem project_ne_equiv : ∀ {R : Relation} (σ : Signature), R ≠ .equiv →
    project R σ ≠ .equiv := by
  decide

/-- Projecting through `φ` and then through `ψ` is projecting through `ψ * φ` ([icard-2012]
Definition 2.6 and Lemma 2.7), since applying the composite property rule is applying the two
rules in turn. -/
theorem project_project (R : Relation) (φ ψ : Signature) :
    project (project R φ) ψ = project R (ψ * φ) := by
  by_cases hR : R = .equiv
  · subst hR; simp only [project_equiv]
  refine Relation.constraints_injective <| Finset.ext fun _ ↦ ?_
  simp only [mem_constraints_project (project_ne_equiv φ hR), mem_constraints_project hR,
    mem_properties_mul]
  exact (exists_bind_comm Property.compose_project).symm

instance : SMul Signature Relation := ⟨fun σ R ↦ project R σ⟩

@[simp] theorem smul_def (σ : Signature) (R : Relation) : σ • R = project R σ := rfl

/-- Projection is an action of the signature monoid on the relations, with
`Signature.project_project` as its `mul_smul` law. -/
instance : MulAction Signature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (project_project R φ ψ).symm

private theorem eq_of_project_eq : ∀ σ τ : Signature, project .forward σ = project .forward τ →
    project .negation σ = project .negation τ → σ = τ := by
  decide

/-- A signature is determined by how it projects the relations, already by its projections of `⊑`
and `^`. -/
instance : FaithfulSMul Signature Relation where
  eq_of_smul_eq_smul {σ τ} h := eq_of_project_eq σ τ (h .forward) (h .negation)

end Signature

end NaturalLogic
