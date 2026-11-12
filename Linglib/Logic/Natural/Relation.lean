module

public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.Tactic.DeriveFintype

/-!
# The seven relations of natural logic

MacCartney and Manning relate denotations by equivalence `≡`, forward and reverse entailment `⊑`
and `⊒`, negation `^`, alternation `|`, cover `⌣` and independence `#`. Following Icard, each
relation is a conjunction of atomic lattice constraints, `x ≤ y`, `y ≤ x`, disjointness and
codisjointness, so that `≡` also satisfies `⊑` and the relations are ordered by implication;
MacCartney and Manning's mutually exclusive relations are their strict versions. The join `R ⋈ S`,
the strongest relation that `R` followed by `S` guarantees, makes the relations a monoid, and it
is [sound](##NaturalLogic.Relation.Holds.join) over distributive lattices.

## References

* [maccartney-manning-2009]
* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

/-- Chaining two partial operations gives the same results in either bracketing when the operations
agree pointwise. -/
theorem exists_bind_comm {α β γ δ ζ ε : Type*} {f : α → β → Option γ}
    {g : γ → δ → Option ε} {f' : β → δ → Option ζ} {g' : α → ζ → Option ε}
    (h : ∀ a b d, (f a b).bind (g · d) = (f' b d).bind (g' a ·))
    {s : α → Prop} {t : β → Prop} {u : δ → Prop} {e : ε} :
    (∃ c, (∃ a, s a ∧ ∃ b, t b ∧ f a b = some c) ∧ ∃ d, u d ∧ g c d = some e) ↔
      ∃ a, s a ∧ ∃ z, (∃ b, t b ∧ ∃ d, u d ∧ f' b d = some z) ∧ g' a z = some e := by
  constructor
  · rintro ⟨c, ⟨a, ha, b, hb, hab⟩, d, hd, hcd⟩
    have := h a b d
    rw [hab, Option.bind_some, hcd] at this
    obtain ⟨z, hz, hze⟩ := Option.bind_eq_some_iff.1 this.symm
    exact ⟨a, ha, z, ⟨b, hb, d, hd, hz⟩, hze⟩
  · rintro ⟨a, ha, z, ⟨b, hb, d, hd, hbd⟩, hze⟩
    have := h a b d
    rw [hbd, Option.bind_some, hze] at this
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.1 this
    exact ⟨c, ⟨a, ha, b, hb, hc⟩, d, hd, hce⟩

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
and `∅` for `#`. A relation holds iff all its constraints do (`Relation.holds_iff`), and of the
sixteen constraint sets exactly these seven are nondegenerately realizable
(`Relation.mem_range_constraints_iff` in `Logic/Natural/Completeness.lean`). -/
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

/-- A primitive relation as one of the seven: `⊑`, `⊒`, `|` and `⌣` are the relations asserting a
single constraint, and the others are their conjunctions. -/
def Atom.toRelation : Atom → Relation
  | .le => .forward
  | .ge => .reverse
  | .disjoint => .alternation
  | .codisjoint => .cover

@[simp] theorem constraints_toRelation : ∀ a : Atom, a.toRelation.constraints = {a} := by decide

/-- A relation asserts the primitive relations it entails. -/
theorem mem_constraints_iff_le {R : Relation} {a : Atom} :
    a ∈ R.constraints ↔ R ≤ a.toRelation := by
  rw [le_iff, constraints_toRelation, Finset.singleton_subset_iff]

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

namespace Atom

/-- The polarity of the first argument when a constraint between elements of a Boolean lattice is
read as an inequality between the arguments or their complements: `x ≤ y` and `x ≤ yᶜ` take `x`
itself, `xᶜ ≤ yᶜ` and `xᶜ ≤ y` its complement. -/
def src : Atom → Polarity
  | .le | .disjoint => .positive
  | .ge | .codisjoint => .negative

/-- The polarity of the second argument in a constraint read as an inequality. -/
def tgt : Atom → Polarity
  | .le | .codisjoint => .positive
  | .ge | .disjoint => .negative

/-- The constraint saying that the first argument with polarity `m` is below the second with
polarity `q`. -/
def ofPolarities : Polarity → Polarity → Atom
  | .positive, .positive => .le
  | .positive, .negative => .disjoint
  | .negative, .positive => .codisjoint
  | .negative, .negative => .ge

theorem ofPolarities_injective : Function.Injective2 ofPolarities := by
  unfold Function.Injective2; decide

@[simp] theorem ofPolarities_src_tgt : ∀ a : Atom, ofPolarities a.src a.tgt = a := by decide

@[simp] theorem src_ofPolarities : ∀ m q : Polarity, (ofPolarities m q).src = m := by decide

@[simp] theorem tgt_ofPolarities : ∀ m q : Polarity, (ofPolarities m q).tgt = q := by decide

/-- The constraint between `x` and `z` that a constraint between `x` and `y` and one between `y`
and `z` guarantee, when there is one (`Relation.Atom.Holds.join`): read as inequalities, the two
chain by transitivity when they take `y` with the same polarity. So `≤` and `≥` are transitive,
disjointness is inherited downward and codisjointness upward, and `x` disjoint from `y` and `y`
codisjoint with `z` give `x ≤ z`. -/
def join (a b : Atom) : Option Atom :=
  if a.tgt = b.src then some (ofPolarities a.src b.tgt) else none

/-- The constraint in the order dual: `≤` and `≥` exchange, as do disjointness and
codisjointness. -/
def dual (a : Atom) : Atom := ofPolarities (.negative * a.src) (.negative * a.tgt)

end Atom

private theorem Atom.join_assoc :
    ∀ a b c : Atom, (a.join b).bind (·.join c) = (b.join c).bind (a.join ·) := by
  decide

/-- The join `R ⋈ R'` ([icard-2012], Lemma 1.5) is the strongest relation guaranteed between `x`
and `z` given `xRy` and `yR'z`, the relation asserting what the atom rule gives for each pair of
constraints of `R` and `R'` (`Relation.mem_constraints_mul`). It approximates relational
composition, which [maccartney-manning-2009] call join after the database operation; it is not the
lattice join.
Each cell is sound (`Relation.Holds.join`) and is the least
sound relation (`Relation.isLeast_join` in `Logic/Natural/Completeness.lean`), as [icard-2012]'s
Definition 1.4 requires. On a Boolean lattice it is relational composition (`Relation.holds_mul`
in `Logic/Natural/Completeness.lean`), the middle term ranging over every element;
[maccartney-manning-2009]'s relations exclude one another and the elements `⊥` and `⊤`, and their
composition is a union of relations on 17 of the 49 cells (§3). -/
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

/-- The converse of a relation, holding of `x` and `y` when the relation holds of `y` and `x`
(`Relation.holds_converse`): `⊑` and `⊒` exchange, and the other five are symmetric. -/
def converse : Relation → Relation
  | .forward => .reverse
  | .reverse => .forward
  | R => R

@[simp] theorem converse_converse (R : Relation) : R.converse.converse = R := by cases R <;> rfl

end Relation

/-! ### Lattice content of the relations -/

/-- The lattice content of a natural-logic relation ([icard-2012]
Definition 1.2), in mathlib's complementation vocabulary: `negation` is
`IsCompl`, `alternation` is `Disjoint`, `cover` is `Codisjoint`; `forward`
is non-strict `≤` (MacCartney's exclusive reading takes it proper, which
the projectivity tables do not need). -/
def Relation.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    Relation → α → α → Prop
  | .equiv => (· = ·)
  | .forward => (· ≤ ·)
  | .reverse => (· ≥ ·)
  | .negation => IsCompl
  | .alternation => Disjoint
  | .cover => Codisjoint
  | .independent => fun _ _ => True

/-- The lattice content of an atomic constraint ([icard-2012]
Definition 1.2). -/
def Relation.Atom.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    Relation.Atom → α → α → Prop
  | .le => (· ≤ ·)
  | .ge => (· ≥ ·)
  | .disjoint => Disjoint
  | .codisjoint => Codisjoint

theorem Relation.holds_iff {α : Type*} [Lattice α] [BoundedOrder α]
    {R : Relation} {x y : α} :
    R.Holds x y ↔ ∀ a ∈ R.constraints, a.Holds x y := by
  cases R <;>
    simp [Relation.Holds, Relation.Atom.Holds, Relation.constraints,
      isCompl_iff, le_antisymm_iff]

/-- In a Boolean algebra a constraint is an inequality between its arguments taken with its two
polarities. -/
theorem Relation.Atom.holds_iff_complHom_le {α : Type*} [BooleanAlgebra α] {a : Relation.Atom}
    {x y : α} : a.Holds x y ↔ Polarity.complHom a.src x ≤ Polarity.complHom a.tgt y := by
  cases a
  · exact Iff.rfl
  · exact compl_le_compl_iff_le.symm
  · exact le_compl_iff_disjoint_right.symm
  · exact codisjoint_iff_compl_le_right

theorem Relation.holds_toRelation {α : Type*} [Lattice α] [BoundedOrder α] {a : Relation.Atom}
    {x y : α} : a.toRelation.Holds x y ↔ a.Holds x y := by
  cases a <;> rfl

theorem Relation.holds_converse {α : Type*} [Lattice α] [BoundedOrder α] {R : Relation}
    {x y : α} : R.converse.Holds x y ↔ R.Holds y x := by
  cases R with
  | equiv => exact eq_comm
  | forward | reverse | independent => exact Iff.rfl
  | negation => exact ⟨IsCompl.symm, IsCompl.symm⟩
  | alternation => exact disjoint_comm
  | cover => exact codisjoint_comm

/-- A constraint holds in the order dual exactly when its dual holds. -/
theorem Relation.Atom.holds_toDual {α : Type*} [Lattice α] [BoundedOrder α] {a : Relation.Atom}
    {x y : α} : a.Holds (OrderDual.toDual x) (OrderDual.toDual y) ↔ a.dual.Holds x y := by
  cases a
  · exact Iff.rfl
  · exact Iff.rfl
  · exact disjoint_toDual_iff
  · exact codisjoint_toDual_iff

/-- The converse reverses the join. -/
theorem Relation.converse_mul : ∀ R S : Relation, (R * S).converse = S.converse * R.converse := by
  decide

instance Relation.Atom.decidableHolds {α : Type*} [Lattice α] [BoundedOrder α]
    [DecidableEq α] [DecidableLE α] :
    ∀ (a : Relation.Atom) (x y : α), Decidable (a.Holds x y)
  | .le, x, y => inferInstanceAs (Decidable (x ≤ y))
  | .ge, x, y => inferInstanceAs (Decidable (y ≤ x))
  | .disjoint, x, y => decidable_of_iff (x ⊓ y = ⊥) disjoint_iff.symm
  | .codisjoint, x, y => decidable_of_iff (x ⊔ y = ⊤) codisjoint_iff.symm

instance Relation.decidableHolds {α : Type*} [Lattice α] [BoundedOrder α]
    [DecidableEq α] [DecidableLE α] :
    ∀ (R : Relation) (x y : α), Decidable (R.Holds x y)
  | .equiv, x, y => inferInstanceAs (Decidable (x = y))
  | .forward, x, y => inferInstanceAs (Decidable (x ≤ y))
  | .reverse, x, y => inferInstanceAs (Decidable (y ≤ x))
  | .negation, x, y =>
      decidable_of_iff (x ⊓ y = ⊥ ∧ x ⊔ y = ⊤)
        (by rw [← disjoint_iff, ← codisjoint_iff]; exact isCompl_iff.symm)
  | .alternation, x, y => decidable_of_iff (x ⊓ y = ⊥) disjoint_iff.symm
  | .cover, x, y => decidable_of_iff (x ⊔ y = ⊤) codisjoint_iff.symm
  | .independent, _, _ => .isTrue trivial

/-- Relation-level order soundness: `≤` is the implication order on
the lattice content ([icard-2012] §1). -/
theorem Relation.Holds.of_le {β : Type*} [Lattice β] [BoundedOrder β]
    {R R' : Relation} {u v : β} (h : R.Holds u v) (href : R ≤ R') :
    R'.Holds u v := by
  cases R <;> cases R' <;>
    first
    | exact h
    | trivial
    | exact h.1
    | exact h.2
    | exact le_of_eq h
    | exact le_of_eq (Eq.symm h)

theorem Relation.Holds.apply {β ι : Type*} [Lattice β] [BoundedOrder β] {R : Relation} {f g : ι → β}
    (h : R.Holds f g) (i : ι) : R.Holds (f i) (g i) := by
  cases R with
  | equiv => exact congrFun h i
  | forward | reverse => exact h i
  | negation =>
    exact isCompl_iff.2 ⟨disjoint_iff.2 (congrFun (disjoint_iff.1 h.disjoint) i),
      codisjoint_iff.2 (congrFun (codisjoint_iff.1 h.codisjoint) i)⟩
  | alternation => exact disjoint_iff.2 (congrFun (disjoint_iff.1 h) i)
  | cover => exact codisjoint_iff.2 (congrFun (codisjoint_iff.1 h) i)
  | independent => trivial

/-! ### Join soundness -/

/-- The atom rule is sound: chained constraints give the constraint `Relation.Atom.join` says.
Distributivity is needed for a disjoint pair followed by a codisjoint one, which gives `≤`. -/
theorem Relation.Atom.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {a b c : Relation.Atom} (h : a.join b = some c) {x y z : β} (ha : a.Holds x y)
    (hb : b.Holds y z) : c.Holds x z := by
  cases a <;> cases b <;>
    simp only [Relation.Atom.join, Relation.Atom.src, Relation.Atom.tgt,
      Relation.Atom.ofPolarities, reduceCtorEq, ite_true, ite_false, Option.some.injEq] at h <;>
    subst h <;> simp only [Relation.Atom.Holds] at ha hb ⊢
  all_goals first
    | exact le_trans ha hb
    | exact ge_trans ha hb
    | exact hb.mono_left ha
    | exact ha.mono_right hb
    | exact ha.le_of_codisjoint hb
    | exact hb.symm.le_of_codisjoint ha.symm

/-- Chained relations compose as the join says, constraint by constraint. -/
theorem Relation.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {R S : Relation} {x y z : β} (hR : R.Holds x y) (hS : S.Holds y z) :
    (R * S).Holds x z :=
  Relation.holds_iff.2 fun _ hc ↦ by
    obtain ⟨a, ha, b, hb, h⟩ := Relation.mem_constraints_mul.1 hc
    exact Relation.Atom.Holds.join h (Relation.holds_iff.1 hR a ha) (Relation.holds_iff.1 hS b hb)

end NaturalLogic
