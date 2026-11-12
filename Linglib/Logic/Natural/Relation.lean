module

public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.PEquiv
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
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

/-! ### Atomic constraints

An atomic constraint relates `x` or its complement to `y` or its complement by `≤`: it is an arrow
from a polarity of the first argument to a polarity of the second. -/

/-- An atomic constraint between two elements ([icard-2012] Definition 1.2): the first, taken with
polarity `src`, is below the second taken with polarity `tgt`
(`Relation.Atom.holds_iff_smul_subset`). -/
structure Atom where
  /-- The polarity of the first argument. -/
  src : Polarity
  /-- The polarity of the second argument. -/
  tgt : Polarity
  deriving DecidableEq, Repr

namespace Atom

/-- `x ≤ y`. -/
@[match_pattern] abbrev le : Atom := ⟨.positive, .positive⟩

/-- `y ≤ x`, that is, `xᶜ ≤ yᶜ`. -/
@[match_pattern] abbrev ge : Atom := ⟨.negative, .negative⟩

/-- `x ⊓ y = ⊥`, that is, `x ≤ yᶜ`. -/
@[match_pattern] abbrev disjoint : Atom := ⟨.positive, .negative⟩

/-- `x ⊔ y = ⊤`, that is, `xᶜ ≤ y`. -/
@[match_pattern] abbrev codisjoint : Atom := ⟨.negative, .positive⟩

instance : Fintype Atom :=
  ⟨{le, ge, disjoint, codisjoint}, by rintro ⟨_ | _, _ | _⟩ <;> decide⟩

/-- The constraint between `x` and `z` that a constraint between `x` and `y` and one between `y`
and `z` guarantee: the composite arrow, when the polarities of `y` agree
(`Relation.Atom.Holds.join`). -/
def join (a b : Atom) : Option Atom :=
  if a.tgt = b.src then some ⟨a.src, b.tgt⟩ else none

end Atom

/-! ### Relations as partial bijections of the polarities -/

/-- A relation as a partial bijection of the two polarities, sending the polarity of the first
argument to the polarity of the second that it is below: `≡` is the identity, `^` exchanges the
polarities, `#` is nowhere defined, and each of the other four is a single arrow. -/
def toPEquiv : Relation → (Polarity ≃. Polarity)
  | .equiv => PEquiv.refl Polarity
  | .forward => PEquiv.single .positive .positive
  | .reverse => PEquiv.single .negative .negative
  | .negation => (Equiv.mulLeft Polarity.negative).toPEquiv
  | .alternation => PEquiv.single .positive .negative
  | .cover => PEquiv.single .negative .positive
  | .independent => ⊥

/-- The relation of a partial bijection of the polarities. -/
def ofPEquiv (f : Polarity ≃. Polarity) : Relation :=
  match f .positive, f .negative with
  | some .positive, some .negative => .equiv
  | some .negative, some .positive => .negation
  | some .positive, none => .forward
  | none, some .negative => .reverse
  | some .negative, none => .alternation
  | none, some .positive => .cover
  | _, _ => .independent

@[simp] theorem ofPEquiv_toPEquiv : ∀ R : Relation, ofPEquiv R.toPEquiv = R := by decide

@[simp] theorem toPEquiv_ofPEquiv (f : Polarity ≃. Polarity) : (ofPEquiv f).toPEquiv = f := by
  sorry

/-- The seven relations are the partial bijections of the two polarities. -/
def equivPEquiv : Relation ≃ (Polarity ≃. Polarity) where
  toFun := toPEquiv
  invFun := ofPEquiv
  left_inv := ofPEquiv_toPEquiv
  right_inv := toPEquiv_ofPEquiv

theorem toPEquiv_injective : Function.Injective toPEquiv := equivPEquiv.injective

/-- The atomic constraints a relation asserts, the arrows of its partial bijection
(`Relation.mem_constraints_iff`): `{le, ge}` for `≡`, `{disjoint, codisjoint}` for `^` and `∅` for
`#`. A relation holds iff all its constraints do (`Relation.holds_iff`). -/
def constraints : Relation → Finset Atom
  | .equiv => {.le, .ge}
  | .forward => {.le}
  | .reverse => {.ge}
  | .negation => {.disjoint, .codisjoint}
  | .alternation => {.disjoint}
  | .cover => {.codisjoint}
  | .independent => ∅

theorem mem_constraints_iff : ∀ {R : Relation} {a : Atom},
    a ∈ R.constraints ↔ R.toPEquiv a.src = some a.tgt := by
  decide

theorem constraints_injective : Function.Injective constraints := by decide

/-- The strongest relation all of whose constraints satisfy `P`, found by trying the relations
from the strongest down to `#`, which has none. When the atoms satisfying `P` are the constraints
of a relation, it is that relation. -/
def ofAtoms (P : Atom → Prop) [DecidablePred P] : Relation :=
  ([equiv, negation, forward, reverse, alternation, cover].find?
    (fun R ↦ ∀ a ∈ R.constraints, P a)).getD independent

/-- In the implication order ([icard-2012]'s ≪), `R ≤ R'` iff `xRy` entails `xR'y`, i.e. iff the
partial bijection of `R` extends that of `R'` (`Relation.Holds.of_le`). It consists of two diamonds
sharing only the top `#`, one with `≡` below `⊑` and `⊒`, the other with `^` below `|` and `⌣`;
there is no bottom, since a partial bijection of two points has two maximal extensions. The most
informative relation, which [icard-2012] calls ≪-maximal, is the least one in this order. -/
instance : PartialOrder Relation :=
  .lift (fun R ↦ OrderDual.toDual R.toPEquiv) (OrderDual.toDual.injective.comp toPEquiv_injective)

theorem le_iff_toPEquiv_le {R R' : Relation} : R ≤ R' ↔ R'.toPEquiv ≤ R.toPEquiv := Iff.rfl

theorem le_iff {R R' : Relation} :
    R ≤ R' ↔ constraints R' ⊆ constraints R := by
  sorry

instance : DecidableLE Relation := fun _ _ ↦
  decidable_of_iff _ le_iff.symm

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

@[simp] theorem toPEquiv_top : (⊤ : Relation).toPEquiv = ⊥ := rfl

/-- The join `R ⋈ R'` ([icard-2012], Lemma 1.5) is the strongest relation guaranteed between `x`
and `z` given `xRy` and `yR'z`: the composite of the two partial bijections, which chains each
constraint of `R` with each constraint of `R'` on the same polarity of `y`
(`Relation.mem_constraints_mul`). [maccartney-manning-2009] call it join after the database
operation; it is not the lattice join. On a Boolean algebra it is relational composition
(`Relation.holds_mul` in `Logic/Natural/Completeness.lean`), the middle term ranging over all
elements; [maccartney-manning-2009]'s relations exclude `⊥` and `⊤` and each other, and their
composition is a union of relations in 17 of the 49 cells. -/
def join (R S : Relation) : Relation := ofPEquiv (R.toPEquiv.trans S.toPEquiv)

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

@[simp] theorem toPEquiv_mul (R S : Relation) :
    (R * S).toPEquiv = R.toPEquiv.trans S.toPEquiv := toPEquiv_ofPEquiv _

@[simp] theorem toPEquiv_one : (1 : Relation).toPEquiv = PEquiv.refl Polarity := rfl

theorem mem_constraints_mul {R S : Relation} {c : Atom} :
    c ∈ (R * S).constraints ↔ ∃ a ∈ R.constraints, ∃ b ∈ S.constraints, a.join b = some c := by
  revert R S c
  decide

/-- The relations form a monoid under ⋈ with identity `≡`, the monoid of partial bijections of the
two polarities. The identity and absorption laws are printed in [icard-2012] (p. 710);
associativity is printed in neither [icard-2012] nor [maccartney-manning-2009]. The monoid is not
commutative, since `^ ⋈ ⌣ = ⊑` but `⌣ ⋈ ^ = ⊒`. -/
instance : Monoid Relation where
  mul_assoc R S T := toPEquiv_injective <| by simp only [toPEquiv_mul, PEquiv.trans_assoc]
  one_mul R := toPEquiv_injective <| by simp only [toPEquiv_mul, toPEquiv_one, PEquiv.refl_trans]
  mul_one R := toPEquiv_injective <| by simp only [toPEquiv_mul, toPEquiv_one, PEquiv.trans_refl]

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

/-- The converse reverses the join. -/
theorem converse_mul (R S : Relation) : (R * S).converse = S.converse * R.converse := by
  sorry

/-- The converse reverses each arrow and negates both of its polarities, `x ≤ y` being
`yᶜ ≤ xᶜ`. -/
theorem toPEquiv_converse (R : Relation) :
    R.converse.toPEquiv = ((Equiv.mulLeft Polarity.negative).toPEquiv.trans R.toPEquiv.symm).trans
      (Equiv.mulLeft Polarity.negative).toPEquiv := by
  sorry

/-- Chaining on the left is monotone. -/
instance : MulLeftMono Relation := ⟨by sorry⟩

/-- Chaining on the right is monotone. -/
instance : MulRightMono Relation := ⟨by sorry⟩

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

theorem Relation.holds_converse {α : Type*} [Lattice α] [BoundedOrder α] {R : Relation}
    {x y : α} : R.converse.Holds x y ↔ R.Holds y x := by
  cases R with
  | equiv => exact eq_comm
  | forward | reverse | independent => exact Iff.rfl
  | negation => exact ⟨IsCompl.symm, IsCompl.symm⟩
  | alternation => exact disjoint_comm
  | cover => exact codisjoint_comm

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
  obtain ⟨s, t⟩ := a
  obtain ⟨s', t'⟩ := b
  unfold Relation.Atom.join at h
  split_ifs at h with hst
  obtain rfl : t = s' := hst
  obtain rfl := Option.some.inj h
  cases s <;> cases t <;> cases t' <;> first
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
