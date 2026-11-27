module

public import Linglib.Semantics.Dynamic.Possibility
public import Linglib.Core.Data.Set.Sups
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Basic.Rel
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Hom.Basic

/-!
# Information states

A hearer takes in a discourse one sentence at a time, and each sentence changes what she takes to be
the case. An **information state** models where she stands: the possibilities she has not yet ruled
out. In a discourse with pronouns a possibility has to say two things, how the world is and which
individuals the discourse referents stand for, so a state is a set of pairs of a world and an
assignment. This is Heim's **file**. The assignments are partial, since a referent that has not been
introduced has no value.

Take two worlds, *w*ₐ where only *a* is P and *w*₀ where nothing is, and the state {(*w*ₐ, [x ↦ a]),
(*w*ₐ, [x ↦ b]), (*w*₀, [ ])}, an example of Elliott's. It leaves open whether anything is P. Where
something is, x stands for *a* or for *b*; where nothing is, x has no value.

## Implementation notes

A state has no domain apart from its points, so at the absurd state every referent is both familiar
and novel. Heim's files keep their domain of cards apart from their satisfaction set, and a false
file still has cards; a result that needs a familiarity failure must assume its state nonempty.

The order has the more informed state lower, as inclusion of sets does. Kamp, van Genabith and Reyle
draw it the other way up, with the initial state at the bottom; the content is the same. Since two
states can each be as informed as the other without being equal, the order is a preorder.

## References

* [heim-1982]
* [groenendijk-stokhof-veltman-1996], Defs. 2.8 (extension) and 2.9 (descendants, subsistence)
* [groenendijk-stokhof-veltman-1996b]
* [kamp-vangenabith-reyle-2011]
* [elliott-2023]
* [elliott-sudo-2025]
* [visser-vermeulen-1996]
* [nouwen-brasoveanu-vaneijck-visser-2016]
-/

@[expose] public section

namespace DynamicSemantics

open scoped SetRel

variable {W V M : Type*}

/-!
### States and what they know

A state holds two kinds of information: its *worldly* information is the worlds of its points, and
its *anaphoric* information is their assignments. One state is at least as **informative** as
another when each of its points extends a point of the other, having ruled out worlds, or settled
more referents, or both. Groenendijk, Stokhof and Veltman call it an extension of the other.
-/

/-- An **information state** is a set of possibilities, that is, of world–assignment pairs. -/
def State (W V M : Type*) := Set (Possibility W V (Part M))

namespace State

variable {s s' t : State W V M} {p q r : Possibility W V (Part M)} {X Y : Set V}

@[reducible] instance : Membership (Possibility W V (Part M)) (State W V M) :=
  inferInstanceAs (Membership _ (Set _))

instance : HasSubset (State W V M) := ⟨fun s s' => ∀ ⦃p⦄, p ∈ s → p ∈ s'⟩

@[reducible] instance : EmptyCollection (State W V M) :=
  inferInstanceAs (EmptyCollection (Set _))

@[reducible] instance : Union (State W V M) :=
  ⟨fun s s' ↦ (s ∪ s' : Set (Possibility W V (Part M)))⟩

@[reducible] instance : Inter (State W V M) :=
  ⟨fun s s' ↦ (s ∩ s' : Set (Possibility W V (Part M)))⟩

@[reducible] instance : SDiff (State W V M) := inferInstanceAs (SDiff (Set _))

@[ext] theorem ext (h : ∀ p, p ∈ s ↔ p ∈ s') : s = s' :=
  Set.ext h

/-- A state lies below another in the order of informativeness, written `s ≤ s'`, when it is at
least as informative as the other. -/
instance : Preorder (State W V M) :=
  .lift (OrderDual.toDual ∘ upperClosure :
    State W V M → (UpperSet (Possibility W V (Part M)))ᵒᵈ)

/-- A state is at least as informative as another exactly when each of its points extends a point of
the other. -/
theorem le_def : s ≤ s' ↔ ∀ p ∈ s, ∃ q ∈ s', q ≤ p :=
  le_upperClosure

/-- The **initial state** knows nothing. It has every world, each paired with the assignment that
gives no referent a value. -/
instance : OrderTop (State W V M) where
  top := Set.range Possibility.bot
  le_top _ := le_def.mpr fun p _ => ⟨.bot p.world, ⟨p.world, rfl⟩, Possibility.bot_le⟩

theorem mem_top : r ∈ (⊤ : State W V M) ↔ ∀ v, r.assignment v = ⊥ :=
  ⟨fun ⟨_, hw⟩ _ => hw ▸ rfl, fun h =>
    ⟨r.world, Possibility.ext rfl (funext fun v => (h v).symm)⟩⟩

/-- The **absurd state** is empty, everything having been ruled out. It is the most informative
state. -/
instance : OrderBot (State W V M) where
  bot := ∅
  bot_le _ := le_def.mpr fun _ hq => hq.elim

@[simp] theorem bot_eq_empty : (⊥ : State W V M) = ∅ := rfl

theorem le_of_subset (h : s ⊆ s') : s ≤ s' :=
  le_def.mpr fun p hp ↦ ⟨p, h hp, le_rfl⟩

theorem eq_empty_of_le_bot (h : s ≤ ⊥) : s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp ↦ let ⟨_, hq, _⟩ := le_def.mp h p hp; hq.elim

/-!
### Subsistence

Introducing a referent replaces a point by its extensions, one for each value the referent may take,
so the point itself is gone from the new state. Groenendijk, Stokhof and Veltman call an extension
of it in the new state a *descendant*, and say that the point **subsists** when it has one.
Elliott's negative update of an existential is stated with subsistence.
-/

/-!
### Merging states

Two states **merge** into the state of their unifications: a point of each, in the same world, with
assignments that agree wherever both are defined. Merging pools what the two states know.
-/

/-- The **merge** of two states, written `s * s'`, is the set of the unifications of a point of the
one with a point of the other. -/
instance : Mul (State W V M) := ⟨Set.lubs⟩

/-- Merging with the initial state changes nothing. -/
instance : One (State W V M) := ⟨⊤⟩

theorem one_eq_top : (1 : State W V M) = ⊤ := rfl

theorem mem_mul : r ∈ s * s' ↔ ∃ p ∈ s, ∃ q ∈ s', IsLUB {p, q} r := Iff.rfl

instance : CommMonoid (State W V M) where
  mul_assoc := Set.lubs_assoc
  one_mul s := Set.ext fun r ↦
    ⟨fun ⟨_, ⟨w, rfl⟩, p, hp, h⟩ ↦
      have hw : Possibility.bot w ≤ p := Possibility.bot_le_of_compat (Compat.symm ⟨r, h.1⟩)
      h.unique (isLUB_pair_iff_forall_le.2 ⟨hw, le_rfl, fun _ _ hu ↦ hu⟩) ▸ hp,
     fun hr ↦ ⟨_, ⟨r.world, rfl⟩, r, hr,
      isLUB_pair_iff_forall_le.2 ⟨Possibility.bot_le, le_rfl, fun _ _ hu ↦ hu⟩⟩⟩
  mul_one s := Set.ext fun r ↦
    ⟨fun ⟨p, hp, _, ⟨w, rfl⟩, h⟩ ↦
      have hw : Possibility.bot w ≤ p := Possibility.bot_le_of_compat ⟨r, h.1⟩
      h.unique (isLUB_pair_iff_forall_le.2 ⟨le_rfl, hw, fun _ hu _ ↦ hu⟩) ▸ hp,
     fun hr ↦ ⟨r, hr, _, ⟨r.world, rfl⟩,
      isLUB_pair_iff_forall_le.2 ⟨le_rfl, Possibility.bot_le, fun _ hu _ ↦ hu⟩⟩⟩
  mul_comm := Set.lubs_comm

@[simp] theorem empty_mul : (∅ : State W V M) * s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hr ↦ let ⟨_, hp, _⟩ := mem_mul.mp hr; Set.notMem_empty _ hp

@[simp] theorem mul_empty : s * (∅ : State W V M) = ∅ := by rw [mul_comm, empty_mul]

theorem upperClosure_mul :
    upperClosure (s * s') = upperClosure s ⊔ upperClosure s' :=
  Set.upperClosure_lubs s s'

theorem mul_le_left : s * s' ≤ s :=
  le_sup_left.trans_eq upperClosure_mul.symm

theorem mul_le_right : s * s' ≤ s' :=
  le_sup_right.trans_eq upperClosure_mul.symm

theorem le_mul (h : t ≤ s) (h' : t ≤ s') : t ≤ s * s' :=
  upperClosure_mul.trans_le (sup_le h h')

theorem isGLB_mul : IsGLB {s, s'} (s * s') :=
  ⟨by rintro x (rfl | rfl); exacts [mul_le_left, mul_le_right],
   fun _ hu => le_mul (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-- Merging more informative states gives a more informative state. -/
instance : CovariantClass (State W V M) (State W V M) (· * ·) (· ≤ ·) :=
  ⟨fun _ _ _ h => le_mul mul_le_left (mul_le_right.trans h)⟩

/-!
### Union

The union of two states keeps only what they have in common. In the order of informativeness it is
the least upper bound, as merge is the greatest lower bound. Among states that define the same
referents merge is intersection, the eliminative update of propositional update semantics.
-/

theorem upperClosure_union :
    upperClosure (s ∪ s') = upperClosure s ⊓ upperClosure s' :=
  _root_.upperClosure_union _ _

theorem left_le_union : s ≤ s ∪ s' :=
  upperClosure_union.trans_le inf_le_left

theorem right_le_union : s' ≤ s ∪ s' :=
  upperClosure_union.trans_le inf_le_right

theorem union_le (h : s ≤ t) (h' : s' ≤ t) : s ∪ s' ≤ t :=
  (le_inf h h').trans_eq upperClosure_union.symm

theorem isLUB_union : IsLUB {s, s'} (s ∪ s') :=
  ⟨by rintro x (rfl | rfl); exacts [left_le_union, right_le_union],
   fun _ hu => union_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))⟩

/-!
### States up to equivalence

Two states can be as informative as each other and differ, when one has a point the other only
extends. Identifying such states leaves the sets of possibilities closed under extension.
-/

/-- Up to informational equivalence, the states are the sets of possibilities closed under
extension, ordered by inclusion. -/
def antisymmetrizationOrderIso :
    Antisymmetrization (State W V M) (· ≤ ·) ≃o
      (UpperSet (Possibility W V (Part M)))ᵒᵈ where
  toFun := Quotient.lift (fun s : State W V M => OrderDual.toDual (upperClosure s))
    fun _ _ h => le_antisymm (α := (UpperSet _)ᵒᵈ) h.1 h.2
  invFun U := toAntisymmetrization (· ≤ ·)
    (↑(OrderDual.ofDual U) : Set (Possibility W V (Part M)))
  left_inv := by
    refine Quotient.ind fun s => Quotient.sound ?_
    have key : upperClosure ↑(upperClosure (s : Set (Possibility W V (Part M)))) =
        upperClosure (s : Set (Possibility W V (Part M))) :=
      SetLike.coe_injective (upperClosure _).upper'.upperClosure
    exact ⟨le_of_eq (α := UpperSet _) key.symm, le_of_eq (α := UpperSet _) key⟩
  right_inv U :=
    congrArg OrderDual.toDual (SetLike.coe_injective (OrderDual.ofDual U).upper'.upperClosure)
  map_rel_iff' {a b} := by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Iff.rfl

/-!
### Familiarity

Heim's familiarity is read off the partial assignments. In the example above x is neither familiar
nor novel: two points give it a value and one does not.
-/

/-- A referent is **familiar** at a state when every point gives it a value. -/
def Familiar (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, x ∈ p.domain

/-- A referent is **novel** at a state when no point gives it a value. -/
def Novel (s : State W V M) (x : V) : Prop :=
  ∀ p ∈ s, x ∉ p.domain

theorem Familiar.mono {s s' : State W V M} {x : V} (h : Familiar s' x) (hs : s ⊆ s') :
    Familiar s x := fun p hp => h p (hs hp)

theorem Novel.mono {s s' : State W V M} {x : V} (h : Novel s' x) (hs : s ⊆ s') :
    Novel s x := fun p hp => h p (hs hp)

theorem Familiar.of_le {x : V} (h : Familiar s x) (hs : s' ≤ s) : Familiar s' x := fun q hq ↦
  let ⟨p, hp, hpq⟩ := le_def.mp hs q hq
  Possibility.domain_mono hpq (h p hp)

theorem Familiar.mul_left {x : V} (h : Familiar s x) : Familiar (s * s') x :=
  h.of_le mul_le_left

theorem Familiar.mul_right {x : V} (h : Familiar s' x) : Familiar (s * s') x :=
  h.of_le mul_le_right

theorem Novel.mul {x : V} (h : Novel s x) (h' : Novel s' x) : Novel (s * s') x := by
  intro r hr
  obtain ⟨p, hp, q, hq, hr⟩ := mem_mul.mp hr
  rw [Possibility.domain_eq_of_isLUB hr]
  exact fun hx ↦ hx.elim (h p hp) (h' q hq)

/-!
### Strata

The states that define exactly the referents in a set *X* form a layer, with a least informative
member, the **stratum** at *X*. Merging with a state of that layer extends each point to *X* and
then keeps the extensions the state allows. These are the two clauses of Heim's rule for an atomic
formula, the one that adds cards and the one that filters.
-/

/-- The **stratum** at a set of referents is the state of all the possibilities that define exactly
those referents. -/
def stratum (X : Set V) : State W V M := {p | p.domain = X}

@[simp] theorem mem_stratum : p ∈ (stratum X : State W V M) ↔ p.domain = X := Iff.rfl

/-- A state is **uniform** at a set of referents when each of its points defines exactly those
referents. -/
def UniformAt (X : Set V) (s : State W V M) : Prop :=
  ∀ p ∈ s, Possibility.domain p = X

theorem uniformAt_iff_subset_stratum : UniformAt X s ↔ s ⊆ stratum X := Iff.rfl

theorem uniformAt_stratum : UniformAt X (stratum X : State W V M) := fun _ hp ↦ hp

theorem stratum_empty : (stratum ∅ : State W V M) = ⊤ :=
  ext fun _ ↦ by rw [mem_stratum, Possibility.domain_eq_empty_iff, mem_top]

theorem uniformAt_top : UniformAt ∅ (⊤ : State W V M) :=
  stratum_empty ▸ uniformAt_stratum

@[simp] theorem mul_stratum_empty : s * stratum ∅ = s := by
  rw [stratum_empty, ← one_eq_top, mul_one]

theorem mem_mul_stratum :
    r ∈ s * stratum X ↔ ∃ p ∈ s, p ≤ r ∧ r.domain = p.domain ∪ X := by
  rw [mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, hr⟩
    exact ⟨p, hp, (Possibility.isLUB_pair_iff.mp hr).1,
      by rw [Possibility.domain_eq_of_isLUB hr, mem_stratum.mp hq]⟩
  · rintro ⟨p, hp, hpr, hdom⟩
    refine ⟨p, hp, r.restrict X, ?_, Possibility.isLUB_restrict hpr hdom⟩
    show (r.restrict X).domain = X
    rw [Possibility.domain_restrict, hdom, Set.inter_eq_left.mpr Set.subset_union_right]

/-- **Extension** along a set of referents relates a point to the points that extend it and define
exactly its own referents and those of the set. -/
def extend (X : Set V) : SetRel (Possibility W V (Part M)) (Possibility W V (Part M)) :=
  {(a, b) | (a ≤ b) ∧ b.domain = a.domain ∪ X}

theorem mem_extend : p ~[extend X] q ↔ p ≤ q ∧ q.domain = p.domain ∪ X := Iff.rfl

theorem image_extend (s : State W V M) : (extend X).image s = s * stratum X :=
  Set.ext fun _ ↦ mem_mul_stratum.symm

theorem stratum_union : (stratum (X ∪ Y) : State W V M) = stratum X * stratum Y := by
  ext r
  rw [mem_mul_stratum, mem_stratum]
  constructor
  · intro hr
    have hX : (r.restrict X).domain = X := by
      rw [Possibility.domain_restrict, hr, Set.inter_eq_left.mpr Set.subset_union_left]
    exact ⟨r.restrict X, hX, Possibility.restrict_le, by rw [hX, hr]⟩
  · rintro ⟨p, hp, -, hdom⟩
    rw [hdom, mem_stratum.mp hp]

theorem mul_stratum_eq_self (h : ∀ p ∈ s, X ⊆ p.domain) : s * stratum X = s := by
  ext r
  rw [mem_mul_stratum]
  constructor
  · rintro ⟨p, hp, hpr, hdom⟩
    rw [Set.union_eq_left.mpr (h p hp)] at hdom
    exact Possibility.eq_of_le_of_domain_eq hpr hdom.symm ▸ hp
  · exact fun hr ↦ ⟨r, hr, le_rfl, (Set.union_eq_left.mpr (h r hr)).symm⟩

theorem familiar_mul_stratum {x : V} (hx : x ∈ X) : Familiar (s * stratum X) x := fun r hr ↦ by
  obtain ⟨_, _, _, hdom⟩ := mem_mul_stratum.mp hr
  show x ∈ r.domain
  rw [hdom]
  exact Set.mem_union_right _ hx

theorem Familiar.mul_stratum_singleton {x : V} (h : Familiar s x) : s * stratum {x} = s :=
  mul_stratum_eq_self fun p hp ↦ Set.singleton_subset_iff.mpr (h p hp)

theorem mul_eq_sep_of_uniformAt (hs' : UniformAt X s') :
    s * s' = {r ∈ s * stratum X | r.restrict X ∈ s'} := by
  ext r
  rw [mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, hr⟩
    refine ⟨mem_mul.mpr ⟨p, hp, q, hs' q hq, hr⟩, ?_⟩
    rwa [← (Possibility.le_iff_eq_restrict (hs' q hq)).mp (Possibility.isLUB_pair_iff.mp hr).2.1]
  · rintro ⟨hr, hq⟩
    obtain ⟨p, hp, hpr, hdom⟩ := mem_mul_stratum.mp hr
    exact ⟨p, hp, _, hq, Possibility.isLUB_restrict hpr hdom⟩

theorem UniformAt.isAntichain (hs : UniformAt X s) :
    IsAntichain (· ≤ ·) (s : Set (Possibility W V (Part M))) :=
  fun p hp q hq hne hpq =>
    hne (Possibility.eq_of_le_of_domain_eq hpq ((hs p hp).trans (hs q hq).symm))

theorem UniformAt.mul_eq_inter (hs : UniformAt X s) (hs' : UniformAt X s') :
    s * s' = s ∩ s' := by
  rw [mul_eq_sep_of_uniformAt hs', mul_stratum_eq_self fun p hp ↦ (hs p hp).symm.subset]
  exact ext fun r ↦ and_congr_right fun hr ↦ by
    rw [Possibility.restrict_eq_self (hs r hr)]

/-- The **restriction** of a state to a set of referents forgets, at each point, the values of the
referents outside the set. -/
def restrict (X : Set V) (s : State W V M) : State W V M :=
  Possibility.restrict X '' s

theorem mem_restrict : p ∈ s.restrict X ↔ ∃ q ∈ s, q.restrict X = p :=
  Iff.rfl

theorem UniformAt.restrict_eq (hs : UniformAt X s) : s.restrict X = s :=
  ext fun p =>
    ⟨fun ⟨q, hq, hqp⟩ => (hqp.symm.trans (Possibility.restrict_eq_self (hs q hq))) ▸ hq,
     fun hp => ⟨p, hp, Possibility.restrict_eq_self (hs p hp)⟩⟩

theorem mem_lowerClosure_iff_mem_restrict (hp : p.domain = X) :
    p ∈ lowerClosure s ↔ p ∈ s.restrict X :=
  ⟨fun ⟨q, hq, hpq⟩ => ⟨q, hq, ((Possibility.le_iff_eq_restrict hp).mp hpq).symm⟩,
   fun ⟨q, hq, hqp⟩ => ⟨q, hq, hqp ▸ Possibility.restrict_le⟩⟩

theorem UniformAt.mem_upperClosure_iff_restrict_mem (hs : UniformAt X s) :
    q ∈ upperClosure s ↔ q.restrict X ∈ s :=
  ⟨fun ⟨p, hp, hpq⟩ => (Possibility.le_iff_eq_restrict (hs p hp)).mp hpq ▸ hp,
   fun h => ⟨q.restrict X, h, Possibility.restrict_le⟩⟩

theorem UniformAt.mem_lowerClosure (hs : UniformAt X s) (hp : p.domain = X) :
    p ∈ lowerClosure s ↔ p ∈ s :=
  (mem_lowerClosure_iff_mem_restrict hp).trans (by rw [hs.restrict_eq])

theorem UniformAt.lowerClosure_le_iff (hs : UniformAt X s) (hs' : UniformAt X s') :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s' :=
  lowerClosure_le.trans (forall₂_congr fun p hp => hs'.mem_lowerClosure (hs p hp))

theorem UniformAt.mem_upperClosure (hs : UniformAt X s) (hq : q.domain = X) :
    q ∈ upperClosure s ↔ q ∈ s :=
  hs.mem_upperClosure_iff_restrict_mem.trans (by rw [Possibility.restrict_eq_self hq])

theorem UniformAt.le_iff_subset (hs : UniformAt X s) (hs' : UniformAt X s') :
    s ≤ s' ↔ s ⊆ s' :=
  le_def.trans (forall₂_congr fun p hp => hs'.mem_upperClosure (hs p hp))

section Fibred

theorem UniformAt.mul (hs : UniformAt X s) (hs' : UniformAt Y s') :
    UniformAt (X ∪ Y) (s * s') := by
  intro r hr
  obtain ⟨p, hp, q, hq, hr⟩ := mem_mul.mp hr
  rw [Possibility.domain_eq_of_isLUB hr, hs p hp, hs' q hq]

theorem UniformAt.lowerClosure_le_iff_restrict (hs : UniformAt X s) :
    lowerClosure s ≤ lowerClosure s' ↔ s ⊆ s'.restrict X :=
  lowerClosure_le.trans
    (forall₂_congr fun p hp => mem_lowerClosure_iff_mem_restrict (hs p hp))

theorem UniformAt.le_iff_restrict_subset (hs : UniformAt X s) :
    s' ≤ s ↔ s'.restrict X ⊆ s :=
  le_def.trans <|
    (forall₂_congr fun _ _ => hs.mem_upperClosure_iff_restrict_mem).trans
      Set.forall_mem_image.symm

end Fibred

theorem lowerClosure_restrict_le :
    lowerClosure (s.restrict X) ≤ lowerClosure s :=
  lowerClosure_le.mpr <|
    Set.forall_mem_image.mpr fun q hq => ⟨q, hq, Possibility.restrict_le⟩

theorem UniformAt.restrict (hs : UniformAt Y s) :
    UniformAt (X ∩ Y) (s.restrict X) := by
  rintro p ⟨q, hq, rfl⟩
  rw [Possibility.domain_restrict, hs q hq]

theorem restrict_restrict :
    (s.restrict Y).restrict X = s.restrict (X ∩ Y) := by
  ext p
  simp only [restrict]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, Possibility.restrict_restrict.symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, Possibility.restrict_restrict⟩

/-! ### States without referents -/

/-- The states uniform at a set of referents correspond one to one to the sets of pairs of a world
and a total assignment to those referents. -/
def uniformEquiv (X : Set V) :
    {I : State W V M // UniformAt X I} ≃ Set (W × (X → M)) :=
  (Equiv.Set.powerset {p : Possibility W V (Part M) | p.domain = X}).trans
    (Equiv.setCongr (Possibility.domainEquiv X))

@[simp] theorem mem_uniformEquiv {I : {I : State W V M // UniformAt X I}}
    {e : W × (X → M)} :
    e ∈ uniformEquiv X I ↔ ((Possibility.domainEquiv X).symm e).1 ∈ I.1 :=
  Set.mem_image_equiv

/-- With no referents a state is a set of worlds, and to be more informative is to be included in
the other, as in propositional update semantics. -/
def worldOrderIso : State W Empty M ≃o Set W where
  toEquiv := Equiv.setCongr (Possibility.worldEquiv W (Part M))
  map_rel_iff' {s t} := by
    have hu (s : State W Empty M) : UniformAt ∅ s := fun _ _ ↦ Set.eq_empty_of_isEmpty _
    exact (Set.image_subset_image_iff (Possibility.worldEquiv W (Part M)).injective).trans
      ((hu s).le_iff_subset (hu t)).symm

variable [DecidableEq V]

/-- **Random assignment** at a variable replaces each point by the points that differ from it only
in giving that variable a value, one for each individual. It is how an indefinite introduces its
referent. -/
def randomAssign (s : State W V M) (x : V) : State W V M :=
  {p | ∃ q ∈ s, ∃ m : M, p = q.update x (.some m)}

theorem familiar_randomAssign (s : State W V M) (x : V) :
    Familiar (s.randomAssign x) x := by
  rintro p ⟨q, -, m, rfl⟩
  simp

theorem Familiar.randomAssign {s : State W V M} {y : V} (h : Familiar s y) (x : V) :
    Familiar (s.randomAssign x) y := by
  rintro p ⟨q, hq, m, rfl⟩
  by_cases hyx : y = x
  · subst hyx; simp
  · simpa [Possibility.update, Function.update_of_ne hyx] using h q hq

theorem Novel.randomAssign {s : State W V M} {y : V} (h : Novel s y) {x : V} (hyx : y ≠ x) :
    Novel (s.randomAssign x) y := by
  rintro p ⟨q, hq, m, rfl⟩
  simpa [Possibility.update, Function.update_of_ne hyx] using h q hq

theorem randomAssign_le {s : State W V M} {x : V} (h : Novel s x) : s.randomAssign x ≤ s :=
  le_def.mpr fun _ ⟨p, hp, _, hq⟩ ↦ ⟨p, hp, hq ▸ Possibility.le_update_of_notMem (h p hp) _⟩

theorem Novel.mul_stratum_singleton {s : State W V M} {x : V} (h : Novel s x) :
    s * stratum {x} = s.randomAssign x := by
  ext r
  rw [mem_mul_stratum]
  constructor
  · rintro ⟨p, hp, hpr, hdom⟩
    rw [Set.union_singleton] at hdom
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (show x ∈ r.domain from hdom ▸ Set.mem_insert x _)
    exact ⟨p, hp, m, Possibility.eq_update_of_le hpr hdom (Part.eq_some_iff.2 hm)⟩
  · rintro ⟨p, hp, m, rfl⟩
    exact ⟨p, hp, Possibility.le_update_of_notMem (h p hp) _,
      by rw [Possibility.domain_update_some, Set.union_singleton]⟩

end State

end DynamicSemantics
