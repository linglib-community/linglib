module

public import Linglib.Core.Data.Fintype.Order
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.SuccPred.Basic
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Number.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# The φ-feature geometry

The morphosyntactic feature geometry of pronouns: monovalent person, number,
and class features organized as a dependency tree under a root Referring
Expression node, with Participant (Speaker, Addressee) and Individuation
(Group, Minimal with its dependent Augmented, and Class) as the organizing
nodes, with the collective first-person node Multispeaker below Speaker. A
feature appears only together with the nodes it depends on, so the
feature content of a pronoun is a lower set of the dominance order; markedness
is node count; and an organizing node with no dependent receives its default
daughter — Speaker, Minimal, Inanimate — by rule. Person and number cells are
assigned their geometries, the contrastive Minimal node being present only in
inventories that activate it. The tree is a feature geometry in the sense of
[clements-1985] and [sagey-1986] whose nodes are the features themselves, a
rooted tree in mathlib's terms: dominance the partial order, the root `⊥` and
the parent `Order.pred`.

## Main definitions

* `Node`, `Node.ancestors` and `Node.pred`, and dominance `≤`, the tree of the parent map
  with the root as `⊥`; `Node.below` is the content a node brings with it.
* `Node.defaultDependent?`, `fillDefaults`: the default daughters and their fill-in.
* `personNodes`, `numberNodes`, `cell`: the geometries of person, of number, and of
  a person–number cell, relative to an active inventory.
* `personFeatures`: the nodes a person bears, the root and default daughter included.
* `Licenses`: an inventory licenses a cell when the cell's geometry lies within it.

## Main results

* `cell_isLowerSet`: every assigned geometry is a lower set.
* `fillDefaults_isLowerSet`: default fill-in preserves lower sets.

## References

* [H. Harley and E. Ritter, *Person and number in pronouns: A feature-geometric
  analysis*][harley-ritter-2002]
* [H. Harley, *Hug a tree*][harley-1994]
* [M. McGinnis, *Agree and Fission in Georgian plurals*][mcginnis-2013]
* [G. N. Clements, *The geometry of phonological features*][clements-1985]
* [E. Sagey, *The representation of features and relations in non-linear
  phonology*][sagey-1986]
-/

@[expose] public section

namespace Phi.Geometry

/-- The nodes of the geometry are the root, the three organizing nodes, and
their dependents. -/
inductive Node where
  /-- The root is borne by every pronoun, and alone it is the third person. -/
  | referringExpression
  /-- Discourse participant marks the first and second person. -/
  | participant
  /-- Includes the speaker; Participant's default dependent. -/
  | speaker
  /-- Multispeaker includes the speaker and others, a collective first person expressing
  first-person plurality through person where number does not. -/
  | multispeaker
  /-- Includes the addressee. -/
  | addressee
  /-- Number and class. -/
  | individuation
  /-- Group marks more than one, the plural. -/
  | group
  /-- A minimal set; Individuation's default dependent, singular alone and dual
  together with Group. -/
  | minimal
  /-- Augmented marks a minimal group and more, the paucal or trial. -/
  | augmented
  /-- Gender and class. -/
  | nounClass
  /-- Animate. -/
  | animate
  /-- Inanimate or neuter; Class's default dependent. -/
  | inanimate
  /-- Feminine. -/
  | feminine
  /-- Masculine. -/
  | masculine
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The nodes a node depends on, nearest first, form the path from the node to the root. -/
def ancestors : Node → List Node
  | .referringExpression => []
  | .participant | .individuation => [.referringExpression]
  | .speaker | .addressee => [.participant, .referringExpression]
  | .multispeaker => [.speaker, .participant, .referringExpression]
  | .group | .minimal | .nounClass => [.individuation, .referringExpression]
  | .augmented => [.minimal, .individuation, .referringExpression]
  | .animate | .inanimate => [.nounClass, .individuation, .referringExpression]
  | .feminine | .masculine => [.animate, .nounClass, .individuation, .referringExpression]

/-- The node a node depends on directly, the root fixed. -/
def pred (n : Node) : Node := n.ancestors.head?.getD n

/-- `a ≤ b` when `b` depends on `a`, the dominance of the geometry: `a` is `b` or one of the nodes
`b` depends on. -/
instance : PartialOrder Node where
  le a b := a = b ∨ a ∈ b.ancestors
  le_refl := by decide
  le_trans := by decide +kernel
  le_antisymm := by decide

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a = b ∨ a ∈ b.ancestors))

instance : DecidableLT Node := decidableLTOfDecidableLE

/-- The root dominates every node. -/
instance : OrderBot Node where
  bot := .referringExpression
  bot_le := by decide

/-- The parent as the predecessor. -/
instance : PredOrder Node where
  pred := pred
  pred_le := by decide
  min_of_le_pred := by decide
  le_pred_of_lt := by decide

instance : LocallyFiniteOrder Node := Fintype.toLocallyFiniteOrder

theorem le_iff {a b : Node} : a ≤ b ↔ a = b ∨ a ∈ b.ancestors := Iff.rfl

/-- The nodes a node depends on, itself included and the root excluded, from the root down:
the content a privative feature brings with it. -/
def below (n : Node) : List Node := ((n :: n.ancestors).filter (· ≠ ⊥)).reverse

theorem mem_below : ∀ {a n : Node}, a ∈ below n ↔ ⊥ < a ∧ a ≤ n := by decide

theorem toFinset_below : ∀ n : Node, (below n).toFinset = Finset.Ioc ⊥ n := by decide

theorem below_subset_below : ∀ {a b : Node}, a ≤ b → below a ⊆ below b := by decide

/-- The default daughters of the organizing nodes are Speaker, Minimal, and Inanimate. -/
def defaultDependent? : Node → Option Node
  | .participant => some .speaker
  | .individuation => some .minimal
  | .nounClass => some .inanimate
  | _ => none

end Node

/-! ### Default fill-in -/

/-- Default fill-in gives an organizing node present without any dependent
its default daughter. The node count of a geometry is taken before
fill-in. -/
def fillDefaults (s : Finset Node) : Finset Node :=
  s ∪ Finset.univ.filter fun d => ∃ o ∈ s, o.defaultDependent? = some d ∧ ∀ c ∈ s, ¬ o < c

theorem subset_fillDefaults (s : Finset Node) : s ⊆ fillDefaults s := Finset.subset_union_left

theorem fillDefaults_isLowerSet {s : Finset Node} (hs : IsLowerSet (↑s : Set Node)) :
    IsLowerSet (↑(fillDefaults s) : Set Node) := by
  intro b a hab hb
  simp only [fillDefaults, Finset.mem_coe, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at hb ⊢
  rcases hb with hb | ⟨o, ho, hod, hno⟩
  · exact .inl (hs hab hb)
  · have key : ∀ o d x : Node, o.defaultDependent? = some d → x ≤ d → x = d ∨ x ≤ o := by
      decide +kernel
    rcases key o b a hod hab with rfl | hao
    · exact .inr ⟨o, ho, hod, hno⟩
    · exact .inl (hs hao ho)

/-! ### Person and number cells -/

/-- In the person geometries first person is the bare Participant node (Speaker
by default), exclusive Participant with Speaker, inclusive Participant with
Speaker and Addressee, second Participant with Addressee, third nothing. -/
def personNodes : Person → Finset Node
  | .first => {.participant}
  | .firstExclusive => {.participant, .speaker}
  | .firstInclusive => {.participant, .speaker, .addressee}
  | .second => {.participant, .addressee}
  | .third => ∅

/-- In the number geometries, relative to an active inventory, singular is the bare
Individuation node, with Minimal where the inventory activates it
contrastively; plural adds Group; dual Minimal with Group; paucal and trial add
Augmented; the number-neutral value is nothing. Greater numbers and the
minimal–augmented values have no geometry. -/
def numberNodes (active : Finset Node) : Number → Option (Finset Node)
  | .singular =>
    some (if Node.minimal ∈ active then {.individuation, .minimal} else {.individuation})
  | .plural => some {.individuation, .group}
  | .dual => some {.individuation, .minimal, .group}
  | .trial | .paucal => some {.individuation, .minimal, .group, .augmented}
  | .general => some ∅
  | _ => none

/-- The geometry of a person–number cell is the root with the person and number
nodes, the latter only in an inventory that activates Individuation. -/
def cell (active : Finset Node) (p : Person) (n : Number) : Option (Finset Node) := do
  let ns ← if Node.individuation ∈ active then numberNodes active n else pure ∅
  pure (insert .referringExpression (personNodes p ∪ ns))

/-- An inventory licenses a cell when the cell's geometry lies within it. -/
def Licenses (active : Finset Node) (p : Person) (n : Number) : Prop :=
  ∃ g ∈ cell active p n, g ⊆ active

instance (active : Finset Node) (p : Person) (n : Number) : Decidable (Licenses active p n) :=
  inferInstanceAs (Decidable (∃ g ∈ cell active p n, g ⊆ active))

theorem personNodes_isLowerSet (p : Person) :
    IsLowerSet (↑(insert ⊥ (personNodes p)) : Set Node) := by
  cases p <;> decide

/-- A person bears the root, the nodes of its person geometry, and the default daughter of a
bare Participant node, so that the first person bears Speaker. -/
def personFeatures (p : Person) : Finset Node := fillDefaults (insert ⊥ (personNodes p))

theorem bot_mem_personFeatures (p : Person) : ⊥ ∈ personFeatures p :=
  subset_fillDefaults _ (Finset.mem_insert_self _ _)

theorem personFeatures_isLowerSet (p : Person) : IsLowerSet (↑(personFeatures p) : Set Node) :=
  fillDefaults_isLowerSet (personNodes_isLowerSet p)

theorem numberNodes_isLowerSet {active : Finset Node} {n : Number} {ns : Finset Node}
    (h : numberNodes active n = some ns) : IsLowerSet (↑(insert ⊥ ns) : Set Node) := by
  cases n <;> simp [numberNodes] at h <;> (try split_ifs at h) <;> subst h <;> decide

theorem cell_isLowerSet {active : Finset Node} {p : Person} {n : Number} {g : Finset Node}
    (h : cell active p n = some g) : IsLowerSet (↑g : Set Node) := by
  simp only [cell, Option.bind_eq_bind, Option.pure_def] at h
  have key : ∀ ns : Finset Node, IsLowerSet (↑(insert ⊥ ns) : Set Node) →
      IsLowerSet (↑(insert Node.referringExpression (personNodes p ∪ ns)) : Set Node) :=
    fun ns hns ↦ by
      rw [show insert Node.referringExpression (personNodes p ∪ ns) =
          insert ⊥ (personNodes p) ∪ insert ⊥ ns by
        rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]; rfl, Finset.coe_union]
      exact (personNodes_isLowerSet p).union hns
  split_ifs at h <;> obtain ⟨ns, hns, hg⟩ := Option.bind_eq_some_iff.1 h <;> cases hg
  · exact key ns (numberNodes_isLowerSet hns)
  · cases hns; exact key ∅ (by decide)

end Phi.Geometry
