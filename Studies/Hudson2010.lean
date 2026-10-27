module

public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.DeriveFintype

/-!
# Hudson (2010): An Introduction to Word Grammar

This file formalizes the worked examples of Part I of [hudson-2010] on the default-inheritance
substrate `DefaultInheritance`. Default inheritance is the book's engine. An exemplar inherits every
property of the concepts above it in the isA taxonomy except those overridden lower down. So a
penguin exemplar inherits *lays eggs* from *bird* but *doesn't fly* from *penguin* (Figure 2.8,
`inherited_flight_e2`), and a diesel car exemplar runs on diesel rather than the default petrol
(Figure 3.18, `inherited_fuel_e`). The book's searcher climbs the taxonomy from the exemplar and
keeps the first answer it finds (Section 2.5.3). The substrate proves that this answer is an
inherited one for every climb that starts at the bottom
(`DefaultInheritance.mem_inherited_of_find?_eq_some`). Multiple inheritance can leave a conflict
with no recognized resolution, the Nixon diamond of Figure 2.7. Nixon inherits both *accepts war*
and *rejects war* as credulous conclusions and neither as a skeptical one (`inherited_war_nixon`,
`not_entails_war_nixon`), and the two climbs that visit his parents in opposite orders find
different answers (`search_war_nixon`). Nixon's own choice, a copy of *accepts war* at his node,
settles the conflict (`nixon_resolved`). Choice sets keep such conflicts from arising. No one is
both male and female, or both adult and child, so a property attached to the members of either
choice set is never inherited twice, although *man*, *boy*, *woman* and *girl* each inherit from two
concepts (Figure 3.9, `subsingleton_inherited_sex`, `subsingleton_inherited_age`).

Relational concepts are defined in terms of existing ones: *parent* merges *mother* and
*father*, *grandmother* is the mother of a parent, and *ancestor* is the recursive closure of
*parent* (Section 3.2.7, `ancestor`). The definition of *grandmother* is a relational
`Triangle`, one node's two relations converging on a third, and the same triangle is the
syntactic pattern of raising: an auxiliary's subject is also its valent's subject
(Figure 7.6). Closing the asserted subjects under the triangle along the valent chain
(`raise`) makes *he* the subject of every verb in *He keeps seeming to have forgotten to go*
(Figure 7.12, `he_subject_of_go`).

## Implementation notes

* A property is an attribute, a partial map from concepts to values, and two values compete when
  they are values of one attribute. The book's competition between links one of which isA the
  other (Section 3.5.3) is not modelled.
* Only exemplars inherit (Section 2.5). `DefaultInheritance.inherited` is defined at every
  concept, and the theorems query the exemplars.
* Each taxonomy is declared by its immediate isA links, and its order is their reflexive
  transitive closure (`partialOrderOfCovers`).
* The kinship system of Figure 8.16 is built from `mother` and `father` on an arbitrary type
  of people, with sex as predicates; the compositions are mathlib's `Relation.Comp` and
  `Relation.TransGen`.

## References

* [hudson-2010]
-/

@[expose] public section

namespace Hudson2010

open DefaultInheritance

/-! ### Default inheritance -/

/-- The concepts of Figure 2.8: birds, the typical sparrow, the exceptional penguin, and an
exemplar of each. -/
inductive Bird where
  | bird
  | sparrow
  | penguin
  | e1
  | e2
  deriving DecidableEq, Fintype

/-- The concepts each concept of Figure 2.8 immediately isA. -/
def Bird.parents : Bird → List Bird
  | .bird => []
  | .sparrow | .penguin => [.bird]
  | .e1 => [.sparrow]
  | .e2 => [.penguin]

/-- The depth of a concept below *bird*. -/
def Bird.rank : Bird → ℕ
  | .bird => 0
  | .sparrow | .penguin => 1
  | .e1 | .e2 => 2

instance : PartialOrder Bird :=
  partialOrderOfCovers (fun a b : Bird ↦ b ∈ a.parents) Bird.rank (by decide)

instance : DecidableLE Bird :=
  decidableLEOfCovers (covers := fun a b : Bird ↦ b ∈ a.parents) [.bird, .sparrow, .penguin]
    (by decide)

/-- How a bird moves. -/
inductive Flight where
  | flies
  | doesntFly
  deriving DecidableEq

/-- How a bird reproduces. -/
inductive Reproduction where
  | laysEggs
  deriving DecidableEq

/-- Figure 2.8: birds fly, and penguins do not. -/
def flight : Bird → Option Flight
  | .bird => some .flies
  | .penguin => some .doesntFly
  | _ => none

/-- Figure 2.8: birds lay eggs. -/
def reproduction : Bird → Option Reproduction
  | .bird => some .laysEggs
  | _ => none

theorem e2_le_bird : Bird.e2 ≤ .bird := by decide

theorem sparrow_not_le_penguin : ¬ Bird.sparrow ≤ .penguin := by decide

theorem inherited_flight_e1 : inherited flight .e1 = {.flies} :=
  inherited_eq_singleton_of_isLeast (m := .bird) (by decide) rfl

/-- A penguin exemplar inherits *doesn't fly*, the lower of the competing properties
(Section 2.5.3). -/
theorem inherited_flight_e2 : inherited flight .e2 = {.doesntFly} :=
  inherited_eq_singleton_of_isLeast (m := .penguin) (by decide) rfl

theorem inherited_reproduction_e2 : inherited reproduction .e2 = {.laysEggs} :=
  inherited_eq_singleton_of_isLeast (m := .bird) (by decide) rfl

/-- The concepts of Figure 3.18: cars, the exceptional diesel car, and an exemplar of each. -/
inductive Car where
  | car
  | dieselCar
  | e
  | e'
  deriving DecidableEq, Fintype

/-- The concepts each concept of Figure 3.18 immediately isA. -/
def Car.parents : Car → List Car
  | .car => []
  | .dieselCar | .e' => [.car]
  | .e => [.dieselCar]

/-- The depth of a concept below *car*. -/
def Car.rank : Car → ℕ
  | .car => 0
  | .dieselCar | .e' => 1
  | .e => 2

instance : PartialOrder Car :=
  partialOrderOfCovers (fun a b : Car ↦ b ∈ a.parents) Car.rank (by decide)

instance : DecidableLE Car :=
  decidableLEOfCovers (covers := fun a b : Car ↦ b ∈ a.parents) [.car, .dieselCar] (by decide)

/-- A car's fuel. -/
inductive Fuel where
  | petrol
  | diesel
  deriving DecidableEq

/-- Figure 3.18: petrol is the default car fuel and diesel the exception. -/
def fuel : Car → Option Fuel
  | .car => some .petrol
  | .dieselCar => some .diesel
  | _ => none

theorem inherited_fuel_e : inherited fuel .e = {.diesel} :=
  inherited_eq_singleton_of_isLeast (m := .dieselCar) (by decide) rfl

theorem inherited_fuel_e' : inherited fuel .e' = {.petrol} :=
  inherited_eq_singleton_of_isLeast (m := .car) (by decide) rfl

/-! ### The Nixon diamond -/

/-- The concepts of Figure 2.7: Nixon is both a Republican and a Quaker. -/
inductive Person where
  | person
  | republican
  | quaker
  | nixon
  deriving DecidableEq, Fintype

/-- The concepts each concept of Figure 2.7 immediately isA. -/
def Person.parents : Person → List Person
  | .person => []
  | .republican | .quaker => [.person]
  | .nixon => [.republican, .quaker]

/-- The depth of a concept below *person*. -/
def Person.rank : Person → ℕ
  | .person => 0
  | .republican | .quaker => 1
  | .nixon => 2

instance : PartialOrder Person :=
  partialOrderOfCovers (fun a b : Person ↦ b ∈ a.parents) Person.rank (by decide)

instance : DecidableLE Person :=
  decidableLEOfCovers (covers := fun a b : Person ↦ b ∈ a.parents)
    [.person, .republican, .quaker] (by decide)

/-- A view of war. -/
inductive Stance where
  | accepts
  | rejects
  deriving DecidableEq

/-- Figure 2.7: Republicans accept war and Quakers reject it. -/
def war : Person → Option Stance
  | .republican => some .accepts
  | .quaker => some .rejects
  | _ => none

/-- Nixon inherits both views of war, each a credulous and neither a skeptical conclusion (Section
2.4.2). -/
theorem inherited_war_nixon : inherited war .nixon = {.accepts, .rejects} := by
  ext s
  cases s <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide

/-- Neither view of war is a skeptical conclusion: Nixon's specifiers preferentially entail
neither. -/
theorem not_entails_war_nixon (s : Stance) :
    {m | war m = some s} ∉
      OrderingSemantics.necessityFilter inferInstance (specifiers war .nixon) := by
  rw [mem_necessityFilter_iff_inherited_subset, inherited_war_nixon]
  cases s <;> simp

theorem search_war_nixon :
    ([Person.nixon, .republican, .quaker, .person].find? (· ∈ specifiers war .nixon)).bind war =
        some .accepts ∧
      ([Person.nixon, .quaker, .republican, .person].find? (· ∈ specifiers war .nixon)).bind war =
        some .rejects := by
  decide

/-- Nixon's resolution: a copy of *accepts war* at his own node wins (Section 2.4.2). -/
theorem nixon_resolved :
    inherited (Function.update war .nixon (some .accepts)) .nixon = {.accepts} :=
  inherited_eq_singleton_of_eq_some (by simp)

/-! ### Choice sets -/

/-- The concepts of Figure 3.9: a person is male or female and adult or child, and *man*,
*boy*, *woman* and *girl* are the four combinations. -/
inductive Human where
  | person
  | male
  | female
  | adult
  | child
  | man
  | boy
  | woman
  | girl
  deriving DecidableEq, Fintype

/-- The concepts each concept of Figure 3.9 immediately isA. -/
def Human.parents : Human → List Human
  | .person => []
  | .male | .female | .adult | .child => [.person]
  | .man => [.male, .adult]
  | .boy => [.male, .child]
  | .woman => [.female, .adult]
  | .girl => [.female, .child]

/-- The depth of a concept below *person*. -/
def Human.rank : Human → ℕ
  | .person => 0
  | .male | .female | .adult | .child => 1
  | .man | .boy | .woman | .girl => 2

instance : PartialOrder Human :=
  partialOrderOfCovers (fun a b : Human ↦ b ∈ a.parents) Human.rank (by decide)

instance : DecidableLE Human :=
  decidableLEOfCovers (covers := fun a b : Human ↦ b ∈ a.parents)
    [.person, .male, .female, .adult, .child] (by decide)

/-- The choice set *sex* of Figure 3.8. -/
def sex : Set Human := {.male, .female}

/-- The choice set *age* of Figure 3.9. -/
def age : Set Human := {.adult, .child}

-- Section 3.3.2
theorem pairwiseDisjoint_sex : sex.PairwiseDisjoint Set.Iic := by
  have h : ∀ x : Human, x ≤ .male → x ≤ .female → False := by decide
  rintro a (rfl | rfl) b (rfl | rfl) hne
  exacts [absurd rfl hne, Set.disjoint_left.2 fun x h₁ h₂ ↦ h x h₁ h₂,
    Set.disjoint_left.2 fun x h₁ h₂ ↦ h x h₂ h₁, absurd rfl hne]

theorem pairwiseDisjoint_age : age.PairwiseDisjoint Set.Iic := by
  have h : ∀ x : Human, x ≤ .adult → x ≤ .child → False := by decide
  rintro a (rfl | rfl) b (rfl | rfl) hne
  exacts [absurd rfl hne, Set.disjoint_left.2 fun x h₁ h₂ ↦ h x h₁ h₂,
    Set.disjoint_left.2 fun x h₁ h₂ ↦ h x h₂ h₁, absurd rfl hne]

/-- A property attached only to the members of the choice set *sex* is inherited at most once
(Section 2.4.3). -/
theorem subsingleton_inherited_sex {β : Type*} {att : Human → Option β}
    (h : ∀ m, (att m).isSome → m ∈ sex) (a : Human) : (inherited att a).Subsingleton :=
  subsingleton_inherited_of_pairwiseDisjoint (pairwiseDisjoint_sex.subset h)

theorem subsingleton_inherited_age {β : Type*} {att : Human → Option β}
    (h : ∀ m, (att m).isSome → m ∈ age) (a : Human) : (inherited att a).Subsingleton :=
  subsingleton_inherited_of_pairwiseDisjoint (pairwiseDisjoint_age.subset h)

/-! ### Relational concepts -/

section Kinship

variable {α : Type*} (mother father : α → α → Prop) (male female : α → Prop)

/-- Figure 8.16 (a): a person's parent is either their mother or their father. -/
def parent (x p : α) : Prop := mother x p ∨ father x p

/-- Figure 8.16 (b): a person's child is anyone whose parent they are. -/
def child (x c : α) : Prop := parent mother father c x

/-- Figure 3.7: a grandmother is the mother of a parent, a relational triangle. -/
def grandmother : α → α → Prop := Relation.Comp (parent mother father) mother

/-- Figure 3.17: a grandparent is a parent's parent. -/
def grandparent : α → α → Prop := Relation.Comp (parent mother father) (parent mother father)

-- Figure 3.17, Section 3.5.2
theorem comp_grandparent_parent :
    Relation.Comp (grandparent mother father) (parent mother father) =
      Relation.Comp (parent mother father)
        (Relation.Comp (parent mother father) (parent mother father)) :=
  Relation.comp_assoc

/-- Section 3.2.7: a person's ancestor is either their parent or an ancestor of their
parent, the recursive definition. -/
def ancestor : α → α → Prop := Relation.TransGen (parent mother father)

theorem ancestor_iff (x a : α) :
    ancestor mother father x a ↔
      parent mother father x a ∨ ∃ p, parent mother father x p ∧ ancestor mother father p a := by
  constructor
  · intro h
    obtain ⟨p, hxp, hpa⟩ := Relation.TransGen.head'_iff.1 h
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hpa with rfl | hpa
    · exact Or.inl hxp
    · exact Or.inr ⟨p, hxp, hpa⟩
  · rintro (h | ⟨p, hxp, hpa⟩)
    · exact Relation.TransGen.single h
    · exact Relation.TransGen.head hxp hpa

theorem ancestor_of_grandparent {x g : α} (h : grandparent mother father x g) :
    ancestor mother father x g :=
  let ⟨_, hxp, hpg⟩ := h
  Relation.TransGen.head hxp (Relation.TransGen.single hpg)

/-- Figure 8.16 (c): brothers and sisters are the sons and daughters of a parent. -/
def brother (x b : α) : Prop := Relation.Comp (parent mother father) (child mother father) x b ∧
  male b ∧ x ≠ b

def sister (x s : α) : Prop := Relation.Comp (parent mother father) (child mother father) x s ∧
  female s ∧ x ≠ s

/-- Figure 8.16 (d): uncles and aunts are the brothers and sisters of a parent. -/
def uncle : α → α → Prop := Relation.Comp (parent mother father) (brother mother father male)

def aunt : α → α → Prop := Relation.Comp (parent mother father) (sister mother father female)

-- Figure 8.16
theorem uncle_of_parent_brother {x p u : α} (hp : parent mother father x p)
    (hb : brother mother father male p u) : uncle mother father male x u :=
  ⟨p, hp, hb⟩

end Kinship

/-! ### Triangles in kinship and in syntax -/

section Triangle

variable {α : Type*}

/-- The triangle of Figure 7.6: a node's `r₁` value and `r₂` value stand in `r₃`. -/
def Triangle (r₁ r₂ r₃ : α → α → Prop) : Prop := ∀ x y z, r₁ x y → r₂ x z → r₃ y z

theorem triangle_grandmother (mother father : α → α → Prop) :
    Triangle (child mother father) mother (grandmother mother father) :=
  fun x _ _ hc hm ↦ ⟨x, hc, hm⟩

variable (valent subj : α → α → Prop)

/-- Raising, the syntactic triangle: a word's subject is also its valent's subject. -/
def Raising : Prop := Triangle valent subj subj

/-- The subjects derived from the asserted ones by closing under the triangle along the
valent chain. -/
def raise (v s : α) : Prop := ∃ h, subj h s ∧ Relation.ReflTransGen valent h v

theorem subj_le_raise : ∀ x s, subj x s → raise valent subj x s :=
  fun x _ h ↦ ⟨x, h, Relation.ReflTransGen.refl⟩

theorem raising_raise : Raising valent (raise valent subj) :=
  fun _ _ _ hv ⟨h, hs, hchain⟩ ↦ ⟨h, hs, hchain.tail hv⟩

theorem raise_le_of_raising {S : α → α → Prop} (hS : Raising valent S)
    (hsubj : ∀ x s, subj x s → S x s) : ∀ v s, raise valent subj v s → S v s := by
  rintro v s ⟨h, hs, hchain⟩
  induction hchain with
  | refl => exact hsubj _ _ hs
  | tail _ hv ih => exact hS _ _ _ hv ih

-- Section 7.2.6, Figure 7.12
theorem raise_of_transGen {h v s : α} (hs : subj h s) (hchain : Relation.TransGen valent h v) :
    raise valent subj v s :=
  ⟨h, hs, hchain.to_reflTransGen⟩

end Triangle

/-! ### Figure 7.12 -/

/-- The words of *He keeps seeming to have forgotten to go*. -/
inductive W where
  | he
  | keeps
  | seeming
  | to₁
  | have
  | forgotten
  | to₂
  | go
  deriving DecidableEq, Repr

/-- The valent chain of Figure 7.12, each verb's valent the next. -/
def valent : W → W → Prop
  | .keeps, .seeming | .seeming, .to₁ | .to₁, .have | .have, .forgotten
  | .forgotten, .to₂ | .to₂, .go => True
  | _, _ => False

/-- The one asserted subject: *he* is the subject of *keeps*. -/
def asserted : W → W → Prop
  | .keeps, .he => True
  | _, _ => False

theorem he_subject_of_go : raise valent asserted .go .he := by
  refine ⟨.keeps, trivial, ?_⟩
  exact (((((Relation.ReflTransGen.refl.tail (c := W.seeming) trivial).tail (c := W.to₁)
    trivial).tail (c := W.have) trivial).tail (c := W.forgotten) trivial).tail (c := W.to₂)
    trivial).tail (c := W.go) trivial

end Hudson2010
