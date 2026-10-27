module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Order.Basic

/-!
# Chatzikyriakidis & Luo (2017): On the interpretation of common nouns

Montague semantics interprets common nouns as predicates over a single type of entities, while the
semantics of modern type theories, following Ranta, interprets them as types. The chapter argues
that only types are compatible with the subtyping that copredication needs, as in "John picked up
and mastered three books in the library". It turns judgements such as "John is a man" into
propositions through a trivial predicate on each noun and a negation operator NOT governed by two
laws, and checks the account in Coq. Gradable nouns such as *idiot* are Σ-types indexed by degree,
which makes *small idiot* contradictory.

## Main definitions

* `p A`: the trivial predicate on the noun `A`, the propositional form of a judgement `a : A`.
* `NegOperator Obj`: a negation operator NOT satisfying the laws (L1) and (L2).
* `Idiot Human STND`: the gradable noun *idiot*, a Σ-type indexed by degree.

## Main statements

* `standardNeg Obj`: a model of the laws (L1) and (L2).
* `man_and_not_man`, `not_not_man`, `notll`, `nothl`, `not_human_not_man`: the chapter's Coq
  examples, proved from the laws.
* `no_aspect_map`: in general no map adds an informational aspect to a physical object.
* `small_idiot_contradictory`: no degree is both above and below the standard.

## Implementation notes

* A noun is an object `A` of `Over Obj`, a type `A.left` with an embedding `A.hom` into the type
  `Obj` of all objects, the chapter's top type. A coercion from `A` to `B` is a morphism
  `A ⟶ B` of `Over Obj`.
* The chapter introduces NOT through Coq parameters without exhibiting a model; `standardNeg` is
  our model.

## References

* [S. Chatzikyriakidis and Z. Luo, *On the Interpretation of Common Nouns: Types Versus
  Predicates* (2017)][chatzikyriakidis-luo-2017]
* [R. Montague, *The Proper Treatment of Quantification in Ordinary English*
  (1973)][montague-1973]
* [A. Ranta, *Type-Theoretical Grammar* (1994)][ranta-1994]
* [N. Asher, *Lexical Meaning in Context: A Web of Words* (2011)][asher-2011]
-/

@[expose] public section

namespace ChatzikyriakidisLuo2017

open CategoryTheory

universe u

variable {Obj : Type u}

@[simp]
theorem over_w_apply {A B : Over Obj} (s : A ⟶ B) (a : A.left) : B.hom (s.left a) = A.hom a :=
  types_congr_hom (Over.w s) a

/-- The trivial predicate on a noun, true of all its objects, the propositional form of a
judgement `a : A` (Definition 1). -/
def p (A : Over Obj) : A.left → Prop := fun _ ↦ True

/-- A negation operator NOT, saying that an object does not satisfy a predicate on a noun, with
the laws (L1) and (L2) for the trivial predicates. -/
structure NegOperator (Obj : Type u) where
  /-- The negation operator. -/
  not : (A : Over Obj) → (A.left → Prop) → Obj → Prop
  /-- An object of `A` does not satisfy `p A` exactly when it is not an `A`, law (L1). -/
  l1 : ∀ (A : Over Obj) (a : A.left), not A (p A) (A.hom a) ↔ ¬ p A a
  /-- What is not a `B` is not an `A`, along a coercion from `A` to `B`, law (L2). -/
  l2 : ∀ {A B : Over Obj}, (A ⟶ B) → ∀ c : Obj, not B (p B) c → not A (p A) c

/-- The predicate `P_A` of a hypothetical judgement, the negation of NOT at `p A`, as in "if John
is a student, he is happy" (Definition 2). -/
def NegOperator.bigP (N : NegOperator Obj) (A : Over Obj) (o : Obj) : Prop :=
  ¬ N.not A (p A) o

/-- The operator under which an object does not satisfy `P` when no object of `A` located at it
does. -/
def standardNeg (Obj : Type u) : NegOperator Obj where
  not A P o := ∀ a, A.hom a = o → ¬ P a
  l1 _ a := iff_of_false (fun h ↦ h a rfl trivial) (fun h ↦ h trivial)
  l2 s _ hB a ha _ := hB (s.left a) ((over_w_apply s a).trans ha) trivial

/-! ### The Coq examples

Each theorem is one of the chapter's Coq examples, proved from the laws of NOT. -/

section Examples

variable (N : NegOperator Obj) (Man Human Linguist Logician Table : Over Obj)

/-- "John is a man and John is not a man" is contradictory ((25)–(27)). -/
theorem man_and_not_man (j : Man.left) : ¬ (p Man j ∧ N.not Man (p Man) (Man.hom j)) :=
  fun ⟨_, hn⟩ ↦ (N.l1 Man j).mp hn trivial

/-- It is not the case that John, a man, is not a man ((34)–(36)). -/
theorem not_not_man (j : Man.left) : ¬ N.not Man (p Man) (Man.hom j) :=
  fun h ↦ (N.l1 Man j).mp h trivial

-- (31), (33)
theorem tables_dont_talk_red (Red : Obj → Prop) (talk : Human.left → Prop)
    (h : ∀ x : Table.left, N.not Human talk (Table.hom x)) :
    ∀ y : {x : Table.left // Red (Table.hom x)}, N.not Human talk (Table.hom y.1) :=
  fun y ↦ h y.1

/-- "It is not the case that every linguist is a logician" entails "some linguist is not a
logician" ((47)–(49)). -/
theorem notll (h : ¬ ∀ l : Linguist.left, N.bigP Logician (Linguist.hom l)) :
    ∃ l : Linguist.left, N.not Logician (p Logician) (Linguist.hom l) := by
  obtain ⟨l, hl⟩ := not_forall.mp h
  exact ⟨l, not_not.mp hl⟩

/-- "Not every linguist is a logician" entails "not every human is a logician", along a
coercion from linguists to humans ((50)–(52)). -/
theorem nothl (s : Linguist ⟶ Human)
    (h : ¬ ∀ l : Linguist.left, N.bigP Logician (Linguist.hom l)) :
    ¬ ∀ x : Human.left, N.bigP Logician (Human.hom x) :=
  fun hall ↦ h fun l ↦ over_w_apply s l ▸ hall (s.left l)

/-- "If John is not a human, then John is not a man", which is law (L2) ((53)–(55)). -/
theorem not_human_not_man (s : Man ⟶ Human) (c : Obj) (h : N.not Human (p Human) c) :
    N.not Man (p Man) c :=
  N.l2 s c h

theorem some_man_walks (s : Man ⟶ Human) (walk : Human.left → Prop) (j : Man.left)
    (h : walk (s.left j)) : ∃ x : Man.left, walk (s.left x) :=
  ⟨j, h⟩

end Examples

/-! ### Copredication

Interpreting *book* as a predicate over the dot type `Phy • Info` would need `Phy ≤ Phy • Info`,
the wrong direction. With nouns as types, `Book ≤ Phy • Info` gives both aspects of a book. -/

section Copredication

variable {Phy Info Book : Type*}

/-- When some physical object exists and no informational one does, no map adds an informational
aspect to a physical object (§2.2). -/
theorem no_aspect_map (hp : Nonempty Phy) (hi : IsEmpty Info) : IsEmpty (Phy → Phy × Info) :=
  ⟨fun f ↦ hp.elim fun x ↦ hi.false (f x).2⟩

/-- The copredication "picked up and mastered" of a book, through its physical and informational
aspects (5). -/
def copredication (toPhy : Book → Phy) (toInfo : Book → Info) (pickUp : Phy → Prop)
    (master : Info → Prop) (b : Book) : Prop :=
  pickUp (toPhy b) ∧ master (toInfo b)

end Copredication

/-! ### Gradable nouns

Nouns may be families indexed by degrees (58), whose order the chapter axiomatizes as a dense
linear order. -/

section Grades

variable {Idiocy : Type*} [LinearOrder Idiocy]

/-- An idiot is a human together with an idiocy degree above the standard (62). -/
structure Idiot (Human : Idiocy → Type*) (STND : Idiocy) where
  /-- The idiocy degree. -/
  degree : Idiocy
  /-- The human indexed at that degree. -/
  human : Human degree
  /-- The degree exceeds the standard. -/
  above : STND < degree

/-- No degree is both above and below the standard, so *small idiot* is contradictory. -/
theorem small_idiot_contradictory (STND : Idiocy) : ¬ ∃ i : Idiocy, STND < i ∧ i < STND :=
  fun ⟨_, h1, h2⟩ ↦ lt_asymm h1 h2

end Grades

end ChatzikyriakidisLuo2017
