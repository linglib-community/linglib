module

public import Studies.ChatzikyriakidisLuo2017
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Order.Setoid.Basic

/-!
# Chatzikyriakidis & Luo (2020): Formal semantics in modern type theories

In the formal semantics of modern type theories, common nouns are interpreted as types rather than
predicates, and subtyping is coercive: one noun is a subtype of another when a unique coercion
between them may be inserted wherever an object of the second is expected. A noun modified by a
predicate is the Σ-type of its objects satisfying the predicate, a subtype of the noun through
the first projection. This file formalizes the book's classification of adjectival modification,
its operator NOT for the propositional forms of judgements, and its identity criteria for counting.

The book's Theorem 7.1 states that the laws (A1)–(A5) of NOT are provable once NOT is defined from
the heterogeneous equality JMeq. We show that with Lean's heterogeneous equality, which validates
the rules of JMeq, (A1) and (A2) hold but (A3), (A4) and (A5) fail at every proper finite Σ-subtype,
such as the men among the humans. With heterogeneous equality read as equality in a common
carrier, all five laws hold.

## Main definitions

* `sigma A P`: the Σ-type of the objects of `A` satisfying `P`, a subtype of `A` by `sigmaFst A P`.
* `DoesNot A P B b`: the operator NOT, from which `Is` and `Does` define IS and DO.
* `TypeDisjoint A B`: no inhabited noun is a subtype of both `A` and `B`.
* `SubSetoid A B sA sB`: `A` is a subtype of `B` whose identity criterion `sA` is inherited
  from `sB`.

## Main statements

* `range_sigma_comp`: intersective modification meets the noun's extension with the adjective's.
* `not_forall_nonempty_hom_sigma`: subsective modification need not respect subtyping.
* `forall_does_iff_mono`: law (A1) holds on a noun exactly when its embedding is a monomorphism.
* `not_doesNot_comp_heq`, `not_forall_doesNot_of_sub_heq`, `not_exists_doesNot_of_sub_heq`: laws
  (A3), (A4) and (A5) fail for `HEq`.
* `three₀_iff_two_lt_card`: three objects distinct under an identity criterion satisfy a predicate
  exactly when more than two of its identity classes do.

## Implementation notes

* As in [chatzikyriakidis-luo-2017], a noun is an object of `Over Obj`, a type embedded in a type
  `Obj` of all objects, and a coercion is a morphism of `Over Obj`. The book's universe has no such
  `Obj`; here it supplies the heterogeneous equality, under which two objects are equal when their
  images are. This equality identifies an object with its image under a coercion, the axiom that
  [xue-luo-chatzikyriakidis-2018] add to prove (A3)–(A5).
* Coercions are morphisms rather than `Coe` instances, so that statements quantify over nouns.
* By propositional extensionality every modal collection `Prop → Prop` respects logical
  equivalence, the property for which the book rejects the belief contexts of [ranta-1994].

## TODO

* Gradable, multidimensional and adverbial modification.
* Dot-types for copredication, and counting under copredication.
* Negative occurrences (Definition 7.2) and dependent event types.
* A universe without the type `Obj`, with coercions along a directed order.

## References

* [S. Chatzikyriakidis and Z. Luo, *Formal Semantics in Modern Type Theories*
  (2020)][chatzikyriakidis-luo-2020]
* [S. Chatzikyriakidis and Z. Luo, *On the Interpretation of Common Nouns: Types Versus
  Predicates* (2017)][chatzikyriakidis-luo-2017]
* [T. Xue, Z. Luo and S. Chatzikyriakidis, *Propositional Forms of Judgemental Interpretations*
  (2018)][xue-luo-chatzikyriakidis-2018]
* [H. Kamp, *Two theories about adjectives* (1975)][kamp-1975]
* [B. H. Partee, *Privative adjectives: Subsective plus coercion* (2010)][partee-2010]
* [A. Ranta, *Type-Theoretical Grammar* (1994)][ranta-1994]
-/

@[expose] public section

namespace ChatzikyriakidisLuo2020

open CategoryTheory TypeCat ChatzikyriakidisLuo2017

universe u

variable {Obj : Type u}

/-! ### Σ-types and coercive subtyping -/

/-- The Σ-type of the objects of `A` satisfying `P`, located through `A` ((2.41), (3.21)). -/
def sigma (A : Over Obj) (P : A.left → Prop) : Over Obj :=
  Over.mk (↾fun x : {x // P x} ↦ A.hom x.1)

/-- The first projection, which makes a modified noun a subtype of the noun ((2.42), (3.33)). -/
def sigmaFst (A : Over Obj) (P : A.left → Prop) : sigma A P ⟶ A :=
  Over.homMk (↾Subtype.val)

/-- A Σ-type embeds injectively when its noun does, since by proof irrelevance two of its objects
are equal when their first projections are (p. 69). -/
instance mono_sigma_hom (A : Over Obj) (P : A.left → Prop) [Mono A.hom] : Mono (sigma A P).hom :=
  (mono_iff_injective _).2 fun _ _ h ↦ Subtype.ext ((mono_iff_injective A.hom).1 ‹_› h)

variable {A B C : Over Obj}

-- p. 40
theorem subsingleton_hom [Mono B.hom] : Subsingleton (A ⟶ B) :=
  ⟨fun s t ↦ Over.OverMorphism.ext ((cancel_mono B.hom).1 ((Over.w s).trans (Over.w t).symm))⟩

theorem mono_left [Mono A.hom] (s : A ⟶ B) : Mono s.left :=
  mono_of_mono_fac (Over.w s)

/-! ### Adjectival modification -/

/-- Intersective modification respects subtyping, so a black cat is a black object (3.91). -/
def sigmaMap (s : A ⟶ B) (adj : Obj → Prop) :
    sigma A (adj ∘ A.hom) ⟶ sigma B (adj ∘ B.hom) :=
  Over.homMk (↾fun x ↦ ⟨s.left x.1, by simpa using x.2⟩) (by ext x; exact over_w_apply s x.1)

/-- The extension of an intersectively modified noun is the meet of the noun's extension with the
adjective's, the intersective class of [kamp-1975] ((3.92)–(3.97)). -/
theorem range_sigma_comp (A : Over Obj) (adj : Obj → Prop) :
    Set.range (sigma A (adj ∘ A.hom)).hom =
      Modifier.intersective {o | adj o} (Set.range A.hom) := by
  ext o
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨ha, a, rfl⟩
  · rintro ⟨ho, a, rfl⟩
    exact ⟨⟨a, ho⟩, rfl⟩

/-- Since the instances of a Π-polymorphic adjective at two nouns are unrelated, a subtyping
need not lift to the modified nouns (3.101). -/
theorem not_forall_nonempty_hom_sigma :
    ¬ ∀ (A B : Over Bool) (_ : A ⟶ B) (adj : (C : Over Bool) → C.left → Prop),
      Nonempty (sigma A (adj A) ⟶ sigma B (adj B)) := fun h ↦ by
  obtain ⟨s⟩ := h (Over.mk (↾fun _ : PUnit ↦ true)) (Over.mk (𝟙 Bool))
    (Over.homMk (↾fun _ ↦ true)) (fun C _ ↦ Subsingleton C.left)
  exact Bool.noConfusion ((s.left ⟨PUnit.unit, ⟨fun _ _ ↦ rfl⟩⟩).2.elim true false)

section Privative

/-! Privative adjectives are subsective over the disjoint union of real and fake guns, as
[partee-2010] proposes. -/

/-- The disjoint union of two nouns, as in the type of guns `G = G_R + G_F` (3.110). -/
def sum (A B : Over Obj) : Over Obj := Over.mk (↾Sum.elim A.hom B.hom)

variable {GR GF : Over Obj}

/-- A gun is real when it comes from the real guns (3.111). -/
def IsReal : (sum GR GF).left → Prop := Sum.elim (fun _ ↦ True) (fun _ ↦ False)

/-- A gun is fake when it comes from the fake guns (3.112). -/
def IsFake : (sum GR GF).left → Prop := Sum.elim (fun _ ↦ False) (fun _ ↦ True)

-- (3.120)
theorem isReal_or_isFake (g : (sum GR GF).left) : IsReal g ∨ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

-- p. 71
theorem isReal_iff_not_isFake (g : (sum GR GF).left) : IsReal g ↔ ¬ IsFake g := by
  cases g <;> simp [IsReal, IsFake]

-- (3.121)
theorem not_isReal_sigmaFst (f : (sigma (sum GR GF) IsFake).left) :
    ¬ IsReal ((sigmaFst (sum GR GF) IsFake).left f) :=
  (isReal_iff_not_isFake f.1).1.mt (not_not_intro f.2)

-- p. 72
theorem disjoint_range_isFake [Mono (sum GR GF).hom] :
    Disjoint (Set.range (sigma (sum GR GF) IsFake).hom)
      (Set.range (sigma (sum GR GF) IsReal).hom) := by
  rw [Set.disjoint_left]
  rintro _ ⟨f, rfl⟩ ⟨r, hr⟩
  have h : r.1 = f.1 := (mono_iff_injective (sum GR GF).hom).1 ‹_› hr
  exact (isReal_iff_not_isFake f.1).1 (h ▸ r.2) f.2

end Privative

/-! ### Propositional forms of judgements -/

/-- The operator NOT, read "`b` does not `P`", defined from heterogeneous equality as equality of
images in `Obj` ((7.5), (7.11)). -/
def DoesNot (A : Over Obj) (P : A.left → Prop) (B : Over Obj) (b : B.left) : Prop :=
  ∀ x, A.hom x = B.hom b → ¬ P x

/-- The operator IS, the propositional form of the judgement that `y` is an `X` (7.7). -/
def Is (X : Over Obj) (y : B.left) : Prop := ¬ DoesNot X (p X) B y

/-- The operator DO, the propositional form of applying `P` to `y` (7.9). -/
def Does (P : A.left → Prop) (y : B.left) : Prop := ¬ DoesNot A P B y

theorem does_iff {P : A.left → Prop} {y : B.left} :
    Does P y ↔ ∃ x, A.hom x = B.hom y ∧ P x := by
  simp [Does, DoesNot]

theorem is_iff {y : B.left} : Is A y ↔ ∃ x, A.hom x = B.hom y := by
  simp [Is, DoesNot, p]

-- p. 64
theorem is_self (a : A.left) : Is A a := is_iff.2 ⟨a, rfl⟩

/-- Law (A1) holds on a noun exactly when its embedding is a monomorphism (p. 153). -/
theorem forall_does_iff_mono : (∀ (P : A.left → Prop) x, Does P x ↔ P x) ↔ Mono A.hom := by
  rw [mono_iff_injective]
  refine ⟨fun h x y hxy ↦ (h (· = y) x).1 (does_iff.2 ⟨y, hxy.symm, rfl⟩), fun hA P x ↦ ?_⟩
  rw [does_iff]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ hA hy ▸ hP, fun hP ↦ ⟨x, rfl, hP⟩⟩

theorem doesNot_mono {P Q : A.left → Prop} (h : ∀ x, P x → Q x) (y : B.left)
    (hQ : DoesNot A Q B y) : DoesNot A P B y :=
  fun x hx hP ↦ hQ x hx (h x hP)

theorem doesNot_comp (s : A ⟶ B) (P : B.left → Prop) (z : C.left)
    (h : DoesNot B P C z) : DoesNot A (P ∘ s.left) C z :=
  fun x hx ↦ h (s.left x) ((over_w_apply s x).trans hx)

theorem forall_doesNot_of_hom (s : A ⟶ B) (P : C.left → Prop)
    (h : ∀ y, DoesNot C P B y) (x : A.left) : DoesNot C P A x :=
  fun w hw ↦ h (s.left x) w (hw.trans (over_w_apply s x).symm)

theorem exists_doesNot_of_hom (s : A ⟶ B) (P : C.left → Prop)
    (h : ∃ x, DoesNot C P A x) : ∃ y, DoesNot C P B y :=
  let ⟨x, hx⟩ := h
  ⟨s.left x, fun w hw ↦ hx w (hw.trans (over_w_apply s x))⟩

-- p. 154
theorem is_of_hom (s : A ⟶ B) {z : C.left} (h : Is A z) : Is B z :=
  fun hB ↦ h (doesNot_comp s (p B) z hB)

theorem standardNeg_not_iff (P : A.left → Prop) (b : B.left) :
    (standardNeg Obj).not A P (B.hom b) ↔ DoesNot A P B b :=
  Iff.rfl

/-- Two nouns are disjoint when no inhabited noun is a subtype of both (Definition 7.1). -/
def TypeDisjoint (A B : Over Obj) : Prop :=
  ∀ C : Over Obj, (C ⟶ A) → (C ⟶ B) → IsEmpty C.left

-- (3.66), (3.71)
theorem typeDisjoint_iff : TypeDisjoint A B ↔ ∀ b : B.left, ¬ Is A b := by
  refine ⟨fun h b hb ↦ ?_, fun h C s t ↦ ⟨fun c ↦ h (t.left c) (is_iff.2 ⟨s.left c, ?_⟩)⟩⟩
  · obtain ⟨a, ha⟩ := is_iff.1 hb
    exact (h (Over.mk (↾fun _ : PUnit.{u + 1} ↦ B.hom b))
      (Over.homMk (↾fun _ ↦ a) (by ext; exact ha)) (Over.homMk (↾fun _ ↦ b))).false PUnit.unit
  · exact (over_w_apply s c).trans (over_w_apply t c).symm

-- (3.5), (3.7)
theorem isEmpty_hom_of_typeDisjoint (h : TypeDisjoint A B) [Nonempty A.left] : IsEmpty (A ⟶ B) :=
  ⟨fun s ↦ (h A (𝟙 A) s).false (Classical.arbitrary _)⟩

/-- An object is an alleged `M` when someone's collection of allegations contains that it is an
`M` (3.125). -/
def Alleged {Hum : Over Obj} (H : Hum.left → Prop → Prop) (M : Over Obj) (x : Hum.left) : Prop :=
  ∃ h, H h (Is M x)

-- (3.122)
theorem alleged_noncommittal {Hum M : Over Obj} {x y : Hum.left} (hx : ¬ Is M x) (hy : Is M y) :
    (∃ H, Alleged H M x ∧ ¬ Is M x) ∧ ∃ H, Alleged H M y ∧ Is M y :=
  ⟨⟨fun _ _ ↦ True, ⟨x, trivial⟩, hx⟩, ⟨fun _ q ↦ q, ⟨y, hy⟩, hy⟩⟩

/-! ### NOT with Lean's heterogeneous equality -/

section HEq

/-- The operator NOT defined as in (7.11), with `HEq` for JMeq. -/
def HDoesNot {A B : Type} (P : A → Prop) (b : B) : Prop := ∀ x : A, HEq x b → ¬ P x

theorem not_hDoesNot_self_iff {A : Type} {P : A → Prop} {x : A} : ¬ HDoesNot P x ↔ P x := by
  simp only [HDoesNot, not_forall, not_not, exists_prop]
  exact ⟨fun ⟨y, hy, hP⟩ ↦ eq_of_heq hy ▸ hP, fun hP ↦ ⟨x, HEq.rfl, hP⟩⟩

theorem hDoesNot_mono {A B : Type} {P Q : A → Prop} (h : ∀ x, P x → Q x) {y : B}
    (hQ : HDoesNot Q y) : HDoesNot P y :=
  fun x hx hP ↦ hQ x hx (h x hP)

theorem hDoesNot_of_ne {A B : Type} (h : A ≠ B) (P : A → Prop) (b : B) : HDoesNot P b :=
  fun _ hx ↦ (h (type_eq_of_heq hx)).elim

variable {α : Type} [Fintype α] {M : α → Prop} [DecidablePred M]

theorem subtype_ne (h : ∃ a, ¬ M a) : {a // M a} ≠ α := fun e ↦ by
  obtain ⟨a, ha⟩ := h
  exact (Fintype.card_subtype_lt ha).ne (Fintype.card_congr (Equiv.cast e))

/-- Law (A3) fails for `HDoesNot` at a proper finite Σ-subtype, such as the men among the humans. -/
theorem not_doesNot_comp_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (P : α → Prop) (C : Type) (z : C),
      HDoesNot P z → HDoesNot (P ∘ Subtype.val : {a // M a} → Prop) z :=
  fun h3 ↦ not_hDoesNot_self_iff.2 trivial
    (h3 (fun _ ↦ True) _ m (hDoesNot_of_ne (subtype_ne h).symm _ m))

/-- Law (A4) fails for `HDoesNot` at a proper finite Σ-subtype. -/
theorem not_forall_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∀ y : α, HDoesNot P y) → ∀ x : {a // M a}, HDoesNot P x :=
  fun h4 ↦ not_hDoesNot_self_iff.2 trivial
    (h4 _ (fun _ ↦ True) (hDoesNot_of_ne (subtype_ne h) _) m)

/-- Law (A5) fails for `HDoesNot` at a proper finite Σ-subtype. -/
theorem not_exists_doesNot_of_sub_heq (h : ∃ a, ¬ M a) (m : {a // M a}) :
    ¬ ∀ (C : Type) (P : C → Prop), (∃ x : {a // M a}, HDoesNot P x) → ∃ y : α, HDoesNot P y :=
  fun h5 ↦
    let ⟨_, hy⟩ := h5 α (fun _ ↦ True) ⟨m, hDoesNot_of_ne (subtype_ne h).symm _ m⟩
    not_hDoesNot_self_iff.2 trivial hy

theorem not_heq_val (h : ∃ a, ¬ M a) (x : {a // M a}) : ¬ HEq x x.1 :=
  fun hx ↦ subtype_ne h (type_eq_of_heq hx)

end HEq

/-! ### Identity criteria and counting -/

section Setoid

/-- A sub-setoid is a subtype whose identity criterion is the restriction of the supertype's
(Definition 5.2). -/
structure SubSetoid (A B : Over Obj) (sA : Setoid A.left) (sB : Setoid B.left) where
  /-- The coercion from `A` to `B`. -/
  sub : A ⟶ B
  /-- The identity criterion of `A` is that of `B` restricted along the coercion. -/
  comap_eq : sA = Setoid.comap sub.left sB

/-- `Three₀ B sB P` holds when three objects of `B`, pairwise distinct under `sB`, satisfy `P`
(Definition 5.3). -/
def Three₀ (B : Over Obj) (sB : Setoid B.left) (P : B.left → Prop) : Prop :=
  ∃ x y z, ¬ sB x y ∧ ¬ sB y z ∧ ¬ sB x z ∧ P x ∧ P y ∧ P z

-- (5.26)
theorem three₀_of_subSetoid {sA : Setoid A.left} {sB : Setoid B.left}
    (h : SubSetoid A B sA sB) (P : B.left → Prop) (hA : Three₀ A sA (P ∘ h.sub.left)) :
    Three₀ B sB P := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩ := hA
  exact ⟨_, _, _, hxy, hyz, hxz, hx, hy, hz⟩

/-- For a predicate respecting the identity criterion, `Three₀` holds exactly when more than two
identity classes satisfy it (p. 110). -/
theorem three₀_iff_two_lt_card (sB : Setoid B.left) [Fintype B.left] [DecidableRel sB]
    (P : B.left → Prop) [DecidablePred P] (hP : ∀ x y, sB x y → (P x ↔ P y)) :
    Three₀ B sB P ↔
      2 < Fintype.card {q : Quotient sB // Quotient.lift P (fun x y h ↦ propext (hP x y h)) q} := by
  rw [Fintype.two_lt_card_iff]
  constructor
  · rintro ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩
    exact ⟨⟨⟦x⟧, hx⟩, ⟨⟦y⟧, hy⟩, ⟨⟦z⟧, hz⟩, fun e ↦ hxy (Quotient.exact (Subtype.mk.inj e)),
      fun e ↦ hxz (Quotient.exact (Subtype.mk.inj e)),
      fun e ↦ hyz (Quotient.exact (Subtype.mk.inj e))⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    induction c using Quotient.inductionOn with | h z => ?_
    exact ⟨x, y, z, fun e ↦ hab (by simp [Quotient.sound e]),
      fun e ↦ hbc (by simp [Quotient.sound e]), fun e ↦ hac (by simp [Quotient.sound e]),
      ha, hb, hc⟩

end Setoid

end ChatzikyriakidisLuo2020
