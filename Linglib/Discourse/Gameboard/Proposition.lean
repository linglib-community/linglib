module

public import Mathlib.Data.PFun
public import Linglib.Semantics.Questions.Answerhood

/-!
# Austinian propositions

In Ginzburg's theory of dialogue, KoS, a proposition pairs a situation with a situation type and
is true when the situation is of the type. Situation types come in positive and negative pairs:
the dual `Tᶜ` of a type `T` classifies the situations of some type incompatible with `T`, so no
situation is of both, and a situation that settles nothing about `T` is of neither. The negation
of a proposition is the proposition of the same situation and the dual type.

Whether a situation is of a type is relative to a possibility, and one proposition entails
another when it cannot be that the first is true and the second is not: the possibilities in
which the first is true are among those in which the second is. A proposition is about a
question when it entails a disjunction of two simple answers to it, where a disjunction is true
when one of its disjuncts is.

When every situation is of each type or of its dual, the negation of a proposition is true
exactly where the proposition is not, and every proposition is about every question that has an
instantiation.

## Main definitions

* `Gameboard.Austinian`: a situation paired with a situation type.
* `Gameboard.Austinian.truthSet`: the possibilities in which a proposition is true.
* `Gameboard.IsExclusive`, `Gameboard.IsBivalent`: no situation is of a type and of its dual;
  every situation is of a type or of its dual.
* `Gameboard.About`: a proposition entails a disjunction of two simple answers to a question.

## Main results

* `Gameboard.disjoint_truthSet_compl`: a proposition and its negation are true in no common
  possibility.
* `Gameboard.truthSet_compl`: under bivalence the negation of a proposition is true exactly
  where the proposition is not.
* `Gameboard.about_of_isBivalent`: under bivalence every proposition is about every question
  that has an instantiation.

## Implementation notes

* Situations, situation types and possibilities are parameters, and the typing judgement is a
  relation `ofType : M → Sit → Ty → Prop`. Records and record types, of which situations and
  situation types are instances in the source, are not represented.
* The disjunction of two propositions is not constructed: its situation depends on which
  disjunct is true. Only its truth condition is used, that one of the disjuncts is true.
* The source derives exclusivity from its definition of dual types through incompatible types;
  here it is the hypothesis `IsExclusive`.

## References

* [ginzburg-2012]
-/

@[expose] public section

namespace Gameboard

variable {Sit Ty M R : Type*}

/-- An Austinian proposition pairs a situation with a situation type ([ginzburg-2012] (16a)). -/
@[ext]
structure Austinian (Sit Ty : Type*) where
  /-- The situation. -/
  sit : Sit
  /-- The situation type. -/
  sitType : Ty

namespace Austinian

/-- The negation of a proposition is the proposition of the same situation and the dual type. -/
instance [Compl Ty] : Compl (Austinian Sit Ty) :=
  ⟨fun p ↦ ⟨p.sit, p.sitTypeᶜ⟩⟩

@[simp] theorem sit_compl [Compl Ty] (p : Austinian Sit Ty) : pᶜ.sit = p.sit := rfl

@[simp] theorem sitType_compl [Compl Ty] (p : Austinian Sit Ty) : pᶜ.sitType = p.sitTypeᶜ := rfl

/-- The possibilities in which a proposition is true: those in which its situation is of its
type ([ginzburg-2012] (16b)). -/
def truthSet (ofType : M → Sit → Ty → Prop) (p : Austinian Sit Ty) : Set M :=
  {m | ofType m p.sit p.sitType}

@[simp] theorem mem_truthSet {ofType : M → Sit → Ty → Prop} {p : Austinian Sit Ty} {m : M} :
    m ∈ p.truthSet ofType ↔ ofType m p.sit p.sitType :=
  Iff.rfl

end Austinian

variable [Compl Ty] (ofType : M → Sit → Ty → Prop) {p : Austinian Sit Ty}
  {q : R →. Austinian Sit Ty}

/-- No situation is of a type and of its dual ([ginzburg-2012] (41c)). -/
def IsExclusive : Prop :=
  ∀ m s T, ofType m s T → ¬ofType m s Tᶜ

/-- Every situation is of each type or of its dual, which fails of the situations that settle
nothing about a type ([ginzburg-2012] (40c)). -/
def IsBivalent : Prop :=
  ∀ m s T, ofType m s T ∨ ofType m s Tᶜ

/-- `p` is about `q` when it entails a disjunction of two simple answers to `q`: in every
possibility in which `p` is true, one of the two is. -/
def About (p : Austinian Sit Ty) (q : R →. Austinian Sit Ty) : Prop :=
  p.truthSet ofType ∈
    Answerhood.about (Austinian.truthSet ofType '' Answerhood.simpleAnswers q.ran)

variable {ofType}

theorem about_iff : About ofType p q ↔
    ∃ a ∈ Answerhood.simpleAnswers q.ran, ∃ b ∈ Answerhood.simpleAnswers q.ran,
      p.truthSet ofType ⊆ a.truthSet ofType ∪ b.truthSet ofType := by
  simp [About, Answerhood.mem_about]

/-- A proposition that entails a simple answer to `q` is about `q`. -/
theorem about_of_subset {a : Austinian Sit Ty} (ha : a ∈ Answerhood.simpleAnswers q.ran)
    (h : p.truthSet ofType ⊆ a.truthSet ofType) : About ofType p q :=
  about_iff.mpr ⟨a, ha, a, ha, h.trans Set.subset_union_left⟩

/-- A proposition and its negation are true in no common possibility. -/
theorem disjoint_truthSet_compl (h : IsExclusive ofType) :
    Disjoint (p.truthSet ofType) (pᶜ.truthSet ofType) :=
  Set.disjoint_left.mpr fun m hm ↦ h m _ _ hm

/-- Under bivalence the negation of a proposition is true exactly where the proposition is
not. -/
theorem truthSet_compl (he : IsExclusive ofType) (hb : IsBivalent ofType) :
    pᶜ.truthSet ofType = (p.truthSet ofType)ᶜ :=
  Set.ext fun m ↦ ⟨fun hm hp ↦ he m _ _ hp hm, fun hm ↦ (hb m p.sit p.sitType).resolve_left hm⟩

/-- Under bivalence every proposition is about every question that has an instantiation. -/
theorem about_of_isBivalent (hb : IsBivalent ofType) (h : q.ran.Nonempty) : About ofType p q := by
  obtain ⟨a, ha⟩ := h
  refine about_iff.mpr ⟨a, Answerhood.subset_simpleAnswers ha, aᶜ,
    Answerhood.compl_mem_simpleAnswers ha, fun m _ ↦ hb m a.sit a.sitType⟩

end Gameboard
