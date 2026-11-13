module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Case frames

This file defines the case frame of a verb, the case of its subject and the cases of its objects
in their unmarked linear order, over the cases of a language: nominative–dative–accusative for
Icelandic *gefa* 'give'. A case frame records which cases the arguments bear and nothing of where
they come from. Which cases a verb assigns lexically and which fall out of the configuration is
what accounts of case disagree about, and each study states its own.

## Main definitions

* `Verb.CaseFrame`: the subject's case and the objects' cases
* `Verb.CaseFrame.cases`: the case frame as a list
* `Verb.CaseFrame.argumentFrame`: the argument frame whose core arguments bear the cases

## References

* [zaenen-maling-thrainsson-1985]
* [thrainsson-2007]
-/

@[expose] public section

/-- A verb's case frame records the case of its subject and the cases of its objects in their
unmarked linear order, the cases being those of the language, `C`. -/
structure Verb.CaseFrame (C : Type*) where
  /-- The subject bears this case. -/
  subject : C
  /-- The objects bear these cases, in linear order. -/
  objects : List C := []
  deriving DecidableEq, Repr

namespace Verb.CaseFrame

variable {C : Type*} (a : CaseFrame C)

/-- `a.cases` lists the subject's case, then the objects'. -/
def cases : List C := a.subject :: a.objects

@[simp] theorem length_cases : a.cases.length = a.objects.length + 1 := rfl

/-- The argument frame whose core arguments bear the cases of `a`: a nominal subject and a
nominal complement for each object. -/
def argumentFrame : ArgumentFrame := ⟨some .nominal, a.objects.map fun _ ↦ .nominal⟩

@[simp] theorem external_argumentFrame : a.argumentFrame.external = some .nominal := rfl

@[simp] theorem complements_argumentFrame :
    a.argumentFrame.complements = a.objects.map fun _ ↦ .nominal := rfl

/-- Every slot of the argument frame is a core argument, the subject first. -/
theorem coreSlots_argumentFrame :
    a.argumentFrame.coreSlots = .external :: (List.range a.objects.length).map .complement := by
  have hs : a.argumentFrame.slots = .external :: (List.range a.objects.length).map .complement := by
    simp [ArgumentFrame.slots]
  rw [ArgumentFrame.coreSlots, hs, List.filter_eq_self]
  intro s hs'
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hs'
  rcases hs' with rfl | ⟨i, hi, rfl⟩
  · simp [ArgumentFrame.get?]; rfl
  · simp [ArgumentFrame.get?, hi]; rfl

/-- The core arguments of the argument frame are as many as the cases. -/
@[simp] theorem valency_argumentFrame : a.argumentFrame.valency = a.cases.length := by
  simp [ArgumentFrame.valency, coreSlots_argumentFrame]

/-- The core objects of the argument frame are as many as the objects' cases. -/
@[simp] theorem length_coreObjects_argumentFrame :
    a.argumentFrame.coreObjects.length = a.objects.length := by
  rw [ArgumentFrame.coreObjects, coreSlots_argumentFrame, List.filter_cons_of_neg (by simp),
    List.filter_eq_self.2 (by simp)]
  simp

end Verb.CaseFrame
