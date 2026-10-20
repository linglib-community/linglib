module

public import Linglib.Syntax.Voice.Basic
public import Mathlib.Data.Finset.Image

/-!
# Voice systems

A voice system is the finite set of a language's voices. Its symmetrical voices select which
participant is the pivot, the syntactically privileged term, without affecting the transitivity
of the construction, and the system is symmetrical when they select different pivots: binary
when each is a nuclear term, multiple when one is an oblique. Symmetrical voices do not exclude
others, so a symmetrical system may also have a passive, an applicative or a causative.

Of the four characteristics Erlewine, Levin and van Urk give an Austronesian-type voice system,
the privileged argument realized in one form or position whatever its function is
`Voice.pivot`, and verb morphology varying with its choice, obliques included, is `Voice.marker`
and `IsMultiple`; the extraction restriction to the pivot and the marking of non-pivot subjects
are recorded where a fragment states them.

## Main definitions

* `Voice.System`: a finite set of voices.
* `Voice.System.symmetrical`, `pivotRoles`: the symmetrical voices of a system, and the roles of
  the pivots of its voices.
* `Voice.System.IsSymmetrical`, `IsMultiple`, `IsEquipollent`: a symmetrical system, a multiple
  one, and one whose symmetrical voices are all coded.

## Main statements

* `Voice.System.symmetrical_insert_of_not_isSymmetrical`: a voice that is not symmetrical leaves
  the symmetrical voices of a system unchanged.
* `Voice.System.IsSymmetrical.mono`: a system containing a symmetrical one is symmetrical.

## Implementation notes

* Creissels reports two rival criteria for symmetry, equipollent marking (Himmelmann) and equal
  transitivity of all voices (Riesberg), and adopts the second. `Voice.IsSymmetrical` is the
  book's criterion and `IsEquipollent`, no symmetrical voice derived from an unmarked one, the
  first; Balinese separates them (`Studies/Creissels2024.lean`).
* A pivot is identified by its transitivity-related role, so the locative, conveyance and
  instrumental voices of Tagalog all select an X.

## References

* [creissels-2024]
* [erlewine-levin-van-urk-2017]
-/

@[expose] public section

namespace Voice

/-- A voice system is the finite set of a language's voices. -/
abbrev System := Finset Voice

namespace System

variable (S T : System) {v : Voice}

/-- The symmetrical voices of a system. -/
def symmetrical : System := S.filter Voice.IsSymmetrical

/-- The transitivity-related roles of the pivots of a system's voices. -/
def pivotRoles : Finset (Option TermRole) := S.image pivotRole

/-- A system is symmetrical when its symmetrical voices select two different pivots, coding the
selection of a participant as the pivot without affecting the transitivity of the construction
([creissels-2024] §8.1.7, §8.5). -/
def IsSymmetrical : Prop := S.symmetrical.pivotRoles.Nontrivial

/-- A symmetrical system is multiple when one of its symmetrical voices selects an oblique, and
binary when they select only nuclear terms ([creissels-2024] §8.5.1, §8.5.2). -/
def IsMultiple : Prop := S.IsSymmetrical ∧ some .X ∈ S.symmetrical.pivotRoles

/-- A system is equipollent when every symmetrical voice is coded, so that none is derived from
an unmarked one, the criterion for symmetry that [creissels-2024] §8.1.7 attributes to
Himmelmann and does not adopt. -/
def IsEquipollent : Prop := ∀ v ∈ S.symmetrical, v.IsCoded

instance : Decidable S.IsSymmetrical := inferInstanceAs (Decidable (Finset.Nontrivial _))
instance : Decidable S.IsMultiple := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable S.IsEquipollent := inferInstanceAs (Decidable (∀ _ ∈ _, _))

variable {S T}

@[simp] theorem mem_symmetrical : v ∈ S.symmetrical ↔ v ∈ S ∧ v.IsSymmetrical :=
  Finset.mem_filter

@[simp] theorem mem_pivotRoles {r : Option TermRole} :
    r ∈ S.pivotRoles ↔ ∃ v ∈ S, v.pivotRole = r :=
  Finset.mem_image

theorem symmetrical_mono : Monotone symmetrical := Finset.monotone_filter_left _

theorem pivotRoles_mono : Monotone pivotRoles := Finset.image_mono _

/-- A voice that is not symmetrical, such as a passive, an applicative or a causative, leaves the
symmetrical voices of a system unchanged ([creissels-2024] §8.5.3). -/
theorem symmetrical_insert_of_not_isSymmetrical (h : ¬ v.IsSymmetrical) :
    (insert v S).symmetrical = S.symmetrical :=
  (Finset.filter_insert _ _ _).trans (ite_eq_right h)

theorem IsSymmetrical.mono (h : S.IsSymmetrical) (hST : S ⊆ T) : T.IsSymmetrical :=
  Set.Nontrivial.mono h <| Finset.coe_subset.2 <| pivotRoles_mono <| symmetrical_mono hST

end System

end Voice
