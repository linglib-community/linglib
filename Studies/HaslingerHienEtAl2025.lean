module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Mereology
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.HaslingerHienEtAl2025
public import Mathlib.Data.PFun
public import Mathlib.Tactic.DeriveFintype

/-!
# Haslinger, Hien, Rosina, Schmitt and Wurm (2025): A unified semantics for universal quantifiers

This file formalizes the single universal quantifier of Haslinger, Hien, Rosina, Schmitt and
Wurm and the two presuppositional heads it combines with. The quantifier `Q∀` applies its scope
to every element of its restrictor that contains each restrictor element it overlaps. Whether the
result distributes falls out of the restrictor's part structure. A restrictor of pairwise
non-overlapping elements, such as the denotation of a singular count noun, makes `Q∀` the
ordinary universal quantifier, and a sum-closed plural restrictor with a largest element makes it
a claim about that largest sum. This is the authors' Distributivity–Number Generalization, which
strengthens the implicational universal of Gil. In two-form languages such as English and German
a head ONE below the quantifier presupposes that the restrictor has more than one element and
either is pairwise non-overlapping (English *every*) or consists of atoms (*each*, German
*jeder*), following Fassi Fehri. The heads are partial identities on restrictors, so a
presupposition failure is undefinedness rather than falsity.

## Main definitions

* `MaxNonOverlap`, `QForall`: the quantifier's domain condition and the quantifier `Q∀`.
* `oneEmpty`, `oneAt`: the heads ONE_∅ and ONE_AT as partial functions on restrictors.
* `over`, `every`, `each`, `jeder`: the quantifier over a head, and the English and German
  structures as partial propositions.

## Implementation notes

The null individual is `IsBot`, the overlap relation `Mereology.Overlap`, and non-overlap of a
restrictor `Mereology.DisjointPred`. The heads are `PFun.res` of the identity on the
restrictors meeting their presupposition, and a structure applied to a restrictor and a scope is
a `Part Prop`, defined when the head is. Time is measured in minutes, so *ten minutes* denotes the
consecutive half-open intervals of `ℕ`. The survey of universal quantifiers in the paper's first
two tables is not formalized here, since a survey of lexemes has no data format in the library.

## References

* [haslinger-etal-2025-nllt]
* [gil-1995]
* [fassi-fehri-2020]
-/

@[expose] public section

namespace HaslingerHienEtAl2025

open Mereology

variable {α : Type*} {P Q : Set α} {x : α}

/-! ### The quantifier -/

section PartialOrder

variable [PartialOrder α]

/-- `MaxNonOverlap P x` says that `x` is a `P`-element containing every `P`-element it
overlaps, the domain condition of the quantifier. -/
def MaxNonOverlap (P : Set α) (x : α) : Prop := x ∈ P ∧ ∀ y ∈ P, Overlap x y → y ≤ x

/-- The single universal quantifier `Q∀` says that the scope holds of every maximal
non-overlapping element of the restrictor. -/
def QForall (P Q : Set α) : Prop := ∀ x, MaxNonOverlap P x → x ∈ Q

theorem MaxNonOverlap.mem (h : MaxNonOverlap P x) : x ∈ P := h.1

theorem MaxNonOverlap.maximal (hx : ¬ IsBot x) (h : MaxNonOverlap P x) : Maximal (· ∈ P) x :=
  ⟨h.1, fun y hy hle ↦ h.2 y hy ⟨x, hx, le_rfl, hle⟩⟩

theorem maxNonOverlap_iff_of_disjoint (h : DisjointPred Overlap P) :
    MaxNonOverlap P x ↔ x ∈ P :=
  ⟨And.left, fun hx ↦ ⟨hx, fun y hy hov ↦
    (Classical.byContradiction fun hne ↦ h ⟨x, hx, y, hy, Ne.symm hne, hov⟩).le⟩⟩

/-- The singular half of the generalization says that on a pairwise non-overlapping restrictor
the quantifier is the ordinary universal. -/
theorem qForall_iff_of_disjoint (h : DisjointPred Overlap P) : QForall P Q ↔ ∀ x ∈ P, x ∈ Q :=
  forall_congr' fun _ ↦ imp_congr_left (maxNonOverlap_iff_of_disjoint h)

theorem qForall_iff_every (h : DisjointPred Overlap P) :
    QForall P Q ↔ Quantifier.Det.every P Q :=
  qForall_iff_of_disjoint h

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {m : α}

theorem maxNonOverlap_of_supClosed (hP : SupClosed P) (hm : Maximal (· ∈ P) m) :
    MaxNonOverlap P m :=
  ⟨hm.1, fun _ hy _ ↦ le_sup_right.trans (hm.2 (hP hm.1 hy) le_sup_left)⟩

theorem maxNonOverlap_iff_of_supClosed (h0 : ∀ x ∈ P, ¬ IsBot x) (hP : SupClosed P)
    (hm : Maximal (· ∈ P) m) : MaxNonOverlap P x ↔ x = m :=
  ⟨fun hx ↦ cum_maximal_unique hP (hx.maximal (h0 x hx.1)) hm,
   fun hxm ↦ hxm ▸ maxNonOverlap_of_supClosed hP hm⟩

/-- The plural half of the generalization says that on a sum-closed restrictor without the null
individual the quantifier applies the scope to the largest sum. -/
theorem qForall_iff_of_supClosed (h0 : ∀ x ∈ P, ¬ IsBot x) (hP : SupClosed P)
    (hm : Maximal (· ∈ P) m) : QForall P Q ↔ m ∈ Q := by
  simp only [QForall, maxNonOverlap_iff_of_supClosed h0 hP hm, forall_eq]

end SemilatticeSup

/-! ### The heads ONE_∅ and ONE_AT -/

section Heads

variable [PartialOrder α]

/-- The presupposition of ONE_∅ is that the restrictor has more than one element and no two of
them overlap. -/
def OneEmptyDom (P : Set α) : Prop := P.Nontrivial ∧ DisjointPred Overlap P

/-- The presupposition of ONE_AT is that the restrictor has more than one element, all of them
atoms. -/
def OneAtDom (P : Set α) : Prop := P.Nontrivial ∧ ∀ x ∈ P, Atom x

theorem OneAtDom.oneEmptyDom (h : OneAtDom P) : OneEmptyDom P :=
  ⟨h.1, fun ⟨x, hx, y, hy, hne, _, hz, hzx, hzy⟩ ↦
    hne (((h.2 x hx).eq hzx hz).symm.trans ((h.2 y hy).eq hzy hz))⟩

/-- The head ONE_∅ is the identity on the restrictors meeting its presupposition. -/
def oneEmpty : Set α →. Set α := PFun.res id {P | OneEmptyDom P}

/-- The head ONE_AT is the identity on the restrictors meeting its presupposition. -/
def oneAt : Set α →. Set α := PFun.res id {P | OneAtDom P}

/-- The quantifier over a head is defined when the head is defined on the restrictor, and is then
the quantifier over the head's output. -/
def over (h : Set α →. Set α) (P Q : Set α) : Part Prop := (h P).map (QForall · Q)

/-- English *every* is the quantifier over ONE_∅. -/
def every (P Q : Set α) : Part Prop := over oneEmpty P Q

/-- English *each* is the quantifier over ONE_∅ over ONE_AT. -/
def each (P Q : Set α) : Part Prop := over (oneEmpty.comp oneAt) P Q

/-- German *jeder* is the quantifier over ONE_AT alone, since German lacks ONE_∅. -/
def jeder (P Q : Set α) : Part Prop := over oneAt P Q

theorem every_dom : (every P Q).Dom ↔ OneEmptyDom P := Iff.rfl

theorem jeder_dom : (jeder P Q).Dom ↔ OneAtDom P := Iff.rfl

theorem each_dom : (each P Q).Dom ↔ OneAtDom P :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.oneEmptyDom⟩⟩

/-- *Each* is defined on fewer restrictors than *every*, and where both are defined they agree,
since the presupposition of *each* entails that of *every* and both leave the bare quantifier. -/
theorem each_le_every : each P Q ≤ every P Q :=
  fun _ ⟨h, hp⟩ ↦ ⟨(each_dom.1 h).oneEmptyDom, hp⟩

theorem every_get_iff (h : (every P Q).Dom) : (every P Q).get h ↔ ∀ x ∈ P, x ∈ Q :=
  qForall_iff_of_disjoint h.2

theorem each_get_iff (h : (each P Q).Dom) : (each P Q).get h ↔ ∀ x ∈ P, x ∈ Q :=
  qForall_iff_of_disjoint (each_dom.1 h).oneEmptyDom.2

/-! ### Decidability on finite carriers -/

section Decidable

variable [Fintype α] [DecidableEq α] [DecidableLE α] [DecidablePred (IsBot : α → Prop)]
  [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Q)]

instance (x y : α) : Decidable (Overlap x y) := Fintype.decidableExistsFintype

instance (x : α) : Decidable (Atom x) :=
  inferInstanceAs (Decidable (¬ IsBot x ∧ ∀ ⦃y⦄, ¬ IsBot y → y ≤ x → x ≤ y))

instance (x : α) : Decidable (Maximal (· ∈ P) x) :=
  inferInstanceAs (Decidable (x ∈ P ∧ ∀ ⦃y⦄, y ∈ P → x ≤ y → y ≤ x))

instance : DecidablePred (MaxNonOverlap P) := fun x ↦
  inferInstanceAs (Decidable (x ∈ P ∧ ∀ y ∈ P, Overlap x y → y ≤ x))

instance : Decidable (QForall P Q) :=
  inferInstanceAs (Decidable (∀ x, MaxNonOverlap P x → x ∈ Q))

instance : Decidable P.Nontrivial := inferInstanceAs (Decidable (∃ x ∈ P, ∃ y ∈ P, x ≠ y))

instance : Decidable (OverlapPred Overlap P) :=
  inferInstanceAs (Decidable (∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ Overlap x y))

instance : Decidable (DisjointPred Overlap P) :=
  inferInstanceAs (Decidable (¬ OverlapPred Overlap P))

instance : Decidable (OneEmptyDom P) :=
  inferInstanceAs (Decidable (P.Nontrivial ∧ DisjointPred Overlap P))

instance : Decidable (OneAtDom P) :=
  inferInstanceAs (Decidable (P.Nontrivial ∧ ∀ x ∈ P, Atom x))

end Decidable

end Heads

/-! ### Three students -/

section Students

/-- Three salient students; a plurality is a nonempty finset and the null individual is `∅`. -/
inductive Student where
  | alice
  | bob
  | carol
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The plural restrictor *students* holds of the nonempty pluralities and is closed under sum. -/
def students : Set (Finset Student) := {s | s.Nonempty}

/-- The singular restrictor *student* holds of the atoms. -/
def student : Set (Finset Student) := {s | s.card = 1}

/-- The restrictor *two students* holds of the pairs. -/
def twoStudents : Set (Finset Student) := {s | s.card = 2}

/-- The collective scope *met*, true of the whole group only. -/
def met : Set (Finset Student) := {s | s = Finset.univ}

instance : DecidablePred (· ∈ students) := fun s ↦ inferInstanceAs (Decidable s.Nonempty)
instance : DecidablePred (· ∈ student) := fun s ↦ inferInstanceAs (Decidable (s.card = 1))
instance : DecidablePred (· ∈ twoStudents) := fun s ↦ inferInstanceAs (Decidable (s.card = 2))
instance : DecidablePred (· ∈ met) := fun s ↦ inferInstanceAs (Decidable (s = Finset.univ))

/-- The Distributivity–Number Generalization on one algebra, where the collective scope holds
under the plural restrictor and fails under the singular one. -/
theorem dng : QForall students met ∧ ¬ QForall student met := by decide

theorem qForall_students_iff (Q : Set (Finset Student)) : QForall students Q ↔ Finset.univ ∈ Q :=
  qForall_iff_of_supClosed (fun _ hs h ↦ hs.ne_empty (Finset.subset_empty.1 (h ∅)))
    (fun _ hx _ _ ↦ hx.mono Finset.subset_union_left)
    ⟨Finset.univ_nonempty, fun y _ _ ↦ Finset.subset_univ y⟩

theorem qForall_student_iff (Q : Set (Finset Student)) : QForall student Q ↔ ∀ s ∈ student, s ∈ Q :=
  qForall_iff_of_disjoint (by decide)

theorem maximal_twoStudents : ∀ s ∈ twoStudents, Maximal (· ∈ twoStudents) s := by decide

theorem not_maxNonOverlap_twoStudents : ∀ s, ¬ MaxNonOverlap twoStudents s := by decide

/-- With three salient students the quantifier over *two students* is vacuous, so the reading
on which every pair of students satisfies the scope is unavailable. -/
theorem qForall_twoStudents (Q : Set (Finset Student)) : QForall twoStudents Q :=
  fun s hs ↦ (not_maxNonOverlap_twoStudents s hs).elim

theorem not_oneEmptyDom_students : ¬ OneEmptyDom students := by decide

theorem oneAtDom_student : OneAtDom student := by decide

end Students

/-! ### Ten minutes -/

section Intervals

/-- The coerced denotation of *ten minutes* holds of the consecutive ten-minute intervals, with
time measured in minutes. -/
def tenMinutes : Set (Set ℕ) := Set.range fun k ↦ Set.Ico (10 * k) (10 * k + 10)

theorem tenMinutes_nontrivial : tenMinutes.Nontrivial :=
  Set.nontrivial_of_mem_mem_ne (Set.mem_range_self 0) (Set.mem_range_self 1) fun h ↦ by
    simpa using Set.ext_iff.1 h 0

theorem tenMinutes_disjoint : DisjointPred Overlap tenMinutes := by
  rintro ⟨_, ⟨j, rfl⟩, _, ⟨k, rfl⟩, hne, z, hz, hzj, hzk⟩
  obtain ⟨n, hn⟩ : z.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦ hz (h ▸ isBot_bot)
  obtain ⟨hj₁, hj₂⟩ := hzj hn
  obtain ⟨hk₁, hk₂⟩ := hzk hn
  obtain rfl : j = k := by omega
  exact hne rfl

theorem oneEmptyDom_tenMinutes : OneEmptyDom tenMinutes :=
  ⟨tenMinutes_nontrivial, tenMinutes_disjoint⟩

theorem not_atom_tenMinutes : ∀ I ∈ tenMinutes, ¬ Atom I := by
  rintro _ ⟨k, rfl⟩ h
  obtain ⟨n, hn⟩ := Set.isAtom_iff.1 (atom_iff_isAtom.1 h)
  rw [Set.ext_iff] at hn
  have h0 : 10 * k = n := (hn _).1 ⟨le_rfl, by omega⟩
  have h1 : 10 * k + 1 = n := (hn _).1 ⟨by omega, by omega⟩
  omega

theorem not_oneAtDom_tenMinutes : ¬ OneAtDom tenMinutes :=
  fun h ↦ not_atom_tenMinutes _ (Set.mem_range_self 0) (h.2 _ (Set.mem_range_self 0))

/-- *Every ten minutes* is defined. -/
theorem every_tenMinutes_dom (Q : Set (Set ℕ)) : (every tenMinutes Q).Dom :=
  oneEmptyDom_tenMinutes

/-- *Each ten minutes* is a presupposition failure. -/
theorem each_tenMinutes_undefined (Q : Set (Set ℕ)) : ¬ (each tenMinutes Q).Dom :=
  fun h ↦ not_oneAtDom_tenMinutes (each_dom.1 h)

theorem jeder_tenMinutes_undefined (Q : Set (Set ℕ)) : ¬ (jeder tenMinutes Q).Dom :=
  not_oneAtDom_tenMinutes

end Intervals

/-! ### The English and German forms -/

/-- A universal quantifier form realizes one of four structures, namely the bare quantifier, the
quantifier over ONE_∅, the quantifier over ONE_∅ and ONE_AT, or the quantifier over ONE_AT alone,
as in German. -/
inductive Structure where
  | bare
  | nonOverlap
  | atomic
  | atomicOnly
  deriving DecidableEq, Repr, Fintype

/-- The head a structure spells out. -/
def Structure.head [PartialOrder α] : Structure → (Set α →. Set α)
  | .bare => PFun.lift id
  | .nonOverlap => oneEmpty
  | .atomic => oneEmpty.comp oneAt
  | .atomicOnly => oneAt

/-- The English universal determiners *all*, *every* and *each*. -/
def english : English.Determiners.QuantityWord → Option Structure
  | .all => some .bare
  | .every => some .nonOverlap
  | .each => some .atomic
  | _ => none

/-- At the lexicon the generalization says that the English forms carrying a ONE head are exactly
the universal determiners the fragment records as selecting the singular. -/
theorem one_iff_singular :
    ∀ w s, english w = some s →
      (s ≠ .bare ↔ w.numberRestriction = some .singular) := by
  decide

theorem structure_dom_tenMinutes (s : Structure) (Q : Set (Set ℕ)) :
    (over s.head tenMinutes Q).Dom ↔ s = .bare ∨ s = .nonOverlap := by
  cases s
  · exact iff_of_true trivial (.inl rfl)
  · exact iff_of_true oneEmptyDom_tenMinutes (.inr rfl)
  · exact iff_of_false (each_tenMinutes_undefined Q) (by decide)
  · exact iff_of_false not_oneAtDom_tenMinutes (by decide)

instance (s : Structure) (Q : Set (Set ℕ)) : Decidable (over s.head tenMinutes Q).Dom :=
  decidable_of_iff _ (structure_dom_tenMinutes s Q).symm

/-- The structure names of the example rows. -/
def structureTable : List (String × Structure) :=
  [("bare", .bare), ("nonOverlap", .nonOverlap), ("atomic", .atomic),
    ("atomicOnly", .atomicOnly)]

/-- The paper's judgments on universal quantifiers with *ten minutes* are the definedness
predictions, since a form is acceptable just in case its structure is defined on the intervals. -/
theorem judgment_rows :
    ∀ row ∈ Examples.all, ∃ s, row.parse? "structure" structureTable = some s ∧
      (row.judgment = .acceptable ↔ (over s.head tenMinutes Set.univ).Dom) := by
  decide +kernel

end HaslingerHienEtAl2025
