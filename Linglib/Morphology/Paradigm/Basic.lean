module

public import Mathlib.Data.Finset.Image
public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Morphology.Realization

/-!
# Paradigms: forms over cells

A paradigm assigns a surface form to each of `n` linearly ordered cells, and its syncretism is
the kernel setoid `Setoid.ker p` of that assignment, decidable over finitely many cells. The
ordered carrier serves realization-pattern typology (*ABA and contiguity). A paradigm system
assigns a form to each row and cell of a table whose rows are lexemes or inflection classes and
whose cells form any type; it carries implicative structure and entropy over the cells
(`Complexity.lean`) and proportional analogy (`Analogy.lean`).

## Main declarations

* `Morphology.Paradigm n F`: a form for each of `n` ordered cells.
* `Morphology.formsAt`: the forms an inventory offers for each cell.
* `Morphology.ParadigmSystem D Cell Form`: a form for each row of `D` at each cell of `Cell`.
* `Morphology.ParadigmSystem.toRealization`: a paradigm system as a total, univalent
  `Realization`.

## References

* [ackerman-malouf-2013]
* [bobaljik-2012]
-/

@[expose] public section

namespace Morphology

/-- A paradigm over `n` linearly ordered cells assigns the form occupying each cell, the carrier
of [bobaljik-2012]'s realization patterns such as AAA, ABB and ABC. -/
abbrev Paradigm (n : ℕ) (F : Type*) := Fin n → F

/-! ### The paradigm of an inventory -/

section FormsAt

variable {ι Cell F : Type*} [DecidableEq Cell] [DecidableEq F]
  {cells : ι → Finset Cell} {form : ι → F} {I J : Finset ι} {c : Cell} {f : F}

/-- The forms an inventory `I` offers for the cell `c`, where the item `i` has the form `form i`
and realizes the cells `cells i`. A cell no item realizes gets `∅` and an overabundant cell
several forms, and `Setoid.ker (formsAt cells form I)` relates the cells the inventory does not
distinguish. -/
def formsAt (cells : ι → Finset Cell) (form : ι → F) (I : Finset ι) (c : Cell) : Finset F :=
  (I.filter (c ∈ cells ·)).image form

theorem mem_formsAt : f ∈ formsAt cells form I c ↔ ∃ i ∈ I, c ∈ cells i ∧ form i = f := by
  simp [formsAt, and_assoc]

@[gcongr]
theorem formsAt_mono (h : I ⊆ J) (c : Cell) :
    formsAt cells form I c ⊆ formsAt cells form J c :=
  Finset.image_subset_image (Finset.filter_subset_filter _ h)

theorem formsAt_union [DecidableEq ι] (I J : Finset ι) (c : Cell) :
    formsAt cells form (I ∪ J) c = formsAt cells form I c ∪ formsAt cells form J c := by
  simp [formsAt, Finset.filter_union, Finset.image_union]

end FormsAt

/-- A paradigm system assigns a form to each row of a table, a lexeme or an inflection class, at
each cell, such as the inflection-class table of [ackerman-malouf-2013]'s Table 1, whose class
count (the enumerative complexity of that paper's Table 3) is `Fintype.card D`. -/
abbrev ParadigmSystem (D Cell Form : Type*) := D → Cell → Form

namespace ParadigmSystem

variable {D Cell Form : Type*} (M : ParadigmSystem D Cell Form)

/-- A paradigm system realizes each row at each cell by its one form. -/
def toRealization : Realization D Cell Form := ⟨fun d c ↦ {M d c}⟩

@[simp] theorem toRealization_realize (d : D) (c : Cell) : M.toRealization.realize d c = {M d c} :=
  rfl

theorem isTotal_toRealization : M.toRealization.IsTotal := fun _ _ ↦ Finset.singleton_nonempty _

theorem isUnivalent_toRealization : M.toRealization.IsUnivalent := fun _ _ ↦
  (Finset.card_singleton _).le

end ParadigmSystem

end Morphology
