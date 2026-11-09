module

public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.Tactic.Choose

/-!
# Proportional analogy

A paradigm system `p : ParadigmSystem L Cell F` gives the form of each lexeme at each cell. It
is [analogical](##IsAnalogical) under a class of operations on forms when the forms at any two
cells are related by one operation of the class, the same for every lexeme, as in *walk : walks =
jump : jumps*; under arbitrary operations this says only that [each cell determines every
other](##isAnalogical_univ_iff). Under translations it says that the shift between two cells is
the same for every lexeme, which holds iff [the family is a lexeme part plus a cell
part](##isAnalogicallyRegular_iff_exists_add); within each class of a partition of the lexemes,
iff [the cell part depends only on the class](##forall_isAnalogicallyRegular_domRestrict_iff).

## References

* [blevins-2016]
* [heitmeier-chuang-baayen-2026]
* [shafaei-bajestan-moradipour-tari-uhrig-baayen-2024]
-/

@[expose] public section

namespace Morphology

variable {L Cell F G : Type*} {p : ParadigmSystem L Cell F}

/-- A paradigm system is analogical under a class of operations on forms when the forms at any
two cells are related by one operation of the class, the same for every lexeme. -/
def IsAnalogical (ops : Set (F → F)) (p : ParadigmSystem L Cell F) : Prop :=
  ∀ c c', ∃ g ∈ ops, ∀ l, p l c' = g (p l c)

theorem IsAnalogical.mono {ops ops' : Set (F → F)} (h : IsAnalogical ops p) (hops : ops ⊆ ops') :
    IsAnalogical ops' p :=
  fun c c' ↦ (h c c').imp fun _ ⟨hg, hp⟩ ↦ ⟨hops hg, hp⟩

/-- Analogy under arbitrary operations says only that the form at each cell determines the form
at every other cell. -/
theorem isAnalogical_univ_iff :
    IsAnalogical Set.univ p ↔ ∀ c c', (p · c').FactorsThrough (p · c) := by
  refine ⟨fun h c c' l l' hl ↦ ?_, fun h c c' ↦
    ⟨_, trivial, fun l ↦ ((h c c').extend_apply id l).symm⟩⟩
  obtain ⟨g, -, hg⟩ := h c c'
  exact (hg l).trans <| (congrArg g hl).trans (hg l').symm

section Add

variable [Add F] [Add G]

/-- A paradigm system is analogically regular when it is analogical under translations, so that
the shift from the form at one cell to the form at another is the same for every lexeme. -/
def IsAnalogicallyRegular (p : ParadigmSystem L Cell F) : Prop :=
  IsAnalogical (Set.range fun v ↦ (· + v)) p

theorem IsAnalogicallyRegular.map {M : Type*} [FunLike M F G] [AddHomClass M F G]
    (h : IsAnalogicallyRegular p) (f : M) : IsAnalogicallyRegular fun l c ↦ f (p l c) := by
  intro c c'
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h c c'
  exact ⟨_, ⟨f v, rfl⟩, fun l ↦ (congrArg f (hv l)).trans (map_add f _ _)⟩

end Add

section AddCommGroup

variable [AddCommGroup F]

theorem isAnalogicallyRegular_iff :
    IsAnalogicallyRegular p ↔ ∀ l l' c c', p l c - p l c' = p l' c - p l' c' := by
  refine ⟨fun h l l' c c' ↦ ?_, fun h c c' ↦ ?_⟩
  · obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h c' c
    exact (sub_eq_of_eq_add' (hv l)).trans (sub_eq_of_eq_add' (hv l')).symm
  · rcases isEmpty_or_nonempty L with hL | ⟨⟨l₀⟩⟩
    · exact ⟨(· + 0), ⟨0, rfl⟩, isEmptyElim⟩
    · exact ⟨_, ⟨p l₀ c' - p l₀ c, rfl⟩, fun l ↦ eq_add_of_sub_eq' (h l l₀ c' c)⟩

theorem isAnalogicallyRegular_add (a : L → F) (b : Cell → F) :
    IsAnalogicallyRegular fun l c ↦ a l + b c :=
  isAnalogicallyRegular_iff.2 fun _ _ _ _ ↦ by
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]

theorem isAnalogicallyRegular_iff_exists_add :
    IsAnalogicallyRegular p ↔ ∃ (a : L → F) (b : Cell → F), ∀ l c, p l c = a l + b c := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, hab⟩ ↦ ?_⟩
  · rcases isEmpty_or_nonempty Cell with hC | ⟨⟨c₀⟩⟩
    · exact ⟨0, 0, fun _ ↦ isEmptyElim⟩
    choose g hg hgp using h c₀
    choose v hv using hg
    exact ⟨(p · c₀), v, fun l c ↦ by rw [hgp c l, ← hv c]⟩
  · rw [show p = fun l c ↦ a l + b c from funext₂ hab]
    exact isAnalogicallyRegular_add a b

/-- A paradigm system is analogically regular within each class of a partition of its lexemes iff
it is a lexeme part plus a part fixed by the class and the cell, the shift between two cells
depending only on the class, as plural semantics shifts by semantic class
([shafaei-bajestan-moradipour-tari-uhrig-baayen-2024]). -/
theorem forall_isAnalogicallyRegular_domRestrict_iff {K : Type*} (κ : L → K) :
    (∀ k, IsAnalogicallyRegular ((κ ⁻¹' {k}).domRestrict p)) ↔
      ∃ (a : L → F) (b : K → Cell → F), ∀ l c, p l c = a l + b (κ l) c := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, hab⟩ k ↦ isAnalogicallyRegular_iff_exists_add.2
    ⟨fun l ↦ a l, b k, fun ⟨l, hl⟩ c ↦ by rw [Set.domRestrict_apply, hab, hl]⟩⟩
  choose a b hab using fun k ↦ isAnalogicallyRegular_iff_exists_add.1 (h k)
  exact ⟨fun l ↦ a (κ l) ⟨l, rfl⟩, b, fun l c ↦ hab (κ l) ⟨l, rfl⟩ c⟩

end AddCommGroup

end Morphology
