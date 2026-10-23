module

public import Linglib.Semantics.Dynamic.PCDRT
import Mathlib.Tactic.Set

/-!
# Brasoveanu (2010): Decomposing Modal Quantification

[brasoveanu-2010] interprets discourse relative to plural information states, sets of variable
assignments that store both the values of discourse referents and the dependencies between
them, in a Dynamic Ty2 reformulation of [muskens-1996]'s CDRT. Generalized determiners store
their restrictor and nuclear scope sets together with the dependencies inside them, and singular
pronouns require the dref they retrieve to have one value. The modal half of the paper adds
drefs for possible worlds and analyses modal verbs as the modal counterparts of determiners.

This file formalizes the system for individuals of §2. The indefinite, pronoun and proper name
translations (36), (37), (42) compose the wolf discourse (27), whose truth at the dummy state
(35) is derived for any model: *A wolf came in. It ate Harvey.* is true exactly when some wolf
came in and ate Harvey (`wolfDiscourse_true_iff`), while a pronoun out of the blue is false
there. On the matrix (64), value inclusion (65) scrambles the dependency between conventions and
women and structured inclusion (66) keeps it.

## Implementation notes

* A row is an assignment `Dref → Flat E`, CDRT's canonical register structure at `Flat E`,
  and the dummy individual ★ is `⊥`.
* Predication is interpreted distributively over the rows where its drefs have values ((30),
  (34)); this is `PCDRT.atom` and `PCDRT.atom₂`.

## TODO

* Dynamic generalized quantifiers (74)–(77), quantificational subordination and donkey anaphora
  (§2.5–§2.7).
* Intensional PCDRT (§3): world drefs, modal quantifiers and modal subordination.
* The entailment particles of §4.

## References

* [brasoveanu-2010]
* [muskens-1996]
* [van-den-berg-1996]
-/

@[expose] public section

namespace Brasoveanu2010

open DynamicSemantics DynamicSemantics.Update PCDRT SetRel

/-! ### Indefinites, pronouns and proper names (§2.2) -/

/-- The drefs of the wolf discourse (27): the wolf `u` and Harvey `u'`. -/
inductive Dref where
  | u
  | u'
  deriving DecidableEq

variable {E : Type*}

/-- A row of a plural info state: an individual or ★ for each dref. -/
abbrev Row (E : Type*) := Dref → Flat E

/-- A property, type `et`: a dref to an update. -/
abbrev Pred (E : Type*) := Dref → Update (Set (Row E))

/-- The dummy assignment `i★`, which assigns ★ to every dref; `{i★}` is the dummy info state
(28), which holds no anaphoric information. -/
def iStar : Row E := ⊥

/-- (26), (30): a noun or intransitive verb is a test that its argument satisfies it. -/
def noun (P : E → Prop) : Pred E := fun v ↦ test (atom P v)

/-- (36): the singular indefinite introduces `u`, makes it singular, and predicates its restrictor
and its scope of it. -/
def indef (d : Dref) (P P' : Pred E) : Update (Set (Row E)) :=
  intro d ○ test (sing d) ○ P d ○ P' d

/-- (37): the singular pronoun requires its dref to be singular and passes it to the predicate. -/
def pron (d : Dref) (P : Pred E) : Update (Set (Row E)) := test (sing d) ○ P d

/-- (42), (43): a proper name introduces a dref whose only value is its bearer. -/
def name (x : E) (d : Dref) (P : Pred E) : Update (Set (Row E)) :=
  intro d ○ test {I | value d I = {x}} ○ P d

/-- (45a): a transitive verb applies its object's quantifier to the relation. -/
def transVerb (R : E → E → Prop) (Q : Pred E → Update (Set (Row E))) : Pred E :=
  fun v ↦ Q fun v' ↦ test (atom₂ R v v')

/-- The wolf discourse (27), (46): *A^u wolf came in. It_u ate Harvey^{u'}.* -/
def wolfDiscourse (wolf comeIn : E → Prop) (eat : E → E → Prop) (harvey : E) :
    Update (Set (Row E)) :=
  indef .u (noun wolf) (noun comeIn) ○ pron .u (transVerb eat (name harvey .u'))

/-- The truth conditions of (27) at the dummy state (35): the discourse can update `{i★}` exactly
when some wolf came in and ate Harvey. -/
theorem wolfDiscourse_true_iff (wolf comeIn : E → Prop) (eat : E → E → Prop) (harvey : E) :
    {iStar} ∈ (wolfDiscourse wolf comeIn eat harvey).dom ↔
      ∃ x, wolf x ∧ comeIn x ∧ eat x harvey := by
  constructor
  · rintro ⟨J, K, hA, hB⟩
    simp only [indef, noun, mem_comp_test] at hA
    obtain ⟨⟨⟨hint, x, hx⟩, hwolf⟩, hcome⟩ := hA
    simp only [pron, transVerb, name, mem_test_comp, mem_comp_test] at hB
    obtain ⟨-, ⟨hint', hharvey⟩, ⟨p, hp⟩, heat⟩ := hB
    have hu : value Dref.u J = {x} := (value_intro_of_ne (by decide) hint').trans hx
    have h1 : p.1 = x := by simpa [hu] using fst_mem_value_of_mem_dep hp
    have hh : value Dref.u' J = {harvey} := hharvey
    have h2 : p.2 = harvey := by simpa [hh] using snd_mem_value_of_mem_dep hp
    refine ⟨x, hwolf.2 x (by simp [hx]), hcome.2 x (by simp [hx]), ?_⟩
    simpa [h1, h2] using heat p hp
  · rintro ⟨x, hw, hc, he⟩
    set i₁ : Row E := Function.update iStar .u ↑x
    set i₂ : Row E := Function.update i₁ .u' ↑harvey
    have hv₁ : value Dref.u {i₁} = {x} := value_singleton_of_eq (by simp [i₁])
    have hv₂ : value Dref.u' {i₂} = {harvey} := value_singleton_of_eq (by simp [i₂])
    have hd : dep Dref.u Dref.u' {i₂} = {(x, harvey)} :=
      dep_singleton_of_eq (by simp [i₂, i₁]) (by simp [i₂])
    refine ⟨{i₂}, {i₁}, ?_, ?_⟩
    · simp only [indef, noun, mem_comp_test]
      exact ⟨⟨⟨singleton_mem_intro _ _ _, x, hv₁⟩, by simp [atom, hv₁, hw]⟩,
        by simp [atom, hv₁, hc]⟩
    · simp only [pron, transVerb, name, mem_test_comp, mem_comp_test]
      exact ⟨⟨x, hv₁⟩, ⟨singleton_mem_intro _ _ _, hv₂⟩, by simp [atom₂, hd, he]⟩

/-- A pronoun out of the blue is infelicitous (§2.2): its singular number fails at the dummy
state, where its dref has no value. -/
theorem pron_not_true_at_iStar (d : Dref) (P : Pred E) : {iStar} ∉ (pron d P).dom := by
  rintro ⟨J, K, ⟨rfl, x, hx⟩, -⟩
  have : value d ({iStar} : Set (Row E)) = ∅ := by
    ext y
    simp [value, iStar]
  simp [this] at hx

/-! ### Structured inclusion (63)–(66)

The matrix (64): the conventions `α₁ … α₄` in `u₁`, the women `β₁ … β₄` courted at them in `u₂`,
and two ways of storing a subset of the conventions in `u₃`. -/

/-- The drefs of (63): conventions, women, and a subset of the conventions. -/
inductive Dref₃ where
  | u₁
  | u₂
  | u₃
  deriving DecidableEq

/-- The individuals of (64). -/
inductive Ind where
  | α₁ | α₂ | α₃ | α₄
  | β₁ | β₂ | β₃ | β₄
  deriving DecidableEq

open Ind

/-- A row of (64) from its `u₁`, `u₂` and `u₃` values. -/
def row (a b c : Flat Ind) : Dref₃ → Flat Ind
  | .u₁ => a
  | .u₂ => b
  | .u₃ => c

/-- (64) with the value-inclusion column: `u₃` holds `α₁, α₃, α₁, α₂`. -/
def valueCol : Set (Dref₃ → Flat Ind) :=
  {row α₁ β₁ α₁, row α₂ β₂ α₃, row α₃ β₃ α₁, row α₄ β₄ α₂}

/-- (64) with the structured column: `u₃` holds `α₁, α₂, ★, α₄`. -/
def structCol : Set (Dref₃ → Flat Ind) :=
  {row α₁ β₁ α₁, row α₂ β₂ α₂, row α₃ β₃ ⊥, row α₄ β₄ α₄}

/-- Both columns store a subset of the conventions (65). -/
theorem value_subset_valueCol : value Dref₃.u₃ valueCol ⊆ value Dref₃.u₁ valueCol := by
  rintro x ⟨i, hi, hx⟩
  simp only [valueCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [RegisterStructure.val_apply, row, Flat.coe_inj] at hx <;> subst hx
  exacts [⟨row α₁ β₁ α₁, by simp [valueCol], rfl⟩, ⟨row α₃ β₃ α₁, by simp [valueCol], rfl⟩,
    ⟨row α₁ β₁ α₁, by simp [valueCol], rfl⟩, ⟨row α₂ β₂ α₃, by simp [valueCol], rfl⟩]

theorem value_subset_structCol : value Dref₃.u₃ structCol ⊆ value Dref₃.u₁ structCol := by
  rintro x ⟨i, hi, hx⟩
  simp only [structCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [RegisterStructure.val_apply, row,
    Flat.coe_inj, Flat.bot_ne_coe] at hx <;> subst hx
  exacts [⟨row α₁ β₁ α₁, by simp [structCol], rfl⟩, ⟨row α₂ β₂ α₂, by simp [structCol], rfl⟩,
    ⟨row α₄ β₄ α₄, by simp [structCol], rfl⟩]

/-- The value-inclusion column pairs `α₁` with `β₃`, a dependency (63a) never established. -/
theorem valueCol_scrambles_dep :
    ¬dep Dref₃.u₃ Dref₃.u₂ valueCol ⊆ dep Dref₃.u₁ Dref₃.u₂ valueCol := by
  intro h
  obtain ⟨i, hi, h₁, h₂⟩ := h (show (α₁, β₃) ∈ dep Dref₃.u₃ Dref₃.u₂ valueCol from
    ⟨row α₃ β₃ α₁, by simp [valueCol], rfl, rfl⟩)
  simp only [valueCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [row] at h₁ h₂

/-- The value-inclusion column is not a structured subset (66). -/
theorem valueCol_not_structSub : valueCol ∉ structSub Dref₃.u₃ Dref₃.u₁ := fun h ↦ by
  rcases h (row α₂ β₂ α₃) (by simp [valueCol]) with h | h <;> simp [row] at h

/-- The structured column is a fully structured subset (68). -/
theorem structCol_structSubAll : structCol ∈ structSubAll Dref₃.u₃ Dref₃.u₁ := by
  refine ⟨fun i hi ↦ ?_, fun i hi x hx hix ↦ ?_⟩
  · simp only [structCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [row, RegisterStructure.val]
  · obtain ⟨k, hk, hkx⟩ := hx
    simp only [structCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hk
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [RegisterStructure.val_apply, row, Flat.coe_inj, Flat.bot_ne_coe] at hix hkx ⊢ <;>
      subst_vars <;> simp_all

theorem structCol_keeps_dep : dep Dref₃.u₃ Dref₃.u₂ structCol ⊆ dep Dref₃.u₁ Dref₃.u₂ structCol :=
  dep_subset_of_structSub structCol_structSubAll.1

end Brasoveanu2010
