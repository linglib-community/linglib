module

public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Semantics.Modality.Basic
public import Linglib.Data.Examples.Geurts2005
public import Linglib.Data.Examples.Readers

/-!
# Geurts (2005): Entertaining Alternatives: Disjunctions as Modals

This file formalizes Geurts's modal analysis of disjunction. "S₁ or … or Sₙ" is a conjunction of
modal propositions AᵢMᵢBᵢ, each a domain Aᵢ drawn from a contextual background C, a force Mᵢ, and a
descriptive content Bᵢ, constrained by Exhaustivity, Disjointness, and Non-triviality. Following
Zimmermann, *or* merely presents a list of alternatives; unlike Zimmermann, an overt modal fuses
with the covert one, and the context dependence of the domains does the work of the
Self-Reflection Principle.

The case studies of section 3 are theorems about the constraints. Existential disjuncts bind their
domains to the background by default, so each alternative is possible (`holds_defaultBinding`) and
under Exhaustivity the background lies within the union of the contents
(`exhaustive_defaultBinding`). Two universal disjuncts cannot both be bound to the background, since
Disjointness and Non-triviality would fail together (`not_disjoint_of_necessity`); their domains
partition it instead (`partition_of_necessity`) and neither "It must be here" nor "It must be
there" follows (`mustHereOrThere`). In a mixed disjunction the universal disjunct's domain is the
background minus the existential disjunct's content (`domain_eq_diff`), so the form with the
universal disjunct first refers forward (`rows_forward_reference`). If-clauses restrict the domain
of a covert necessity modal, as for Kratzer, so a disjunction of conditionals entails the
disjunction of its consequents (`consequents_of_conditionals`), Woods's intuition against
Johnson-Laird and Savary's illusory inference; and Disjointness yields the exclusive reading of
section 5 (`exclusive_of_disjoint`).

## Implementation notes

Force is the project's `Modality.ModalForce`; the paper's ∃ is possibility and its ∀ covers both
necessities. The specialisation of the analysis to trivalent propositions lives in the study of the
later paper that draws it, `Studies/Yagi2025.lean`.

## References

* [geurts-2005]
* [zimmermann-2000]
* [kratzer-1991]
* [woods-1997]
* [johnson-laird-savary-1999]
-/

@[expose] public section

namespace Geurts2005

open Modality Function

variable {W : Type*}

/-- A modal proposition AMB consists of a domain, a modal force, and a descriptive content. -/
structure Disjunct (W : Type*) where
  domain : Set W
  force : ModalForce
  content : Set W

namespace Disjunct

variable (d : Disjunct W)

/-- AMB holds when an existential domain meets the content and a universal one lies within it. -/
def Holds : Prop :=
  if d.force = .possibility then (d.domain ∩ d.content).Nonempty else d.domain ⊆ d.content

/-- A disjunct entertains the worlds of its domain within its content. -/
def cell : Set W := d.domain ∩ d.content

theorem holds_iff_nonempty (h : d.force = .possibility) :
    d.Holds ↔ (d.domain ∩ d.content).Nonempty := by
  simp [Holds, h]

theorem holds_iff_subset (h : d.force ≠ .possibility) : d.Holds ↔ d.domain ⊆ d.content := by
  simp [Holds, h]

theorem cell_eq_domain (h : d.force ≠ .possibility) (hd : d.Holds) : d.cell = d.domain :=
  Set.inter_eq_left.mpr ((d.holds_iff_subset h).mp hd)

end Disjunct

/-- The logical form of "S₁ or … or Sₙ" is a conjunction of modal propositions. -/
abbrev Disjunction (W : Type*) := List (Disjunct W)

namespace Disjunction

variable (C : Set W) (ds : Disjunction W)

/-- Every disjunct's modal claim holds. -/
def Holds : Prop := ∀ d ∈ ds, d.Holds

/-- Exhaustivity holds when the background lies within the union of the cells. -/
def Exhaustive : Prop := C ⊆ ⋃ d ∈ ds, d.cell

/-- Disjointness holds when distinct disjuncts have disjoint cells. -/
def PairwiseDisjoint : Prop := ds.Pairwise (Disjoint on Disjunct.cell)

/-- Non-triviality holds when every domain is nonempty. -/
def Nontrivial : Prop := ∀ d ∈ ds, d.domain.Nonempty

/-- Under default binding the hearer first equates every domain with the background. -/
def defaultBinding (f : ModalForce) (bs : List (Set W)) : Disjunction W :=
  bs.map fun b ↦ ⟨C, f, b⟩

end Disjunction

section Cases

open Disjunction

variable (C : Set W) {d d' : Disjunct W}

theorem holds_defaultBinding (bs : List (Set W)) :
    (defaultBinding C .possibility bs).Holds ↔ ∀ b ∈ bs, (C ∩ b).Nonempty := by
  simp [Holds, defaultBinding, Disjunct.Holds]

theorem exhaustive_defaultBinding (f : ModalForce) (bs : List (Set W)) :
    (defaultBinding C f bs).Exhaustive C ↔ C ⊆ ⋃ b ∈ bs, b := by
  simp only [Exhaustive, defaultBinding, Set.subset_def, Set.mem_iUnion, List.mem_map,
    Disjunct.cell, Set.mem_inter_iff, exists_prop]
  constructor
  · intro h w hw
    obtain ⟨_, ⟨b, hb, rfl⟩, -, hwb⟩ := h w hw
    exact ⟨b, hb, hwb⟩
  · intro h w hw
    obtain ⟨b, hb, hwb⟩ := h w hw
    exact ⟨_, ⟨b, hb, rfl⟩, hw, hwb⟩

theorem not_disjoint_of_necessity (hf : d.force ≠ .possibility) (hf' : d'.force ≠ .possibility)
    (hd : d.Holds) (hd' : d'.Holds) (hC : d.domain = C) (hC' : d'.domain ⊆ C)
    (hne : d'.domain.Nonempty) : ¬ Disjoint d.cell d'.cell := by
  rw [d.cell_eq_domain hf hd, d'.cell_eq_domain hf' hd', hC]
  obtain ⟨w, hw⟩ := hne
  exact fun h ↦ Set.disjoint_left.mp h (hC' hw) hw

theorem partition_of_necessity (hf : d.force ≠ .possibility) (hf' : d'.force ≠ .possibility)
    (hd : d.Holds) (hd' : d'.Holds) (hex : Exhaustive C [d, d']) (hdis : Disjoint d.cell d'.cell) :
    C ⊆ d.domain ∪ d'.domain ∧ Disjoint d.domain d'.domain := by
  rw [d.cell_eq_domain hf hd, d'.cell_eq_domain hf' hd'] at hdis
  refine ⟨fun w hw ↦ ?_, hdis⟩
  have h := hex hw
  simpa only [Set.mem_iUnion, List.mem_cons, List.not_mem_nil, or_false, exists_prop,
    exists_eq_or_imp, exists_eq_left, d.cell_eq_domain hf hd, d'.cell_eq_domain hf' hd',
    Set.mem_union] using h

theorem domain_eq_diff (hf' : d'.force ≠ .possibility) (hd' : d'.Holds) (hC : d.domain = C)
    (hC' : d'.domain ⊆ C) (hex : Exhaustive C [d, d']) (hdis : Disjoint d.cell d'.cell) :
    d'.domain = C \ d.content := by
  rw [d'.cell_eq_domain hf' hd'] at hdis
  refine Set.Subset.antisymm (fun w hw ↦ ⟨hC' hw, fun hb ↦ ?_⟩) (fun w ⟨hwC, hwB⟩ ↦ ?_)
  · exact Set.disjoint_left.mp hdis ⟨by rw [hC]; exact hC' hw, hb⟩ hw
  · have h := hex hwC
    simp only [Set.mem_iUnion, List.mem_cons, List.not_mem_nil, or_false, exists_prop,
      exists_eq_or_imp, exists_eq_left, Disjunct.cell, Set.mem_inter_iff] at h
    rcases h with ⟨-, hb⟩ | ⟨hb, -⟩
    · exact absurd hb hwB
    · exact hb

/-- A conditional "if S₁ then S₂" against the background, whose if-clause restricts the domain of
a covert necessity modal to the antecedent worlds ([kratzer-1991]). -/
def conditional (A B : Set W) : Disjunct W := ⟨C ∩ A, .necessity, B⟩

theorem conditional_holds_iff (A B : Set W) : (conditional C A B).Holds ↔ C ∩ A ⊆ B := by
  simp [conditional, Disjunct.Holds]

variable {A₁ B₁ A₂ B₂ : Set W}

theorem exhaustive_conditionals_iff (h₁ : (conditional C A₁ B₁).Holds)
    (h₂ : (conditional C A₂ B₂).Holds) :
    Exhaustive C [conditional C A₁ B₁, conditional C A₂ B₂] ↔ C ⊆ A₁ ∪ A₂ := by
  rw [conditional_holds_iff] at h₁ h₂
  simp only [Exhaustive, Set.subset_def, Set.mem_iUnion, List.mem_cons, List.not_mem_nil,
    or_false, exists_prop, exists_eq_or_imp, exists_eq_left, Disjunct.cell, conditional,
    Set.mem_inter_iff, Set.mem_union]
  exact forall₂_congr fun w hw ↦
    ⟨fun h ↦ h.imp (·.1.2) (·.1.2),
     fun h ↦ h.imp (fun ha ↦ ⟨⟨hw, ha⟩, h₁ ⟨hw, ha⟩⟩) (fun ha ↦ ⟨⟨hw, ha⟩, h₂ ⟨hw, ha⟩⟩)⟩

theorem consequents_of_conditionals (h₁ : (conditional C A₁ B₁).Holds)
    (h₂ : (conditional C A₂ B₂).Holds)
    (hex : Exhaustive C [conditional C A₁ B₁, conditional C A₂ B₂]) : C ⊆ B₁ ∪ B₂ := by
  rw [exhaustive_conditionals_iff C h₁ h₂] at hex
  rw [conditional_holds_iff] at h₁ h₂
  exact fun w hw ↦ (hex hw).imp (fun ha ↦ h₁ ⟨hw, ha⟩) (fun ha ↦ h₂ ⟨hw, ha⟩)

theorem exclusive_of_disjoint {A B B' : Set W} (hA : A ⊆ C)
    (h : Disjunction.Holds [⟨A, .possibility, B⟩, ⟨C, .possibility, B ∩ B'⟩])
    (hex : Exhaustive C [⟨A, .possibility, B⟩, ⟨C, .possibility, B ∩ B'⟩])
    (hdis : Disjoint (A ∩ B) (C ∩ (B ∩ B'))) :
    C ⊆ B ∧ (C ∩ B').Nonempty ∧ (C \ B').Nonempty := by
  simp only [Disjunction.Holds, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Disjunct.Holds, ite_true] at h
  obtain ⟨⟨a, haA, haB⟩, ⟨b, hbC, -, hbB'⟩⟩ := h
  refine ⟨fun w hw ↦ ?_, ⟨b, hbC, hbB'⟩, ⟨a, hA haA, fun haB' ↦ ?_⟩⟩
  · have h := hex hw
    simp only [Set.mem_iUnion, List.mem_cons, List.not_mem_nil, or_false, exists_prop,
      exists_eq_or_imp, exists_eq_left, Disjunct.cell, Set.mem_inter_iff] at h
    rcases h with ⟨-, hb⟩ | ⟨-, hb, -⟩ <;> exact hb
  · exact Set.disjoint_left.mp hdis ⟨haA, haB⟩ ⟨hA haA, haB, haB'⟩

end Cases

/-! ### Case 3 does not entail either disjunct -/

/-- The two locations of "It must be here or it must be there". -/
inductive Loc where
  | here
  | there
  deriving DecidableEq

/-- Case 3 with the two-world background partitioned by the domains. -/
def mustHereOrThere : Disjunction Loc :=
  [⟨{.here}, .necessity, {.here}⟩, ⟨{.there}, .necessity, {.there}⟩]

theorem mustHereOrThere_holds : mustHereOrThere.Holds := by
  intro d hd
  simp only [mustHereOrThere, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> exact (Disjunct.holds_iff_subset _ (by decide)).mpr subset_rfl

theorem mustHereOrThere_exhaustive : mustHereOrThere.Exhaustive Set.univ := by
  intro w _
  cases w
  · exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_self .., ⟨rfl, rfl⟩⟩
  · exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ⟨rfl, rfl⟩⟩

theorem mustHereOrThere_pairwiseDisjoint : mustHereOrThere.PairwiseDisjoint := by
  simp [Disjunction.PairwiseDisjoint, mustHereOrThere, Function.onFun, Disjunct.cell]

theorem mustHereOrThere_nontrivial : mustHereOrThere.Nontrivial := by
  intro d hd
  simp only [mustHereOrThere, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> exact Set.singleton_nonempty _

-- (27)
theorem not_must_here : ¬ (Set.univ : Set Loc) ⊆ {.here} :=
  fun h ↦ by simpa using h (Set.mem_univ Loc.there)

/-! ### The orders of (1)–(2) -/

/-- An example of (1)–(2) records the forces of the two disjuncts, the flavour of the background,
and the judgment. -/
structure Row where
  force₁ : ModalForce
  force₂ : ModalForce
  flavor : ModalFlavor
  judgment : Judgment
  deriving DecidableEq

def forces : List (String × ModalForce) := [("may", .possibility), ("must", .necessity)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let force₁ ← ex.parse? "force1" forces
  let force₂ ← ex.parse? "force2" forces
  let flavor ← ex.parse? "flavor" [("deontic", .deontic), ("epistemic", .epistemic)]
  pure ⟨force₁, force₂, flavor, ex.judgment⟩

/-- The deontic and epistemic disjunctions (1) and (2). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = Examples.all.length := by decide

/-- By `domain_eq_diff` the universal disjunct's domain is fixed by the existential disjunct's
content; the dependence points forward when the universal disjunct comes first. -/
def ForwardReference (f₁ f₂ : ModalForce) : Prop := f₁ ≠ .possibility ∧ f₂ = .possibility

instance : DecidableRel ForwardReference := fun _ _ ↦ by unfold ForwardReference; infer_instance

/-- A disjunction of modals is acceptable exactly when no domain refers forward, which explains the
oddness of (1)–(2). -/
theorem rows_forward_reference :
    ∀ r ∈ rows, r.judgment = .acceptable ↔ ¬ ForwardReference r.force₁ r.force₂ := by
  decide

end Geurts2005
