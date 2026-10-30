module

public import Linglib.Logic.BeliefRevision.Iterated
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# Darwiche and Pearl (1997): On the Logic of Iterated Belief Revision

The AGM postulates constrain one revision of a belief set, so Darwiche and Pearl revise epistemic
states, which [can share their beliefs and revise them differently](##jurors_revise), and add four
postulates on iterated revision, (C1)–(C4), which
[the AGM postulates do not entail](##exists_isAGM_not_c1_c2_c3_c4). Boutilier's stronger postulate
[forgets an observation once a later one corrects another](##cb_forgets); Spohn's
conditionalisation [satisfies (C1)–(C4) but not Boutilier's
postulate](##spohnRevision_c1_c2_c3_c4_not_cb), and an operator moving disbelieved worlds down
[satisfies (C1) but neither (C3) nor (C4)](##diamondRevision_c1_not_c3_c4).

## Implementation notes

* The worlds of an appendix table are the valuations of its two propositions, so a
  proposition is a set of pairs of Booleans, `first` and `second` naming the two.
* A table of Appendix A gives one ranking and its revision by one proposition. `patch` extends it
  to an operator by Spohn's revision elsewhere, which a faithful assignment still represents when
  the table's revised belief worlds are the least evidence-worlds of the prior (`patch_faithful`).

## Errata

* The proof of Theorem 15 derives (C1) for `◇` from part (1) of Lemma B.2 "according to Theorem
  14", but the theorem that equates (C1) with condition (CR1) is Theorem 13.

## References

* [darwiche-pearl-1997]
* [boutilier-1996]
* [goldszmidt-pearl-1996]
-/

@[expose] public section

namespace DarwichePearl1997

open BeliefRevision RankingFunction

/-! ### Epistemic states against belief sets -/

/-- The suspects of the murder trial of Example 7, which the paper takes from Goldszmidt and Pearl.
-/
inductive Suspect
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- The first juror holds A guilty, B a remote possibility and C innocent. -/
def juror1 : Suspect → ℕ
  | .a => 0
  | .b => 1
  | .c => 2

/-- The second juror holds A guilty, C a remote possibility and B innocent. -/
def juror2 : Suspect → ℕ
  | .a => 0
  | .c => 1
  | .b => 2

theorem jurors_bel :
    (spohnRevision Suspect).bel juror1 = (spohnRevision Suspect).bel juror2 := by
  ext w
  cases w <;> simp [juror1, juror2]

/-- Example 7: two jurors who believe the same, that A is guilty, revise their beliefs differently
on learning that A is innocent, the first coming to believe B guilty and the second not. -/
theorem jurors_revise :
    Suspect.b ∈
        (spohnRevision Suspect).bel ((spohnRevision Suspect).revise juror1 {w | w ≠ .a}) ∧
      Suspect.b ∉
        (spohnRevision Suspect).bel ((spohnRevision Suspect).revise juror2 {w | w ≠ .a}) := by
  rw [spohnRevision_faithful.bel_revise, spohnRevision_faithful.bel_revise]
  decide

/-! ### The appendix tables -/

/-- A world of a language with two propositions gives the truth values of its propositions. -/
abbrev World := Bool × Bool

/-- The first proposition. -/
abbrev first : Set World := {w | w.1 = true}

/-- The second proposition. -/
abbrev second : Set World := {w | w.2 = true}

/-- Table A.1, before revising by `¬(adder_ok ∧ multiplier_ok)`. -/
def tableA1 : World → ℕ
  | (true, true) => 0
  | (true, false) => 1
  | (false, true) => 2
  | (false, false) => 3

/-- Table A.1, after. -/
def tableA1' : World → ℕ
  | (true, true) => 1
  | (true, false) => 0
  | (false, true) => 2
  | (false, false) => 1

-- Example A.1
theorem exampleA1 :
    (∀ w, tableA1' w = 0 ↔
      w ∈ (Preorder.lift tableA1).minimals {w | ¬ (w ∈ first ∧ w ∈ second)}) ∧
    (∀ w, w ∈ (Preorder.lift tableA1).minimals {w | w ∉ first} ↔ w = (false, true)) ∧
    (∀ w, w ∈ (Preorder.lift tableA1').minimals {w | w ∉ first} ↔ w = (false, false)) ∧
    ¬ AgreesOn (Preorder.lift tableA1) (Preorder.lift tableA1')
      {w | ¬ (w ∈ first ∧ w ∈ second)} := by
  decide

/-- Table A.2, before revising by `¬smart`. -/
def tableA2 : World → ℕ
  | (true, true) => 0
  | (true, false) => 1
  | (false, true) => 1
  | (false, false) => 2

/-- Table A.2, after. -/
def tableA2' : World → ℕ
  | (true, true) => 2
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

-- Example A.2
theorem exampleA2 :
    (∀ w, tableA2' w = 0 ↔ w ∈ (Preorder.lift tableA2).minimals {w | w ∉ first}) ∧
    (∀ w, w ∈ (Preorder.lift tableA2).minimals first ↔ w = (true, true)) ∧
    (∀ w, w ∈ (Preorder.lift tableA2').minimals first ↔ w = (true, false)) ∧
    ¬ AgreesOn (Preorder.lift tableA2) (Preorder.lift tableA2') first := by
  decide

/-- Table A.3, before revising by `flies`. -/
def tableA3 : World → ℕ
  | (true, true) => 2
  | (true, false) => 3
  | (false, true) => 1
  | (false, false) => 0

/-- Table A.3, after. -/
def tableA3' : World → ℕ
  | (true, true) => 1
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

-- Example A.3
theorem exampleA3 :
    (∀ w, tableA3' w = 0 ↔ w ∈ (Preorder.lift tableA3).minimals second) ∧
    (∀ w, w ∈ (Preorder.lift tableA3).minimals first ↔ w = (true, true)) ∧
    (∀ w, w ∈ (Preorder.lift tableA3').minimals first ↔ w ∈ first) ∧
    ¬ PreservesLt (Preorder.lift tableA3) (Preorder.lift tableA3') second secondᶜ := by
  decide

/-- Table A.4, before revising by `nice_day`. -/
def tableA4 : World → ℕ
  | (true, true) => 1
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 0

/-- Table A.4, after. -/
def tableA4' : World → ℕ
  | (true, true) => 2
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

-- Example A.4
theorem exampleA4 :
    (∀ w, tableA4' w = 0 ↔ w ∈ (Preorder.lift tableA4).minimals second) ∧
    (∀ w, w ∈ (Preorder.lift tableA4).minimals first ↔ w ∈ first) ∧
    (∀ w, w ∈ (Preorder.lift tableA4').minimals first ↔ w = (true, false)) ∧
    ¬ PreservesLe (Preorder.lift tableA4) (Preorder.lift tableA4') second secondᶜ := by
  decide

/-! ### The AGM postulates entail none of (C1)–(C4) -/

section Patch

variable {W : Type*}

open Classical in
/-- Spohn's revision, except that the ranking `κ₀` revised by `μ₀` becomes `κ₁`: a table of
Appendix A, extended to an operator. -/
noncomputable def patch (κ₀ : W → ℕ) (μ₀ : Set W) (κ₁ : W → ℕ) : Revision (W → ℕ) W where
  bel κ := {w | κ w = 0}
  revise κ μ := if κ = κ₀ ∧ μ = μ₀ then κ₁ else spohn κ μ

variable {κ₀ κ₁ : W → ℕ} {μ₀ : Set W}

theorem patch_revise_self : (patch κ₀ μ₀ κ₁).revise κ₀ μ₀ = κ₁ := by
  simp [patch]

-- the rankings' orderings represent the extended table when its revised belief worlds are the
-- least evidence-worlds of the prior
theorem patch_faithful (h : ∀ w, κ₁ w = 0 ↔ w ∈ (Preorder.lift κ₀).minimals μ₀) :
    (patch κ₀ μ₀ κ₁).Faithful fun κ ↦ Preorder.lift κ where
  total := spohnRevision_faithful.total
  wellFounded := spohnRevision_faithful.wellFounded
  equiv_of_mem := spohnRevision_faithful.equiv_of_mem
  lt_of_mem := spohnRevision_faithful.lt_of_mem
  bel_revise κ μ := by
    by_cases hκμ : κ = κ₀ ∧ μ = μ₀
    · obtain ⟨rfl, rfl⟩ := hκμ
      ext w
      simp [h, patch]
    · simpa [patch, hκμ] using spohnRevision_faithful.bel_revise κ μ

end Patch

-- Example A.1
theorem exists_isAGM_not_c1 : ∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C1 := by
  have hr := patch_faithful exampleA1.1
  refine ⟨_, hr.isAGM, fun h ↦ exampleA1.2.2.2 ?_⟩
  simpa [patch_revise_self] using hr.c1_iff.1 h tableA1 {w | ¬ (w ∈ first ∧ w ∈ second)}

-- Example A.2
theorem exists_isAGM_not_c2 : ∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C2 := by
  have hr := patch_faithful exampleA2.1
  refine ⟨_, hr.isAGM, fun h ↦ exampleA2.2.2.2 ?_⟩
  have hc : ({w | w ∉ first} : Set World)ᶜ = first := by ext; simp
  have := hr.c2_iff.1 h tableA2 {w | w ∉ first}
  rwa [patch_revise_self, hc] at this

-- Example A.3
theorem exists_isAGM_not_c3 : ∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C3 := by
  have hr := patch_faithful exampleA3.1
  refine ⟨_, hr.isAGM, fun h ↦ exampleA3.2.2.2 ?_⟩
  simpa [patch_revise_self] using hr.c3_iff.1 h tableA3 second

-- Example A.4
theorem exists_isAGM_not_c4 : ∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C4 := by
  have hr := patch_faithful exampleA4.1
  refine ⟨_, hr.isAGM, fun h ↦ exampleA4.2.2.2 ?_⟩
  simpa [patch_revise_self] using hr.c4_iff.1 h tableA4 second

/-- Appendix A: the AGM postulates entail none of (C1)–(C4), since each table extends to an AGM
operator that violates its postulate. -/
theorem exists_isAGM_not_c1_c2_c3_c4 :
    (∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C1) ∧
      (∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C2) ∧
      (∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C3) ∧
      ∃ r : Revision (World → ℕ) World, r.IsAGM ∧ ¬ r.C4 :=
  ⟨exists_isAGM_not_c1, exists_isAGM_not_c2, exists_isAGM_not_c3, exists_isAGM_not_c4⟩

/-! ### Boutilier's postulate forgets -/

/-- Example A.5: under Boutilier's postulate an agent who believes the animal a bird, observes it
red, and learns that it is not a bird after all, believes what it would have believed without the
observation. -/
theorem cb_forgets {S W : Type*} {r : Revision S W} (h : r.IsAGM) (hCB : r.CB) {Ψ : S}
    {bird red : Set W} (hΨ : r.bel Ψ = bird) (hne : (bird ∩ red).Nonempty)
    (hΨ' : r.bel (r.revise Ψ birdᶜ) = birdᶜ) :
    r.bel (r.revise (r.revise Ψ red) birdᶜ) = birdᶜ := by
  rw [hCB Ψ red birdᶜ (by
    rw [h.expansion Ψ red (by rwa [hΨ]), hΨ, compl_compl]
    exact Set.inter_subset_left), hΨ']

/-! ### Boutilier's postulate is stronger than (C1)–(C4) -/

/-- A prior believing world `0`, with the evidence-world `1` less plausible than the world `2`
outside the evidence. -/
def c6Prior : Fin 3 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 1

/-- `c6Prior` after Spohn's revision by `c6Evidence`. -/
def c6Prior' : Fin 3 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 2

/-- The evidence of `c6Prior`. -/
abbrev c6Evidence : Set (Fin 3) := {w | w ≠ 2}

theorem spohn_c6Prior : spohn c6Prior c6Evidence = c6Prior' := by
  have h : rank c6Prior c6Evidence = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 => simp only [spohn, aPart, h]; simp [c6Evidence, c6Prior, c6Prior']

theorem not_spohnRevision_c6 : ¬ (spohnRevision (Fin 3)).C6 := by
  intro h
  have hlt := spohnRevision_faithful.c6_iff.1 h c6Prior c6Evidence 2 (by simp) 1
    ⟨by simp, by simp [spohn_c6Prior, c6Prior']⟩ (by decide)
  rw [Preorder.lift_lt_iff, spohnRevision_revise, spohn_c6Prior] at hlt
  exact absurd hlt (by decide)

/-- Section 7: Spohn's revision satisfies (C1)–(C4) but not Boutilier's postulate, which adds
(C5) and (C6). -/
theorem spohnRevision_c1_c2_c3_c4_not_cb :
    (spohnRevision (Fin 3)).C1 ∧ (spohnRevision (Fin 3)).C2 ∧ (spohnRevision (Fin 3)).C3 ∧
      (spohnRevision (Fin 3)).C4 ∧ ¬ (spohnRevision (Fin 3)).CB := by
  refine ⟨spohnRevision_c1, spohnRevision_c2, spohnRevision_c3, spohnRevision_c4, fun h ↦ ?_⟩
  obtain ⟨-, -, -, -, -, h6⟩ := spohnRevision_faithful.cb_iff_c1_c2_c3_c4_c5_c6.1 h
  exact not_spohnRevision_c6 h6

/-! ### An operator satisfying (C1) but neither (C3) nor (C4) -/

section Diamond

variable {W : Type*}

open Classical in
/-- The operator `◇` of Theorem 15 is Spohn's, except that a disbelieved world of rank two or more
moves down a degree instead of up. -/
noncomputable def diamond (κ : W → ℕ) (μ : Set W) : W → ℕ := fun w ↦
  if w ∈ μ then aPart κ μ w else if κ w < 2 then κ w + 1 else κ w - 1

/-- `diamond` as a revision operator on rankings. -/
noncomputable def diamondRevision (W : Type*) : Revision (W → ℕ) W where
  bel κ := {w | κ w = 0}
  revise := diamond

@[simp] theorem diamondRevision_revise (κ : W → ℕ) (μ : Set W) :
    (diamondRevision W).revise κ μ = diamond κ μ :=
  rfl

theorem diamond_of_mem {κ : W → ℕ} {μ : Set W} {w : W} (hw : w ∈ μ) :
    diamond κ μ w = aPart κ μ w := by
  simp [diamond, hw]

theorem diamond_of_notMem {κ : W → ℕ} {μ : Set W} {w : W} (hw : w ∉ μ) :
    diamond κ μ w = if κ w < 2 then κ w + 1 else κ w - 1 := by
  simp [diamond, hw]

-- Theorem 15
theorem diamondRevision_faithful : (diamondRevision W).Faithful (fun κ ↦ Preorder.lift κ) :=
  faithful_lift (fun _ _ _ hw ↦ diamond_of_mem hw)
    (fun _ _ _ hw ↦ by rw [diamond_of_notMem hw]; split_ifs <;> omega)

theorem diamondRevision_isAGM : (diamondRevision W).IsAGM :=
  diamondRevision_faithful.isAGM

-- Theorem 15
theorem diamondRevision_c1 : (diamondRevision W).C1 :=
  diamondRevision_faithful.c1_iff.2 fun κ μ ↦ agreesOn_lift κ μ fun _ _ _ hw ↦ diamond_of_mem hw

end Diamond

/-- The prior of Table B.1. -/
def tableB1 : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 0

/-- Table B.1 after `diamond` by `μ`. -/
def tableB1' : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | 3 => 1

/-- The evidence `μ` of Tables B.1 and B.2. -/
abbrev μB : Set (Fin 4) := {w | w = 0 ∨ w = 1}

/-- The evidence `α` of Tables B.1 and B.2. -/
abbrev αB : Set (Fin 4) := {w | w = 1 ∨ w = 2}

theorem diamond_tableB1 : diamond tableB1 μB = tableB1' := by
  have h : rank tableB1 μB = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 | 3 => simp only [diamond, aPart, h]; simp [μB, tableB1, tableB1']

-- Table B.1, Theorem 15
theorem not_diamondRevision_c3 : ¬ (diamondRevision (Fin 4)).C3 := by
  intro h
  have := h tableB1 μB αB (by
    rw [diamondRevision_faithful.bel_revise, Set.subset_def]
    decide)
  rw [diamondRevision_faithful.bel_revise, diamondRevision_revise, diamond_tableB1] at this
  exact absurd (this (show (2 : Fin 4) ∈ (Preorder.lift tableB1').minimals αB by decide))
    (by decide)

/-- The prior of Table B.2. -/
def tableB2 : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | 3 => 0

/-- Table B.2 after `diamond` by `μ`. -/
def tableB2' : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

theorem diamond_tableB2 : diamond tableB2 μB = tableB2' := by
  have h : rank tableB2 μB = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 | 3 => simp only [diamond, aPart, h]; simp [μB, tableB2, tableB2']

-- Table B.2, Theorem 15
theorem not_diamondRevision_c4 : ¬ (diamondRevision (Fin 4)).C4 := by
  intro h
  refine h tableB2 μB αB ?_ ?_
  · rw [diamondRevision_faithful.bel_revise, Set.not_subset]
    exact ⟨1, by decide, fun h ↦ h (by decide)⟩
  · rw [diamondRevision_faithful.bel_revise, diamondRevision_revise, diamond_tableB2,
      Set.subset_def]
    simp only [Set.mem_compl_iff]
    decide

/-- Theorem 15: the operator `◇` satisfies (C1) but neither (C3) nor (C4). -/
theorem diamondRevision_c1_not_c3_c4 :
    (diamondRevision (Fin 4)).C1 ∧ ¬ (diamondRevision (Fin 4)).C3 ∧
      ¬ (diamondRevision (Fin 4)).C4 :=
  ⟨diamondRevision_c1, not_diamondRevision_c3, not_diamondRevision_c4⟩

end DarwichePearl1997
