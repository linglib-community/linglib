module

public import Linglib.Logic.BeliefRevision.Iterated
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# Darwiche and Pearl (1997): On the Logic of Iterated Belief Revision

This file formalizes the examples and appendix tables of Darwiche and Pearl's paper on iterated
belief revision.

The AGM postulates constrain a single revision of a belief set and leave the agent's
conditional beliefs, its disposition to revise, almost unconstrained, so an AGM-compatible
operator may drop a conditional belief because the observation that would have triggered it
arrived (an animal seen to fly is no longer believed to fly should it be a bird) or acquire
one (a lady believed smart and rich is no longer believed rich once evidence against her
smartness is overturned). The paper moves revision to epistemic states, weakens the postulate
of syntax-irrelevance accordingly, since two states with the same beliefs may revise
differently (two jurors who both believe A guilty but rank B and C differently), and adds four
postulates: revising by a weaker proposition before a stronger one is redundant (C1), by a
contradicted one is overridden (C2), evidence implied by later evidence is retained (C3), and
evidence not contradicted by later evidence stays uncontradicted (C4). Each is equivalent to a
condition on the faithful total preorders that represent the operator, Spohn's
conditionalisation satisfies them all, and Boutilier's stronger postulate, minimising every
change of conditional belief, forgets a colour observation once the animal's species is
corrected. That postulate is C1–C4 together with two more, C5 and C6, and Spohn's
conditionalisation violates C6. Four partial operators in the appendix show that the AGM
postulates entail none of C1–C4, and an operator that moves the disbelieved worlds of rank two
or more down rather than up satisfies C1 but neither C3 nor C4.

The framework and its theorems are in `Logic/BeliefRevision/Iterated.lean`; here the paper's
examples and appendix tables are checked against them.

## Implementation notes

* The worlds of an appendix table are the valuations of its two propositions, so a
  proposition is a set of pairs of Booleans, `first` and `second` naming the two.
* A table gives only the preorders before and after one revision; its compatibility with the
  postulates is that the revised belief worlds are the least evidence-worlds of the prior.

## References

* [A. Darwiche and J. Pearl, *On the logic of iterated belief revision*
  (1997)][darwiche-pearl-1997]
* [C. Boutilier, *Iterated revision and minimal change of conditional beliefs*
  (1996)][boutilier-1996]
* [M. Goldszmidt and J. Pearl, *Qualitative probabilities for default reasoning, belief
  revision, and causal modeling* (1996)][goldszmidt-pearl-1996]
-/

@[expose] public section

namespace DarwichePearl1997

open BeliefRevision RankingFunction

/-! ### Epistemic states against belief sets -/

/-- The suspects of the murder trial of Example 3, which the paper takes from Goldszmidt and Pearl.
-/
inductive Suspect
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- The first juror holds A guilty, B a remote possibility and C innocent. -/
def juror₁ : Suspect → ℕ
  | .a => 0
  | .b => 1
  | .c => 2

/-- The second juror holds A guilty, C a remote possibility and B innocent. -/
def juror₂ : Suspect → ℕ
  | .a => 0
  | .c => 1
  | .b => 2

theorem jurors_bel :
    (spohnRevision Suspect).bel juror₁ = (spohnRevision Suspect).bel juror₂ := by
  ext w
  cases w <;> simp [spohnRevision, juror₁, juror₂]

theorem jurors_revise :
    Suspect.b ∈
        (spohnRevision Suspect).bel ((spohnRevision Suspect).revise juror₁ {w | w ≠ .a}) ∧
      Suspect.b ∉
        (spohnRevision Suspect).bel ((spohnRevision Suspect).revise juror₂ {w | w ≠ .a}) := by
  rw [spohnRevision_faithful.bel_revise, spohnRevision_faithful.bel_revise]
  decide

/-! ### The appendix tables -/

/-- A world of a language with two propositions gives the truth values of its propositions. -/
abbrev World := Bool × Bool

/-- The first proposition. -/
abbrev first : Set World := {w | w.1 = true}

/-- The second proposition. -/
abbrev second : Set World := {w | w.2 = true}

/-- Table 1, before revising by `¬(adder_ok ∧ multiplier_ok)`. -/
def table₁ : World → ℕ
  | (true, true) => 0
  | (true, false) => 1
  | (false, true) => 2
  | (false, false) => 3

/-- Table 1, after. -/
def table₁' : World → ℕ
  | (true, true) => 1
  | (true, false) => 0
  | (false, true) => 2
  | (false, false) => 1

/-- In Example 6, a revision compatible with the basic postulates violates (C1) and (CR1). -/
theorem example₆ :
    (∀ w, w ∈ (Preorder.lift table₁').minimals Set.univ ↔
      w ∈ (Preorder.lift table₁).minimals {w | ¬ (w ∈ first ∧ w ∈ second)}) ∧
    (∀ w, w ∈ (Preorder.lift table₁).minimals {w | w ∉ first} ↔ w = (false, true)) ∧
    (∀ w, w ∈ (Preorder.lift table₁').minimals {w | w ∉ first} ↔ w = (false, false)) ∧
    ¬ AgreesOn (Preorder.lift table₁) (Preorder.lift table₁')
      {w | ¬ (w ∈ first ∧ w ∈ second)} := by
  decide

/-- Table 2, before revising by `¬smart`. -/
def table₂ : World → ℕ
  | (true, true) => 0
  | (true, false) => 1
  | (false, true) => 1
  | (false, false) => 2

/-- Table 2, after. -/
def table₂' : World → ℕ
  | (true, true) => 2
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

/-- In Example 7, revising by `smart` violates (C2) and (CR2). -/
theorem example₇ :
    (∀ w, w ∈ (Preorder.lift table₂').minimals Set.univ ↔
      w ∈ (Preorder.lift table₂).minimals {w | w ∉ first}) ∧
    (∀ w, w ∈ (Preorder.lift table₂).minimals first ↔ w = (true, true)) ∧
    (∀ w, w ∈ (Preorder.lift table₂').minimals first ↔ w = (true, false)) ∧
    ¬ AgreesOn (Preorder.lift table₂) (Preorder.lift table₂') first := by
  decide

/-- Table 3, before revising by `flies`. -/
def table₃ : World → ℕ
  | (true, true) => 2
  | (true, false) => 3
  | (false, true) => 1
  | (false, false) => 0

/-- Table 3, after. -/
def table₃' : World → ℕ
  | (true, true) => 1
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

/-- In Example 8, revising by `bird` violates (C3) and (CR3). -/
theorem example₈ :
    (∀ w, w ∈ (Preorder.lift table₃').minimals Set.univ ↔
      w ∈ (Preorder.lift table₃).minimals second) ∧
    (∀ w, w ∈ (Preorder.lift table₃).minimals first ↔ w = (true, true)) ∧
    (∀ w, w ∈ (Preorder.lift table₃').minimals first ↔ w ∈ first) ∧
    ¬ PreservesLt (Preorder.lift table₃) (Preorder.lift table₃') second secondᶜ := by
  decide

/-- Table 4, before revising by `nice_day`. -/
def table₄ : World → ℕ
  | (true, true) => 1
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 0

/-- Table 4, after. -/
def table₄' : World → ℕ
  | (true, true) => 2
  | (true, false) => 1
  | (false, true) => 0
  | (false, false) => 1

/-- In Example 9, revising by `shining_sun` violates (C4) and (CR4). -/
theorem example₉ :
    (∀ w, w ∈ (Preorder.lift table₄').minimals Set.univ ↔
      w ∈ (Preorder.lift table₄).minimals second) ∧
    (∀ w, w ∈ (Preorder.lift table₄).minimals first ↔ w ∈ first) ∧
    (∀ w, w ∈ (Preorder.lift table₄').minimals first ↔ w = (true, false)) ∧
    ¬ PreservesLe (Preorder.lift table₄) (Preorder.lift table₄') second secondᶜ := by
  decide

/-! ### Boutilier's postulate forgets -/

/-- Under (CB), finding a red bird not to be a bird leaves only the belief that it is not a bird,
provided `¬bird` alone left the colour open (Example 10). -/
theorem cb_forgets {S W : Type*} {r : Revision S W} (h : r.IsAGM) (hCB : r.CB) {Ψ : S}
    {bird red : Set W} (hΨ : r.bel Ψ = bird) (hne : (bird ∩ red).Nonempty)
    (hΨ' : r.bel (r.revise Ψ birdᶜ) = birdᶜ) :
    r.bel (r.revise (r.revise Ψ red) birdᶜ) = birdᶜ := by
  rw [hCB Ψ red birdᶜ (by
    rw [h.expansion Ψ red (by rwa [hΨ]), hΨ, compl_compl]
    exact Set.inter_subset_left), hΨ']

/-! ### Boutilier's postulate is stronger than (C1)–(C4) -/

/-- A prior believing world `0`, with the `μ`-world `1` less plausible than the non-`μ`-world
`2`. -/
def table₇ : Fin 3 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 1

/-- `table₇` after Spohn's revision by `μ₇`. -/
def table₇' : Fin 3 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 2

/-- The evidence of `table₇`. -/
abbrev μ₇ : Set (Fin 3) := {w | w ≠ 2}

theorem spohn_table₇ : spohn table₇ μ₇ = table₇' := by
  have h : rank table₇ μ₇ = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 => simp only [spohn, aPart, h]; simp [μ₇, table₇, table₇']

theorem not_spohnRevision_c6 : ¬ (spohnRevision (Fin 3)).C6 := by
  intro h
  have hlt := spohnRevision_faithful.c6_iff.1 h table₇ μ₇ 2 (by simp) 1
    ⟨by simp, by simp [spohnRevision, spohn_table₇, table₇']⟩ (by decide)
  change spohn table₇ μ₇ 2 < spohn table₇ μ₇ 1 at hlt
  rw [spohn_table₇] at hlt
  exact absurd hlt (by decide)

/-- (CB) implies (C1)–(C4) but is not implied by them (Section 7): Spohn's revision meets (C1)–(C4)
and violates (CB), since it violates (C6). -/
theorem spohnRevision_c1_c2_c3_c4_not_cb :
    (spohnRevision (Fin 3)).C1 ∧ (spohnRevision (Fin 3)).C2 ∧ (spohnRevision (Fin 3)).C3 ∧
      (spohnRevision (Fin 3)).C4 ∧ ¬ (spohnRevision (Fin 3)).CB :=
  ⟨spohnRevision_c1, spohnRevision_c2, spohnRevision_c3, spohnRevision_c4, fun h ↦
    not_spohnRevision_c6 (spohnRevision_faithful.cb_iff_c1_c2_c3_c4_c5_c6.1 h).2.2.2.2.2⟩

/-! ### An operator satisfying (C1) but neither (C3) nor (C4) -/

open Classical in
/-- The operator of Theorem 6 is Spohn's, except that a disbelieved world of rank two or more moves
down a degree instead of up. -/
noncomputable def diamond {W : Type*} (κ : W → ℕ) (μ : Set W) : W → ℕ := fun w ↦
  if w ∈ μ then aPart κ μ w else if κ w < 2 then κ w + 1 else κ w - 1

/-- `diamond` as a revision operator on rankings. -/
noncomputable def diamondRevision (W : Type*) : Revision (W → ℕ) W where
  bel κ := {w | κ w = 0}
  revise := diamond

theorem diamond_of_mem {W : Type*} {κ : W → ℕ} {μ : Set W} {w : W} (hw : w ∈ μ) :
    diamond κ μ w = aPart κ μ w := by
  simp [diamond, hw]

theorem diamond_of_notMem {W : Type*} {κ : W → ℕ} {μ : Set W} {w : W} (hw : w ∉ μ) :
    diamond κ μ w = if κ w < 2 then κ w + 1 else κ w - 1 := by
  simp [diamond, hw]

/-- The rankings' orderings represent `diamond`, so it satisfies the postulates (Theorem 6). -/
theorem diamondRevision_faithful (W : Type*) :
    (diamondRevision W).Faithful (fun κ ↦ Preorder.lift κ) :=
  faithful_lift (fun _ _ _ hw ↦ diamond_of_mem hw)
    (fun _ _ _ hw ↦ by rw [diamond_of_notMem hw]; split_ifs <;> omega)

theorem diamondRevision_isAGM (W : Type*) : (diamondRevision W).IsAGM :=
  (diamondRevision_faithful W).isAGM

/-- `diamond` satisfies (C1) (Theorem 6). -/
theorem diamondRevision_c1 (W : Type*) : (diamondRevision W).C1 :=
  (diamondRevision_faithful W).c1_iff.2 fun κ μ ↦ agreesOn_lift κ μ fun _ _ _ hw ↦ diamond_of_mem hw

/-- The prior of Table 5. -/
def table₅ : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 0

/-- Table 5 after `diamond` by `μ`. -/
def table₅' : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | 3 => 1

/-- The evidence `μ` of Tables 5 and 6. -/
abbrev μ₅ : Set (Fin 4) := {w | w = 0 ∨ w = 1}

/-- The evidence `α` of Tables 5 and 6. -/
abbrev α₅ : Set (Fin 4) := {w | w = 1 ∨ w = 2}

theorem diamond_table₅ : diamond table₅ μ₅ = table₅' := by
  have h : rank table₅ μ₅ = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 | 3 => simp only [diamond, aPart, h]; simp [μ₅, table₅, table₅']

/-- `diamond` violates (C3), by Table 5 (Theorem 6). -/
theorem not_diamondRevision_c3 : ¬ (diamondRevision (Fin 4)).C3 := by
  intro h
  have := h table₅ μ₅ α₅ (by
    rw [(diamondRevision_faithful _).bel_revise, Set.subset_def]
    decide)
  rw [(diamondRevision_faithful _).bel_revise] at this
  change (Preorder.lift (diamond table₅ μ₅)).minimals α₅ ⊆ μ₅ at this
  rw [diamond_table₅] at this
  exact absurd (this (show (2 : Fin 4) ∈ (Preorder.lift table₅').minimals α₅ by decide))
    (by decide)

/-- The prior of Table 6. -/
def table₆ : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | 3 => 0

/-- Table 6 after `diamond` by `μ`. -/
def table₆' : Fin 4 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

theorem diamond_table₆ : diamond table₆ μ₅ = table₆' := by
  have h : rank table₆ μ₅ = 0 := (rank_eq_zero_iff _).2 ⟨0, by decide, rfl⟩
  funext w
  match w with
  | 0 | 1 | 2 | 3 => simp only [diamond, aPart, h]; simp [μ₅, table₆, table₆']

/-- `diamond` violates (C4), by Table 6 (Theorem 6). -/
theorem not_diamondRevision_c4 : ¬ (diamondRevision (Fin 4)).C4 := by
  intro h
  refine h table₆ μ₅ α₅ ?_ ?_
  · rw [(diamondRevision_faithful _).bel_revise, Set.not_subset]
    exact ⟨1, by decide, fun h ↦ h (by decide)⟩
  · rw [(diamondRevision_faithful _).bel_revise]
    change (Preorder.lift (diamond table₆ μ₅)).minimals α₅ ⊆ μ₅ᶜ
    rw [diamond_table₆, Set.subset_def]
    simp only [Set.mem_compl_iff]
    decide

end DarwichePearl1997
