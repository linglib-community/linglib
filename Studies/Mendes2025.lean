module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Tense.Defs

/-!
# Mendes (2025): Indefiniteness in future reference

Mendes analyses the Subordinate Future, a subjunctive combined with a forward-shifting temporal
morpheme, in Muskens's compositional discourse representation theory over situations. The
subjunctive is an indefinite that introduces a situation among the historical alternatives of
its anchor, and the indicative is the definite that retrieves it. A main clause is therefore
evaluated in the future situation its subordinate clause introduced (modal donkey anaphora), and
a strong quantifier whose restrictor carries the form has its existence presupposition satisfied
in a historical alternative rather than at the anchor (modal displacement).

## Main results

* `sfForm_true_at`: the truth conditions of the paper's conditional and relative-clause
  derivations.
* `temporal_shift`, `modal_donkey_anaphora`: the orderings of the paper's table of main-clause
  tenses, and the retrieval of the introduced situation.
* `subj_fut_true_at`, `ind_fut_true_at`: a restrictor in the Subordinate Future is true in some
  later historical alternative of the anchor, one in the indicative only in the anchor's world.

## Implementation notes

* States assign situations to registers only: individual drefs are saturated in the radicals
  (*Ivan leaves the room* is a situation predicate), so the quantifying-in of the relative clause
  reduces to the implication of its restrictor and nuclear scope.
* A situation is a world–time `Index`, and *s₂ is part of the world of s₁* is world identity.

## References

* [mendes-2025]
* [muskens-1996]
-/

@[expose] public section

namespace Mendes2025

open Semantics

open HistoricalAlternatives DynamicSemantics Update SetRel Kaplan
open RegisterStructure

variable {W T : Type*}

/-! ### Types -/

/-- A state assigns situations to drefs. -/
abbrev State (W T : Type*) := Assignment (Index W T)

/-- A situation dref, the type `s`. -/
abbrev Sit (W T : Type*) := State W T → Index W T

/-- A sentence radical, of type `st`, takes a situation dref to an update. -/
abbrev Radical (W T : Type*) := Sit W T → Update (State W T)

/-- A tensed radical, the type `(s, st)`, the argument of a mood morpheme. -/
abbrev Tensed (W T : Type*) := Sit W T → Sit W T → Update (State W T)

/-- The radical of a situation predicate, `λs.[ | P(s)]`. -/
def radical (P : Index W T → Prop) : Radical W T := fun s ↦ test {i | P (s i)}

/-! ### Lexical entries -/

/-- The indicative `ind^{s₂,s₁} ⇝ λℙ.[ | s₂ ≤ w_{s₁}]; ℙ(s₂)(s₁)` is a definite over situations,
testing that `s₂` is part of the world of `s₁`. -/
def ind (s₂ s₁ : Sit W T) (ℙ : Tensed W T) : Update (State W T) :=
  test {i | (s₂ i).world = (s₁ i).world} ○ ℙ s₂ s₁

variable {ℙ : Tensed W T} {s s' : Sit W T} {i o : State W T}

theorem ind_apply :
    i ~[ind s s' ℙ] o ↔ (s i).world = (s' i).world ∧ i ~[ℙ s s'] o := by
  simp [ind]

variable [LinearOrder T] (history : HistoricalAlternatives W T)

/-- A temporal morpheme `λ𝒫.λs.λs'.[ | τ(s) ⋈ τ(s')]; 𝒫(s)` tests that the running times of `s`
and `s'` compare within the cell, then runs the radical at `s`. -/
def temporal (cell : Finset Ordering) (P : Radical W T) (s s' : Sit W T) :
    Update (State W T) :=
  test {i | compare (s i).time (s' i).time ∈ cell} ○ P s

/-- `fut` places the event situation after the evaluation situation. -/
abbrev fut : Radical W T → Sit W T → Sit W T → Update (State W T) := temporal ⟦Tense.future⟧

/-- `pres` places the event situation at the evaluation situation. -/
abbrev pres : Radical W T → Sit W T → Sit W T → Update (State W T) := temporal ⟦Tense.present⟧

/-- `past` places the event situation before the evaluation situation. -/
abbrev past : Radical W T → Sit W T → Sit W T → Update (State W T) := temporal ⟦Tense.past⟧

/-- The subjunctive `subj^{s₁}_{s₀} ⇝ λℙ.[s₁ | s₁ ∈ hist s₀]; ℙ(s₁)(s₀)` is an indefinite over
situations, introducing `s₁` among the historical alternatives of the anchor `s₀`. -/
def subj (s₁ : ℕ) (s₀ : Sit W T) (ℙ : Tensed W T) : Update (State W T) :=
  box {s₁} {i | val s₁ i ∈ historicalBase history (s₀ i)} ○ ℙ (val s₁) s₀

/-! ### Unpacking the entries -/

variable {cell : Finset Ordering} {P : Index W T → Prop} {s₁ : ℕ}

theorem temporal_radical_apply :
    i ~[temporal cell (radical P) s s'] o ↔
      i = o ∧ compare (s o).time (s' o).time ∈ cell ∧ P (s o) := by
  rw [temporal, radical, test_comp_test]; exact Iff.rfl

theorem isTest_temporal_radical : IsTest (temporal cell (radical P) s s') :=
  (isTest_test _).comp (isTest_test _)

theorem subj_apply :
    i ~[subj history s₁ s ℙ] o ↔
      ∃ e, e ∈ historicalBase history (s (Function.update i s₁ e)) ∧
        Function.update i s₁ e ~[ℙ (val s₁) s] o := by
  simp only [subj, box_singleton, dexists, mem_comp, mem_randomAssign, mem_test]
  constructor
  · rintro ⟨_, ⟨_, ⟨e, rfl⟩, rfl, he⟩, hℙ⟩
    exact ⟨e, by simpa using he, hℙ⟩
  · rintro ⟨e, he, hℙ⟩
    exact ⟨_, ⟨_, ⟨e, rfl⟩, rfl, by simpa using he⟩, hℙ⟩

/-! ### The Subordinate Future

The forms `SF(A); tense(C)` of the paper's table of main-clause tenses: a conditional
antecedent or a relative clause carrying the Subordinate Future, `subj^{s₁}_{s₀}(fut(A))`, and
a main clause `ind^{s₂,s₁}(tense(C))` whose evaluation situation is the introduced `s₁`. The
anchor `s₀` is the dref `0`, the introduced situation the dref `1`, the main-clause situation
the dref `2`. -/

variable (A C : Index W T → Prop)

/-- A subordinate clause carrying the Subordinate Future and a main clause with the tense `cell`
form a dynamic implication, as in the conditional and the relative-clause quantification of the
paper's derivations. -/
def sfForm (cell : Finset Ordering) : Update (State W T) :=
  test (impl (subj history 1 (val 0) (fut (radical A)))
    (ind (val 2) (val 1) (temporal cell (radical C))))

/-- *If Ivan leaves the room smiling, the interview went well* has the Subordinate Future in the
antecedent and the past in the consequent. -/
abbrev conditional (leaves wentWell : Index W T → Prop) : Update (State W T) :=
  sfForm history leaves wentWell ⟦Tense.past⟧

/-- *Every candidate who delivers a good job talk has an equal chance of being hired* has the
Subordinate Future in the restrictor and the present in the nuclear scope. -/
abbrev relativeClause (delivers chance : Index W T → Prop) : Update (State W T) :=
  sfForm history delivers chance ⟦Tense.present⟧

/-- The form of the paper's derivations is a test, true at a state iff every historical
alternative `e` of the anchor after it where `A` holds has the main-clause situation in its
world, timed by the cell relative to `e`, satisfying `C`. -/
theorem sfForm_true_at :
    i ∈ (sfForm history A C cell).dom ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → A e →
        (i 2).world = e.world ∧ compare (i 2).time e.time ∈ cell ∧ C (i 2) := by
  rw [sfForm, dom_test]
  simp only [mem_impl, subj_apply, temporal_radical_apply, ind_apply, RegisterStructure.val_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_and_left, exists_eq_left']
  simp

theorem conditional_true_at (leaves wentWell : Index W T → Prop) :
    i ∈ (conditional history leaves wentWell).dom ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → leaves e →
        (i 2).world = e.world ∧ (i 2).time < e.time ∧ wentWell (i 2) := by
  simp only [conditional, sfForm_true_at, Tense.compare_mem_past]

theorem relativeClause_true_at (delivers chance : Index W T → Prop) :
    i ∈ (relativeClause history delivers chance).dom ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → delivers e →
        (i 2).world = e.world ∧ (i 2).time = e.time ∧ chance (i 2) := by
  simp only [relativeClause, sfForm_true_at, Tense.compare_mem_present]

variable {k l : State W T}

/-- The Subordinate Future places the situation it introduces after the anchor, and the main
clause is timed by its tense relative to that situation, not the anchor. The rows of the paper's
table of main-clause tenses are the cells `future`, `present` and `past`. -/
theorem temporal_shift (hk : i ~[subj history 1 (val 0) (fut (radical A))] k)
    (hl : k ~[ind (val 2) (val 1) (temporal cell (radical C))] l) :
    (l 0).time < (l 1).time ∧ compare (l 2).time (l 1).time ∈ cell := by
  obtain ⟨e, -, hk⟩ := (subj_apply history).mp hk
  obtain ⟨rfl, ht, -⟩ := temporal_radical_apply.mp hk
  obtain ⟨-, hl⟩ := ind_apply.mp hl
  obtain ⟨rfl, hc, -⟩ := temporal_radical_apply.mp hl
  exact ⟨by simpa using ht, hc⟩

/-- In modal donkey anaphora the indicative retrieves the situation the subjunctive introduced,
so the main clause is evaluated in a historical alternative of the anchor. -/
theorem modal_donkey_anaphora (hk : i ~[subj history 1 (val 0) (fut (radical A))] k)
    (hl : k ~[ind (val 2) (val 1) (temporal cell (radical C))] l) :
    (l 2).world ∈ history (l 0) := by
  obtain ⟨e, he, hk⟩ := (subj_apply history).mp hk
  obtain ⟨rfl, -, -⟩ := temporal_radical_apply.mp hk
  obtain ⟨hw, hl⟩ := ind_apply.mp hl
  obtain ⟨rfl, -, -⟩ := temporal_radical_apply.mp hl
  have h₁ := he.1
  simp at hw h₁ ⊢
  rwa [hw]

/-! ### Modal displacement

A restrictor carrying the Subordinate Future is true at a state iff some historical alternative
of the anchor, after it, satisfies it: the existence presupposition of a strong quantifier is
satisfied in a historical alternative, not at the anchor, which is why the continuation *I doubt
anyone will come at all* is felicitous. Under the indicative it must be satisfied in the
anchor's world. -/

/-- The Subordinate Future restrictor is true iff the anchor has a later historical alternative
satisfying `A`. -/
theorem subj_fut_true_at :
    i ∈ (subj history 1 (val 0) (fut (radical A))).dom ↔
      ∃ e ∈ historicalBase history (i 0), (i 0).time < e.time ∧ A e := by
  simp [subj_apply, temporal_radical_apply]

/-- The indicative restrictor is true iff its situation lies in the anchor's world, after the
anchor, and satisfies `A`. -/
theorem ind_fut_true_at :
    i ∈ (ind (val 2) (val 0) (fut (radical A))).dom ↔
      (i 2).world = (i 0).world ∧ (i 0).time < (i 2).time ∧ A (i 2) := by
  simp [ind_apply, temporal_radical_apply]

end Mendes2025
