module

public import Linglib.Data.Examples.Hofmann2025
public import Linglib.Semantics.Dynamic.ICDRT

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

Every indefinite introduces its discourse referent globally, relative to its own local context, and
a pronoun needs that referent throughout its own local context under consistent speaker commitments.
Over an arbitrary model this derives that [a negated antecedent leaves a veridical anaphor no
consistent commitments](##mem_dom_thereIsnt_comp_itIs), that
[double negation](##mem_dom_notThereIsnt_comp_itIs) and
[the bathroom disjunction](##mem_dom_thereIsntOr) have the weak reading, that
[interlocutors who disagree stay consistent](##mem_dom_disagree), and that [a hypothetical anaphor
can have a counterfactual antecedent](##disjoint_of_mem_thereIsnt_comp_believes). The paper's
figures and tables are instances on its models.

## Implementation notes

* The operators of the fragment are CDRT's: a DRS `[δ | C]` is `box {δ} C`. Maximization is
  `Update.maxInput`, the repair of (40) that the Errata explain. `HasTruthSet` says of a clause
  that one value of its context is greatest, so that the truth conditions of the operators compose.
* This file follows the formulas on commitment sets, in which one is a register fixed by the initial
  state. The commitment sets a discourse allows, Table 1's column, range over initial states, and
  pragmatic maximization (35) is `maxInput φDC`. Consistency (31) holds of every state, so
  `Acceptable` reads it off the initial state.
* `Clause.knows` is the veridical attitude of §2.4, which Appendix C does not list, and `Cole said`
  in (6c) and (13a) is `believes` at a doxastic state of its own. `dox₃` is one doxastic state with
  the column of Table 4, which fixes no more. Appendix C's conjunction (18d) enters no derivation
  and is not encoded.
* The second clause of (15) is run without its modal `have to`, so the theorem equally covers
  *There isn't a bathroom. It isn't upstairs*, on which the paper gives no judgment.
* In (44) the outer maximization forces `υ` to an upstairs bathroom wherever one exists; in (43)
  it leaves `υ` free, and the anaphor's context picks the worlds where it is upstairs.

## Errata

* (40) cites Brasoveanu, whose `max^u(D)` introduces `u` under the operator ([brasoveanu-2007] (40),
  p. 148; [brasoveanu-2010] (69), p. 466). Hofmann's omits it, and (18a) tests `φ ≡ φ̄'` between
  `[φ']` and the operator, so that restoring it would overwrite what the test constrains. As printed
  every maximization ranges over updates that fix its dref, and `Update.maxAt_eq_of_fixes` makes it
  vacuous: every row of Table 3 is [an output of (41)](##mem_printed41), including a speaker who
  commits to a bathroom world and asserts that there is no bathroom. Comparing values of the dref,
  and leaving (18) and (19) as printed, [selects the first row](##mem_thereIsnt_bathroom), [only
  removes outputs](##thereIsnt_subset_printed41), and with nothing between `[φ]` and the operator
  [is Brasoveanu's](##DynamicSemantics.Update.randomAssign_comp_maxInput). (26) survives the defect:
  [it needs no maximization](##eq_empty_of_mem_printed41_comp_printedIt).
* Figures 3 and 4 and pp. 12, 14 and 28 narrow a commitment set, but (19) has no `[φDC]`, and
  Tables 1 and 2 instead eliminate its possible values. [No assertion changes a commitment
  set](##Clause.fixes_dec), so (35) and the formal clause of (21a) hold of every update. A `P` with
  no successful update is true by that clause and false by (21c), and (21d) and (21e) collapse with
  it, so the "contextually entails" of (45) is read here as inclusion of contexts.
* An indefinite outscoping negation, *a bathroom isn't upstairs*, [has a context of every
  world](##eq_univ_of_mem_indefinite_not_it) under (16), (18a) and (25), so it [has no output on
  M₁](##not_mem_indefinite_not_it): the negated scope needs the referent exactly outside the worlds
  where it exists. (1) restricts itself to unspecific indefinites, and the fragment derives no
  other.
* (18c) and (18d) subscript `max` with the unbound `φ₁`, and (18d)'s first box prints the trivial
  `φ ⋐ φ` for `φ ⋐ φ'`. (52) omits `φ₄` from the box in which (18e) introduces it. p. 18 cites (21)
  for (19), and p. 28 swaps the antecedent (19b) and the anaphor (30).

## TODO

* `would` and `might`, for (2d), (6b), (8), (11), (15)'s modal, (42d) and (55), and the attitudes of
  (53) and (54).
* Commitment sets that narrow, for Figures 3 and 4 and (21).
* A specific indefinite that outscopes negation.
* The projective inferences of (5), which §4.1.2 sets aside.
* Plural anaphora (57b) in `Semantics/Dynamic/PCDRT.lean`, and the comparison of §5 with
  `Semantics/Dynamic/Bilateral.lean`.

## References

* [hofmann-2025]
* [muskens-1996]
* [stone-1999]
* [brasoveanu-2007]
* [brasoveanu-2010]
* [krahmer-muskens-1995]
* [roberts-1989]
* [karttunen-1976]
-/

@[expose] public section

namespace Hofmann2025

open DynamicSemantics
open DynamicSemantics.Update (test box maxAt maxInput maxInput_subset Fixes mem_box_singleton_comp
  mem_test_iff_left)
open ICDRT SetRel

variable {W E : Type*} {i j : State W E} {φ φ' φ'' r : PVar} {v : IVar} {D : Update (State W E)}

/-! ### The fragment of Appendix C -/

/-- A clause, of type `wt`, takes a local context to an update. -/
abbrev Clause (W E : Type*) := PVar → Update (State W E)

/-- A common noun or intransitive verb is a test that its argument satisfies it in the local
context (App. C (15)). -/
def commonNoun (R : E → W → Prop) : IVar → Clause W E := fun v φ ↦ test (predication R φ v)

/-- The indefinite introduces its dref relative to the local context, then runs its restrictor
and its scope (App. C (16)). -/
def indefinite (v : IVar) (P P' : IVar → Clause W E) : Clause W E :=
  fun φ ↦ relUpdate φ v ○ P v φ ○ P' v φ

/-- A pronoun passes its index to the predicate (App. C (17)). -/
def pronoun (v : IVar) (P : IVar → Clause W E) : Clause W E := P v

/-- A proper name introduces a dref equal to its constant (App. C (14)). -/
def properName (a : E) (v : IVar) (P : IVar → Clause W E) : Clause W E :=
  fun φ ↦ box {v} {j | j.indiv v = fun _ ↦ Part.some a} ○ P v φ

namespace Clause

/-- Negation introduces the complement of its context as the prejacent's context (App. C (18a)). -/
def not (P : Clause W E) (φ' : PVar) : Clause W E :=
  fun φ ↦ box {φ'} (eqCompl φ φ') ○ maxInput φ' (P φ')

/-- A binary connective introduces a context for each operand and relates its own to them by the
static function `f` (App. C (18b), (18c)). -/
def connective (f : Set W → Set W → Set W) (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E :=
  fun φ ↦ box {φ', φ''} {j | j.prop φ = f (j.prop φ') (j.prop φ'')} ○ maxInput φ' (P φ') ○
    maxInput φ'' (Q φ'')

/-- Disjunction's context is the union of the contexts of its disjuncts (App. C (18b)). -/
abbrev or (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E := connective (· ∪ ·) P Q φ' φ''

/-- The conditional's context is the union of the antecedent's complement and the consequent's
context (App. C (18c)). -/
abbrev ifThen (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E :=
  connective (fun s t ↦ sᶜ ∪ t) P Q φ' φ''

/-- The relation `believe_φ(υ, φ')` of fn. 14: at each world of `φ`, the doxastic state of the
referent of `υ` entails `φ'`. -/
def believe (dox : E → W → Set W) (φ : PVar) (v : IVar) (φ' : PVar) : Condition (State W E) :=
  {i | i.prop φ ⊆ sat (fun a w ↦ dox a w ⊆ i.prop φ') (i.indiv v)}

/-- An attitude verb introduces a context the subject's doxastic state entails (App. C (18e)). -/
def believed (dox : E → W → Set W) (P : Clause W E) (φ' : PVar) : IVar → Clause W E :=
  fun v φ ↦ box {φ'} (believe dox φ v φ') ○ maxInput φ' (P φ')

/-- A veridical attitude's complement is, moreover, entailed by its context (§2.4). -/
def knows (dox : E → W → Set W) (P : Clause W E) (φ' : PVar) : IVar → Clause W E :=
  fun v φ ↦ box {φ'} (believe dox φ v φ' ∩ incl φ φ') ○ maxInput φ' (P φ')

/-- The declarative introduces the assertion's context, which the speaker's commitments entail
(20a), and maximizes it over the clause (App. C (19)). -/
def dec (P : Clause W E) (φDC φ : PVar) : Update (State W E) :=
  box {φ} (incl φDC φ) ○ maxInput φ (P φ)

end Clause

/-! ### Truth sets -/

variable {R S : E → W → Prop} {P Q : Clause W E} {T : (IVar → W →. E) → Set W}

/-- A clause has truth set `T`, read off the referents of the individual drefs, at the context `φ`
if `T` is the greatest value of `φ` at which it succeeds. -/
def Clause.HasTruthSet (P : Clause W E) (φ : PVar) (T : (IVar → W →. E) → Set W) : Prop :=
  ∀ i : State W E, IsGreatest {s | i.updateProp φ s ∈ (P φ).dom} (T i.indiv)

theorem Clause.HasTruthSet.mem_max (hP : P.HasTruthSet φ T) :
    i ~[maxInput φ (P φ)] j ↔ i.prop φ = T i.indiv ∧ i ~[P φ] j :=
  Update.mem_maxInput_of_isGreatest (hP i)

theorem Clause.HasTruthSet.of_mem_dom_iff (h : ∀ i, i ∈ (P φ).dom ↔ i.prop φ ⊆ T i.indiv) :
    P.HasTruthSet φ T :=
  fun i ↦ ⟨by simp [h], fun s hs ↦ by simpa [h] using hs⟩

theorem Clause.HasTruthSet.mem_box_comp_max {C : Condition (State W E)} (hP : P.HasTruthSet φ T) :
    i ~[box {φ} C ○ maxInput φ (P φ)] j ↔
      i.updateProp φ (T i.indiv) ∈ C ∧ i.updateProp φ (T i.indiv) ~[P φ] j := by
  simp only [mem_box_singleton_comp, extend_pvar, hP.mem_max, State.updateProp_prop_self,
    State.updateProp_indiv]
  exact ⟨fun ⟨_, hC, rfl, hj⟩ ↦ ⟨hC, hj⟩, fun ⟨hC, hj⟩ ↦ ⟨_, hC, rfl, hj⟩⟩

theorem Clause.HasTruthSet.mem_not (hφ : φ ≠ φ') (hP : P.HasTruthSet φ' T) :
    i ~[P.not φ' φ] j ↔ i.prop φ = (T i.indiv)ᶜ ∧ i.updateProp φ' (T i.indiv) ~[P φ'] j :=
  hP.mem_box_comp_max.trans <| and_congr_left' <| by
    simp [eqCompl, State.updateProp_prop_of_ne _ hφ]

theorem Clause.HasTruthSet.not (hφ : φ ≠ φ') (hP : P.HasTruthSet φ' T) :
    (P.not φ').HasTruthSet φ fun g ↦ (T g)ᶜ := fun i ↦ by
  refine ⟨?_, fun s ⟨_, hs⟩ ↦ ?_⟩
  · obtain ⟨j, hj⟩ := (hP (i.updateProp φ (T i.indiv)ᶜ)).1
    exact ⟨j, (hP.mem_not hφ).mpr ⟨by simp, by simpa using hj⟩⟩
  · simpa using ((hP.mem_not hφ).mp hs).1.le

theorem Clause.HasTruthSet.mem_dec (hφ : r ≠ φ) (hP : P.HasTruthSet φ T) :
    i ~[P.dec r φ] j ↔ i.prop r ⊆ T i.indiv ∧ i.updateProp φ (T i.indiv) ~[P φ] j :=
  hP.mem_box_comp_max.trans <| and_congr_left' <| by
    simp [incl, State.updateProp_prop_of_ne _ hφ]

theorem Clause.HasTruthSet.mem_dom_dec (hφ : r ≠ φ) (hP : P.HasTruthSet φ T) :
    i ∈ (P.dec r φ).dom ↔ i.prop r ⊆ T i.indiv := by
  simp only [SetRel.mem_dom, hP.mem_dec hφ, exists_and_left, and_iff_left_iff_imp]
  exact fun _ ↦ (hP i).1

/-! ### The clauses -/

/-- *There is an `R`* (24) is the indefinite with a vacuous scope (fn. 8). -/
def existential (R : E → W → Prop) (v : IVar) : Clause W E :=
  indefinite v (commonNoun R) fun _ _ ↦ SetRel.id

/-- *It is `S`* (30) is the pronoun with the predicate. -/
def it (S : E → W → Prop) (v : IVar) : Clause W E := pronoun v (commonNoun S)

theorem mem_existential :
    i ~[existential R v φ] j ↔ ∃ e, IsWitness R (i.prop φ) e ∧ j = i.updateIndiv v e := by
  constructor
  · rintro ⟨_, ⟨_, hrel, rfl, hp⟩, rfl⟩
    obtain ⟨⟨e, rfl⟩, hdom⟩ := mem_relUpdate.mp hrel
    simp only [extend_ivar, State.updateIndiv_prop, State.updateIndiv_indiv_self] at hdom
    exact ⟨e, ⟨hdom, by simpa using hp⟩, rfl⟩
  · rintro ⟨e, ⟨hdom, hsat⟩, rfl⟩
    exact ⟨_, ⟨_, updateIndiv_mem_relUpdate hdom, rfl, by simpa using hsat⟩, rfl⟩

theorem mem_it : i ~[it S v φ] j ↔ i = j ∧ i.prop φ ⊆ sat S (i.indiv v) :=
  mem_test_iff_left

theorem hasTruthSet_existential : (existential R v).HasTruthSet φ fun _ ↦ witnessed R :=
  .of_mem_dom_iff fun i ↦ by
    refine ⟨fun ⟨j, hj⟩ ↦ ?_, fun hs ↦ ?_⟩
    · obtain ⟨e, he, -⟩ := mem_existential.mp hj
      exact he.subset_witnessed
    · obtain ⟨e, he, -⟩ := exists_isWitness_sat hs ⊤
      exact ⟨_, mem_existential.mpr ⟨e, he, rfl⟩⟩

theorem hasTruthSet_it : (it S v).HasTruthSet φ fun g ↦ sat S (g v) :=
  .of_mem_dom_iff fun i ↦ ⟨fun ⟨_, hj⟩ ↦ (mem_it.mp hj).2, fun h ↦ ⟨i, mem_it.mpr ⟨rfl, h⟩⟩⟩

theorem mem_dec_it (hr : r ≠ φ) :
    i ~[(it S v).dec r φ] j ↔ i.prop r ⊆ sat S (i.indiv v) ∧
      j = i.updateProp φ (sat S (i.indiv v)) := by
  rw [hasTruthSet_it.mem_dec hr, mem_it]
  simp [eq_comm]

-- (24)
theorem fixes_existential (r : PVar) : Fixes r (existential R v φ) :=
  ((fixes_relUpdate r φ v).comp (Update.fixes_test r _)).comp (Update.fixes_id r)

-- (21a): no assertion changes a commitment set
theorem Clause.fixes_dec {φDC : PVar} (h : r ≠ φ) (hP : Fixes r (P φ)) : Fixes r (P.dec φDC φ) :=
  (Update.fixes_box (by simpa using h) _).comp ((Update.fixes_test r _).comp hP)

/-! ### Antecedent and anaphor -/

/-- The drefs of the derivations: the assertion's context and those of embedded clauses, the
commitment sets of the speaker and of the interlocutors of §4.3, the indefinite, and the attitude's
subject. -/
def φ₁ : PVar := ⟨1⟩
@[inherit_doc φ₁] def φ₂ : PVar := ⟨2⟩
@[inherit_doc φ₁] def φ₃ : PVar := ⟨3⟩
@[inherit_doc φ₁] def φ₄ : PVar := ⟨4⟩
@[inherit_doc φ₁] def φDC : PVar := ⟨10⟩
@[inherit_doc φ₁] def φDCA : PVar := ⟨11⟩
@[inherit_doc φ₁] def φDCB : PVar := ⟨12⟩
@[inherit_doc φ₁] def υ : IVar := ⟨0⟩
@[inherit_doc φ₁] def υ₂ : IVar := ⟨1⟩

/-- *There is an `R`* (19a), asserted. -/
abbrev thereIs (R : E → W → Prop) : Update (State W E) := (existential R υ).dec φDC φ₁

/-- *There isn't an `R`* (19b), (41), asserted by the speaker whose commitment set is `s`. -/
abbrev thereIsnt (R : E → W → Prop) (s : PVar) : Update (State W E) :=
  ((existential R υ).not φ₂).dec s φ₁

/-- *It's not the case that there isn't an `R`* (43), asserted. -/
abbrev notThereIsnt (R : E → W → Prop) : Update (State W E) :=
  (((existential R υ).not φ₃).not φ₂).dec φDC φ₁

/-- *It is `S`* (30), asserted by the speaker whose commitment set is `s`, in the context `φ`. -/
abbrev itIs (S : E → W → Prop) (s φ : PVar) : Update (State W E) := (it S υ).dec s φ

/-- *Either there isn't an `R`, or it is `S`* (44), asserted. -/
abbrev thereIsntOr (R S : E → W → Prop) : Update (State W E) :=
  (((existential R υ).not φ₄).or (it S υ) φ₂ φ₃).dec φDC φ₁

theorem mem_thereIs :
    i ~[thereIs R] j ↔ i.prop φDC ⊆ witnessed R ∧ ∃ e, IsWitness R (witnessed R) e ∧
      j = (i.updateProp φ₁ (witnessed R)).updateIndiv υ e := by
  simp [hasTruthSet_existential.mem_dec (by decide : φDC ≠ φ₁), mem_existential]

theorem mem_thereIsnt {s : PVar} (hs : s ≠ φ₁) :
    i ~[thereIsnt R s] j ↔ i.prop s ⊆ (witnessed R)ᶜ ∧ ∃ e, IsWitness R (witnessed R) e ∧
      j = ((i.updateProp φ₁ (witnessed R)ᶜ).updateProp φ₂ (witnessed R)).updateIndiv υ e := by
  simp [(hasTruthSet_existential.not (by decide : φ₁ ≠ φ₂)).mem_dec hs,
    hasTruthSet_existential.mem_not (by decide : φ₁ ≠ φ₂), mem_existential]

theorem mem_notThereIsnt :
    i ~[notThereIsnt R] j ↔ i.prop φDC ⊆ witnessed R ∧ ∃ e, IsWitness R (witnessed R) e ∧
      j = (((i.updateProp φ₁ (witnessed R)).updateProp φ₂ (witnessed R)ᶜ).updateProp φ₃
        (witnessed R)).updateIndiv υ e := by
  have hP := hasTruthSet_existential (R := R) (v := υ) (φ := φ₃)
  simp [((hP.not (by decide : φ₂ ≠ φ₃)).not (by decide : φ₁ ≠ φ₂)).mem_dec (by decide : φDC ≠ φ₁),
    (hP.not (by decide : φ₂ ≠ φ₃)).mem_not (by decide : φ₁ ≠ φ₂),
    hP.mem_not (by decide : φ₂ ≠ φ₃), mem_existential]

theorem mem_dom_comp {U : Update (State W E)} : i ∈ (D ○ U).dom ↔ ∃ k, i ~[D] k ∧ k ∈ U.dom :=
  ⟨fun ⟨j, k, h, h'⟩ ↦ ⟨k, h, j, h'⟩, fun ⟨k, h, j, h'⟩ ↦ ⟨j, k, h, h'⟩⟩

/-- A veridical anaphor to a negated antecedent leaves the speaker no consistent commitments
(§3.4.2), whatever the model. -/
theorem mem_dom_thereIsnt_comp_itIs :
    i ∈ (thereIsnt R φDC ○ itIs S φDC φ₃).dom ↔ i.prop φDC = ∅ := by
  have : (witnessed R)ᶜ ∩ witnessed (R ⊓ S) = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨h, h'⟩ ↦ h (witnessed_inf_subset_left h')
  simp (decide := true) [mem_thereIsnt, mem_dec_it, and_assoc, exists_isWitness_subset_sat_iff,
    ← Set.subset_inter_iff, this]

-- (18a), (18c): the weak reading of a veridical antecedent
theorem mem_dom_thereIs_comp_itIs :
    i ∈ (thereIs R ○ itIs S φDC φ₃).dom ↔ i.prop φDC ⊆ witnessed (R ⊓ S) := by
  simpa (decide := true) [mem_thereIs, mem_dec_it, and_assoc, exists_isWitness_subset_sat_iff]
    using fun h ↦ h.trans witnessed_inf_subset_left

/-- A veridical anaphor to a doubly negated antecedent has the weak reading of §4.5: it is true
where some `R` is an `S`, whatever other `R`s there are. -/
theorem mem_dom_notThereIsnt_comp_itIs :
    i ∈ (notThereIsnt R ○ itIs S φDC φ₄).dom ↔ i.prop φDC ⊆ witnessed (R ⊓ S) := by
  simpa (decide := true) [mem_notThereIsnt, mem_dec_it, and_assoc,
    exists_isWitness_subset_sat_iff] using fun h ↦ h.trans witnessed_inf_subset_left

/-- Interlocutors may contradict each other (§4.3): `A` commits that there is no `R`, `B` that an
`R` is an `S`, and neither commitment set need be empty. -/
theorem mem_dom_disagree :
    i ∈ (thereIsnt R φDCA ○ itIs S φDCB φ₃).dom ↔
      i.prop φDCA ⊆ (witnessed R)ᶜ ∧ i.prop φDCB ⊆ witnessed (R ⊓ S) := by
  simp (decide := true) [mem_thereIsnt, mem_dec_it, and_assoc, exists_isWitness_subset_sat_iff]

-- (15): the second prejacent's context lies in the counterfactual first, so the speaker commits
-- to nothing about `S`
theorem mem_dom_thereIsnt_comp_not_it :
    i ∈ (thereIsnt R φDC ○ ((it S υ).not φ₄).dec φDC φ₃).dom ↔
      i.prop φDC ⊆ (witnessed R)ᶜ := by
  simp only [mem_dom_comp, mem_thereIsnt (by decide : φDC ≠ φ₁),
    (hasTruthSet_it.not (by decide : φ₃ ≠ φ₄)).mem_dom_dec (by decide : φDC ≠ φ₃)]
  refine ⟨fun ⟨_, ⟨h, _⟩, _⟩ ↦ h, fun h ↦ ?_⟩
  obtain ⟨e, he, -⟩ := exists_isWitness_sat_eq R S
  exact ⟨_, ⟨h, e, he, rfl⟩, by
    simp (decide := true)
    exact fun w hw hs ↦ h hw (he.sat_subset hs).1⟩

/-! ### Veridical and counterfactual drefs (16), (36), (37), (39) -/

-- (36a): the dref of an affirmative assertion is veridical
theorem subset_dom_of_mem_thereIs (h : i ~[thereIs R] j) : j.prop φDC ⊆ (j.indiv υ).Dom := by
  obtain ⟨hC, e, he, rfl⟩ := mem_thereIs.mp h
  simpa (decide := true) [← he.1] using hC

-- (37a), §3.4.1: the dref of a negated assertion is counterfactual
theorem disjoint_dom_of_mem_thereIsnt (h : i ~[thereIsnt R φDC] j) :
    Disjoint (j.prop φDC) (j.indiv υ).Dom := by
  obtain ⟨hC, e, he, rfl⟩ := (mem_thereIsnt (by decide)).mp h
  simpa (decide := true) [← he.1, Set.disjoint_left] using fun _ hw hw' ↦ hC hw hw'

-- §4.1: the dref of a doubly negated assertion is veridical
theorem subset_dom_of_mem_notThereIsnt (h : i ~[notThereIsnt R] j) :
    j.prop φDC ⊆ (j.indiv υ).Dom := by
  obtain ⟨hC, e, he, rfl⟩ := mem_notThereIsnt.mp h
  simpa (decide := true) [← he.1] using hC

-- (38), (39): a pronoun's referent is entailed in its local context, which lies in its antecedent's
theorem subset_of_mem_itIs {k : State W E} (hφ : φ' ≠ φ) (hk : k.prop φ' = (k.indiv υ).Dom)
    (h : k ~[itIs S r φ] j) : j ∈ localEntailment φ υ ∧ j.prop φ ⊆ j.prop φ' := by
  obtain ⟨s, -, hj⟩ := mem_box_singleton_comp.mp h
  obtain ⟨-, hj⟩ := hasTruthSet_it.mem_max.mp hj
  obtain ⟨rfl, hp⟩ := mem_it.mp hj
  have hl := mem_localEntailment_of_mem_predication (R := S) hp
  exact ⟨hl, (mem_localEntailment_iff (by simpa [State.updateProp_prop_of_ne _ hφ] using hk)).mp hl⟩

/-! ### Connectives over a pronoun (44), (45), (61) -/

section Connective

variable {f : Set W → Set W → Set W} {A : Set W} {g : State W E → State W E}

theorem mem_connective
    (hP : ∀ i j : State W E, i ~[maxInput φ₂ (P φ₂)] j ↔ i.prop φ₂ = A ∧
      ∃ e, IsWitness R (witnessed R) e ∧ j = (g i).updateIndiv υ e)
    (hg : ∀ i : State W E, (g i).prop φ₃ = i.prop φ₃) :
    i ~[Clause.connective f P (it S υ) φ₂ φ₃ φ₁] j ↔ ∃ e, IsWitness R (witnessed R) e ∧
      i.prop φ₁ = f A (sat S e) ∧
      j = (g ((i.updateProp φ₂ A).updateProp φ₃ (sat S e))).updateIndiv υ e := by
  rw [Clause.connective, comp_assoc, mem_box_pair_comp]
  constructor
  · rintro ⟨s, t, hC, k, hk, hj⟩
    obtain ⟨hs, e, he, rfl⟩ := (hP _ _).mp hk
    obtain ⟨ht, hj⟩ := hasTruthSet_it.mem_max.mp hj
    obtain ⟨rfl, -⟩ := mem_it.mp hj
    simp (decide := true) only [hg, State.updateIndiv_prop, State.updateIndiv_indiv_self,
      State.updateProp_prop_self, State.updateProp_prop_of_ne, Set.mem_ofPred_eq] at hs ht hC
    subst hs ht
    exact ⟨e, he, by simpa (decide := true) using hC, rfl⟩
  · rintro ⟨e, he, hC, rfl⟩
    have hA : ((i.updateProp φ₂ A).updateProp φ₃ (sat S e)).prop φ₂ = A := by
      simp (decide := true)
    exact ⟨_, _, by simpa (decide := true) using hC, _, (hP _ _).mpr ⟨hA, e, he, rfl⟩,
      hasTruthSet_it.mem_max.mpr ⟨by simp [hg], mem_it.mpr ⟨rfl, by simp [hg]⟩⟩⟩

theorem hasTruthSet_connective
    (hP : ∀ i j : State W E, i ~[maxInput φ₂ (P φ₂)] j ↔ i.prop φ₂ = A ∧
      ∃ e, IsWitness R (witnessed R) e ∧ j = (g i).updateIndiv υ e)
    (hg : ∀ i : State W E, (g i).prop φ₃ = i.prop φ₃) (hf : Monotone (f A)) :
    (Clause.connective f P (it S υ) φ₂ φ₃).HasTruthSet φ₁ fun _ ↦ f A (witnessed (R ⊓ S)) := by
  refine fun i ↦ ⟨?_, ?_⟩
  · obtain ⟨e, he, h⟩ := exists_isWitness_sat_eq R S
    exact ⟨_, (mem_connective hP hg).mpr ⟨e, he, by simp [h], rfl⟩⟩
  · rintro s ⟨_, hs⟩
    obtain ⟨e, he, hC, -⟩ := (mem_connective hP hg).mp hs
    simp only [State.updateProp_prop_self] at hC
    exact hC ▸ hf (he.sat_subset.trans Set.inter_subset_right)

end Connective

theorem mem_max_existential :
    i ~[maxInput φ₂ (existential R υ φ₂)] j ↔ i.prop φ₂ = witnessed R ∧
      ∃ e, IsWitness R (witnessed R) e ∧ j = i.updateIndiv υ e := by
  rw [hasTruthSet_existential.mem_max, mem_existential, and_congr_right_iff]
  exact fun h ↦ by rw [h]

theorem mem_max_not_existential :
    i ~[maxInput φ₂ ((existential R υ).not φ₄ φ₂)] j ↔ i.prop φ₂ = (witnessed R)ᶜ ∧
      ∃ e, IsWitness R (witnessed R) e ∧
        j = (i.updateProp φ₄ (witnessed R)).updateIndiv υ e := by
  rw [(hasTruthSet_existential.not (by decide : φ₂ ≠ φ₄)).mem_max,
    hasTruthSet_existential.mem_not (by decide : φ₂ ≠ φ₄), mem_existential]
  simp

/-- The bathroom disjunction has the weak reading of §4.5: it is true where there is no `R` or
some `R` is an `S`. -/
theorem mem_dom_thereIsntOr :
    i ∈ (thereIsntOr R S).dom ↔ i.prop φDC ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  (hasTruthSet_connective (f := (· ∪ ·)) (fun _ _ ↦ mem_max_not_existential)
    (fun _ ↦ by simp (decide := true))
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec (by decide : φDC ≠ φ₁)

-- (61): the conditional and the bathroom disjunction agree, with no stipulated equivalence
theorem mem_dom_ifThen :
    i ∈ (((existential R υ).ifThen (it S υ) φ₂ φ₃).dec φDC φ₁).dom ↔
      i.prop φDC ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  (hasTruthSet_connective (f := fun s t ↦ sᶜ ∪ t) (fun _ _ ↦ mem_max_existential)
    (fun _ ↦ rfl)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec (by decide : φDC ≠ φ₁)

-- (45): the semantics admits it
theorem mem_dom_or_existential_it :
    i ∈ (((existential R υ).or (it S υ) φ₂ φ₃).dec φDC φ₁).dom ↔ i.prop φDC ⊆ witnessed R := by
  rw [(hasTruthSet_connective (f := (· ∪ ·)) (fun _ _ ↦ mem_max_existential) (fun _ ↦ rfl)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec (by decide : φDC ≠ φ₁),
    Set.union_eq_left.mpr witnessed_inf_subset_left]

-- (45): the second disjunct's context lies in the first's
theorem subset_of_mem_or_existential_it
    (h : i ~[((existential R υ).or (it S υ) φ₂ φ₃).dec φDC φ₁] j) : j.prop φ₃ ⊆ j.prop φ₂ := by
  obtain ⟨-, h⟩ := (hasTruthSet_connective (f := (· ∪ ·)) (fun _ _ ↦ mem_max_existential)
    (fun _ ↦ rfl)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dec (by decide : φDC ≠ φ₁) |>.mp h
  obtain ⟨e, he, -, rfl⟩ := (mem_connective (fun _ _ ↦ mem_max_existential) (fun _ ↦ rfl)).mp h
  simpa (decide := true) using he.sat_subset.trans Set.inter_subset_left

/-! ### Attitudes (52) -/

variable {a : E} {dox : E → W → Set W}

/-- *`a` believes it is `S`* (52). -/
abbrev believes (a : E) (dox : E → W → Set W) (S : E → W → Prop) : Clause W E :=
  properName a υ₂ (Clause.believed dox (it S υ) φ₄)

theorem mem_believes (hφ : φ ≠ φ₄) :
    i ~[believes a dox S φ] j ↔ i.prop φ ⊆ {w | dox a w ⊆ sat S (i.indiv υ)} ∧
      j = (i.updateIndiv υ₂ fun _ ↦ Part.some a).updateProp φ₄ (sat S (i.indiv υ)) := by
  have hυ : ((i.updateIndiv υ₂ fun _ ↦ Part.some a).indiv υ) = i.indiv υ :=
    State.updateIndiv_indiv_of_ne _ (by decide) _
  rw [believes, properName, mem_box_singleton_comp]
  simp [Clause.believed, hasTruthSet_it.mem_box_comp_max, mem_it, Clause.believe,
    State.updateProp_prop_of_ne _ hφ, hυ, eq_comm]

theorem hasTruthSet_believes :
    (believes a dox S).HasTruthSet φ₃ fun g ↦ {w | dox a w ⊆ sat S (g υ)} :=
  .of_mem_dom_iff fun _ ↦ ⟨fun ⟨_, hj⟩ ↦ ((mem_believes (by decide)).mp hj).1,
    fun h ↦ ⟨_, (mem_believes (by decide)).mpr ⟨h, rfl⟩⟩⟩

theorem mem_dec_believes (hr : r ≠ φ₃) :
    i ~[(believes a dox S).dec r φ₃] j ↔ i.prop r ⊆ {w | dox a w ⊆ sat S (i.indiv υ)} ∧
      j = ((i.updateProp φ₃ {w | dox a w ⊆ sat S (i.indiv υ)}).updateIndiv υ₂
        fun _ ↦ Part.some a).updateProp φ₄ (sat S (i.indiv υ)) := by
  rw [hasTruthSet_believes.mem_dec hr, mem_believes (by decide)]
  simp

theorem mem_dom_thereIsnt_comp_believes :
    i ∈ (thereIsnt R φDC ○ (believes a dox S).dec φDC φ₃).dom ↔
      i.prop φDC ⊆ (witnessed R)ᶜ ∧
        ∃ e, IsWitness R (witnessed R) e ∧ i.prop φDC ⊆ {w | dox a w ⊆ sat S e} := by
  simp only [mem_dom_comp, mem_thereIsnt (by decide : φDC ≠ φ₁),
    hasTruthSet_believes.mem_dom_dec (by decide : φDC ≠ φ₃)]
  simp (decide := true) [and_assoc]

/-- A hypothetical anaphor can have a counterfactual antecedent (§4.4), since the attitude does not
make the speaker's commitments entail the anaphor's context: that context lies in the antecedent's,
and outside the commitments. -/
theorem disjoint_of_mem_thereIsnt_comp_believes
    (h : i ~[thereIsnt R φDC ○ (believes a dox S).dec φDC φ₃] j) :
    j.prop φ₄ ⊆ j.prop φ₂ ∧ Disjoint (j.prop φDC) (j.prop φ₄) := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := (mem_thereIsnt (by decide)).mp hk
  obtain ⟨-, rfl⟩ := (mem_dec_believes (by decide)).mp hj
  simp (decide := true) only [State.updateProp_prop_self, State.updateProp_prop_of_ne,
    State.updateIndiv_prop, State.updateIndiv_indiv_self]
  have hsub : sat S e ⊆ witnessed R := he.sat_subset.trans Set.inter_subset_left
  exact ⟨hsub, Set.disjoint_left.mpr fun w hw hs ↦ hdc hw (hsub hs)⟩

-- (13b): a veridical attitude requires the referent where the speaker commits, which a
-- counterfactual antecedent excludes
theorem eq_empty_of_mem_thereIsnt_comp_knows
    (h : i ~[thereIsnt R φDC ○ (properName a υ₂ (Clause.knows dox (it S υ) φ₄)).dec φDC φ₃] j) :
    i.prop φDC = ∅ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := (mem_thereIsnt (by decide)).mp hk
  obtain ⟨s, hs, hj⟩ := mem_box_singleton_comp.mp hj
  obtain ⟨c, -, hj⟩ := mem_box_singleton_comp.mp (Update.mem_maxInput.mp hj).2
  obtain ⟨t, ⟨-, hst⟩, hj⟩ := mem_box_singleton_comp.mp hj
  obtain ⟨ht, -⟩ := hasTruthSet_it.mem_max.mp hj
  simp (decide := true) only [extend_pvar, extend_ivar, incl, Set.mem_ofPred_eq,
    State.updateProp_prop_of_ne, State.updateProp_prop_self, State.updateProp_indiv,
    State.updateIndiv_prop, State.updateIndiv_indiv_self,
    State.updateIndiv_indiv_of_ne] at hs hst ht
  subst ht
  exact Set.eq_empty_of_subset_empty fun w hw ↦ hdc hw (he.sat_subset (hst (hs hw))).1

/-! ### The relative update and the local context (§§2.1, 3.2.1) -/

-- (16), (18a), (25): the negated scope needs the referent exactly outside where it exists
theorem eq_univ_of_mem_indefinite_not_it (hφ : φ ≠ φ')
    (h : i ~[indefinite v (commonNoun R) (fun u ↦ (it S u).not φ') φ] j) :
    i.prop φ = Set.univ ∧ witnessed R = Set.univ := by
  obtain ⟨_, ⟨k, hk, rfl, hR⟩, hj⟩ := h
  obtain ⟨⟨e, rfl⟩, hdom⟩ := mem_relUpdate.mp hk
  obtain ⟨s, hs, hj⟩ := mem_box_singleton_comp.mp hj
  obtain ⟨-, hsat⟩ := mem_it.mp (maxInput_subset _ _ hj)
  simp only [extend_ivar, State.updateIndiv_prop, State.updateIndiv_indiv_self] at hdom
  simp only [extend_pvar, extend_ivar, mem_eqCompl, State.updateProp_prop_of_ne _ hφ,
    State.updateProp_prop_self, State.updateIndiv_prop] at hs
  simp only [extend_pvar, extend_ivar, State.updateProp_prop_self, State.updateProp_indiv,
    State.updateIndiv_indiv_self] at hsat
  have hempty : s = ∅ := Set.eq_empty_of_forall_notMem fun w hw ↦ by
    have hd : w ∈ e.Dom := sat_subset_dom S e (hsat hw)
    rw [← hdom, hs] at hd
    exact hd hw
  have huniv : i.prop φ = Set.univ := by rw [hs, hempty, Set.compl_empty]
  refine ⟨huniv, Set.eq_univ_of_forall fun w ↦ ?_⟩
  obtain ⟨a, -, hRa⟩ := hR (by simp [huniv] : w ∈ (i.updateIndiv v e).prop φ)
  exact ⟨a, hRa⟩

/-- Stone's relative variable update has only the implication from the context to a referent. -/
def stoneExistential (R : E → W → Prop) (v : IVar) : Clause W E :=
  fun φ ↦ box {v} {j | j.prop φ ⊆ (j.indiv v).Dom} ○ test (predication R φ v)

theorem mem_stoneExistential :
    i ~[stoneExistential R v φ] j ↔ ∃ e, i.prop φ ⊆ sat R e ∧ j = i.updateIndiv v e := by
  constructor
  · rintro ⟨k, hk, rfl, hp⟩
    obtain ⟨⟨e, rfl⟩, -⟩ := Update.mem_box_singleton.mp hk
    exact ⟨e, by simpa using hp, rfl⟩
  · rintro ⟨e, hs, rfl⟩
    exact ⟨_, Update.mem_box_singleton.mpr ⟨⟨e, rfl⟩,
      by simpa using hs.trans (sat_subset_dom R e)⟩, rfl, by simpa using hs⟩

theorem hasTruthSet_stoneExistential :
    (stoneExistential R v).HasTruthSet φ fun _ ↦ witnessed R :=
  .of_mem_dom_iff fun i ↦ by
    refine ⟨fun ⟨j, hj⟩ w hw ↦ ?_, fun hs ↦ ?_⟩
    · obtain ⟨e, he, -⟩ := mem_stoneExistential.mp hj
      obtain ⟨a, -, hR⟩ := he hw
      exact ⟨a, hR⟩
    · obtain ⟨e, he, -⟩ := exists_isWitness_sat hs ⊤
      exact ⟨_, mem_stoneExistential.mpr ⟨e, he.2, rfl⟩⟩

-- (14), (15): a local context under Heim's negation lies in the global context, so none is
-- available to a pronoun whose referent exists only in the negated worlds
theorem eq_empty_of_subset_ccp_neg {X : Type*} {f g : CCP X} {c : Set X} (hg : g.IsEliminative)
    (h : g (CCP.neg f c) ⊆ f c) : g (CCP.neg f c) = ∅ :=
  Set.eq_empty_of_subset_empty fun _ hw ↦ (hg _ hw).2 (h hw)

/-! ### Acceptability (§3.3.1) -/

/-- An update is acceptable if it succeeds at some initial state (33), which introduces the
commitment sets `dcs` to the null assignment (32), and they are nonempty (31). -/
def Acceptable (dcs : Finset PVar) (D : Update (State W E)) : Prop :=
  ∃ i, State.null ~[box dcs Set.univ] i ∧ (∀ x ∈ dcs, (i.prop x).Nonempty) ∧ ∃ j, i ~[D] j

/-- An initial state of a single speaker whose commitment set is `dc`. -/
def init (dc : Set W) : State W E := State.null.updateProp φDC dc

@[simp] theorem init_prop (dc : Set W) : (init dc : State W E).prop φDC = dc := by
  simp [init]

theorem acceptable_iff_nonempty {T : Set W}
    (hT : ∀ i : State W E, i ∈ (D).dom ↔ i.prop φDC ⊆ T) :
    Acceptable {φDC} D ↔ T.Nonempty := by
  constructor
  · rintro ⟨i, -, hne, hj⟩
    exact (hne φDC (Finset.mem_singleton_self _)).mono ((hT i).mp hj)
  · intro hne
    exact ⟨init T, Update.mem_box_singleton.mpr ⟨⟨T, rfl⟩, trivial⟩, by simpa using hne,
      (hT _).mpr (by simp)⟩

-- (42c): the commitment sets of the interlocutors are independent
theorem acceptable_disagree :
    Acceptable {φDCA, φDCB} (thereIsnt R φDCA ○ itIs S φDCB φ₃) ↔
      ((witnessed R)ᶜ).Nonempty ∧ (witnessed (R ⊓ S)).Nonempty := by
  constructor
  · rintro ⟨i, -, hne, hj⟩
    obtain ⟨hA, hB⟩ := mem_dom_disagree.mp hj
    exact ⟨(hne φDCA (by simp)).mono hA, (hne φDCB (by simp)).mono hB⟩
  · rintro ⟨hX, hY⟩
    refine ⟨(State.null.updateProp φDCA (witnessed R)ᶜ).updateProp φDCB (witnessed (R ⊓ S)),
      Update.mem_box_insert_of_mem ⟨_, rfl⟩ (Update.mem_box_singleton.mpr ⟨⟨_, rfl⟩, trivial⟩),
      ?_, mem_dom_disagree.mpr (by simp (decide := true))⟩
    simpa (decide := true) using ⟨hX, hY⟩

/-! ### The models -/

section Models

variable {b : E} {s t : Set W} {e : W →. E}

/-- A relation that holds of the one individual `b`, at the worlds of `s`, as the predicates of the
paper's models do. -/
def atom (b : E) (s : Set W) : E → W → Prop := fun a w ↦ a = b ∧ w ∈ s

/-- The individual concept that refers to `b` at the worlds of `s`. -/
def refer (b : E) (s : Set W) : W →. E := PFun.res (fun _ ↦ b) s

theorem witnessed_atom : witnessed (atom b s) = s := by
  ext w
  simp [witnessed, atom]

theorem isWitness_refer (hs : s ⊆ t) : IsWitness (atom b t) s (refer b s) :=
  ⟨by ext; simp [refer, PFun.res], fun w hw ↦ ⟨b, by simp [refer, hw, PFun.mem_res], rfl, hs hw⟩⟩

theorem isWitness_atom_iff : IsWitness (atom b s) (witnessed (atom b s)) e ↔ e = refer b s := by
  rw [witnessed_atom]
  refine ⟨fun ⟨hd, hs⟩ ↦ funext fun w ↦ Part.ext fun a ↦ ?_, fun h ↦ h ▸ isWitness_refer subset_rfl⟩
  rw [refer, PFun.mem_res]
  constructor
  · intro ha
    have hw : w ∈ s := hd ▸ Part.dom_iff_mem.2 ⟨a, ha⟩
    obtain ⟨c, hc, rfl, -⟩ := hs hw
    exact ⟨hw, (Part.mem_unique ha hc).symm⟩
  · rintro ⟨hw, rfl⟩
    obtain ⟨c, hc, rfl, -⟩ := hs hw
    exact hc

theorem sat_refer_atom : sat (atom b t) (refer b s) = s ∩ t := by
  ext w
  simp only [sat, refer, PFun.mem_res, atom, Set.mem_ofPred_eq, Set.mem_inter_iff]
  aesop

theorem witnessed_atom_inf_atom : witnessed (atom b s ⊓ atom b t) = s ∩ t := by
  ext w
  simp [witnessed, atom]

-- (35): selecting the greatest commitment set at which an update succeeds is `maxInput φDC`
theorem mem_max_init {T : Set W} {f : Set W → State W E} {dc : Set W} {j : State W E}
    (h : ∀ dc j, (init dc : State W E) ~[D] j ↔ dc ⊆ T ∧ j = f dc) :
    (init dc : State W E) ~[maxInput φDC D] j ↔ dc = T ∧ j = f T := by
  have hinit (s : Set W) : (init dc : State W E).updateProp φDC s = init s := by simp [init]
  refine (Update.mem_maxInput_of_isGreatest (T := T) ⟨⟨f T, ?_⟩, ?_⟩).trans ?_
  · rw [extend_pvar, hinit]; exact (h T (f T)).mpr ⟨subset_rfl, rfl⟩
  · rintro s ⟨k, hk⟩
    rw [extend_pvar, hinit] at hk
    exact ((h s k).mp hk).1
  · rw [val_pvar, init_prop, h]
    constructor
    · rintro ⟨rfl, -, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, subset_rfl, rfl⟩

end Models

/-! ### The model M₁ (§3.3.2) -/

/-- The entities of the models that enter a relation: the bathroom and Sue. -/
inductive Ent where
  | b | sue

/-- The four worlds have a bathroom that is upstairs, a bathroom that is not, no bathroom and
something upstairs, and neither. -/
inductive World where
  | wbu | wb | wu | w0

/-- `b` is a bathroom in the two bathroom worlds. -/
abbrev bathroom : Ent → World → Prop := atom .b {.wbu, .wb}

/-- `b` is upstairs in the two upstairs worlds. -/
abbrev upstairs : Ent → World → Prop := atom .b {.wbu, .wu}

/-- The individual dref of the bathroom, defined exactly in the bathroom worlds. -/
abbrev bathroomRef : World →. Ent := refer .b {.wbu, .wb}

theorem compl_bathroom_worlds : ({.wbu, .wb} : Set World)ᶜ = {.wu, .w0} := by
  ext w
  cases w <;> simp

theorem bathroom_worlds_inter : ({.wbu, .wb} ∩ {.wbu, .wu} : Set World) = {.wbu} := by
  ext w
  cases w <;> simp

section M₁

variable {dc : Set World} {j : State World Ent}

/-- The output of Figure 5, at the commitment set `dc`. -/
def j₅ (dc : Set World) : State World Ent :=
  ((init dc).updateProp φ₁ {.wbu, .wb}).updateIndiv υ bathroomRef

/-- The output of Figure 6, at the commitment set `dc`. -/
def j₆ (dc : Set World) : State World Ent := (j₅ dc).updateProp φ₃ {.wbu}

-- Table 1: assertion eliminates the commitment sets that are not subsets of the bathroom worlds
theorem mem_thereIs_bathroom :
    init dc ~[thereIs bathroom] j ↔ dc ⊆ {.wbu, .wb} ∧ j = j₅ dc := by
  simp only [mem_thereIs, isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, init_prop, j₅]

-- Figure 5
theorem figure5 :
    init dc ~[maxInput φDC (thereIs bathroom)] j ↔ dc = {.wbu, .wb} ∧ j = j₅ {.wbu, .wb} :=
  mem_max_init fun _ _ ↦ mem_thereIs_bathroom

-- Table 2: the pronoun narrows the commitment sets further
theorem mem_thereIs_comp_itIs_bathroom :
    init dc ~[thereIs bathroom ○ itIs upstairs φDC φ₃] j ↔ dc ⊆ {.wbu} ∧ j = j₆ dc := by
  have hk : (j₅ dc).prop φDC = dc := by simp (decide := true) [j₅]
  have hv : (j₅ dc).indiv υ = bathroomRef := by simp [j₅]
  have hs : sat upstairs bathroomRef = {.wbu} := by rw [sat_refer_atom, bathroom_worlds_inter]
  have hit : j₅ dc ~[itIs upstairs φDC φ₃] j ↔ dc ⊆ {.wbu} ∧ j = j₆ dc := by
    rw [mem_dec_it (by decide), hk, hv, hs, j₆]
  constructor
  · rintro ⟨k, hk', hj⟩
    obtain ⟨-, rfl⟩ := mem_thereIs_bathroom.mp hk'
    exact hit.mp hj
  · intro h
    exact ⟨j₅ dc, mem_thereIs_bathroom.mpr ⟨h.1.trans (by simp), rfl⟩, hit.mpr h⟩

-- Figure 6: pragmatic maximization is defeasible, since it applies to the whole discourse
theorem figure6 :
    init dc ~[maxInput φDC (thereIs bathroom ○ itIs upstairs φDC φ₃)] j ↔
      dc = {.wbu} ∧ j = j₆ {.wbu} :=
  mem_max_init fun _ _ ↦ mem_thereIs_comp_itIs_bathroom

/-- The output of Figure 7, the first row of Table 3, at the commitment set `dc`. -/
def j₇ (dc : Set World) : State World Ent :=
  (((init dc).updateProp φ₁ {.wu, .w0}).updateProp φ₂ {.wbu, .wb}).updateIndiv υ bathroomRef

-- (41), Figure 7: the prejacent's context is all and only the bathroom worlds, the first row of
-- Table 3
theorem mem_thereIsnt_bathroom :
    init dc ~[thereIsnt bathroom φDC] j ↔ dc ⊆ {.wu, .w0} ∧ j = j₇ dc := by
  simp only [mem_thereIsnt (by decide : φDC ≠ φ₁), isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, compl_bathroom_worlds, init_prop, j₇]

/-- (41) as printed, with the maximization (40) of App. B (10b). -/
def printed41 : Update (State World Ent) :=
  box {φ₁} (incl φDC φ₁) ○ maxAt φ₁ (box {φ₂} (eqCompl φ₁ φ₂) ○
    maxAt φ₂ (existential bathroom υ φ₂))

/-- (30) with the maximization of App. C (19), as (48) prints it for `B`. -/
def printedIt : Update (State World Ent) :=
  box {φ₃} (incl φDC φ₃) ○ maxAt φ₃ (it upstairs υ φ₃)

theorem printed41_eq : printed41 =
    box {φ₁} (incl φDC φ₁) ○ (box {φ₂} (eqCompl φ₁ φ₂) ○ existential bathroom υ φ₂) := by
  rw [printed41, Update.maxAt_eq_of_fixes (fixes_existential _), Update.maxAt_eq_of_fixes
    ((Update.fixes_box (by simp (decide := true)) _).comp (fixes_existential _))]

/-- A row of Table 3, with `s` the value of `φ₂`. -/
def table3 (s : Set World) : State World Ent :=
  (((init sᶜ).updateProp φ₁ sᶜ).updateProp φ₂ s).updateIndiv υ (refer .b s)

-- Table 3: every row is an output of (41) as printed; `mem_thereIsnt_bathroom` keeps only the first
theorem mem_printed41 {s : Set World} (hs : s ⊆ {.wbu, .wb}) : init sᶜ ~[printed41] table3 s := by
  rw [printed41_eq, mem_box_singleton_comp]
  refine ⟨sᶜ, by simp (decide := true) [incl, init], mem_box_singleton_comp.mpr
    ⟨s, by simp (decide := true) [eqCompl], mem_existential.mpr ⟨_, ?_, rfl⟩⟩⟩
  simpa using isWitness_refer hs

theorem thereIsnt_subset_printed41 : thereIsnt bathroom φDC ⊆ printed41 := by
  rw [printed41_eq]
  exact comp_subset_comp_right ((maxInput_subset _ _).trans
    (comp_subset_comp_right (maxInput_subset _ _)))

-- §3.4.2: local entailment and consistency exclude (26) under (40) as printed
theorem eq_empty_of_mem_printed41_comp_printedIt {i : State World Ent}
    (h : i ~[printed41 ○ printedIt] j) : j.prop φDC = ∅ := by
  have h₃ : maxAt φ₃ (it upstairs υ φ₃) = it upstairs υ φ₃ :=
    Update.maxAt_eq_of_fixes (Update.fixes_test _ _)
  rw [printed41_eq, printedIt, h₃] at h
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨s, hs, hk⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨t, ht, hk⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨e, he, rfl⟩ := mem_existential.mp hk
  obtain ⟨u, hu, hj⟩ := mem_box_singleton_comp.mp hj
  obtain ⟨rfl, hsat⟩ := mem_it.mp hj
  simp (decide := true) only [extend_pvar, mem_incl, mem_eqCompl, State.updateProp_prop_of_ne,
    State.updateProp_prop_self, State.updateProp_indiv, State.updateIndiv_prop,
    State.updateIndiv_indiv_self] at hs ht hu hsat he ⊢
  refine Set.eq_empty_of_subset_empty fun w hw ↦ ?_
  have hc := ht ▸ hs hw
  exact hc (he.1 ▸ sat_subset_dom _ _ (hsat (hu hw)))

-- (35): pragmatic maximization as printed leaves an assertion unchanged
example : maxAt φDC (thereIs bathroom) = thereIs bathroom :=
  Update.maxAt_eq_of_fixes (Clause.fixes_dec (by decide) (fixes_existential _))

/-- The output of Figure 8, at the commitment set `dc`. -/
def j₈ (dc : Set World) : State World Ent :=
  ((((init dc).updateProp φ₁ {.wbu, .wb}).updateProp φ₂ {.wu, .w0}).updateProp φ₃
    {.wbu, .wb}).updateIndiv υ bathroomRef

-- Figure 8
theorem mem_notThereIsnt_bathroom :
    init dc ~[notThereIsnt bathroom] j ↔ dc ⊆ {.wbu, .wb} ∧ j = j₈ dc := by
  simp only [mem_notThereIsnt, isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, compl_bathroom_worlds, init_prop, j₈]

/-- The output of Figure 9, at the commitment set `dc`. -/
def j₉ (dc : Set World) : State World Ent :=
  (((((init dc).updateProp φ₁ {.wbu, .wu, .w0}).updateProp φ₂ {.wu, .w0}).updateProp φ₃
    {.wbu}).updateProp φ₄ {.wbu, .wb}).updateIndiv υ bathroomRef

-- Figure 9
theorem mem_thereIsntOr_bathroom :
    init dc ~[thereIsntOr bathroom upstairs] j ↔ dc ⊆ {.wbu, .wu, .w0} ∧ j = j₉ dc := by
  have hT : ({.wu, .w0} ∪ {.wbu} : Set World) = {.wbu, .wu, .w0} := by
    ext w
    cases w <;> simp
  have hg : ∀ i : State World Ent,
      (i.updateProp φ₄ (witnessed bathroom)).prop φ₃ = i.prop φ₃ := fun _ ↦ by simp (decide := true)
  rw [(hasTruthSet_connective (S := upstairs) (f := (· ∪ ·))
    (fun _ _ ↦ mem_max_not_existential) hg
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dec (by decide : φDC ≠ φ₁),
    mem_connective (fun _ _ ↦ mem_max_not_existential) hg]
  simp only [isWitness_atom_iff, exists_eq_left]
  simp only [init_prop, sat_refer_atom, witnessed_atom, compl_bathroom_worlds,
    witnessed_atom_inf_atom, bathroom_worlds_inter, hT, State.updateProp_prop_self, true_and, j₉]

-- Figure 9: the dref of the bathroom disjunction is hypothetical without being counterfactual
theorem hypothetical_j₉ :
    ¬ (j₉ {.wbu, .wu, .w0}).prop φDC ⊆ ((j₉ {.wbu, .wu, .w0}).indiv υ).Dom ∧
      ¬ Disjoint ((j₉ {.wbu, .wu, .w0}).prop φDC) ((j₉ {.wbu, .wu, .w0}).indiv υ).Dom := by
  have hDC : (j₉ {.wbu, .wu, .w0}).prop φDC = {.wbu, .wu, .w0} := by simp (decide := true) [j₉]
  have hv : (j₉ {.wbu, .wu, .w0}).indiv υ = bathroomRef := by simp [j₉]
  rw [hDC, hv]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [refer, PFun.res] using h (by simp : World.wu ∈ _)
  · exact Set.disjoint_left.mp h (by simp : World.wbu ∈ _) (by simp [refer, PFun.res])

-- (42b): the disjuncts' contexts do not overlap, an exclusive reading of the disjunction
theorem disjoint_of_mem_thereIsntOr_bathroom (h : init dc ~[thereIsntOr bathroom upstairs] j) :
    Disjoint (j.prop φ₂) (j.prop φ₃) := by
  obtain ⟨-, rfl⟩ := mem_thereIsntOr_bathroom.mp h
  simp (decide := true) [j₉]

/-- An initial state of the two interlocutors of §4.3. -/
def init₂ (dcA dcB : Set World) : State World Ent :=
  (State.null.updateProp φDCA dcA).updateProp φDCB dcB

/-- The output of Figure 10, at the commitment sets `dcA` and `dcB`. -/
def j₁₀ (dcA dcB : Set World) : State World Ent :=
  ((((init₂ dcA dcB).updateProp φ₁ {.wu, .w0}).updateProp φ₂ {.wbu, .wb}).updateIndiv υ
    bathroomRef).updateProp φ₃ {.wbu}

-- Figure 10: each interlocutor's commitments stay consistent, though they cannot overlap
theorem mem_disagree_bathroom {dcA dcB : Set World} :
    init₂ dcA dcB ~[thereIsnt bathroom φDCA ○ itIs upstairs φDCB φ₃] j ↔
      dcA ⊆ {.wu, .w0} ∧ dcB ⊆ {.wbu} ∧ j = j₁₀ dcA dcB := by
  have hA : (init₂ dcA dcB : State World Ent).prop φDCA = dcA := by simp (decide := true) [init₂]
  have hB : (init₂ dcA dcB : State World Ent).prop φDCB = dcB := by simp [init₂]
  have hs : sat upstairs bathroomRef = {.wbu} := by rw [sat_refer_atom, bathroom_worlds_inter]
  have hk {k : State World Ent} : (init₂ dcA dcB ~[thereIsnt bathroom φDCA] k) ↔
      dcA ⊆ {.wu, .w0} ∧ k = (((init₂ dcA dcB).updateProp φ₁ {.wu, .w0}).updateProp φ₂
        {.wbu, .wb}).updateIndiv υ bathroomRef := by
    simp only [mem_thereIsnt (by decide : φDCA ≠ φ₁), isWitness_atom_iff, exists_eq_left]
    simp only [witnessed_atom, compl_bathroom_worlds, hA]
  have hit {k : State World Ent} (hd : k.prop φDCB = dcB) (hv : k.indiv υ = bathroomRef) :
      k ~[itIs upstairs φDCB φ₃] j ↔ dcB ⊆ {.wbu} ∧ j = k.updateProp φ₃ {.wbu} := by
    rw [mem_dec_it (by decide), hd, hv, hs]
  have hk₂ : ((((init₂ dcA dcB).updateProp φ₁ {.wu, .w0}).updateProp φ₂ {.wbu, .wb}).updateIndiv υ
      bathroomRef).prop φDCB = dcB := by
    simpa (decide := true) using hB
  constructor
  · rintro ⟨k, hk', hj⟩
    obtain ⟨hdc, rfl⟩ := hk.mp hk'
    exact ⟨hdc, (hit hk₂ (by simp)).mp hj⟩
  · rintro ⟨hdc, hb, rfl⟩
    exact ⟨_, hk.mpr ⟨hdc, rfl⟩, (hit hk₂ (by simp)).mpr ⟨hb, rfl⟩⟩

-- an indefinite outscoping negation has no output on the model
theorem not_mem_indefinite_not_it {i j : State World Ent} :
    ¬ i ~[indefinite υ (commonNoun bathroom) (fun u ↦ (it upstairs u).not φ₂) φ₁] j := fun h ↦ by
  have := (eq_univ_of_mem_indefinite_not_it (by decide) h).2
  rw [witnessed_atom] at this
  simpa using this.ge (Set.mem_univ World.wu)

-- §3.2.1: under [stone-1999]'s update (26) is consistent, so the biconditional of (25) is crucial
theorem stone_admits_26 :
    ∃ j, init {.wu} ~[((stoneExistential bathroom υ).not φ₂).dec φDC φ₁ ○
      itIs upstairs φDC φ₃] j := by
  have hT := hasTruthSet_stoneExistential (R := bathroom) (v := υ) (φ := φ₂)
  let e : World →. Ent := fun _ ↦ Part.some .b
  let k : State World Ent :=
    (((init {.wu}).updateProp φ₁ (witnessed bathroom)ᶜ).updateProp φ₂
      (witnessed bathroom)).updateIndiv υ e
  have hk : init {.wu} ~[((stoneExistential bathroom υ).not φ₂).dec φDC φ₁] k := by
    refine (hT.not (by decide : φ₁ ≠ φ₂)).mem_dec (by decide : φDC ≠ φ₁) |>.mpr ⟨?_, ?_⟩
    · simp [witnessed_atom, compl_bathroom_worlds]
    · refine (hT.mem_not (by decide : φ₁ ≠ φ₂)).mpr ⟨by simp, mem_stoneExistential.mpr ⟨e, ?_, rfl⟩⟩
      intro w hw
      exact ⟨.b, by simp [e], rfl, by simpa [witnessed_atom] using hw⟩
  refine ⟨_, k, hk, (mem_dec_it (by decide)).mpr ⟨?_, rfl⟩⟩
  intro w hw
  obtain rfl : w = .wu := by simpa (decide := true) [k, init] using hw
  exact ⟨.b, by simp [k, e], rfl, by simp⟩

end M₁

/-! ### The model M₃ (§4.4.2) -/

/-- The eight worlds of Table 4 add to the worlds of `World` whether Sue has the belief. -/
inductive World₃ where
  | wbus | wbu | wbs | wb | wus | wu | ws | w0

/-- `b` is a bathroom in the four bathroom worlds of Table 4. -/
abbrev bathroom₃ : Ent → World₃ → Prop := atom .b {.wbus, .wbu, .wbs, .wb}

/-- `b` is upstairs in the four upstairs worlds of Table 4. -/
abbrev upstairs₃ : Ent → World₃ → Prop := atom .b {.wbus, .wbu, .wus, .wu}

/-- Sue's doxastic state entails that there is a bathroom upstairs in the worlds `wbus`, `wbs`,
`wus` and `ws`, and she has no belief elsewhere. -/
def dox₃ : Ent → World₃ → Set World₃
  | .sue, .wbus | .sue, .wbs | .sue, .wus | .sue, .ws => {.wbus, .wbu}
  | _, _ => Set.univ

-- Table 4: the column of `believe`
theorem dox₃_subset_iff (w : World₃) :
    dox₃ .sue w ⊆ {.wbus, .wbu} ↔ w ∈ ({.wbus, .wbs, .wus, .ws} : Set World₃) := by
  have huniv : ¬ (Set.univ : Set World₃) ⊆ {.wbus, .wbu} := fun h ↦ by
    simpa using h (Set.mem_univ .w0)
  cases w <;> simp [dox₃, huniv]

/-- *There isn't a bathroom. Sue believes it's upstairs.* (51) -/
abbrev modalSub : Update (State World₃ Ent) :=
  thereIsnt bathroom₃ φDC ○ (believes .sue dox₃ upstairs₃).dec φDC φ₃

theorem sat_refer_upstairs₃ :
    sat upstairs₃ (refer Ent.b {.wbus, .wbu, .wbs, .wb}) = {.wbus, .wbu} := by
  rw [sat_refer_atom]
  ext w
  cases w <;> simp

/-- The output of Figure 11, at the commitment set `dc`. -/
def j₁₁ (dc : Set World₃) : State World₃ Ent :=
  ((((((init dc).updateProp φ₁ {.wus, .wu, .ws, .w0}).updateProp φ₂
    {.wbus, .wbu, .wbs, .wb}).updateIndiv υ (refer .b {.wbus, .wbu, .wbs, .wb})).updateProp φ₃
      {.wbus, .wbs, .wus, .ws}).updateIndiv υ₂ fun _ ↦ Part.some .sue).updateProp φ₄ {.wbus, .wbu}

-- Figure 11
theorem mem_modalSub {dc : Set World₃} {j : State World₃ Ent} :
    init dc ~[modalSub] j ↔ dc ⊆ {.wus, .ws} ∧ j = j₁₁ dc := by
  have hT : {w | dox₃ .sue w ⊆ ({.wbus, .wbu} : Set World₃)} = {.wbus, .wbs, .wus, .ws} :=
    Set.ext fun w ↦ dox₃_subset_iff w
  have hI : ({.wus, .wu, .ws, .w0} ∩ {.wbus, .wbs, .wus, .ws} : Set World₃) = {.wus, .ws} := by
    ext w
    cases w <;> simp
  have hc : ({.wbus, .wbu, .wbs, .wb} : Set World₃)ᶜ = {.wus, .wu, .ws, .w0} := by
    ext w
    cases w <;> simp
  have hk {k : State World₃ Ent} : (init dc ~[thereIsnt bathroom₃ φDC] k) ↔
      dc ⊆ {.wus, .wu, .ws, .w0} ∧ k = (((init dc).updateProp φ₁ {.wus, .wu, .ws, .w0}).updateProp
        φ₂ {.wbus, .wbu, .wbs, .wb}).updateIndiv υ (refer .b {.wbus, .wbu, .wbs, .wb}) := by
    simp only [mem_thereIsnt (by decide : φDC ≠ φ₁), isWitness_atom_iff, exists_eq_left]
    simp only [witnessed_atom, hc, init_prop]
  have hdc : dc ⊆ {.wus, .ws} ↔ dc ⊆ {.wus, .wu, .ws, .w0} ∧ dc ⊆ {.wbus, .wbs, .wus, .ws} := by
    rw [← Set.subset_inter_iff, hI]
  rw [hdc]
  constructor
  · rintro ⟨k, hk', hj⟩
    obtain ⟨h₁, rfl⟩ := hk.mp hk'
    obtain ⟨h₂, rfl⟩ := (mem_dec_believes (by decide)).mp hj
    simp (decide := true) only [State.updateProp_prop_of_ne, State.updateIndiv_prop,
      State.updateIndiv_indiv_self, sat_refer_upstairs₃, hT, init_prop] at h₂ ⊢
    exact ⟨⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨⟨h₁, h₂⟩, rfl⟩
    refine ⟨_, hk.mpr ⟨h₁, rfl⟩, (mem_dec_believes (by decide)).mpr ?_⟩
    simp (decide := true) only [State.updateProp_prop_of_ne, State.updateIndiv_prop,
      State.updateIndiv_indiv_self, sat_refer_upstairs₃, hT, init_prop]
    exact ⟨h₂, rfl⟩

/-! ### The judgments -/

section Rows

open Examples

variable (R S : E → W → Prop)

theorem rows_veridical (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex1a, ex18ac],
    (Acceptable {φDC} (thereIs R ○ itIs S φDC φ₃) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦
    mem_dom_thereIs_comp_itIs).mpr h) (by revert d; decide)

theorem rows_negated : ∀ d ∈ [ex1b, ex6a, ex18bc, ex26],
    (Acceptable {φDC} (thereIsnt R φDC ○ itIs S φDC φ₃) ↔ d.judgment = .acceptable) := fun d hd ↦ by
  refine iff_of_false ?_ (by revert d; decide)
  rintro ⟨i, -, hne, hj⟩
  simpa [mem_dom_thereIsnt_comp_itIs.mp hj] using hne φDC

theorem rows_doubleNeg (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex2a, ex9, ex42a],
    (Acceptable {φDC} (notThereIsnt R ○ itIs S φDC φ₄) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦
    mem_dom_notThereIsnt_comp_itIs).mpr h) (by revert d; decide)

theorem rows_bathDisj (h : ((witnessed R)ᶜ ∪ witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2b, ex10, ex42b], (Acceptable {φDC} (thereIsntOr R S) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_thereIsntOr).mpr h)
    (by revert d; decide)

theorem rows_disagree (h : ((witnessed R)ᶜ).Nonempty) (h' : (witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2c, ex12, ex42c],
    (Acceptable {φDCA, φDCB} (thereIsnt R φDCA ○ itIs S φDCB φ₃) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true (acceptable_disagree.mpr ⟨h, h'⟩) (by revert d; decide)

-- (15), without its modal
theorem rows_15 (h : ((witnessed R)ᶜ).Nonempty) :
    (Acceptable {φDC} (thereIsnt R φDC ○ ((it S υ).not φ₄).dec φDC φ₃) ↔
      ex15.judgment = .acceptable) :=
  iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_thereIsnt_comp_not_it).mpr h)
    (by decide)

theorem rows_knows (a : E) (dox : E → W → Set W) :
    (Acceptable {φDC} (thereIsnt R φDC ○
        (properName a υ₂ (Clause.knows dox (it S υ) φ₄)).dec φDC φ₃) ↔
      ex13b.judgment = .acceptable) := by
  refine iff_of_false ?_ (by decide)
  rintro ⟨i, -, hne, j, hj⟩
  simpa [eq_empty_of_mem_thereIsnt_comp_knows hj] using hne φDC

-- §4.2.2: the semantics admits the unacceptable (45), whose second disjunct's context lies in the
-- first's; Hurford's constraint "might be viewed" as the pragmatic filter on it (p. 34)
theorem rows_45 (h : (witnessed R).Nonempty) :
    Acceptable {φDC} ((existential R υ).or (it S υ) φ₂ φ₃ |>.dec φDC φ₁) ∧
      (∀ i j : State W E, i ~[(existential R υ).or (it S υ) φ₂ φ₃ |>.dec φDC φ₁] j →
        j.prop φ₃ ⊆ j.prop φ₂) ∧ ex45.judgment = .unacceptable :=
  ⟨(acceptable_iff_nonempty fun _ ↦ mem_dom_or_existential_it).mpr h,
    fun _ _ ↦ subset_of_mem_or_existential_it, rfl⟩

-- (6c) and (13a) are `Cole said` at the doxastic state `dox`, (49) and (51) Sue's
theorem rows_attitude (a : E) (dox : E → W → Set W)
    (h : ∃ e, IsWitness R (witnessed R) e ∧ ((witnessed R)ᶜ ∩ {w | dox a w ⊆ sat S e}).Nonempty) :
    ∀ d ∈ [ex6c, ex13a, ex49, ex51],
    (Acceptable {φDC} (thereIsnt R φDC ○ (believes a dox S).dec φDC φ₃) ↔
      d.judgment = .acceptable) := fun d hd ↦ by
  refine iff_of_true ?_ (by revert d; decide)
  obtain ⟨e, he, hne⟩ := h
  exact ⟨init ((witnessed R)ᶜ ∩ {w | dox a w ⊆ sat S e}),
    Update.mem_box_singleton.mpr ⟨⟨_, rfl⟩, trivial⟩, by simpa using hne,
    mem_dom_thereIsnt_comp_believes.mpr ⟨by simp, e, he, by simp⟩⟩

-- §4.4.2: the hypothesis of `rows_attitude` holds on M₃
theorem exists_isWitness_modalSub :
    ∃ e, IsWitness bathroom₃ (witnessed bathroom₃) e ∧
      ((witnessed bathroom₃)ᶜ ∩ {w | dox₃ .sue w ⊆ sat upstairs₃ e}).Nonempty := by
  refine ⟨_, isWitness_atom_iff.mpr rfl, .wus, ?_, ?_⟩
  · simp [witnessed_atom]
  · rw [Set.mem_ofPred_eq, sat_refer_upstairs₃]
    exact (dox₃_subset_iff _).mpr (by simp)

end Rows

end Hofmann2025
