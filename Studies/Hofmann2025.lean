module

public import Linglib.Data.Examples.Hofmann2025
public import Linglib.Semantics.Dynamic.ICDRT.Clause

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

Every indefinite introduces its discourse referent globally, relative to its own local context, and
a pronoun needs that referent throughout its own local context under consistent speaker commitments.
Over an arbitrary model this derives that [a negated antecedent leaves a veridical anaphor no
consistent commitments](##mem_dom_not_comp_it_self), that
[double negation](##mem_dom_not_not_comp_it) and [the bathroom disjunction](##mem_dom_or_not_it)
have the weak reading, that [interlocutors who disagree stay consistent](##mem_dom_not_comp_it), and
that [a hypothetical anaphor can have a counterfactual
antecedent](##status_thereIsnt_comp_believes). The paper's figures and tables are instances on its
models.

## Implementation notes

* The fragment is `Semantics/Dynamic/ICDRT/Clause.lean`, where a clause returns its local context
  instead of reading it from a register. There its operators are shown to be the DRSs of Appendix C,
  with the repair of (40) that the Errata explain (`ICDRT.maxInput`).
* This file follows the formulas on commitment sets, in which one is a register fixed by the initial
  state. The commitment sets a discourse allows, Table 1's column, range over initial states, and
  pragmatic maximization (35) is `maxInput φDC`. Consistency (31) holds of every state, so
  `Acceptable` reads it off the initial state.
* The rows carry no analysis. The status (16) of each antecedent and anaphor is derived from the run
  of its discourse (`status_thereIs_comp_itIs` and the theorems after it).
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
  and leaving (18) and (19) as printed, [selects the first row](##mem_thereIsnt_bathroom) and [only
  removes outputs](##thereIsnt_subset_printed41). (26) survives the defect:
  [it needs no maximization](##eq_empty_of_mem_printed41_comp_printedIt).
* Figures 3 and 4 and pp. 12, 14 and 28 narrow a commitment set, but (19) has no `[φDC]`, and
  Tables 1 and 2 instead eliminate its possible values. [No assertion changes a commitment
  set](##ICDRT.Clause.fixes_dec), so (35) and the formal clause of (21a) hold of every update. A `P`
  with no successful update is true by that clause and false by (21c), and (21d) and (21e) collapse
  with it, so the "contextually entails" of (45) is read here as inclusion of contexts.
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
  (53) and (54). Those rows have no derived status yet.
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

universe u

namespace Hofmann2025

open DynamicSemantics
open DynamicSemantics.Update (test box maxAt Fixes mem_box_singleton_comp)
open ICDRT SetRel

variable {W E : Type u} {i j k : State W E} {s t : Set W} {R S : E → W → Prop} {v v' : IVar}
  {φ φ' φ'' φ''' r r' : PVar} {a : E} {dox : E → W → Set W}

/-! ### Antecedent and anaphor -/

/-- Interlocutors may contradict each other (§4.3): the first commits that there is no `R`, the
second that an `R` is an `S`, and neither commitment set need be empty. -/
theorem mem_dom_not_comp_it (h : r' ≠ φ) (h' : r' ≠ φ') :
    i ∈ (((existential R v).not φ').dec r φ ○ (it S v).dec r' φ'').dom ↔
      i.prop r ⊆ (witnessed R)ᶜ ∧ i.prop r' ⊆ witnessed (R ⊓ S) := by
  simp [mem_dec_not_existential, mem_dec_it, State.updateProp_prop_of_ne _ h,
    State.updateProp_prop_of_ne _ h', and_assoc, exists_isWitness_subset_sat_iff]

/-- A veridical anaphor to a negated antecedent leaves the speaker no consistent commitments
(§3.4.2), whatever the model. -/
theorem mem_dom_not_comp_it_self (h : r ≠ φ) (h' : r ≠ φ') :
    i ∈ (((existential R v).not φ').dec r φ ○ (it S v).dec r φ'').dom ↔ i.prop r = ∅ := by
  have : (witnessed R)ᶜ ∩ witnessed (R ⊓ S) = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨h, h'⟩ ↦ h (witnessed_inf_subset_left h')
  rw [mem_dom_not_comp_it h h', ← Set.subset_inter_iff, this, Set.subset_empty_iff]

-- (18a), (18c): the weak reading of a veridical antecedent
theorem mem_dom_existential_comp_it (h : r ≠ φ) :
    i ∈ ((existential R v).dec r φ ○ (it S v).dec r φ'').dom ↔
      i.prop r ⊆ witnessed (R ⊓ S) := by
  simpa [mem_dec_existential, mem_dec_it, State.updateProp_prop_of_ne _ h, and_assoc,
    exists_isWitness_subset_sat_iff] using fun h ↦ h.trans witnessed_inf_subset_left

/-- A veridical anaphor to a doubly negated antecedent has the weak reading of §4.5: it is true
where some `R` is an `S`, whatever other `R`s there are. -/
theorem mem_dom_not_not_comp_it (h : r ≠ φ) (h' : r ≠ φ') (h'' : r ≠ φ'') :
    i ∈ (((((existential R v).not φ'').not φ').dec r φ) ○ (it S v).dec r φ''').dom ↔
      i.prop r ⊆ witnessed (R ⊓ S) := by
  simpa [mem_dec_not_not_existential, mem_dec_it, State.updateProp_prop_of_ne _ h,
    State.updateProp_prop_of_ne _ h', State.updateProp_prop_of_ne _ h'', and_assoc,
    exists_isWitness_subset_sat_iff] using fun h ↦ h.trans witnessed_inf_subset_left

-- (15): the second prejacent's context lies in the counterfactual first, so the speaker commits
-- to nothing about `S`
theorem mem_dom_not_comp_not_it (h : r ≠ φ) (h' : r ≠ φ') :
    i ∈ (((existential R v).not φ').dec r φ ○ ((it S v).not φ''').dec r φ'').dom ↔
      i.prop r ⊆ (witnessed R)ᶜ := by
  simp only [SetRel.mem_dom, SetRel.mem_comp, mem_dec_not_existential]
  refine ⟨fun ⟨_, _, ⟨hr, _⟩, _⟩ ↦ hr, fun hr ↦ ?_⟩
  obtain ⟨e, he, -⟩ := exists_isWitness_sat_eq R S
  obtain ⟨j, hj⟩ := (hasTruthSet_it (S := S) (v := v)).not (φ' := φ''').mem_dom_dec
    (i := ((i.updateIndiv v e).updateProp φ' (witnessed R)).updateProp φ (witnessed R)ᶜ)
    (r := r) (φ := φ'') |>.mpr (by
      have hc : i.prop r ⊆ (sat S e)ᶜ := fun w hw hs ↦ hr hw (he.sat_subset hs).1
      simpa [State.updateProp_prop_of_ne _ h, State.updateProp_prop_of_ne _ h'] using hc)
  exact ⟨j, _, ⟨hr, e, he, rfl⟩, hj⟩

-- (38), (39): a pronoun's referent is entailed in its local context, which lies in its antecedent's
theorem subset_of_mem_dec_it (hφ : φ' ≠ φ) (hk : k.prop φ' = (k.indiv v).Dom)
    (h : k ~[(it S v).dec r φ] j) : j ∈ localEntailment φ v ∧ j.prop φ ⊆ j.prop φ' := by
  obtain ⟨-, rfl⟩ := mem_dec_it.mp h
  have hl : k.updateProp φ (sat S (k.indiv v)) ∈ localEntailment φ v :=
    mem_localEntailment_of_mem_predication (R := S) (by simp)
  exact ⟨hl, (mem_localEntailment_iff (by simpa [State.updateProp_prop_of_ne _ hφ] using hk)).mp hl⟩

/-- The bathroom disjunction has the weak reading of §4.5: it is true where there is no `R` or
some `R` is an `S`. -/
theorem mem_dom_or_not_it :
    i ∈ ((((existential R v).not φ').or (it S v) φ φ'').dec r φ''').dom ↔
      i.prop r ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  (hasTruthSet_connective_it (f := (· ∪ ·)) mem_maximal_not_existential (fun _ _ ↦ by simp)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec

-- (61): the conditional and the bathroom disjunction agree, with no stipulated equivalence
theorem mem_dom_ifThen_it :
    i ∈ (((existential R v).ifThen (it S v) φ φ'').dec r φ''').dom ↔
      i.prop r ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  (hasTruthSet_connective_it (f := fun s t ↦ sᶜ ∪ t) mem_maximal_existential (fun _ _ ↦ by simp)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec

-- (45): the semantics admits it
theorem mem_dom_or_existential_it :
    i ∈ (((existential R v).or (it S v) φ φ'').dec r φ''').dom ↔ i.prop r ⊆ witnessed R := by
  rw [(hasTruthSet_connective_it (f := (· ∪ ·)) mem_maximal_existential (fun _ _ ↦ by simp)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec,
    Set.union_eq_left.mpr witnessed_inf_subset_left]

-- (45): the second disjunct's context lies in the first's
theorem subset_of_mem_or_existential_it (hφ : φ ≠ φ'') (hφ' : φ''' ≠ φ) (hφ'' : φ''' ≠ φ'')
    (h : i ~[((existential R v).or (it S v) φ φ'').dec r φ'''] j) : j.prop φ'' ⊆ j.prop φ := by
  obtain ⟨-, _, hk, rfl⟩ := (hasTruthSet_connective_it (f := (· ∪ ·)) mem_maximal_existential
    (fun _ _ ↦ by simp) fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dec.mp h
  obtain ⟨e, he, -, rfl⟩ := (mem_connective_it mem_maximal_existential (fun _ _ ↦ by simp)).mp hk
  simpa [State.updateProp_prop_of_ne _ hφ'.symm, State.updateProp_prop_of_ne _ hφ''.symm,
    State.updateProp_prop_of_ne _ hφ] using he.sat_subset.trans Set.inter_subset_left

theorem mem_dom_not_comp_believes (hv : v ≠ v') (h : r ≠ φ) (h' : r ≠ φ') :
    i ∈ (((existential R v).not φ').dec r φ ○ (believes a dox S v v' φ'').dec r φ''').dom ↔
      i.prop r ⊆ (witnessed R)ᶜ ∧
        ∃ e, IsWitness R (witnessed R) e ∧ i.prop r ⊆ {w | dox a w ⊆ sat S e} := by
  simp [mem_dec_not_existential, mem_dec_believes hv, State.updateProp_prop_of_ne _ h,
    State.updateProp_prop_of_ne _ h', and_assoc]

-- (13b): a veridical attitude requires the referent where the speaker commits, which a
-- counterfactual antecedent excludes
theorem eq_empty_of_mem_not_comp_knows (hv : v ≠ v') (hr : r ≠ φ) (hr' : r ≠ φ')
    (h : i ~[((existential R v).not φ').dec r φ ○
      (properName a v' (Clause.knows dox (it S v) φ'')).dec r φ'''] j) : i.prop r = ∅ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨s, _, hm, hs, -⟩ := Clause.mem_dec.mp hj
  obtain ⟨t, _, hb, hst, -⟩ := Clause.mem_knows.mp hm.1
  obtain ⟨rfl, -⟩ := hasTruthSet_it.mem_maximal.mp hb
  simp only [State.updateProp_prop_of_ne _ hr, State.updateProp_prop_of_ne _ hr',
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_of_ne _ hv,
    State.updateIndiv_indiv_self] at hs hst
  exact Set.eq_empty_of_subset_empty fun w hw ↦ hdc hw (he.sat_subset (hst (hs hw)).1).1

/-! ### The relative update and the local context (§§2.1, 3.2.1) -/

-- (16), (18a), (25): the negated scope needs the referent exactly outside where it exists
theorem eq_univ_of_mem_indefinite_not_it
    (h : (s, j) ∈ indefinite v (commonNoun R) (fun u ↦ (it S u).not φ') i) :
    s = Set.univ ∧ witnessed R = Set.univ := by
  obtain ⟨e, k, hd, ⟨hR, rfl⟩, hj⟩ := h
  obtain ⟨t, l, ht, hs, -⟩ := Clause.mem_not.mp hj
  obtain ⟨rfl, -⟩ := hasTruthSet_it.mem_maximal.mp ht
  simp only [State.updateIndiv_indiv_self] at hd hR hs
  have hempty : sat S e = ∅ := Set.eq_empty_of_forall_notMem fun w hw ↦ by
    have hdw : w ∈ e.Dom := sat_subset_dom S e hw
    rw [← hd, hs] at hdw
    exact hdw hw
  have huniv : s = Set.univ := by rw [hs, hempty, Set.compl_empty]
  refine ⟨huniv, Set.eq_univ_of_forall fun w ↦ ?_⟩
  obtain ⟨a, -, hRa⟩ := hR (huniv ▸ Set.mem_univ w)
  exact ⟨a, hRa⟩

/-- Stone's relative variable update has only the implication from the context to a referent. -/
def stoneExistential (R : E → W → Prop) (v : IVar) : Clause W E :=
  fun i ↦ {p | ∃ e, p.1 ⊆ e.Dom ∧ p.1 ⊆ sat R e ∧ p.2 = i.updateIndiv v e}

theorem hasTruthSet_stoneExistential : (stoneExistential R v).HasTruthSet fun _ ↦ witnessed R :=
  fun i ↦ by
    refine ⟨?_, fun s ⟨j, e, _, he, _⟩ w hw ↦ ?_⟩
    · obtain ⟨e, he, -⟩ := exists_isWitness_sat (subset_refl (witnessed R)) ⊤
      exact ⟨_, e, he.1.subset, he.2, rfl⟩
    · obtain ⟨a, -, hR⟩ := he hw
      exact ⟨a, hR⟩

-- (14), (15): a local context under Heim's negation lies in the global context, so none is
-- available to a pronoun whose referent exists only in the negated worlds
theorem eq_empty_of_subset_ccp_neg {X : Type*} {f g : CCP X} {c : Set X} (hg : g.IsEliminative)
    (h : g (CCP.neg f c) ⊆ f c) : g (CCP.neg f c) = ∅ :=
  Set.eq_empty_of_subset_empty fun _ hw ↦ (hg _ hw).2 (h hw)

/-! ### Acceptability (§3.3.1) -/

/-- An update is acceptable if it succeeds at some initial state (33), which introduces the
commitment sets `dcs` to the null assignment (32), and they are nonempty (31). -/
def Acceptable (dcs : Finset PVar) (D : Update (State W E)) : Prop :=
  ∃ i, State.null ~[box dcs Set.univ] i ∧ (∀ x ∈ dcs, (i.prop x).Nonempty) ∧ i ∈ D.dom

theorem acceptable_iff_nonempty {D : Update (State W E)} {A : Set W}
    (hA : ∀ i : State W E, i ∈ D.dom ↔ i.prop r ⊆ A) : Acceptable {r} D ↔ A.Nonempty := by
  constructor
  · rintro ⟨i, -, hne, hj⟩
    exact (hne r (Finset.mem_singleton_self _)).mono ((hA i).mp hj)
  · intro hne
    exact ⟨State.null.updateProp r A, Update.mem_box_singleton.mpr ⟨⟨A, rfl⟩, trivial⟩,
      by simpa using hne, (hA _).mpr (by simp)⟩

-- (42c): the commitment sets of the interlocutors are independent
theorem acceptable_not_comp_it (hrr : r ≠ r') (h : r' ≠ φ) (h' : r' ≠ φ') :
    Acceptable {r, r'} (((existential R v).not φ').dec r φ ○ (it S v).dec r' φ'') ↔
      ((witnessed R)ᶜ).Nonempty ∧ (witnessed (R ⊓ S)).Nonempty := by
  constructor
  · rintro ⟨i, -, hne, hj⟩
    obtain ⟨hA, hB⟩ := (mem_dom_not_comp_it h h').mp hj
    exact ⟨(hne r (by simp)).mono hA, (hne r' (by simp)).mono hB⟩
  · rintro ⟨hX, hY⟩
    refine ⟨(State.null.updateProp r (witnessed R)ᶜ).updateProp r' (witnessed (R ⊓ S)),
      Update.mem_box_insert_of_mem ⟨_, rfl⟩ (Update.mem_box_singleton.mpr ⟨⟨_, rfl⟩, trivial⟩),
      ?_, (mem_dom_not_comp_it h h').mpr ?_⟩
    · simpa [State.updateProp_prop_of_ne _ hrr] using ⟨hX, hY⟩
    · simp [State.updateProp_prop_of_ne _ hrr]

/-! ### The discourses -/

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

/-! ### The status of antecedent and anaphor (16), (36), (37) -/

-- (1a), (18a), (18c): a veridical antecedent and a veridical anaphor
theorem status_thereIs_comp_itIs (h : i ~[thereIs R ○ itIs S φDC φ₃] j) :
    j.prop φDC ⊆ (j.indiv υ).Dom ∧ j.prop φDC ⊆ j.prop φ₃ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_existential.mp hk
  obtain ⟨hs, rfl⟩ := mem_dec_it.mp hj
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self, ← he.1] at hs ⊢
  exact ⟨hdc, hs⟩

-- (1b), (6a), (18b), (18c), (26): a counterfactual antecedent and a veridical anaphor
theorem status_thereIsnt_comp_itIs (h : i ~[thereIsnt R φDC ○ itIs S φDC φ₃] j) :
    Disjoint (j.prop φDC) (j.indiv υ).Dom ∧ j.prop φDC ⊆ j.prop φ₃ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨hs, rfl⟩ := mem_dec_it.mp hj
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self, ← he.1] at hs ⊢
  exact ⟨Set.disjoint_left.mpr fun _ hw hw' ↦ hdc hw hw', hs⟩

-- (2a), (9), (42a): double negation makes the antecedent veridical
theorem status_notThereIsnt_comp_itIs (h : i ~[notThereIsnt R ○ itIs S φDC φ₄] j) :
    j.prop φDC ⊆ (j.indiv υ).Dom ∧ j.prop φDC ⊆ j.prop φ₄ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_not_existential.mp hk
  obtain ⟨hs, rfl⟩ := mem_dec_it.mp hj
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self, ← he.1] at hs ⊢
  exact ⟨hdc, hs⟩

-- (2c), (12), (42c): the antecedent is counterfactual for `A` and veridical for `B`, whose anaphor
-- is veridical
theorem status_disagree (h : i ~[thereIsnt R φDCA ○ itIs S φDCB φ₃] j) :
    Disjoint (j.prop φDCA) (j.indiv υ).Dom ∧ j.prop φDCB ⊆ (j.indiv υ).Dom ∧
      j.prop φDCB ⊆ j.prop φ₃ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨hs, rfl⟩ := mem_dec_it.mp hj
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self] at hs ⊢
  exact ⟨Set.disjoint_left.mpr fun _ hw hw' ↦ hdc hw (he.1 ▸ hw'),
    hs.trans (sat_subset_dom S e), hs⟩

-- (15): a counterfactual antecedent, and an anaphor in a context disjoint from the commitments
theorem status_thereIsnt_comp_not_it
    (h : i ~[thereIsnt R φDC ○ ((it S υ).not φ₄).dec φDC φ₃] j) :
    Disjoint (j.prop φDC) (j.indiv υ).Dom ∧ Disjoint (j.prop φDC) (j.prop φ₄) := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨-, _, hk', rfl⟩ := ((hasTruthSet_it (S := S) (v := υ)).not (φ' := φ₄)).mem_dec.mp hj
  obtain ⟨_, _, hm, -, rfl⟩ := Clause.mem_not.mp hk'
  obtain ⟨rfl, -, rfl⟩ := hasTruthSet_it.mem_maximal.mp hm
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self, ← he.1]
  exact ⟨Set.disjoint_left.mpr fun _ hw hw' ↦ hdc hw hw',
    Set.disjoint_left.mpr fun _ hw hs ↦ hdc hw (he.sat_subset hs).1⟩

-- (13b): a counterfactual antecedent, and a veridical attitude's complement that the commitments
-- entail
theorem status_thereIsnt_comp_knows
    (h : i ~[thereIsnt R φDC ○ (properName a υ₂ (Clause.knows dox (it S υ) φ₄)).dec φDC φ₃] j) :
    Disjoint (j.prop φDC) (j.indiv υ).Dom ∧ j.prop φDC ⊆ j.prop φ₄ := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨s, l, hm, hs, rfl⟩ := Clause.mem_dec.mp hj
  obtain ⟨t, m, hb, hst, rfl⟩ := Clause.mem_knows.mp hm.1
  obtain ⟨rfl, -, rfl⟩ := hasTruthSet_it.mem_maximal.mp hb
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self,
    State.updateIndiv_indiv_of_ne, ← he.1] at hs hst ⊢
  exact ⟨Set.disjoint_left.mpr fun _ hw hw' ↦ hdc hw hw', fun w hw ↦ (hst (hs hw)).1⟩

-- (2b), (10), (42b): where some worlds have no `R` and some have an `R` that is an `S`, the
-- antecedent of the bathroom disjunction at its greatest commitment set is hypothetical without
-- being counterfactual, its anaphor is not veridical, and the disjuncts' contexts do not overlap
theorem status_thereIsntOr (hX : ((witnessed R)ᶜ).Nonempty) (hY : (witnessed (R ⊓ S)).Nonempty)
    (hi : i.prop φDC = (witnessed R)ᶜ ∪ witnessed (R ⊓ S)) (h : i ~[thereIsntOr R S] j) :
    ¬ j.prop φDC ⊆ (j.indiv υ).Dom ∧ ¬ Disjoint (j.prop φDC) (j.indiv υ).Dom ∧
      ¬ j.prop φDC ⊆ j.prop φ₃ ∧ Disjoint (j.prop φ₂) (j.prop φ₃) := by
  obtain ⟨-, k, hk, rfl⟩ := (hasTruthSet_connective_it (f := (· ∪ ·)) mem_maximal_not_existential
    (fun _ _ ↦ by simp) fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dec.mp h
  obtain ⟨e, he, -, rfl⟩ :=
    (mem_connective_it mem_maximal_not_existential (fun _ _ ↦ by simp)).mp hk
  simp (decide := true) only [State.updateProp_prop_of_ne, State.updateProp_prop_self,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self, ← he.1, hi]
  have hsub : sat S e ⊆ witnessed R := he.sat_subset.trans Set.inter_subset_left
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  refine ⟨fun h ↦ hx (h (Or.inl hx)), fun h ↦ Set.disjoint_left.mp h (Or.inr hy)
    (witnessed_inf_subset_left hy), fun h ↦ hx (hsub (h (Or.inl hx))), ?_⟩
  exact Set.disjoint_left.mpr fun _ hw hs ↦ hw (hsub hs)

/-- A hypothetical anaphor can have a counterfactual antecedent (§4.4), since the attitude does not
make the speaker's commitments entail the anaphor's context: that context lies in the antecedent's,
and outside the commitments. -/
theorem status_thereIsnt_comp_believes
    (h : i ~[thereIsnt R φDC ○ (believes a dox S υ υ₂ φ₄).dec φDC φ₃] j) :
    Disjoint (j.prop φDC) (j.indiv υ).Dom ∧ j.prop φ₄ ⊆ j.prop φ₂ ∧
      Disjoint (j.prop φDC) (j.prop φ₄) := by
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
  obtain ⟨-, rfl⟩ := (mem_dec_believes (by decide)).mp hj
  have hsub : sat S e ⊆ witnessed R := he.sat_subset.trans Set.inter_subset_left
  simp (decide := true) only [State.updateProp_prop_self, State.updateProp_prop_of_ne,
    State.updateIndiv_prop, State.updateProp_indiv, State.updateIndiv_indiv_self,
    State.updateIndiv_indiv_of_ne, ← he.1]
  exact ⟨Set.disjoint_left.mpr fun _ hw hw' ↦ hdc hw hw', hsub,
    Set.disjoint_left.mpr fun w hw hs ↦ hdc hw (hsub hs)⟩

/-! ### The models -/

/-- An initial state of a single speaker whose commitment set is `dc`. -/
def init (dc : Set W) : State W E := State.null.updateProp φDC dc

@[simp] theorem init_prop (dc : Set W) : (init dc : State W E).prop φDC = dc := by
  simp [init]

section Models

variable {b : E} {e : W →. E}

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
theorem mem_maxInput_init {D : Update (State W E)} {A : Set W} {g : Set W → State W E}
    (h : ∀ dc j, (init dc : State W E) ~[D] j ↔ dc ⊆ A ∧ j = g dc) {dc : Set W} :
    (init dc : State W E) ~[maxInput φDC D] j ↔ dc = A ∧ j = g A := by
  have hinit (s : Set W) : (init dc : State W E).updateProp φDC s = init s := by simp [init]
  have hg : IsGreatest {s | (init dc : State W E).updateProp φDC s ∈ D.dom} A := by
    refine ⟨⟨g A, ?_⟩, ?_⟩
    · rw [hinit]
      exact (h A (g A)).mpr ⟨subset_rfl, rfl⟩
    · rintro s ⟨k, hk⟩
      rw [hinit] at hk
      exact ((h s k).mp hk).1
  have hm : Maximal (fun s ↦ (init dc : State W E).updateProp φDC s ∈ D.dom) dc ↔ dc = A :=
    hg.maximal_iff
  rw [mem_maxInput, init_prop, hm, h]
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

theorem sat_upstairs_bathroomRef : sat upstairs bathroomRef = {.wbu} := by
  rw [sat_refer_atom, bathroom_worlds_inter]

section M₁

variable {dc : Set World} {j : State World Ent}

/-- The output of Figure 5, at the commitment set `dc`. -/
def j₅ (dc : Set World) : State World Ent :=
  ((init dc).updateIndiv υ bathroomRef).updateProp φ₁ {.wbu, .wb}

/-- The output of Figure 6, at the commitment set `dc`. -/
def j₆ (dc : Set World) : State World Ent := (j₅ dc).updateProp φ₃ {.wbu}

-- Table 1: assertion eliminates the commitment sets that are not subsets of the bathroom worlds
theorem mem_thereIs_bathroom :
    init dc ~[thereIs bathroom] j ↔ dc ⊆ {.wbu, .wb} ∧ j = j₅ dc := by
  simp only [mem_dec_existential, isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, init_prop, j₅]

-- Figure 5
theorem figure5 :
    init dc ~[maxInput φDC (thereIs bathroom)] j ↔ dc = {.wbu, .wb} ∧ j = j₅ {.wbu, .wb} :=
  mem_maxInput_init fun _ _ ↦ mem_thereIs_bathroom

-- Table 2: the pronoun eliminates further commitment sets
theorem mem_thereIs_comp_itIs_bathroom :
    init dc ~[thereIs bathroom ○ itIs upstairs φDC φ₃] j ↔ dc ⊆ {.wbu} ∧ j = j₆ dc := by
  have hk : (j₅ dc).prop φDC = dc := by simp (decide := true) [j₅]
  have hv : (j₅ dc).indiv υ = bathroomRef := by simp [j₅]
  have hit : j₅ dc ~[itIs upstairs φDC φ₃] j ↔ dc ⊆ {.wbu} ∧ j = j₆ dc := by
    rw [mem_dec_it, hk, hv, sat_upstairs_bathroomRef, j₆]
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
  mem_maxInput_init fun _ _ ↦ mem_thereIs_comp_itIs_bathroom

/-- The output of Figure 7, the first row of Table 3, at the commitment set `dc`. -/
def j₇ (dc : Set World) : State World Ent :=
  (((init dc).updateIndiv υ bathroomRef).updateProp φ₂ {.wbu, .wb}).updateProp φ₁ {.wu, .w0}

-- (41), Figure 7: the prejacent's context is all and only the bathroom worlds, the first row of
-- Table 3
theorem mem_thereIsnt_bathroom :
    init dc ~[thereIsnt bathroom φDC] j ↔ dc ⊆ {.wu, .w0} ∧ j = j₇ dc := by
  simp only [mem_dec_not_existential, isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, compl_bathroom_worlds, init_prop, j₇]

/-- (41) as printed, with the maximization (40) of App. B (10b). -/
def printed41 : Update (State World Ent) :=
  box {φ₁} (incl φDC φ₁) ○ maxAt φ₁ (box {φ₂} (eqCompl φ₁ φ₂) ○
    maxAt φ₂ (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ)))

/-- (30) with the maximization of App. C (19), as (48) prints it for `B`. -/
def printedIt : Update (State World Ent) :=
  box {φ₃} (incl φDC φ₃) ○ maxAt φ₃ (test (predication upstairs φ₃ υ))

theorem printed41_eq : printed41 = box {φ₁} (incl φDC φ₁) ○ (box {φ₂} (eqCompl φ₁ φ₂) ○
    (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ))) := by
  have hf {r : PVar} : Fixes r (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ) :
      Update (State World Ent)) :=
    (fixes_relUpdate _ _ _).comp (Update.fixes_test _ _)
  rw [printed41, Update.maxAt_eq_of_fixes hf, Update.maxAt_eq_of_fixes
    ((Update.fixes_box (by simp (decide := true)) _).comp hf)]

/-- A row of Table 3, with `s` the value of `φ₂`. -/
def table3 (s : Set World) : State World Ent :=
  (((init sᶜ).updateProp φ₁ sᶜ).updateProp φ₂ s).updateIndiv υ (refer .b s)

-- Table 3: every row is an output of (41) as printed; `mem_thereIsnt_bathroom` keeps only the first
theorem mem_printed41 {s : Set World} (hs : s ⊆ {.wbu, .wb}) :
    init sᶜ ~[printed41] table3 s := by
  have hW := isWitness_refer (b := Ent.b) hs
  rw [printed41_eq, mem_box_singleton_comp]
  refine ⟨sᶜ, by simp (decide := true) [incl, init], mem_box_singleton_comp.mpr
    ⟨s, by simp (decide := true) [eqCompl], _, updateIndiv_mem_relUpdate (by simpa using hW.1), rfl,
      ?_⟩⟩
  simpa [table3] using hW.2

theorem thereIsnt_subset_printed41 : thereIsnt bathroom φDC ⊆ printed41 := by
  rw [thereIsnt, dec_not_existential_eq (by decide) (by decide), printed41_eq]
  exact comp_subset_comp_right ((maxInput_subset _ _).trans
    (comp_subset_comp_right (maxInput_subset _ _)))

-- §3.4.2: local entailment and consistency exclude (26) under (40) as printed
theorem eq_empty_of_mem_printed41_comp_printedIt {i : State World Ent}
    (h : i ~[printed41 ○ printedIt] j) : j.prop φDC = ∅ := by
  have h₃ : maxAt φ₃ (test (predication upstairs φ₃ υ)) =
      (test (predication upstairs φ₃ υ) : Update (State World Ent)) :=
    Update.maxAt_eq_of_fixes (Update.fixes_test _ _)
  rw [printed41_eq, printedIt, h₃] at h
  obtain ⟨k, hk, hj⟩ := h
  obtain ⟨s, hs, hk⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨t, ht, m, hm, rfl, -⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨⟨e, rfl⟩, hd⟩ := mem_relUpdate.mp hm
  obtain ⟨u, hu, rfl, hsat⟩ := mem_box_singleton_comp.mp hj
  simp (decide := true) only [extend_pvar, extend_ivar, mem_incl, mem_eqCompl, mem_predication,
    State.updateProp_prop_of_ne, State.updateProp_prop_self, State.updateProp_indiv,
    State.updateIndiv_prop, State.updateIndiv_indiv_self] at hs ht hu hsat hd ⊢
  refine Set.eq_empty_of_subset_empty fun w hw ↦ ?_
  have hc := ht ▸ hs hw
  exact hc (hd ▸ sat_subset_dom _ _ (hsat (hu hw)))

-- (35): pragmatic maximization as printed leaves an assertion unchanged
example : maxAt φDC (thereIs bathroom) = thereIs bathroom :=
  Update.maxAt_eq_of_fixes (Clause.fixes_dec (by decide) fun i ⟨_, _⟩ hp ↦ by
    obtain ⟨e, -, rfl⟩ := mem_existential.mp hp
    rfl)

/-- The output of Figure 8, at the commitment set `dc`. -/
def j₈ (dc : Set World) : State World Ent :=
  (((((init dc).updateIndiv υ bathroomRef).updateProp φ₃ {.wbu, .wb}).updateProp φ₂
    {.wu, .w0})).updateProp φ₁ {.wbu, .wb}

-- Figure 8
theorem mem_notThereIsnt_bathroom :
    init dc ~[notThereIsnt bathroom] j ↔ dc ⊆ {.wbu, .wb} ∧ j = j₈ dc := by
  simp only [mem_dec_not_not_existential, isWitness_atom_iff, exists_eq_left]
  simp only [witnessed_atom, compl_bathroom_worlds, init_prop, j₈]

/-- The output of Figure 9, at the commitment set `dc`. -/
def j₉ (dc : Set World) : State World Ent :=
  (((((init dc).updateIndiv υ bathroomRef).updateProp φ₄ {.wbu, .wb}).updateProp φ₂
    {.wu, .w0}).updateProp φ₃ {.wbu}).updateProp φ₁ {.wbu, .wu, .w0}

-- Figure 9
theorem mem_thereIsntOr_bathroom :
    init dc ~[thereIsntOr bathroom upstairs] j ↔ dc ⊆ {.wbu, .wu, .w0} ∧ j = j₉ dc := by
  have hT : ({.wu, .w0} ∪ {.wbu} : Set World) = {.wbu, .wu, .w0} := by
    ext w
    cases w <;> simp
  have hg (i : State World Ent) (e : World →. Ent) :
      ((i.updateIndiv υ e).updateProp φ₄ (witnessed bathroom)).indiv υ = e := by simp
  rw [(hasTruthSet_connective_it (f := (· ∪ ·)) mem_maximal_not_existential hg
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dec]
  simp only [mem_connective_it mem_maximal_not_existential hg, isWitness_atom_iff, exists_eq_left]
  simp only [init_prop, sat_upstairs_bathroomRef, witnessed_atom, compl_bathroom_worlds,
    witnessed_atom_inf_atom, bathroom_worlds_inter, hT, true_and, exists_eq_left, j₉]

/-- An initial state of the two interlocutors of §4.3. -/
def init₂ (dcA dcB : Set World) : State World Ent :=
  (State.null.updateProp φDCA dcA).updateProp φDCB dcB

/-- The output of Figure 10, at the commitment sets `dcA` and `dcB`. -/
def j₁₀ (dcA dcB : Set World) : State World Ent :=
  ((((init₂ dcA dcB).updateIndiv υ bathroomRef).updateProp φ₂ {.wbu, .wb}).updateProp φ₁
    {.wu, .w0}).updateProp φ₃ {.wbu}

-- Figure 10: each interlocutor's commitments stay consistent, though they cannot overlap
theorem mem_disagree_bathroom {dcA dcB : Set World} :
    init₂ dcA dcB ~[thereIsnt bathroom φDCA ○ itIs upstairs φDCB φ₃] j ↔
      dcA ⊆ {.wu, .w0} ∧ dcB ⊆ {.wbu} ∧ j = j₁₀ dcA dcB := by
  have hA : (init₂ dcA dcB : State World Ent).prop φDCA = dcA := by
    simp (decide := true) [init₂]
  have hB : (init₂ dcA dcB : State World Ent).prop φDCB = dcB := by simp [init₂]
  constructor
  · rintro ⟨k, hk, hj⟩
    obtain ⟨hdc, e, he, rfl⟩ := mem_dec_not_existential.mp hk
    obtain rfl := isWitness_atom_iff.mp he
    obtain ⟨hb, rfl⟩ := mem_dec_it.mp hj
    simp (decide := true) only [State.updateProp_prop_of_ne, State.updateIndiv_prop,
      State.updateProp_indiv, State.updateIndiv_indiv_self, sat_upstairs_bathroomRef, hB] at hb ⊢
    rw [hA, witnessed_atom, compl_bathroom_worlds] at hdc
    exact ⟨hdc, hb, by simp [j₁₀, witnessed_atom, compl_bathroom_worlds]⟩
  · rintro ⟨hdc, hb, rfl⟩
    refine ⟨_, mem_dec_not_existential.mpr ⟨?_, _, isWitness_atom_iff.mpr rfl, rfl⟩,
      mem_dec_it.mpr ⟨?_, ?_⟩⟩
    · rwa [hA, witnessed_atom, compl_bathroom_worlds]
    · simpa (decide := true) [hB, sat_upstairs_bathroomRef] using hb
    · simp [j₁₀, witnessed_atom, compl_bathroom_worlds, sat_upstairs_bathroomRef]

-- an indefinite outscoping negation has no output on the model
theorem not_mem_indefinite_not_it {i : State World Ent} {t : Set World} :
    (t, j) ∉ indefinite υ (commonNoun bathroom) (fun u ↦ (it upstairs u).not φ₂) i := fun h ↦ by
  have := (eq_univ_of_mem_indefinite_not_it h).2
  rw [witnessed_atom] at this
  simpa using this.ge (Set.mem_univ World.wu)

-- §3.2.1: under [stone-1999]'s update (26) is consistent, so the biconditional of (25) is crucial
theorem stone_admits_26 :
    init {.wu} ∈ (((stoneExistential bathroom υ).not φ₂).dec φDC φ₁ ○
      itIs upstairs φDC φ₃).dom := by
  have hT := hasTruthSet_stoneExistential (R := bathroom) (v := υ)
  have hsat {s : Set World} (hs : s ⊆ {.wbu, .wb}) :
      s ⊆ sat bathroom (PFun.lift fun _ ↦ Ent.b) := by
    rw [sat_lift_const]
    exact fun w hw ↦ ⟨rfl, hs hw⟩
  let e : World →. Ent := PFun.lift fun _ ↦ .b
  let k : State World Ent := (((init {.wu}).updateIndiv υ e).updateProp φ₂
    (witnessed bathroom)).updateProp φ₁ (witnessed bathroom)ᶜ
  have hk : init {.wu} ~[((stoneExistential bathroom υ).not φ₂).dec φDC φ₁] k := by
    refine (hT.not (φ' := φ₂)).mem_dec.mpr ⟨?_, _, Clause.mem_not.mpr ⟨_, _, hT.mem_maximal.mpr
      ⟨rfl, e, ?_, hsat (by rw [witnessed_atom]), rfl⟩, rfl, rfl⟩, rfl⟩
    · simp [witnessed_atom, compl_bathroom_worlds]
    · intro w _
      simp [e]
  refine ⟨_, k, hk, mem_dec_it.mpr ⟨?_, rfl⟩⟩
  have hk' : k.prop φDC = {.wu} := by simp (decide := true) [k]
  have hv : k.indiv υ = e := by simp [k]
  rw [hk', hv]
  rintro w rfl
  rw [sat_lift_const]
  simp [upstairs, atom]

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
  thereIsnt bathroom₃ φDC ○ (believes .sue dox₃ upstairs₃ υ υ₂ φ₄).dec φDC φ₃

theorem sat_refer_upstairs₃ :
    sat upstairs₃ (refer Ent.b {.wbus, .wbu, .wbs, .wb}) = {.wbus, .wbu} := by
  rw [sat_refer_atom]
  ext w
  cases w <;> simp

/-- The output of Figure 11, at the commitment set `dc`. -/
def j₁₁ (dc : Set World₃) : State World₃ Ent :=
  ((((((init dc).updateIndiv υ (refer .b {.wbus, .wbu, .wbs, .wb})).updateProp φ₂
    {.wbus, .wbu, .wbs, .wb}).updateProp φ₁ {.wus, .wu, .ws, .w0}).updateIndiv υ₂
      (PFun.lift fun _ ↦ .sue)).updateProp φ₄ {.wbus, .wbu}).updateProp φ₃ {.wbus, .wbs, .wus, .ws}

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
  have hdc : dc ⊆ {.wus, .ws} ↔ dc ⊆ {.wus, .wu, .ws, .w0} ∧ dc ⊆ {.wbus, .wbs, .wus, .ws} := by
    rw [← Set.subset_inter_iff, hI]
  have hk {k : State World₃ Ent} : (init dc ~[thereIsnt bathroom₃ φDC] k) ↔
      dc ⊆ {.wus, .wu, .ws, .w0} ∧ k = (((init dc).updateIndiv υ
        (refer .b {.wbus, .wbu, .wbs, .wb})).updateProp φ₂ {.wbus, .wbu, .wbs, .wb}).updateProp φ₁
          {.wus, .wu, .ws, .w0} := by
    simp only [mem_dec_not_existential, isWitness_atom_iff, exists_eq_left]
    simp only [witnessed_atom, hc, init_prop]
  rw [hdc]
  constructor
  · rintro ⟨k, hk', hj⟩
    obtain ⟨h₁, rfl⟩ := hk.mp hk'
    obtain ⟨h₂, rfl⟩ := (mem_dec_believes (by decide)).mp hj
    simp (decide := true) only [State.updateProp_prop_of_ne, State.updateIndiv_prop,
      State.updateProp_indiv, State.updateIndiv_indiv_self, sat_refer_upstairs₃, hT, init_prop]
      at h₂ ⊢
    exact ⟨⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨⟨h₁, h₂⟩, rfl⟩
    refine ⟨_, hk.mpr ⟨h₁, rfl⟩, (mem_dec_believes (by decide)).mpr ?_⟩
    simp (decide := true) only [State.updateProp_prop_of_ne, State.updateIndiv_prop,
      State.updateProp_indiv, State.updateIndiv_indiv_self, sat_refer_upstairs₃, hT, init_prop]
    exact ⟨h₂, rfl⟩

/-! ### The judgments -/

section Rows

open Examples

variable (R S : E → W → Prop)

theorem rows_veridical (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex1a, ex18ac],
    (Acceptable {φDC} (thereIs R ○ itIs S φDC φ₃) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦
    mem_dom_existential_comp_it (by decide)).mpr h) (by revert d; decide)

theorem rows_negated : ∀ d ∈ [ex1b, ex6a, ex18bc, ex26],
    (Acceptable {φDC} (thereIsnt R φDC ○ itIs S φDC φ₃) ↔ d.judgment = .acceptable) := fun d hd ↦ by
  refine iff_of_false ?_ (by revert d; decide)
  rintro ⟨i, -, hne, hj⟩
  simpa [(mem_dom_not_comp_it_self (by decide) (by decide)).mp hj] using hne φDC

theorem rows_doubleNeg (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex2a, ex9, ex42a],
    (Acceptable {φDC} (notThereIsnt R ○ itIs S φDC φ₄) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦
    mem_dom_not_not_comp_it (by decide) (by decide) (by decide)).mpr h) (by revert d; decide)

theorem rows_bathDisj (h : ((witnessed R)ᶜ ∪ witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2b, ex10, ex42b], (Acceptable {φDC} (thereIsntOr R S) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_or_not_it).mpr h)
    (by revert d; decide)

theorem rows_disagree (h : ((witnessed R)ᶜ).Nonempty) (h' : (witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2c, ex12, ex42c],
    (Acceptable {φDCA, φDCB} (thereIsnt R φDCA ○ itIs S φDCB φ₃) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_not_comp_it (by decide) (by decide) (by decide)).mpr ⟨h, h'⟩)
    (by revert d; decide)

-- (15), without its modal
theorem rows_15 (h : ((witnessed R)ᶜ).Nonempty) :
    (Acceptable {φDC} (thereIsnt R φDC ○ ((it S υ).not φ₄).dec φDC φ₃) ↔
      ex15.judgment = .acceptable) :=
  iff_of_true ((acceptable_iff_nonempty fun _ ↦
    mem_dom_not_comp_not_it (by decide) (by decide)).mpr h) (by decide)

theorem rows_knows (a : E) (dox : E → W → Set W) :
    (Acceptable {φDC} (thereIsnt R φDC ○
        (properName a υ₂ (Clause.knows dox (it S υ) φ₄)).dec φDC φ₃) ↔
      ex13b.judgment = .acceptable) := by
  refine iff_of_false ?_ (by decide)
  rintro ⟨i, -, hne, j, hj⟩
  simpa [eq_empty_of_mem_not_comp_knows (by decide) (by decide) (by decide) hj] using hne φDC

-- §4.2.2: the semantics admits the unacceptable (45), whose second disjunct's context lies in the
-- first's; Hurford's constraint "might be viewed" as the pragmatic filter on it (p. 34)
theorem rows_45 (h : (witnessed R).Nonempty) :
    Acceptable {φDC} ((existential R υ).or (it S υ) φ₂ φ₃ |>.dec φDC φ₁) ∧
      (∀ i j : State W E, i ~[(existential R υ).or (it S υ) φ₂ φ₃ |>.dec φDC φ₁] j →
        j.prop φ₃ ⊆ j.prop φ₂) ∧ ex45.judgment = .unacceptable :=
  ⟨(acceptable_iff_nonempty fun _ ↦ mem_dom_or_existential_it).mpr h,
    fun _ _ ↦ subset_of_mem_or_existential_it (by decide) (by decide) (by decide), rfl⟩

-- (6c) and (13a) are `Cole said` at the doxastic state `dox`, (49) and (51) Sue's
theorem rows_attitude (a : E) (dox : E → W → Set W)
    (h : ∃ e, IsWitness R (witnessed R) e ∧ ((witnessed R)ᶜ ∩ {w | dox a w ⊆ sat S e}).Nonempty) :
    ∀ d ∈ [ex6c, ex13a, ex49, ex51],
    (Acceptable {φDC} (thereIsnt R φDC ○ (believes a dox S υ υ₂ φ₄).dec φDC φ₃) ↔
      d.judgment = .acceptable) := fun d hd ↦ by
  refine iff_of_true ?_ (by revert d; decide)
  obtain ⟨e, he, hne⟩ := h
  exact ⟨init ((witnessed R)ᶜ ∩ {w | dox a w ⊆ sat S e}),
    Update.mem_box_singleton.mpr ⟨⟨_, rfl⟩, trivial⟩, by simpa using hne,
    (mem_dom_not_comp_believes (by decide) (by decide) (by decide)).mpr ⟨by simp, e, he, by simp⟩⟩

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
