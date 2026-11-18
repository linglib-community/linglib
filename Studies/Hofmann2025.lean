module

public import Linglib.Data.Examples.Hofmann2025
public import Linglib.Semantics.Dynamic.ICDRT
public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

Every indefinite introduces its discourse referent globally, relative to its own local context, and
a pronoun needs that referent throughout its own local context under consistent speaker commitments.
Over an arbitrary model this derives that [a negated antecedent leaves a veridical anaphor no
consistent commitments](##mem_dom_not_comp_it_self), that [double
negation](##mem_dom_not_not_comp_it) and [the bathroom disjunction](##mem_dom_or_not_it) have the
weak reading, that [interlocutors who disagree stay consistent](##mem_dom_not_comp_it), and that
[a hypothetical anaphor can have a counterfactual antecedent](##status_thereIsnt_comp_believes). The
paper's figures and tables are instances on its models.

## Implementation notes

* The fragment is `Semantics/Dynamic/ICDRT.lean`. The paper stores each local context in a
  propositional dref, read only in the scope of the operator introducing it, and it relies on no
  modal anaphora (§4.4.3), so there a clause returns its context, the state holds only the
  individual drefs, and the commitment set is an argument of `Clause.dec`. The registers appear here
  only for the formulas as printed (`printed41`, `printedIt`), and the fragment's
  output for (41) is [among theirs, with Figure 7's contexts](##exists_mem_printed41).
* The commitment sets a discourse allows, Table 1's column, are the `dc` at which it succeeds, and
  pragmatic maximization (35) [selects the greatest of them](##figure5).
* The rows carry no analysis. The status (16) of each antecedent and anaphor is derived from the run
  of its discourse (`status_veridical` and the theorems after it).
* `Clause.knows` is the veridical attitude of §2.4, which Appendix C does not list, and `Cole said`
  in (6c) and (13a) is `believes` at a doxastic state of its own. `dox₃` is one doxastic state with
  the column of Table 4, which fixes no more. Appendix C's conjunction (18d) enters no derivation
  and is not encoded.
* The second clause of (15) is run without its modal `have to`, so the theorem equally covers
  *There isn't a bathroom. It isn't upstairs*, on which the paper gives no judgment.
* In (44) the outer maximization forces `υ` to an upstairs bathroom wherever one exists; in (43)
  it leaves `υ` free, and the anaphor's context picks the worlds where it is upstairs.

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
open DynamicSemantics.Update
  (test box maxAt Fixes mem_box_singleton mem_box_singleton_comp randomAssign)
open ICDRT SetRel

variable {W E : Type u} {g h : ℕ → (W →. E)} {s t dc dc' A : Set W} {R S : E → W → Prop}
  {v v' : ℕ} {a : E} {dox : E → W → Set W} {P : Clause W E}

/-! ### Antecedent and anaphor -/

/-- Interlocutors may contradict each other (§4.3): the first commits that there is no `R`, the
second that an `R` is an `S`, and neither commitment set need be empty. -/
theorem mem_dom_not_comp_it :
    g ∈ ((existential R v).not.dec dc ○ (it S v).dec dc').dom ↔
      dc ⊆ (witnessed R)ᶜ ∧ dc' ⊆ witnessed (R ⊓ S) :=
  introduces_existential.not.mem_dom_comp_it

/-- A veridical anaphor to a negated antecedent leaves the speaker no consistent commitments
(§3.4.2), whatever the model. -/
theorem mem_dom_not_comp_it_self :
    g ∈ ((existential R v).not.dec dc ○ (it S v).dec dc).dom ↔ dc = ∅ := by
  have : (witnessed R)ᶜ ∩ witnessed (R ⊓ S) = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨h, h'⟩ ↦ h (witnessed_inf_subset_left h')
  rw [mem_dom_not_comp_it, ← Set.subset_inter_iff, this, Set.subset_empty_iff]

-- (18a), (18c): the weak reading of a veridical antecedent
theorem mem_dom_comp_it_of_introduces (hP : P.Introduces R v (witnessed R)) :
    g ∈ (P.dec dc ○ (it S v).dec dc).dom ↔ dc ⊆ witnessed (R ⊓ S) :=
  hP.mem_dom_comp_it.trans <| and_iff_right_of_imp (·.trans witnessed_inf_subset_left)

/-- A veridical anaphor to a doubly negated antecedent has the weak reading of §4.5: it is true
where some `R` is an `S`, whatever other `R`s there are. -/
theorem mem_dom_not_not_comp_it :
    g ∈ ((existential R v).not.not.dec dc ○ (it S v).dec dc).dom ↔ dc ⊆ witnessed (R ⊓ S) :=
  mem_dom_comp_it_of_introduces introduces_existential.not_not

-- (15): the second prejacent's context lies in the counterfactual first, so the speaker commits
-- to nothing about `S`
theorem mem_dom_not_comp_not_it :
    g ∈ ((existential R v).not.dec dc ○ (it S v).not.dec dc).dom ↔ dc ⊆ (witnessed R)ᶜ := by
  rw [introduces_existential.not.mem_dom_comp hasTruthSet_it.not]
  refine and_iff_left_of_imp fun hr ↦ ?_
  obtain ⟨e, he, -⟩ := exists_isWitness_sat_eq R S
  simp only [Function.update_self]
  exact ⟨e, he, fun w hw hs ↦ hr hw (he.sat_subset hs).1⟩

/-- The bathroom disjunction has the weak reading of §4.5: it is true where there is no `R` or
some `R` is an `S`. -/
theorem mem_dom_or_not_it :
    g ∈ (((existential R v).not.or (it S v)).dec dc).dom ↔
      dc ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  introduces_existential.not.hasTruthSet_or_it.mem_dom_dec

-- (61): the conditional and the bathroom disjunction agree, with no stipulated equivalence
theorem mem_dom_ifThen_it :
    g ∈ (((existential R v).ifThen (it S v)).dec dc).dom ↔
      dc ⊆ (witnessed R)ᶜ ∪ witnessed (R ⊓ S) :=
  (introduces_existential.hasTruthSet_connective_it (f := fun s t ↦ sᶜ ∪ t)
    fun _ _ h ↦ Set.union_subset_union_right _ h).mem_dom_dec

-- (45): the semantics admits it
theorem mem_dom_or_existential_it :
    g ∈ (((existential R v).or (it S v)).dec dc).dom ↔ dc ⊆ witnessed R := by
  rw [introduces_existential.hasTruthSet_or_it.mem_dom_dec,
    Set.union_eq_left.mpr witnessed_inf_subset_left]

-- (45): the second disjunct's context lies in the first's
theorem subset_of_mem_or_existential_it (hj : g ~[((existential R v).or (it S v)).dec dc] h) :
    sat S (h v) ⊆ witnessed R := by
  obtain ⟨-, hk⟩ := introduces_existential.hasTruthSet_or_it.mem_dec.mp hj
  obtain ⟨e, he, -, rfl⟩ := introduces_existential.mem_connective_it.mp hk
  simpa using he.sat_subset.trans Set.inter_subset_left

-- (51): the speaker commits that there is no `R`, and to where the attitude holds of a witness
theorem mem_dom_not_comp_believes (hv : v ≠ v') :
    g ∈ ((existential R v).not.dec dc ○ (believes a dox S v v').dec dc).dom ↔
      dc ⊆ (witnessed R)ᶜ ∧ ∃ e, IsWitness R (witnessed R) e ∧ dc ⊆ {w | dox a w ⊆ sat S e} := by
  simp [introduces_existential.not.mem_dom_comp (hasTruthSet_believes hv)]

/-! ### The relative update and the local context (§§2.1, 3.2.1) -/

-- (16), (18a), (25): the negated scope needs the referent exactly outside where it exists
theorem eq_univ_of_mem_indefinite_not_it
    (hj : (s, h) ∈ indefinite v (commonNoun R) (fun u ↦ (it S u).not) g) :
    s = Set.univ ∧ witnessed R = Set.univ := by
  obtain ⟨e, k, hd, ⟨hR, rfl⟩, hj⟩ := hj
  obtain ⟨rfl, -⟩ := hasTruthSet_it.mem_not.mp hj
  simp only [Function.update_self] at hd hR ⊢
  have he : sat S e = ∅ := le_compl_self.mp (hd ▸ sat_subset_dom S e)
  rw [he, Set.compl_empty] at hd hR ⊢
  exact ⟨rfl, Set.univ_subset_iff.mp (IsWitness.subset_witnessed ⟨hd, hR⟩)⟩

/-- Stone's relative variable update has only the implication from the context to a referent. -/
def stoneExistential (R : E → W → Prop) (v : ℕ) : Clause W E :=
  fun g ↦ {p | ∃ e, p.1 ⊆ e.Dom ∧ p.1 ⊆ sat R e ∧ p.2 = g[v ↦ e]}

theorem hasTruthSet_stoneExistential : (stoneExistential R v).HasTruthSet fun _ ↦ witnessed R :=
  fun g ↦ by
    refine ⟨?_, fun s ⟨j, e, _, he, _⟩ w hw ↦ ?_⟩
    · obtain ⟨e, he, -⟩ := exists_isWitness_sat_eq R ⊤
      exact ⟨_, e, he.1.subset, he.2, rfl⟩
    · obtain ⟨a, -, hR⟩ := he hw
      exact ⟨a, hR⟩

-- (14), (15): a local context under Heim's negation lies in the global context, so none is
-- available to a pronoun whose referent exists only in the negated worlds
theorem eq_empty_of_subset_ccp_neg {X : Type*} {f g : CCP X} {c : Set X} (hg : g.IsEliminative)
    (h : g (CCP.neg f c) ⊆ f c) : g (CCP.neg f c) = ∅ :=
  Set.eq_empty_of_subset_empty fun _ hw ↦ (hg _ hw).2 (h hw)

/-! ### Acceptability (§3.3.1) -/

/-- The null assignment holds no information: no dref has a referent (32). -/
def nullAssignment : ℕ → (W →. E) := fun _ _ ↦ Part.none

/-- A discourse is acceptable if some nonempty commitment set satisfies it (31), (33). Nested, it
gives each interlocutor a commitment set of their own. -/
def Acceptable (D : Set W → Prop) : Prop := ∃ dc, dc.Nonempty ∧ D dc

theorem acceptable_iff_nonempty {D : Set W → Prop} (hD : ∀ dc, D dc ↔ dc ⊆ A) :
    Acceptable D ↔ A.Nonempty :=
  ⟨fun ⟨dc, hne, hd⟩ ↦ hne.mono ((hD dc).mp hd), fun hne ↦ ⟨A, hne, (hD A).mpr subset_rfl⟩⟩

-- (35): pragmatic maximization selects the greatest commitment set at which a discourse succeeds
theorem isGreatest_of_forall_iff {D : Set W → Prop} (hD : ∀ dc, D dc ↔ dc ⊆ A) :
    IsGreatest {dc | D dc} A :=
  (Set.ext hD : {dc | D dc} = Set.Iic A) ▸ isGreatest_Iic

/-! ### The discourses -/

/-- The drefs of the derivations: the indefinite and the attitude's subject. -/
def υ : ℕ := 0
@[inherit_doc υ] def υ₂ : ℕ := 1

/-- *There is an `R`.* (19a) -/
abbrev thereIs (R : E → W → Prop) (dc : Set W) : Update ((ℕ → (W →. E))) :=
  (existential R υ).dec dc

/-- *There isn't an `R`.* (41) -/
abbrev thereIsnt (R : E → W → Prop) (dc : Set W) : Update ((ℕ → (W →. E))) :=
  (existential R υ).not.dec dc

/-- *It isn't the case that there isn't an `R`.* (2a), (42a) -/
abbrev notThereIsnt (R : E → W → Prop) (dc : Set W) : Update ((ℕ → (W →. E))) :=
  (existential R υ).not.not.dec dc

/-- *It is `S`.* (30) -/
abbrev itIs (S : E → W → Prop) (dc : Set W) : Update ((ℕ → (W →. E))) := (it S υ).dec dc

/-- *There isn't an `R`, or it is `S`.* (2b), (42b) -/
abbrev thereIsntOr (R S : E → W → Prop) (dc : Set W) : Update ((ℕ → (W →. E))) :=
  ((existential R υ).not.or (it S υ)).dec dc

/-! ### The status of antecedent and anaphor (16), (36), (37) -/

-- whatever embeds it, the antecedent's dref refers at exactly the worlds where its restrictor is
-- witnessed, and the anaphor's speaker commits to the pronoun's local context
theorem status_of_introduces (hP : P.Introduces R v A) (hj : g ~[P.dec dc ○ (it S v).dec dc'] h) :
    dc ⊆ A ∧ (h v).Dom = witnessed R ∧ dc' ⊆ sat S (h v) := by
  obtain ⟨hA, e, he, hk⟩ := hP.mem_comp.mp hj
  obtain ⟨hs, rfl⟩ := mem_dec_it.mp hk
  simp only [Function.update_self] at hs ⊢
  exact ⟨hA, he.1.symm, hs⟩

-- (1a), (2a), (9), (18a), (18c), (42a), at `introduces_existential` and its double negation: a
-- veridical antecedent and a veridical anaphor
theorem status_veridical (hP : P.Introduces R v (witnessed R))
    (hj : g ~[P.dec dc ○ (it S v).dec dc'] h) : dc ⊆ (h v).Dom ∧ dc' ⊆ sat S (h v) := by
  obtain ⟨hA, hd, hs⟩ := status_of_introduces hP hj
  exact ⟨hd ▸ hA, hs⟩

-- (1b), (2c), (6a), (12), (18b), (18c), (26), (42c): the antecedent is counterfactual for the first
-- speaker and veridical for the second, whose anaphor is veridical
theorem status_counterfactual (hP : P.Introduces R v (witnessed R)ᶜ)
    (hj : g ~[P.dec dc ○ (it S v).dec dc'] h) :
    Disjoint dc (h v).Dom ∧ dc' ⊆ (h v).Dom ∧ dc' ⊆ sat S (h v) := by
  obtain ⟨hA, hd, hs⟩ := status_of_introduces hP hj
  exact ⟨hd ▸ Set.subset_compl_iff_disjoint_right.mp hA, hs.trans (sat_subset_dom S _), hs⟩

-- (15): a counterfactual antecedent, and an anaphor in a context disjoint from the commitments
theorem status_thereIsnt_comp_not_it
    (hj : g ~[(existential R v).not.dec dc ○ (it S v).not.dec dc] h) :
    Disjoint dc (h v).Dom ∧ Disjoint dc (sat S (h v)) := by
  obtain ⟨hdc, e, he, hk⟩ := introduces_existential.not.mem_comp.mp hj
  obtain ⟨-, hm⟩ := hasTruthSet_it.not.mem_dec.mp hk
  obtain ⟨-, rfl⟩ := mem_it.mp (hasTruthSet_it.mem_not.mp hm).2
  have hd : Disjoint dc e.Dom := he.1 ▸ Set.subset_compl_iff_disjoint_right.mp hdc
  simpa using ⟨hd, hd.mono_right (sat_subset_dom S e)⟩

-- (13b): a veridical attitude requires the referent where the speaker commits, which a
-- counterfactual antecedent excludes
theorem eq_empty_of_mem_not_comp_knows (hv : v ≠ v')
    (hj : g ~[(existential R v).not.dec dc ○
      (properName a v' (Clause.knows dox (it S v))).dec dc] h) :
    dc = ∅ := by
  obtain ⟨hdc, e, he, hk⟩ := introduces_existential.not.mem_comp.mp hj
  obtain ⟨s, hm, hs⟩ := Clause.mem_dec.mp hk
  obtain ⟨t, hb, hst⟩ := hm.1
  obtain ⟨rfl, -⟩ := mem_maximal_it.mp hb
  rw [Function.update_of_ne hv, Function.update_self] at hst
  exact Set.eq_empty_of_subset_empty fun w hw ↦ hdc hw (he.sat_subset (hst (hs hw)).1).1

-- (2b), (10), (42b): where some worlds have no `R` and some have an `R` that is an `S`, the
-- antecedent of the bathroom disjunction at its greatest commitment set is hypothetical without
-- being counterfactual, its anaphor is not veridical, and the disjuncts' contexts do not overlap
theorem status_thereIsntOr (hX : ((witnessed R)ᶜ).Nonempty) (hY : (witnessed (R ⊓ S)).Nonempty)
    (hdc : dc = (witnessed R)ᶜ ∪ witnessed (R ⊓ S))
    (hj : g ~[((existential R v).not.or (it S v)).dec dc] h) :
    ¬ dc ⊆ (h v).Dom ∧ ¬ Disjoint dc (h v).Dom ∧ ¬ dc ⊆ sat S (h v) ∧
      Disjoint (witnessed R)ᶜ (sat S (h v)) := by
  obtain ⟨-, hk⟩ := introduces_existential.not.hasTruthSet_or_it.mem_dec.mp hj
  obtain ⟨e, he, -, rfl⟩ := introduces_existential.not.mem_connective_it.mp hk
  simp only [Function.update_self, ← he.1, hdc]
  have hsub : sat S e ⊆ witnessed R := he.sat_subset.trans Set.inter_subset_left
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  exact ⟨fun h ↦ hx (h (Or.inl hx)), fun h ↦ Set.disjoint_left.mp h (Or.inr hy)
    (witnessed_inf_subset_left hy), fun h ↦ hx (hsub (h (Or.inl hx))),
    Set.disjoint_left.mpr fun _ hw hs ↦ hw (hsub hs)⟩

/-- A hypothetical anaphor can have a counterfactual antecedent (§4.4), since the attitude does not
make the speaker's commitments entail the anaphor's context: that context lies in the antecedent's,
and outside the commitments. -/
theorem status_thereIsnt_comp_believes (hv : v ≠ v')
    (hj : g ~[(existential R v).not.dec dc ○ (believes a dox S v v').dec dc] h) :
    Disjoint dc (h v).Dom ∧ sat S (h v) ⊆ witnessed R ∧ Disjoint dc (sat S (h v)) := by
  obtain ⟨hdc, e, he, hk⟩ := introduces_existential.not.mem_comp.mp hj
  obtain ⟨-, rfl⟩ := (mem_dec_believes hv).mp hk
  have hd : Disjoint dc e.Dom := he.1 ▸ Set.subset_compl_iff_disjoint_right.mp hdc
  simpa [Function.update_of_ne hv] using ⟨hd, he.sat_subset.trans Set.inter_subset_left,
    hd.mono_right (sat_subset_dom S e)⟩

/-! ### The models -/

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

theorem witnessed_atom_inf_atom : witnessed (atom b s ⊓ atom b t) = s ∩ t := by
  ext w
  simp [witnessed, atom]

theorem isWitness_refer (hs : s ⊆ t) : IsWitness (atom b t) s (refer b s) :=
  ⟨by ext; simp [refer, PFun.mem_dom, PFun.mem_res],
    fun w hw ↦ ⟨b, by simp [refer, hw, PFun.mem_res], rfl, hs hw⟩⟩

theorem isWitness_atom_iff : IsWitness (atom b s) (witnessed (atom b s)) e ↔ e = refer b s := by
  rw [witnessed_atom]
  refine ⟨fun h ↦ PFun.ext fun w a ↦ ?_, fun h ↦ h ▸ isWitness_refer subset_rfl⟩
  rw [refer, PFun.mem_res]
  refine ⟨fun ha ↦ ⟨(h.rel ha).2, (h.rel ha).1.symm⟩, ?_⟩
  rintro ⟨hw, rfl⟩
  obtain ⟨c, hc, rfl, -⟩ := h.2 hw
  exact hc

theorem sat_refer_atom : sat (atom b t) (refer b s) = s ∩ t := by
  ext w
  simp only [sat, refer, PFun.mem_res, atom, Set.mem_ofPred_eq, Set.mem_inter_iff]
  aesop

-- the outputs of an antecedent at a one-individual predicate: Figures 5, 7, 8
theorem mem_dec_atom (hP : P.Introduces (atom b s) v A) :
    g ~[P.dec dc] h ↔ dc ⊆ A ∧ h = g[v ↦ refer b s] := by
  simp [hP.mem_dec, isWitness_atom_iff]

-- the outputs of an antecedent and a pronoun: Figures 6, 10
theorem mem_comp_atom {D : Update ((ℕ → (W →. E)))} (hP : P.Introduces (atom b s) v A) :
    g ~[P.dec dc ○ D] h ↔ dc ⊆ A ∧ g[v ↦ refer b s] ~[D] h := by
  simp [hP.mem_comp, isWitness_atom_iff]

theorem mem_comp_it_atom (hP : P.Introduces (atom b s) v A) :
    g ~[P.dec dc ○ (it (atom b t) v).dec dc'] h ↔ dc ⊆ A ∧ dc' ⊆ s ∩ t ∧ h = g[v ↦ refer b s] := by
  simp [mem_comp_atom hP, mem_dec_it, sat_refer_atom]

-- the outputs of a connective over an antecedent and a pronoun: Figure 9
theorem mem_dec_or_it_atom (hP : P.Introduces (atom b s) v A) :
    g ~[(P.or (it (atom b t) v)).dec dc] h ↔ dc ⊆ A ∪ s ∩ t ∧ h = g[v ↦ refer b s] := by
  simp [hP.hasTruthSet_or_it.mem_dec, hP.mem_connective_it, isWitness_atom_iff, sat_refer_atom,
    witnessed_atom_inf_atom]

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

theorem introduces_bathroom : (existential bathroom υ).Introduces bathroom υ {.wbu, .wb} := by
  simpa [witnessed_atom] using introduces_existential (R := bathroom) (v := υ)

theorem introduces_not_bathroom : (existential bathroom υ).not.Introduces bathroom υ {.wu, .w0} :=
  compl_bathroom_worlds ▸ introduces_bathroom.not

section M₁

variable {g h : ℕ → (World →. Ent)} {dc dc' s : Set World}

-- Table 1: assertion eliminates the commitment sets that are not subsets of the bathroom worlds
theorem mem_thereIs_bathroom :
    g ~[thereIs bathroom dc] h ↔ dc ⊆ {.wbu, .wb} ∧ h = g[υ ↦ bathroomRef] :=
  mem_dec_atom introduces_bathroom

-- Figure 5
theorem figure5 : IsGreatest {dc | g ∈ (thereIs bathroom dc).dom} {.wbu, .wb} :=
  isGreatest_of_forall_iff fun _ ↦ by simp [SetRel.mem_dom, mem_thereIs_bathroom]

-- Table 2: the pronoun eliminates further commitment sets
theorem mem_thereIs_comp_itIs_bathroom :
    g ~[thereIs bathroom dc ○ itIs upstairs dc] h ↔ dc ⊆ {.wbu} ∧ h = g[υ ↦ bathroomRef] := by
  rw [mem_comp_it_atom introduces_bathroom, bathroom_worlds_inter]
  exact ⟨fun ⟨_, h₂, h₃⟩ ↦ ⟨h₂, h₃⟩, fun ⟨h₂, h₃⟩ ↦ ⟨h₂.trans (by simp), h₂, h₃⟩⟩

-- Figure 6: pragmatic maximization is defeasible, since it applies to the whole discourse
theorem figure6 : IsGreatest {dc | g ∈ (thereIs bathroom dc ○ itIs upstairs dc).dom} {.wbu} :=
  isGreatest_of_forall_iff fun _ ↦ by
    simp only [SetRel.mem_dom, mem_thereIs_comp_itIs_bathroom]
    simp

-- (41), Figure 7: the prejacent's context is all and only the bathroom worlds, the first row of
-- Table 3
theorem mem_thereIsnt_bathroom :
    g ~[thereIsnt bathroom dc] h ↔ dc ⊆ {.wu, .w0} ∧ h = g[υ ↦ bathroomRef] :=
  mem_dec_atom introduces_not_bathroom

-- Figure 8
theorem mem_notThereIsnt_bathroom :
    g ~[notThereIsnt bathroom dc] h ↔ dc ⊆ {.wbu, .wb} ∧ h = g[υ ↦ bathroomRef] :=
  mem_dec_atom introduces_bathroom.not_not

-- Figure 9
theorem mem_thereIsntOr_bathroom :
    g ~[thereIsntOr bathroom upstairs dc] h ↔ dc ⊆ {.wbu, .wu, .w0} ∧ h = g[υ ↦ bathroomRef] := by
  have hT : ({.wu, .w0} ∪ {.wbu} : Set World) = {.wbu, .wu, .w0} := by
    ext w
    cases w <;> simp
  rw [thereIsntOr, mem_dec_or_it_atom introduces_not_bathroom, bathroom_worlds_inter, hT]

-- Figure 10: each interlocutor's commitments stay consistent, though they cannot overlap
theorem mem_disagree_bathroom :
    g ~[thereIsnt bathroom dc ○ itIs upstairs dc'] h ↔
      dc ⊆ {.wu, .w0} ∧ dc' ⊆ {.wbu} ∧ h = g[υ ↦ bathroomRef] := by
  rw [mem_comp_it_atom introduces_not_bathroom, bathroom_worlds_inter]

-- an indefinite outscoping negation has no output on the model
theorem not_mem_indefinite_not_it :
    (s, h) ∉ indefinite υ (commonNoun bathroom) (fun u ↦ (it upstairs u).not) g := fun hj ↦ by
  have := (eq_univ_of_mem_indefinite_not_it hj).2
  rw [witnessed_atom] at this
  simpa using this.ge (Set.mem_univ World.wu)

-- §3.2.1: under [stone-1999]'s update (26) is consistent, so the biconditional of (25) is crucial
theorem stone_admits_26 :
    g ∈ ((stoneExistential bathroom υ).not.dec {.wu} ○ itIs upstairs {.wu}).dom := by
  have hT := hasTruthSet_stoneExistential (R := bathroom) (v := υ)
  let e : World →. Ent := PFun.lift fun _ ↦ .b
  have hsat : witnessed bathroom ⊆ sat bathroom e := by
    rw [sat_lift_const, witnessed_atom]
    exact fun w hw ↦ ⟨rfl, hw⟩
  refine ⟨_, g[υ ↦ e], hT.not.mem_dec.mpr ⟨?_, ?_⟩, mem_dec_it.mpr ⟨?_, rfl⟩⟩
  · simp [witnessed_atom, compl_bathroom_worlds]
  · refine hT.mem_not.mpr ⟨rfl, e, fun w _ ↦ ?_, hsat, rfl⟩
    simp [e]
  · rintro w rfl
    simp [e, upstairs, atom]

end M₁

/-! ### The formulas as printed -/

section Registers

variable {W E : Type*}

/-- A propositional variable, the name of a propositional dref, which stores a local context. -/
structure PVar where
  /-- The index of the variable. -/
  idx : ℕ
  deriving DecidableEq, Repr

/-- The discourse state of the printed formulas assigns an individual concept to each individual
dref and a proposition to each propositional dref, so a variable update `[δ]` is
`Update.randomAssign` at either sort and a DRS `[δ | C]` is `Update.box {δ} C`. -/
@[ext] structure State (W E : Type*) where
  /-- The individual concept of an individual dref. -/
  indiv : ℕ → (W →. E)
  /-- The proposition of a propositional dref. -/
  prop : PVar → Set W

namespace State

/-- Reassign an individual dref. -/
@[simps] def updateIndiv (g : State W E) (v : ℕ) (e : W →. E) : State W E :=
  { g with indiv := Function.update g.indiv v e }

/-- Reassign a propositional dref. -/
@[simps] def updateProp (g : State W E) (p : PVar) (s : Set W) : State W E :=
  { g with prop := Function.update g.prop p s }

end State

/-- Individual drefs are registers holding individual concepts. -/
instance : RegisterStructure ℕ (State W E) (W →. E) where
  val v i := i.indiv v
  extend i v e := i.updateIndiv v e
  val_extend_self _ _ _ := by simp
  val_extend_of_ne _ _ _ _ h := by simp [Function.update_of_ne h]
  extend_eq_self _ _ := by simp [State.updateIndiv]
  extend_idem _ _ _ _ := by simp [State.updateIndiv]
  extend_comm _ _ _ h _ _ := by simp [State.updateIndiv, Function.update_comm h]

/-- Propositional drefs are registers holding propositions. -/
instance : RegisterStructure PVar (State W E) (Set W) where
  val p i := i.prop p
  extend i p s := i.updateProp p s
  val_extend_self _ _ _ := by simp
  val_extend_of_ne _ _ _ _ h := by simp [Function.update_of_ne h]
  extend_eq_self _ _ := by simp [State.updateProp]
  extend_idem _ _ _ _ := by simp [State.updateProp]
  extend_comm _ _ _ h _ _ := by simp [State.updateProp, Function.update_comm h]

variable {i j : State W E} {v u : ℕ} {φ φ' ψ : PVar}
@[simp] theorem extend_indiv (i : State W E) (v : ℕ) (e : W →. E) :
    RegisterStructure.extend i v e = i.updateIndiv v e := rfl

@[simp] theorem extend_prop (i : State W E) (p : PVar) (s : Set W) :
    RegisterStructure.extend i p s = i.updateProp p s := rfl

/-- The relative variable update `[φ : υ]` ([hofmann-2025] (25), App. B (9b)) updates `υ` so
that it has a referent at all and only the `φ`-worlds. -/
def relUpdate (φ : PVar) (v : ℕ) : Update (State W E) :=
  box {v} {j | j.prop φ = (j.indiv v).Dom}

theorem mem_relUpdate :
    i ~[relUpdate φ v] j ↔ i ~[randomAssign v] j ∧ j.prop φ = (j.indiv v).Dom :=
  mem_box_singleton

theorem fixes_relUpdate (ψ φ : PVar) (v : ℕ) : Fixes ψ (relUpdate (W := W) (E := E) φ v) :=
  fun _ _ h ↦ by
    obtain ⟨⟨e, rfl⟩, -⟩ := mem_relUpdate.mp h
    rfl

/-- Predication `R_φ(υ)` ([hofmann-2025] (27), App. B (7a)) holds if `R` holds of `υ`'s
referent at every world of the local context `φ`; ⋆ satisfies no relation. -/
def predication (R : E → W → Prop) (φ : PVar) (v : ℕ) : Condition (State W E) :=
  {i | i.prop φ ⊆ sat R (i.indiv v)}

/-- Inclusion `φ₁ ⋐ φ₂` (App. B (7c)). -/
def incl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ ⊆ i.prop φ₂}

/-- `φ₁ ≡ φ̄₂` (App. B (7b), (8a)), the condition negation places on its context. -/
def eqCompl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ = (i.prop φ₂)ᶜ}

@[simp] theorem mem_predication {R : E → W → Prop} :
    i ∈ predication R φ v ↔ i.prop φ ⊆ sat R (i.indiv v) := Iff.rfl

@[simp] theorem mem_incl : i ∈ incl φ φ' ↔ i.prop φ ⊆ i.prop φ' := Iff.rfl

@[simp] theorem mem_eqCompl : i ∈ eqCompl φ φ' ↔ i.prop φ = (i.prop φ')ᶜ := Iff.rfl

end Registers

section Printed

variable {h : ℕ → (World →. Ent)} {s : Set World}

/-- The registers of the printed formulas: the contexts of (41) and (30), and the commitment set. -/
def φ₁ : PVar := ⟨1⟩
@[inherit_doc φ₁] def φ₂ : PVar := ⟨2⟩
@[inherit_doc φ₁] def φ₃ : PVar := ⟨3⟩
@[inherit_doc φ₁] def φDC : PVar := ⟨10⟩

/-- (41) as printed, with the maximization (40) of App. B (10b). -/
def printed41 : Update (State World Ent) :=
  box {φ₁} (incl φDC φ₁) ○ maxAt φ₁ (box {φ₂} (eqCompl φ₁ φ₂) ○
    maxAt φ₂ (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ)))

/-- (30) with the maximization of App. C (19), as (48) prints it for `B`. -/
def printedIt : Update (State World Ent) :=
  box {φ₃} (incl φDC φ₃) ○ maxAt φ₃ (test (predication upstairs φ₃ υ))

private theorem fixes_body {r : PVar} : Fixes r (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ) :
    Update (State World Ent)) :=
  (fixes_relUpdate _ _ _).comp (Update.fixes_test _ _)

theorem printed41_eq : printed41 = box {φ₁} (incl φDC φ₁) ○ (box {φ₂} (eqCompl φ₁ φ₂) ○
    (relUpdate φ₂ υ ○ test (predication bathroom φ₂ υ))) := by
  rw [printed41, Update.maxAt_eq_of_fixes fixes_body, Update.maxAt_eq_of_fixes
    ((Update.fixes_box (by decide) _).comp fixes_body)]

-- Table 3: every value `s` of `φ₂` within the bathroom worlds gives an output of (41) as printed;
-- `mem_thereIsnt_bathroom` keeps only the first
theorem mem_printed41 {i : State World Ent} (hs : s ⊆ {.wbu, .wb}) (hdc : i.prop φDC ⊆ sᶜ) :
    i ~[printed41] ((i.updateProp φ₁ sᶜ).updateProp φ₂ s).updateIndiv υ (refer .b s) := by
  have hW := isWitness_refer (b := Ent.b) hs
  rw [printed41_eq, mem_box_singleton_comp]
  refine ⟨sᶜ, by simpa (decide := true) [incl] using hdc, mem_box_singleton_comp.mpr
    ⟨s, by simp (decide := true) [eqCompl], _, mem_relUpdate.mpr ⟨⟨_, rfl⟩, by simpa using hW.1⟩,
      rfl, ?_⟩⟩
  simpa using hW.2

-- the fragment's output for (41) is one of its outputs as printed, with Figure 7's contexts
theorem exists_mem_printed41 {i : State World Ent}
    (hj : i.indiv ~[thereIsnt bathroom (i.prop φDC)] h) :
    ∃ j, i ~[printed41] j ∧ j.indiv = h ∧ j.prop φ₁ = {.wu, .w0} ∧ j.prop φ₂ = {.wbu, .wb} := by
  obtain ⟨hA, rfl⟩ := mem_thereIsnt_bathroom.mp hj
  refine ⟨_, mem_printed41 subset_rfl (compl_bathroom_worlds ▸ hA), rfl, ?_, by simp⟩
  simp (decide := true) [compl_bathroom_worlds]

-- (35): pragmatic maximization as printed leaves an assertion unchanged, since it fixes `φDC`
theorem maxAt_printed41 : maxAt φDC printed41 = printed41 := by
  refine Update.maxAt_eq_of_fixes ?_
  rw [printed41_eq]
  exact (Update.fixes_box (by decide) _).comp
    ((Update.fixes_box (by decide) _).comp fixes_body)

-- §3.4.2: local entailment and consistency exclude (26) under (40) as printed
theorem eq_empty_of_mem_printed41_comp_printedIt {i j : State World Ent}
    (hj : i ~[printed41 ○ printedIt] j) : j.prop φDC = ∅ := by
  have h₃ : maxAt φ₃ (test (predication upstairs φ₃ υ)) =
      (test (predication upstairs φ₃ υ) : Update (State World Ent)) :=
    Update.maxAt_eq_of_fixes (Update.fixes_test _ _)
  rw [printed41_eq, printedIt, h₃] at hj
  obtain ⟨k, hk, hj⟩ := hj
  obtain ⟨s, hs, hk⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨t, ht, m, hm, rfl, -⟩ := mem_box_singleton_comp.mp hk
  obtain ⟨⟨e, rfl⟩, hd⟩ := mem_relUpdate.mp hm
  obtain ⟨u, hu, rfl, hsat⟩ := mem_box_singleton_comp.mp hj
  simp (decide := true) only [extend_prop, extend_indiv, mem_incl, mem_eqCompl, mem_predication,
    State.updateProp_prop, State.updateProp_indiv, State.updateIndiv_prop, State.updateIndiv_indiv,
    Function.update_self, ne_eq, Function.update_of_ne] at hs ht hu hsat hd ⊢
  refine Set.eq_empty_of_subset_empty fun w hw ↦ ?_
  have hc := ht ▸ hs hw
  exact hc (hd ▸ sat_subset_dom _ _ (hsat (hu hw)))

end Printed

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

theorem sat_refer_upstairs₃ :
    sat upstairs₃ (refer Ent.b {.wbus, .wbu, .wbs, .wb}) = {.wbus, .wbu} := by
  rw [sat_refer_atom]
  ext w
  cases w <;> simp

-- Figure 11
theorem mem_modalSub {g h : ℕ → (World₃ →. Ent)} {dc : Set World₃} :
    g ~[thereIsnt bathroom₃ dc ○ (believes .sue dox₃ upstairs₃ υ υ₂).dec dc] h ↔
      dc ⊆ {.wus, .ws} ∧
        h = g[υ ↦ refer .b {.wbus, .wbu, .wbs, .wb}][υ₂ ↦ PFun.lift fun _ ↦ .sue] := by
  have hT : {w | dox₃ .sue w ⊆ ({.wbus, .wbu} : Set World₃)} = {.wbus, .wbs, .wus, .ws} :=
    Set.ext fun w ↦ dox₃_subset_iff w
  have hI : ({.wus, .wu, .ws, .w0} ∩ {.wbus, .wbs, .wus, .ws} : Set World₃) = {.wus, .ws} := by
    ext w
    cases w <;> simp
  have hc : ({.wbus, .wbu, .wbs, .wb} : Set World₃)ᶜ = {.wus, .wu, .ws, .w0} := by
    ext w
    cases w <;> simp
  have hN := (introduces_existential (R := bathroom₃) (v := υ)).not
  rw [witnessed_atom, hc] at hN
  simp only [mem_comp_atom hN, mem_dec_believes (show υ ≠ υ₂ by decide), Function.update_self,
    sat_refer_upstairs₃, hT, ← and_assoc, ← Set.subset_inter_iff, hI]

/-! ### The judgments -/

section Rows

open Examples

variable (R S : E → W → Prop)

theorem rows_veridical (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex1a, ex18ac],
    ((Acceptable fun dc ↦ nullAssignment ∈ (thereIs R dc ○ itIs S dc).dom) ↔
      d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦
      mem_dom_comp_it_of_introduces introduces_existential).mpr h)
    (by revert d; decide)

theorem rows_negated : ∀ d ∈ [ex1b, ex6a, ex18bc, ex26],
    ((Acceptable fun dc ↦ nullAssignment ∈ (thereIsnt R dc ○ itIs S dc).dom) ↔
      d.judgment = .acceptable) := fun d hd ↦ by
  refine iff_of_false ?_ (by revert d; decide)
  rintro ⟨dc, hne, hj⟩
  exact hne.ne_empty (mem_dom_not_comp_it_self.mp hj)

theorem rows_doubleNeg (h : (witnessed (R ⊓ S)).Nonempty) : ∀ d ∈ [ex2a, ex9, ex42a],
    ((Acceptable fun dc ↦ nullAssignment ∈ (notThereIsnt R dc ○ itIs S dc).dom) ↔
      d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_not_not_comp_it).mpr h)
    (by revert d; decide)

theorem rows_bathDisj (h : ((witnessed R)ᶜ ∪ witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2b, ex10, ex42b],
    ((Acceptable fun dc ↦ nullAssignment ∈ (thereIsntOr R S dc).dom) ↔
      d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_or_not_it).mpr h)
    (by revert d; decide)

theorem rows_disagree (h : ((witnessed R)ᶜ).Nonempty) (h' : (witnessed (R ⊓ S)).Nonempty) :
    ∀ d ∈ [ex2c, ex12, ex42c],
    ((Acceptable fun dcA ↦ Acceptable fun dcB ↦
        nullAssignment ∈ (thereIsnt R dcA ○ itIs S dcB).dom) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ iff_of_true ⟨_, h, _, h', mem_dom_not_comp_it.mpr ⟨subset_rfl, subset_rfl⟩⟩
    (by revert d; decide)

-- (15), without its modal
theorem rows_15 (h : ((witnessed R)ᶜ).Nonempty) :
    ((Acceptable fun dc ↦ nullAssignment ∈ (thereIsnt R dc ○ (it S υ).not.dec dc).dom) ↔
      ex15.judgment = .acceptable) :=
  iff_of_true ((acceptable_iff_nonempty fun _ ↦ mem_dom_not_comp_not_it).mpr h) (by decide)

theorem rows_knows (a : E) (dox : E → W → Set W) :
    ((Acceptable fun dc ↦ nullAssignment ∈
        (thereIsnt R dc ○ (properName a υ₂ (Clause.knows dox (it S υ))).dec dc).dom) ↔
      ex13b.judgment = .acceptable) := by
  refine iff_of_false ?_ (by decide)
  rintro ⟨dc, hne, j, hj⟩
  exact hne.ne_empty (eq_empty_of_mem_not_comp_knows (by decide) hj)

-- §4.2.2: the semantics admits the unacceptable (45), whose second disjunct's context lies in the
-- first's; Hurford's constraint "might be viewed" as the pragmatic filter on it (p. 34)
theorem rows_45 (h : (witnessed R).Nonempty) :
    (Acceptable fun dc ↦ nullAssignment ∈ (((existential R υ).or (it S υ)).dec dc).dom) ∧
      (∀ (g h : ℕ → (W →. E)) dc, g ~[((existential R υ).or (it S υ)).dec dc] h →
        sat S (h υ) ⊆ witnessed R) ∧ ex45.judgment = .unacceptable :=
  ⟨(acceptable_iff_nonempty fun _ ↦ mem_dom_or_existential_it).mpr h,
    fun _ _ _ ↦ subset_of_mem_or_existential_it, rfl⟩

-- (6c) and (13a) are `Cole said` at the doxastic state `dox`, (49) and (51) Sue's
theorem rows_attitude (a : E) (dox : E → W → Set W)
    (h : ∃ e, IsWitness R (witnessed R) e ∧ ((witnessed R)ᶜ ∩ {w | dox a w ⊆ sat S e}).Nonempty) :
    ∀ d ∈ [ex6c, ex13a, ex49, ex51],
    ((Acceptable fun dc ↦ nullAssignment ∈
        (thereIsnt R dc ○ (believes a dox S υ υ₂).dec dc).dom) ↔ d.judgment = .acceptable) :=
  fun d hd ↦ by
    refine iff_of_true ?_ (by revert d; decide)
    obtain ⟨e, he, hne⟩ := h
    exact ⟨_, hne, (mem_dom_not_comp_believes (by decide)).mpr
      ⟨Set.inter_subset_left, e, he, Set.inter_subset_right⟩⟩

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
