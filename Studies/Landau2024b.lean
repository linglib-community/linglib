module

public import Linglib.Syntax.Minimalist.SyntacticObject.FormCopy
public import Linglib.Syntax.Control.Basic
public import Linglib.Fragments.Mixtec.SMPM.Pronouns
public import Linglib.Fragments.Mixtec.SMPM.Verbs
public import Studies.Landau2013
public import Linglib.Data.Examples.Landau2024b

/-!
# Landau (2024): Empirical challenges to the Form-Copy Theory of Control

Landau assesses the Form Copy theory of obligatory control of Chomsky and colleagues, on which
the controlled subject is a silent copy of the controller: the two are merged separately as
structurally identical inscriptions, and Form Copy relates them as copies under c-command
(`Minimalist.SyntacticObject.copyRel`), leaving the lower one unpronounced. So Form Copy silences
a lexical controllee (`naJuana_mem_copyRel`), but it relates only structurally identical
inscriptions and never makes a pronoun the copy of a lexical controller
(`pronoun_not_mem_copyRel`). Yet in Gã, Bùlì and San
Martín Peras Mixtec the controlled subject must be an overt pronoun.

Form Copy interprets copies alike, so the partial reading of a controlled subject is not one it
assigns (`not_isExhaustive_pcReading`). The theory derives partial control instead by deleting
the subject of a *for*-infinitive, an operation on pronunciation that leaves the readings of its
source in place. But the *for*-subject may exclude its antecedent and has a strict reading under
*only*, refuting both clauses of the signature of obligatory control, while the partially
controlled subject has neither (`profile_pro_ne_profile_forNP`); and *persuade* takes no
*for*-subject yet allows partial control (`exists_pro_without_forNP_source`). Nor can Form Copy
supply the partial reading itself: a partial reading of its relation needs a repetition
(`exists_isRepetition_of_isPartial`), which Internal Merge never leaves, so raising has none
(`not_isPartial_appearedToGather`). Form Copy would have to tell apart the derivations it is
blind to.

## Implementation notes

The controlled subject of (46c) is the feminine clitic of the San Martín Peras Mixtec fragment.
The semantic clause of Form Copy, copies interpreted in exactly the same way, is exhaustive
control over the copy relation (`Control.IsExhaustive`). The example rows are read as
diagnostics by `Landau2013.attests`: a reading on which the embedded subject
excludes its antecedent ((56), (57)) is a free reading, refuting co-dependence, and a strict
reading under *only* ((58), (59)) refutes variable binding. Every row with a silent subject is
partial control, which the paper marks by indexing the subject `i+`.

## TODO

The challenges from reconstruction (§3), from the optionality of Form Copy (§4), from control
into phases (§5) and from control across the passive (§6.1). The arguments of §4 and §5 turn on
the co-phasehood condition on Form Copy, which `copyRel` omits. In §7, the rarity of *for*-subjects
across languages ((53)) and the collective plurality of the partially controlled subject
((54), (55)).

## References

* [landau-2024b]
* [chomsky-etal-2023]
* [landau-2013]
-/

@[expose] public section

namespace Landau2024b

open Minimalist SyntacticObject Control

/-! ### Controlled pronouns (46) -/

/-- *ña Juana*, the controller of (46c). -/
noncomputable def naJuana : SyntacticObject :=
  merge (leaf ⟨.of .D [.N] "ña", 0⟩) (leaf ⟨.of .N [] "Juana", 1⟩)

/-- *ña Juana* from fresh tokens, the controlled subject of (46c) on the Form Copy theory. -/
noncomputable def naJuana' : SyntacticObject := naJuana.renumber 2

/-- (46c) as the Form Copy theory builds it, *ña Juana* merged into the theta positions of
*nantǒso* 'forget', the fragment's entry (Landau prints *nàntŏso*), and *nakatsya* 'wash'. -/
noncomputable def forgotToWash : SyntacticObject :=
  merge naJuana (merge (leaf ⟨.of .V [.V] Mixtec.SMPM.forget.form, 4⟩)
    (merge naJuana' (leaf ⟨.of .V [] "nakatsya míí tsyàà", 5⟩)))

/-- Form Copy relates a lexical controllee to its controller, so the controllee goes unpronounced.
The theory thus derives the silent controlled subject that (46c) stars. -/
theorem naJuana_mem_copyRel : (naJuana, naJuana') ∈ forgotToWash.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains])
    (structurallyIdentical_renumber 2 naJuana)

/-- The controlled subject of (46c), the feminine clitic *=ñá*. -/
def nya : SyntacticObject := leaf ⟨.of .D [] (Mixtec.SMPM.cl3 .feminine).form, 6⟩

/-- The pronoun that (46c) requires is a copy of its controller in no object, since the two are
not structurally identical. -/
theorem pronoun_not_mem_copyRel (s : SyntacticObject) : (naJuana, nya) ∉ s.copyRel :=
  fun h ↦ by simpa [naJuana, nya] using h.2.numNodes_eq

/-! ### Partial control by Form Copy (§7) -/

/-- *John*, the controller of (48a). -/
def john : SyntacticObject := leaf ⟨.of .N [] "John", 0⟩

/-- *John* from a fresh token, the controlled subject of (48a) on the Form Copy theory. -/
def john' : SyntacticObject := john.renumber 3

/-- (48a) *John arranged to meet at noon*, the controller and the controlled subject merged
separately into the theta positions of *arranged* and *meet*. -/
noncomputable def arrangedToMeet : SyntacticObject :=
  merge john (merge (leaf ⟨.of .V [.T] "arranged", 1⟩) (merge (leaf ⟨.of .T [.V] "to", 2⟩)
    (merge john' (leaf ⟨.of .V [] "meet at noon", 4⟩))))

/-- Form Copy relates the controller of (48a) to its controlled subject. -/
theorem john_mem_copyRel : (john, john') ∈ arrangedToMeet.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains])
    (structurallyIdentical_renumber 3 john)

/-- The partial reading of (48a), on which the controlled subject denotes a group of John, `0`,
and an associate, `1`. -/
def pcReading (x : SyntacticObject) : Set ℕ := if x = john' then {0, 1} else {0}

/-- The partial reading is partial on the copy relation, since the controlled subject's group
strictly contains John. -/
theorem isPartial_pcReading : IsPartial pcReading arrangedToMeet.copyRel :=
  ⟨john, john', john_mem_copyRel, by
    have hne : john ≠ john' := by simp [john, john', renumber]
    simp only [pcReading, hne, ↓reduceIte]
    exact (Set.ssubset_iff_of_subset (by simp)).2 ⟨1, by simp, by simp⟩⟩

/-- So it is no interpretation Form Copy assigns, which gives copies one value. -/
theorem not_isExhaustive_pcReading : ¬ IsExhaustive pcReading arrangedToMeet.copyRel :=
  fun h ↦ h.not_isPartial isPartial_pcReading

/-- A partial reading of Form Copy's relation lives on a repetition. The copy Internal Merge
leaves is one object at two positions, which no valuation splits. -/
theorem exists_isRepetition_of_isPartial {Ref : Type*} [Preorder Ref]
    {val : SyntacticObject → Ref} {s : SyntacticObject} (h : IsPartial val s.copyRel) :
    ∃ x y, (x, y) ∈ s.copyRel ∧ IsRepetition x y ∧ val x < val y :=
  let ⟨x, y, hxy, hlt⟩ := h
  ⟨x, y, hxy, ⟨hxy.2, ne_of_apply_ne val hlt.ne⟩, hlt⟩

/-- *the chair*, raised in Landau's example of the missing partial raising. -/
def chair : SyntacticObject := leaf ⟨.of .D [] "the chair", 0⟩

/-- *The chair appeared to be gathering*, the raised subject left as its own copy by Internal
Merge. -/
noncomputable def appearedToGather : SyntacticObject :=
  merge chair (merge (leaf ⟨.of .V [.T] "appeared", 1⟩) (merge (leaf ⟨.of .T [.V] "to", 2⟩)
    (merge chair (leaf ⟨.of .V [] "be gathering", 3⟩))))

/-- Form Copy relates the raised subject to its Internal Merge copy. -/
theorem chair_mem_copyRel : (chair, chair) ∈ appearedToGather.copyRel :=
  self_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains])

/-- Distinct tokens of `appearedToGather` inscribe distinct items. -/
theorem hasDistinctItems_appearedToGather : appearedToGather.HasDistinctItems := by
  intro a b ha hb hab
  simp only [appearedToGather, chair, terms_merge, terms_leaf, Multiset.mem_cons, Multiset.mem_add,
    Multiset.mem_singleton, leaf_inj, leaf_ne_merge, traceOf_ne_merge, traceOf_ne_leaf, false_or,
    or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | simp [LexicalItem.of] at hab

/-- So every valuation interprets the copies of `appearedToGather` alike: on a raising structure
the semantic clause of Form Copy holds for free. -/
theorem isExhaustive_appearedToGather {Ref : Type*} (val : SyntacticObject → Ref) :
    IsExhaustive val appearedToGather.copyRel :=
  .of_subset_id (copyRel_subset_id hasDistinctItems_appearedToGather)

/-- There is no partial raising. -/
theorem not_isPartial_appearedToGather {Ref : Type*} [Preorder Ref]
    (val : SyntacticObject → Ref) : ¬ IsPartial val appearedToGather.copyRel :=
  (isExhaustive_appearedToGather val).not_isPartial

/-! ### Partial control by deletion of a *for*-subject (§7) -/

/-- The subject of an infinitive in the rows, a silent controlled subject or the subject of a
*for*-infinitive. -/
inductive Subject where
  | pro
  | forNP
  deriving DecidableEq, Repr

/-- The subject of a row's infinitive. -/
def subjectOf (row : Datum) : Option Subject :=
  row.parse? "embeddedSubject" [("PRO", .pro), ("for", .forNP)]

/-- The diagnostics the rows attest for a kind of subject. -/
def attested (s : Subject) : Set Diagnostic :=
  {d | ∃ row ∈ Examples.all, subjectOf row = some s ∧ Landau2013.attests row d}

instance (s : Subject) : DecidablePred (· ∈ attested s) := fun d ↦ by
  unfold attested; infer_instance

/-- The profile of a kind of subject in the signature of obligatory control, the clauses no
attested diagnostic refutes. -/
def profile (s : Subject) : Set Landau2013.Clause74 := ofAttested (attested s)

/-- The partially controlled subject attests no diagnostic ((56b), (57d), (58b), (59b)), so it is
obligatory control. -/
theorem profile_pro_eq_univ : profile .pro = Set.univ :=
  ofAttested_eq_univ_iff.2 <| Set.eq_empty_iff_forall_notMem.2 <| by decide +kernel

/-- The *for*-subject has a free reading ((56a), (57c)) and a strict reading under *only* ((58a),
(59a)), refuting both clauses. -/
theorem profile_forNP_eq_empty : profile .forNP = ∅ :=
  ofAttested_eq_empty_iff.2 <| by decide +kernel

/-- Deleting the *for*-subject leaves the readings of the source in place, so the Form Copy theory
predicts partial control to have the profile of its source. It does not. -/
theorem profile_pro_ne_profile_forNP : profile .pro ≠ profile .forNP := by
  rw [profile_pro_eq_univ, profile_forNP_eq_empty]
  exact (Set.nonempty_of_mem (Set.mem_univ Landau2013.Clause74.codependent)).ne_empty

/-- Partial control without a *for*-subject source: (52c) under *persuade*, which takes no
*for*-subject ((15a), (15b)). -/
theorem exists_pro_without_forNP_source :
    ∃ row ∈ Examples.all, subjectOf row = some .pro ∧ row.judgment = .acceptable ∧
      ∀ src ∈ Examples.all, src.feature? "verb" = row.feature? "verb" →
        subjectOf src = some .forNP → src.judgment = .ungrammatical := by
  decide +kernel

end Landau2024b
