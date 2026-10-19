module

public import Eval.Presupposition.Account
public import Studies.ChemlaSchlenker2012

/-!
# The map of projection accounts

The comparisons between the accounts of `Eval.Presupposition.Account` that the library proves. An
edge `(a, b)` says that `a` predicts presuppositions at least as strong as `b` (`edges`,
`edges_sound`); a cut `(a, b)` says that it does not, because some context accepts a formula by
`a` and rejects it by `b` (`cuts`, `cuts_sound`). Every edge and cut is a theorem about the
accounts' own definitions, taken from the study that proves it; a pair in neither list is open.

In the propositional fragment the incremental accounts coincide: dynamic semantics, filtering,
incremental Transparency, incremental local satisfaction, and incremental Kleene and supervaluation
acceptability are edges in both directions (Theorem 1, C.21 and C.22 of Local Contexts, and
Theorem 36 of its manuscript). Each incremental account is stronger than its symmetric counterpart
(item 20), and symmetric Kleene is stronger than symmetric supervaluation (Lemma 8). Symmetric
Transparency is incomparable with symmetric Kleene and supervaluation in one direction (Theorem
39a) and supervaluation is not stronger than Kleene (Lemma 11); the symmetric accounts are not
stronger than the incremental ones (Chemla and Schlenker's (13b)). Kalomoiros's Limited
Symmetry lies strictly between the two Transparencies: incremental Transparency is
stronger than it and it is stronger than symmetric Transparency, since the good finals it consults
shrink from the incremental theory's to the sentence itself; it is not stronger than incremental
Transparency (Fact 3.4.3), and symmetric Transparency is not stronger than it. Symmetric
supervaluation is not stronger than Limited Symmetry (Fact 3.4.1).

## References

* [schlenker-2009]
* [schlenker-2008b]
* [chemla-schlenker-2012]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Presupposition

open _root_.Presupposition Schlenker2009

namespace Account

/-! ### Edges -/

theorem dynamic_stronger_filtering : dynamic.Stronger filtering :=
  fun _ _ I _ _ h ↦ (Formula.admits_ccp_iff I).1 h

theorem filtering_stronger_dynamic : filtering.Stronger dynamic :=
  fun _ _ I _ _ h ↦ (Formula.admits_ccp_iff I).2 h

theorem transparencyIncremental_stronger_dynamic : transparencyIncremental.Stronger dynamic :=
  fun _ _ I C F h ↦ (transparency_incremental_iff_admits I C F).1 h

theorem dynamic_stronger_transparencyIncremental : dynamic.Stronger transparencyIncremental :=
  fun _ _ I C F h ↦ (transparency_incremental_iff_admits I C F).2 h

theorem satisfactionIncremental_stronger_transparencyIncremental :
    satisfactionIncremental.Stronger transparencyIncremental :=
  fun _ _ I C F h ↦ (satisfaction_iff_transparency I .incremental C F).1 h

theorem transparencyIncremental_stronger_satisfactionIncremental :
    transparencyIncremental.Stronger satisfactionIncremental :=
  fun _ _ I C F h ↦ (satisfaction_iff_transparency I .incremental C F).2 h

theorem satisfactionSymmetric_stronger_transparencySymmetric :
    satisfactionSymmetric.Stronger transparencySymmetric :=
  fun _ _ I C F h ↦ (satisfaction_iff_transparency I .symmetric C F).1 h

theorem transparencySymmetric_stronger_satisfactionSymmetric :
    transparencySymmetric.Stronger satisfactionSymmetric :=
  fun _ _ I C F h ↦ (satisfaction_iff_transparency I .symmetric C F).2 h

theorem kleeneIncremental_stronger_filtering : kleeneIncremental.Stronger filtering :=
  fun _ _ I C F h ↦ (strongKleeneAcceptable_incremental_iff I C F).1 h

theorem filtering_stronger_kleeneIncremental : filtering.Stronger kleeneIncremental :=
  fun _ _ I C F h ↦ (strongKleeneAcceptable_incremental_iff I C F).2 h

theorem supervaluationIncremental_stronger_filtering :
    supervaluationIncremental.Stronger filtering :=
  fun _ _ I C F h ↦ (supervaluationAcceptable_incremental_iff I C F).1 h

theorem filtering_stronger_supervaluationIncremental :
    filtering.Stronger supervaluationIncremental :=
  fun _ _ I C F h ↦ (supervaluationAcceptable_incremental_iff I C F).2 h

theorem transparencyIncremental_stronger_transparencySymmetric :
    transparencyIncremental.Stronger transparencySymmetric :=
  fun _ _ _ _ _ h ↦ h.symmetric

theorem satisfactionIncremental_stronger_satisfactionSymmetric :
    satisfactionIncremental.Stronger satisfactionSymmetric :=
  fun _ _ I _ _ h ↦ Satisfaction.symmetric I h

theorem kleeneIncremental_stronger_kleeneSymmetric :
    kleeneIncremental.Stronger kleeneSymmetric :=
  fun _ _ I _ _ h ↦ StrongKleeneAcceptable.symmetric I h

theorem supervaluationIncremental_stronger_supervaluationSymmetric :
    supervaluationIncremental.Stronger supervaluationSymmetric :=
  fun _ _ I _ _ h ↦ SupervaluationAcceptable.symmetric I h

theorem kleeneSymmetric_stronger_supervaluationSymmetric :
    kleeneSymmetric.Stronger supervaluationSymmetric :=
  fun _ _ I _ _ h ↦ StrongKleeneAcceptable.supervaluationAcceptable I h

/-- Limited Symmetry consults at each parsing point only incremental good finals. -/
theorem transparencyIncremental_stronger_limitedSymmetry :
    transparencyIncremental.Stronger limitedSymmetry :=
  fun _ _ _ _ _ h ↦ Kalomoiros2023.LimitedSymmetry.of_transparency h

/-- At its last parsing point Limited Symmetry consults the sentence itself. -/
theorem limitedSymmetry_stronger_transparencySymmetric :
    limitedSymmetry.Stronger transparencySymmetric :=
  fun _ _ _ _ _ h ↦ Kalomoiros2023.LimitedSymmetry.transparency h

/-! ### Cuts -/

/-- The context of Theorem 39a has a world where `p` and `q` fail and one where both hold. -/
private def interp39 : Fin 4 → Set Bool := fun a ↦ if a = 0 ∨ a = 2 then {true} else Set.univ

private theorem theorem39a :
    Transparency .symmetric {false, true}
        (Formula.occurrences interp39 (.bin .conj (.trigger 0 1) (.trigger 2 3))) ∧
      ¬ StrongKleeneAcceptable interp39 .symmetric {false, true}
        (.bin .conj (.trigger 0 1) (.trigger 2 3)) ∧
      ¬ SupervaluationAcceptable interp39 .symmetric {false, true}
        (.bin .conj (.trigger 0 1) (.trigger 2 3)) :=
  transparency_symmetric_not_strongKleeneAcceptable_not_supervaluationAcceptable interp39
    (by simp [interp39]) (by simp [interp39]) (by simp [interp39]) (by simp [interp39])

theorem not_transparencySymmetric_stronger_kleeneSymmetric :
    ¬ transparencySymmetric.Stronger kleeneSymmetric :=
  fun h ↦ theorem39a.2.1 (h _ _ interp39 _ _ theorem39a.1)

theorem not_transparencySymmetric_stronger_supervaluationSymmetric :
    ¬ transparencySymmetric.Stronger supervaluationSymmetric :=
  fun h ↦ theorem39a.2.2 (h _ _ interp39 _ _ theorem39a.1)

/-- By Lemma 11, `(pp' or (not pp'))` separates the two where `p` fails somewhere. -/
theorem not_supervaluationSymmetric_stronger_kleeneSymmetric :
    ¬ supervaluationSymmetric.Stronger kleeneSymmetric := by
  let I : Fin 2 → Set Bool := fun _ ↦ {true}
  have := supervaluationAcceptable_symmetric_not_strongKleeneAcceptable I (p := 0) (p' := 1)
    (w₀ := false) (by decide)
  exact fun h ↦ this.2 (h _ _ I _ _ this.1)

/-- The empty interpretation makes every atom false at the one world. -/
private def interpEmpty : Fin 3 → Set Unit := fun _ ↦ ∅

/-- [chemla-schlenker-2012]'s (13b), `qq' or (not p)`, where `p` and `q` fail. -/
private theorem inverseOr :
    SupervaluationAcceptable interpEmpty .symmetric {()}
        (ChemlaSchlenker2012.target 0 1 2 .orSentence .inverse) ∧ ¬ {()} ⊆ interpEmpty 1 :=
  ChemlaSchlenker2012.exists_supervaluationAcceptable_symmetric_inverse_not_subset interpEmpty
    .orSentence (by simp [interpEmpty]) (by simp [interpEmpty])

theorem not_supervaluationSymmetric_stronger_supervaluationIncremental :
    ¬ supervaluationSymmetric.Stronger supervaluationIncremental :=
  fun h ↦ inverseOr.2
    ((ChemlaSchlenker2012.supervaluationAcceptable_incremental_inverse interpEmpty .orSentence).1
      (h _ _ interpEmpty _ _ inverseOr.1))

theorem not_kleeneSymmetric_stronger_kleeneIncremental :
    ¬ kleeneSymmetric.Stronger kleeneIncremental := by
  have hK : StrongKleeneAcceptable interpEmpty .symmetric {()}
      (ChemlaSchlenker2012.target 0 1 2 .orSentence .inverse) :=
    (strongKleeneAcceptable_symmetric_iff interpEmpty _ _).2 fun w hw ↦
      (supervaluationDefined_iff_of_nodup interpEmpty
        (by simp [ChemlaSchlenker2012.target, Formula.triggers])).1
        ((supervaluationAcceptable_symmetric_iff interpEmpty _ _).1 inverseOr.1 w hw)
  exact fun h ↦ inverseOr.2
    ((ChemlaSchlenker2012.supervaluationAcceptable_incremental_inverse interpEmpty .orSentence).1
      ((strongKleeneAcceptable_iff_supervaluationAcceptable_incremental interpEmpty _ _).1
        (h _ _ interpEmpty _ _ hK)))

/-- By Fact 3.4.3, `(pp' or q)` separates the two where `p` fails and `q` holds. -/
theorem not_limitedSymmetry_stronger_transparencyIncremental :
    ¬ limitedSymmetry.Stronger transparencyIncremental := by
  let I : Fin 3 → Set Unit := fun a ↦ if a = 2 then Set.univ else ∅
  have hls : Kalomoiros2023.LimitedSymmetry Set.univ
      (Formula.occurrences I (.bin .disj (.trigger 0 1) (.atom 2))) :=
    (Kalomoiros2023.limitedSymmetry_or_left I).2 fun w _ hq ↦ absurd (by simp [I]) hq
  intro h
  have := (Formula.admits_ccp_iff I).1
    ((transparency_incremental_iff_admits I _ _).1 (h _ _ _ _ _ hls)) (Set.mem_univ ())
  simp [I, Formula.middleKleene, Formula.eval] at this

/-- By Fact 3.4.1, `(pp' and q)` separates the two where `p` and `q` fail. -/
theorem not_supervaluationSymmetric_stronger_limitedSymmetry :
    ¬ supervaluationSymmetric.Stronger limitedSymmetry := by
  let I : Fin 3 → Set Unit := fun _ ↦ ∅
  have hs : SupervaluationAcceptable I .symmetric Set.univ (.bin .conj (.trigger 0 1) (.atom 2)) :=
    (supervaluationAcceptable_symmetric_iff I _ _).2 fun w _ ↦
      (supervaluationDefined_iff_of_nodup I (by simp [Formula.triggers])).2
        (by simp [I, Formula.strongKleene, Formula.eval])
  intro h
  have := (Kalomoiros2023.limitedSymmetry_and_left I).1 (h _ _ _ _ _ hs) (Set.mem_univ ())
  simp [I] at this

/-- `(pp' and q)` separates the two where `p` and `q` fail: symmetric Transparency checks the
trigger against the false second conjunct and accepts, while Limited Symmetry checks it before. -/
theorem not_transparencySymmetric_stronger_limitedSymmetry :
    ¬ transparencySymmetric.Stronger limitedSymmetry := by
  let I : Fin 3 → Set Unit := fun _ ↦ ∅
  have ht : Transparency .symmetric Set.univ
      (Formula.occurrences I (.bin .conj (.trigger 0 1) (.atom 2))) :=
    (satisfaction_iff_transparency I .symmetric _ _).1
      ((satisfaction_symmetric_and_left_iff I).2 fun w _ ↦ by simp [I, Formula.truth, Connective.eval])
  intro h
  have := (Kalomoiros2023.limitedSymmetry_and_left I).1 (h _ _ _ _ _ ht) (Set.mem_univ ())
  simp [I] at this

end Account

open Account

/-- The comparisons the library proves, `(a, b)` when `a` is stronger than `b`. -/
def edges : List (Account × Account) :=
  [(dynamic, filtering), (filtering, dynamic),
    (transparencyIncremental, dynamic), (dynamic, transparencyIncremental),
    (satisfactionIncremental, transparencyIncremental),
    (transparencyIncremental, satisfactionIncremental),
    (satisfactionSymmetric, transparencySymmetric),
    (transparencySymmetric, satisfactionSymmetric),
    (kleeneIncremental, filtering), (filtering, kleeneIncremental),
    (supervaluationIncremental, filtering), (filtering, supervaluationIncremental),
    (transparencyIncremental, transparencySymmetric),
    (satisfactionIncremental, satisfactionSymmetric),
    (kleeneIncremental, kleeneSymmetric),
    (supervaluationIncremental, supervaluationSymmetric),
    (kleeneSymmetric, supervaluationSymmetric),
    (transparencyIncremental, limitedSymmetry), (limitedSymmetry, transparencySymmetric)]

theorem edges_sound : ∀ e ∈ edges, e.1.Stronger e.2 := by
  simp only [edges, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  exact ⟨dynamic_stronger_filtering, filtering_stronger_dynamic,
    transparencyIncremental_stronger_dynamic, dynamic_stronger_transparencyIncremental,
    satisfactionIncremental_stronger_transparencyIncremental,
    transparencyIncremental_stronger_satisfactionIncremental,
    satisfactionSymmetric_stronger_transparencySymmetric,
    transparencySymmetric_stronger_satisfactionSymmetric,
    kleeneIncremental_stronger_filtering, filtering_stronger_kleeneIncremental,
    supervaluationIncremental_stronger_filtering, filtering_stronger_supervaluationIncremental,
    transparencyIncremental_stronger_transparencySymmetric,
    satisfactionIncremental_stronger_satisfactionSymmetric,
    kleeneIncremental_stronger_kleeneSymmetric,
    supervaluationIncremental_stronger_supervaluationSymmetric,
    kleeneSymmetric_stronger_supervaluationSymmetric,
    transparencyIncremental_stronger_limitedSymmetry,
    limitedSymmetry_stronger_transparencySymmetric⟩

/-- The non-comparisons the library proves, `(a, b)` when `a` is not stronger than `b`. -/
def cuts : List (Account × Account) :=
  [(transparencySymmetric, kleeneSymmetric), (transparencySymmetric, supervaluationSymmetric),
    (supervaluationSymmetric, kleeneSymmetric),
    (supervaluationSymmetric, supervaluationIncremental), (kleeneSymmetric, kleeneIncremental),
    (limitedSymmetry, transparencyIncremental), (transparencySymmetric, limitedSymmetry),
    (supervaluationSymmetric, limitedSymmetry)]

theorem cuts_sound : ∀ c ∈ cuts, ¬ c.1.Stronger c.2 := by
  simp only [cuts, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  exact ⟨not_transparencySymmetric_stronger_kleeneSymmetric,
    not_transparencySymmetric_stronger_supervaluationSymmetric,
    not_supervaluationSymmetric_stronger_kleeneSymmetric,
    not_supervaluationSymmetric_stronger_supervaluationIncremental,
    not_kleeneSymmetric_stronger_kleeneIncremental,
    not_limitedSymmetry_stronger_transparencyIncremental,
    not_transparencySymmetric_stronger_limitedSymmetry,
    not_supervaluationSymmetric_stronger_limitedSymmetry⟩

end Eval.Presupposition
