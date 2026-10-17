module

public import Linglib.Semantics.Presupposition.SyntacticEnvironment
public import Linglib.Semantics.Presupposition.QuantifiedClause
public import Studies.Heim1983
public import Studies.Heim1992

/-!
# Schlenker (2009): Local Contexts

A restriction on the denotation of an expression is transparent in a syntactic environment, relative
to a context set, when conjoining it to any denotation of the expression's type changes the truth
value at no world of the context. The local context of the expression is the least transparent
restriction, and a presupposition is satisfied when its local context entails it. Each theory has
two readings (`Reading`): the incremental reading consults every good final of the string up to the
expression, the first parse point, and the symmetric reading only the sentence itself, the last
(`Reading.parsePoint`). Transparency and local satisfaction check each trigger's presupposition at
that parse point (`Transparency`, `Satisfaction`, over the occurrences of
`Presupposition.Occurrence`, for formulas and quantified clauses alike), and Strong Kleene and
supervaluation acceptability check the definedness of the sentences the reading completes with its
finals (`Reading.Finals`, `Reading.completions`). This file covers the propositional fragment of the
paper's language after its Appendix C, its quantified clauses, the belief reports of its third
section, and the comparison with supervaluations and Strong Kleene logic in the appendix of
Schlenker's 2008 manuscript, which the published appendix shortens.

## Main statements

* `isLocalContext_incremental`: the incremental local context of every position is Karttunen's,
  the global context except in a second argument, which takes the context updated with the first
  argument, or with its negation in a disjunction.
* `satisfaction_iff_transparency`, `satisfaction_incremental_iff_admits`: satisfaction in the
  local context is Transparency on either reading, and on the incremental one it is admittance by
  Heim's context change potentials with Beaver's disjunction.
* `isLocalContext_believe`, `satisfied_believe_iff_admits`: the local context of the complement of
  *believe* pairs each world of the context with the worlds compatible with the agent's beliefs
  there, and it entails a presupposition iff the context admits the report under Heim's belief
  rule.
* `kleeneAcceptable_iff_superAcceptable_incremental`, `Transparency.kleeneAcceptable`,
  `transparency_symmetric_not_kleeneAcceptable_not_superAcceptable`: on the incremental reading
  Kleene and supervaluation acceptability coincide and follow from Transparency, and on the
  symmetric reading Transparency accepts a sentence that both reject.
* `transparent_scope_iff_universal`, `not_exists_isLocalContext_infinitelyMany`,
  `transparentAt_not_transparent_no`: in a quantified sentence Transparency gives universal
  projection under Non-Triviality, the scope of *infinitely many* has no local context, and with
  *no* Strong Kleene accepts a sentence that Transparency rejects.
* `QuantifiedClause.kleeneAcceptable_trigger_iff`: a clause with a final trigger is Kleene
  acceptable iff the trigger is transparent at its assertion.

## Implementation notes

* The gap's denotation ranges over all propositions, where the paper quantifies over the
  expressions that may fill the gap and assumes that every proposition is denoted.
* The continuations a theory consults at a gap are the functions from the gap's truth set to the
  sentence's. For the first argument of a conjunction or a disjunction the connective follows the
  gap in the string and is itself free. The finals the trivalent theories complete a sentence with
  carry no trigger after the gap (items 26a, 29a).
* A trigger whose presupposition fails at a world may be resolved either way (`resolve`).
  Supervaluation resolves all tokens of a trigger alike (`SuperDefined`) and Kleene each token
  separately (`TokenDefined`), which `tokenDefined_iff` shows is the Strong Kleene evaluation. On
  the symmetric reading both evaluate the sentence itself (`kleeneAcceptable_symmetric_iff`,
  `superAcceptable_symmetric_iff`, items 26b and 29b).
* The incremental Kleene and supervaluation results are proved by reducing acceptability to
  entailment of the filtering presupposition (`kleeneAcceptable_incremental_iff`,
  `superAcceptable_incremental_iff`), not by the manuscript's induction on the number of triggers.
* In a quantified clause the continuations at the first parse point after a restrictor are every
  predicate, by Expressivity, while the clauses Kleene and supervaluation acceptability evaluate
  take formula scopes, which a token resolution needs.

## TODO

* Theorem 2 of C.9 is formalized for a single quantified clause, against the universal
  presupposition rather than a dynamic semantics for quantifiers, which linglib does not define.
  The conditions on quantificational clauses and domains in the equivalence with dynamic semantics
  hold trivially in the propositional fragment and are omitted there.

## References

* [schlenker-2009]
* [schlenker-2008b]
* [karttunen-1974-presupposition]
* [heim-1983]
* [beaver-2001]
* [heim-1992]
-/

@[expose] public section

namespace Schlenker2009

open Presupposition Heim1983 DynamicSemantics

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### Transparency and local satisfaction -/

/-- The two readings of a theory of projection: the incremental reading consults every good final
of the string up to an expression, and the symmetric reading only the sentence itself (C.8). -/
inductive Reading where
  | incremental
  | symmetric
  deriving DecidableEq

/-- The parse point a reading consults: the first, where every good final is consulted, or the
last, where only the sentence itself is. -/
def Reading.parsePoint : Reading → ℕ∞
  | .incremental => 0
  | .symmetric => ⊤

/-- The finals the trivalent theories complete a sentence with at the gap of `K`: on the
incremental reading each good final without triggers (items 26a, 29a), on the symmetric reading
`K` itself. -/
def Reading.Finals : Reading → SyntacticEnvironment Atom → SyntacticEnvironment Atom → Prop
  | .incremental, K, K' => K.SameInitialString K' ∧ K'.TriggerFreeFinal
  | .symmetric, K, K' => K' = K

section Occurrences

variable {α : Type*} [SemilatticeInf α] {C : Set W} {os : List (Occurrence W α)}

/-- Transparency on a reading: at every trigger the presupposition is transparent at the parse
point the reading consults (C.8). -/
def Transparency (r : Reading) (C : Set W) (os : List (Occurrence W α)) : Prop :=
  ∀ o ∈ os, o.Transparent r.parsePoint C

/-- Local satisfaction on a reading: at every trigger the local context at the parse point the
reading consults entails the presupposition (C.17). -/
def Satisfaction (r : Reading) (C : Set W) (os : List (Occurrence W α)) : Prop :=
  ∀ o ∈ os, o.Satisfied r.parsePoint C

/-- Incremental Transparency implies symmetric Transparency, since the last parse point consults
fewer continuations (C.20). -/
theorem Transparency.symmetric (h : Transparency .incremental C os) :
    Transparency .symmetric C os :=
  fun o ho ↦ (h o ho).mono le_top

theorem Satisfaction.transparency {r : Reading} (h : Satisfaction r C os) : Transparency r C os :=
  fun o ho ↦ (h o ho).transparent

end Occurrences

/-! ### Local contexts in the propositional fragment -/

/-- The incremental local context of any gap is [karttunen-1974-presupposition]'s (C.16 with
§2.3). -/
theorem isLocalContext_incremental [Nonempty Atom] (K : SyntacticEnvironment Atom) (C : Set W) :
    IsLocalContext C (K.parsePoint I 0) (K.localContext I C) := by
  have h := isLocalContext_of_isTruthFunctional (C := C) (env := K.parsePoint I 0)
    fun _ hf ↦ SyntacticEnvironment.isTruthFunctional_of_mem_parsePoint I hf
  rwa [show {w | ∃ f ∈ K.parsePoint I 0, DependsAt f w} = K.localContext I Set.univ from
    Set.ext fun w ↦ by
      rw [SyntacticEnvironment.parsePoint_zero]
      exact Set.exists_mem_image.trans (SyntacticEnvironment.exists_dependsAt_iff I K w),
    ← SyntacticEnvironment.localContext_eq_inter] at h

/-- The first argument of a connective takes the global context, (18) and (27). -/
theorem isLocalContext_left [Nonempty Atom] (c : Connective) (G : Formula Atom) (C : Set W) :
    IsLocalContext C (SyntacticEnvironment.parsePoint I 0 [.left c G]) C :=
  isLocalContext_incremental I _ C

/-- Negation is a hole, (21). -/
theorem isLocalContext_not [Nonempty Atom] (C : Set W) :
    IsLocalContext C
      (SyntacticEnvironment.parsePoint I 0 [(.not : SyntacticEnvironment.Step Atom)]) C :=
  isLocalContext_incremental I _ C

/-- The second argument of a conjunction or a conditional takes the context updated with the first,
the second disjunct the context updated with the first's negation, (24), (30) and (33). -/
theorem isLocalContext_right [Nonempty Atom] (c : Connective) (F : Formula Atom) (C : Set W) :
    IsLocalContext C (SyntacticEnvironment.parsePoint I 0 [.right c F])
      (c.localContext C (F.truth I)) :=
  isLocalContext_incremental I _ C

/-- The symmetric local context of any gap is the worlds of the context at which the truth value
of the actual sentence depends on the gap. -/
theorem isLocalContext_symmetric (K : SyntacticEnvironment Atom) (C : Set W) :
    IsLocalContext C (K.parsePoint I ⊤) (C ∩ {w | DependsAt (K.truth I) w}) := by
  simpa using isLocalContext_of_isTruthFunctional (C := C) fun _ hf ↦
    SyntacticEnvironment.isTruthFunctional_of_mem_parsePoint I (n := ⊤) hf

/-! ### Transparency, satisfaction and dynamic semantics -/

/-- Local satisfaction is Transparency, on either reading (C.21). -/
theorem satisfaction_iff_transparency (r : Reading) (C : Set W) (F : Formula Atom) :
    Satisfaction r C (Occurrence.ofFormula I F) ↔ Transparency r C (Occurrence.ofFormula I F) := by
  simp only [Satisfaction, Transparency, Occurrence.forall_mem_ofFormula]
  exact forall₂_congr fun _ _ ↦ satisfied_iff_transparent
    (fun _ hf ↦ SyntacticEnvironment.isTruthFunctional_of_mem_parsePoint I hf) _

/-- Incremental satisfaction predicts presuppositions at least as strong as symmetric satisfaction
(C.20). -/
theorem Satisfaction.symmetric {C : Set W} {F : Formula Atom}
    (h : Satisfaction .incremental C (Occurrence.ofFormula I F)) :
    Satisfaction .symmetric C (Occurrence.ofFormula I F) :=
  (satisfaction_iff_transparency I _ C F).2
    ((satisfaction_iff_transparency I _ C F).1 h).symmetric

/-- Incremental Transparency is admittance by the formula's context change potential, which updates
the context to its worlds at which the formula is true (`Formula.ccp_get`; Theorem 1 of C.9). -/
theorem transparency_incremental_iff_admits (C : Set W) (F : Formula Atom) :
    Transparency .incremental C (Occurrence.ofFormula I F) ↔ (F.ccp I).Admits C := by
  rw [Formula.admits_ccp_iff, Transparency, Occurrence.forall_mem_ofFormula]
  have henv {K : SyntacticEnvironment Atom} : ∀ f ∈ K.parsePoint I 0, IsTruthFunctional f :=
    fun _ hf ↦ SyntacticEnvironment.isTruthFunctional_of_mem_parsePoint I hf
  have hdep [Nonempty Atom] (K : SyntacticEnvironment Atom) (w : W) :
      (∃ f ∈ K.parsePoint I 0, DependsAt f w) ↔ w ∈ K.localContext I Set.univ := by
    rw [SyntacticEnvironment.parsePoint_zero]
    exact Set.exists_mem_image.trans (SyntacticEnvironment.exists_dependsAt_iff I K w)
  refine ⟨fun h w hw ↦ (Formula.filter_ne_zero_iff I F w).2 fun o ho hl ↦ ?_,
    fun h o ho ↦ (transparent_iff_subset henv).2 fun w ⟨hw, hl⟩ ↦ ?_⟩
  · have : Nonempty Atom := ⟨o.2.1⟩
    exact (transparent_iff_subset henv).1 (h o ho) ⟨hw, (hdep o.1 w).2 hl⟩
  · have : Nonempty Atom := ⟨o.2.1⟩
    exact (Formula.filter_ne_zero_iff I F w).1 (h hw) o ho ((hdep o.1 w).1 hl)

/-- Incremental satisfaction is admittance by the formula's context change potential (C.22). -/
theorem satisfaction_incremental_iff_admits (C : Set W) (F : Formula Atom) :
    Satisfaction .incremental C (Occurrence.ofFormula I F) ↔ (F.ccp I).Admits C :=
  (satisfaction_iff_transparency I _ C F).trans (transparency_incremental_iff_admits I C F)

/-- Symmetric satisfaction requires each trigger's presupposition at the worlds of the context
at which the truth value of the sentence depends on the trigger. -/
theorem satisfaction_symmetric_iff (C : Set W) (F : Formula Atom) :
    Satisfaction .symmetric C (Occurrence.ofFormula I F) ↔
      ∀ o ∈ F.occurrences, C ∩ {w | DependsAt (o.1.truth I) w} ⊆ I o.2.1 := by
  rw [Satisfaction, Occurrence.forall_mem_ofFormula]
  exact forall₂_congr fun o _ ↦ satisfied_iff (isLocalContext_symmetric I o.1 C) _

/-! ### Examples (§2.3) -/

variable {p p' q q' : Atom} {C : Set W}

/-- On the incremental theory `(pp' and q)` and `(pp' or q)` presuppose `p`, (20). -/
theorem satisfaction_incremental_initial_iff {c : Connective} (hc : c ≠ .cond) :
    Satisfaction .incremental C (Occurrence.ofFormula I (.bin c (.trigger p p') (.atom q))) ↔
      C ⊆ I p := by
  rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
  cases c <;> simp_all [Set.subset_def, Formula.filter, Formula.eval]

/-- On the incremental theory `(not pp')` presupposes `p`, (23). -/
theorem satisfaction_incremental_not_iff :
    Satisfaction .incremental C (Occurrence.ofFormula I (.not (.trigger p p'))) ↔ C ⊆ I p := by
  rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.eval]

/-- On the incremental theory `(if pp' . q)` presupposes `p`, (29). -/
theorem satisfaction_incremental_if_iff :
    Satisfaction .incremental C (Occurrence.ofFormula I (.bin .cond (.trigger p p') (.atom q))) ↔
      C ⊆ I p := by
  rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.eval]

/-- On the incremental theory `(if p . qq')` presupposes `(if p . q)`, (32). -/
theorem satisfaction_incremental_then_iff :
    Satisfaction .incremental C (Occurrence.ofFormula I (.bin .cond (.atom p) (.trigger q q'))) ↔
      C ⊆ (Formula.bin .cond (.atom p) (.atom q)).truth I := by
  rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
  simp [Set.subset_def, Formula.filter, Formula.truth, Formula.eval, Connective.eval]

/-! ### A trigger alone, and conjunction on both readings -/

/-- A trigger standing alone presupposes `p` on either reading. -/
theorem satisfaction_trigger_iff (r : Reading) :
    Satisfaction r C (Occurrence.ofFormula I (.trigger p p')) ↔ C ⊆ I p := by
  cases r
  · rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
    simp [Set.subset_def, Formula.filter, Formula.eval]
  · simp [satisfaction_symmetric_iff, Formula.occurrences, SyntacticEnvironment.truth, DependsAt]

/-- `(q and pp')` presupposes `(if q . p)` on either reading, (26). -/
theorem satisfaction_and_right_iff (r : Reading) :
    Satisfaction r C (Occurrence.ofFormula I (.bin .conj (.atom q) (.trigger p p'))) ↔
      C ⊆ (Formula.bin .cond (.atom q) (.atom p)).truth I := by
  cases r
  · rw [satisfaction_incremental_iff_admits, Formula.admits_ccp_iff]
    simp [Set.subset_def, Formula.filter, Formula.truth, Formula.eval, Connective.eval]
  · simp [satisfaction_symmetric_iff, Formula.occurrences, SyntacticEnvironment.truth,
      SyntacticEnvironment.Step.truth, DependsAt, Connective.eval, Formula.truth, Set.subset_def]

/-- On the symmetric theory `(pp' and q)` presupposes `(if q . p)`, since the local context of a
conjunct is the context updated with the other conjunct, whichever comes first. -/
theorem satisfaction_symmetric_and_left_iff :
    Satisfaction .symmetric C (Occurrence.ofFormula I (.bin .conj (.trigger p p') (.atom q))) ↔
      C ⊆ (Formula.bin .cond (.atom q) (.atom p)).truth I := by
  simp [satisfaction_symmetric_iff, Formula.occurrences, SyntacticEnvironment.truth,
    SyntacticEnvironment.Step.truth, DependsAt, Connective.eval, Formula.truth, Set.subset_def]

/-! ### Belief reports (§3.1.2) -/

section Belief

variable (Dox : W → Set W) {C : Set W}

/-- The meaning of `(believe _)` on two-dimensional denotations, sets of pairs of an utterance world
and a world of evaluation. The report holds at the utterance world when the complement holds at
every world compatible with the agent's beliefs there, (51). -/
def believe : Set (Set (W × W) → Set W) :=
  {fun d ↦ {w₀ | ∀ w ∈ Dox w₀, (w₀, w) ∈ d}}

/-- The local context of the complement of *believe* pairs each utterance world of the context with
the worlds compatible with the agent's beliefs there, (52). -/
theorem isLocalContext_believe :
    IsLocalContext C (believe Dox) {q | q.1 ∈ C ∧ q.2 ∈ Dox q.1} := by
  constructor
  · rintro _ rfl d w₀ hw₀
    exact ⟨fun h w hw ↦ (h w hw).2, fun h w hw ↦ ⟨⟨hw₀, hw⟩, h w hw⟩⟩
  · rintro x hx ⟨w₀, w⟩ ⟨hw₀, hw⟩
    exact ((hx _ rfl Set.univ w₀ hw₀).2 fun _ _ ↦ trivial) w hw |>.1

/-- The worlds of evaluation of the local context of the complement of *believe* are the image of
the context under the doxastic accessibility, the worlds compatible with the agent's beliefs at some
world of the context. -/
theorem image_snd_localContext_believe :
    Prod.snd '' {q : W × W | q.1 ∈ C ∧ q.2 ∈ Dox q.1} = (SetRel.ofSuccessors Dox).image C := by
  ext; simp [and_comm]

/-- A presupposition about the world of evaluation is satisfied in the complement of *believe* iff
every world compatible with the agent's beliefs at a world of the context satisfies it (p. 3:32). -/
theorem satisfied_believe_iff {P : Set W} :
    Satisfied C (believe Dox) (Prod.snd ⁻¹' P) ↔ (SetRel.ofSuccessors Dox).image C ⊆ P := by
  rw [satisfied_iff (isLocalContext_believe Dox), ← Set.image_subset_iff,
    image_snd_localContext_believe]

end Belief

/-- The complement's presupposition is satisfied in the complement of *believe* iff the context
admits the report under rule (18) of [heim-1992], which the paper calls the standard result obtained
in Heim's framework (p. 3:32). -/
theorem satisfied_believe_iff_admits {E : Type*} (Dox : E → W → Set W) (a : E)
    (p : W → SignType) {C : Set W} :
    Satisfied C (believe (Dox a)) (Prod.snd ⁻¹' Function.support p) ↔
      (Heim1992.believes Dox a (CCP.Partial.ofTrivalent p)).Admits C := by
  rw [satisfied_believe_iff, Heim1992.admits_believes_iff]

/-! ### The King conditional ([heim-1983]) -/

variable {king son bald : W → Prop}

/-- For *if the king has a son, the king's son is bald*, incremental satisfaction is admittance by
Heim's context change potential, both holding iff the context entails a king. -/
theorem satisfaction_incremental_king_iff_admits {k s ks b : Atom} (hk : I k = {w | king w})
    (hs : I s = {w | son w}) (hks : I ks = {w | king w ∧ son w}) (C : Set W) :
    Satisfaction .incremental C
        (Occurrence.ofFormula I (.bin .cond (.trigger k s) (.trigger ks b))) ↔
      (ifKingHasSon king son bald).Admits C := by
  rw [satisfaction_incremental_iff_admits, king_admits_iff, Formula.admits_ccp_iff]
  simp [Formula.filter, Formula.eval, hk, hs, hks, Set.subset_def]

/-! ### Strong Kleene and supervaluations (items 24–41 of [schlenker-2008b]) -/

section Trivalent

variable {w : W}

/-- The classical value at `w` of `F`, at the gap `K` of a larger formula, when each trigger whose
presupposition fails at `w` takes the value `ρ` gives its position and its type (items 24–25). -/
def resolve (w : W) (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    SyntacticEnvironment Atom → Formula Atom → Prop
  | _, .atom p => w ∈ I p
  | K, .trigger p p' => w ∈ I p ∧ w ∈ I p' ∨ w ∉ I p ∧ ρ K p p'
  | K, .not F => ¬ resolve w ρ (.not :: K) F
  | K, .bin c F G => c.eval (resolve w ρ (.left c G :: K) F) (resolve w ρ (.right c F :: K) G)

/-- `F` is super-defined at `w` when every resolution of its trigger types gives it the same value
(item 25). -/
def SuperDefined (w : W) (F : Formula Atom) : Prop :=
  ∀ σ σ' : Atom → Atom → Prop, resolve I w (fun _ ↦ σ) [] F ↔ resolve I w (fun _ ↦ σ') [] F

/-- `F` is Kleene-defined at `w` when every resolution of its trigger tokens gives it the same value
(items 27–28). -/
def TokenDefined (w : W) (F : Formula Atom) : Prop :=
  ∀ ρ ρ', resolve I w ρ [] F ↔ resolve I w ρ' [] F

/-- The sentences a reading evaluates: the string up to each trigger completed by each final the
reading consults, which on the symmetric reading is the sentence itself (items 26, 29). -/
def Reading.completions (r : Reading) (F : Formula Atom) : Set (Formula Atom) :=
  {X | ∃ o ∈ F.occurrences, ∃ K', r.Finals o.1 K' ∧ X = K'.fill (.trigger o.2.1 o.2.2)}

/-- Kleene acceptability on a reading: every sentence the reading evaluates has a Strong Kleene
value at every world of `C`, by the evaluation of item 40, which Theorem 41 (`tokenDefined_iff`)
shows equivalent to items 27–28 (item 29). -/
def KleeneAcceptable (r : Reading) (C : Set W) (F : Formula Atom) : Prop :=
  ∀ w ∈ C, ∀ X ∈ r.completions F, X.strong I w ≠ 0

/-- Supervaluation acceptability on a reading: every sentence the reading evaluates is
super-defined at every world of `C` (item 26). -/
def SuperAcceptable (r : Reading) (C : Set W) (F : Formula Atom) : Prop :=
  ∀ w ∈ C, ∀ X ∈ r.completions F, SuperDefined I w X

theorem forall_mem_completions {r : Reading} {F : Formula Atom} {P : Formula Atom → Prop} :
    (∀ X ∈ r.completions F, P X) ↔
      ∀ o ∈ F.occurrences, ∀ K', r.Finals o.1 K' → P (K'.fill (.trigger o.2.1 o.2.2)) :=
  ⟨fun h o ho K' hK ↦ h _ ⟨o, ho, K', hK, rfl⟩, fun h _ ⟨o, ho, K', hK, hX⟩ ↦ hX ▸ h o ho K' hK⟩

/-- The symmetric reading evaluates the sentence itself, if it holds a trigger. -/
theorem forall_mem_completions_symmetric {F : Formula Atom} {P : Formula Atom → Prop} :
    (∀ X ∈ Reading.symmetric.completions F, P X) ↔ (F.occurrences ≠ [] → P F) := by
  simp only [forall_mem_completions, Reading.Finals, forall_eq]
  refine ⟨fun h hF ↦ ?_, fun h o ho ↦ ?_⟩
  · obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hF
    simpa [Formula.fill_of_mem_occurrences ho] using h o ho
  · rw [Formula.fill_of_mem_occurrences ho]
    exact h (List.ne_nil_of_mem ho)

/-- A property holds of `F` incrementally when it holds of the string up to each trigger completed
by any good final without triggers. -/
private def Incrementally (P : Formula Atom → Prop) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, ∀ K', o.1.SameInitialString K' → K'.TriggerFreeFinal →
    P (K'.fill (.trigger o.2.1 o.2.2))

private theorem forall_mem_completions_incremental {F : Formula Atom} {P : Formula Atom → Prop} :
    (∀ X ∈ Reading.incremental.completions F, P X) ↔ Incrementally P F :=
  forall_mem_completions.trans (forall₂_congr fun _ _ ↦ forall_congr' fun _ ↦ and_imp)

/-! #### Resolutions -/

theorem resolve_congr {ρ ρ' : SyntacticEnvironment Atom → Atom → Atom → Prop}
    {K : SyntacticEnvironment Atom} (F : Formula Atom) (h : ∀ L, ρ (L ++ K) = ρ' (L ++ K)) :
    resolve I w ρ K F ↔ resolve I w ρ' K F := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' => simp only [resolve, show ρ K = ρ' K from h []]
  | not F ih =>
    exact not_congr (ih fun L ↦ by
      have := h (L ++ [.not]); rwa [List.append_assoc, List.singleton_append] at this)
  | bin c F G ihF ihG =>
    simp only [resolve]
    rw [ihF fun L ↦ by
      have := h (L ++ [.left c G]); rwa [List.append_assoc, List.singleton_append] at this,
      ihG fun L ↦ by
      have := h (L ++ [.right c F]); rwa [List.append_assoc, List.singleton_append] at this]

/-- A resolution of trigger types does not depend on the positions. -/
theorem resolve_const (σ : Atom → Atom → Prop) (K K' : SyntacticEnvironment Atom)
    (F : Formula Atom) : resolve I w (fun _ ↦ σ) K F ↔ resolve I w (fun _ ↦ σ) K' F := by
  induction F generalizing K K' with
  | atom p => rfl
  | trigger p p' => rfl
  | not F ih => exact not_congr (ih _ _)
  | bin c F G ihF ihG => simp only [resolve]; rw [ihF _ (.left c G :: K'), ihG _ (.right c F :: K')]

private theorem append_left_ne_append_right {L L' K : SyntacticEnvironment Atom} {c c' : Connective}
    {F G : Formula Atom} : L ++ .left c G :: K ≠ L' ++ .right c' F :: K := by
  intro h
  have hl : L.length = L'.length := by simpa using congrArg List.length h
  obtain ⟨-, h'⟩ := List.append_inj h hl
  cases h'

open Classical in
/-- Resolutions of the two arguments of a binary connective combine into one. -/
private theorem exists_resolve_merge (c : Connective) (F G : Formula Atom)
    (K : SyntacticEnvironment Atom) (ρ₁ ρ₂ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    ∃ ρ, (resolve I w ρ (.left c G :: K) F ↔ resolve I w ρ₁ (.left c G :: K) F) ∧
      (resolve I w ρ (.right c F :: K) G ↔ resolve I w ρ₂ (.right c F :: K) G) :=
  ⟨fun K₀ ↦ if ∃ L, K₀ = L ++ .left c G :: K then ρ₁ K₀ else ρ₂ K₀,
    resolve_congr I F fun L ↦ ite_eq_left ⟨L, rfl⟩,
    resolve_congr I G fun _ ↦ ite_eq_right fun ⟨_, h⟩ ↦ append_left_ne_append_right h.symm⟩

/-- On its filtering presupposition, a formula takes its classical value under every resolution. -/
theorem resolve_of_filter_ne_zero {F : Formula Atom} (h : F.filter I w ≠ 0)
    (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) (K : SyntacticEnvironment Atom) :
    resolve I w ρ K F ↔ w ∈ F.truth I := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' =>
    have hp : w ∈ I p := Set.mem_of_indicator_ne_zero h
    simp only [resolve, Formula.truth, Set.mem_inter_iff, hp, not_true_eq_false, false_and,
      or_false, true_and]
  | not F ih => exact not_congr (ih (by simpa [Formula.filter, Formula.eval] using h) _)
  | bin c F G ihF ihG =>
    rw [Formula.filter_bin_ne_zero] at h
    simp only [resolve, Formula.truth, Set.mem_ofPred_eq, ihF h.1]
    cases c <;> simp only [Connective.eval, Connective.localContext, Set.mem_inter_iff,
      Set.mem_univ, true_and, Set.mem_compl_iff] at h ⊢
    · by_cases ht : w ∈ F.truth I
      · rw [ihG (h.2 ht)]
      · simp [ht]
    · by_cases ht : w ∈ F.truth I
      · rw [ihG (h.2 ht)]
      · simp [ht]
    · by_cases ht : w ∈ F.truth I
      · simp [ht]
      · rw [ihG (h.2 ht)]

/-! #### Theorem 41: Strong Kleene is supervaluation over trigger tokens -/

private theorem inf_ne_neg_one {a b : SignType} : a ⊓ b ≠ -1 ↔ a ≠ -1 ∧ b ≠ -1 := by
  cases a <;> cases b <;> decide
private theorem inf_ne_one {a b : SignType} : a ⊓ b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by
  cases a <;> cases b <;> decide
private theorem sup_ne_neg_one {a b : SignType} : a ⊔ b ≠ -1 ↔ a ≠ -1 ∨ b ≠ -1 := by
  cases a <;> cases b <;> decide
private theorem sup_ne_one {a b : SignType} : a ⊔ b ≠ 1 ↔ a ≠ 1 ∧ b ≠ 1 := by
  cases a <;> cases b <;> decide
private theorem neg_ne_neg_one {a : SignType} : -a ≠ -1 ↔ a ≠ 1 := by
  cases a <;> decide
private theorem neg_ne_one {a : SignType} : -a ≠ 1 ↔ a ≠ -1 := by
  cases a <;> decide

/-- A formula can be true under some resolution of its tokens iff its Strong Kleene value is not
false, and false under some resolution iff its value is not true. -/
private theorem exists_resolve_iff (F : Formula Atom) (K : SyntacticEnvironment Atom) :
    ((∃ ρ, resolve I w ρ K F) ↔ F.strong I w ≠ -1) ∧
      ((∃ ρ, ¬ resolve I w ρ K F) ↔ F.strong I w ≠ 1) := by
  induction F generalizing K with
  | atom p =>
    simp [resolve, Formula.strong, Formula.eval]
  | trigger p p' =>
    have e₁ : (∃ ρ, resolve I w ρ K (.trigger p p')) ↔ (w ∈ I p ∧ w ∈ I p' ∨ w ∉ I p) :=
      ⟨fun ⟨_, h⟩ ↦ h.imp_right And.left,
        fun h ↦ ⟨fun _ _ _ ↦ True, h.imp_right fun h ↦ ⟨h, trivial⟩⟩⟩
    have e₀ : (∃ ρ, ¬ resolve I w ρ K (.trigger p p')) ↔ ¬ (w ∈ I p ∧ w ∈ I p') :=
      ⟨fun ⟨_, h⟩ hp ↦ h (.inl hp),
        fun h ↦ ⟨fun _ _ _ ↦ False, fun h' ↦ h'.elim h fun h'' ↦ h''.2⟩⟩
    refine ⟨e₁.trans ?_, e₀.trans ?_⟩ <;>
      simp only [Formula.strong, Formula.eval, ne_eq, Trivalent.indicator_apply_eq_neg_one_iff,
        Trivalent.indicator_apply_eq_one_iff, SignType.ofProp_eq_neg_one_iff,
        SignType.ofProp_eq_one_iff]
    tauto
  | not F ih =>
    simp only [resolve, Formula.strong, Formula.eval, Pi.neg_apply, neg_ne_neg_one, neg_ne_one,
      not_not]
    exact ⟨(ih _).2, (ih _).1⟩
  | bin c F G ihF ihG =>
    obtain ⟨hF₁, hF₀⟩ := ihF (.left c G :: K)
    obtain ⟨hG₁, hG₀⟩ := ihG (.right c F :: K)
    have merge := exists_resolve_merge I (w := w) c F G K
    cases c <;> simp only [resolve, Formula.strong, Formula.eval, Connective.table,
      Trivalent.Connectives.strongKleene_conj, Trivalent.Connectives.strongKleene_cond,
      Trivalent.Connectives.strongKleene_disj, Connective.eval, inf_ne_neg_one, inf_ne_one,
      sup_ne_neg_one, sup_ne_one, neg_ne_neg_one, neg_ne_one, ← hF₁, ← hF₀, ← hG₁, ← hG₀]
    · refine ⟨⟨fun ⟨ρ, a, b⟩ ↦ ⟨⟨ρ, a⟩, ⟨ρ, b⟩⟩, fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ?_, fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, fun h ↦ a h.1⟩)
          (fun ⟨ρ, b⟩ ↦ ⟨ρ, fun h ↦ b h.2⟩)⟩⟩
      · obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂; exact ⟨ρ, e₁.2 a, e₂.2 b⟩
      · by_cases a : resolve I w ρ (.left .conj G :: K) F
        · exact .inr ⟨ρ, fun b ↦ h ⟨a, b⟩⟩
        · exact .inl ⟨ρ, a⟩
    · refine ⟨⟨fun ⟨ρ, h⟩ ↦ ?_, fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, fun h ↦ absurd h a⟩)
          (fun ⟨ρ, b⟩ ↦ ⟨ρ, fun _ ↦ b⟩)⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ⟨⟨ρ, by tauto⟩, ⟨ρ, fun b ↦ h fun _ ↦ b⟩⟩, fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩⟩
      · by_cases a : resolve I w ρ (.left .cond G :: K) F
        · exact .inr ⟨ρ, h a⟩
        · exact .inl ⟨ρ, a⟩
      · obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂; exact ⟨ρ, fun h ↦ b (e₂.1 (h (e₁.2 a)))⟩
    · refine ⟨⟨fun ⟨ρ, h⟩ ↦ h.elim (fun a ↦ .inl ⟨ρ, a⟩) (fun b ↦ .inr ⟨ρ, b⟩),
          fun h ↦ h.elim (fun ⟨ρ, a⟩ ↦ ⟨ρ, .inl a⟩) (fun ⟨ρ, b⟩ ↦ ⟨ρ, .inr b⟩)⟩,
        ⟨fun ⟨ρ, h⟩ ↦ ⟨⟨ρ, fun a ↦ h (.inl a)⟩, ⟨ρ, fun b ↦ h (.inr b)⟩⟩,
          fun ⟨⟨ρ₁, a⟩, ⟨ρ₂, b⟩⟩ ↦ ?_⟩⟩
      obtain ⟨ρ, e₁, e₂⟩ := merge ρ₁ ρ₂
      exact ⟨ρ, fun h ↦ h.elim (fun h ↦ a (e₁.1 h)) (fun h ↦ b (e₂.1 h))⟩

/-- Where the Strong Kleene evaluation is defined, every resolution of the tokens gives its value
(the value half of Theorem 41). -/
theorem resolve_iff_of_ne_zero {F : Formula Atom} (h : F.strong I w ≠ 0)
    (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    resolve I w ρ [] F ↔ F.strong I w = 1 := by
  obtain ⟨h₁, h₀⟩ := exists_resolve_iff I (w := w) F []
  by_cases ha : F.strong I w = 1
  · exact iff_of_true (by by_contra hn; exact h₀.1 ⟨ρ, hn⟩ ha) ha
  · have he : F.strong I w = -1 := by cases hv : F.strong I w <;> simp_all
    exact iff_of_false (fun hr ↦ h₁.1 ⟨ρ, hr⟩ he) ha

/-- A formula is Kleene-defined in the sense of items 27–28 iff its Strong Kleene evaluation is
defined (Theorem 41). -/
theorem tokenDefined_iff (F : Formula Atom) : TokenDefined I w F ↔ F.strong I w ≠ 0 := by
  refine ⟨fun hd he ↦ ?_, fun hp ρ ρ' ↦ by
    rw [resolve_iff_of_ne_zero I hp, resolve_iff_of_ne_zero I hp]⟩
  obtain ⟨h₁, h₀⟩ := exists_resolve_iff I (w := w) F []
  obtain ⟨ρ, hρ⟩ := h₁.2 (by rw [he]; decide)
  obtain ⟨ρ', hρ'⟩ := h₀.2 (by rw [he]; decide)
  exact hρ' ((hd ρ ρ').1 hρ)

/-! #### Lemmas 6–8 and 11: Kleene and supervaluations -/

/-- Where the Strong Kleene evaluation is defined, the supervaluation is defined, with the same
value by `resolve_iff_of_ne_zero` (Lemma 7, item 31). -/
theorem superDefined_of_strong_ne_zero {F : Formula Atom} (h : F.strong I w ≠ 0) :
    SuperDefined I w F :=
  fun _ _ ↦ (tokenDefined_iff I F).2 h _ _

theorem resolve_congr_occurrences {ρ ρ' : SyntacticEnvironment Atom → Atom → Atom → Prop}
    {K : SyntacticEnvironment Atom} (F : Formula Atom)
    (h : ∀ o ∈ F.occurrences, ρ (o.1 ++ K) o.2.1 o.2.2 ↔ ρ' (o.1 ++ K) o.2.1 o.2.2) :
    resolve I w ρ K F ↔ resolve I w ρ' K F := by
  induction F generalizing K with
  | atom p => rfl
  | trigger p p' =>
    have := h _ (List.mem_singleton_self ([], p, p'))
    simp only [List.nil_append] at this
    simp only [resolve, this]
  | not F ih =>
    refine not_congr (ih fun o ho ↦ ?_)
    have := h _ (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.not], o.2)) ho)
    simpa only [List.append_assoc, List.singleton_append] using this
  | bin c F G ihF ihG =>
    simp only [resolve]
    rw [ihF fun o ho ↦ ?_, ihG fun o ho ↦ ?_]
    · have := h _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.right c F], o.2)) ho))
      simpa only [List.append_assoc, List.singleton_append] using this
    · have := h _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun o ↦ (o.1 ++ [.left c G], o.2)) ho))
      simpa only [List.append_assoc, List.singleton_append] using this

/-- When every trigger occurs once, the supervaluation and the Strong Kleene evaluation are defined
together (Lemma 6, item 30). -/
theorem superDefined_iff_of_nodup {F : Formula Atom} (hF : (F.occurrences.map Prod.snd).Nodup) :
    SuperDefined I w F ↔ F.strong I w ≠ 0 := by
  refine ⟨fun hs ↦ (tokenDefined_iff I F).1 fun ρ ρ' ↦ ?_, superDefined_of_strong_ne_zero I⟩
  have key (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) : resolve I w ρ [] F ↔
      resolve I w (fun _ p p' ↦ ∃ o ∈ F.occurrences, o.2 = (p, p') ∧ ρ o.1 p p') [] F :=
    resolve_congr_occurrences I F fun o ho ↦ by
      simp only [List.append_nil]
      refine ⟨fun h ↦ ⟨o, ho, rfl, h⟩, fun ⟨o', ho', he, h⟩ ↦ ?_⟩
      obtain rfl := List.inj_on_of_nodup_map hF ho' ho he
      exact h
  rw [key ρ, key ρ']
  exact hs _ _

/-- Kleene acceptability implies super-acceptability on either reading (Lemma 8, item 32). -/
theorem KleeneAcceptable.superAcceptable {r : Reading} {C : Set W} {F : Formula Atom}
    (h : KleeneAcceptable I r C F) : SuperAcceptable I r C F :=
  fun w hw X hX ↦ superDefined_of_strong_ne_zero I (h w hw X hX)

/-! #### Incremental acceptability -/

private theorem Incrementally.congr {P Q : Formula Atom → Prop} (h : ∀ X, P X ↔ Q X)
    {F : Formula Atom} : Incrementally P F ↔ Incrementally Q F :=
  forall₂_congr fun _ _ ↦ forall_congr' fun _ ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    h _

private theorem incrementally_atom (P : Formula Atom → Prop) (p : Atom) :
    Incrementally P (.atom p) := by
  simp [Incrementally, Formula.occurrences]

private theorem incrementally_trigger {P : Formula Atom → Prop} {p p' : Atom} :
    Incrementally P (.trigger p p') ↔ P (.trigger p p') := by
  simp only [Incrementally, Formula.occurrences, List.mem_singleton, forall_eq]
  refine ⟨fun h ↦ h [] (.refl []) fun _ _ h ↦ by simp at h, fun h K' hK _ ↦ ?_⟩
  cases hK
  exact h

private theorem incrementally_not {P : Formula Atom → Prop} {F : Formula Atom} :
    Incrementally P (.not F) ↔ Incrementally (fun X ↦ P (.not X)) F := by
  simp only [Incrementally, Formula.occurrences, List.forall_mem_map]
  refine forall₂_congr fun o _ ↦ ⟨fun h K' hK hT ↦ ?_, fun h K' hK hT ↦ ?_⟩
  · have := h (K' ++ [.not])
      (SyntacticEnvironment.sameInitialString_append_singleton.2 ⟨K', .not, rfl, hK, .not⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    cases hs
    rw [SyntacticEnvironment.fill_append]
    exact h K'' hK'' (SyntacticEnvironment.triggerFreeFinal_append.1 hT).1

private theorem incrementally_bin {P : Formula Atom → Prop} {c : Connective} {F G : Formula Atom} :
    Incrementally P (.bin c F G) ↔
      Incrementally (fun X ↦ ∀ c' G', (c = .cond ↔ c' = .cond) → G'.occurrences = [] →
        P (.bin c' X G')) F ∧ Incrementally (fun Y ↦ P (.bin c F Y)) G := by
  simp only [Incrementally, Formula.occurrences, List.forall_mem_append, List.forall_mem_map]
  refine and_congr (forall₂_congr fun o _ ↦ ⟨fun h K' hK hT c' G' hc hG ↦ ?_,
    fun h K' hK hT ↦ ?_⟩) (forall₂_congr fun o _ ↦ ⟨fun h K' hK hT ↦ ?_, fun h K' hK hT ↦ ?_⟩)
  · have := h (K' ++ [.left c' G'])
      (SyntacticEnvironment.sameInitialString_append_singleton.2
        ⟨K', _, rfl, hK, .left hc G G'⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h; exact hG⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    obtain ⟨hT'', hTs⟩ := SyntacticEnvironment.triggerFreeFinal_append.1 hT
    cases hs with
    | left hc _ G' =>
      rw [SyntacticEnvironment.fill_append]
      exact h K'' hK'' hT'' _ G' hc (SyntacticEnvironment.triggerFreeFinal_singleton.1 hTs _ _ rfl)
  · have := h (K' ++ [.right c F])
      (SyntacticEnvironment.sameInitialString_append_singleton.2 ⟨K', _, rfl, hK, .right c F⟩)
      (SyntacticEnvironment.triggerFreeFinal_append.2
        ⟨hT, SyntacticEnvironment.triggerFreeFinal_singleton.2 fun _ _ h ↦ by cases h⟩)
    rwa [SyntacticEnvironment.fill_append] at this
  · obtain ⟨K'', s', rfl, hK'', hs⟩ :=
      SyntacticEnvironment.sameInitialString_append_singleton.1 hK
    cases hs
    rw [SyntacticEnvironment.fill_append]
    exact h K'' hK'' (SyntacticEnvironment.triggerFreeFinal_append.1 hT).1

/-- A property of formulas that is decided like definedness, at triggers, under negation, and at
each argument of a connective, holds incrementally of a formula iff the filtering presupposition
holds. -/
private theorem incrementally_iff_filter (P : Formula Atom → Prop)
    (htrig : ∀ p p' : Atom, P (.trigger p p') ↔ w ∈ I p)
    (hnot : ∀ X : Formula Atom, P (.not X) ↔ P X)
    (hleft : ∀ (c : Connective) (X : Formula Atom), (∀ (c' : Connective) (G' : Formula Atom),
      (c = .cond ↔ c' = .cond) → G'.occurrences = [] → P (.bin c' X G')) ↔ P X)
    (hright : ∀ (c : Connective) (F Y : Formula Atom), F.filter I w ≠ 0 →
      (P (.bin c F Y) ↔ (w ∈ c.localContext Set.univ (F.truth I) → P Y)))
    (F : Formula Atom) : Incrementally P F ↔ F.filter I w ≠ 0 := by
  induction F with
  | atom p => exact iff_of_true (incrementally_atom P p) (by simp [Formula.filter, Formula.eval])
  | trigger p p' => rw [incrementally_trigger, htrig]; simp [Formula.filter, Formula.eval]
  | not F ih =>
    rw [incrementally_not, Incrementally.congr hnot, ih]; simp [Formula.filter, Formula.eval]
  | bin c F G ihF ihG =>
    rw [incrementally_bin, Incrementally.congr (hleft c), ihF, Formula.filter_bin_ne_zero]
    refine and_congr_right fun hF ↦ ?_
    rw [Incrementally.congr (hright c F · hF), ← ihG]
    exact ⟨fun h hk o ho K' hK hT ↦ h o ho K' hK hT hk, fun h o ho K' hK hT hk ↦ h hk o ho K' hK hT⟩

/-- A tautology, from any atom. -/
private def taut (a : Atom) : Formula Atom := .bin .cond (.atom a) (.atom a)

private theorem occurrences_taut (a : Atom) : (taut a).occurrences = [] := rfl

private theorem filter_ne_zero_of_occurrences {F : Formula Atom} (h : F.occurrences = []) :
    F.filter I w ≠ 0 :=
  (Formula.filter_ne_zero_iff I F w).2 fun o ho ↦ by simp [h] at ho

open Classical in
/-- On its filtering presupposition, a formula's Strong Kleene evaluation is its classical
value. -/
theorem strong_eq_ofProp_of_filter_ne_zero {F : Formula Atom} (h : F.filter I w ≠ 0) :
    F.strong I w = SignType.ofProp (w ∈ F.truth I) := by
  have hp : F.strong I w ≠ 0 := (tokenDefined_iff I F).1 fun ρ ρ' ↦ by
    rw [resolve_of_filter_ne_zero I h, resolve_of_filter_ne_zero I h]
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp [hp]) ?_
  rw [SignType.ofProp_eq_one_iff, ← resolve_iff_of_ne_zero I hp fun _ _ _ ↦ True]
  exact resolve_of_filter_ne_zero I h _ _

private theorem strong_ne_zero (c : Connective) {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
    c.table .strongKleene a b ≠ 0 := by
  revert ha hb; cases c <;> cases a <;> cases b <;> decide

/-- Incremental Strong Kleene definedness is the filtering presupposition. -/
private theorem incrementally_strong_iff (w : W) (F : Formula Atom) :
    Incrementally (fun X ↦ X.strong I w ≠ 0) F ↔ F.filter I w ≠ 0 := by
  refine incrementally_iff_filter I _ (fun _ _ ↦ by simp [Formula.strong, Formula.eval])
    (fun _ ↦ by simp [Formula.strong, Formula.eval]) (fun c X ↦ ?_) (fun c F Y hF ↦ ?_) F
  · have : Nonempty Atom := X.nonempty_atom
    let a := Classical.arbitrary Atom
    have htaut : (taut a).strong I w = 1 := by
      by_cases ha : w ∈ I a <;> simp [taut, Formula.strong, Formula.eval, ha]
    refine ⟨fun h ↦ ?_, fun hX c' G' _ hG ↦ ?_⟩
    · cases c
      · simpa [Formula.strong, Formula.eval, htaut] using h .conj (taut a) Iff.rfl rfl
      · simpa [Formula.strong, Formula.eval, htaut] using h .cond (.not (taut a)) Iff.rfl rfl
      · simpa [Formula.strong, Formula.eval, htaut] using h .disj (.not (taut a)) Iff.rfl rfl
    · have hG' := strong_eq_ofProp_of_filter_ne_zero I (w := w) (filter_ne_zero_of_occurrences I hG)
      exact strong_ne_zero c' hX (by simp [hG'])
  · have hF' := strong_eq_ofProp_of_filter_ne_zero I hF
    cases c <;> by_cases ht : w ∈ F.truth I <;>
      simp [Formula.strong, Formula.eval, Connective.localContext, hF', ht]

/-- Incremental supervaluation definedness is the filtering presupposition. -/
private theorem incrementally_superDefined_iff (w : W) (F : Formula Atom) :
    Incrementally (SuperDefined I w) F ↔ F.filter I w ≠ 0 := by
  have hconst (σ : Atom → Atom → Prop) (K : SyntacticEnvironment Atom) (X : Formula Atom) :=
    resolve_const I (w := w) σ K [] X
  have hbin (σ : Atom → Atom → Prop) (c : Connective) (X Y : Formula Atom) :
      resolve I w (fun _ ↦ σ) [] (.bin c X Y) ↔
        c.eval (resolve I w (fun _ ↦ σ) [] X) (resolve I w (fun _ ↦ σ) [] Y) := by
    simp only [resolve]
    rw [hconst σ [.left c Y] X, hconst σ [.right c X] Y]
  have hfree {G : Formula Atom} (hG : G.occurrences = []) (σ : Atom → Atom → Prop) :
      resolve I w (fun _ ↦ σ) [] G ↔ w ∈ G.truth I :=
    resolve_of_filter_ne_zero I (filter_ne_zero_of_occurrences I hG) _ _
  refine incrementally_iff_filter I _ (fun p p' ↦ ?_) (fun X ↦ ?_) (fun c X ↦ ?_)
    (fun c F Y hF ↦ ?_) F
  · by_cases hp : w ∈ I p
    · exact iff_of_true (fun σ σ' ↦ by simp [resolve, hp]) hp
    · refine iff_of_false (fun h ↦ ?_) hp
      have := h (fun _ _ ↦ True) (fun _ _ ↦ False)
      simp [resolve, hp] at this
  · refine forall₂_congr fun σ σ' ↦ ?_
    simp only [resolve]
    rw [hconst σ, hconst σ', not_iff_not]
  · have : Nonempty Atom := X.nonempty_atom
    let a := Classical.arbitrary Atom
    refine ⟨fun h σ σ' ↦ ?_, fun hX c' G' _ hG σ σ' ↦ ?_⟩
    · cases c
      · have := h .conj (taut a) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (occurrences_taut a), hfree (occurrences_taut a)] at this
        simpa [taut, Formula.truth, Connective.eval] using this
      · have := h .cond (.not (taut a)) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (G := (taut a).not) rfl, hfree (G := (taut a).not) rfl] at this
        exact not_iff_not.1 (by simpa [taut, Formula.truth, Connective.eval] using this)
      · have := h .disj (.not (taut a)) Iff.rfl rfl σ σ'
        rw [hbin, hbin, hfree (G := (taut a).not) rfl, hfree (G := (taut a).not) rfl] at this
        simpa [taut, Formula.truth, Connective.eval] using this
    · rw [hbin, hbin, hfree hG, hfree hG, hX σ σ']
  · have hF' (σ : Atom → Atom → Prop) := resolve_of_filter_ne_zero I hF (fun _ ↦ σ) []
    simp only [SuperDefined, hbin, hF']
    cases c <;> by_cases ht : w ∈ F.truth I <;>
      simp [Connective.eval, Connective.localContext, ht]

/-- Incremental Kleene acceptability is entailment of the filtering presupposition, the route by
which Theorems 36 and 38a are proved here. -/
theorem kleeneAcceptable_incremental_iff (C : Set W) (F : Formula Atom) :
    KleeneAcceptable I .incremental C F ↔ C ⊆ Function.support (F.filter I) :=
  forall₂_congr fun w _ ↦ forall_mem_completions_incremental.trans (incrementally_strong_iff I w F)

/-- Incremental super-acceptability is entailment of the filtering presupposition. -/
theorem superAcceptable_incremental_iff (C : Set W) (F : Formula Atom) :
    SuperAcceptable I .incremental C F ↔ C ⊆ Function.support (F.filter I) :=
  forall₂_congr fun w _ ↦
    forall_mem_completions_incremental.trans (incrementally_superDefined_iff I w F)

/-- Symmetric Kleene acceptability is Strong Kleene definedness of the sentence (item 29b). -/
theorem kleeneAcceptable_symmetric_iff (C : Set W) (F : Formula Atom) :
    KleeneAcceptable I .symmetric C F ↔ C ⊆ Function.support (F.strong I) := by
  simp only [Set.subset_def, Function.mem_support]
  refine forall₂_congr fun w _ ↦ forall_mem_completions_symmetric.trans ⟨fun h ↦ ?_, fun h _ ↦ h⟩
  by_cases hF : F.occurrences = []
  · simp [strong_eq_ofProp_of_filter_ne_zero I (filter_ne_zero_of_occurrences I (w := w) hF)]
  · exact h hF

/-- Symmetric super-acceptability is super-definedness of the sentence (item 26b). -/
theorem superAcceptable_symmetric_iff (C : Set W) (F : Formula Atom) :
    SuperAcceptable I .symmetric C F ↔ ∀ w ∈ C, SuperDefined I w F := by
  refine forall₂_congr fun w _ ↦ forall_mem_completions_symmetric.trans ⟨fun h ↦ ?_, fun h _ ↦ h⟩
  by_cases hF : F.occurrences = []
  · refine superDefined_of_strong_ne_zero I ?_
    simp [strong_eq_ofProp_of_filter_ne_zero I (filter_ne_zero_of_occurrences I (w := w) hF)]
  · exact h hF

/-- Incremental Kleene acceptability is incremental super-acceptability (Theorem 36, item 36). -/
theorem kleeneAcceptable_iff_superAcceptable_incremental (C : Set W) (F : Formula Atom) :
    KleeneAcceptable I .incremental C F ↔ SuperAcceptable I .incremental C F :=
  (kleeneAcceptable_incremental_iff I C F).trans (superAcceptable_incremental_iff I C F).symm

/-- As item 20 notes for every theory, incremental Kleene acceptability implies symmetric Kleene
acceptability. -/
theorem KleeneAcceptable.symmetric {C : Set W} {F : Formula Atom}
    (h : KleeneAcceptable I .incremental C F) : KleeneAcceptable I .symmetric C F :=
  (kleeneAcceptable_symmetric_iff I C F).2 fun _ hw ↦ by
    simp [strong_eq_ofProp_of_filter_ne_zero I ((kleeneAcceptable_incremental_iff I C F).1 h hw)]

/-- As item 20 notes for every theory, incremental super-acceptability implies symmetric
super-acceptability. -/
theorem SuperAcceptable.symmetric {C : Set W} {F : Formula Atom}
    (h : SuperAcceptable I .incremental C F) : SuperAcceptable I .symmetric C F :=
  (((kleeneAcceptable_iff_superAcceptable_incremental I C F).2 h).symmetric I).superAcceptable I

/-- Incremental Transparency implies incremental Kleene and supervaluation acceptability (Theorem
38a, item 38). -/
theorem Transparency.kleeneAcceptable {C : Set W} {F : Formula Atom}
    (h : Transparency .incremental C (Occurrence.ofFormula I F)) :
    KleeneAcceptable I .incremental C F ∧ SuperAcceptable I .incremental C F :=
  have hK := (kleeneAcceptable_incremental_iff I C F).2
    (Formula.admits_ccp_iff I |>.1 ((transparency_incremental_iff_admits I C F).1 h))
  ⟨hK, (kleeneAcceptable_iff_superAcceptable_incremental I C F).1 hK⟩

/-- With a world where `p` and `q` fail and one where both hold, `(pp' and qq')` satisfies symmetric
Transparency but is neither Kleene- nor super-acceptable (Theorem 39a, item 39). -/
theorem transparency_symmetric_not_kleeneAcceptable_not_superAcceptable {p p' q q' : Atom}
    {w₁ w₂ : W} (hp₁ : w₁ ∉ I p) (hq₁ : w₁ ∉ I q) (hp₂ : w₂ ∈ I p) (hq₂ : w₂ ∈ I q) :
    Transparency .symmetric {w₁, w₂}
        (Occurrence.ofFormula I (.bin .conj (.trigger p p') (.trigger q q'))) ∧
      ¬ KleeneAcceptable I .symmetric {w₁, w₂} (.bin .conj (.trigger p p') (.trigger q q')) ∧
      ¬ SuperAcceptable I .symmetric {w₁, w₂} (.bin .conj (.trigger p p') (.trigger q q')) := by
  refine ⟨Occurrence.forall_mem_ofFormula.2 fun o ho f hf d w hw ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Formula.occurrences, List.map_cons, List.map_nil, List.nil_append,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    obtain rfl : f = o.1.truth I := hf
    rcases hw with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp [SyntacticEnvironment.occurrence, SyntacticEnvironment.truth,
        SyntacticEnvironment.Step.truth, Connective.eval, Formula.truth, hp₁, hq₁, hp₂, hq₂]
  · have h₁ : Formula.strong I (.bin .conj (.trigger p p') (.trigger q q')) w₁ ≠ 0 :=
      (kleeneAcceptable_symmetric_iff I _ _).1 h (Set.mem_insert w₁ _)
    simp [Formula.strong, Formula.eval, hp₁, hq₁] at h₁
  · have := (superAcceptable_symmetric_iff I _ _).1 h w₁ (Set.mem_insert _ _)
      (fun _ _ ↦ True) (fun _ _ ↦ False)
    simp [resolve, Connective.eval, hp₁, hq₁] at this

/-- `(pp' or (not pp'))` is symmetrically super-acceptable in the set of all worlds, but not
Kleene-acceptable there when `p` is not a tautology (Lemma 11, item 37). -/
theorem superAcceptable_symmetric_not_kleeneAcceptable {p p' : Atom} {w₀ : W} (hw₀ : w₀ ∉ I p) :
    SuperAcceptable I .symmetric Set.univ (.bin .disj (.trigger p p') (.not (.trigger p p'))) ∧
      ¬ KleeneAcceptable I .symmetric Set.univ
        (.bin .disj (.trigger p p') (.not (.trigger p p'))) := by
  refine ⟨(superAcceptable_symmetric_iff I _ _).2 fun w _ σ σ' ↦ ?_, fun h ↦ ?_⟩
  · simp only [resolve, Connective.eval]
    tauto
  · have h₀ : Formula.strong I (.bin .disj (.trigger p p') (.not (.trigger p p'))) w₀ ≠ 0 :=
      (kleeneAcceptable_symmetric_iff I _ _).1 h (Set.mem_univ w₀)
    simp [Formula.strong, Formula.eval, hw₀] at h₀

end Trivalent

/-! ### Quantified sentences (C.9, C.23 and items 38–39 of [schlenker-2008b]) -/

section Quantified

open Quantifier

variable {E : Type*} {q : NumberTree} {A : W → E → Prop} {C : Set W} {P : Set (W × E)}

/-- Where `q` is not constant on the row of the restrictor's size at any world of the context, as
C.9's Non-Triviality and Constancy together guarantee, a presupposition triggered in the nuclear
scope is transparent iff every individual of the restrictor satisfies it at every world of the
context. This is universal projection, the consequence of Theorem 2 of C.9 for a quantified
clause. -/
theorem transparent_scope_iff_universal [Finite E]
    (hNT : ∀ w ∈ C, ¬ q.ConstantOnRow {x | A w x}.ncard) :
    Transparent C {scopeTruth q A} P ↔ ∀ w ∈ C, ∀ e, A w e → (w, e) ∈ P := by
  rw [transparent_scopeTruth_iff]
  exact ⟨fun h w hw ↦ h w hw (hNT w hw), fun h w hw _ ↦ h w hw⟩

/-- The truth set of `(Infinitely-many P. _)` at a single world where every natural number is a
`P`, as a function of its scope. -/
def infinitelyMany (d : Set (Unit × ℕ)) : Set Unit := {u | {n | (u, n) ∈ d}.Infinite}

/-- A presupposition that fails of finitely many individuals is transparent in the scope of
*infinitely many*, which does not then presuppose that every individual satisfies it (C.23ii). -/
theorem transparent_infinitelyMany_of_finite {P : Set (Unit × ℕ)}
    (hP : {n | ((), n) ∉ P}.Finite) : Transparent Set.univ {infinitelyMany} P := by
  rintro f rfl d ⟨⟩ -
  change {n | ((), n) ∈ P ∩ d}.Infinite ↔ {n | ((), n) ∈ d}.Infinite
  exact ⟨fun h ↦ h.mono fun _ hn ↦ hn.2,
    fun h ↦ (h.sdiff hP).mono fun _ hn ↦ ⟨by simpa using hn.2, hn.1⟩⟩

/-- The scope of *infinitely many* has no local context. Leaving out any one individual is
transparent, so a least transparent restriction would contain no individual, but the empty
restriction is not transparent (C.23i). -/
theorem not_exists_isLocalContext_infinitelyMany :
    ¬ ∃ x, IsLocalContext Set.univ {infinitelyMany} x := by
  rintro ⟨x, hx, hle⟩
  obtain rfl : x = ∅ := Set.eq_empty_of_forall_notMem fun ⟨_, n⟩ h ↦
    hle (transparent_infinitelyMany_of_finite (P := {p | p.2 ≠ n})
      ((Set.finite_singleton n).subset fun m hm ↦ by simpa using hm)) h rfl
  have := hx infinitelyMany rfl Set.univ () trivial
  simp [infinitelyMany, Set.infinite_univ] at this

/-- With one world and two individuals, the first not `Q` and the second `Q` and `Q'`, the sentence
`(No P. QQ')` is false however the first individual is resolved, so the trigger is transparent at
its assertion and the sentence is Kleene and supervaluation acceptable
(`QuantifiedClause.kleeneAcceptable_trigger_iff`), but Transparency rejects it, since for a scope
false of the second individual the first decides (Theorems 38b and 39b; the trigger is final, so the
incremental and symmetric versions coincide). -/
theorem transparentAt_not_transparent_no :
    TransparentAt {()} {scopeTruth NumberTree.no fun (_ : Unit) (_ : Fin 2) ↦ True}
        {p | p.2 = 1} Set.univ ∧
      ¬ Transparent {()} {scopeTruth NumberTree.no fun (_ : Unit) (_ : Fin 2) ↦ True}
        {p | p.2 = 1} := by
  refine ⟨transparentAt_scopeTruth_iff.2 fun _ _ D D' hD hD' ↦ ?_, fun h ↦ ?_⟩
  · have h1 : D 1 := (hD 1 rfl).2 trivial
    have h1' : D' 1 := (hD' 1 rfl).2 trivial
    simp only [NumberTree.toGQ_apply, NumberTree.no, true_and]
    refine iff_of_false (fun h ↦ ?_) fun h ↦ ?_
    · exact (Set.ncard_eq_zero (s := {x | D x}).1 h).subset (Set.mem_ofPred.2 h1) |>.elim
    · exact (Set.ncard_eq_zero (s := {x | D' x}).1 h).subset (Set.mem_ofPred.2 h1') |>.elim
  · have := (transparent_scopeTruth_iff NumberTree.no).1 h () rfl (fun hc ↦ ?_) 0 trivial
    · exact absurd this (by decide)
    · have h2 : {_x : Fin 2 | True}.ncard = 2 := by simp
      have := hc 2 0 1 1 h2.symm h2.symm
      simp [NumberTree.no] at this

end Quantified

/-! ### Quantified clauses -/

section QuantifiedClause

open Quantifier

variable {E : Type*} (J : Atom → Set (W × E)) {C : Set W} {c : QuantifiedClause Atom}

namespace QuantifiedClause

/-- In a clause whose scope is a trigger and whose restrictor holds none, symmetric Transparency is
universal projection over the restrictor, at each world where the quantifier is not constant on
the row of the restrictor's size. -/
theorem transparency_symmetric_trigger_iff [Finite E] {q : NumberTree} {R : Formula Atom}
    {p a : Atom} (hR : R.occurrences = []) :
    Transparency .symmetric C (Occurrence.ofClause J ⟨q, R, .trigger p a⟩) ↔
      ∀ w ∈ C, ¬ q.ConstantOnRow {e | (w, e) ∈ R.truth J}.ncard →
        ∀ e, (w, e) ∈ R.truth J → (w, e) ∈ J p := by
  simp only [Transparency, Occurrence.forall_mem_ofClause, QuantifiedClause.occurrences, hR,
    Formula.occurrences, List.map_nil, List.nil_append, List.map_cons, List.mem_singleton,
    forall_eq]
  change Transparent C (QuantifiedClause.Env.parsePoint J ⊤ ⟨q, .scope R, []⟩) (J p) ↔ _
  rw [QuantifiedClause.Env.parsePoint_top]
  exact transparent_scopeTruth_iff q

/-! #### Strong Kleene and supervaluations -/

/-- The value at `w` of a clause when each trigger token of the restrictor whose presupposition
fails of an individual takes the value `ρR` gives it for that individual, and each token of the
scope the value `ρS` gives it (items 24–25, individual by individual). -/
def resolve (w : W) (ρR ρS : E → SyntacticEnvironment Atom → Atom → Atom → Prop)
    (c : QuantifiedClause Atom) : Prop :=
  c.quantifier.toGQ (fun e ↦ Schlenker2009.resolve J (w, e) (ρR e) [] c.restrictor)
    fun e ↦ Schlenker2009.resolve J (w, e) (ρS e) [] c.scope

/-- A clause is Kleene-defined at `w` when every resolution of its trigger tokens gives it the same
value (items 27–28). -/
def TokenDefined (w : W) (c : QuantifiedClause Atom) : Prop :=
  ∀ ρR ρS ρR' ρS', resolve J w ρR ρS c ↔ resolve J w ρR' ρS' c

/-- A clause is super-defined at `w` when every resolution of its trigger types, alike for all
their tokens, gives it the same value (item 25). -/
def SuperDefined (w : W) (c : QuantifiedClause Atom) : Prop :=
  ∀ σ σ' : E → Atom → Atom → Prop, resolve J w (fun e _ ↦ σ e) (fun e _ ↦ σ e) c ↔
    resolve J w (fun e _ ↦ σ' e) (fun e _ ↦ σ' e) c

/-- The finals a reading consults at the gap of a clause's environment, as `Reading.Finals` does
for formulas: on the incremental reading each good final without triggers, on the symmetric reading
the environment itself. -/
def Finals : Reading → QuantifiedClause.Env Atom → QuantifiedClause.Env Atom → Prop
  | .incremental, k, k' => k.SameInitialString k' ∧ k'.TriggerFreeFinal
  | .symmetric, k, k' => k' = k

/-- The clauses a reading evaluates: the string up to each trigger completed by each final the
reading consults, as `Reading.completions` does for formulas. -/
def completions (r : Reading) (c : QuantifiedClause Atom) : Set (QuantifiedClause Atom) :=
  {X | ∃ o ∈ c.occurrences, ∃ k', Finals r o.1 k' ∧ X = k'.fill (.trigger o.2.1 o.2.2)}

/-- Kleene acceptability of a clause on a reading (item 29). -/
def KleeneAcceptable (r : Reading) (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ w ∈ C, ∀ X ∈ completions r c, TokenDefined J w X

/-- Supervaluation acceptability of a clause on a reading (item 26). -/
def SuperAcceptable (r : Reading) (C : Set W) (c : QuantifiedClause Atom) : Prop :=
  ∀ w ∈ C, ∀ X ∈ completions r c, SuperDefined J w X

theorem KleeneAcceptable.superAcceptable {r : Reading} (h : KleeneAcceptable J r C c) :
    SuperAcceptable J r C c :=
  fun w hw X hX _ _ ↦ h w hw X hX _ _ _ _

/-- A clause without triggers is Kleene acceptable in every context, on either reading. -/
theorem kleeneAcceptable_of_occurrences_eq_nil (r : Reading) (hc : c.occurrences = []) :
    KleeneAcceptable J r C c :=
  fun _ _ _ ⟨_, ho, _⟩ ↦ by simp [hc] at ho

/-- A clause without triggers is super acceptable in every context, on either reading. -/
theorem superAcceptable_of_occurrences_eq_nil (r : Reading) (hc : c.occurrences = []) :
    SuperAcceptable J r C c :=
  (kleeneAcceptable_of_occurrences_eq_nil J r hc).superAcceptable J

section Trigger

variable {q : NumberTree} {R : Formula Atom} {p a : Atom}

/-- A formula without triggers takes its classical value under every resolution. -/
private theorem resolve_iff_of_occurrences {F : Formula Atom} (hF : F.occurrences = [])
    (x : W × E) (ρ : SyntacticEnvironment Atom → Atom → Atom → Prop) :
    Schlenker2009.resolve J x ρ [] F ↔ x ∈ F.truth J :=
  resolve_of_filter_ne_zero J (filter_ne_zero_of_occurrences J hF) ρ []

/-- A resolution gives a clause whose scope is a trigger and whose restrictor holds none the
value of the quantifier on the scope that agrees with the assertion where the presupposition holds
and with the resolution elsewhere. -/
private theorem resolve_trigger_iff (hR : R.occurrences = []) {w : W} {ρR ρS} :
    resolve J w ρR ρS ⟨q, R, .trigger p a⟩ ↔ q.toGQ (fun e ↦ (w, e) ∈ R.truth J)
      fun e ↦ (w, e) ∈ J p ∧ (w, e) ∈ J a ∨ (w, e) ∉ J p ∧ ρS e [] p a := by
  simp only [resolve, Schlenker2009.resolve, resolve_iff_of_occurrences J hR]

/-- A predicate of scopes is constant over the resolutions of a trigger iff it is constant over
the scopes that agree with the assertion where the presupposition holds. -/
private theorem forall_resolution_iff {P A : E → Prop} (G : (E → Prop) → Prop) :
    (∀ ρ ρ' : E → Prop,
      G (fun e ↦ P e ∧ A e ∨ ¬ P e ∧ ρ e) ↔ G (fun e ↦ P e ∧ A e ∨ ¬ P e ∧ ρ' e)) ↔
    ∀ D D' : E → Prop, (∀ e, P e → (D e ↔ A e)) → (∀ e, P e → (D' e ↔ A e)) →
      (G D ↔ G D') := by
  have key {D : E → Prop} (hD : ∀ e, P e → (D e ↔ A e)) :
      (fun e ↦ P e ∧ A e ∨ ¬ P e ∧ D e) = D := funext fun e ↦ propext <| by
    by_cases h : P e
    · simp [h, hD e h]
    · simp [h]
  refine ⟨fun h D D' hD hD' ↦ ?_, fun h ρ ρ' ↦ h _ _ (fun e he ↦ by simp [he])
    fun e he ↦ by simp [he]⟩
  rw [← key hD, ← key hD']
  exact h D D'

/-- A clause whose scope is a trigger and whose restrictor holds none is the one clause either
reading evaluates, since the trigger is final. -/
theorem completions_trigger (hR : R.occurrences = []) (r : Reading) :
    completions r ⟨q, R, .trigger p a⟩ = {⟨q, R, .trigger p a⟩} := by
  ext X
  simp only [completions, QuantifiedClause.occurrences, hR, Formula.occurrences, List.map_nil,
    List.nil_append, List.map_cons, List.mem_singleton, exists_eq_left, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨⟨q', a', K'⟩, hk, hX⟩ ↦ hX ▸ ?_, fun hX ↦ ⟨⟨q, .scope R, []⟩, ?_, hX⟩⟩
  · cases r
    · obtain ⟨⟨rfl, ha, hK⟩, -⟩ := hk
      cases ha
      cases hK
      rfl
    · cases hk
      rfl
  · cases r
    · exact ⟨⟨rfl, .scope R, .nil⟩, fun _ _ h ↦ by simp at h, fun _ h ↦ by cases h⟩
    · rfl

/-- A clause whose scope is a trigger and whose restrictor holds none is Kleene acceptable, on
either reading, iff the trigger is transparent at its assertion. -/
theorem kleeneAcceptable_trigger_iff (hR : R.occurrences = []) (r : Reading) :
    KleeneAcceptable J r C ⟨q, R, .trigger p a⟩ ↔
      TransparentAt C {scopeTruth q fun w e ↦ (w, e) ∈ R.truth J} (J p) (J a) := by
  simp only [KleeneAcceptable, completions_trigger hR, Set.mem_singleton_iff, forall_eq]
  rw [transparentAt_scopeTruth_iff]
  refine forall₂_congr fun w _ ↦ Iff.trans ?_ (forall_resolution_iff _)
  simp only [TokenDefined, resolve_trigger_iff J hR]
  exact ⟨fun h ρ ρ' ↦ h (fun _ _ _ _ ↦ True) (fun e _ _ _ ↦ ρ e) (fun _ _ _ _ ↦ True)
    (fun e _ _ _ ↦ ρ' e), fun h _ ρS _ ρS' ↦ h (ρS · [] p a) (ρS' · [] p a)⟩

/-- A clause whose scope is a trigger and whose restrictor holds none is super acceptable, on either
reading, iff the trigger is transparent at its assertion. -/
theorem superAcceptable_trigger_iff (hR : R.occurrences = []) (r : Reading) :
    SuperAcceptable J r C ⟨q, R, .trigger p a⟩ ↔
      TransparentAt C {scopeTruth q fun w e ↦ (w, e) ∈ R.truth J} (J p) (J a) := by
  simp only [SuperAcceptable, completions_trigger hR, Set.mem_singleton_iff, forall_eq]
  rw [transparentAt_scopeTruth_iff]
  refine forall₂_congr fun w _ ↦ Iff.trans ?_ (forall_resolution_iff _)
  simp only [SuperDefined, resolve_trigger_iff J hR]
  exact ⟨fun h ρ ρ' ↦ h (fun e _ _ ↦ ρ e) (fun e _ _ ↦ ρ' e),
    fun h σ σ' ↦ h (σ · p a) (σ' · p a)⟩

end Trigger

end QuantifiedClause

end QuantifiedClause

end Schlenker2009
