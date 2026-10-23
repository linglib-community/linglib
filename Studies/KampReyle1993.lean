module

public import Linglib.Semantics.Dynamic.DRS.Dynamics
public import Linglib.Semantics.Dynamic.DRS.Accessibility
public import Linglib.Core.Data.Fin.VecNotation

/-!
# Kamp and Reyle (1993): From Discourse to Logic

A discourse is interpreted by constructing a discourse representation structure (DRS), and a DRS
is verified by an embedding of its referents into a model. The worked examples are evaluated
through `DRS.trueRel`, Muskens's relational truth, which is the existential closure of the book's
Def. 1.4.5.

## Main statements

* `ulysses_tc`: *Jones owns Ulysses. It fascinates him.* (1.1) is true of a single owning pair,
  the pronoun equations adding no quantificational force.
* `porsche_tc`, `porsche_referent_inaccessible`: *Jones does not own a Porsche.* (1.56) denies a
  verifying extension, and the referent under the negation is inaccessible from the top level.
* `donkey_universal_reading`, `donkeyPronoun_agree`: *If a farmer owns a donkey he beats it.*
  (2.47) gets its universal reading from the verification clause for `⇒`, whether or not the
  pronoun has a referent of its own.

## Implementation notes

The truth conditions are claims over arbitrary models, proved by unfolding the verifying
embeddings; sequencing a discourse is `DRS.merge`, whose dynamics is the Merging Lemma
`DRS.toRel_merge`. Names enter a DRS as the unary conditions the construction algorithm writes
for them.

## References

* [kamp-reyle-1993]
* [muskens-1996]
* [geurts-beaver-maier-2024]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

namespace KampReyle1993

/-- The relation symbols of the worked examples; names (`jones`, `ulysses`, `porsche`)
enter as the unary conditions the construction algorithm writes for them (`Jones(x)`). -/
inductive KRRel : ℕ → Type
  | jones : KRRel 1 | ulysses : KRRel 1 | porsche : KRRel 1
  | farmer : KRRel 1 | donkey : KRRel 1
  | owns : KRRel 2 | fascinates : KRRel 2 | beats : KRRel 2

/-- The first-order language of the examples (no functions). -/
def krLang : Language := ⟨fun _ ↦ Empty, KRRel⟩

open DRT

variable {M : Type*} [krLang.Structure M]

/-- `RelMap` with the language pinned (a relation symbol alone does not determine
`L`). Lets truth-conditions read as `rm .farmer ![e]`. -/
abbrev rm {n} (R : krLang.Relations n) (x : Fin n → M) : Prop := Structure.RelMap R x

/-! ### Names and pronouns: "Jones owns Ulysses. It fascinates him." (1.1) -/

/-- The completed §1.1 DRS of (1.1),
`[u₁ u₂ u₃ u₄ | Jones u₁, Ulysses u₂, u₁ owns u₂, u₃ = u₂, u₄ = u₁, u₃ fascinates u₄]`. Each name
and pronoun introduces a referent, and the (1.17)-style equations resolve *it* and *him* to the
first sentence's referents. -/
def ulyssesDiscourse : DRS krLang ℕ :=
  .mk {1, 2, 3, 4} [.atom ⟨.jones, ![1]⟩, .atom ⟨.ulysses, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩,
    .eq 3 2, .eq 4 1, .atom ⟨.fascinates, ![3, 4]⟩]

/-- The (1.1) discourse is true iff a single pair verifies both sentences. -/
theorem ulysses_tc (a : ℕ → M) :
    DRS.trueRel ulyssesDiscourse a ↔
      ∃ x y : M, rm .jones ![x] ∧ rm .ulysses ![y] ∧ rm .owns ![x, y] ∧
        rm .fascinates ![y, x] := by
  simp only [DRS.trueRel_iff, ulyssesDiscourse, DRS.toRel_iff, Box.Extends,
    verifies_mk, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, verifies_atom, Language.Atom.realize_mk, verifies_eq, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, hj, hu, ho, h32, h41, hf⟩
    rw [h32, h41] at hf
    exact ⟨a' 1, a' 2, hj, hu, ho, hf⟩
  · rintro ⟨x, y, hj, hu, ho, hf⟩
    exact ⟨fun n ↦ match n with | 1 => x | 2 => y | 3 => y | 4 => x | n => a n,
      fun z hz ↦ by dsimp only; split <;> simp_all, hj, hu, ho, rfl, rfl, hf⟩

/-- The completed (1.1) DRS is proper (Def. 1.4.2–1.4.3), every referent its conditions use
being introduced by the discourse itself. -/
theorem ulysses_proper : ulyssesDiscourse.IsProper := by decide

/-! ### Negation blocks anaphora: "Jones does not own a Porsche." (1.56) -/

/-- The box under `¬` in (1.57) is `[u₂ | Porsche u₂, u₁ owns u₂]`. -/
def porscheNeg : DRS krLang ℕ := .mk {2} [.atom ⟨.porsche, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩]

/-- The DRS (1.57) of (1.56), `[u₁ | Jones u₁, ¬[u₂ | Porsche u₂, u₁ owns u₂]]`, introduces
the indefinite's referent *inside* the negation. -/
def porscheDiscourse : DRS krLang ℕ := .mk {1} [.atom ⟨.jones, ![1]⟩, .neg porscheNeg]

/-- (1.57) is true when there is no Porsche that Jones owns, the negated box being verified by
the non-existence of a verifying extension. -/
theorem porsche_tc (a : ℕ → M) :
    DRS.trueRel porscheDiscourse a ↔
      ∃ x : M, rm .jones ![x] ∧ ¬ ∃ y : M, rm .porsche ![y] ∧ rm .owns ![x, y] := by
  simp only [DRS.trueRel_iff, porscheDiscourse, porscheNeg, DRS.toRel_iff, Box.Extends,
    verifies_mk, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, verifies_neg, verifies_atom, Language.Atom.realize_mk, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, hj, hneg⟩
    exact ⟨a' 1, hj, fun ⟨y, hp, ho⟩ ↦ hneg
      ⟨fun n ↦ match n with | 2 => y | n => a' n,
        fun z hz ↦ by dsimp only; split <;> simp_all, hp, ho⟩⟩
  · rintro ⟨x, hj, hn⟩
    refine ⟨fun n ↦ match n with | 1 => x | n => a n,
      fun z hz ↦ by dsimp only; split <;> simp_all, hj, fun ⟨g, hag, hp, ho⟩ ↦ hn ⟨g 2, hp, ?_⟩⟩
    rw [hag 1 (by simp)] at ho
    exact ho

/-- From the top-level position, the referent trapped under `¬` is not accessible
(Def. 2.1.3) — the reason a continuation "*It fascinates him." cannot resolve *it*. -/
theorem porsche_referent_inaccessible : ¬ DRS.Accessible porscheDiscourse 1 2 := by
  decide

/-- Accessibility looks left and up, so from inside the negation the outer referent is
accessible, the asymmetry of Def. 2.1.3. -/
theorem outer_referent_accessible : DRS.Accessible porscheDiscourse 2 1 := by
  decide

/-- A continuation resolved to the trapped referent anyway is improper (Def. 1.4.2–1.4.3), since
merging *It fascinates him* with *it* forced to `u₂` leaves `u₂` free. -/
theorem continuation_improper :
    ¬ (porscheDiscourse.merge (.mk ∅ [.atom ⟨.fascinates, ![2, 1]⟩])).IsProper := by
  decide

/-! ### Donkey anaphora: "If a farmer owns a donkey he beats it." (2.47) -/

/-- The antecedent box `[u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂]`. -/
def donkeyAnte : DRS krLang ℕ :=
  .mk {1, 2} [.atom ⟨.farmer, ![1]⟩, .atom ⟨.donkey, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩]
/-- The consequent box `[ | beats u₁ u₂]` (pronouns resolved directly, (2.44)-style). -/
def donkeyCons : DRS krLang ℕ := .mk ∅ [.atom ⟨.beats, ![1, 2]⟩]
/-- (2.47) as `[ | donkeyAnte ⇒ donkeyCons]`. -/
def donkey : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyCons]

/-- By the verification clause for `⇒` ((2.31), Def. 2.1.4), the donkey sentence is true iff every
owning farmer–donkey pair satisfies `beats`. -/
theorem donkey_universal_reading (a : ℕ → M) :
    DRS.trueRel donkey a ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  simp only [DRS.trueRel_iff, donkey, donkeyAnte, donkeyCons, DRS.toRel_iff, Box.Extends,
    verifies_mk, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, verifies_imp, verifies_atom, Language.Atom.realize_mk,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, himp⟩ e₁ e₂ ⟨hf, hd, ho⟩
    obtain ⟨v'', hag, hb⟩ := himp (fun n ↦ match n with | 1 => e₁ | 2 => e₂ | n => a' n)
      (fun z hz ↦ by split <;> simp_all) ⟨hf, hd, ho⟩
    simpa [hag 1 (by simp), hag 2 (by simp)] using hb
  · intro hall
    exact ⟨a, fun _ _ ↦ rfl, fun v' _ ⟨hf, hd, ho⟩ ↦
      ⟨v', fun _ _ ↦ rfl, hall (v' 1) (v' 2) ⟨hf, hd, ho⟩⟩⟩

theorem donkey_proper : donkey.IsProper := by decide

/-- The (2.45)-style consequent `[u₃ | u₃ = u₂, beats u₁ u₃]`, in which the pronoun *it*
introduces its own referent, resolved to the donkey by an equation. -/
def donkeyPronounCons : DRS krLang ℕ := .mk {3} [.eq 3 2, .atom ⟨.beats, ![1, 3]⟩]
/-- (2.47) with the pronoun completed by referent-plus-equation. -/
def donkeyPronoun : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyPronounCons]

theorem donkeyPronoun_tc (a : ℕ → M) :
    DRS.trueRel donkeyPronoun a ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  simp only [DRS.trueRel_iff, donkeyPronoun, donkeyAnte, donkeyPronounCons, DRS.toRel_iff,
    Box.Extends, verifies_mk, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, verifies_imp, verifies_atom, Language.Atom.realize_mk,
    verifies_eq, Matrix.comp_vecCons, Matrix.comp_vecEmpty, and_true]
  constructor
  · rintro ⟨a', -, himp⟩ e₁ e₂ ⟨hf, hd, ho⟩
    obtain ⟨v'', hag, h32, hb⟩ := himp (fun n ↦ match n with | 1 => e₁ | 2 => e₂ | n => a' n)
      (fun z hz ↦ by split <;> simp_all) ⟨hf, hd, ho⟩
    rw [h32] at hb
    simpa [hag 1 (by simp), hag 2 (by simp)] using hb
  · intro hall
    exact ⟨a, fun _ _ ↦ rfl, fun v' _ ⟨hf, hd, ho⟩ ↦
      ⟨fun n ↦ match n with | 3 => v' 2 | n => v' n,
        fun z hz ↦ by dsimp only; split <;> simp_all, rfl, hall (v' 1) (v' 2) ⟨hf, hd, ho⟩⟩⟩

/-- Completing the pronoun directly or by a referent and an equation gives the same truth
conditions, (2.44) and (2.45). -/
theorem donkeyPronoun_agree (a : ℕ → M) :
    DRS.trueRel donkeyPronoun a ↔ DRS.trueRel donkey a :=
  (donkeyPronoun_tc a).trans (donkey_universal_reading a).symm

/-! ### Subordination and accessibility geometry -/

/-- The antecedent box is directly subordinate to the donkey DRS (Def. 1.4.10 as
extended by Def. 2.1.2). -/
theorem donkey_antecedent_subordinate : DirectlySubordinate donkeyAnte donkey :=
  .impAnte (c := donkeyCons) (by simp [donkey])

theorem donkey_consequent_subordinate : DirectlySubordinate donkeyCons donkey :=
  .impCons (a := donkeyAnte) (by simp [donkey])

/-- The antecedent is accessible to the consequent ([geurts-beaver-maier-2024]
§4.2) — the geometry that licenses the donkey anaphora. -/
theorem donkey_antecedent_accessible : AccessibleTo donkey donkeyAnte donkeyCons :=
  ⟨[donkeyCons, donkeyAnte, donkey], .single (.impCons (by simp [donkey])), by simp⟩

theorem donkey_not_consequent_accessible : ¬ AccessibleTo donkey donkeyCons donkeyAnte := by
  rintro ⟨bs, h, hmem⟩
  rw [Occurrence, ← DRS.mem_occurrences_iff] at h
  simp only [DRS.occurrences, donkey, Condition.occurrencesList, Condition.occurrences_imp,
    List.append_nil, List.mem_cons, List.mem_append, Prod.mk.injEq] at h
  rcases h with ⟨-, h⟩ | (⟨rfl, -⟩ | h) | ⟨-, h⟩ | h
  · simpa [donkeyAnte] using congrArg Box.referents h
  · rcases List.mem_cons.1 hmem with h | h
    · exact absurd (congrArg Box.referents h) (by decide)
    · simpa [donkeyCons] using congrArg Box.conditions (List.mem_singleton.1 h)
  · simp [donkeyAnte, Condition.occurrencesList, Condition.occurrences] at h
  · simpa [donkeyAnte, donkeyCons] using congrArg Box.referents h
  · simp [donkeyCons, Condition.occurrencesList, Condition.occurrences] at h

/-! ### Model evaluation: the donkey conditional in concrete models

Positive: a two-element domain where farmer `0` owns and beats donkey `1`. Negative: a
domain where the owning pair goes unbeaten falsifies the conditional. -/

instance : krLang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args ↦ args 0 = 0
    | 1, .donkey => fun args ↦ args 0 = 1
    | 2, .owns => fun args ↦ args 0 = 0 ∧ args 1 = 1
    | 2, .beats => fun args ↦ args 0 = 0 ∧ args 1 = 1
    | _, _ => fun _ ↦ False

/-- The donkey conditional is true in this model, whose only owning pair `(0, 1)` is a beating
pair. -/
theorem donkey_true_in_model (a : ℕ → Fin 2) : DRS.trueRel donkey a := by
  rw [donkey_universal_reading]
  rintro e₁ e₂ ⟨hf, hd, -⟩
  exact ⟨hf, hd⟩

instance : krLang.Structure Bool where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args ↦ args 0 = false
    | 1, .donkey => fun args ↦ args 0 = true
    | 2, .owns => fun args ↦ args 0 = false ∧ args 1 = true
    | _, _ => fun _ ↦ False

theorem donkey_false_in_model (a : ℕ → Bool) : ¬ DRS.trueRel donkey a := by
  rw [donkey_universal_reading]
  exact fun h ↦ h false true ⟨rfl, rfl, rfl, rfl⟩

end KampReyle1993
