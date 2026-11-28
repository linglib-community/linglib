/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Embedding.NegRaising.Inquisitive
public import Linglib.Languages.English.Verbs.Inventory
public import Linglib.Languages.English.Complementizers
public import Linglib.Data.Examples.TheilerEtAl2019
public import Linglib.Data.Examples.Readers

/-!
# Theiler, Roelofsen and Aloni (2019): Picky predicates

A declarative and an interrogative complement denote objects of one type, an inquisitive
proposition, and a clause-embedding predicate applies to either. A declarative complement is never
inquisitive and an interrogative complement is never informative. A predicate that rejects one of
the two does so because its meaning is trivial there: true wherever it is defined, or true
nowhere.

*Be certain* holds where the subject's doxastic state resolves the complement. A neg-raising
predicate over a modal base presupposes that the base resolves the polar question of the
complement and asserts that it resolves the complement. With a declarative complement the
presupposition is the excluded middle, and a denial yields the lowered reading. With an
interrogative complement the presupposition and the assertion coincide. *Be true* is resolution
by the state that knows the world, which every interrogative complement satisfies. *Wonder* holds
where the doxastic state does not resolve the complement and the inquisitive state lies below it,
which no declarative complement allows, and *depend on* requires two alternatives of each
argument.

## Main definitions

* `TheilerEtAl2019.wonder`: the worlds where an agent wonders about a proposition.
* `TheilerEtAl2019.dependsOn`: the worlds where one proposition depends on another relative to a
  modal base.
* `TheilerEtAl2019.negRaising`: the neg-raising predicate whose presupposition is stated with the
  operator that ensures inquisitiveness.
* `TheilerEtAl2019.Trivial`: a predicate of a class has one truth value, wherever defined, with
  every complement of a type.

## Implementation notes

The type of a row's clause is read from the spans that mark it: a complementizer's entry says
which sentence types it marks, and an interrogative phrase marks a constituent interrogative. A
complement type is the set of propositions a complement of that type may denote: those that are
not inquisitive for a declarative, those with no informative content for an interrogative, and
those both inquisitive and informative for a declarative conjoined with an interrogative.
Triviality quantifies over every model on every type of worlds, a model giving the subject's
doxastic and inquisitive states.

The article gives *be certain* as its entry for a responsive predicate and *know* as its example
of one, so *know* is classed with *be certain*. *Be certain* and *be true* are adjectives and have
no entry in the language file; the rows that test them are predicted by their class alone.

The function of *depend on* is defined on every set of worlds and constrained on the alternatives
of its argument.

## TODO

The suspension of the neg-raising inference in context, and the unacceptability of an
interrogative complement there, are not formalized, since they turn on local accommodation. The
sentences with *believe* and an interrogative complement that the article sets aside are not
recorded, nor are the presuppositional questions of its last appendix. *Feel* in its neg-raising
sense and *be likely* have no entry.

## References

* [theiler-etal-2019]
* [ciardelli-roelofsen-2015]
* [ciardelli-2016]
* [gajewski-2002]
* [gajewski-2007]
* [bartsch-1973]
-/

@[expose] public section

namespace TheilerEtAl2019

open Inquisitive Inquisitive.Proposition

variable {W : Type*} {M dox σ : W → Set W} {inq : W → Proposition (Set W)}
  {P P' : Proposition (Set W)} {p : Set W} {w : W}

/-! ### Responsive predicates -/

-- (9): *be certain* of a question holds where the doxastic state lies within one of its
-- alternatives
theorem mem_resolvedBy_generate {Q : Set (Set W)} :
    w ∈ (generate Q).resolvedBy dox ↔ dox w = ∅ ∨ ∃ p ∈ Q, dox w ⊆ p :=
  mem_generate

/-! ### Neg-raising predicates -/

-- the definition of inquisitive negation
theorem mem_compl_iff (P : Proposition (Set W)) (p : Set W) :
    p ∈ Pᶜ ↔ ∀ q ∈ P, q ∩ p = ∅ := by
  rw [compl_eq, mem_ofSet]
  refine ⟨fun h q hq ↦ Set.eq_empty_of_forall_notMem fun u ⟨huq, hup⟩ ↦ h hup ⟨q, hq, huq⟩,
    fun h u hu ⟨q, hq, huq⟩ ↦ ?_⟩
  exact Set.notMem_empty u (h q hq ▸ ⟨huq, hu⟩)

-- (19), (30): *believe* over the doxastic state, defined where the state resolves the complement
-- or its negation
theorem ofModalBase_ne_undefined_iff :
    NegRaising.ofModalBase dox P w ≠ .undefined ↔ dox w ∈ P ∨ dox w ∈ Pᶜ :=
  NegRaising.ofModalBase_ne_undefined_iff

-- (15)
theorem subset_compl_of_ofModalBase_ofSet_eq_false
    (h : NegRaising.ofModalBase dox (ofSet p) w = .false) : dox w ⊆ pᶜ :=
  (NegRaising.ofModalBase_ofSet_eq_false_iff.1 h).1

-- (20), (31), (33)
theorem ofModalBase_query_eq_true (M : W → Set W) (P : Proposition (Set W)) (w : W)
    (hd : NegRaising.ofModalBase M P.query w ≠ .undefined) :
    NegRaising.ofModalBase M P.query w = .true :=
  NegRaising.ofModalBase_query_eq_true hd

-- with a declarative complement the predicate is not trivial
theorem exists_ofModalBase_ofSet_eq_false :
    ∃ (M : Bool → Set Bool) (p : Set Bool) (w : Bool),
      NegRaising.ofModalBase M (ofSet p) w = .false :=
  ⟨fun _ ↦ {false}, {true}, true, NegRaising.ofModalBase_ofSet_eq_false_iff.2 (by simp)⟩

/-! ### Truth-evaluating predicates -/

theorem resolvedBy_singleton_of_info_eq_univ (h : P.info = Set.univ) :
    P.resolvedBy (fun w ↦ {w}) = Set.univ := by
  rw [resolvedBy_singleton, h]

-- *be false* holds nowhere of such a complement
theorem compl_resolvedBy_singleton_of_info_eq_univ (h : P.info = Set.univ) :
    (P.resolvedBy fun w ↦ {w})ᶜ = ∅ := by
  rw [resolvedBy_singleton_of_info_eq_univ h, Set.compl_univ]

/-! ### Rogative predicates -/

/-- An agent wonders about `P` where her doxastic state does not resolve `P` and her inquisitive
state lies below `P`. -/
def wonder (dox : W → Set W) (inq : W → Proposition (Set W)) (P : Proposition (Set W)) : Set W :=
  (P.resolvedBy dox)ᶜ ∩ P.entertainedBy inq

theorem wonder_ofSet (h : ∀ w, (inq w).info = dox w) (p : Set W) :
    wonder dox inq (ofSet p) = ∅ := by
  ext w
  simp [wonder, entertainedBy_ofSet, h]

-- an agent can wonder about a question
theorem exists_mem_wonder :
    ∃ (dox : Bool → Set Bool) (inq : Bool → Proposition (Set Bool)) (P : Proposition (Set Bool))
      (w : Bool), (∀ w, (inq w).info = dox w) ∧ w ∈ wonder dox inq P := by
  refine ⟨fun _ ↦ Set.univ, fun _ ↦ (ofSet {true}).query, (ofSet {true}).query, true,
    fun _ ↦ info_query _, ?_, mem_entertainedBy.2 le_rfl⟩
  simp only [Set.mem_compl_iff, mem_resolvedBy, query_eq_sup_compl, compl_eq, info_ofSet, mem_sup,
    mem_ofSet, not_or]
  exact ⟨fun h ↦ Bool.false_ne_true (h (Set.mem_univ false)), fun h ↦ h (Set.mem_univ true) rfl⟩

/-- `P` depends on `P'` relative to the modal base `σ` where some function from the alternatives
of `P'` to those of `P` takes every state of `σ` within an alternative into its value, and takes
two alternatives compatible with `σ` to different values. -/
def dependsOn (σ : W → Set W) (P' P : Proposition (Set W)) : Set W :=
  {w | ∃ f : Set W → Set W, (∀ a ∈ alt P', f a ∈ alt P) ∧
    (∀ q ⊆ σ w, ∀ a ∈ alt P', q ⊆ a → q ⊆ f a) ∧
    ∃ a ∈ alt P', ∃ a' ∈ alt P', (a ∩ σ w).Nonempty ∧ (a' ∩ σ w).Nonempty ∧ f a ≠ f a'}

theorem dependsOn_eq_empty_of_subsingleton_alt (h : (alt P).Subsingleton ∨ (alt P').Subsingleton) :
    dependsOn σ P' P = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro w ⟨f, hf, -, a, ha, a', ha', -, -, hne⟩
  refine hne ?_
  rcases h with h | h
  · exact h (hf a ha) (hf a' ha')
  · rw [h ha ha']

-- (42), (43): a declarative in either argument
theorem dependsOn_ofSet_right (σ : W → Set W) (P' : Proposition (Set W)) (p : Set W) :
    dependsOn σ P' (ofSet p) = ∅ :=
  dependsOn_eq_empty_of_subsingleton_alt (.inl (alt_ofSet p ▸ Set.subsingleton_singleton))

theorem dependsOn_ofSet_left (σ : W → Set W) (p : Set W) (P : Proposition (Set W)) :
    dependsOn σ (ofSet p) P = ∅ :=
  dependsOn_eq_empty_of_subsingleton_alt (.inr (alt_ofSet p ▸ Set.subsingleton_singleton))

/-! ### Complements conjoining a declarative with an interrogative -/

open Classical in
/-- (46): the operator that ensures inquisitiveness turns a proposition that is not inquisitive
into its polar question and leaves an inquisitive one as it is. -/
noncomputable def ensureInquisitive (P : Proposition (Set W)) : Proposition (Set W) :=
  if P.IsInquisitive then P else P.query

open Classical in
/-- (48): the neg-raising predicate whose presupposition is that the modal base resolves the
complement made inquisitive. -/
noncomputable def negRaising (M : W → Set W) (P : Proposition (Set W)) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ w ∈ (ensureInquisitive P).resolvedBy M) fun w ↦ w ∈ P.resolvedBy M

-- (49): of a complement that is not inquisitive it is the neg-raising predicate of (47)
theorem negRaising_of_not_isInquisitive (h : ¬ P.IsInquisitive) :
    negRaising M P = NegRaising.ofModalBase M P := by
  have he : ensureInquisitive P = P.query := if_neg h
  unfold negRaising NegRaising.ofModalBase
  rw [he]

open Classical in
-- (50): of an inquisitive complement it asserts what it presupposes
theorem negRaising_eq_true_of_isInquisitive (h : P.IsInquisitive)
    (hd : negRaising M P w ≠ .undefined) : negRaising M P w = .true := by
  have hq : w ∈ P.resolvedBy M := by
    by_contra hn
    exact hd (Trivalent.condEvent_eq_undefined_iff.2 (by simpa [ensureInquisitive, h] using hn))
  exact Trivalent.condEvent_eq_true_iff.2 ⟨by simpa [ensureInquisitive, h] using hq, hq⟩

theorem negRaising_eq_true_of_info_eq_univ (h : P.info = Set.univ)
    (hd : negRaising M P w ≠ .undefined) : negRaising M P w = .true := by
  by_cases hi : P.IsInquisitive
  · exact negRaising_eq_true_of_isInquisitive hi hd
  · rw [negRaising_of_not_isInquisitive hi] at hd ⊢
    exact NegRaising.ofModalBase_eq_true_of_info_eq_univ h hd

/-! ### The predicates and their complements -/

/-- A model gives the subject a doxastic state at each world and an inquisitive state with that
informative content. -/
structure Model (W : Type*) where
  /-- The doxastic state at each world. -/
  dox : W → Set W
  /-- The inquisitive state at each world. -/
  inq : W → Proposition (Set W)
  info_inq : ∀ w, (inq w).info = dox w

/-- The model whose subject entertains no issue beyond what she believes. -/
def Model.ofDox (dox : W → Set W) : Model W := ⟨dox, fun w ↦ ofSet (dox w), fun _ ↦ info_ofSet _⟩

/-- The model whose subject entertains `P` everywhere and believes its informative content. -/
def Model.ofIssue (P : Proposition (Set W)) : Model W := ⟨fun _ ↦ P.info, fun _ ↦ P, fun _ ↦ rfl⟩

/-- The classes of predicate with one clausal argument that the article gives an entry. -/
inductive PredicateClass
  /-- *Be certain*, (7). -/
  | responsive
  /-- *Believe*, (48). -/
  | negRaising
  /-- *Be true*, (36). -/
  | truthEvaluating
  /-- *Wonder*, (37). -/
  | inquisitive
  deriving DecidableEq, Repr

open Classical in
/-- The meaning of a predicate of each class with a complement, in a model. -/
noncomputable def PredicateClass.meaning :
    PredicateClass → Model W → Proposition (Set W) → W → Trivalent
  | .responsive, m, P => fun w ↦ .ofProp (w ∈ P.resolvedBy m.dox)
  | .negRaising, m, P => TheilerEtAl2019.negRaising m.dox P
  | .truthEvaluating, _, P => fun w ↦ .ofProp (w ∈ P.info)
  | .inquisitive, m, P => fun w ↦ .ofProp (w ∈ wonder m.dox m.inq P)

/-- The types of complement the article distinguishes. -/
inductive Complement
  /-- A declarative clause. -/
  | declarative
  /-- An interrogative clause. -/
  | interrogative
  /-- A declarative conjoined with an interrogative. -/
  | mixed
  deriving DecidableEq, Repr

/-- The propositions a complement of each type denotes: a declarative is never inquisitive, an
interrogative never informative, and their conjunction is both informative and inquisitive. -/
def Complement.Denotes : Complement → Proposition (Set W) → Prop
  | .declarative, P => ¬ P.IsInquisitive
  | .interrogative, P => P.info = Set.univ
  | .mixed, P => P.IsInquisitive ∧ P.info ≠ Set.univ

/-- A predicate of class `k` with a complement of type `c` has the truth value `t` at some world
of some model. -/
def Attains (k : PredicateClass) (c : Complement) (t : Trivalent) : Prop :=
  ∃ (W : Type) (m : Model W) (P : Proposition (Set W)) (w : W), c.Denotes P ∧ k.meaning m P w = t

/-- A predicate with a complement of a given type is trivial when it has one truth value wherever
it is defined, in every model. -/
def Trivial (k : PredicateClass) (c : Complement) : Prop :=
  ¬ (Attains k c .true ∧ Attains k c .false)

section Witnesses

private abbrev S : Proposition (Set Bool) := ofSet {true}

private abbrev Q : Proposition (Set Bool) := (ofSet {true}).query

private abbrev X : Proposition (Set (Fin 3)) := ofSet {0} ⊔ ofSet {1}

private theorem denotes_S : Complement.declarative.Denotes S := not_isInquisitive_ofSet _

private theorem info_Q : Q.info = Set.univ := info_query _

private theorem isInquisitive_Q : Q.IsInquisitive :=
  isInquisitive_query (by simp [Set.ext_iff]) (by simp [Set.ext_iff])

private theorem isInquisitive_X : X.IsInquisitive :=
  isInquisitive_ofSet_sup_ofSet (by simp) (by simp)

private theorem info_X : X.info ≠ Set.univ := fun h ↦ by
  have h2 : (2 : Fin 3) ∈ X.info := h ▸ Set.mem_univ _
  simp at h2

private theorem denotes_X : Complement.mixed.Denotes X := ⟨isInquisitive_X, info_X⟩

theorem not_trivial_responsive (c : Complement) : ¬ Trivial .responsive c := by
  refine not_not.2 ?_
  cases c
  · exact ⟨⟨Bool, .ofDox fun _ ↦ {true}, S, true, denotes_S, by simp [PredicateClass.meaning,
      Model.ofDox]⟩, ⟨Bool, .ofDox fun _ ↦ {false}, S, true, denotes_S, by
      simp [PredicateClass.meaning, Model.ofDox]⟩⟩
  · exact ⟨⟨Bool, .ofDox fun _ ↦ {true}, Q, true, info_Q, by simp [PredicateClass.meaning,
      Model.ofDox]⟩, ⟨Bool, .ofDox fun _ ↦ Set.univ, Q, true, info_Q, by
      simp [PredicateClass.meaning, Model.ofDox, Set.ext_iff]⟩⟩
  · exact ⟨⟨Fin 3, .ofDox fun _ ↦ {0}, X, 0, denotes_X, by simp [PredicateClass.meaning,
      Model.ofDox]⟩, ⟨Fin 3, .ofDox fun _ ↦ {2}, X, 0, denotes_X, by
      simp [PredicateClass.meaning, Model.ofDox]⟩⟩

open Classical in
/-- A neg-raising predicate is trivial with every complement but a declarative. -/
theorem trivial_negRaising_iff (c : Complement) :
    Trivial .negRaising c ↔ c ≠ .declarative := by
  have key : ∀ {W : Type} {m : Model W} {P : Proposition (Set W)} {w : W},
      (P.IsInquisitive ∨ P.info = Set.univ) → PredicateClass.negRaising.meaning m P w ≠ .false :=
    fun {W m P w} h hf ↦ by
      have hf' : negRaising m.dox P w = .false := hf
      have hd : negRaising m.dox P w ≠ .undefined := by rw [hf']; simp
      have ht := h.elim (negRaising_eq_true_of_isInquisitive · hd)
        (negRaising_eq_true_of_info_eq_univ · hd)
      rw [hf'] at ht
      exact absurd ht (by simp)
  cases c
  · refine iff_of_false (not_not.2 ⟨⟨Bool, .ofDox fun _ ↦ {true}, S, true, denotes_S, ?_⟩,
      ⟨Bool, .ofDox fun _ ↦ {false}, S, true, denotes_S, ?_⟩⟩) (by simp)
    · rw [PredicateClass.meaning, negRaising_of_not_isInquisitive denotes_S]
      simp [NegRaising.ofModalBase, Model.ofDox]
    · rw [PredicateClass.meaning, negRaising_of_not_isInquisitive denotes_S]
      exact NegRaising.ofModalBase_ofSet_eq_false_iff.2 (by simp [Model.ofDox])
  · exact iff_of_true (fun ⟨_, _, _, _, _, hP, hf⟩ ↦ key (.inr hP) hf) (by simp)
  · exact iff_of_true (fun ⟨_, _, _, _, _, hP, hf⟩ ↦ key (.inl hP.1) hf) (by simp)

/-- A truth-evaluating predicate is trivial exactly with an interrogative complement. -/
theorem trivial_truthEvaluating_iff (c : Complement) :
    Trivial .truthEvaluating c ↔ c = .interrogative := by
  have key : ∀ {W : Type} {m : Model W} {P : Proposition (Set W)} {w : W}, P.info = Set.univ →
      PredicateClass.truthEvaluating.meaning m P w ≠ .false := fun h hf ↦ by
    simp [PredicateClass.meaning, h] at hf
  cases c
  · exact iff_of_false (not_not.2 ⟨⟨Bool, .ofDox fun _ ↦ ∅, S, true, denotes_S, by
      simp [PredicateClass.meaning]⟩, ⟨Bool, .ofDox fun _ ↦ ∅, S, false, denotes_S, by
      simp [PredicateClass.meaning]⟩⟩) (by simp)
  · exact iff_of_true (fun ⟨_, _, _, _, _, hP, hf⟩ ↦ key hP hf) (by simp)
  · exact iff_of_false (not_not.2 ⟨⟨Fin 3, .ofDox fun _ ↦ ∅, X, 0, denotes_X, by
      simp [PredicateClass.meaning]⟩, ⟨Fin 3, .ofDox fun _ ↦ ∅, X, 2, denotes_X, by
      simp [PredicateClass.meaning]⟩⟩) (by simp)

/-- An inquisitive predicate is trivial exactly with a declarative complement. -/
theorem trivial_inquisitive_iff (c : Complement) :
    Trivial .inquisitive c ↔ c = .declarative := by
  have wit : ∀ {W : Type} {P : Proposition (Set W)} (w : W), P.IsInquisitive →
      PredicateClass.inquisitive.meaning (.ofIssue P) P w = .true ∧
        PredicateClass.inquisitive.meaning (.ofDox fun _ ↦ ∅) P w = .false :=
    fun {W P} w h ↦ by
      constructor
      · simpa [PredicateClass.meaning, wonder, Model.ofIssue, IsInquisitive] using h
      · simp [PredicateClass.meaning, wonder, Model.ofDox, empty_mem]
  cases c
  · refine iff_of_true (fun ⟨⟨_, m, P, w, hP, ht⟩, _⟩ ↦ ?_) rfl
    have hP' : P = ofSet P.info := (info_mem_iff_eq_ofSet_info P).1 (not_not.1 hP)
    have hw : w ∈ wonder m.dox m.inq P := by simpa [PredicateClass.meaning] using ht
    rw [hP', wonder_ofSet m.info_inq] at hw
    exact hw
  · exact iff_of_false (not_not.2 ⟨⟨Bool, _, Q, true, info_Q, (wit true isInquisitive_Q).1⟩,
      ⟨Bool, _, Q, true, info_Q, (wit true isInquisitive_Q).2⟩⟩) (by simp)
  · exact iff_of_false (not_not.2 ⟨⟨Fin 3, _, X, 0, denotes_X, (wit 0 isInquisitive_X).1⟩,
      ⟨Fin 3, _, X, 0, denotes_X, (wit 0 isInquisitive_X).2⟩⟩) (by simp)

end Witnesses

instance (k : PredicateClass) (c : Complement) : Decidable (Trivial k c) :=
  match k with
  | .responsive => isFalse (not_trivial_responsive c)
  | .negRaising => decidable_of_iff _ (trivial_negRaising_iff c).symm
  | .truthEvaluating => decidable_of_iff _ (trivial_truthEvaluating_iff c).symm
  | .inquisitive => decidable_of_iff _ (trivial_inquisitive_iff c).symm

/-! ### The rows -/

open Examples (Example Lexeme)

/-- The class the article assigns each predicate under test that has one clausal argument. -/
def _root_.TheilerEtAl2019.Examples.Lexeme.class? : Lexeme → Option PredicateClass
  | .know | .beCertain => some .responsive
  | .believe | .think => some .negRaising
  | .beTrue => some .truthEvaluating
  | .wonder => some .inquisitive
  | .dependOn | .that | .whether => none

/-- The English verb of a predicate under test; the two adjectives have no entry. -/
def _root_.TheilerEtAl2019.Examples.Lexeme.verb? : Lexeme → Option English.Verbs.Verb
  | .know => some English.Verbs.know
  | .believe => some English.Verbs.believe
  | .think => some English.Verbs.think
  | .wonder => some English.Verbs.wonder
  | .dependOn => some English.Verbs.depend_on
  | .beCertain | .beTrue | .that | .whether => none

/-- The English complementizer a span names. -/
def _root_.TheilerEtAl2019.Examples.Lexeme.complementizer? : Lexeme → Option Complementizer
  | .that => some English.Complementizers.that
  | .whether => some English.Complementizers.whether
  | _ => none

/-- The type of a clause, from its complementizers and whether it has an interrogative phrase. A
complementizer that types declaratives gives the clause a declarative part, and one that types an
interrogative, or an interrogative phrase, gives it an interrogative part. -/
def Complement.ofMarkers (zs : List Complementizer) (wh : Bool) : Option Complement :=
  if (∃ z ∈ zs, .declarative ∈ z.types) ∧ (wh ∨ ∃ z ∈ zs, ∃ t ∈ z.types, t.IsInterrogative) then
    some .mixed
  else if ∃ z ∈ zs, .declarative ∈ z.types then some .declarative
  else if wh ∨ ∃ z ∈ zs, ∃ t ∈ z.types, t.IsInterrogative then some .interrogative
  else none

/-- The type of an example's complement clause, from the spans that mark it. -/
def _root_.TheilerEtAl2019.Examples.Example.complement? (x : Example) : Option Complement :=
  Complement.ofMarkers ((x.lexemes .complementizer).filterMap Lexeme.complementizer?)
    (x.datum.spans.any fun p ↦ Examples.label? p = some .wh)

/-- The type of an example's clausal subject. -/
def _root_.TheilerEtAl2019.Examples.Example.subject? (x : Example) : Option Complement :=
  Complement.ofMarkers ((x.lexemes .subjectComplementizer).filterMap Lexeme.complementizer?) false

/-- The rows the account leaves unexplained: *be true* and *wonder* with a declarative conjoined
with an interrogative, (44b) and (44c). -/
def unexplained : List Example := [.ex_44b, .ex_44c]

/-- A predicate is acceptable with a complement exactly when its class is not trivial with
complements of that type, the unexplained rows apart. -/
theorem acceptable_iff_not_trivial :
    ∀ x : Example, x ∉ unexplained → ∀ l ∈ x.lexemes .predicate, ∀ k ∈ l.class?,
      ∀ c ∈ x.complement?, (x.datum.judgment = .acceptable ↔ ¬ Trivial k c) := by
  decide +kernel

theorem unexplained_not_trivial :
    ∀ x ∈ unexplained, ∀ l ∈ x.lexemes .predicate, ∀ k ∈ l.class?, ∀ c ∈ x.complement?,
      x.datum.judgment ≠ .acceptable ∧ ¬ Trivial k c := by
  decide +kernel

-- (15): the lowered reading of a negated neg-raising predicate
theorem lowered_reading :
    Example.ex_15.reading .lowered = some .acceptable ↔
      ∀ (W : Type) (M : W → Set W) (p : Set W) (w : W),
        NegRaising.ofModalBase M (ofSet p) w = .false → M w ⊆ pᶜ :=
  iff_of_true rfl fun _ _ _ _ ↦ subset_compl_of_ofModalBase_ofSet_eq_false

/-! ### Dependency -/

/-- Something of type `c` depends on something of type `cs` at some world of some model. -/
def DependsSomewhere (cs c : Complement) : Prop :=
  ∃ (W : Type) (σ : W → Set W) (P' P : Proposition (Set W)) (w : W),
    cs.Denotes P' ∧ c.Denotes P ∧ w ∈ dependsOn σ P' P

private theorem subsingleton_alt_of_denotes {P : Proposition (Set W)}
    (h : Complement.declarative.Denotes P) : (alt P).Subsingleton := by
  rw [(info_mem_iff_eq_ofSet_info P).1 (not_not.1 h), alt_ofSet]
  exact Set.subsingleton_singleton

-- of a declarative and an interrogative in either argument, *depend on* holds somewhere exactly
-- when both are interrogative
theorem dependsSomewhere_iff {cs c : Complement} (hcs : cs ≠ .mixed) (hc : c ≠ .mixed) :
    DependsSomewhere cs c ↔ cs = .interrogative ∧ c = .interrogative := by
  cases cs <;> cases c <;> first | exact absurd rfl hcs | exact absurd rfl hc | skip
  · exact iff_of_false (fun ⟨_, σ, P', P, w, _, hP, hw⟩ ↦ by
      rw [dependsOn_eq_empty_of_subsingleton_alt (.inl (subsingleton_alt_of_denotes hP))] at hw
      exact hw) (by simp)
  · exact iff_of_false (fun ⟨_, σ, P', P, w, hP', _, hw⟩ ↦ by
      rw [dependsOn_eq_empty_of_subsingleton_alt (.inr (subsingleton_alt_of_denotes hP'))] at hw
      exact hw) (by simp)
  · exact iff_of_false (fun ⟨_, σ, P', P, w, _, hP, hw⟩ ↦ by
      rw [dependsOn_eq_empty_of_subsingleton_alt (.inl (subsingleton_alt_of_denotes hP))] at hw
      exact hw) (by simp)
  · refine iff_of_true ?_ ⟨rfl, rfl⟩
    have halt : alt ((ofSet ({true} : Set Bool)).query) = {{true}, {true}ᶜ} := by
      rw [query, info_ofSet]
      exact alt_ofSet_sup_ofSet (by simp) (by simp)
    refine ⟨Bool, fun _ ↦ Set.univ, (ofSet {true}).query, (ofSet {true}).query, true,
      info_query _, info_query _, id, fun _ h ↦ h,
      fun _ _ _ _ h ↦ h, {true}, ?_, {true}ᶜ, ?_, ?_, ?_, ?_⟩
    · rw [halt]; simp
    · rw [halt]; simp
    · simp
    · exact ⟨false, by simp⟩
    · simp [Set.ext_iff]

/-- A sentence with *depend on* is acceptable exactly when something of its complement's type
depends somewhere on something of its subject's type. -/
theorem acceptable_iff_dependsSomewhere :
    ∀ x : Example, ∀ cs ∈ x.subject?, ∀ c ∈ x.complement?,
      (x.datum.judgment = .acceptable ↔ DependsSomewhere cs c) := by
  have data : ∀ x : Example, ∀ cs ∈ x.subject?, ∀ c ∈ x.complement?,
      cs ≠ .mixed ∧ c ≠ .mixed ∧
        (x.datum.judgment = .acceptable ↔ cs = .interrogative ∧ c = .interrogative) := by
    decide +kernel
  intro x cs hcs c hc
  obtain ⟨h₁, h₂, h⟩ := data x cs hcs c hc
  exact h.trans (dependsSomewhere_iff h₁ h₂).symm

/-! ### The words of the rows and their entries -/

-- a verb's entry takes a complementizer exactly when the verb's class is not trivial with the
-- type of clause the complementizer marks
theorem takes_iff_not_trivial :
    ∀ l : Lexeme, ∀ v ∈ l.verb?, ∀ k ∈ l.class?,
      ∀ z ∈ [English.Complementizers.that, English.Complementizers.whether],
        ∀ c ∈ Complement.ofMarkers [z] false, (v.valency.Takes z ↔ ¬ Trivial k c) := by
  decide +kernel

-- *depend on* takes *whether* and not *that*
theorem dependOn_takes :
    English.Verbs.depend_on.valency.Takes English.Complementizers.whether ∧
      ¬ English.Verbs.depend_on.valency.Takes English.Complementizers.that := by
  decide +kernel

-- (11): the neg-raising verbs with an entry take no interrogative complementizer
theorem negRaisers_not_takes_whether :
    ∀ v ∈ [English.Verbs.believe, English.Verbs.think, English.Verbs.expect, English.Verbs.want,
      English.Verbs.seem], ¬ v.valency.Takes English.Complementizers.whether := by
  decide +kernel

/-- Words are a form of an English verb if the entry realizes them, spaced, in some cell. -/
def IsFormOf (ws : List (List Char)) (v : English.Verbs.Verb) : Prop :=
  ∃ c ∈ [English.Verbs.Verb.Cell.base, .thirdSg], [' '].intercalate ws = (v.realize c).toList

instance (ws : List (List Char)) (v : English.Verbs.Verb) : Decidable (IsFormOf ws v) :=
  inferInstanceAs (Decidable (∃ c ∈ _, _))

-- a span that names a verb is a form of its entry, and one that names a complementizer is the
-- complementizer's form, a capital apart
theorem english_forms :
    ∀ x : Example, ∀ p ∈ x.datum.spans, ∀ l ∈ Examples.lexeme? p,
      (∀ v ∈ l.verb?, IsFormOf ((p.words x.datum).map (·.word)) v) ∧
        ∀ z ∈ l.complementizer?,
          ∃ w ∈ (p.words x.datum).head?, w.word.map Char.toLower = z.form.toList := by
  decide +kernel

end TheilerEtAl2019
