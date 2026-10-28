module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Functor
public import Linglib.Semantics.Composition.Assignment
public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Quantification.Individual
public import Linglib.Semantics.Reference.ChoiceFunction
public import Studies.Charlow2014
public import Linglib.Data.Examples.Charlow2020

/-!
# Charlow (2020): the scope of alternatives

Charlow takes an indefinite to denote a set of individuals and lets it take scope through two
type-shifters: `η` forms a singleton, and `≫=` feeds the members of a set one by one to a scope
and unions the results. They are the unit and bind of the set monad. Because bind is associative,
an indefinite that takes scope at the edge of an island turns the island into a set of
alternatives, and the island can then take scope in its turn, which gives exceptional scope
without movement out of the island. Higher-order alternative sets let two indefinites on one
island take scope independently; with the alternatives in the types, the composition engine
[derives the island's two higher-order sets and their point-wise flattening](##translations_island)
without moving either indefinite. Once assignments are added to the monad, an indefinite whose
restrictor holds a bound pronoun cannot outscope the pronoun's binder.

## Main definitions

* `closureCond`, `det`, `distr`: the conditional (31), the determiners (65) and (84), and the
  distributivity operator (41), each closing off the alternatives of its scope.
* `lawyerOuter`, `relativeOuter`: the two higher-order islands of Figure 10.
* `Si.pro`, `Si.beta`, `Si.det`: pronouns (58), `β`-binding (61) and determiners over
  `ReaderT (Assignment E) Set`.
* `Si.a`, `Si.that`: the indefinite determiner (83) and the relative pronoun (87).
* `Si.abstractChoice`: abstraction by a choice function in alternative semantics (74).

## Implementation notes

* `η`, `≫=` and flattening are `pure`, `>>=` and `joinM` of mathlib's `Set.monad`, and the
  closure `⇓` (19) is `sSup` on `Set Prop`. Truth values are `Prop`, as in the paper's main text.
* The paper's conditional `if : t → t → t` is a parameter `cond`; the witnesses that separate
  readings use the material conditional. Pluralities are `Finset`s of atoms.
* A derivation is a term in the monad, and which constituent takes scope where is not
  represented, so a reading the paper rules out is shown to differ from the derived ones.
* `Si.cf_reading_iff` assumes that no two candidates wrote the same papers, which the paper's
  gloss of (69) needs and leaves implicit.
* `Si.abstractChoice` is the first line of (74); the composition engine's set effect abstracts by
  the second, and resolving words before interpretation gives the layering of (80) and (81) for
  lexical alternatives that do not depend on the assignment.

## Errata

* Footnote 25 says that the two lines of (74) are equivalent when every alternative set is
  nonempty, and (75) and (76) equate the first with a Skolemized choice function. A choice
  function picks the same member from equal sets, so values of the variable with the same
  alternatives receive the same one under the first line but not under the second; distinct
  alternatives at distinct values suffice for the two to agree (`Si.abstractChoice_eq_distribute`).
  With truth values as alternatives, two people who each met some but not all linguists already
  separate them: the first line gives `[λ₀ t₀ met a linguist]` the constant predicates, the second
  line and the right-hand side of (75) every predicate (`Si.abstractChoice_ne_distribute`,
  `Si.range_skolem_eq_distribute`). The verdict on (77) holds under either line
  (`Si.nobody_met_iff`, `Si.sSup_interp_nobodyMet_iff`).
* Figure 9 prints `die X` for `die x`.

## TODO

* (46), and point-wise composition with a closure inside the island (45) on (46) and (47).
* (78), whose `wrote x y` puts the paper second where (69) and (82) put it first.
* (79) and (82) on the composition engine, (88), and Appendix B.

## References

* [charlow-2020]
* [charlow-2014]
* [partee-1987]
* [reinhart-1997]
* [brasoveanu-farkas-2011]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

attribute [local instance] Set.monad

namespace Charlow2020

open Quantifier Quantifier.NP

-- (19)
theorem sSup_iff_true_mem (m : Set Prop) : sSup m ↔ True ∈ m := by
  rw [sSup_Prop_eq]
  exact ⟨fun ⟨p, hp, h⟩ ↦ eq_true h ▸ hp, fun h ↦ ⟨True, h, trivial⟩⟩

/-! ### The extended Partee triangle (Figure 4) -/

section Shifters

variable {α β : Type}

/-- `plusWh Q` is the `+wh` shifter (25), which turns a generalized quantifier into a scope-taker
over sets. -/
def plusWh (Q : NP α) (f : α → Set β) : Set β := {y | Q fun x ↦ y ∈ f x}

/-- Partee's `A`, existential closure over a set, sends a singleton to the Montague lift,
`A ∘ η = LIFT` (24). -/
theorem some_pure (x : α) : GQ.some (pure x : Set α) = individual x :=
  some_ident x

/-- Binding a singleton is the Montague lift at result type `Set β`, `(≫=) ∘ η = LIFT` (28). -/
theorem bind_pure_left (x : α) : (fun f : α → Set β ↦ pure x >>= f) = fun f ↦ f x :=
  funext (pure_bind x)

/-- Applying `+wh` to Partee's `A` gives bind, `+wh ∘ A = (≫=)` (29). -/
theorem plusWh_some (m : Set α) : plusWh (GQ.some m) = fun f : α → Set β ↦ m >>= f := by
  funext f; ext y; simp [plusWh, GQ.some, Set.bind_def]; rfl

-- Figure 4
theorem plusWh_individual (x : α) : plusWh (individual x) = fun f : α → Set β ↦ f x := by
  funext f; ext y; simp [plusWh, individual]

end Shifters

/-! ### Exceptional scope -/

section Conditional

variable {E : Type} (cond : Prop → Prop → Prop)

/-- `closureCond cond m n` is the conditional (31), `{if m⇓ n⇓}`, which closes off the
alternatives of both arguments. -/
def closureCond (m n : Set Prop) : Set Prop := pure (cond (sSup m) (sSup n))

/-- `det D P f` is the determiner `D` over `P` closing off the alternatives of its scope `f`, as
in (65) and (84) without assignments. -/
def det (D : GQ E) (P : Set E) (f : E → Set Prop) : Set Prop := pure (D (· ∈ P) fun x ↦ sSup (f x))

variable (rel : Set E) (dies : E → Prop) (house : Prop)

/-- Scoping over its island, which scopes over the conditional, gives the indefinite exceptional
scope ((33), `Examples.ex1`). -/
theorem exceptional_scope :
    (rel >>= fun x ↦ pure (dies x)) >>= (fun p ↦ closureCond cond (pure p) (pure house)) =
      (fun x ↦ cond (dies x) house) '' rel := by
  ext q; simp [closureCond, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

-- Figure 7
theorem exceptional_scope_eq_wide :
    (rel >>= fun x ↦ pure (dies x)) >>= (fun p ↦ closureCond cond (pure p) (pure house)) =
      rel >>= fun x ↦ closureCond cond (pure (dies x)) (pure house) := by
  simp only [bind_assoc, pure_bind]

-- (13)
theorem narrow_scope :
    closureCond cond (rel >>= fun x ↦ pure (dies x)) (pure house) =
      {cond (∃ x ∈ rel, dies x) house} := by
  simp [closureCond, Set.bind_def, sSup_Prop_eq, -eq_iff_iff]

/-- A universal closes its island off to a singleton, so pied-piping the island gives the narrow
reading again (2), as in `Examples.ex2`. -/
theorem every_island :
    det GQ.every rel (fun x ↦ pure (dies x)) >>= (fun p ↦ closureCond cond (pure p) (pure house)) =
      closureCond cond (det GQ.every rel fun x ↦ pure (dies x)) (pure house) := by
  simp [det, closureCond, sSup_singleton, -eq_iff_iff]

variable (student : Set E) (wrong : E → Prop) (argue : E → Prop → Prop)

/-- The island of (3) can scope over *three arguments showing that* and stop below *each
student*, as in `Examples.ex3`. -/
theorem intermediate_scope :
    det GQ.every student (fun y ↦ (rel >>= fun c ↦ pure (wrong c)) >>= fun p ↦ pure (argue y p)) =
      {∀ y ∈ student, ∃ c ∈ rel, argue y (wrong c)} := by
  simp [det, GQ.every, Set.bind_def, sSup_Prop_eq, -eq_iff_iff]

-- (3)
theorem widest_scope :
    (rel >>= fun c ↦ pure (wrong c)) >>= (fun p ↦ det GQ.every student fun y ↦ pure (argue y p)) =
      (fun c ↦ ∀ y ∈ student, argue y (wrong c)) '' rel := by
  ext q; simp [det, GQ.every, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

end Conditional

-- (3)
theorem intermediate_ne_widest : ¬ ∀ (student rel : Set Bool) (wrong : Bool → Prop)
    (argue : Bool → Prop → Prop),
    sSup (det GQ.every student fun y ↦ (rel >>= fun c ↦ pure (wrong c)) >>=
        fun p ↦ pure (argue y p)) ↔
      sSup ((rel >>= fun c ↦ pure (wrong c)) >>= fun p ↦ det GQ.every student fun y ↦
        pure (argue y p)) := by
  intro h
  have h := h Set.univ Set.univ (· = true) fun y p ↦ (p ↔ y = true)
  rw [intermediate_scope, widest_scope] at h
  simp [-eq_iff_iff] at h

/-- The exceptional and narrow readings of (1) differ. -/
theorem exceptional_ne_narrow : ¬ ∀ (rel : Set Bool) (dies : Bool → Prop) (house : Prop),
    sSup ((rel >>= fun x ↦ pure (dies x)) >>=
        fun p ↦ closureCond (· → ·) (pure p) (pure house)) ↔
      sSup (closureCond (· → ·) (rel >>= fun x ↦ pure (dies x)) (pure house)) := by
  intro h
  have h := h Set.univ (· = true) False
  simp only [exceptional_scope, narrow_scope, sSup_singleton, sSup_Prop_eq] at h
  exact h.1 ⟨_, ⟨false, trivial, rfl⟩, by simp⟩ ⟨true, trivial, rfl⟩

/-! ### Plural indefinites -/

section Plural

variable {A : Type} (cond : Prop → Prop → Prop) (house : Prop)

/-- `two P` is the set of pluralities of two atoms of `P`, as `two.rels` (40). -/
def two (P : Set A) : Set (Finset A) := {X | X.card = 2 ∧ ∀ x ∈ X, x ∈ P}

/-- `distr f` is the distributivity operator `∆` (41), which requires every atom of a plurality
to satisfy the closed scope `f`. -/
def distr (f : A → Set Prop) (X : Finset A) : Set Prop := pure (∀ x ∈ X, sSup (f x))

-- Figure 9
theorem two_wrote_something (ling something : Set A) (wrote : A → A → Prop) :
    two ling >>= distr (fun x ↦ something >>= fun y ↦ pure (wrote y x)) =
      (fun X ↦ ∀ x ∈ X, ∃ y ∈ something, wrote y x) '' two ling := by
  ext q; simp [distr, Set.bind_def, sSup_Prop_eq, eq_comm, -eq_iff_iff]

/-- In *if two relatives of mine die* the plural's existential scope leaves the island while `∆`
stays inside it (Figure 9, right), as in `Examples.ex39`. -/
theorem two_island (rel : Set A) (die : A → Prop) :
    (two rel >>= distr fun x ↦ pure (die x)) >>=
        (fun p ↦ closureCond cond (pure p) (pure house)) =
      (fun X ↦ cond (∀ x ∈ X, die x) house) '' two rel := by
  ext q; simp [distr, closureCond, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

-- (39)
theorem two_island_ne_distr_wide : ¬ ∀ (rel : Set Bool) (die : Bool → Prop) (house : Prop),
    sSup ((two rel >>= distr fun x ↦ pure (die x)) >>=
        fun p ↦ closureCond (· → ·) (pure p) (pure house)) ↔
      sSup (two rel >>= distr fun x ↦ closureCond (· → ·) (pure (die x)) (pure house)) := by
  intro h
  have h := h Set.univ (· = true) False
  simp [distr, closureCond, two, Set.bind_def, sSup_Prop_eq, sSup_singleton, -eq_iff_iff] at h
  obtain ⟨X, hX, ht⟩ := h.1 ⟨Finset.univ, rfl, Finset.mem_univ _⟩
  exact ht (Finset.eq_univ_of_card X (by simpa using hX) ▸ Finset.mem_univ _)

end Plural

/-! ### Selectivity -/

section Selectivity

variable {E : Type} (cond : Prop → Prop → Prop) (lawyer rel : Set E) (visits : E → E → Prop)
  (house : Prop)

/-- `lawyerOuter` is the higher-order island `{{visits y x | rel y} | lawyer x}` of Figure 10,
left, with the lawyer in the outer layer. -/
def lawyerOuter : Set (Set Prop) :=
  lawyer >>= fun x ↦ pure (rel >>= fun y ↦ pure (visits y x))

/-- `relativeOuter` is the higher-order island `{{visits y x | lawyer x} | rel y}` of Figure 10,
right, with the relative in the outer layer. -/
def relativeOuter : Set (Set Prop) :=
  rel >>= fun y ↦ pure (lawyer >>= fun x ↦ pure (visits y x))

-- (44)
theorem both_wide :
    (lawyer >>= fun x ↦ rel >>= fun y ↦ pure (visits y x)) >>=
        (fun p ↦ closureCond cond (pure p) (pure house)) =
      Set.image2 (fun x y ↦ cond (visits y x) house) lawyer rel := by
  ext q; simp [closureCond, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

/-- Pied-piping the island of Figure 10, right, scopes the relative above the conditional and
reconstructs the lawyer below it, (49) and Figure 11. -/
theorem relative_wide :
    relativeOuter lawyer rel visits >>= (fun m ↦ closureCond cond m (pure house)) =
      (fun y ↦ cond (∃ x ∈ lawyer, visits y x) house) '' rel := by
  ext q; simp [relativeOuter, closureCond, Set.bind_def, sSup_Prop_eq, eq_comm, -eq_iff_iff]

/-- Pied-piping the island of Figure 10, left, scopes the lawyer above the conditional and
reconstructs the relative below it (section 5.3). -/
theorem lawyer_wide :
    lawyerOuter lawyer rel visits >>= (fun m ↦ closureCond cond m (pure house)) =
      (fun x ↦ cond (∃ y ∈ rel, visits y x) house) '' lawyer := by
  ext q; simp [lawyerOuter, closureCond, Set.bind_def, sSup_Prop_eq, eq_comm, -eq_iff_iff]

-- (11)
theorem joinM_lawyerOuter :
    joinM (lawyerOuter lawyer rel visits) = pure visits <*> rel <*> lawyer := by
  ext q; simp [lawyerOuter, joinM, Set.bind_def, Set.seq_eq_set_seq, Set.mem_seq_iff]; aesop

theorem joinM_relativeOuter :
    joinM (relativeOuter lawyer rel visits) = pure visits <*> rel <*> lawyer := by
  ext q; simp [relativeOuter, joinM, Set.bind_def, Set.seq_eq_set_seq, Set.mem_seq_iff]; aesop

/-- In (47) the seminar scopes above *every grad* and the paper reconstructs between *every grad*
and the conditional, as in `Examples.ex47`. -/
theorem seminar_paper (grad seminar paper : Set E) (disc : E → E → Prop) (joy : E → Prop) :
    (seminar >>= fun s ↦ pure (paper >>= fun p ↦ pure (disc p s))) >>=
        (fun m ↦ det GQ.every grad fun g ↦ m >>= fun q ↦ closureCond cond (pure q) (pure (joy g))) =
      (fun s ↦ ∀ g ∈ grad, ∃ p ∈ paper, cond (disc p s) (joy g)) '' seminar := by
  ext q
  simp [det, GQ.every, closureCond, Set.bind_def, sSup_Prop_eq, sSup_singleton, eq_comm,
    -eq_iff_iff]

end Selectivity

/-! #### The island on the composition engine

With the indefinites' alternatives in their types, the engine finds every way of composing the
island of Figure 10 without moving either indefinite: mapping composition over the alternatives
of one indefinite and then the other's gives the two higher-order islands, and structured
application, which is point-wise application (11), merges the two sets of alternatives into one,
the flattening of either. -/

section SelectivityEngine

open Montague PhraseStructure

variable {E : Type} (lawyer rel : Set E) (visits : E → E → Prop)

/-- The words of the island of Figure 10. -/
inductive IslandWord
  | aLawyer
  | visits
  | aRelative
  deriving DecidableEq

/-- The island's lexicon, each indefinite a computation whose alternatives are the members of its
restrictor ([bumford-charlow-2026]). -/
def islandLexicon : IslandWord → Option (Σ ty, Ty.Domain E Unit ty)
  | .aLawyer => some ⟨.comp .set .e, lawyer⟩
  | .visits => some ⟨.e ⇒ .e ⇒ .t, visits⟩
  | .aRelative => some ⟨.comp .set .e, rel⟩

/-- The island *a lawyer visits a relative*. -/
def island : Tree Unit IslandWord :=
  .bin (.leaf .aLawyer) (.bin (.leaf .visits) (.leaf .aRelative))

/-- The island has three derivations, the three that [bumford-charlow-2026]'s `combine` finds for a
set of individuals and a set of properties: the lawyer's alternatives mapped inside the
relative's, the higher-order island of Figure 10, right; the relative's inside the lawyer's,
Figure 10, left; and point-wise application (11), which flattens either. -/
theorem translations_island (g : Assignment E) :
    (Tree.translations individualIndices (islandLexicon lawyer rel visits) island).map
        (fun d ↦ (⟨d.1, d.2.eval (fun c ↦ c) g⟩ : Denotation E Unit)) =
      [⟨.comp .set (.comp .set .t), relativeOuter lawyer rel visits⟩,
       ⟨.comp .set (.comp .set .t), lawyerOuter lawyer rel visits⟩,
       ⟨.comp .set .t, (pure visits <*> rel <*> lawyer : Set Prop)⟩] := by
  simp [Tree.translations, island, islandLexicon, Ty.modes, Ty.mode?, Mode.functionalLeft?,
    Mode.functionalRight?, Mode.predicateModification?, Mode.eventIdentification?, Eff.map,
    Eff.seq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [relativeOuter, bind_pure_comp, Set.fmap_eq_image, Set.image_image]
  · simp only [lawyerOuter, bind_pure_comp, Set.fmap_eq_image, Set.image_image]
  · refine Set.ext fun q ↦ ?_
    simp only [Set.mem_seq_iff, Set.mem_image, Set.mem_singleton_iff]
    aesop

end SelectivityEngine

-- (43)
theorem lawyer_wide_ne_relative_wide : ¬ ∀ visits : Fin 4 → Fin 4 → Prop,
    sSup (lawyerOuter {0, 1} {2, 3} visits >>= fun m ↦ closureCond (· → ·) m (pure False)) ↔
      sSup (relativeOuter {0, 1} {2, 3} visits >>= fun m ↦ closureCond (· → ·) m (pure False)) := by
  intro h
  have h := h fun _ x ↦ x = 0
  rw [lawyer_wide, relative_wide] at h
  simp [-eq_iff_iff] at h

/-- No function of the point-wise island meaning gives the lawyer-wide reading of (43) (section
5.4). -/
theorem lawyer_wide_not_pointwise :
    ¬ ∃ F : Set Prop → Prop, ∀ visits : Fin 4 → Fin 4 → Prop,
      F (pure visits <*> {2, 3} <*> {0, 1}) ↔
        sSup (lawyerOuter {0, 1} {2, 3} visits >>= fun m ↦ closureCond (· → ·) m (pure False)) := by
  rintro ⟨F, hF⟩
  have univ_of : ∀ visits : Fin 4 → Fin 4 → Prop, visits 2 0 → ¬ visits 3 0 →
      (pure visits <*> ({2, 3} : Set (Fin 4)) <*> {0, 1}) = Set.univ := by
    intro v h1 h2
    refine Set.eq_univ_of_forall fun q ↦ ?_
    simp only [Set.seq_eq_set_seq, Set.mem_seq_iff]
    by_cases hq : q
    · exact ⟨v 2, ⟨v, rfl, 2, by simp, rfl⟩, 0, by simp, eq_true hq ▸ eq_true h1⟩
    · exact ⟨v 3, ⟨v, rfl, 3, by simp, rfl⟩, 0, by simp, eq_false hq ▸ eq_false h2⟩
  have h1 := hF fun y x ↦ x = 0 ∧ y = 2
  have h2 := hF fun y _ ↦ y = 2
  rw [univ_of _ (by simp) (by simp), lawyer_wide] at h1
  rw [univ_of _ rfl (by decide), lawyer_wide] at h2
  simp [-eq_iff_iff] at h1 h2
  exact h2 h1

/-! ### Assignments

The monad of (54)–(56) is `ReaderT (Assignment E) Set`, whose membership lemmas come from the
Reader.Set monad of `Charlow2014`. -/

namespace Si

open Montague
open scoped Assignment

variable {E α : Type}

example : LawfulMonad (ReaderT (Assignment E) Set) := inferInstance

@[simp] theorem monadLift_apply (m : Set α) (g : Assignment E) :
    (monadLift m : ReaderT (Assignment E) Set α) g = m := rfl

/-- `pro n` is the pronoun `she_n` (58), the singleton of the value of index `n`. -/
def pro (n : ℕ) : ReaderT (Assignment E) Set E := fun g ↦ {g n}

@[simp] theorem pro_apply (n : ℕ) (g : Assignment E) : pro n g = {g n} := rfl

/-- `beta n f x` is the binder `βⁿ` (61), which evaluates the scope `f x` with index `n` anchored
to `x`. -/
def beta (n : ℕ) (f : E → ReaderT (Assignment E) Set α) (x : E) : ReaderT (Assignment E) Set α :=
  withReader (·[n ↦ x]) (f x)

@[simp] theorem beta_apply (n : ℕ) (f : E → ReaderT (Assignment E) Set α) (x : E)
    (g : Assignment E) : beta n f x g = f x (g[n ↦ x]) := rfl

/-- `det D P f` is the determiner `D` over `P` closing off its scope `f` at each assignment, as
*everybody* (65) and the *no candidate* of Figure 14 do. -/
def det (D : GQ E) (P : Set E) (f : E → ReaderT (Assignment E) Set Prop) :
    ReaderT (Assignment E) Set Prop :=
  fun g ↦ pure (D (· ∈ P) fun y ↦ sSup (f y g))

variable (ling : Set E) (cited : E → E → Prop)

-- (59), Figure 12
theorem ling_cited_her :
    (monadLift ling : ReaderT (Assignment E) Set E) >>=
        (fun x ↦ pro 0 >>= fun y ↦ pure (cited y x)) =
      fun g ↦ (fun x ↦ cited (g 0) x) '' ling := by
  funext g; ext q; simp [eq_comm, -eq_iff_iff]

-- Figure 12
theorem ling_cited_herself :
    (monadLift ling : ReaderT (Assignment E) Set E) >>=
        beta 0 (fun x ↦ pro 0 >>= fun y ↦ pure (cited y x)) =
      fun _ ↦ (fun x ↦ cited x x) '' ling := by
  funext g; ext q; simp [eq_comm, -eq_iff_iff]

/-- `expertCites` is the higher-order island *a famous expert on indefinites cites her₀* of
Figure 13, left, with the indefinite in the outer layer and the pronoun in the inner. -/
def expertCites (exp : Set E) (cites : E → E → Prop) :
    ReaderT (Assignment E) Set (ReaderT (Assignment E) Set Prop) :=
  (monadLift exp : ReaderT (Assignment E) Set E) >>= fun x ↦
    pure (pro 0 >>= fun y ↦ pure (cites y x))

/-- Pied-piping the island over *everybody* while reconstructing its inner layer gives the
indefinite wide scope and binds the pronoun ((51), Figure 13, `Examples.ex51`). -/
theorem expert_wide_bound (exp human : Set E) (cites : E → E → Prop)
    (lovesWhen : Prop → E → Prop) :
    expertCites exp cites >>=
        (fun m ↦ det GQ.every human (beta 0 fun y ↦ m >>= fun p ↦ pure (lovesWhen p y))) =
      fun _ ↦ (fun x ↦ ∀ y ∈ human, lovesWhen (cites y x) y) '' exp := by
  funext g; ext q; simp [expertCites, det, GQ.every, sSup_Prop_eq, eq_comm, -eq_iff_iff]

/-! #### The Binder Roof Constraint -/

section BinderRoof

variable (cand paper : Set E) (wrote subm : E → E → Prop)

/-- `paperBy paper wrote` is *a paper he₀ had written* (66), the papers written by the value of
index 0. -/
def paperBy : ReaderT (Assignment E) Set E := fun g ↦ {x | x ∈ paper ∧ wrote x (g 0)}

/-- Scoped over *no candidate*, the indefinite leaves its pronoun free (Figure 14). -/
theorem paper_wide :
    paperBy paper wrote >>= (fun x ↦ det GQ.no cand (beta 0 fun y ↦ pure (subm x y))) =
      fun g ↦ (fun x ↦ ¬ ∃ y ∈ cand, subm x y) '' {x | x ∈ paper ∧ wrote x (g 0)} := by
  funext g; ext q; simp [paperBy, det, GQ.no, sSup_Prop_eq, eq_comm, -eq_iff_iff]

-- Figure 14
theorem paper_wide_beta :
    paperBy paper wrote >>= (fun x ↦ det GQ.no cand (beta 0 fun y ↦ pure (subm x y))) =
      paperBy paper wrote >>= fun x ↦ det GQ.no cand fun y ↦ pure (subm x y) :=
  rfl

theorem dependsOn_paper_wide :
    DependsOn (paperBy paper wrote >>= fun x ↦ det GQ.no cand (beta 0 fun y ↦ pure (subm x y)))
      {0} := by
  intro g g' h
  rw [paper_wide]
  simp only [h 0 rfl]

/-- Below `β⁰` the indefinite has its pronoun bound, and the reading is the same at every
assignment, as in `Examples.ex53`. -/
theorem paper_narrow :
    det GQ.no cand (beta 0 fun y ↦ paperBy paper wrote >>= fun x ↦ pure (subm x y)) =
      fun _ ↦ {¬ ∃ y ∈ cand, ∃ x ∈ paper, wrote x y ∧ subm x y} := by
  funext g; simp [paperBy, det, GQ.no, sSup_Prop_eq, -eq_iff_iff]

theorem dependsOn_paper_narrow :
    DependsOn (det GQ.no cand (beta 0 fun y ↦ paperBy paper wrote >>= fun x ↦ pure (subm x y)))
      ∅ := by
  rw [paper_narrow]; exact dependsOn_const _

/-- The wide reading does depend on the pronoun, so it is not the bound reading. -/
theorem not_dependsOn_paper_wide :
    ¬ DependsOn (paperBy (E := Bool) Set.univ (fun _ y ↦ y = true) >>=
      fun x ↦ det GQ.no Set.univ (beta 0 fun y ↦ pure (x = y))) ∅ := by
  intro h
  have h := congrArg Set.Nonempty (h.empty (fun _ ↦ true) fun _ ↦ false)
  rw [paper_wide] at h
  simp at h

/-- With a choice function (67), the reading (69) of (53) holds iff no candidate submitted every
paper she wrote. -/
theorem cf_reading_iff [Nonempty E] (hwrote : ∀ x ∈ cand, ∃ y ∈ paper, wrote y x)
    (hinj : Set.InjOn (fun x y ↦ y ∈ paper ∧ wrote y x) cand) :
    (∃ f : ChoiceFunction E,
        ¬ ∃ x ∈ cand, subm (f fun y ↦ y ∈ paper ∧ wrote y x) x) ↔
      ¬ ∃ x ∈ cand, ∀ y ∈ paper, wrote y x → subm y x := by
  simpa [and_imp] using Charlow2014.cf_no_candidate_iff (· ∈ cand)
    (fun x y ↦ y ∈ paper ∧ wrote y x) (fun y x ↦ subm y x)
    (fun x hx ↦ (hwrote x hx).imp fun _ ↦ id) hinj

/-- The reading (69) does not entail the bound reading of (53). -/
theorem cf_reading_not_imp_bound :
    ¬ ∀ (cand paper : Set (Fin 3)) (wrote subm : Fin 3 → Fin 3 → Prop) (g : Assignment (Fin 3)),
    (∃ f : ChoiceFunction (Fin 3),
        ¬ ∃ x ∈ cand, subm (f fun y ↦ y ∈ paper ∧ wrote y x) x) →
      sSup (det GQ.no cand (beta 0 fun y ↦ paperBy paper wrote >>= fun x ↦ pure (subm x y))
        g) := by
  intro h
  have := h {0} {1, 2} (fun _ x ↦ x = 0) (fun y _ ↦ y = 1) (fun _ ↦ 0) <| by
    refine (cf_reading_iff {0} {1, 2} (fun _ x ↦ x = 0) (fun y _ ↦ y = 1) (by simp)
      (by simp [Set.InjOn])).2 ?_
    simp
  rw [paper_narrow] at this
  simp at this

end BinderRoof

/-! #### Building the indefinite (Appendix A) -/

section Determiners

variable (paper : Set E) (wrote : E → E → Prop)

/-- `a f` is the indefinite determiner (83), the set of individuals whose restrictor `f` holds. -/
def a (f : E → ReaderT (Assignment E) Set Prop) : ReaderT (Assignment E) Set E :=
  fun g ↦ {x | sSup (f x g)}

/-- `that r l` is the relative pronoun (87), which conjoins two assignment-relative sets of
propositions. -/
def that (r l : ReaderT (Assignment E) Set Prop) : ReaderT (Assignment E) Set Prop :=
  fun g ↦ Set.image2 (· ∧ ·) (l g) (r g)

-- (85)
theorem a_pure (ling : Set E) : a (fun x ↦ pure (x ∈ ling)) = monadLift ling := by
  funext g; ext x; simp [a, sSup_Prop_eq, -eq_iff_iff]

/-- *A paper (that) she₀ had written*, with `β¹` binding the gap, is (66) (Figure 15, right). -/
theorem a_paper_that_she_wrote :
    a (beta 1 fun x ↦
        that (pro 1 >>= fun z ↦ pro 0 >>= fun w ↦ pure (wrote z w)) (pure (x ∈ paper))) =
      paperBy paper wrote := by
  funext g; ext x
  simp [a, that, paperBy, sSup_Prop_eq, Function.update_of_ne, -eq_iff_iff]

end Determiners

/-! #### Binding in alternative semantics -/

section AlternativeSemantics

/-- `abstractChoice n m` is abstraction over index `n` in alternative semantics (74), in which a
choice function flattens the alternatives of `m` at each value of the index. -/
def abstractChoice (n : ℕ) (m : ReaderT (Assignment E) Set Prop) :
    ReaderT (Assignment E) Set (E → Prop) :=
  fun g ↦ Set.range fun f : ChoiceFunction Prop ↦ fun x ↦ f (· ∈ m (g[n ↦ x]))

/-- Composed point-wise with the abstraction (74), `nobody [λ₀ t₀ met a phonologist]` has a true
alternative exactly when nobody met every phonologist (77). -/
theorem nobody_met_iff (human phon : Set E) (met : E → E → Prop) (hphon : phon.Nonempty)
    (g : Assignment E) :
    sSup ((fun P ↦ ¬ ∃ x ∈ human, P x) ''
        abstractChoice 0 (fun g ↦ (fun y ↦ met y (g 0)) '' phon) g) ↔
      ¬ ∃ x ∈ human, ∀ y ∈ phon, met y x := by
  simp only [abstractChoice, sSup_Prop_eq, Set.mem_image, Set.mem_range, Function.update_self]
  constructor
  · rintro ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, h⟩ ⟨x, hx, hall⟩
    obtain ⟨y, hy, hq⟩ := f.apply_of_exists (P := fun q ↦ ∃ y ∈ phon, met y x = q)
      (hphon.elim fun y hy ↦ ⟨_, y, hy, rfl⟩)
    exact h ⟨x, hx, show f _ from hq ▸ hall y hy⟩
  · intro h
    push Not at h
    obtain ⟨f, hf⟩ := (ChoiceFunction.exists_forall_apply_iff (ι := human)
      (fun x q ↦ ∃ y ∈ phon, met y x.1 = q) Not).2 fun x ↦ by
        obtain ⟨y, hy, hn⟩ := h x x.2
        obtain ⟨f, hf⟩ := ChoiceFunction.exists_apply_eq
          (N := fun q ↦ ∃ y ∈ phon, met y x.1 = q) ⟨y, hy, rfl⟩
        exact ⟨f, hf ▸ hn⟩
    exact ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, fun ⟨x, hx, hfx⟩ ↦ hf ⟨x, hx⟩ hfx⟩

-- (74)
theorem abstractChoice_subset_distribute (n : ℕ) (m : ReaderT (Assignment E) Set Prop)
    (g : Assignment E) (hm : ∀ x, (m (g[n ↦ x])).Nonempty) :
    abstractChoice n m g ⊆ (distribute (M := SetM) fun x ↦ m (g[n ↦ x])).run := by
  rintro _ ⟨f, rfl⟩
  exact SetM.mem_run_distribute.2 fun x ↦ f.apply_of_exists (hm x)

/-- When the alternatives are nonempty and distinct values of the index give distinct ones, the
two lines of (74) agree. -/
theorem abstractChoice_eq_distribute (n : ℕ) (m : ReaderT (Assignment E) Set Prop)
    (g : Assignment E) (hm : ∀ x, (m (g[n ↦ x])).Nonempty)
    (hinj : Function.Injective fun x ↦ m (g[n ↦ x])) :
    abstractChoice n m g = (distribute (M := SetM) fun x ↦ m (g[n ↦ x])).run := by
  refine (abstractChoice_subset_distribute n m g hm).antisymm fun P hP ↦ ?_
  obtain ⟨f, hf⟩ := (ChoiceFunction.exists_forall_apply_iff_of_injective
    (R := fun x ↦ (· ∈ m (g[n ↦ x]))) (fun _ _ h ↦ hinj (Set.ext fun y ↦ iff_of_eq (congrFun h y)))
    hm fun x ↦ (· = P x)).2 fun x ↦ ⟨P x, SetM.mem_run_distribute.1 hP x, rfl⟩
  exact ⟨f, funext hf⟩

-- (74)
theorem abstractChoice_met_linguist (ling : Set E) (met : E → E → Prop)
    (h : ∀ x, (∃ y ∈ ling, met y x) ∧ ∃ y ∈ ling, ¬ met y x) (g : Assignment E) :
    abstractChoice 0 (fun g ↦ (fun y ↦ met y (g 0)) '' ling) g = Set.range (Function.const E) ∧
      (distribute (M := SetM) fun x ↦ (fun y ↦ met y x) '' ling).run = Set.univ := by
  have hu (x : E) : (fun y ↦ met y x) '' ling = Set.univ := Set.eq_univ_of_forall fun p ↦ by
    by_cases hp : p
    · obtain ⟨y, hy, hm⟩ := (h x).1
      exact ⟨y, hy, propext ⟨fun _ ↦ hp, fun _ ↦ hm⟩⟩
    · obtain ⟨y, hy, hm⟩ := (h x).2
      exact ⟨y, hy, propext ⟨fun h' ↦ (hm h').elim, fun h' ↦ (hp h').elim⟩⟩
  refine ⟨Set.ext fun P ↦ ?_, Set.eq_univ_of_forall fun P ↦
    SetM.mem_run_distribute.2 fun x ↦ (hu x).symm ▸ Set.mem_univ (P x)⟩
  simp only [abstractChoice, Function.update_self, hu, Set.mem_univ, Set.mem_range]
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f fun _ ↦ True, hf⟩, fun ⟨p, hp⟩ ↦ ?_⟩
  obtain ⟨f, hf⟩ := ChoiceFunction.exists_apply_eq (N := fun _ : Prop ↦ True) (x := p) trivial
  exact ⟨f, hf ▸ hp⟩

-- (74)
theorem abstractChoice_ne_distribute [Nontrivial E] (ling : Set E) (met : E → E → Prop)
    (h : ∀ x, (∃ y ∈ ling, met y x) ∧ ∃ y ∈ ling, ¬ met y x) (g : Assignment E) :
    abstractChoice 0 (fun g ↦ (fun y ↦ met y (g 0)) '' ling) g ≠
      (distribute (M := SetM) fun x ↦ (fun y ↦ met y x) '' ling).run := by
  rw [(abstractChoice_met_linguist ling met h g).1, (abstractChoice_met_linguist ling met h g).2]
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  intro hc
  obtain ⟨p, hp⟩ : (· = a) ∈ Set.range (Function.const E) := hc ▸ Set.mem_univ _
  exact hab (((congrFun hp b).symm.trans (congrFun hp a)).mpr rfl).symm

-- (75), (74)
theorem range_skolem_eq_distribute (ling : Set E) (met : E → E → Prop) (hling : ling.Nonempty) :
    Set.range (fun F : E → ChoiceFunction E ↦ fun x ↦ met (F x (· ∈ ling)) x) =
      (distribute (M := SetM) fun x ↦ (fun y ↦ met y x) '' ling).run := by
  ext P
  refine ⟨fun ⟨F, hF⟩ ↦ hF ▸ SetM.mem_run_distribute.2 fun x ↦
    ⟨_, (F x).apply_of_exists hling, rfl⟩, fun hP ↦ ?_⟩
  choose y hy hyP using fun x ↦ (SetM.mem_run_distribute.1 hP x : ∃ y ∈ ling, met y x = P x)
  choose F hF using fun x ↦ ChoiceFunction.exists_apply_eq (N := (· ∈ ling)) (hy x)
  exact ⟨F, funext fun x ↦ (congrArg (met · x) (hF x)).trans (hyP x)⟩

end AlternativeSemantics

/-! #### Alternatives on the composition engine

On the composition engine, Kratzer and Shimoyama's lexicon, where an indefinite denotes the set
of its restrictor, gives (77) the abstraction of the second line of (74). Resolving each
occurrence of a word before interpretation, `PhraseStructure.Tree.readings`, gives it the layering
of (80) and (81), which reads the indefinite as one phonologist at every value of the
variable. -/

section Engine

open PhraseStructure

variable (human phon : Set E) (met : E → E → Prop)

/-- The words of (77). -/
inductive Word
  | nobody
  | met
  | aPhonologist
  deriving DecidableEq

/-- The lexicon of (77), the indefinite denoting the set of phonologists. -/
def lexicon : Word → Option (Denotation E Unit SetM)
  | .nobody => some ⟨(.e ⇒ .t) ⇒ .t, pure fun P ↦ ¬ ∃ x ∈ human, P x⟩
  | .met => some ⟨.e ⇒ .e ⇒ .t, pure met⟩
  | .aPhonologist => some ⟨.e, phon⟩

/-- (77), `Nobody [λ₀ t₀ met a phonologist]`. -/
def nobodyMet : Tree Unit Word :=
  .bin (.leaf .nobody) (.binder 0 (.bin (.tr 0) (.bin (.leaf .met) (.leaf .aPhonologist))))

theorem interp_nobodyMet (g : Assignment E) :
    Tree.interp (lexicon human phon met) g nobodyMet = some ⟨.t,
      ((fun P ↦ ¬ ∃ x ∈ human, P x) '' Set.univ.pi fun x ↦ (fun y ↦ met y x) '' phon :
        Set Prop)⟩ := by
  refine congrArg (fun v : Set Prop ↦ some (⟨.t, v⟩ : Denotation E Unit SetM)) ?_
  simp only [Mode.evalM, Set.pure_def, Set.fmap_eq_image, Set.image_singleton, Term.evalM,
    Term.realize, Interpretation.effectful, Function.update_self, Set.seq_eq_set_seq,
    Set.singleton_seq, Set.image_image]
  rfl

-- (77)
theorem sSup_interp_nobodyMet_iff (hphon : phon.Nonempty) (g : Assignment E) {X : SetM Prop}
    (hX : Tree.interp (lexicon human phon met) g nobodyMet = some ⟨.t, X⟩) :
    sSup X.run ↔ ¬ ∃ x ∈ human, ∀ y ∈ phon, met y x := by
  obtain rfl := sigma_mk_injective (Option.some_injective _
    (hX.symm.trans (interp_nobodyMet human phon met g)))
  simp only [SetM.run, sSup_Prop_eq, Set.mem_image, Set.mem_univ_pi]
  refine ⟨fun ⟨_, ⟨P, hP, hb⟩, h⟩ ⟨x, hx, hall⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy, hPy⟩ := hP x
    exact (hb ▸ h) ⟨x, hx, hPy ▸ hall y hy⟩
  · have (x : E) : ∃ y ∈ phon, x ∈ human → ¬ met y x := by
      by_cases hx : x ∈ human
      · obtain ⟨y, hy, hn⟩ : ∃ y ∈ phon, ¬ met y x := by
          by_contra h'
          push Not at h'
          exact h ⟨x, hx, h'⟩
        exact ⟨y, hy, fun _ ↦ hn⟩
      · obtain ⟨y, hy⟩ := hphon
        exact ⟨y, hy, fun h' ↦ (hx h').elim⟩
    choose y hy hn using this
    exact ⟨_, ⟨fun x ↦ met (y x) x, fun x ↦ ⟨y x, hy x, rfl⟩, rfl⟩,
      fun ⟨x, hx, hm⟩ ↦ hn x hx hm⟩

theorem readings_nobodyMet (g : Assignment E) :
    Tree.readings (Tree.wordReadings (lexicon human phon met)) g nobodyMet =
      (fun y ↦ (⟨.t, ¬ ∃ x ∈ human, met y x⟩ : Denotation E Unit Id)) '' phon := by
  ext d
  simp only [nobodyMet, Tree.mem_readings_phrase_binary, Tree.readings_terminal,
    Tree.mem_readings_bind, Set.mem_image]
  constructor
  · rintro ⟨⟨τ₁, v₁⟩, ⟨X₁, h₁, hm₁⟩, d₂, ⟨r, hr, hd₂⟩, hb⟩
    simp only [lexicon, Option.some.injEq, Sigma.mk.inj_iff] at h₁
    obtain ⟨rfl, h₁⟩ := h₁
    obtain rfl := eq_of_heq h₁
    obtain rfl : v₁ = _ := hm₁
    obtain ⟨cs, rfl, hcs⟩ := Tree.map_eq_phrase_iff.1 hr
    obtain ⟨r₁, cs₁, rfl, h₁, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
    obtain ⟨r₂, cs₂, rfl, h₂, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
    obtain rfl := List.map_eq_nil_iff.mp hcs₂
    obtain rfl := Tree.map_eq_trace_iff.1 h₁
    obtain ⟨cs', rfl, hcs'⟩ := Tree.map_eq_phrase_iff.1 h₂
    obtain ⟨r₃, cs₃, rfl, h₃, hcs₃⟩ := List.map_eq_cons_iff.mp hcs'
    obtain ⟨r₄, cs₄, rfl, h₄, hcs₄⟩ := List.map_eq_cons_iff.mp hcs₃
    obtain rfl := List.map_eq_nil_iff.mp hcs₄
    obtain ⟨⟨⟨w₃, τ₃, v₃⟩, X₃, hX₃, hv₃⟩, rfl, hw₃⟩ := Tree.map_eq_terminal_iff.1 h₃
    obtain ⟨⟨⟨w₄, τ₄, v₄⟩, X₄, hX₄, hv₄⟩, rfl, hw₄⟩ := Tree.map_eq_terminal_iff.1 h₄
    clear hr hcs hcs₁ hcs₂ h₁ h₂ hcs' hcs₃ hcs₄ h₃ h₄
    obtain rfl : w₃ = .met := hw₃
    obtain rfl : w₄ = .aPhonologist := hw₄
    simp only [lexicon, Option.some.injEq, Sigma.mk.inj_iff] at hX₃ hX₄
    obtain ⟨rfl, hX₃⟩ := hX₃
    obtain rfl := eq_of_heq hX₃
    obtain ⟨rfl, hX₄⟩ := hX₄
    obtain rfl := eq_of_heq hX₄
    have e₃ : met = v₃ := (id hv₃).symm
    subst e₃
    obtain rfl := Option.some.inj hd₂
    obtain rfl := Option.some.inj hb
    exact ⟨v₄, hv₄, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(.e ⇒ .t) ⇒ .t, fun P ↦ ¬ ∃ x ∈ human, P x⟩, ⟨_, rfl, rfl⟩,
      ⟨.e ⇒ .t, fun x ↦ met y x⟩,
      ⟨.bin (.tr 0) (.bin (.leaf ⟨(.met, ⟨.e ⇒ .e ⇒ .t, met⟩), _, rfl, rfl⟩)
        (.leaf ⟨(.aPhonologist, ⟨.e, y⟩), _, rfl, hy⟩)), rfl, rfl⟩, rfl⟩

/-- Under the layering of (80) and (81), (77) has a true alternative exactly when there is a
phonologist nobody met, the wide-scope reading of the indefinite. -/
theorem sSup_readings_nobodyMet_iff (g : Assignment E) :
    sSup {b : Prop | (⟨.t, b⟩ : Denotation E Unit Id) ∈
      Tree.readings (Tree.wordReadings (lexicon human phon met)) g nobodyMet} ↔
      ∃ y ∈ phon, ¬ ∃ x ∈ human, met y x := by
  simp only [readings_nobodyMet, Set.mem_image, Sigma.mk.inj_iff, heq_eq_eq, true_and,
    sSup_Prop_eq, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, ⟨y, hy, hb⟩, h⟩ ↦ ⟨y, hy, hb.mpr h⟩, fun ⟨y, hy, h⟩ ↦ ⟨_, ⟨y, hy, rfl⟩, h⟩⟩

end Engine

end Si

end Charlow2020
