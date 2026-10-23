module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Functor
public import Linglib.Semantics.Composition.Assignment
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
island take scope independently, and once assignments are added to the monad, an indefinite whose
restrictor holds a bound pronoun cannot outscope the pronoun's binder.

## Main definitions

* `closureCond`, `det`, `distr`: the conditional (31), the determiners (65) and (84), and the
  distributivity operator (41), each closing off the alternatives of its scope.
* `lawyerOuter`, `relativeOuter`: the two higher-order islands of Figure 10.
* `Si.pro`, `Si.beta`, `Si.det`: pronouns (58), `β`-binding (61) and determiners over
  `ReaderT (Assignment E) Set`.
* `Si.a`, `Si.that`: the indefinite determiner (83) and the relative pronoun (87).
* `Si.abstractChoice`: abstraction by a choice function in alternative semantics (74).

## Main results

* `some_pure`, `bind_pure_left`, `plusWh_some`: the extended Partee triangle of Figure 4
  commutes.
* `exceptional_scope`, `exceptional_ne_narrow`: (33), and the exceptional reading of (1) is not
  the narrow one.
* `every_island`: pied-piping a universal's island gives nothing new (2).
* `intermediate_scope`, `two_island`: intermediate exceptional scope (3), and the distributive
  scope of a plural indefinite stays in its island (39).
* `relative_wide`, `lawyer_wide`, `seminar_paper`: selective exceptional scope, (43), (47), (49).
* `lawyer_wide_not_pointwise`: no function of the point-wise island meaning gives the
  lawyer-wide reading of (43).
* `Si.expert_wide_bound`: exceptional scope beside a bound pronoun (51).
* `Si.paper_wide`, `Si.paper_narrow`, `Si.not_dependsOn_paper_wide`: the Binder Roof
  Constraint of (53), Figure 14.
* `Si.cf_reading_iff`, `Si.cf_reading_not_imp_bound`: the choice-function reading (69) and its
  over-generation.
* `Si.a_paper_that_she_wrote`: the determiners of Appendix A derive (66).
* `Si.nobody_met_iff`: abstraction by a choice function over-generates (77).

## Implementation notes

* `η`, `≫=` and flattening are `pure`, `>>=` and `joinM` of mathlib's `Set.monad`, and the
  closure `⇓` (19) is `sSup` on `Set Prop`. Truth values are `Prop`, as in the paper's main text.
* The paper's conditional `if : t → t → t` is a parameter `cond`; the witnesses that separate
  readings use the material conditional. Pluralities are `Finset`s of atoms.
* A derivation is a term in the monad, and which constituent takes scope where is not
  represented, so a reading the paper rules out is shown to differ from the derived ones.
* `Si.cf_reading_iff` assumes that no two candidates wrote the same papers, which the paper's
  gloss of (69) needs and leaves implicit.
* Figure 9 prints `die X` for `die x`.

## TODO

* (46), and point-wise composition with a closure inside the island (45) on (46) and (47).
* (79)–(82), (88), and Appendix B.

## References

* [charlow-2020]
* [charlow-2014]
* [partee-1987]
* [reinhart-1997]
* [brasoveanu-farkas-2011]
-/

@[expose] public section

attribute [local instance] Set.monad

namespace Charlow2020

open Quantifier Quantifier.NP

/-- The closure `⇓` (19), `T ∈ m`, is the supremum of a set of truth values. -/
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

/-- Applying `+wh` to the Montague lift gives the lift at result type `Set β`, the last face of
Figure 4. -/
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

/-- Taking scope over its island, which then takes scope over the conditional, gives the
indefinite exceptional scope, `{if (dies x) house | rel x}` (33), as in `Examples.ex1`. -/
theorem exceptional_scope :
    (rel >>= fun x ↦ pure (dies x)) >>= (fun p ↦ closureCond cond (pure p) (pure house)) =
      (fun x ↦ cond (dies x) house) '' rel := by
  ext q; simp [closureCond, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

/-- Pied-piping the island is scoping the indefinite out of it directly (Figure 7). -/
theorem exceptional_scope_eq_wide :
    (rel >>= fun x ↦ pure (dies x)) >>= (fun p ↦ closureCond cond (pure p) (pure house)) =
      rel >>= fun x ↦ closureCond cond (pure (dies x)) (pure house) := by
  simp only [bind_assoc, pure_bind]

/-- Closing the island off in the antecedent gives the narrow reading `if ≫ ∃` (13). -/
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

/-- The island of (3) can also scope over *each student*. -/
theorem widest_scope :
    (rel >>= fun c ↦ pure (wrong c)) >>= (fun p ↦ det GQ.every student fun y ↦ pure (argue y p)) =
      (fun c ↦ ∀ y ∈ student, argue y (wrong c)) '' rel := by
  ext q; simp [det, GQ.every, Set.bind_def, sSup_singleton, eq_comm, -eq_iff_iff]

end Conditional

/-- The intermediate and widest readings of (3) differ. -/
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

/-- With `∆`, *two linguists wrote something* gets its distributive reading (Figure 9, left). -/
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

/-- The reading of (39) with `∆` above the conditional, which would need the plural to scope out
of the island, differs from the derived one. -/
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

/-- Pied-piping the flat island scopes both indefinites over the conditional (44). -/
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

/-- Flattening a higher-order island gives the point-wise island (11) and forgets the layers. -/
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

/-- The two selective readings of (43) differ, as in `Examples.ex43`. -/
theorem lawyer_wide_ne_relative_wide : ¬ ∀ visits : Fin 4 → Fin 4 → Prop,
    sSup (lawyerOuter {0, 1} {2, 3} visits >>= fun m ↦ closureCond (· → ·) m (pure False)) ↔
      sSup (relativeOuter {0, 1} {2, 3} visits >>= fun m ↦ closureCond (· → ·) m (pure False)) := by
  intro h
  have h := h fun _ x ↦ x = 0
  rw [lawyer_wide, relative_wide] at h
  simp [-eq_iff_iff] at h

/-- No function of the point-wise island meaning gives the lawyer-wide reading of (43), since two
visiting relations with the same point-wise island differ on it (section 5.4). -/
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

/-- *A linguist cited her₀* leaves the pronoun free, (59) and Figure 12, left. -/
theorem ling_cited_her :
    (monadLift ling : ReaderT (Assignment E) Set E) >>=
        (fun x ↦ pro 0 >>= fun y ↦ pure (cited y x)) =
      fun g ↦ (fun x ↦ cited (g 0) x) '' ling := by
  funext g; ext q; simp [eq_comm, -eq_iff_iff]

/-- In *a linguist β⁰ cited herself₀* the pronoun is bound, and the meaning is the same at every
assignment (Figure 12, right). -/
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

/-- Pied-piping the island over *everybody* while its inner layer reconstructs under `β⁰` gives
the indefinite scope over *everybody* and binds the pronoun, (51) and Figure 13, right, as in
`Examples.ex51`. -/
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

/-- Below the indefinite, `β⁰` does nothing (Figure 14). -/
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

/-- With a choice function (67), the reading (69) of (53) holds exactly when no candidate
submitted every paper she wrote, given that every candidate wrote a paper and no two wrote the
same ones. -/
theorem cf_reading_iff [Nonempty E] (hwrote : ∀ x ∈ cand, ∃ y ∈ paper, wrote y x)
    (hinj : Set.InjOn (fun x y ↦ y ∈ paper ∧ wrote y x) cand) :
    (∃ f : ChoiceFunction E,
        ¬ ∃ x ∈ cand, subm (f fun y ↦ y ∈ paper ∧ wrote y x) x) ↔
      ¬ ∃ x ∈ cand, ∀ y ∈ paper, wrote y x → subm y x := by
  simpa [and_imp] using Charlow2014.cf_no_candidate_iff (· ∈ cand)
    (fun x y ↦ y ∈ paper ∧ wrote y x) (fun y x ↦ subm y x)
    (fun x hx ↦ (hwrote x hx).imp fun _ ↦ id) hinj

/-- The reading (69) over-generates, since it does not entail the bound reading of (53), which
fails when the one candidate wrote two papers and submitted one. -/
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

/-- The determiner scoping over its noun gives the set-denoting indefinite (85). -/
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

end AlternativeSemantics

end Si

end Charlow2020
