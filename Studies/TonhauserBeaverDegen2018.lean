module

public import Linglib.Data.Statistics.TonhauserBeaverDegen2018
public import Linglib.Semantics.Presupposition.Trigger
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Tonhauser, Beaver and Degen (2018): How Projective Is Projective Content? Gradience in Projectivity and At-Issueness

Tonhauser, Beaver and Degen measure how strongly nineteen projective contents of English project
and how at-issue they are, and draw two conclusions. The first is that projectivity is gradient.
The contents whose mean projectivity a post hoc comparison tells apart are the edges of a graph,
and a division of the contents into classes of equal projectivity is a colouring of it. In both
experiments [two classes do not suffice](##not_colorable_two), and the division into hard and soft
triggers is not such a colouring: [two soft triggers differ](##soft_not_a_class), while
[hard and soft triggers do not](##hard_soft_not_adj).

The second is the Gradient Projection Principle, that content embedded under an
entailment-cancelling operator projects to the extent that it is not at-issue, which replaces the
*if and only if* of the Projection Principle of Simons, Tonhauser, Beaver and Roberts by a matter
of degree. The paper draws from it the prediction that projectivity varies together with
not-at-issueness, mathlib's `Monovary`, and tests it by regression:
[the effect has the predicted sign in all four experiments and is significant in
three](##atIssuenessEffect_significant_iff).

## Implementation notes

* An edge of `distinguished1a` or `distinguished1b` is a pair the printed table stars. A marginal
  mark is not an edge, and the tests are not recomputed.
* `le_of_adj_of_lt` reads the paper's observation that contents with higher projectivity ratings
  were also more not-at-issue over the pairs whose projectivity the tables tell apart. The
  paper's own test of the principle is the regression.
* The paper leaves open whether not-at-issueness causes projection or only predicts it.

## TODO

* The paper argues that the projection calculi of [karttunen-1973], [gazdar-1979], [heim-1983]
  and [van-der-sandt-1992] predict uniformly high projectivity for the seventeen
  presuppositions, none of which was under a plug or a filter. Deriving that prediction from
  `Studies/Karttunen1973.lean`, `Studies/Gazdar1979.lean` and `Studies/Heim1983.lean` needs the
  experimental stimuli as derivations of those calculi; here the prediction is met only by its
  consequence, that no two presuppositions are told apart, which `not_colorable_two` refutes.

## References

* [tonhauser-beaver-degen-2018]
* [simons-tonhauser-beaver-roberts-2010]
* [beaver-roberts-simons-tonhauser-2017]
* [abusch-2010]
* [karttunen-1973]
* [gazdar-1979]
* [heim-1983]
* [van-der-sandt-1992]
* [potts-2005]
-/

@[expose] public section

namespace TonhauserBeaverDegen2018

open Data.Statistics SimpleGraph

/-! ### The observed means -/

/-- The mean projectivity of a heterogeneous expression's content, Experiment 1a. -/
def Expression.projectivity (e : Expression) : ℚ := (heterogeneous e).projectivity.toRat

/-- Its mean not-at-issueness. -/
def Expression.notAtIssueness (e : Expression) : ℚ := (heterogeneous e).notAtIssueness.toRat

/-- The mean projectivity of a predicate's complement, Experiment 1b. -/
def Predicate.projectivity (p : Predicate) : ℚ := (predicates p).projectivity.toRat

/-- Its mean not-at-issueness. -/
def Predicate.notAtIssueness (p : Predicate) : ℚ := (predicates p).notAtIssueness.toRat

/-! ### Contents told apart in projectivity -/

/-- A printed mark that counts as a difference in means: starred, not marginal. -/
def Significance.Starred (s : Significance) : Prop := s ≠ .ns ∧ s ≠ .marginal

instance : DecidablePred Significance.Starred := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Table 1: the graph on the Experiment 1a contents whose edges are the pairs with a starred
difference in mean projectivity. -/
def distinguished1a : SimpleGraph Expression :=
  .fromRel fun a b ↦ ∃ r ∈ pairwise1a, r.first = a ∧ r.second = b ∧ r.significance.Starred

/-- Table 3: the graph on the Experiment 1b complements whose edges are the pairs with a starred
difference in mean projectivity. -/
def distinguished1b : SimpleGraph Predicate :=
  .fromRel fun a b ↦ ∃ r ∈ pairwise1b, r.first = a ∧ r.second = b ∧ r.significance.Starred

instance : DecidableRel distinguished1a.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

instance : DecidableRel distinguished1b.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

/-- A pair the table marks `n.s.` is not an edge, and neither is a marginal one. -/
example : ¬ distinguished1a.Adj .nrrc .know ∧ ¬ distinguished1a.Adj .stop .know := by
  decide +kernel

-- The presuppositions of *be annoyed*, *stop* and *only* differ pairwise.
theorem isNClique_annoyed_stop_only : distinguished1a.IsNClique 3 {.annoyed, .stop, .only} :=
  is3Clique_triple_iff.2 (by decide +kernel)

-- The complements of *reveal*, *confess* and *establish* were less projective than those of the
-- semi-factives and differed from each other.
theorem isNClique_learn_reveal_confess_establish :
    distinguished1b.IsNClique 4 {.learn, .reveal, .confess, .establish} := by
  rw [isNClique_iff, isClique_iff]
  exact ⟨by decide +kernel, rfl⟩

/-- In neither experiment can the contents be divided into two classes that keep apart every pair
differing in projectivity; the three presuppositions of *be annoyed*, *stop* and *only* already
cannot. -/
theorem not_colorable_two : ¬ distinguished1a.Colorable 2 ∧ ¬ distinguished1b.Colorable 2 :=
  ⟨fun h ↦ absurd (isNClique_annoyed_stop_only.isClique.card_le_of_colorable h) (by decide),
    fun h ↦ absurd (isNClique_learn_reveal_confess_establish.isClique.card_le_of_colorable h)
      (by decide)⟩

-- *know* was more projective than *discover* and not told apart from *be annoyed*, though
-- numerically lower.
theorem know_between :
    distinguished1a.Adj .discover .know ∧ ¬ distinguished1a.Adj .know .annoyed ∧
      Expression.discover.projectivity < Expression.know.projectivity ∧
      Expression.know.projectivity < Expression.annoyed.projectivity := by
  decide +kernel

/-! ### Hard and soft triggers -/

/-- The classification into hard and soft triggers as the paper cites it for the Experiment 1a
contents: *be annoyed* is a hard trigger, and *discover*, *stop* and *only* are soft triggers. -/
def Expression.hardness? : Expression → Option Presupposition.Hardness
  | .annoyed => some .hard
  | .discover | .stop | .only => some .soft
  | _ => none

-- Some differences follow the classification: the soft *discover* and *stop* against the hard
-- *be annoyed*.
theorem hard_soft_adj :
    ∀ s ∈ [Expression.discover, .stop], s.hardness? = some .soft ∧
      Expression.annoyed.hardness? = some .hard ∧ distinguished1a.Adj s .annoyed := by
  decide +kernel

/-- The soft triggers are not a class: the prejacent of *only* was less projective than the
pre-state of *stop*. -/
theorem soft_not_a_class :
    ∃ a b, a.hardness? = some .soft ∧ b.hardness? = some .soft ∧ distinguished1a.Adj a b ∧
      a.projectivity < b.projectivity :=
  ⟨.only, .stop, rfl, rfl, by decide +kernel⟩

/-- The complements of the hard emotive factives *be annoyed* and *be amused* were not told apart
from those of six soft semi-factives. -/
theorem hard_soft_not_adj :
    ∀ h ∈ [Predicate.annoyed, .amused],
      ∀ s ∈ [Predicate.notice, .aware, .realize, .see, .findOut, .learn],
        ¬ distinguished1b.Adj h s := by
  decide +kernel

/-! ### The Gradient Projection Principle -/

-- The prediction the paper draws from the principle before testing it: the content of a
-- non-restrictive relative clause is more not-at-issue than the complement of *discover*, and
-- more projective.
theorem discover_lt_nrrc :
    Expression.discover.notAtIssueness < Expression.nrrc.notAtIssueness ∧
      distinguished1a.Adj .discover .nrrc ∧
      Expression.discover.projectivity < Expression.nrrc.projectivity := by
  decide +kernel

/-- Among the complements of Experiment 1b, whenever one is told apart as the more projective it
is also at least as not-at-issue. -/
theorem le_of_adj_of_lt {p q : Predicate} (h : distinguished1b.Adj p q)
    (hpq : p.projectivity < q.projectivity) : p.notAtIssueness ≤ q.notAtIssueness := by
  revert p q; decide +kernel

-- In Experiment 1a the same holds of every pair but one: the pre-state of *stop* was more
-- projective than the prejacent of *only* and no more not-at-issue.
theorem le_of_adj_of_lt_1a {a b : Expression} (h : distinguished1a.Adj a b)
    (hab : a.projectivity < b.projectivity) :
    a.notAtIssueness ≤ b.notAtIssueness ∨ a = .only ∧ b = .stop := by
  revert a b; decide +kernel

theorem atIssuenessEffect_beta_pos (x : Experiment) : 0 < (atIssuenessEffect x).beta.toRat := by
  revert x; decide +kernel

/-- Not-at-issueness was a significant predictor of projectivity in every experiment but 2b. -/
theorem atIssuenessEffect_significant_iff (x : Experiment) :
    (atIssuenessEffect x).p.Significant 0.05 ↔ x ≠ .exp2b := by
  revert x; decide +kernel

end TonhauserBeaverDegen2018
