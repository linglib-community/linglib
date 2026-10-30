module

public import Linglib.Data.Examples.BachBrownMarslenWilson1986
public import Linglib.Data.Experiments.BachBrownMarslenWilson1986
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.NormNum

/-!
# Bach, Brown and Marslen-Wilson (1986): crossed and nested dependencies

In Dutch and German a clause can end in a cluster of verbs that follows all their noun phrases.
Dutch orders the cluster from the matrix verb down and German from the most deeply embedded verb
up, so the dependencies between noun phrases and verbs cross in Dutch and nest in German, and
[the German order is the only one whose dependency tree is planar](##isPlanar_graph_iff), the only
one a push-down store can match ([evers-1975]; for Dutch, [no context-free grammar assigns the
clusters their trees](##BresnanEtAl1982.not_strongly_contextFree)). Yet
[bach-brown-marslen-wilson-1986] found the Dutch sentences the easier to understand from two
embedded clauses on.

The paper's explanation is what a listener can do with a clause when its verb arrives: a clause
can be connected up to the matrix once every verb above it has been heard, and
[that is the case on arrival exactly when its dependency crosses every dependency above
it](##held_eq_zero_iff_alternate), so [the Dutch order is the only one that connects every clause
on arrival](##forall_held_eq_zero_iff). The German order holds each clause below the matrix in
store until the verbs above it arrive; from three verbs on, the innermost clause is held past the
next verb, and [that is where the Dutch advantage in comprehension appears](##forall_gap_lt_iff).
The Dutch advantage by noun phrase [peaks at the innermost clause](##errorDifference_lt_np3_iff),
the clause German holds longest, although both orders connect it at the last verb; summed over a
cluster, the time clauses are held and the time they join the matrix
[differ by a constant](##sum_connection), so only the breakdown by noun phrase tells them apart.

## Implementation notes

* A cluster of `n` verbs is a permutation `σ` of `Fin n`: the verbs are indexed from the matrix
  verb `0` down, and `σ i` is the position of verb `i` in the cluster. The Dutch order is `1`, the
  German `Fin.revPerm` (Figure 1).
* The noun phrases are the subjects of the verbs, in the order of their verbs, which is what the
  question task asks about; the object of the last verb is left out. In the string of subjects and
  cluster, subject `i` is at `i` and verb `i` at `n + σ i`, so two dependencies cross when they
  `DependencyGrammar.Alternate`.
* The dependency tree `graph` adds to Figure 1's arcs between verbs and their subjects the arcs
  from each verb to the verb it embeds, so that the matrix verb roots a tree; those arcs join
  neighbours in either order and cross nothing. Its words are a parameter, since no theorem reads
  them.
* A Level-`n` Test sentence has an `n`-verb cluster.
* The model ranks cluster orders. Why both languages break down from Level 3 on, the paper's
  second open question (p. 261), is not modelled.

## Errata

* Table 5's German/Participle NP2 cell is 0.67, while Table 4 gives 1.07 − 0.38 = 0.69; every
  other cell of Table 5 is the difference of the Table 4 cells
  (`errorDifference_eq_sub_iff`).

## References

* [bach-brown-marslen-wilson-1986]
* [evers-1975]
* [bresnan-etal-1982]
-/

@[expose] public section

namespace BachBrownMarslenWilson1986

open Finset DependencyGrammar Data.Experiments

variable {n : ℕ} (σ : Equiv.Perm (Fin n))

/-! ### Clauses held in store -/

/-- The cluster position at which the clause of verb `i` is connected up to the matrix: the last
position among the verbs `0, …, i` from the matrix down to it. -/
def connection (i : Fin n) : Fin n := (Iic i).sup' nonempty_Iic σ

/-- The number of verbs for which the clause of verb `i` is held in store: those after its own
verb, up to the one that connects it. -/
def held (i : Fin n) : ℕ := connection σ i - σ i

variable {σ}

theorem connection_le_iff {i k : Fin n} : connection σ i ≤ k ↔ ∀ j ≤ i, σ j ≤ k := by
  simp [connection]

theorem apply_le_connection {i j : Fin n} (h : j ≤ i) : σ j ≤ connection σ i :=
  le_sup' σ (mem_Iic.2 h)

theorem le_connection (i : Fin n) : σ i ≤ connection σ i := apply_le_connection le_rfl

theorem held_add (i : Fin n) : held σ i + σ i = connection σ i :=
  Nat.sub_add_cancel (le_connection i)

-- A clause is held for no verb exactly when its verb's position is a left-to-right maximum of `σ`.
theorem held_eq_zero_iff {i : Fin n} : held σ i = 0 ↔ ∀ j < i, σ j < σ i := by
  rw [held, Nat.sub_eq_zero_iff_le, ← Fin.le_def, connection_le_iff]
  refine ⟨fun h j hj ↦ (h j hj.le).lt_of_ne (σ.injective.ne hj.ne), fun h j hj ↦ ?_⟩
  rcases hj.lt_or_eq with hj | rfl
  exacts [(h j hj).le, le_rfl]

@[simp] theorem connection_one (i : Fin n) : connection 1 i = i :=
  le_antisymm (connection_le_iff.2 fun _ ↦ id) (le_connection (σ := 1) i)

@[simp] theorem held_one (i : Fin n) : held 1 i = 0 := by simp [held]

theorem val_connection_revPerm (i : Fin n) : (connection Fin.revPerm i : ℕ) = n - 1 := by
  have h : connection Fin.revPerm i = Fin.revPerm ⟨0, i.pos⟩ :=
    le_antisymm (connection_le_iff.2 fun j _ ↦ Fin.rev_le_rev.2 (Nat.zero_le _))
      (apply_le_connection (Nat.zero_le _))
  simp [h]

@[simp] theorem held_revPerm (i : Fin n) : held Fin.revPerm i = i := by
  have := i.isLt
  rw [held, val_connection_revPerm, Fin.revPerm_apply, Fin.val_rev]
  omega

-- Summed over a cluster, the time the clauses are connected up to the matrix exceeds the time
-- they are held by the sum of the positions, which is the same for every order.
theorem sum_connection :
    ∑ i, (connection σ i : ℕ) = ∑ i, held σ i + ∑ i : Fin n, (i : ℕ) := by
  rw [← Equiv.sum_comp σ (fun i : Fin n ↦ (i : ℕ)), ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ (held_add i).symm

/-! ### Crossed and nested dependencies -/

/-- The position of the subject of verb `i`, among the subjects before the cluster. -/
def subject (i : Fin n) : Fin (n + n) := Fin.castAdd n i

variable (σ) in
/-- The position of verb `i`, in the cluster after the subjects. -/
def verb (i : Fin n) : Fin (n + n) := Fin.natAdd n (σ i)

theorem alternate_iff {i j : Fin n} :
    Alternate (subject i) (verb σ i) (subject j) (verb σ j) ↔ i < j ∧ σ i < σ j := by
  have := j.isLt
  simp only [Alternate, subject, verb, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- A clause is connected up to the matrix as soon as its verb is heard exactly when its
dependency crosses the dependency of every clause above it. -/
theorem held_eq_zero_iff_alternate {i : Fin n} :
    held σ i = 0 ↔ ∀ j < i, Alternate (subject j) (verb σ j) (subject i) (verb σ i) := by
  simp only [held_eq_zero_iff, alternate_iff]
  exact forall₂_congr fun j hj ↦ (and_iff_right hj).symm

private theorem eq_one_of_strictMono {τ : Equiv.Perm (Fin n)} (h : StrictMono τ) : τ = 1 :=
  Equiv.ext fun i ↦ Fin.ext (Fin.coe_orderIso_apply (h.orderIsoOfSurjective τ τ.surjective) i)

/-- The crossed, Dutch order is the only cluster order in which every clause is connected up to
the matrix as soon as its verb is heard. -/
theorem forall_held_eq_zero_iff : (∀ i, held σ i = 0) ↔ σ = 1 := by
  refine ⟨fun h ↦ eq_one_of_strictMono fun j i hji ↦ held_eq_zero_iff.1 (h i) j hji, ?_⟩
  rintro rfl i
  exact held_one i

theorem forall_not_alternate_iff :
    (∀ i j, ¬ Alternate (subject i) (verb σ i) (subject j) (verb σ j)) ↔ σ = Fin.revPerm := by
  simp only [alternate_iff, not_and, not_lt]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have : Fin.revPerm * σ = 1 := eq_one_of_strictMono fun i j hij ↦
      Fin.rev_lt_rev.2 ((h i j hij).lt_of_ne (σ.injective.ne hij.ne'))
    exact Equiv.ext fun i ↦ Fin.rev_eq_iff.1 (Equiv.congr_fun this i)
  · rintro rfl i j hij
    exact Fin.rev_le_rev.2 hij.le

theorem exists_one_lt_held_revPerm_iff :
    (∃ i, 1 < held (Fin.revPerm : Equiv.Perm (Fin n)) i) ↔ 2 < n := by
  simp only [held_revPerm]
  exact ⟨fun ⟨i, hi⟩ ↦ by have := i.isLt; omega, fun h ↦ ⟨⟨2, h⟩, by simp⟩⟩

@[simp] theorem subject_inj {i j : Fin n} : subject i = subject j ↔ i = j := by
  simp [subject, Fin.ext_iff]

@[simp] theorem verb_inj {i j : Fin n} : verb σ i = verb σ j ↔ i = j := by
  simp [verb]

@[simp] theorem subject_ne_verb (i j : Fin n) : subject i ≠ verb σ j := by
  simp [subject, verb, Fin.ext_iff]; omega

@[simp] theorem verb_ne_subject (i j : Fin n) : verb σ j ≠ subject i := (subject_ne_verb i j).symm

/-! ### The dependency tree of a cluster -/

section Graph

open Morphology (Word)

variable (σ) in
/-- The dependency tree of a cluster over the words `w`, the subjects before the verbs: each verb
heads its subject and the verb it embeds, and the matrix verb is the root. The arcs are unlabelled,
as in Figure 1, which draws the arcs between verbs and their arguments only. -/
def graph [NeZero n] (w : Fin (n + n) → Word) : Graph Unit (n + n) where
  words := w
  label a b := if (∃ i, a = verb σ i ∧ b = subject i) ∨
      ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ a = verb σ i ∧ b = verb σ j then some () else none
  root := verb σ 0

/-- The depth of a position in the tree: verb `i` at `2 i`, its subject one below it. -/
private def depth (σ : Equiv.Perm (Fin n)) : Fin (n + n) → ℕ :=
  Fin.addCases (fun i ↦ 2 * i + 1) (fun k ↦ 2 * σ.symm k)

private theorem depth_subject (i : Fin n) : depth σ (subject i) = 2 * i + 1 := by
  simp only [depth, subject, Fin.addCases_left]

private theorem depth_verb (i : Fin n) : depth σ (verb σ i) = 2 * i := by
  simp only [depth, verb, Fin.addCases_right, Equiv.symm_apply_apply]

variable [NeZero n] {w : Fin (n + n) → Word}

@[simp] theorem graph_adj {a b : Fin (n + n)} :
    (graph σ w).Adj a b ↔ (∃ i, a = verb σ i ∧ b = subject i) ∨
      ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ a = verb σ i ∧ b = verb σ j := by
  simp only [Graph.Adj, graph]
  split_ifs with h <;> simp [h]

private theorem depth_lt_of_adj {a b : Fin (n + n)} (h : (graph σ w).Adj a b) :
    depth σ a < depth σ b := by
  rcases graph_adj.1 h with ⟨i, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩ <;>
    simp only [depth_subject, depth_verb] <;> omega

private theorem depth_le_of_dominates {a b : Fin (n + n)} (h : Dominates (graph σ w) a b) :
    depth σ a ≤ depth σ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (depth_lt_of_adj hbc).le

-- The graph is a dependency tree, a check on the construction.
theorem isTree_graph : (graph σ w).IsTree where
  not_dominates_of_adj _ _ h hd := (depth_lt_of_adj h).not_ge (depth_le_of_dominates hd)
  leftUnique_adj a b c ha hb := by
    rcases graph_adj.1 ha with ⟨i, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩ <;>
      rcases graph_adj.1 hb with ⟨i', rfl, h⟩ | ⟨i', j', hij', rfl, h⟩
    · exact congrArg (verb σ) (subject_inj.1 h)
    · exact absurd h (subject_ne_verb _ _)
    · exact absurd h (verb_ne_subject _ _)
    · obtain rfl := verb_inj.1 h
      exact verb_inj.2 (Fin.ext (by omega))
  root_dominates p := by
    have hv (k : ℕ) (hk : k < n) : Dominates (graph σ w) (verb σ 0) (verb σ ⟨k, hk⟩) := by
      induction k with
      | zero => exact (show (⟨0, hk⟩ : Fin n) = 0 by simp) ▸ .refl
      | succ k ih =>
        exact (ih (by omega)).tail (graph_adj.2 (.inr ⟨⟨k, by omega⟩, ⟨k + 1, hk⟩, rfl, rfl, rfl⟩))
    induction p using Fin.addCases with
    | left i => exact (hv i i.isLt).tail (graph_adj.2 (.inl ⟨i, rfl, rfl⟩))
    | right k =>
      have h := hv (σ.symm k) (σ.symm k).isLt
      simp only [Fin.eta, verb, Equiv.apply_symm_apply] at h
      exact h

/-- The nested, German order is the only cluster order whose dependency tree is planar, no two of
its arcs crossing. -/
theorem isPlanar_graph_iff : (graph σ w).IsPlanar ↔ σ = Fin.revPerm := by
  refine ⟨fun h ↦ forall_not_alternate_iff.1 fun i j ↦
    h (.inr (graph_adj.2 (.inl ⟨i, rfl, rfl⟩))) (.inr (graph_adj.2 (.inl ⟨j, rfl, rfl⟩))), ?_⟩
  rintro rfl a b c d hab hcd
  simp only [Graph.Linked, graph_adj] at hab hcd
  rcases hab with (⟨⟨i, hi⟩, rfl, rfl⟩ | ⟨⟨i, hi⟩, ⟨i', hi'⟩, hii, rfl, rfl⟩) |
      (⟨⟨i, hi⟩, rfl, rfl⟩ | ⟨⟨i, hi⟩, ⟨i', hi'⟩, hii, rfl, rfl⟩) <;>
    rcases hcd with (⟨⟨j, hj⟩, rfl, rfl⟩ | ⟨⟨j, hj⟩, ⟨j', hj'⟩, hjj, rfl, rfl⟩) |
      (⟨⟨j, hj⟩, rfl, rfl⟩ | ⟨⟨j, hj⟩, ⟨j', hj'⟩, hjj, rfl, rfl⟩) <;>
    simp only [Alternate, subject, verb, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd,
      Fin.revPerm_apply, Fin.val_rev] at * <;>
    omega

end Graph

/-! ### The comprehension task -/

/-- The Paraphrase score less the Test score of a row of comprehension scores, the difference in
error rate that Figure 3 plots. -/
def Comprehension.gap (r : Comprehension) : ℚ := r.para.toRat - r.test.toRat

/-- Table 3 and Figure 3: on the comprehension task, the Dutch group's Test–Paraphrase
difference is below both German groups' exactly at the level at which the German order first
holds a clause past the next verb, Level 3 rather than Level 2, where "the higher structure can be
immediately completed when the next verb is heard" (Discussion, p. 261). The rating means of
Table 1 put the Dutch difference lowest from Level 2 on, by 0.04 against German/Participle at
Level 2. -/
theorem forall_gap_lt_iff {r : Comprehension} (hr : r ∈ comprehension) (hd : r.group = .dutch) :
    (∀ s ∈ comprehension, s.level = r.level → s.group ≠ .dutch → r.gap < s.gap) ↔
      ∃ i, 1 < held (Fin.revPerm : Equiv.Perm (Fin r.level)) i := by
  rw [exists_one_lt_held_revPerm_iff]
  simp only [comprehension, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hd <;>
    simp [comprehension, Comprehension.gap, Decimal.toRat] <;> norm_num

/-- The verb whose subject a questioned noun phrase of a Level 3 sentence is. -/
def NounPhrase.verb : NounPhrase → Fin 3
  | .np1 => 0
  | .np2 => 1
  | .np3 => 2

/-- How far the Dutch Test–Paraphrase difference of error rate lies below a German group's. -/
def advantage (g : Group) (k : NounPhrase) : ℚ :=
  (errorDifference g k).difference.toRat - (errorDifference .dutch k).difference.toRat

/-- Tables 4 and 5 and the Discussion, pp. 260–261: against either German group, the Dutch
advantage in the Test–Paraphrase difference of error rate is greatest for NP3, as the time the
German order holds a clause is greatest for the innermost clause. The time at which a clause is
connected up to the matrix predicts no advantage there, since both orders connect the innermost
clause at the last verb (`connection_one`, `val_connection_revPerm`). With German/Participle, the
advantage for NP1 exceeds that for NP2, against the time held. -/
theorem errorDifference_lt_np3_iff (g : Group) (hg : g ≠ .dutch) (k : NounPhrase) :
    advantage g k < advantage g .np3 ↔
      held Fin.revPerm k.verb - held 1 k.verb <
        held Fin.revPerm NounPhrase.np3.verb - held 1 NounPhrase.np3.verb := by
  cases g <;> cases k <;> simp_all [advantage, errorDifference, NounPhrase.verb, Decimal.toRat] <;>
    norm_num

-- Errata: Table 5 is Table 4's Paraphrase minus Test score in every cell but one
theorem errorDifference_eq_sub_iff (g : Group) (k : NounPhrase) :
    (errorDifference g k).difference.toRat =
        (comprehensionByNP g k).para.toRat - (comprehensionByNP g k).test.toRat ↔
      (g, k) ≠ (.germanPart, .np2) := by
  cases g <;> cases k <;> simp [errorDifference, comprehensionByNP, Decimal.toRat] <;> norm_num

end BachBrownMarslenWilson1986
