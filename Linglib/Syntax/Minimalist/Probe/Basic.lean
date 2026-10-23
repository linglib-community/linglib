module

public import Mathlib.Data.List.Basic

/-!
# Probes as interaction and satisfaction specifications

This file defines a probe over a goal type as two predicates on goals, following Deal's
interaction/satisfaction theory of Agree. A goal *interacts* with the probe when it bears features
the probe copies, and *satisfies* it when it bears features that halt the search. A search over an
ordered goal sequence stops at the first satisfying goal, and the probe Agrees with that goal when
it also interacts; a satisfying goal that does not interact absorbs the probe, Deal's satisfaction
without interaction. A search that finds no goal is failed Agree, tolerated under Preminger's
obligatory-operations model. A goal is licensed when the search reaches it, as for Béjar and Rezac;
which goals need licensing and which satisfy the probe come apart in general, as for Halpert's
Zulu L⁰, which every goal satisfies while only augmentless nominals need it. The full operation,
which copies from every interacting goal up to the satisfier, is `Probe.agree` in
`Probe/Agree.lean`.

Probe *specifications*, such as relativized targets and feature specifications, denote a `Probe`
by a `toProbe` map rather than re-implementing search. The search over a list is Relativized
Minimality keyed by position, `Probe.Finds` in `Probe/Minimal.lean`, and a horizon cuts the domain
the probe searches rather than relativizing the probe.

## Main definitions

* `Minimalist.Probe`: an interaction predicate and a satisfaction predicate on goals.
* `Minimalist.Probe.relativized`, `Minimalist.Probe.ofInt`, `Minimalist.Probe.insatiable`,
  `Minimalist.Probe.indiscriminate`: the probes `[INT:F, SAT:F]`, `[INT:F, SAT:⊤]`,
  `[INT:F, SAT:⊥]` and `[INT:⊤, SAT:⊤]`.
* `Minimalist.Probe.search`, `Minimalist.Probe.goal`: the first satisfying goal, and that goal
  when it interacts, the goal of Agree.
* `Minimalist.Probe.Licensed`, `Minimalist.Probe.AllLicensed`: a goal the search reaches, and
  every needy goal occurrence being reached.
* `Minimalist.Probe.cascade`: the first finding of an ordered sequence of probes.

## Main results

* `Minimalist.Probe.search_eq_some_iff_closest`: locality as list search.
* `Minimalist.Probe.search_isSome`: a search succeeds iff some goal satisfies the probe.
* `Minimalist.Probe.not_rel_of_search_eq_some`: the found goal is minimal for any precedence
  the sequence respects.
* `Minimalist.Probe.AllLicensed.countP_le_one`, `Minimalist.Probe.relativized_allLicensed_iff`:
  one search licenses at most one goal.
* `Minimalist.Probe.indiscriminate_allLicensed_iff`: under bare minimality only the closest goal
  may need licensing.

## References

* [deal-2025a], [deal-2024]
* [bejar-rezac-2003], [preminger-2014], [halpert-2012]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

variable {α : Type*}

/-- A probe over goals of type `α` is an interaction predicate, the goals it copies from, and a
satisfaction predicate, the goals that halt its search ([deal-2025a]). -/
structure Probe (α : Type*) where
  /-- The goal bears features the probe copies. -/
  int : α → Prop
  /-- The goal bears features that halt the probe's search. -/
  sat : α → Prop
  /-- Interaction is decidable, so that Agree runs. -/
  [decInt : DecidablePred int]
  /-- Satisfaction is decidable, so that the search runs. -/
  [decSat : DecidablePred sat]

attribute [instance] Probe.decInt Probe.decSat

namespace Probe

variable (f : α → Prop) [DecidablePred f]

/-- The probe relativized to `f`, which interacts with and is satisfied by the same goals, the
`[INT:F, SAT:F]` probe of [bejar-rezac-2003] and [preminger-2014]. -/
def relativized : Probe α := ⟨f, f⟩

/-- The probe satisfied by every goal and interacting with those that pass `f`, which Agrees
with the closest goal iff that goal is active, the Active Goal Hypothesis of [chomsky-2000]. -/
def ofInt : Probe α := ⟨f, fun _ ↦ True⟩

/-- The insatiable probe interacting with `f`, which no goal halts, so that it copies from every
`f`-goal in its domain, Multiple Agree ([deal-2025a]). -/
def insatiable : Probe α := ⟨f, fun _ ↦ False⟩

/-- The indiscriminate probe, which every goal satisfies and interacts with, so that bare
minimality delivers the closest goal ([halpert-2012]'s L⁰). -/
def indiscriminate : Probe α := relativized fun _ ↦ True

@[simp] theorem relativized_int : (relativized f).int = f := rfl
@[simp] theorem relativized_sat : (relativized f).sat = f := rfl
@[simp] theorem ofInt_int : (ofInt f).int = f := rfl
@[simp] theorem ofInt_sat (a : α) : (ofInt f).sat a := trivial
@[simp] theorem insatiable_int : (insatiable f).int = f := rfl
@[simp] theorem insatiable_sat (a : α) : ¬ (insatiable f).sat a := id
@[simp] theorem indiscriminate_int (a : α) : (indiscriminate : Probe α).int a := trivial
@[simp] theorem indiscriminate_sat (a : α) : (indiscriminate : Probe α).sat a := trivial

/-! ### Search -/

/-- The goal a probe finds in an ordered goal sequence, the first goal that satisfies it. -/
def search (p : Probe α) (goals : List α) : Option α :=
  goals.find? (p.sat ·)

/-- The goal of Agree, the found goal if it interacts with the probe. A satisfying goal that does
not interact absorbs the probe. -/
def goal (p : Probe α) (goals : List α) : Option α :=
  (p.search goals).filter (p.int ·)

variable {p : Probe α} {goals : List α}

@[simp]
theorem search_eq_none_iff : p.search goals = none ↔ ∀ a ∈ goals, ¬ p.sat a := by
  simp [search, List.find?_eq_none]

theorem mem_of_search_eq_some {a : α} (h : p.search goals = some a) : a ∈ goals :=
  List.mem_of_find?_eq_some h

theorem sat_of_search_eq_some {a : α} (h : p.search goals = some a) : p.sat a := by
  simpa using List.find?_some h

theorem search_pair_of_imp {a b : α} (h : p.sat b → p.sat a) :
    p.search [a, b] = if p.sat a then some a else none := by
  by_cases ha : p.sat a <;> by_cases hb : p.sat b <;> simp_all [search]

theorem goal_eq_some_iff {a : α} :
    p.goal goals = some a ↔ p.search goals = some a ∧ p.int a := by
  simp [goal, Option.filter_eq_some_iff]

@[simp] theorem ofInt_search : (ofInt f).search goals = goals.head? := by
  cases goals <;> rfl

theorem ofInt_goal_eq_some_iff {a : α} :
    (ofInt f).goal goals = some a ↔ goals.head? = some a ∧ f a := by
  rw [goal_eq_some_iff, ofInt_search]; rfl

theorem goal_eq_none_of_not_int {a : α} (h : p.search goals = some a) (ha : ¬ p.int a) :
    p.goal goals = none := by
  simp [goal, h, ha]

@[simp] theorem search_nil : p.search [] = none := rfl

theorem goal_le_search {a : α} (h : p.goal goals = some a) : p.search goals = some a :=
  (goal_eq_some_iff.mp h).1

theorem goal_eq_search_of_int (h : ∀ a, p.sat a → p.int a) :
    p.goal goals = p.search goals := by
  rw [goal]
  cases hs : p.search goals with
  | none => rfl
  | some a => simp [h a (sat_of_search_eq_some hs)]

theorem relativized_goal :
    (relativized f).goal goals = (relativized f).search goals :=
  goal_eq_search_of_int fun _ h ↦ h

theorem goal_eq_none_iff : p.goal goals = none ↔ ¬ ∃ a, p.search goals = some a ∧ p.int a := by
  simp only [← Option.not_isSome_iff_eq_none, Option.isSome_iff_exists, goal_eq_some_iff]

/-- Locality as list search. The probe finds `a` iff `a` satisfies it and every earlier goal
does not, so that nothing intervenes. -/
theorem search_eq_some_iff_closest {a : α} :
    p.search goals = some a ↔
      p.sat a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, ¬ p.sat b := by
  simp [search, List.find?_eq_some_iff_append]

/-- Over a goal sequence in which no later goal precedes an earlier one, the found goal is
minimal among the satisfying goals. -/
theorem not_rel_of_search_eq_some {r : α → α → Prop} {a : α}
    (hord : goals.Pairwise fun x y ↦ ¬ r y x) (h : p.search goals = some a) :
    ∀ b ∈ goals, p.sat b → b ≠ a → ¬ r b a := by
  obtain ⟨-, l₁, l₂, rfl, hl₁⟩ := search_eq_some_iff_closest.mp h
  intro b hb hvb hne hba
  rcases List.mem_append.mp hb with hb | hb
  · exact absurd hvb (hl₁ b hb)
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact hne rfl
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 b hb hba

/-! ### Success -/

/-- A probe finds a goal iff some goal satisfies it. -/
@[simp]
theorem search_isSome : (p.search goals).isSome ↔ ∃ a ∈ goals, p.sat a := by
  simp [search, List.find?_isSome]

theorem search_isSome_mono {q : Probe α} (h : ∀ a ∈ goals, p.sat a → q.sat a)
    (hp : (p.search goals).isSome) : (q.search goals).isSome := by
  obtain ⟨a, ha, hva⟩ := search_isSome.1 hp
  exact search_isSome.2 ⟨a, ha, h a ha hva⟩

/-! ### Licensing -/

/-- A goal is licensed by a probe iff the probe's single search reaches it, since for
[bejar-rezac-2003] licensing is an Agree relation with the probe. -/
def Licensed (p : Probe α) (goals : List α) (a : α) : Prop :=
  p.search goals = some a

instance [DecidableEq α] (p : Probe α) (goals : List α) (a : α) :
    Decidable (p.Licensed goals a) :=
  inferInstanceAs (Decidable (p.search goals = some a))

theorem Licensed.unique {a b : α} (ha : p.Licensed goals a) (hb : p.Licensed goals b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

theorem licensed_iff_closest {a : α} :
    p.Licensed goals a ↔ p.sat a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, ¬ p.sat b :=
  search_eq_some_iff_closest

theorem Licensed.mem {a : α} (h : p.Licensed goals a) : a ∈ goals :=
  mem_of_search_eq_some h

theorem Licensed.sat {a : α} (h : p.Licensed goals a) : p.sat a :=
  sat_of_search_eq_some h

theorem indiscriminate_licensed_iff {a : α} :
    (indiscriminate : Probe α).Licensed goals a ↔ goals.head? = some a := by
  cases goals <;> exact Iff.rfl

/-- The goals that `needs` selects are all licensed by the probe's single search when each of them
satisfies the probe and no goal before it does. The condition is on occurrences, like
`List.Nodup`, so one search licenses one occurrence and two equal needy goals are not both
licensed. -/
def AllLicensed (p : Probe α) (needs : α → Prop) (goals : List α) : Prop :=
  (∀ a ∈ goals, needs a → p.sat a) ∧ goals.Pairwise fun a b ↦ needs b → ¬ p.sat a

instance (p : Probe α) (needs : α → Prop) [DecidablePred needs] (goals : List α) :
    Decidable (p.AllLicensed needs goals) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {needs : α → Prop}

@[simp] theorem allLicensed_nil : p.AllLicensed needs [] := by simp [AllLicensed]

theorem allLicensed_cons {a : α} :
    p.AllLicensed needs (a :: goals) ↔
      (needs a → p.sat a) ∧ (∀ b ∈ goals, needs b → ¬ p.sat a) ∧
        p.AllLicensed needs goals := by
  simp only [AllLicensed, List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
  tauto

theorem AllLicensed.licensed (h : p.AllLicensed needs goals) {a : α} (ha : a ∈ goals)
    (hn : needs a) : p.Licensed goals a := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  exact search_eq_some_iff_closest.2 ⟨h.1 a ha hn, l₁, l₂, rfl,
    fun b hb ↦ (List.pairwise_append.1 h.2).2.2 b hb a List.mem_cons_self hn⟩

theorem allLicensed_of_forall_not (h : ∀ a ∈ goals, ¬ needs a) :
    p.AllLicensed needs goals :=
  ⟨fun a ha hn ↦ absurd hn (h a ha),
    List.pairwise_of_forall_mem_list fun _ _ b hb hn ↦ absurd hn (h b hb)⟩

/-- One search licenses at most one needy goal. -/
theorem AllLicensed.countP_le_one [DecidablePred needs] (h : p.AllLicensed needs goals) :
    goals.countP (needs ·) ≤ 1 := by
  induction goals with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl, h⟩ := allLicensed_cons.1 h
    rw [List.countP_cons]
    by_cases hn : needs a
    · rw [List.countP_eq_zero.2 fun b hb hb' ↦ hl b hb (of_decide_eq_true hb') (ha hn)]
      simp [hn]
    · simpa [hn] using ih h

theorem allLicensed_iff_forall_licensed (hnd : goals.Nodup) :
    p.AllLicensed needs goals ↔ ∀ a ∈ goals, needs a → p.Licensed goals a := by
  refine ⟨fun h a ha hn ↦ h.licensed ha hn, fun h ↦ ?_⟩
  induction goals with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hx, hnd⟩ := List.nodup_cons.1 hnd
    have hsat : ∀ b ∈ l, needs b → ¬ p.sat x := fun b hb hn hs ↦ by
      have := h b (List.mem_cons_of_mem _ hb) hn
      simp only [Licensed, search, List.find?_cons, hs, decide_true, Option.some.injEq] at this
      subst this
      exact hx hb
    refine allLicensed_cons.2 ⟨fun hn ↦ (h x List.mem_cons_self hn).sat, hsat, ih hnd ?_⟩
    intro b hb hn
    simpa [Licensed, search, List.find?_cons, hsat b hb hn] using
      h b (List.mem_cons_of_mem _ hb) hn

/-- On the diagonal, where the probe is relativized to exactly the needy goals, all needy goals
are licensed iff at most one goal is needy, one search licensing one goal, the fact behind
[preminger-2014]'s person restriction. -/
theorem relativized_allLicensed_iff :
    (relativized f).AllLicensed f goals ↔ goals.countP (f ·) ≤ 1 := by
  refine ⟨AllLicensed.countP_le_one, fun h ↦ ?_⟩
  induction goals with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons] at h
    refine allLicensed_cons.2 ⟨id, fun b hb hfb ha ↦ ?_, ih (by split at h <;> omega)⟩
    have := List.countP_pos_iff (p := (f ·)).2 ⟨b, hb, decide_eq_true hfb⟩
    simp only [show f a from ha, decide_true, ite_true] at h
    omega

/-- Licensing by the indiscriminate probe allows no needy goal below the head of the sequence,
the highest-element condition of [halpert-2012]. -/
theorem indiscriminate_allLicensed_iff :
    (indiscriminate : Probe α).AllLicensed needs goals ↔ ∀ a ∈ goals.tail, ¬ needs a := by
  cases goals with
  | nil => simp
  | cons a l =>
    simpa [indiscriminate, relativized, AllLicensed] using
      fun h ↦ List.pairwise_of_forall_mem_list fun _ _ b hb ↦ h b hb

/-! ### Cascades -/

/-- The goal an ordered sequence of probes delivers, the first probe's finding, else the next's,
and so on. This is `Probe.search` at the goal level composed with `List.findSome?` at the probe
level, and also the single-slot morphological competition in which the first probe with output
wins the slot, as in [preminger-2014] where π⁰'s clitic beats #⁰'s exponent beats nothing. -/
def cascade (ps : List (Probe α)) (goals : List α) : Option α :=
  ps.findSome? (·.search goals)

variable {ps : List (Probe α)}

@[simp]
theorem cascade_eq_none_iff : cascade ps goals = none ↔ ∀ q ∈ ps, ∀ a ∈ goals, ¬ q.sat a := by
  simp [cascade, List.findSome?_eq_none_iff]

theorem cascade_cons {q : Probe α} :
    cascade (q :: ps) goals = (q.search goals <|> cascade ps goals) := by
  rw [cascade, List.findSome?_cons]
  cases q.search goals <;> rfl

@[simp] theorem cascade_nil : cascade ([] : List (Probe α)) goals = none := rfl

@[simp] theorem cascade_singleton {q : Probe α} : cascade [q] goals = q.search goals := by
  rw [cascade_cons, cascade_nil]
  cases q.search goals <;> rfl

theorem cascade_append {qs : List (Probe α)} :
    cascade (ps ++ qs) goals = (cascade ps goals <|> cascade qs goals) := by
  unfold cascade
  rw [List.findSome?_append]
  cases ps.findSome? (·.search goals) <;> rfl

theorem exists_licensed_of_cascade_eq_some {a : α} (h : cascade ps goals = some a) :
    ∃ q ∈ ps, q.Licensed goals a :=
  List.exists_of_findSome?_eq_some h

theorem mem_of_cascade_eq_some {a : α} (h : cascade ps goals = some a) : a ∈ goals :=
  let ⟨_, _, hq⟩ := exists_licensed_of_cascade_eq_some h
  mem_of_search_eq_some hq

end Probe

end Minimalist
