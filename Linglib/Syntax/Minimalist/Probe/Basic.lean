module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Probes as interaction and satisfaction specifications

This file defines a probe over a goal type as two predicates on goals, following Deal's
interaction/satisfaction theory of Agree. A goal *interacts* with the probe when it bears features
the probe copies, and *satisfies* it when it bears features that halt the search. A search over an
ordered goal sequence stops at the first satisfying goal, and the probe Agrees with that goal when
it also interacts; a satisfying goal that does not interact absorbs the probe, Deal's satisfaction
without interaction. A search that finds no goal is failed Agree, tolerated under Preminger's
obligatory-operations model. Probes are ordered by their two conditions, and reading goals through a
map is a lattice homomorphism. The full operation,
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
* `Minimalist.Probe.comap`: a probe read through a map into its goals, as a probe on the
  positions of a tree reads the features of the term at each.
* `Minimalist.Probe.comapLatticeHom`: `comap` as a lattice homomorphism.

## Main results

* `Minimalist.Probe.search_eq_some_iff_closest`: locality as list search.
* `Minimalist.Probe.search_isSome`: a search succeeds iff some goal satisfies the probe.
* `Minimalist.Probe.not_rel_of_search_eq_some`: the found goal is minimal for any precedence
  the sequence respects.
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

/-- The probe satisfied by every goal and interacting with those that pass `f`: its search stops at
the first goal listed and Agrees with it iff `f` holds of it. With `f` activity, this is
[chomsky-2000]'s Agree with a goal "both local and active", an inactive goal blocking Agree with an
active one below it as in the defective intervention of (42), only over a list of goals that match
the probe, since a listed goal that does not match would stop the search too. -/
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

/-- The probe on `β` that reads each goal through `f`. -/
def comap {β : Type*} (f : β → α) (p : Probe α) : Probe β :=
  ⟨fun b ↦ p.int (f b), fun b ↦ p.sat (f b)⟩

@[simp] theorem comap_int {β : Type*} (f : β → α) (p : Probe α) (b : β) :
    (p.comap f).int b ↔ p.int (f b) := .rfl

@[simp] theorem comap_sat {β : Type*} (f : β → α) (p : Probe α) (b : β) :
    (p.comap f).sat b ↔ p.sat (f b) := .rfl

/-! ### The order on probes -/

@[ext]
theorem ext {p q : Probe α} (hi : ∀ a, p.int a ↔ q.int a) (hs : ∀ a, p.sat a ↔ q.sat a) :
    p = q := by
  rcases p with @⟨pi, ps, dpi, dps⟩
  rcases q with @⟨qi, qs, dqi, dqs⟩
  obtain rfl : pi = qi := funext fun a ↦ propext (hi a)
  obtain rfl : ps = qs := funext fun a ↦ propext (hs a)
  obtain rfl : dpi = dqi := Subsingleton.elim _ _
  obtain rfl : dps = dqs := Subsingleton.elim _ _
  rfl

/-- Probes are ordered by their conditions: a smaller probe interacts with fewer goals and is
satisfied by fewer. -/
instance : PartialOrder (Probe α) where
  le p q := (∀ a, p.int a → q.int a) ∧ ∀ a, p.sat a → q.sat a
  le_refl _ := ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  le_trans _ _ _ h₁ h₂ := ⟨fun a h ↦ h₂.1 a (h₁.1 a h), fun a h ↦ h₂.2 a (h₁.2 a h)⟩
  le_antisymm _ _ h₁ h₂ := ext (fun a ↦ ⟨h₁.1 a, h₂.1 a⟩) fun a ↦ ⟨h₁.2 a, h₂.2 a⟩

theorem le_def {p q : Probe α} :
    p ≤ q ↔ (∀ a, p.int a → q.int a) ∧ ∀ a, p.sat a → q.sat a :=
  .rfl

/-- The join of two probes interacts with and is satisfied by the goals of either, and their meet
by the goals of both. -/
instance : Lattice (Probe α) where
  sup p q := ⟨fun a ↦ p.int a ∨ q.int a, fun a ↦ p.sat a ∨ q.sat a⟩
  le_sup_left _ _ := ⟨fun _ ↦ .inl, fun _ ↦ .inl⟩
  le_sup_right _ _ := ⟨fun _ ↦ .inr, fun _ ↦ .inr⟩
  sup_le _ _ _ h₁ h₂ := ⟨fun a h ↦ h.elim (h₁.1 a) (h₂.1 a), fun a h ↦ h.elim (h₁.2 a) (h₂.2 a)⟩
  inf p q := ⟨fun a ↦ p.int a ∧ q.int a, fun a ↦ p.sat a ∧ q.sat a⟩
  inf_le_left _ _ := ⟨fun _ ↦ And.left, fun _ ↦ And.left⟩
  inf_le_right _ _ := ⟨fun _ ↦ And.right, fun _ ↦ And.right⟩
  le_inf _ _ _ h₁ h₂ := ⟨fun a h ↦ ⟨h₁.1 a h, h₂.1 a h⟩, fun a h ↦ ⟨h₁.2 a h, h₂.2 a h⟩⟩

@[simp] theorem sup_int (p q : Probe α) (a : α) : (p ⊔ q).int a ↔ p.int a ∨ q.int a := .rfl
@[simp] theorem sup_sat (p q : Probe α) (a : α) : (p ⊔ q).sat a ↔ p.sat a ∨ q.sat a := .rfl
@[simp] theorem inf_int (p q : Probe α) (a : α) : (p ⊓ q).int a ↔ p.int a ∧ q.int a := .rfl
@[simp] theorem inf_sat (p q : Probe α) (a : α) : (p ⊓ q).sat a ↔ p.sat a ∧ q.sat a := .rfl

theorem relativized_le_relativized {f g : α → Prop} [DecidablePred f] [DecidablePred g] :
    relativized f ≤ relativized g ↔ ∀ a, f a → g a :=
  and_self_iff

@[simp] theorem comap_id (p : Probe α) : p.comap id = p := ext (fun _ ↦ .rfl) fun _ ↦ .rfl

theorem comap_comap {β γ : Type*} (f : γ → β) (g : β → α) (p : Probe α) :
    (p.comap g).comap f = p.comap (g ∘ f) :=
  ext (fun _ ↦ .rfl) fun _ ↦ .rfl

/-- Reading goals through a map, as a lattice homomorphism of probes. -/
def comapLatticeHom {β : Type*} (f : β → α) : LatticeHom (Probe α) (Probe β) where
  toFun := comap f
  map_sup' _ _ := ext (fun _ ↦ .rfl) fun _ ↦ .rfl
  map_inf' _ _ := ext (fun _ ↦ .rfl) fun _ ↦ .rfl

@[simp] theorem comapLatticeHom_apply {β : Type*} (f : β → α) (p : Probe α) :
    comapLatticeHom f p = p.comap f :=
  rfl

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

/-- Search commutes with a map of goals that carries satisfaction to satisfaction. -/
theorem search_map {β : Type*} {q : Probe β} (g : α → β) (h : ∀ a ∈ goals, q.sat (g a) ↔ p.sat a) :
    q.search (goals.map g) = (p.search goals).map g := by
  induction goals with
  | nil => rfl
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    simp only [search] at hl ⊢
    by_cases hs : p.sat a <;> simp [hs, ha, hl]

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

end Probe

end Minimalist
