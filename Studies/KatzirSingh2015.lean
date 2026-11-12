module

public import Mathlib.Order.Minimal
public import Linglib.Semantics.Questions.HamblinSet
public import Linglib.Logic.Aristotelian.Square

/-!
# Katzir and Singh (2015): Economy of Structure and Information

Katzir and Singh derive the oddness of *Some Italians come from a warm country* and *John has
one wife* from the requirement that an assertion be a good answer to a good question. Which
questions are good, those the participants are commonly known to want settled, the theory takes as
given, so `Scenario.Felicitous` is relative to a family of them. A good answer is true, relevant,
and minimal among the true relevant alternatives in the product of complexity and strength,
`Scenario.cost`. An answer that means what a simpler one means
[is therefore never good](##KatzirSingh2015.Scenario.not_goodAnswer_of_meaning_eq), which
[is Hurford's constraint](##KatzirSingh2015.Scenario.not_felicitous_disj); *some*
[is needlessly weak](##KatzirSingh2015.not_goodAnswer_some) where *all* is true, in every context;
and the indefinite article [gives way to the definite](##KatzirSingh2015.not_goodAnswer_a). The ban
on trivial alternatives that the paper argues against does not read the question:
[it rejects *all*](##KatzirSingh2015.not_noTrivialAlternatives_scalar) under the explicit question
that makes it a good answer, and
[it accepts](##KatzirSingh2015.noTrivialAlternatives_typewriter) an assertion whose only defect is
its question.

## Implementation notes

A question is a Hamblin set and an answer is relevant when, within the context, it does not split
a cell of `Question.partition`. Strength is entailment of the meanings and does not read the
context, which enters through relevance alone. Complexity takes values in any preorder, so the
structural order on trees can be supplied; the examples use `ℕ`. The definite article carries its
presupposition in its truth conditions. The focus semantic value an assertion's question must lie
in is an argument of `Scenario.Felicitous`.

## TODO

* The embedded cases, where oddness persists in environments that satisfy both conditions, and
  the local condition the paper considers for them, are not represented.
* The judgments are not yet rows of `Data/Examples`.

## References

* [katzir-singh-2015]
* [magri-2009]
* [spector-2014]
* [heim-1991]
* [hurford-1974]
* [katzir-2007]
* [groenendijk-stokhof-1984]
* [rooth-1992]
-/

@[expose] public section

namespace KatzirSingh2015

open Set

variable {W U C X : Type*}

/-! ### Trivial alternatives -/

/-- An alternative `φ'` is trivial in the context `c` given `φ` when it is false throughout `c`,
true throughout `c`, or equivalent to `φ` in `c` ([spector-2014], the paper's (4)). -/
def IsTrivial (c φ φ' : Set W) : Prop :=
  Disjoint φ' c ∨ c ⊆ φ' ∨ φ ∩ c = φ' ∩ c

/-- Some alternative of `φ` is not trivial in the context ((5)). -/
def NoTrivialAlternatives (c : Set W) (alt : Set (Set W)) (φ : Set W) : Prop :=
  ∃ φ' ∈ alt, ¬ IsTrivial c φ φ'

/-! ### The answer condition -/

/-- The alternatives an assertion competes with, each with a meaning and a structural complexity,
and the context. -/
structure Scenario (W U C : Type*) where
  meaning : U → Set W
  complexity : U → C
  context : Set W

namespace Scenario

variable (s : Scenario W U C) (Q : Set (Set W)) {u v : U} {w : W}

/-- An assertion is relevant to a question when, within the context, it does not split a cell of
the partition the question induces. -/
def Relevant (u : U) : Prop :=
  ∀ v ∈ s.context, ∀ w ∈ s.context, Question.partition Q v w → (v ∈ s.meaning u ↔ w ∈ s.meaning u)

variable {s Q} in
theorem relevant_of_mem (h : s.meaning u ∈ Q) : s.Relevant Q u :=
  fun _ _ _ _ hvw ↦ Question.partition_iff.1 hvw _ h

variable {s} in
theorem relevant_range_singleton : s.Relevant (range ({·} : W → Set W)) u := fun v _ w _ h ↦ by
  obtain rfl : w = v := (Question.partition_iff.1 h {v} ⟨v, rfl⟩).1 rfl
  exact Iff.rfl

variable {s Q} in
theorem relevant_congr (h : s.meaning u = s.meaning v) : s.Relevant Q u ↔ s.Relevant Q v := by
  simp only [Relevant, h]

variable [Preorder C]

/-- The two dimensions along which answers are compared. In the product order one alternative is
at least as good as another when it is at most as complex and at least as strong (16a), and
better when the comparison is strict (16b). -/
def cost (u : U) : C × Set W := (s.complexity u, s.meaning u)

theorem cost_le_cost_iff :
    s.cost v ≤ s.cost u ↔ s.complexity v ≤ s.complexity u ∧ s.meaning v ⊆ s.meaning u :=
  Iff.rfl

theorem cost_lt_cost_of_ssubset (hc : s.complexity v ≤ s.complexity u)
    (hs : s.meaning v ⊂ s.meaning u) : s.cost v < s.cost u :=
  Prod.mk_lt_mk.2 (.inr ⟨hc, hs⟩)

theorem cost_lt_cost_of_lt (hc : s.complexity v < s.complexity u)
    (hs : s.meaning v ⊆ s.meaning u) : s.cost v < s.cost u :=
  Prod.mk_lt_mk.2 (.inl ⟨hc, hs⟩)

/-- A good answer at `w` is true, relevant, and not needlessly worse than a true relevant
alternative (15). -/
def GoodAnswer (u : U) (w : W) : Prop :=
  MinimalFor (fun v ↦ w ∈ s.meaning v ∧ s.Relevant Q v) s.cost u

/-- An assertion is felicitous at `w` when it is a good answer to a good question it is congruent
to, one included in its focus semantic value (8). -/
def Felicitous (good : Set (Set (Set W))) (focus : U → Set (Set W)) (u : U) (w : W) : Prop :=
  ∃ Q ∈ good, Q ⊆ focus u ∧ s.GoodAnswer Q u w

variable {s Q}

theorem goodAnswer_iff : s.GoodAnswer Q u w ↔ w ∈ s.meaning u ∧ s.Relevant Q u ∧
    ∀ ⦃v⦄, s.cost v < s.cost u → ¬ (w ∈ s.meaning v ∧ s.Relevant Q v) := by
  rw [GoodAnswer, minimalFor_iff_forall_lt, and_assoc]

theorem GoodAnswer.mem (h : s.GoodAnswer Q u w) : w ∈ s.meaning u := h.1.1

theorem GoodAnswer.relevant (h : s.GoodAnswer Q u w) : s.Relevant Q u := h.1.2

-- (17), (18), (21)
theorem not_goodAnswer_of_stronger (hc : s.complexity v ≤ s.complexity u)
    (hs : s.meaning v ⊂ s.meaning u) (hw : w ∈ s.meaning v) (hr : s.Relevant Q v) :
    ¬ s.GoodAnswer Q u w :=
  fun h ↦ h.not_lt ⟨hw, hr⟩ (s.cost_lt_cost_of_ssubset hc hs)

theorem not_goodAnswer_of_simpler (hc : s.complexity v < s.complexity u)
    (hs : s.meaning v ⊆ s.meaning u) (hw : w ∈ s.meaning v) (hr : s.Relevant Q v) :
    ¬ s.GoodAnswer Q u w :=
  fun h ↦ h.not_lt ⟨hw, hr⟩ (s.cost_lt_cost_of_lt hc hs)

theorem not_goodAnswer_of_meaning_eq (hc : s.complexity v < s.complexity u)
    (h : s.meaning v = s.meaning u) : ¬ s.GoodAnswer Q u w :=
  fun hu ↦ not_goodAnswer_of_simpler hc h.le (h.ge hu.mem) ((relevant_congr h).2 hu.relevant) hu

-- (22)
theorem not_goodAnswer_disj {d φ ψ : U} (hd : s.meaning d = s.meaning φ ∪ s.meaning ψ)
    (hψ : s.meaning ψ ⊆ s.meaning φ) (hc : s.complexity φ < s.complexity d) :
    ¬ s.GoodAnswer Q d w :=
  not_goodAnswer_of_meaning_eq hc (hd.trans (union_eq_left.2 hψ)).symm

-- (23)
theorem not_goodAnswer_conj {k φ ψ : U} (hk : s.meaning k = s.meaning φ ∩ s.meaning ψ)
    (hψ : s.meaning φ ⊆ s.meaning ψ) (hc : s.complexity φ < s.complexity k) :
    ¬ s.GoodAnswer Q k w :=
  not_goodAnswer_of_meaning_eq hc (hk.trans (inter_eq_left.2 hψ)).symm

variable {good good' : Set (Set (Set W))} {focus : U → Set (Set W)}

theorem Felicitous.mono (h : s.Felicitous good focus u w) (hg : good ⊆ good') :
    s.Felicitous good' focus u w :=
  let ⟨Q, hQ, hf, ha⟩ := h
  ⟨Q, hg hQ, hf, ha⟩

/-- A disjunction more complex than a disjunct that the other disjunct entails is infelicitous at
every world, whichever questions are good (22). -/
theorem not_felicitous_disj {d φ ψ : U} (hd : s.meaning d = s.meaning φ ∪ s.meaning ψ)
    (hψ : s.meaning ψ ⊆ s.meaning φ) (hc : s.complexity φ < s.complexity d) :
    ¬ s.Felicitous good focus d w :=
  fun ⟨_, _, _, ha⟩ ↦ not_goodAnswer_disj hd hψ hc ha

-- (23)
theorem not_felicitous_conj {k φ ψ : U} (hk : s.meaning k = s.meaning φ ∩ s.meaning ψ)
    (hψ : s.meaning φ ⊆ s.meaning ψ) (hc : s.complexity φ < s.complexity k) :
    ¬ s.Felicitous good focus k w :=
  fun ⟨_, _, _, ha⟩ ↦ not_goodAnswer_conj hk hψ hc ha

end Scenario

/-! ### Some and all

The *some* and *all* alternatives over the three ways a set of grades, names or origins can fall,
the vertices of the triangle of opposition: to none (`E`), to some but not all (`IO`), or to all
(`A`). -/

open Aristotelian

/-- The scalar alternatives. -/
inductive Scalar
  | some_ | all_

/-- *Some* and *all* denote the `I` and `A` corners of the square. -/
def Scalar.meaning : Scalar → Set Triangle
  | .some_ => Triangle.corners.I
  | .all_ => Triangle.corners.A

/-- The alternatives *some* and *all*, of the same complexity, in the context `c`. -/
abbrev scalar (c : Set Triangle) : Scenario Triangle Scalar ℕ := ⟨Scalar.meaning, fun _ ↦ 1, c⟩

theorem Scalar.meaning_all_ssubset_some : Scalar.meaning .all_ ⊂ Scalar.meaning .some_ :=
  Finset.coe_ssubset.2 (by decide)

theorem Scalar.mem_meaning_all : Triangle.A ∈ Scalar.meaning .all_ := Finset.mem_coe.2 (by decide)

-- (1), (19)
theorem Scalar.meaning_inter_ne_IO (u : Scalar) : u.meaning ∩ {w | w ≠ .IO} = {.A} := by
  ext w
  cases u <;> cases w <;> simp [Scalar.meaning, Triangle.corners]

variable {c : Set Triangle} {Q : Set (Set Triangle)}

-- (17b), (20b)
theorem goodAnswer_all (hr : (scalar c).Relevant Q .all_) : (scalar c).GoodAnswer Q .all_ .A :=
  ⟨⟨Scalar.mem_meaning_all, hr⟩, fun v _ _ ↦ (scalar c).cost_le_cost_iff.2 ⟨le_rfl, by
    cases v
    exacts [Scalar.meaning_all_ssubset_some.subset, subset_rfl]⟩⟩

/-- Where *all* is true, *some* is a needlessly weak answer to any question *all* is relevant
to, whatever the context ((17a), (19a), (20a)). -/
theorem not_goodAnswer_some (hr : (scalar c).Relevant Q .all_) :
    ¬ (scalar c).GoodAnswer Q .some_ .A :=
  Scenario.not_goodAnswer_of_stronger (v := .all_) le_rfl Scalar.meaning_all_ssubset_some
    Scalar.mem_meaning_all hr

/-- In the context of (19) every alternative of *some* and of *all* is trivial, whatever the
question, the explicit one of (20) included, under which *all* is a good answer
(`goodAnswer_all` with `Scenario.relevant_range_singleton`). -/
theorem not_noTrivialAlternatives_scalar (u : Scalar) :
    ¬ NoTrivialAlternatives {w | w ≠ .IO} (range Scalar.meaning) u.meaning := by
  rintro ⟨_, ⟨v, rfl⟩, h⟩
  exact h (.inr (.inr ((u.meaning_inter_ne_IO).trans (v.meaning_inter_ne_IO).symm)))

/-! ### Maximize Presupposition -/

/-- How many suns there are and whether one shines. -/
inductive Sky
  | oneShining | oneDark | many

/-- *A sun is shining* and *the sun is shining*. -/
inductive Article
  | a | the

/-- The definite carries the uniqueness presupposition into its truth conditions. -/
def Article.meaning : Article → Set Sky
  | .a => {.oneDark}ᶜ
  | .the => {.oneShining}

/-- The alternatives of (21) in the context `c`. -/
abbrev sun (c : Set Sky) : Scenario Sky Article ℕ := ⟨Article.meaning, fun _ ↦ 1, c⟩

/-- Whether the sun is shining. -/
abbrev shining : Set (Set Sky) := {{.oneShining}, {.oneShining}ᶜ}

theorem Article.meaning_the_ssubset_a : Article.meaning .the ⊂ Article.meaning .a :=
  ⟨by simp [Article.meaning], fun h ↦ by simpa [Article.meaning] using @h .many⟩

theorem Article.meaning_inter_ne_many (u : Article) : u.meaning ∩ {.many}ᶜ = {.oneShining} := by
  ext w
  cases u <;> cases w <;> simp [Article.meaning]

theorem relevant_a : (sun {.many}ᶜ).Relevant shining .a := fun v hv w hw h ↦ by
  have h' := Question.partition_iff.1 h {.oneShining} (mem_insert _ _)
  cases v <;> cases w <;> simp_all [Article.meaning]

theorem not_relevant_a : ¬ (sun univ).Relevant shining .a := fun h ↦ by
  have := h .oneDark trivial .many trivial
    (Question.partition_iff.2 (by rintro p (rfl | rfl) <;> simp))
  simp [Article.meaning] at this

/-- The indefinite is a needlessly weak answer where the definite is true (21a). -/
theorem not_goodAnswer_a {c : Set Sky} : ¬ (sun c).GoodAnswer shining .a .oneShining :=
  Scenario.not_goodAnswer_of_stronger (v := .the) le_rfl Article.meaning_the_ssubset_a
    (mem_singleton _)
    (Scenario.relevant_of_mem (mem_insert _ _))

-- (21b)
theorem goodAnswer_the {c : Set Sky} : (sun c).GoodAnswer shining .the .oneShining :=
  ⟨⟨mem_singleton _, Scenario.relevant_of_mem (mem_insert _ _)⟩, fun v _ _ ↦
    (sun c).cost_le_cost_iff.2 ⟨le_rfl, by
      cases v
      exacts [Article.meaning_the_ssubset_a.subset, subset_rfl]⟩⟩

/-! ### An assertion out of the blue -/

/-- The alternatives *x broke the typewriter* of (13), over who broke it if anyone did, nothing
being known. -/
abbrev typewriter (X : Type*) : Scenario (Option X) X ℕ := ⟨fun x ↦ {some x}, fun _ ↦ 1, univ⟩

/-- The assertion (13a) has an alternative that is not trivial, and it is a good answer to who
broke the typewriter (`goodAnswer_typewriter`), so its oddness out of the blue rests on that
question's not being a good one. -/
theorem noTrivialAlternatives_typewriter [Nontrivial X] (x : X) :
    NoTrivialAlternatives univ (range (typewriter X).meaning) ((typewriter X).meaning x) := by
  obtain ⟨y, hy⟩ := exists_ne x
  refine ⟨_, ⟨y, rfl⟩, ?_⟩
  rintro (h | h | h)
  · exact h.ne_of_mem rfl trivial rfl
  · exact Option.some_ne_none y (h (mem_univ none)).symm
  · rw [inter_univ, inter_univ, singleton_eq_singleton_iff] at h
    exact hy (Option.some_injective _ h).symm

-- (13a)
theorem goodAnswer_typewriter (x : X) :
    (typewriter X).GoodAnswer (range (typewriter X).meaning) x (some x) :=
  ⟨⟨rfl, Scenario.relevant_of_mem ⟨x, rfl⟩⟩, fun y hy _ ↦ by
    obtain rfl : x = y := Option.some_injective _ hy.1
    exact le_rfl⟩

end KatzirSingh2015
