module

public import Mathlib.Order.Minimal
public import Linglib.Semantics.Questions.Entailment
public import Studies.Spector2014

/-!
# Katzir and Singh (2015): Economy of Structure and Information

Katzir and Singh derive the oddness of *Some Italians come from a warm country* and *John has
one wife* from the requirement that an assertion be a good answer to a good question. Which
questions are good, those the participants are commonly known to want settled, the theory takes as
given, so `Felicitous` is relative to a family of them. A `GoodAnswer` is true, relevant, and
minimal among the true relevant alternatives in the product of complexity and strength. An answer
that means what a simpler one means
[is therefore never good](##KatzirSingh2015.not_goodAnswer_of_meaning_eq), which
[is Hurford's constraint](##KatzirSingh2015.not_felicitous_disj); *some*
[is needlessly weak](##KatzirSingh2015.not_goodAnswer_some) where *all* is true, whatever is
known; and the indefinite article [gives way to the definite](##KatzirSingh2015.not_goodAnswer_a).
The ban on trivial alternatives does not read the question:
[it rejects *all*](##KatzirSingh2015.not_noTrivialAlternatives_scalar) under the explicit question
that makes it a good answer, and
[it accepts](##KatzirSingh2015.noTrivialAlternatives_typewriter) an assertion whose only defect is
its question.

## Implementation notes

An assertion is relevant to a question when the question decides it, `Question.decided`, and
relevant in a context `c` when `Question.ofSet c ⊓ Q` does. Strength is entailment of the meanings
and does not read the context. Complexity takes values in any preorder, so the structural order on
trees can be supplied. The definite article carries its presupposition in its truth conditions.
The focus semantic value an assertion's question must lie in is an argument of `Felicitous`.

## TODO

* The embedded cases, where oddness persists in environments that satisfy both conditions, are
  not represented.
* A disjunction *φ or (not φ and ψ)* means what the simpler *φ or ψ* means, so it is
  [never a good answer](##KatzirSingh2015.not_goodAnswer_disj_compl_inter); [katzir-singh-2014]
  reports such sentences as appropriate and compares complexity locally instead, which is not
  formalized.
* The judgments are not yet rows of `Data/Examples`.

## References

* [katzir-singh-2015]
* [magri-2009]
* [spector-2014]
* [heim-1991]
* [hurford-1974]
* [katzir-2007]
* [katzir-singh-2014]
* [groenendijk-stokhof-1984]
* [rooth-1992]
-/

@[expose] public section

namespace KatzirSingh2015

open Set Question Aristotelian
open Spector2014 (NoTrivialAlternatives)

variable {W U C X : Type*} [Preorder C]

/-! ### The answer condition -/

section GoodAnswer

variable (meaning : U → Set W) (complexity : U → C) (Q : Question W) {u v : U} {w : W}

/-- A good answer at `w` is true, relevant, and not needlessly worse than a true relevant
alternative (15). In the product order one alternative is at least as good as another when it is
at most as complex and at least as strong (16a), and better when the comparison is strict
(16b). -/
def GoodAnswer (u : U) (w : W) : Prop :=
  MinimalFor (fun v ↦ w ∈ meaning v ∧ meaning v ∈ Q.decided) (fun v ↦ (complexity v, meaning v)) u

/-- An assertion is felicitous at `w` in the context `c` when it is a good answer to a good
question it is congruent to, one whose alternatives lie in its focus semantic value (8). -/
def Felicitous (c : Set W) (good : Set (Question W)) (focus : U → Set (Set W)) (u : U) (w : W) :
    Prop :=
  ∃ Q ∈ good, alt Q ⊆ focus u ∧ GoodAnswer meaning complexity (ofSet c ⊓ Q) u w

variable {meaning complexity Q}

theorem goodAnswer_iff : GoodAnswer meaning complexity Q u w ↔
    w ∈ meaning u ∧ meaning u ∈ Q.decided ∧ ∀ ⦃v⦄, (complexity v, meaning v) <
      (complexity u, meaning u) → ¬ (w ∈ meaning v ∧ meaning v ∈ Q.decided) := by
  rw [GoodAnswer, minimalFor_iff_forall_lt, and_assoc]

theorem GoodAnswer.mem (h : GoodAnswer meaning complexity Q u w) : w ∈ meaning u := h.1.1

theorem GoodAnswer.mem_decided (h : GoodAnswer meaning complexity Q u w) :
    meaning u ∈ Q.decided :=
  h.1.2

-- (17), (18), (21)
theorem not_goodAnswer_of_stronger (hc : complexity v ≤ complexity u)
    (hs : meaning v ⊂ meaning u) (hw : w ∈ meaning v) (hr : meaning v ∈ Q.decided) :
    ¬ GoodAnswer meaning complexity Q u w :=
  fun h ↦ h.not_lt ⟨hw, hr⟩ (Prod.mk_lt_mk.2 (.inr ⟨hc, hs⟩))

theorem not_goodAnswer_of_simpler (hc : complexity v < complexity u)
    (hs : meaning v ⊆ meaning u) (hw : w ∈ meaning v) (hr : meaning v ∈ Q.decided) :
    ¬ GoodAnswer meaning complexity Q u w :=
  fun h ↦ h.not_lt ⟨hw, hr⟩ (Prod.mk_lt_mk.2 (.inl ⟨hc, hs⟩))

theorem not_goodAnswer_of_meaning_eq (hc : complexity v < complexity u)
    (h : meaning v = meaning u) : ¬ GoodAnswer meaning complexity Q u w :=
  fun hu ↦ not_goodAnswer_of_simpler hc h.le (h.ge hu.mem) (h ▸ hu.mem_decided) hu

-- (22)
theorem not_goodAnswer_disj {d φ ψ : U} (hd : meaning d = meaning φ ∪ meaning ψ)
    (hψ : meaning ψ ⊆ meaning φ) (hc : complexity φ < complexity d) :
    ¬ GoodAnswer meaning complexity Q d w :=
  not_goodAnswer_of_meaning_eq hc (hd.trans (union_eq_left.2 hψ)).symm

-- (23)
theorem not_goodAnswer_conj {k φ ψ : U} (hk : meaning k = meaning φ ∩ meaning ψ)
    (hψ : meaning φ ⊆ meaning ψ) (hc : complexity φ < complexity k) :
    ¬ GoodAnswer meaning complexity Q k w :=
  not_goodAnswer_of_meaning_eq hc (hk.trans (inter_eq_left.2 hψ)).symm

-- the disjunctions of [katzir-singh-2014] (25), which mean what a plain disjunction means
theorem not_goodAnswer_disj_compl_inter {d e φ ψ : U}
    (hd : meaning d = meaning φ ∪ (meaning φ)ᶜ ∩ meaning ψ)
    (he : meaning e = meaning φ ∪ meaning ψ) (hc : complexity e < complexity d) :
    ¬ GoodAnswer meaning complexity Q d w :=
  not_goodAnswer_of_meaning_eq hc (by rw [hd, he, union_inter_distrib_left, union_compl_self,
    univ_inter])

variable {c : Set W} {good good' : Set (Question W)} {focus : U → Set (Set W)}

theorem Felicitous.mono (h : Felicitous meaning complexity c good focus u w)
    (hg : good ⊆ good') : Felicitous meaning complexity c good' focus u w :=
  let ⟨Q, hQ, hf, ha⟩ := h
  ⟨Q, hg hQ, hf, ha⟩

/-- A disjunction more complex than a disjunct that the other disjunct entails is infelicitous at
every world, whatever is known and whichever questions are good (22). -/
theorem not_felicitous_disj {d φ ψ : U} (hd : meaning d = meaning φ ∪ meaning ψ)
    (hψ : meaning ψ ⊆ meaning φ) (hc : complexity φ < complexity d) :
    ¬ Felicitous meaning complexity c good focus d w :=
  fun ⟨_, _, _, ha⟩ ↦ not_goodAnswer_disj hd hψ hc ha

-- (23)
theorem not_felicitous_conj {k φ ψ : U} (hk : meaning k = meaning φ ∩ meaning ψ)
    (hψ : meaning φ ⊆ meaning ψ) (hc : complexity φ < complexity k) :
    ¬ Felicitous meaning complexity c good focus k w :=
  fun ⟨_, _, _, ha⟩ ↦ not_goodAnswer_conj hk hψ hc ha

end GoodAnswer

-- the question that asks which world is actual decides every proposition
theorem mem_decided_iInf_polar_singleton (p : Set W) :
    p ∈ (⨅ w : W, polar {w}).decided := mem_decided.2 fun σ hσ ↦ mem_polar.2 <| by
  by_contra! h
  obtain ⟨x, hx, hxp⟩ := not_subset.1 h.1
  obtain ⟨y, hy, hyp⟩ := not_subset.1 h.2
  rcases mem_polar.1 (le_def.1 (iInf_le (fun w : W ↦ polar {w}) x) hσ) with hs | hs
  · exact hyp (by rwa [mem_singleton_iff.1 (hs hy)])
  · exact hs hx rfl

/-! ### Some and all

The *some* and *all* alternatives over the three ways a set of grades, names or origins can fall,
the vertices of the triangle of opposition: to none (`E`), to some but not all (`IO`), or to all
(`A`). -/

/-- The scalar alternatives. -/
inductive Scalar
  | some_ | all_

/-- *Some* and *all* denote the `I` and `A` corners of the square. -/
def Scalar.meaning : Scalar → Set Triangle
  | .some_ => Triangle.corners.I
  | .all_ => Triangle.corners.A

theorem Scalar.meaning_all_ssubset_some : Scalar.meaning .all_ ⊂ Scalar.meaning .some_ :=
  Finset.coe_ssubset.2 (by decide)

theorem Scalar.mem_meaning_all : Triangle.A ∈ Scalar.meaning .all_ := Finset.mem_coe.2 (by decide)

section Scalar

variable {complexity : Scalar → C} {Q : Question Triangle}

-- (17b), (20b)
theorem goodAnswer_all (hc : complexity .all_ ≤ complexity .some_)
    (hr : Scalar.meaning .all_ ∈ Q.decided) : GoodAnswer Scalar.meaning complexity Q .all_ .A :=
  ⟨⟨Scalar.mem_meaning_all, hr⟩, fun v _ _ ↦ by
    cases v
    exacts [⟨hc, Scalar.meaning_all_ssubset_some.subset⟩, le_rfl]⟩

/-- Where *all* is true and no more complex, *some* is a needlessly weak answer to any question
that decides *all*, whatever is known ((17a), (19a), (20a)). -/
theorem not_goodAnswer_some (hc : complexity .all_ ≤ complexity .some_)
    (hr : Scalar.meaning .all_ ∈ Q.decided) : ¬ GoodAnswer Scalar.meaning complexity Q .some_ .A :=
  not_goodAnswer_of_stronger hc Scalar.meaning_all_ssubset_some Scalar.mem_meaning_all hr

end Scalar

/-- In the context of (19) every alternative of *some* and of *all* is trivial, whatever the
question, the explicit one of (20) included, under which *all* is a good answer (`goodAnswer_all`
with `mem_decided_iInf_polar_singleton`). -/
theorem not_noTrivialAlternatives_scalar (u : Scalar) :
    ¬ NoTrivialAlternatives {w | w ≠ .IO} (range Scalar.meaning) u.meaning :=
  have h : ∀ v : Scalar, v.meaning ∩ {w | w ≠ Triangle.IO} = {Triangle.A} := by
    rintro (_ | _)
    exacts [Spector2014.corners_I_inter_ne_IO, Spector2014.corners_A_inter_ne_IO]
  Spector2014.not_noTrivialAlternatives_of_inter_eq <| by
    rintro _ ⟨v, rfl⟩
    rw [h u, h v]

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

/-- Whether the sun is shining. -/
abbrev shining : Question Sky := polar {.oneShining}

theorem Article.meaning_the_ssubset_a : Article.meaning .the ⊂ Article.meaning .a :=
  ⟨by simp [Article.meaning], fun h ↦ by simpa [Article.meaning] using @h .many⟩

-- (21)
theorem Article.meaning_inter_ne_many (u : Article) : u.meaning ∩ {.many}ᶜ = {.oneShining} := by
  ext w
  cases u <;> cases w <;> simp [Article.meaning]

-- (21a)
theorem mem_decided_a : Article.meaning .a ∈ (ofSet {.many}ᶜ ⊓ shining).decided :=
  mem_decided.2 fun σ ⟨hc, hσ⟩ ↦ mem_polar.2 <| (mem_polar.1 hσ).imp
    (fun h ↦ h.trans Article.meaning_the_ssubset_a.subset) fun h x hx ↦ by
      have h₁ := mem_ofSet.1 hc hx
      have h₂ := h hx
      cases x <;> simp_all [Article.meaning]

-- (21a)
theorem not_mem_decided_a : Article.meaning .a ∉ shining.decided := fun h ↦ by
  have hσ : ({.oneDark, .many} : Set Sky) ∈ shining := mem_polar.2 (.inr (by simp [subset_def]))
  rcases mem_polar.1 (le_def.1 (mem_decided.1 h) hσ) with h | h
  · simpa [Article.meaning] using h (mem_insert _ _)
  · simpa [Article.meaning] using h (mem_insert_of_mem _ rfl)

section Article

variable {complexity : Article → C} {c : Set Sky}

/-- The indefinite is a needlessly weak answer where the definite is true and no more complex
(21a). -/
theorem not_goodAnswer_a (hc : complexity .the ≤ complexity .a) :
    ¬ GoodAnswer Article.meaning complexity (ofSet c ⊓ shining) .a .oneShining :=
  not_goodAnswer_of_stronger hc Article.meaning_the_ssubset_a (mem_singleton _)
    (mem_decided.2 inf_le_right)

-- (21b)
theorem goodAnswer_the (hc : complexity .the ≤ complexity .a) :
    GoodAnswer Article.meaning complexity (ofSet c ⊓ shining) .the .oneShining :=
  ⟨⟨mem_singleton _, mem_decided.2 inf_le_right⟩, fun v _ _ ↦ by
    cases v
    exacts [⟨hc, Article.meaning_the_ssubset_a.subset⟩, le_rfl]⟩

end Article

/-! ### An assertion out of the blue -/

/-- The alternatives *x broke the typewriter* of (13), over who broke it if anyone did. -/
abbrev typewriter (x : X) : Set (Option X) := {some x}

/-- The assertion (13a) has an alternative that is not trivial where nothing is known, and it is a
good answer to who broke the typewriter (`goodAnswer_typewriter`), so its oddness out of the blue
rests on that question's not being a good one. -/
theorem noTrivialAlternatives_typewriter [Nontrivial X] (x : X) :
    NoTrivialAlternatives univ (range (typewriter (X := X))) (typewriter x) := by
  obtain ⟨y, hy⟩ := exists_ne x
  exact Spector2014.noTrivialAlternatives_univ_iff.2 ⟨_, ⟨y, rfl⟩, singleton_ne_empty _,
    fun h ↦ Option.some_ne_none y (h.ge (mem_univ none)).symm,
    fun h ↦ hy (Option.some_injective _ (singleton_eq_singleton_iff.1 h)).symm⟩

-- (13a)
theorem goodAnswer_typewriter (complexity : X → C) (x : X) :
    GoodAnswer typewriter complexity (⨅ y : X, polar (typewriter y)) x (some x) :=
  ⟨⟨rfl, mem_decided.2 (iInf_le _ x)⟩, fun y hy _ ↦ by
    obtain rfl : x = y := Option.some_injective _ hy.1
    exact le_rfl⟩

end KatzirSingh2015
