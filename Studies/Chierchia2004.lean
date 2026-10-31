module

public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Exhaustification.Excluder
public import Studies.KadmonLandman1993
public import Linglib.Data.Examples.Chierchia2004

/-!
# Chierchia (2004): Scalar implicatures, polarity phenomena, and the syntax/pragmatics interface

This file models scalar implicatures computed in parallel with plain meanings. A node's meaning
(`Meaning`) is a meaning of alternative semantics, a plain value with its scalar alternatives,
together with a strong value. An application's alternatives are the function's alternatives
applied to the argument when the function is a scalar term, and otherwise the function applied to
the argument's alternatives, which is Hamblin application
[whenever one daughter is not scalar](##appAlternatives_eq_seq). At a scope site
Krifka's rule conjoins the strong value with the exclusion of the alternatives that asymmetrically
entail the plain value, which on a scale is
[exhaustification](##Chierchia2004.Meaning.lexical_strengthen_strong_eq_exh). Strong Application
passes strong values through a function that is not downward entailing and recalibrates through
one that is: the argument's implicatures are removed and the images of its alternatives compete
again, so that [doubting a conjunction implicates the disjunction](##doubt_conj_strong).

Computed this way, *Mary is either working at her paper or seeing some of her students* denies
*all* inside its second disjunct, where
[a computation at the root alone denies the first](##working_or_seeingSome). The Strength
Condition bars a strong value strictly weaker than the plain one:
[passing an implicature through a strictly antitone function violates
it](##Chierchia2004.Meaning.not_strengthCondition_applyRegular), while a non-monotone quantifier
keeps a strong value [independent of the plain one](##exactlyTwoSmokeOrDrink_independent). Since a
context [may truncate a scale](##isScaleSelection_truncated), *I don't have many matches left*
implicates that I have some [on the scale *some, many, all*](##notMany_strong) but
[not on *many, all*](##notMany_truncated_strong).

*Any* is an indefinite whose domain is [universally closed](##universalClosure) over expansions
of a contextual domain. The closure is defined when it entails the competitor with the plain
indefinite, as it does [in every downward-entailing context](##universalClosure_subset_of_antitone)
but not [in a positive one under a proper widening](##not_universalClosure_id_subset); over a single
expansion this is [Kadmon and Landman's condition](##universalClosure_singleton_subset_iff) that
widening strengthen. The revised condition compares the closure with the competitor's strong value
instead. Under *doubt*, a conjunction gives that competitor an indirect implicature, so
[*any* meets the first condition and fails the second](##doubtAnd_any), while under *doubt … or*
[it meets both](##doubtOr_any), [as the paper's judgments of the two sentences
require](##rows_any).

## Implementation notes

* Numbered items follow the circulated manuscript (Bicocca, May 2001, revised May 2002); the
  published chapter may renumber.
* The paper's scalar assertion picks the weakest alternative that asymmetrically entails the
  plain value, and the contradiction when there is none; it is undefined only when those
  alternatives have no weakest member. `Meaning.strengthen` negates every such alternative, a
  total operation that
  [agrees with negating that member](##Chierchia2004.Meaning.strengthen_strong_eq_of_isGreatest)
  wherever it exists.
* The appendix assigns a node the set of its admissible strong values, Krifka's rule being
  optional; `Meaning.strong` is the strongest of them, the value the paper's computations follow.
* The Strength Condition is stated in the text, not in the appendix's Strong Application. Nodes
  built from monotone and downward-entailing functions have strong values that
  [entail](##Chierchia2004.Meaning.applyRegular_strong_subset) their plain values
  ([recalibration](##Chierchia2004.Meaning.recalibrate_strong_subset) included), which the
  condition does not require.
* A function is a scalar term when its alternatives are more than its own value
  (`WithAlternatives.Given`). Downward entailing is `Antitone`, so a constant function counts as
  downward entailing.
* *Doubt* is complementation, the paper's *not believe* with belief taken as the identity.
* The computation at the root alone is that of the global view the paper argues against: the
  alternatives of *some* projected to the root through a disjunction whose own scale is ignored.
* An open sentence with a trace is a set of pairs of a value for the trace and a world. The
  quantifier *exactly two* and the indefinite *some coffee* are not given their own scales.
* The closure ranges over the expanded domains rather than over the expansion functions. The
  examples take the single widening to every coffee.

## Errata

* The text allows the contextual domain itself as an expansion of the domain of *any* and says
  that the semantics still confines *any* to downward-entailing contexts in that case. Once the
  contextual domain is among the expansions, the closure entails the competitor in every context
  ([`universalClosure_subset`](##universalClosure_subset)), positive ones included, so the
  strengthening condition does not confine it.
* The argument against global computation says that the implicature entails (21c), meaning
  (22c); the discussion of scale selection calls the minimal scales those in (78), meaning (97);
  and the competitor (130b) has *any cake* for *the cake*.

## TODO

* The double-negation contrast between strong values, because-clauses as covert conjunctions,
  the positive implicature of *few*, intervention by numerals through scale truncation, and the
  appendix's *nobody that smokes and drinks* example.

## References

* [chierchia-2004]
* [krifka-1995a]
* [kadmon-landman-1993]
* [rooth-1992]
-/

@[expose] public section

namespace Chierchia2004

open Set
open Exhaustification (excludes exh mem_excludes mem_exh)
open KadmonLandman1993 (Strengthening de_satisfies_strengthening)

universe u

variable {α β : Type*} {W W' : Type*}

private theorem pair_inter_Iio [Preorder α] {a b : α} (h : b < a) :
    ({a, b} : Set α) ∩ Iio a = {b} := by
  ext c
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_Iio]
  constructor
  · rintro ⟨rfl | rfl, hc⟩
    exacts [(lt_irrefl c hc).elim, rfl]
  · rintro rfl
    exact ⟨Or.inr rfl, h⟩

/-! ### Alternatives of an application -/

open Classical in
/-- The alternatives of an application: the function applied to the argument's alternatives when
the function's alternatives are only its value, and otherwise the function's alternatives applied
to the argument. -/
noncomputable def appAlternatives (F : WithAlternatives (α → β)) (x : WithAlternatives α) :
    Set β :=
  if F.Given F.ordinary then F.ordinary '' x.alternatives else (· x.ordinary) '' F.alternatives

section AppAlternatives

variable {F : WithAlternatives (α → β)} {x : WithAlternatives α}

theorem appAlternatives_of_given (h : F.Given F.ordinary) :
    appAlternatives F x = F.ordinary '' x.alternatives :=
  ite_eq_left h

theorem appAlternatives_of_not_given (h : ¬F.Given F.ordinary) :
    appAlternatives F x = (· x.ordinary) '' F.alternatives :=
  ite_eq_right h

theorem appAlternatives_eq_seq {α β : Type u} {F : WithAlternatives (α → β)}
    {x : WithAlternatives α} (h : F.Given F.ordinary ∨ x.Given x.ordinary) :
    appAlternatives F x = (F <*> x).alternatives := by
  by_cases hF : F.Given F.ordinary
  · rw [appAlternatives_of_given hF, hF.alternatives_seq]
  · rw [appAlternatives_of_not_given hF, WithAlternatives.alternatives_seq,
      h.resolve_left hF, seq_singleton]

end AppAlternatives

/-! ### Plain and strong values -/

/-- The values the parallel recursion assigns to a node: its plain value and scalar alternatives,
a meaning of alternative semantics, together with its strong value. -/
structure Meaning (α : Type*) extends WithAlternatives α where
  /-- The strong value `‖α‖^S`. -/
  strong : α

namespace Meaning

/-- A lexical item, whose alternatives are its scale and whose strong value is its plain
value. -/
def lexical (x : α) (ALT : Set α) : Meaning α :=
  ⟨⟨x, ALT⟩, x⟩

/-- The Strength Condition: the strong value is not strictly weaker than the plain value. -/
def StrengthCondition (m : Meaning (Set W)) : Prop :=
  ¬m.ordinary ⊂ m.strong

/-- Krifka's rule: at a scope site, conjoin the strong value with the exclusion of the alternatives
that asymmetrically entail the plain value. -/
def strengthen (m : Meaning (Set W)) : Meaning (Set W) :=
  { m with strong := m.strong ∩ excludes (m.alternatives ∩ Iio m.ordinary) m.ordinary }

/-- Strong Application to a function that is not downward entailing: the function's strong value
applies to the argument's strong value. -/
noncomputable def applyRegular (F : Meaning (α → β)) (x : Meaning α) : Meaning β :=
  ⟨⟨F.ordinary x.ordinary, appAlternatives F.toWithAlternatives x.toWithAlternatives⟩,
    F.strong x.strong⟩

/-- Strong Application to a downward-entailing function: the function's strong value applies to
the argument's plain value, conjoined with the exclusion of the images of the argument's
alternatives that asymmetrically entail the plain result. -/
noncomputable def recalibrate (F : Meaning (Set W → Set W')) (x : Meaning (Set W)) :
    Meaning (Set W') :=
  ⟨⟨F.ordinary x.ordinary, appAlternatives F.toWithAlternatives x.toWithAlternatives⟩,
    F.strong x.ordinary ∩
      excludes (F.ordinary '' x.alternatives ∩ Iio (F.ordinary x.ordinary)) (F.ordinary x.ordinary)⟩

open Classical in
/-- Strong Application: regular application through a function that is not downward entailing,
recalibration through one that is. -/
noncomputable def strongApply (F : Meaning (Set W → Set W')) (x : Meaning (Set W)) :
    Meaning (Set W') :=
  if Antitone F.ordinary then F.recalibrate x else F.applyRegular x

/-! ### Krifka's rule -/

variable {m : Meaning (Set W)} {w : W}

@[simp]
theorem mem_strengthen_strong :
    w ∈ m.strengthen.strong ↔ w ∈ m.strong ∧ ∀ a ∈ m.alternatives, a ⊂ m.ordinary → w ∉ a := by
  simp only [strengthen, mem_inter_iff, mem_excludes, mem_Iio, and_imp]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ forall_congr' fun ha ↦
    ⟨fun h hw ↦ ha.not_ge (h hw), fun h hw ↦ (h hw).elim⟩

theorem strengthen_strong_ssubset (hsc : m.strong ⊆ m.ordinary)
    (h : ∃ a ∈ m.alternatives, a ⊂ m.ordinary ∧ a.Nonempty) :
    m.strengthen.strong ⊂ m.ordinary := by
  obtain ⟨a, haALT, haφ, w, hwa⟩ := h
  exact (ssubset_iff_of_subset (inter_subset_left.trans hsc)).2
    ⟨w, haφ.1 hwa, fun hmem ↦ (mem_strengthen_strong.1 hmem).2 a haALT haφ hwa⟩

-- the scalar assertion of the appendix's (2)
theorem strengthen_strong_eq_of_isGreatest {a₀ : Set W}
    (h : IsGreatest (m.alternatives ∩ Iio m.ordinary) a₀) :
    m.strengthen.strong = m.strong ∩ a₀ᶜ := by
  ext w
  simp only [mem_strengthen_strong, mem_inter_iff, mem_compl_iff]
  exact ⟨fun ⟨hw, hall⟩ ↦ ⟨hw, hall a₀ h.1.1 h.1.2⟩,
    fun ⟨hw, h₀⟩ ↦ ⟨hw, fun a haA haφ hwa ↦ h₀ (h.2 ⟨haA, haφ⟩ hwa)⟩⟩

theorem strengthen_strong_eq_sdiff {ψ : Set W} (h : m.alternatives ∩ Iio m.ordinary = {ψ}) :
    m.strengthen.strong = m.strong \ ψ := by
  rw [strengthen_strong_eq_of_isGreatest (h ▸ isGreatest_singleton), sdiff_eq]

-- the contradiction clause of the appendix's (2)
theorem strengthen_strong_eq_self (h : ∀ a ∈ m.alternatives, ¬a ⊂ m.ordinary) :
    m.strengthen.strong = m.strong :=
  inter_subset_left.antisymm fun _ hw ↦
    mem_strengthen_strong.2 ⟨hw, fun a ha hss ↦ (h a ha hss).elim⟩

theorem strengthen_strong_lexical_pair {φ ψ : Set W} (h : ψ ⊂ φ) :
    (lexical φ {φ, ψ}).strengthen.strong = φ \ ψ :=
  strengthen_strong_eq_sdiff (pair_inter_Iio h)

theorem lexical_strengthen_strong_eq_exh {φ : Set W} {ALT : Set (Set W)}
    (h : ∀ a ∈ ALT, a ⊆ φ ∨ φ ⊆ a) : (lexical φ ALT).strengthen.strong = exh ALT φ := by
  ext w
  simp only [mem_strengthen_strong, lexical, mem_exh]
  refine and_congr_right fun _ ↦ ⟨fun hs a ha hw ↦ by_contra fun hn ↦ ?_,
    fun he a ha hlt hw ↦ hlt.2 (he a ha hw)⟩
  exact hs a ha ⟨(h a ha).resolve_right hn, hn⟩ hw

/-! ### Strong Application -/

variable {F : Meaning (Set W → Set W')} {x : Meaning (Set W)} {v : W'}

theorem strongApply_of_antitone (h : Antitone F.ordinary) : F.strongApply x = F.recalibrate x :=
  ite_eq_left h

theorem strongApply_of_not_antitone (h : ¬Antitone F.ordinary) :
    F.strongApply x = F.applyRegular x :=
  ite_eq_right h

@[simp]
theorem strongApply_ordinary : (F.strongApply x).ordinary = F.ordinary x.ordinary := by
  unfold strongApply; split_ifs <;> rfl

theorem recalibrate_strong :
    (F.recalibrate x).strong =
      (⟨⟨F.ordinary x.ordinary, F.ordinary '' x.alternatives⟩, F.strong x.ordinary⟩ :
        Meaning (Set W')).strengthen.strong :=
  rfl

@[simp]
theorem mem_recalibrate_strong :
    v ∈ (F.recalibrate x).strong ↔
      v ∈ F.strong x.ordinary ∧
        ∀ a ∈ x.alternatives, F.ordinary a ⊂ F.ordinary x.ordinary → v ∉ F.ordinary a := by
  rw [recalibrate_strong, mem_strengthen_strong, forall_mem_image]

-- (84)
theorem recalibrate_strong_eq_of_isGreatest {ψ₀ : Set W'}
    (h : IsGreatest (F.ordinary '' x.alternatives ∩ Iio (F.ordinary x.ordinary)) ψ₀) :
    (F.recalibrate x).strong = F.strong x.ordinary ∩ ψ₀ᶜ := by
  rw [recalibrate_strong]
  exact strengthen_strong_eq_of_isGreatest h

theorem applyRegular_strong_subset (hf : Monotone F.ordinary) (hF : F.strong ≤ F.ordinary)
    (hx : x.strong ⊆ x.ordinary) : (F.applyRegular x).strong ⊆ (F.applyRegular x).ordinary :=
  fun _ hv ↦ hf hx (hF _ hv)

theorem recalibrate_strong_subset (hF : F.strong ≤ F.ordinary) :
    (F.recalibrate x).strong ⊆ (F.recalibrate x).ordinary :=
  fun _ hv ↦ hF _ hv.1

/-- Passing a nonvacuous implicature through a strictly antitone function, as *doubt* is,
violates the Strength Condition (79). -/
theorem not_strengthCondition_applyRegular (hf : StrictAnti F.ordinary) (hF : F.strong = F.ordinary)
    (hx : x.strong ⊂ x.ordinary) : ¬(F.applyRegular x).StrengthCondition := fun h ↦
  h (show F.ordinary x.ordinary < F.strong x.strong from hF ▸ hf hx)

end Meaning

open Meaning

/-! ### *Doubt* and the connectives -/

/-- *Doubt*, taken as complementation. -/
def doubt : Meaning (Set W → Set W) :=
  .lexical compl {compl}

/-- *`A` and*, on the scale of *or* and *and*. -/
def conj (A : Set W) : Meaning (Set W → Set W) :=
  .lexical (A ∩ ·) {(A ∩ ·), (A ∪ ·)}

/-- *`A` or*, on the scale of *or* and *and*. -/
def disj (A : Set W) : Meaning (Set W → Set W) :=
  .lexical (A ∪ ·) {(A ∩ ·), (A ∪ ·)}

section Connectives

variable {A B : Set W} {x : Meaning (Set W)}

@[simp]
theorem mem_doubt_strongApply_strong {v : W} :
    v ∈ (doubt.strongApply x).strong ↔
      v ∉ x.ordinary ∧ ∀ a ∈ x.alternatives, x.ordinary ⊂ a → v ∈ a := by
  rw [strongApply_of_antitone (compl_antitone _), mem_recalibrate_strong]
  simp only [doubt, lexical, mem_compl_iff, not_not]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ imp_congr_left compl_lt_compl_iff_lt

theorem not_antitone_inter (hA : A.Nonempty) : ¬Antitone (A ∩ ·) := fun h ↦
  hA.ne_empty (by simpa using h (empty_subset univ))

theorem not_antitone_union (hA : A ≠ univ) : ¬Antitone (A ∪ ·) := fun h ↦
  hA (eq_univ_of_univ_subset (by simpa using h (empty_subset univ)))

private theorem inter_ne_union [Nonempty W] (A : Set W) : (A ∩ ·) ≠ (A ∪ ·) := fun h ↦ by
  have h₀ : A = ∅ := by simpa using (congrFun h ∅).symm
  have h₁ : A = univ := by simpa using congrFun h univ
  exact (h₀ ▸ empty_ne_univ) h₁

private theorem pair_ne_singleton [Nonempty W] (A : Set W) {f : Set W → Set W} :
    ({(A ∩ ·), (A ∪ ·)} : Set (Set W → Set W)) ≠ {f} := fun h ↦ by
  have h₁ : (A ∩ ·) = f := (Set.ext_iff.1 h _).1 (Or.inl rfl)
  have h₂ : (A ∪ ·) = f := (Set.ext_iff.1 h _).1 (Or.inr rfl)
  exact inter_ne_union A (h₁.trans h₂.symm)

theorem conj_strongApply (hA : A.Nonempty) :
    (conj A).strongApply x =
      ⟨⟨A ∩ x.ordinary, {A ∩ x.ordinary, A ∪ x.ordinary}⟩, A ∩ x.strong⟩ := by
  have : Nonempty W := ⟨hA.some⟩
  rw [strongApply_of_not_antitone (not_antitone_inter hA), applyRegular,
    appAlternatives_of_not_given (F := (conj A).toWithAlternatives) (pair_ne_singleton A)]
  simp [conj, lexical]

theorem disj_strongApply (hA : A.Nonempty) (hA' : A ≠ univ) :
    (disj A).strongApply x =
      ⟨⟨A ∪ x.ordinary, {A ∩ x.ordinary, A ∪ x.ordinary}⟩, A ∪ x.strong⟩ := by
  have : Nonempty W := ⟨hA.some⟩
  rw [strongApply_of_not_antitone (not_antitone_union hA'), applyRegular,
    appAlternatives_of_not_given (F := (disj A).toWithAlternatives) (pair_ne_singleton A)]
  simp [disj, lexical]

/-- Under *doubt*, a conjunction gets the indirect implicature that the disjunction holds
((81)–(83)). -/
theorem doubt_conj_strong (hA : A.Nonempty) (h : A ∩ B ⊂ A ∪ B) :
    (doubt.strongApply ((conj A).strongApply (.lexical B {B}))).strong = (A ∩ B)ᶜ ∩ (A ∪ B) := by
  ext v
  rw [mem_doubt_strongApply_strong, conj_strongApply hA]
  simp only [lexical, forall_mem_insert, mem_singleton_iff, forall_eq]
  exact ⟨fun ⟨h₁, _, h₃⟩ ↦ ⟨h₁, h₃ h⟩, fun ⟨h₁, h₃⟩ ↦ ⟨h₁, fun h' ↦ (h'.2 h'.1).elim, fun _ ↦ h₃⟩⟩

-- (130), and (6) of the appendix
theorem doubt_disj_strong (hA : A.Nonempty) (hA' : A ≠ univ) :
    (doubt.strongApply ((disj A).strongApply (.lexical B {B}))).strong = (A ∪ B)ᶜ := by
  ext v
  rw [mem_doubt_strongApply_strong, disj_strongApply hA hA']
  simp only [lexical, forall_mem_insert, mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ (h'.2 (inter_subset_left.trans subset_union_left)).elim,
    fun h' ↦ (h'.2 h'.1).elim⟩⟩

end Connectives

/-! ### Scale selection -/

/-- An admissible choice of scale in context for an uttered scalar term. -/
structure IsScaleSelection (lexicalScale chosen : Set (Set W)) (utt : Set W) : Prop where
  /-- (99a): the chosen scale is a subset of the lexical scale. -/
  chosen_subset : chosen ⊆ lexicalScale
  /-- (99b): the chosen scale has at least two members. -/
  nontrivial : chosen.Nontrivial
  /-- The uttered term belongs to its chosen scale (presupposed by (99)). -/
  utt_mem : utt ∈ chosen
  /-- (99c): the uttered term is not the strongest chosen member whenever the lexical scale offers
  a stronger one, the "if possible" proviso. -/
  not_strongest : (∃ a ∈ lexicalScale, a ⊂ utt) → ∃ a ∈ chosen, a ⊂ utt

-- (99c)
theorem IsScaleSelection.strengthen_ssubset {lex chosen : Set (Set W)} {utt : Set W}
    (h : IsScaleSelection lex chosen utt) (hstr : ∃ a ∈ lex, a ⊂ utt)
    (hne : ∀ a ∈ chosen, a ⊂ utt → a.Nonempty) :
    (Meaning.lexical utt chosen).strengthen.strong ⊂ utt :=
  let ⟨a, ha, hau⟩ := h.not_strongest hstr
  strengthen_strong_ssubset subset_rfl ⟨a, ha, hau, hne a ha hau⟩

/-! ### The direct implicature of *some* -/

/-- Worlds for *John saw some students*: he saw none, some but not all, or all of them. -/
def sawSome : Set (Fin 3) := {w | w ≠ 0}

/-- *John saw every student*. -/
def sawEvery : Set (Fin 3) := {w | w = 2}

theorem sawEvery_ssubset : sawEvery ⊂ sawSome :=
  (ssubset_iff_of_subset fun w hw ↦ by simp_all [sawEvery, sawSome]).2
    ⟨1, by simp [sawSome], by simp [sawEvery]⟩

-- (74)–(76)
theorem some_not_all_implicature :
    (Meaning.lexical sawSome {sawSome, sawEvery}).strengthen.strong = sawSome \ sawEvery :=
  strengthen_strong_lexical_pair sawEvery_ssubset

-- (78)–(79)
theorem doubt_some_not_strengthCondition :
    ¬(doubt.applyRegular
      (Meaning.lexical sawSome {sawSome, sawEvery}).strengthen).StrengthCondition :=
  not_strengthCondition_applyRegular (compl_strictAnti _) rfl <|
    strengthen_strong_ssubset subset_rfl ⟨sawEvery, Or.inr rfl, sawEvery_ssubset, 2, rfl⟩

/-! ### Local and global computation -/

/-- Worlds for *Mary is either working at her paper or seeing some of her students*: whether she
is working, and whether she is seeing none, some but not all, or all of her students. -/
def working : Set (Bool × Fin 3) := {w | w.1}

/-- *Mary is seeing some of her students*. -/
def seeingSome : Set (Bool × Fin 3) := {w | w.2 ≠ 0}

/-- *Mary is seeing all of her students*. -/
def seeingAll : Set (Bool × Fin 3) := {w | w.2 = 2}

/-- The node *Mary is seeing some of her students*, with the scale of *some*. -/
def seeing : Meaning (Set (Bool × Fin 3)) :=
  .lexical seeingSome {seeingSome, seeingAll}

theorem seeingAll_ssubset : seeingAll ⊂ seeingSome :=
  (ssubset_iff_of_subset fun w hw ↦ by simp_all [seeingAll, seeingSome]).2
    ⟨(true, 1), by simp [seeingSome], by simp [seeingAll]⟩

theorem working_nonempty : working.Nonempty := ⟨(true, 0), rfl⟩

theorem working_ne_univ : working ≠ univ := fun h ↦ by
  simpa [working] using eq_univ_iff_forall.1 h (false, 0)

/-- Computed locally, with Krifka's rule at both scope sites, *Mary is either working at her paper
or seeing some of her students* says that she is either working or seeing some but not all of
them, and not both; computed at the root alone, it says that she is not working ((21)–(22)). -/
theorem working_or_seeingSome :
    ((disj working).strongApply seeing.strengthen).strengthen.strong =
        (working ∪ (seeingSome \ seeingAll)) \ (working ∩ seeingSome) ∧
      ((Meaning.lexical (working ∪ ·) {(working ∪ ·)}).strongApply seeing).strengthen.strong ⊆
        workingᶜ := by
  constructor
  · rw [disj_strongApply working_nonempty working_ne_univ, strengthen_strong_eq_sdiff]
    · exact congrArg (fun s ↦ (working ∪ s) \ (working ∩ seeingSome))
        (strengthen_strong_lexical_pair seeingAll_ssubset)
    · refine (congrArg (· ∩ _) (pair_comm _ _)).trans (pair_inter_Iio ?_)
      exact (ssubset_iff_of_subset (inter_subset_left.trans subset_union_left)).2
        ⟨(false, 1), Or.inr (by decide : (1 : Fin 3) ≠ 0), fun h ↦ Bool.false_ne_true h.1⟩
  · rw [strongApply_of_not_antitone (not_antitone_union working_ne_univ),
      strengthen_strong_eq_sdiff (ψ := working ∪ seeingAll)]
    · exact fun _ hv hw ↦ hv.2 (Or.inl hw)
    · have : ((Meaning.lexical (working ∪ ·) {(working ∪ ·)}).applyRegular seeing).alternatives =
          {working ∪ seeingSome, working ∪ seeingAll} := by
        rw [applyRegular, appAlternatives_of_given
          (F := (Meaning.lexical (working ∪ ·) {(working ∪ ·)}).toWithAlternatives) rfl]
        exact image_pair _ _ _
      rw [this]
      refine pair_inter_Iio ?_
      exact (ssubset_iff_of_subset (union_subset_union_right _ seeingAll_ssubset.1)).2
        ⟨(false, 1), Or.inr (by simp [seeingSome]), by simp [working, seeingAll]⟩

/-! ### A non-monotone quantifier -/

/-- *`x` smokes*, over pairs of a value for `x` among three students and a world recording
whether each student smokes and whether they drink. -/
def smokes : Set (Fin 3 × (Fin 3 → Bool × Bool)) := {p | (p.2 p.1).1}

/-- *`x` drinks*. -/
def drinks : Set (Fin 3 × (Fin 3 → Bool × Bool)) := {p | (p.2 p.1).2}

/-- *Exactly two students* binding `x`. -/
def exactlyTwo (S : Set (Fin 3 × (Fin 3 → Bool × Bool))) : Set (Fin 3 → Bool × Bool) :=
  {w | {x | (x, w) ∈ S}.ncard = 2}

theorem mem_exactlyTwo {S : Set (Fin 3 × (Fin 3 → Bool × Bool))} {w : Fin 3 → Bool × Bool} :
    w ∈ exactlyTwo S ↔ {x | (x, w) ∈ S}.ncard = 2 :=
  Iff.rfl

theorem not_antitone_exactlyTwo : ¬Antitone exactlyTwo := fun h ↦ by
  have h₂ : {x : Fin 3 | x ≠ 2}.ncard = 2 := by
    rw [show {x : Fin 3 | x ≠ 2} = {0, 1} by ext x; fin_cases x <;> simp]
    exact ncard_pair (by decide)
  have := h (empty_subset {p : Fin 3 × (Fin 3 → Bool × Bool) | p.1 ≠ 2})
    (show (fun _ ↦ (false, false)) ∈ exactlyTwo {p | p.1 ≠ 2} from h₂)
  simp [mem_exactlyTwo] at this

/-- *`x` smokes or drinks*, the disjunction applied to the open sentences. -/
noncomputable def smokesOrDrinks : Meaning (Set (Fin 3 × (Fin 3 → Bool × Bool))) :=
  (disj smokes).strongApply (.lexical drinks {drinks})

/-- *Exactly two students smoke or drink*, with Krifka's rule applied to the open sentence. -/
noncomputable def exactlyTwoSmokeOrDrink : Meaning (Set (Fin 3 → Bool × Bool)) :=
  (Meaning.lexical exactlyTwo {exactlyTwo}).strongApply smokesOrDrinks.strengthen

/-- The strong value of *exactly two students smoke or drink*, that exactly two do one but not
both, and its plain value entail neither the other (95). -/
theorem exactlyTwoSmokeOrDrink_independent :
    ¬exactlyTwoSmokeOrDrink.strong ⊆ exactlyTwoSmokeOrDrink.ordinary ∧
      ¬exactlyTwoSmokeOrDrink.ordinary ⊆ exactlyTwoSmokeOrDrink.strong := by
  have hne : smokes.Nonempty := ⟨(0, fun _ ↦ (true, false)), rfl⟩
  have hne' : smokes ≠ univ := fun h ↦ by
    simpa [smokes] using eq_univ_iff_forall.1 h (0, fun _ ↦ (false, false))
  have hlt : smokes ∩ drinks ⊂ smokes ∪ drinks :=
    (ssubset_iff_of_subset fun _ hp ↦ Or.inl hp.1).2
      ⟨(0, fun _ ↦ (true, false)), Or.inl rfl, fun h ↦ Bool.false_ne_true h.2⟩
  have hsd : smokesOrDrinks.strengthen.strong = (smokes ∪ drinks) \ (smokes ∩ drinks) := by
    rw [smokesOrDrinks, disj_strongApply hne hne', strengthen_strong_eq_sdiff]
    · rfl
    · exact (congrArg (· ∩ _) (pair_comm _ _)).trans (pair_inter_Iio hlt)
  have hs : exactlyTwoSmokeOrDrink.strong = exactlyTwo ((smokes ∪ drinks) \ (smokes ∩ drinks)) := by
    rw [exactlyTwoSmokeOrDrink, strongApply_of_not_antitone not_antitone_exactlyTwo, applyRegular,
      ← hsd]
    rfl
  have hp : exactlyTwoSmokeOrDrink.ordinary = exactlyTwo (smokes ∪ drinks) := by
    rw [exactlyTwoSmokeOrDrink, strongApply_ordinary, smokesOrDrinks]
    exact congrArg exactlyTwo (strongApply_ordinary)
  -- two students only smoke and the third smokes and drinks
  have h₁ : {x | (x, fun i : Fin 3 ↦ (true, i == 2)) ∈ (smokes ∪ drinks) \ (smokes ∩ drinks)} =
      ({0, 1} : Set (Fin 3)) := by
    ext x; fin_cases x <;> simp [smokes, drinks]
  have h₁' : {x | (x, fun i : Fin 3 ↦ (true, i == 2)) ∈ smokes ∪ drinks} = univ := by
    ext x; simp [smokes]
  -- two students smoke and drink and the third does neither
  have h₂ : {x | (x, fun i : Fin 3 ↦ (i != 2, i != 2)) ∈ smokes ∪ drinks} =
      ({0, 1} : Set (Fin 3)) := by
    ext x; fin_cases x <;> simp [smokes, drinks]
  have h₂' : {x | (x, fun i : Fin 3 ↦ (i != 2, i != 2)) ∈ (smokes ∪ drinks) \ (smokes ∩ drinks)} =
      ∅ := by
    ext x; simp [smokes, drinks]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h (by rw [hs, mem_exactlyTwo, h₁]; exact ncard_pair (by decide))
    rw [hp, mem_exactlyTwo, h₁', ncard_univ] at this
    simp at this
  · have := h (by rw [hp, mem_exactlyTwo, h₂]; exact ncard_pair (by decide))
    rw [hs, mem_exactlyTwo, h₂'] at this
    simp at this

-- (95)
theorem exactlyTwoSmokeOrDrink_strengthCondition : exactlyTwoSmokeOrDrink.StrengthCondition :=
  fun h ↦ exactlyTwoSmokeOrDrink_independent.2 h.1

/-! ### Scale truncation -/

/-- Worlds for *I have many matches left*: none, a few, many, or all of the box. -/
def haveSome : Set (Fin 4) := {n | 1 ≤ n}

/-- *I have many matches left*. -/
def haveMany : Set (Fin 4) := {n | 2 ≤ n}

/-- *I have all the matches left*. -/
def haveAll : Set (Fin 4) := {n | n = 3}

theorem haveMany_ssubset_haveSome : haveMany ⊂ haveSome :=
  (ssubset_iff_of_subset fun _ (hn : (2 : Fin 4) ≤ _) ↦ (by decide : (1 : Fin 4) ≤ 2).trans hn).2
    ⟨1, show (1 : Fin 4) ≤ 1 from le_rfl, show ¬(2 : Fin 4) ≤ 1 by decide⟩

theorem haveAll_ssubset_haveMany : haveAll ⊂ haveMany :=
  (ssubset_iff_of_subset fun n hn ↦ by simp_all [haveAll, haveMany]).2
    ⟨2, by simp [haveMany], by simp [haveAll]⟩

-- (99), (100)
theorem isScaleSelection_truncated :
    IsScaleSelection {haveSome, haveMany, haveAll} {haveMany, haveAll} haveMany where
  chosen_subset := subset_insert _ _
  nontrivial := nontrivial_pair haveAll_ssubset_haveMany.ne'
  utt_mem := Or.inl rfl
  not_strongest _ := ⟨haveAll, Or.inr rfl, haveAll_ssubset_haveMany⟩

-- (98)
theorem not_isScaleSelection_some_many :
    ¬IsScaleSelection {haveSome, haveMany, haveAll} {haveSome, haveMany} haveMany := fun h ↦ by
  obtain ⟨a, ha, hlt⟩ := h.not_strongest ⟨haveAll, Or.inr (Or.inr rfl), haveAll_ssubset_haveMany⟩
  rcases ha with rfl | rfl
  exacts [haveMany_ssubset_haveSome.2 hlt.1, hlt.2 hlt.1]

-- (100)
theorem notMany_strong :
    (doubt.strongApply (.lexical haveMany {haveSome, haveMany, haveAll})).strong =
      haveManyᶜ ∩ haveSome := by
  ext n
  rw [mem_doubt_strongApply_strong]
  simp only [lexical, forall_mem_insert, mem_singleton_iff, forall_eq]
  exact ⟨fun ⟨h₁, h₂, _⟩ ↦ ⟨h₁, h₂ haveMany_ssubset_haveSome⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun _ ↦ h₂,
    fun h ↦ (h.2 h.1).elim, fun h ↦ (haveAll_ssubset_haveMany.2 h.1).elim⟩⟩

-- (100)
theorem notMany_truncated_strong :
    (doubt.strongApply (.lexical haveMany {haveMany, haveAll})).strong = haveManyᶜ := by
  ext n
  rw [mem_doubt_strongApply_strong]
  simp only [lexical, forall_mem_insert, mem_singleton_iff, forall_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ (h'.2 h'.1).elim,
    fun h' ↦ (haveAll_ssubset_haveMany.2 h'.1).elim⟩⟩

/-! ### *Any* -/

section Closure

variable {E : Type*} {C : Set W → Set W} {Δ : Set (Set E)} {D D' : Set E} {P : E → Set W}

/-- The universal closure of a sentence `C (∃ x ∈ D', P x)` with *any* over the expansions
`D' ∈ Δ` of its domain. -/
def universalClosure (C : Set W → Set W) (Δ : Set (Set E)) (P : E → Set W) : Set W :=
  ⋂ D' ∈ Δ, C (⋃ x ∈ D', P x)

@[simp]
theorem universalClosure_singleton : universalClosure C {D'} P = C (⋃ x ∈ D', P x) :=
  biInter_singleton _ _

theorem universalClosure_subset (h : D' ∈ Δ) :
    universalClosure C Δ P ⊆ C (⋃ x ∈ D', P x) :=
  biInter_subset_of_mem h

theorem universalClosure_singleton_subset_iff :
    universalClosure C {D'} P ⊆ C (⋃ x ∈ D, P x) ↔ Strengthening C D D' P := by
  rw [universalClosure_singleton, Strengthening]

-- (115), (116)
theorem universalClosure_subset_of_antitone (hC : Antitone C) (hΔ : ∀ D' ∈ Δ, D ⊆ D')
    (hne : Δ.Nonempty) : universalClosure C Δ P ⊆ C (⋃ x ∈ D, P x) :=
  let ⟨_, hD'⟩ := hne
  (universalClosure_subset hD').trans (de_satisfies_strengthening hC _ _ P (hΔ _ hD'))

end Closure

/-- Worlds for *I doubt that John ate the cake and drank any coffee*: whether John ate the cake
and which of two coffees he drank. -/
def ateCake : Set (Bool × (Bool → Bool)) := {w | w.1}

/-- *John drank coffee `c`*. -/
def drank (c : Bool) : Set (Bool × (Bool → Bool)) := {w | w.2 c}

/-- *John drank some coffee*, over the contextual domain of the first coffee. -/
def someCoffee : Set (Bool × (Bool → Bool)) :=
  ⋃ c ∈ ({false} : Set Bool), drank c

/-- *I doubt that John ate the cake and drank `X`*. -/
def doubtAnd (X : Set (Bool × (Bool → Bool))) : Set (Bool × (Bool → Bool)) :=
  (ateCake ∩ X)ᶜ

/-- *I doubt that John ate the cake or drank `X`*. -/
def doubtOr (X : Set (Bool × (Bool → Bool))) : Set (Bool × (Bool → Bool)) :=
  (ateCake ∪ X)ᶜ

theorem antitone_doubtAnd : Antitone doubtAnd := fun _ _ h ↦
  compl_subset_compl.2 (inter_subset_inter_right _ h)

theorem antitone_doubtOr : Antitone doubtOr := fun _ _ h ↦
  compl_subset_compl.2 (union_subset_union_right _ h)

/-- The competitor *I doubt that John ate the cake and drank some coffee*. -/
noncomputable def doubtAndSome : Meaning (Set (Bool × (Bool → Bool))) :=
  doubt.strongApply ((conj ateCake).strongApply (.lexical someCoffee {someCoffee}))

/-- The competitor *I doubt that John ate the cake or drank some coffee*. -/
noncomputable def doubtOrSome : Meaning (Set (Bool × (Bool → Bool))) :=
  doubt.strongApply ((disj ateCake).strongApply (.lexical someCoffee {someCoffee}))

theorem ateCake_nonempty : ateCake.Nonempty := ⟨(true, fun _ ↦ false), rfl⟩

theorem ateCake_ne_univ : ateCake ≠ univ := fun h ↦ by
  simpa [ateCake] using eq_univ_iff_forall.1 h (false, fun _ ↦ false)

-- (129b)
theorem doubtAndSome_strong :
    doubtAndSome.strong = (ateCake ∩ someCoffee)ᶜ ∩ (ateCake ∪ someCoffee) :=
  doubt_conj_strong ateCake_nonempty <|
    (ssubset_iff_of_subset (inter_subset_left.trans subset_union_left)).2
      ⟨(true, fun _ ↦ false), Or.inl rfl, fun h ↦ by simp [someCoffee, drank] at h⟩

-- (130)
theorem doubtOrSome_strong : doubtOrSome.strong = (ateCake ∪ someCoffee)ᶜ :=
  doubt_disj_strong ateCake_nonempty ateCake_ne_univ

-- (114)
theorem not_universalClosure_id_subset : ¬universalClosure id {univ} drank ⊆ someCoffee := by
  intro h
  have := h (a := (false, id)) (by simp [drank])
  simp [someCoffee, drank] at this

/-- Under *doubt … and*, the closure of *any* entails the competitor's plain value but not its
strong value ((116), (127)–(129)). -/
theorem doubtAnd_any :
    universalClosure doubtAnd {univ} drank ⊆ doubtAndSome.ordinary ∧
      ¬universalClosure doubtAnd {univ} drank ⊆ doubtAndSome.strong := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [universalClosure_singleton, doubtAndSome, strongApply_ordinary, strongApply_ordinary]
    exact antitone_doubtAnd (biUnion_subset_biUnion_left (subset_univ _))
  · have hw : ((false, fun _ ↦ false) : Bool × (Bool → Bool)) ∈
        universalClosure doubtAnd {univ} drank := by
      simp [doubtAnd, ateCake]
    have := (doubtAndSome_strong ▸ h hw).2
    simp [ateCake, someCoffee, drank] at this

-- (130)
theorem doubtOr_any : universalClosure doubtOr {univ} drank ⊆ doubtOrSome.strong := by
  rw [universalClosure_singleton, doubtOrSome_strong]
  exact antitone_doubtOr (biUnion_subset_biUnion_left (subset_univ _))

/-- The model of a row of *I doubt that John ate the cake … drank any coffee*, read from its
connective: the context of *any* and the competitor with *some*. -/
noncomputable def doubtAny? (e : Datum) :
    Option ((Set (Bool × (Bool → Bool)) → Set (Bool × (Bool → Bool))) ×
      Meaning (Set (Bool × (Bool → Bool)))) :=
  match e.feature? "connective" with
  | some "and" => some (doubtAnd, doubtAndSome)
  | some "or" => some (doubtOr, doubtOrSome)
  | _ => none

-- (128a), (130a)
theorem rows_any : ∀ e ∈ Examples.all, ∀ p ∈ doubtAny? e,
    (e.judgment.band = .accepted ↔ universalClosure p.1 {univ} drank ⊆ p.2.strong) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · obtain rfl : (doubtAnd, doubtAndSome) = p := Option.some_injective _ hp
    exact iff_of_false (by decide) doubtAnd_any.2
  · obtain rfl : (doubtOr, doubtOrSome) = p := Option.some_injective _ hp
    exact iff_of_true rfl doubtOr_any

theorem readCount_doubtAny : Datum.ReadCount doubtAny? Examples.all 2 := by
  decide

end Chierchia2004
