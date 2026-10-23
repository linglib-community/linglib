module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Linglib.Semantics.Exhaustification.Finite

/-!
# Magri (2014): An Account for the Homogeneity Effect Triggered by Plural Definites and Conjunction

This file formalizes the double-strengthening account of homogeneity of [magri-2014]. A plural
definite has the plain existential meaning of the indefinite, and its universal reading is an
implicature of an implicature: the indefinite triggers the *only some* inference, and the definite
triggers the inference that this inference is false, by the iterated exhaustification (19) of
[spector-2007b] over the exhaustivity operator (18). The paper's abstract configuration (§5.2) is
three items, the item displaying homogeneity and the weak and strong poles of the scale it patterns
with (`Item`), with a non-transitive Horn-mateness that pairs the item with one pole only. In the
primal theory (52) the item means the weak pole and is a Horn-mate of it (`primal`,
`primalMates`), so the inner exhaustification excludes nothing for the item while the outer one,
denying the strengthened meaning of the weak pole, yields the strong one, (53b)
(`strengthened_primal_mystery_eq_strong`); in a downward-entailing environment the negated meanings
are already strongest and nothing is strengthened, (53a) (`strengthened_primal_not_mystery`). The
dual theory (54), (55) turns this upside down by swapping the poles (`dual`, `dualMates`), and its
computations are the primal ones relabeled (`strengthened_comp_equiv`). In a scenario where the
weak pole holds without the strong both the positive and the negated sentence are false after
strengthening, the homogeneity gap (`primal_gap`, `dual_gap`).

Plural definites and plural morphology instantiate the primal theory with cardinality thresholds
over the extension of the predicate, (32) (`atLeast`, `the_eq_all`), and the same computation in
the non-monotonic scope of *exactly one student* gives universal force in its upward and
existential force in its downward component, (37) (`exactlyOne_the`). Unfocused conjunction
instantiates the dual theory (§5.3), so under negation it behaves as disjunction, (61)
(`not_andUnF_eq_not_or`); with the appendix's enriched alternatives, the atomic conjuncts (69),
the same result comes out of [fox-2007]'s innocent exclusion, (71) and (72)
(`strengthened_not_andUnF`). Questions, which license no strengthening, would tell the theories
apart, (62) and (63), and the paper conjectures (§4) that a matrix definite has universal force
exactly when the indefinite triggers its implicature, which yields the sloppy existential reading
of the classroom example of [gajewski-2005]; neither is modeled.

## Implementation notes

* Meanings are sets of worlds over a finite world type; exhaustification is the substrate's
  innocent exclusion, so the excludable alternatives of (18) are those of the appendix's (70)
  throughout, which agrees with the paper's simpler definition on every computation it performs.
* Each item carries its own Horn-mates, which is how the non-transitivity of (52b), (54b) and
  (69b) is encoded; the prejacent is not among its own alternatives.
* The consistency hypotheses of the general computations, that the weak pole can hold without
  the strong and that the strong pole is satisfiable, are the conditions under which Fox's
  exclusion denies an alternative.

## TODO

* The appendix's computations for conjunction under *exactly one girl*, (74) to (76), need three
  girls for the strengthened meaning to be satisfiable and are not formalized.

## References

* [magri-2014]
* [spector-2007b]
* [fox-2007]
* [sauerland-2004]
* [szabolcsi-haddican-2004]
* [gajewski-2005]
-/

@[expose] public section

namespace Magri2014

open Exhaustification Finset Function

variable {W ι : Type*} [Fintype W] [DecidableEq W] [DecidableEq ι]

/-! ### Iterated exhaustification over Horn-mates (§3.1, §3.2) -/

/-- (18) with each item's own Horn-mates: the meaning of the item `i` exhaustified against the
meanings of its Horn-mates. -/
def exh (mates : ι → Finset ι) (m : ι → Finset W) (i : ι) : Finset W :=
  innocent.exh ((mates i).image m) (m i)

/-- (19): the strengthened meaning is the iterated exhaustification of [spector-2007b], the outer
operator denying the strengthened meanings of the Horn-mates. Two iterations suffice for every
configuration of the paper. -/
def strengthened (mates : ι → Finset ι) (m : ι → Finset W) : ι → Finset W :=
  (exh mates)^[2] m

theorem exh_comp_equiv (σ : ι ≃ ι) (mates : ι → Finset ι) (m : ι → Finset W) :
    exh (fun i ↦ (mates (σ i)).image σ.symm) (m ∘ σ) = exh mates m ∘ σ := by
  funext i
  simp [exh, image_image, comp_def]

theorem strengthened_comp_equiv (σ : ι ≃ ι) (mates : ι → Finset ι) (m : ι → Finset W) :
    strengthened (fun i ↦ (mates (σ i)).image σ.symm) (m ∘ σ) = strengthened mates m ∘ σ := by
  show exh _ (exh _ (m ∘ σ)) = exh mates (exh mates m) ∘ σ
  rw [exh_comp_equiv, exh_comp_equiv]

/-! ### The primal and the dual theory (§5.2) -/

/-- The three items of a homogeneity configuration: the item displaying homogeneity and the weak
and strong poles of the scale it patterns with. -/
inductive Item where
  | mystery
  | weak
  | strong
  deriving DecidableEq

/-- (52b): in the primal theory the item is a Horn-mate of the weak pole only, while the two poles
are Horn-mates of each other. -/
def primalMates : Item → Finset Item
  | .mystery => {.weak}
  | .weak => {.mystery, .strong}
  | .strong => {.weak}

/-- (52a): in the primal theory the item means the weak pole. -/
def primal (wk st : Finset W) : Item → Finset W
  | .mystery => wk
  | .weak => wk
  | .strong => st

/-- The dual theory turns the primal upside down by exchanging the poles. -/
abbrev swap : Equiv.Perm Item := Equiv.swap .weak .strong

/-- (54b): in the dual theory the item is a Horn-mate of the strong pole only. -/
def dualMates (i : Item) : Finset Item := (primalMates (swap i)).image swap

/-- (54a): in the dual theory the item means the strong pole. -/
def dual (wk st : Finset W) : Item → Finset W := primal st wk ∘ swap

variable {wk st : Finset W}

theorem compl_comp_primal : compl ∘ primal wk st = primal wkᶜ stᶜ := by
  funext i
  cases i <;> rfl

theorem compl_comp_dual : compl ∘ dual wk st = dual wkᶜ stᶜ := by
  funext i
  cases i <;> rfl

theorem strengthened_dual : strengthened dualMates (dual wk st) =
    strengthened primalMates (primal st wk) ∘ swap := by
  have : dualMates = fun i ↦ (primalMates (swap i)).image swap.symm := by
    funext i
    rw [Equiv.symm_swap]
    rfl
  rw [this]
  exact strengthened_comp_equiv swap primalMates (primal st wk)

theorem exh_primal_mystery : exh primalMates (primal wk st) .mystery = wk := by
  show innocent.exh (({.weak} : Finset Item).image (primal wk st)) wk = wk
  rw [image_singleton]
  exact innocent_exh_eq_self_of_forall_subset (by simp [primal])

theorem exh_primal_weak (h : (wk \ st).Nonempty) :
    exh primalMates (primal wk st) .weak = wk \ st := by
  have hne : wk ≠ st := fun e ↦ by simp [e] at h
  show innocent.exh (({.mystery, .strong} : Finset Item).image (primal wk st)) wk = wk \ st
  rw [image_insert, image_singleton]
  simp only [primal]
  rw [innocent_exh_erase_entailed subset_rfl (h.mono sdiff_subset), erase_insert (by simpa),
    innocent_exh_singleton h]

/-- The weak pole excludes nothing when the strong pole is not stronger. -/
theorem exh_primal_weak_of_subset (h : wk ⊆ st) : exh primalMates (primal wk st) .weak = wk :=
  innocent_exh_eq_self_of_forall_subset (by simp [primal, primalMates, h])

/-- The core of (53b) and (37): double strengthening conjoins the item with the strong pole. -/
theorem strengthened_primal_mystery (h₁ : (wk \ st).Nonempty) (h₂ : (wk ∩ st).Nonempty) :
    strengthened primalMates (primal wk st) .mystery = wk ∩ st := by
  show innocent.exh (({.weak} : Finset Item).image (exh primalMates (primal wk st)))
    (exh primalMates (primal wk st) .mystery) = wk ∩ st
  rw [image_singleton, exh_primal_weak h₁, exh_primal_mystery,
    innocent_exh_singleton (by rwa [sdiff_sdiff_right_self, inf_eq_inter]), sdiff_sdiff_right_self,
    inf_eq_inter]

theorem strengthened_primal_mystery_of_subset (h : wk ⊆ st) :
    strengthened primalMates (primal wk st) .mystery = wk := by
  show innocent.exh (({.weak} : Finset Item).image (exh primalMates (primal wk st)))
    (exh primalMates (primal wk st) .mystery) = wk
  rw [image_singleton, exh_primal_weak_of_subset h, exh_primal_mystery]
  exact innocent_exh_eq_self_of_forall_subset (by simp)

/-- (53b): in an upward-entailing environment the primal item strengthens to the strong pole. -/
theorem strengthened_primal_mystery_eq_strong (h : st ⊆ wk) (hne : st.Nonempty) :
    strengthened primalMates (primal wk st) .mystery = st := by
  rcases (wk \ st).eq_empty_or_nonempty with h₁ | h₁
  · rw [strengthened_primal_mystery_of_subset (sdiff_eq_empty_iff_subset.1 h₁)]
    exact subset_antisymm (sdiff_eq_empty_iff_subset.1 h₁) h
  · rw [strengthened_primal_mystery h₁ (by rwa [inter_eq_right.2 h]), inter_eq_right.2 h]

/-- (53a): under negation the primal item is not strengthened and shows its weak meaning. -/
theorem strengthened_primal_not_mystery (h : st ⊆ wk) :
    strengthened primalMates (compl ∘ primal wk st) .mystery = wkᶜ := by
  rw [compl_comp_primal]
  exact strengthened_primal_mystery_of_subset (compl_subset_compl.2 h)

/-- (55b): in an upward-entailing environment the dual item shows its strong meaning. -/
theorem strengthened_dual_mystery (h : st ⊆ wk) :
    strengthened dualMates (dual wk st) .mystery = st := by
  rw [strengthened_dual]
  exact strengthened_primal_mystery_of_subset h

/-- (55a): under negation the dual item strengthens to the negation of the weak pole. -/
theorem strengthened_dual_not_mystery (h : st ⊆ wk) (h₁ : (wk \ st).Nonempty)
    (h₂ : wkᶜ.Nonempty) : strengthened dualMates (compl ∘ dual wk st) .mystery = wkᶜ := by
  rw [compl_comp_dual, strengthened_dual]
  show strengthened primalMates (primal stᶜ wkᶜ) .mystery = wkᶜ
  rw [strengthened_primal_mystery (by rwa [compl_sdiff_compl])
      (by rwa [inter_eq_right.2 (compl_subset_compl.2 h)]),
    inter_eq_right.2 (compl_subset_compl.2 h)]

theorem primal_gap (h : st ⊆ wk) (hne : st.Nonempty) :
    (strengthened primalMates (primal wk st) .mystery)ᶜ ∩
      (strengthened primalMates (compl ∘ primal wk st) .mystery)ᶜ = wk \ st := by
  rw [strengthened_primal_mystery_eq_strong h hne, strengthened_primal_not_mystery h, compl_compl,
    inter_comm, ← inf_eq_inter, ← sdiff_eq]

theorem dual_gap (h : st ⊆ wk) (h₁ : (wk \ st).Nonempty) (h₂ : wkᶜ.Nonempty) :
    (strengthened dualMates (dual wk st) .mystery)ᶜ ∩
      (strengthened dualMates (compl ∘ dual wk st) .mystery)ᶜ = wk \ st := by
  rw [strengthened_dual_mystery h, strengthened_dual_not_mystery h h₁ h₂, compl_compl,
    inter_comm, ← inf_eq_inter, ← sdiff_eq]

/-! ### Plural definites and plural morphology (§3.3, §3.4) -/

section Definites

variable (D : Type*) [Fintype D]

/-- The worlds, extensions of the predicate over the domain `D`, where at least `n` members
satisfy it. -/
def atLeast (n : ℕ) : Finset (Finset D) := univ.filter fun s ↦ n ≤ s.card

/-- (31c), (24c): SOME and SING, at least one. -/
abbrev some : Finset (Finset D) := atLeast D 1

/-- (24b): TWO, at least two. -/
abbrev two : Finset (Finset D) := atLeast D 2

/-- (31b): ALL, the whole domain. -/
abbrev all : Finset (Finset D) := atLeast D (Fintype.card D)

variable {D}

theorem mem_atLeast {n : ℕ} {s : Finset D} : s ∈ atLeast D n ↔ n ≤ s.card := by
  simp [atLeast]

theorem mem_all {s : Finset D} : s ∈ all D ↔ s = univ := by
  rw [mem_atLeast]
  exact ⟨fun h ↦ eq_univ_of_card s (le_antisymm (card_le_univ s) h),
    fun h ↦ by subst h; exact Finset.card_univ.ge⟩

/-- A higher threshold is stronger. -/
theorem atLeast_subset_atLeast {m n : ℕ} (h : m ≤ n) : atLeast D n ⊆ atLeast D m := fun _ hs ↦
  mem_atLeast.2 (h.trans (mem_atLeast.1 hs))

theorem atLeast_nonempty {n : ℕ} (h : n ≤ Fintype.card D) : (atLeast D n).Nonempty :=
  ⟨univ, mem_atLeast.2 (Finset.card_univ (α := D) ▸ h)⟩

variable [DecidableEq D]

/-- An item meaning a lower threshold whose Horn-mate is a higher threshold strengthens to the
higher one ((27), (34)). -/
theorem strengthened_atLeast {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ Fintype.card D) :
    strengthened primalMates (primal (atLeast D m) (atLeast D n)) .mystery = atLeast D n :=
  strengthened_primal_mystery_eq_strong (atLeast_subset_atLeast hmn) (atLeast_nonempty hn)

/-- (34): *Mary saw the boys* is universal. -/
theorem the_eq_all [Nonempty D] :
    strengthened primalMates (primal (some D) (all D)) .mystery = all D :=
  strengthened_atLeast Fintype.card_pos le_rfl

/-- (35): *Mary didn't see the boys* is *Mary saw none of the boys*. -/
theorem not_the_eq_not_some [Nonempty D] :
    strengthened primalMates (compl ∘ primal (some D) (all D)) .mystery = (some D)ᶜ :=
  strengthened_primal_not_mystery (atLeast_subset_atLeast Fintype.card_pos)

theorem the_gap [Nonempty D] :
    (strengthened primalMates (primal (some D) (all D)) .mystery)ᶜ ∩
      (strengthened primalMates (compl ∘ primal (some D) (all D)) .mystery)ᶜ =
        some D \ all D :=
  primal_gap (atLeast_subset_atLeast Fintype.card_pos) (atLeast_nonempty le_rfl)

end Definites

/-! ### Non-monotonic environments (§3.4) -/

section ExactlyOne

variable (S P : Type*) [Fintype S] [Fintype P] [DecidableEq S] [DecidableEq P]

/-- The worlds, assignments of solved problems to students, where the number of students whose
solved problems satisfy `q` is exactly `n`. -/
def solvedBy (q : Finset P → Prop) [DecidablePred q] (n : ℕ) : Finset (S → Finset P) :=
  univ.filter fun w ↦ (univ.filter fun s ↦ q (w s)).card = n

/-- (36c): ∃!SOME, exactly one student solved some of the problems. -/
def exactlyOneSome : Finset (S → Finset P) := solvedBy S P (fun s ↦ 1 ≤ s.card) 1

/-- (36b): ∃!ALL, exactly one student solved all the problems. -/
def exactlyOneAll : Finset (S → Finset P) := solvedBy S P (fun s ↦ s = univ) 1

/-- ¬∃₂SOME ∧ ∃₁ALL: at most one student solved some of the problems, and one solved them
all. -/
def uniqueSolverAll : Finset (S → Finset P) :=
  univ.filter fun w ↦ (univ.filter fun s ↦ 1 ≤ (w s).card).card ≤ 1 ∧ ∃ s, w s = univ

variable {S P}

/-- The last step of (37): exactly one solved some and exactly one solved all iff at most one
solved some and one solved all. -/
theorem exactlyOneSome_inter_exactlyOneAll [Nonempty P] :
    exactlyOneSome S P ∩ exactlyOneAll S P = uniqueSolverAll S P := by
  ext w
  simp only [exactlyOneSome, exactlyOneAll, uniqueSolverAll, solvedBy, mem_inter, mem_filter,
    mem_univ, true_and]
  have hsub : (univ.filter fun s ↦ w s = univ) ⊆ univ.filter fun s ↦ 1 ≤ (w s).card := by
    intro s hs
    rw [mem_filter] at hs ⊢
    exact ⟨hs.1, hs.2 ▸ card_pos.2 univ_nonempty⟩
  have hle := card_le_card hsub
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨s, hs⟩ := card_pos.1 (h₂ ▸ Nat.one_pos)
    exact ⟨h₁.le, s, (mem_filter.1 hs).2⟩
  · rintro ⟨h₁, s, hs⟩
    have : 0 < (univ.filter fun s ↦ w s = univ).card :=
      card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ s, hs⟩⟩
    omega

/-- In the scope of *exactly one student*, the definite strengthens to ∃!THE ∧ ∃!ALL (37). -/
theorem exactlyOne_the [Nonempty P] (h₁ : (exactlyOneSome S P \ exactlyOneAll S P).Nonempty)
    (h₂ : (exactlyOneSome S P ∩ exactlyOneAll S P).Nonempty) :
    strengthened primalMates (primal (exactlyOneSome S P) (exactlyOneAll S P)) .mystery =
      uniqueSolverAll S P := by
  rw [strengthened_primal_mystery h₁ h₂, exactlyOneSome_inter_exactlyOneAll]

end ExactlyOne

/-! ### Unfocused conjunction (§5.3, Appendix) -/

section Conjunction

/-- The two boys of (47). -/
inductive Boy where
  | adam
  | bill
  deriving DecidableEq, Fintype, Nonempty

/-- Unfocused conjunction instantiates the dual theory, with disjunction the weak and focused
conjunction the strong pole (56). -/
theorem not_andUnF_eq_not_or :
    strengthened dualMates (compl ∘ dual (some Boy) (all Boy)) .mystery = (some Boy)ᶜ :=
  strengthened_dual_not_mystery (atLeast_subset_atLeast Fintype.card_pos) (by decide) (by decide)

/-- The five sentences of the appendix's enriched configuration (69): focused and unfocused
conjunction, the two atomic conjuncts, and disjunction. -/
inductive ConjItem where
  | andF
  | andUnF
  | left
  | right
  | or
  deriving DecidableEq

/-- (69b): the atomic conjuncts are alternatives of both conjunctions and of disjunction, after
[sauerland-2004]; disjunction is an alternative of focused conjunction only. -/
def conjMates : ConjItem → Finset ConjItem
  | .andF => {.andUnF, .or, .left, .right}
  | .andUnF => {.andF, .left, .right}
  | .left => {.andF, .andUnF, .or, .right}
  | .right => {.andF, .andUnF, .or, .left}
  | .or => {.andF, .left, .right}

/-- (69a): the meanings of the five sentences. -/
def conj : ConjItem → Finset (Finset Boy)
  | .andF => all Boy
  | .andUnF => all Boy
  | .left => univ.filter (.adam ∈ ·)
  | .right => univ.filter (.bill ∈ ·)
  | .or => some Boy

/-- (71): one exhaustification of the negated sentences; unfocused conjunction excludes nothing,
since denying either negated conjunct forces the other. -/
theorem exh_not_conj :
    exh conjMates (compl ∘ conj) .andF = (all Boy)ᶜ ∩ some Boy ∧
      exh conjMates (compl ∘ conj) .andUnF = (all Boy)ᶜ ∧
      exh conjMates (compl ∘ conj) .left = (conj .left)ᶜ ∩ some Boy ∧
      exh conjMates (compl ∘ conj) .right = (conj .right)ᶜ ∩ some Boy := by
  decide

/-- (72): with the enriched alternatives, negated unfocused conjunction still strengthens to
negated disjunction, as in (61). -/
theorem strengthened_not_andUnF :
    strengthened conjMates (compl ∘ conj) .andUnF = (some Boy)ᶜ := by
  decide

theorem strengthened_not_andUnF_eq :
    strengthened conjMates (compl ∘ conj) .andUnF =
      strengthened dualMates (compl ∘ dual (some Boy) (all Boy)) .mystery := by
  rw [strengthened_not_andUnF, not_andUnF_eq_not_or]

end Conjunction

end Magri2014
