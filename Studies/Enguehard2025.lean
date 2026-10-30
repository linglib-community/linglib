module

public import Studies.Fox2018
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.TFAE

/-!
# Enguehard (2025): Upward monotonicity and the strongest answer condition

Enguehard traces the prevalence of upward-monotone logical words to exhaustification. A set of
alternatives is strongly stable when every world has a strongest true member, Dayal's condition on
answers, and that is when [exhaustifying the non-dominated alternatives yields exactly the
partition they induce](##Enguehard2025.tfae_stronglyStable), for the basic exhaustifier, innocent
exclusion and minimal worlds alike. Over atoms and symmetric functions of them, weak stability of
the alternatives and of their negations
[leaves only *every* and *some*](##Enguehard2025.mem_every_some_of_bilaterallyWeaklyStable).
Strong stability of the atoms and the sentences of a lexicon of conservative, quantity-invariant
determiners, and of their negations, [makes every determiner monotone in its
scope](##Enguehard2025.scopeMonotone_of_bilaterallyStronglyStable). Among proper clones of
functions, strong stability of the alternatives and their negations at every number of atoms
[singles out the upward-monotone ones](##Enguehard2025.bilaterallyStronglyStable_iff_eq_isUpperSet).
The messages a pragmatic speaker can choose as the prior varies [are exactly the minimal true
ones](##Enguehard2025.exists_prior_iff_minimal), so that weak stability [is Bar-Lev and Katzir's
communicative stability](##Enguehard2025.weaklyStable_iff_isOptimal) and, where some message is
true at every world, strong stability
[is its strict form](##Enguehard2025.stronglyStable_iff_isOptimal).

## Implementation notes

* A world is a valuation `Set ι` of the atoms, as the appendix identifies the cells of the atoms'
  partition with worlds, and a proposition is the Boolean function of the atoms it expresses. The
  atom for `i` is `{I | i ∈ I}`, the Montague lift `Quantifier.individual i` of the name in
  *Ann came to the party*. Upward monotonicity is `IsUpperSet`; the conjunction and the disjunction
  of the atoms in `I` and outside `I` are `Set.Ici I` and `(Set.Iic I)ᶜ`.
* Strong stability is `Question.IsExhaustivelyResolvable` at every world. Weak stability is read
  as printed: a strongest true member, or only atoms among the minimal true members. At a world
  where nothing is true this holds vacuously.
* The statements of (26) assume finitely many worlds, which is stronger than the appendix's
  assumption of finitely many alternatives; the basic form's clause (c) needs some such assumption
  (see TODO).
* The paper compares strong stability with the condition of Fox's 2020 manuscript, that
  exhaustification yield exactly the induced partition rather than contain it. [fox-2018] states
  the same condition, Question Partition Matching, so the comparison runs through `Fox2018.QPM`:
  the monotone propositions over two atoms are strongly stable but [fail
  it](##Enguehard2025.not_qpm_isUpperSet).
* Symmetry is invariance under the permutations of the atoms, the counterpart of
  [keenan-stavi-1986]'s logicality for one argument; projective symmetry is living on a set of
  atoms and being symmetric in them. Bar-Lev and Katzir's result on binary connectives
  ([bar-lev-katzir-2025]) is (34c) at two atoms.
* A clone assigns propositions to every number of atoms, zero included; the paper's clones start
  at one atom, and the results quantify over positive numbers. Both halves of (40) are proved
  without the classification of the maximal clones the paper invokes: conjunction and negation
  express every proposition, and the two constants with any non-monotone function compose to
  negation.
* Optimality in A.3 compares the literal listener's mass at the world,
  `RSA.listener μ (RSA.truthful sem)`, strictly across the true messages with other meanings,
  which is the paper's assumption that no two messages tie; the utility is its logarithm, which
  the comparison drops. A prior is a probability measure giving every world positive mass, and the
  worlds are finitely many, where the paper also allows countably many.

## Errata

* (32b) fails when its condition that the atoms are not dominated is read in `A` alone: [six
  propositions over two atoms](##Enguehard2025.exists_not_isUpperSet_of_bilaterallyStronglyStable),
  among them *if q then p*, are bilaterally strongly stable with neither atom dominated, yet
  *if q then p* is not monotone. The result holds when the negated atoms are not dominated among
  the negations either
  ([repaired](##Enguehard2025.eq_setOf_isUpperSet_of_bilaterallyStronglyStable)).
* (34c) and (37b) need at least two atoms: [*p* and *not
  p*](##Enguehard2025.exists_isSymmetric_not_isUpperSet) over one atom are bilaterally strongly
  stable and symmetric, and *not p*, the negated existential, is not monotone.
* Weak stability as defined holds vacuously at a world where no alternative is true, whereas the
  proof of (40a) assumes that every world has a true and a false alternative, the coverage that
  fn. 23 asks of STA and that A.3 assumes. Under the definition as printed (40a) fails:
  [the falsity-preserving
  functions](##Enguehard2025.exists_isClone_bilaterallyWeaklyStable_not_isUpperSet) form a proper
  clone that contains exclusive disjunction and is bilaterally weakly stable,
  vacuously so where no atom holds. With the coverage the result
  [holds](##Enguehard2025.isUpperSet_of_isClone).

## TODO

* (38) on convex functions.
* The basic form of (26) (c) ⇒ (a) for infinitely many alternatives: the omitted lemma that
  exhaustifying against the non-dominated alternatives changes nothing fails for
  `{[n, ∞] | n} ∪ {{n} | n} ∪ {{0, ∞}}` on `ℕ ∪ {∞}`, where the non-dominated alternatives
  exhaustify to the induced partition but no member is strongest at `∞`.

## References

* [enguehard-2025]
* [bar-lev-katzir-2025]
* [dayal-1996]
* [fox-2007]
* [spector-2016]
* [fox-2018]
* [barwise-cooper-1981]
* [keenan-stavi-1986]
-/

@[expose] public section

namespace Enguehard2025

open Question Exhaustification Set Quantifier

variable {W ι : Type*}

/-! ### Stability -/

/-- A set of alternatives is strongly stable when every world has a strongest true member,
Dayal's condition on answers (STA). -/
def StronglyStable (A : Set (Set W)) : Prop := ∀ w, IsExhaustivelyResolvable A w

/-- (31): bilaterally strongly stable, when the alternatives and their negations are both strongly
stable; for the negations this is the weakest false answer condition (WFA). -/
def BilaterallyStronglyStable (A : Set (Set W)) : Prop :=
  StronglyStable A ∧ StronglyStable (compl '' A)

/-- Weakly stable over the atoms (non-atomic STA): every world has a strongest true member, or
only atoms are minimal among the true members. -/
def WeaklyStable (atoms A : Set (Set W)) : Prop :=
  ∀ w, IsExhaustivelyResolvable A w ∨ ∀ φ, Minimal (· ∈ trueAnswers A w) φ → φ ∈ atoms

/-- Bilaterally weakly stable: the alternatives weakly stable over the atoms, and their negations
over the negated atoms. -/
def BilaterallyWeaklyStable (atoms A : Set (Set W)) : Prop :=
  WeaklyStable atoms A ∧ WeaklyStable (compl '' atoms) (compl '' A)

/-- (25): a member is dominated when the members strictly stronger than it cover it. -/
def Dominated (A : Set (Set W)) (φ : Set W) : Prop := φ ⊆ ⋃₀ {ψ ∈ A | ψ ⊂ φ}

/-- `A*`, the members that are not dominated. -/
def nonDominated (A : Set (Set W)) : Set (Set W) := {φ ∈ A | ¬ Dominated A φ}

theorem StronglyStable.weaklyStable {A : Set (Set W)} (h : StronglyStable A)
    (atoms : Set (Set W)) : WeaklyStable atoms A :=
  fun w ↦ .inl (h w)

/-! ### Strong stability and exhaustification -/

section Dominated

variable {A : Set (Set W)} {φ : Set W} {w : W}

-- dominated members exhaustify to the contradiction
theorem exh_eq_empty_of_dominated (h : Dominated A φ) : exh A φ = ∅ :=
  eq_empty_of_forall_notMem fun _ hw ↦
    let ⟨ψ, ⟨hψ, hψφ⟩, hwψ⟩ := h hw.1
    hψφ.2 (hw.2 ψ hψ hwψ)

theorem mem_nonDominated_of_isStrongestTrueAnswer (h : IsStrongestTrueAnswer A w φ) :
    φ ∈ nonDominated A :=
  ⟨h.1.1, fun hd ↦ let ⟨_, ⟨hψ, hψφ⟩, hwψ⟩ := hd h.1.2; hψφ.2 (h.2 ⟨hψ, hwψ⟩)⟩

-- a non-dominated member of a strongly stable set is the strongest true member somewhere
theorem StronglyStable.exists_isStrongestTrueAnswer (hA : StronglyStable A)
    (hφ : φ ∈ nonDominated A) : ∃ w, IsStrongestTrueAnswer A w φ := by
  obtain ⟨w, hwφ, hw⟩ := not_subset.1 hφ.2
  obtain ⟨p, hp⟩ := hA w
  obtain rfl : p = φ := Classical.byContradiction fun hne ↦
    hw ⟨p, ⟨hp.1.1, (hp.2 ⟨hφ.1, hwφ⟩).ssubset_of_ne hne⟩, hp.1.2⟩
  exact ⟨w, hp⟩

theorem exists_mem_nonDominated_subset [Finite W] {ψ : Set W} (hψ : ψ ∈ A) (hw : w ∈ ψ) :
    ∃ m ∈ nonDominated A, w ∈ m ∧ m ⊆ ψ := by
  obtain ⟨m, hmψ, hm⟩ := exists_minimal_le_of_wellFoundedLT (fun m ↦ m ∈ A ∧ w ∈ m) ψ ⟨hψ, hw⟩
  refine ⟨m, ⟨hm.1.1, fun hd ↦ ?_⟩, hm.1.2, hmψ⟩
  obtain ⟨s, ⟨hs, hsm⟩, hws⟩ := hd hm.1.2
  exact hsm.2 (hm.2 ⟨hs, hws⟩ hsm.1)

-- the appendix's omitted lemma: the dominated members change no exhaustification
theorem exh_nonDominated [Finite W] (φ : Set W) : exh (nonDominated A) φ = exh A φ := by
  refine subset_antisymm (fun w hw ↦ ⟨hw.1, fun ψ hψ hwψ ↦ ?_⟩) (exh_antitone (fun _ h ↦ h.1) φ)
  obtain ⟨m, hm, hwm, hmψ⟩ := exists_mem_nonDominated_subset hψ hwψ
  exact (hw.2 m hm hwm).trans hmψ

theorem isStrongestTrueAnswer_of_nonDominated [Finite W]
    (h : IsStrongestTrueAnswer (nonDominated A) w φ) : IsStrongestTrueAnswer A w φ :=
  ⟨⟨h.1.1.1, h.1.2⟩, fun _ ⟨hψ, hwψ⟩ ↦
    let ⟨_, hm, hwm, hmψ⟩ := exists_mem_nonDominated_subset hψ hwψ
    (h.2 ⟨hm, hwm⟩).trans hmψ⟩

private theorem isStrongestTrueAnswer_of_exhMW_subset [Finite W] {B : Set (Set W)} (hφ : φ ∈ B)
    (hw : w ∈ φ) (h : exhMW B φ ⊆ strongAnswer B w) : IsStrongestTrueAnswer B w φ :=
  ⟨⟨hφ, hw⟩, fun ψ ⟨hψ, hwψ⟩ _ hv ↦
    let ⟨_, hu, huv⟩ := exists_isMinimal_le B φ (toFinite B) hv
    huv ψ hψ ((h hu ψ hψ).1 hwψ)⟩

private theorem exhMW_eq_exh {B : Set (Set W)} (h : (exh B φ).Nonempty) :
    exhMW B φ = exh B φ :=
  subset_antisymm ((exhMW_subset_exhIE B φ).trans (exhIE_eq_exh_of_nonempty _ _ h).subset)
    (exh_subset_exhMW B φ)

end Dominated

/-- (26), with its extension in the appendix: over finitely many worlds the alternatives are
strongly stable iff exhaustifying them yields every cell of the partition they induce, iff
exhaustifying the non-dominated ones yields exactly that partition, whether the exhaustifier is the
basic one, innocent exclusion or minimal worlds. -/
theorem tfae_stronglyStable [Finite W] (A : Set (Set W)) :
    List.TFAE [StronglyStable A,
      (partition A).classes ⊆ exh A '' A,
      exh (nonDominated A) '' nonDominated A = (partition A).classes,
      (partition A).classes ⊆ exhIE A '' A,
      exhIE (nonDominated A) '' nonDominated A = (partition A).classes,
      (partition A).classes ⊆ exhMW A '' A,
      exhMW (nonDominated A) '' nonDominated A = (partition A).classes] := by
  rw [classes_partition]
  have hne : ∀ {B : Set (Set W)} {w p}, IsStrongestTrueAnswer B w p → (exh B p).Nonempty :=
    fun {_ w _} hp ↦ ⟨w, (mem_exh_iff_isStrongestTrueAnswer hp.1.1).2 hp⟩
  have hcell : StronglyStable A → ∀ p ∈ nonDominated A,
      ∃ w, exh (nonDominated A) p = strongAnswer A w := fun h p hp ↦
    let ⟨w, hw⟩ := h.exists_isStrongestTrueAnswer hp
    ⟨w, (exh_nonDominated p).trans (exh_eq_strongAnswer A w hw)⟩
  have h13 : StronglyStable A →
      exh (nonDominated A) '' nonDominated A = range (strongAnswer A) := fun h ↦ by
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨w, hw⟩ := hcell h p hp
      exact ⟨w, hw.symm⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨p, hp⟩ := h w
      exact ⟨p, mem_nonDominated_of_isStrongestTrueAnswer hp,
        (exh_nonDominated p).trans (exh_eq_strongAnswer A w hp)⟩
  have hstar : StronglyStable A → ∀ p ∈ nonDominated A, (exh (nonDominated A) p).Nonempty :=
    fun h p hp ↦ let ⟨w, hw⟩ := hcell h p hp; ⟨w, hw ▸ self_mem_strongAnswer A w⟩
  have hsub : ∀ w, strongAnswer A w ⊆ strongAnswer (nonDominated A) w :=
    fun _ _ hv q hq ↦ hv q hq.1
  tfae_have 1 → 2 := fun h _ ⟨w, hw⟩ ↦
    let ⟨p, hp⟩ := h w; ⟨p, hp.1.1, (exh_eq_strongAnswer A w hp).trans hw⟩
  tfae_have 2 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h ⟨w, rfl⟩
    exact ⟨p, (mem_exh_iff_isStrongestTrueAnswer hp).1 (he ▸ self_mem_strongAnswer A w)⟩
  tfae_have 1 → 3 := h13
  tfae_have 3 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h.ge ⟨w, rfl⟩
    rw [exh_nonDominated] at he
    exact ⟨p, (mem_exh_iff_isStrongestTrueAnswer hp.1).1 (he ▸ self_mem_strongAnswer A w)⟩
  tfae_have 1 → 4 := fun h _ ⟨w, hw⟩ ↦ by
    obtain ⟨p, hp⟩ := h w
    exact ⟨p, hp.1.1, (exhIE_eq_exh_of_nonempty _ _ (hne hp)).trans
      ((exh_eq_strongAnswer A w hp).trans hw)⟩
  tfae_have 4 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h ⟨w, rfl⟩
    exact ⟨p, isStrongestTrueAnswer_of_exhMW_subset hp
      (exhIE_subset A p (he ▸ self_mem_strongAnswer A w)) ((exhMW_subset_exhIE A p).trans he.le)⟩
  tfae_have 1 → 5 := fun h ↦
    (image_congr fun p hp ↦ exhIE_eq_exh_of_nonempty _ _ (hstar h p hp)).trans (h13 h)
  tfae_have 5 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h.ge ⟨w, rfl⟩
    have hw : w ∈ p := exhIE_subset _ p (he ▸ self_mem_strongAnswer A w)
    exact ⟨p, isStrongestTrueAnswer_of_nonDominated (isStrongestTrueAnswer_of_exhMW_subset hp hw
      (((exhMW_subset_exhIE _ p).trans he.le).trans (hsub w)))⟩
  tfae_have 1 → 6 := fun h _ ⟨w, hw⟩ ↦ by
    obtain ⟨p, hp⟩ := h w
    exact ⟨p, hp.1.1, (exhMW_eq_exh (hne hp)).trans ((exh_eq_strongAnswer A w hp).trans hw)⟩
  tfae_have 6 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h ⟨w, rfl⟩
    exact ⟨p, isStrongestTrueAnswer_of_exhMW_subset hp
      (exhMW_subset A p (he ▸ self_mem_strongAnswer A w)) he.le⟩
  tfae_have 1 → 7 := fun h ↦
    (image_congr fun p hp ↦ exhMW_eq_exh (hstar h p hp)).trans (h13 h)
  tfae_have 7 → 1 := fun h w ↦ by
    obtain ⟨p, hp, he⟩ := h.ge ⟨w, rfl⟩
    have hw : w ∈ p := exhMW_subset _ p (he ▸ self_mem_strongAnswer A w)
    exact ⟨p, isStrongestTrueAnswer_of_nonDominated
      (isStrongestTrueAnswer_of_exhMW_subset hp hw (he.le.trans (hsub w)))⟩
  tfae_finish

-- (23a): `{p, q}` has no strongest true member where both atoms hold
theorem not_stronglyStable_pair :
    ¬ StronglyStable ({{I | 0 ∈ I}, {I | 1 ∈ I}} : Set (Set (Set (Fin 2)))) := by
  intro h
  obtain ⟨φ, ⟨hφ, -⟩, hmin⟩ := h univ
  rcases hφ with rfl | rfl
  · exact absurd (hmin ⟨Or.inr rfl, mem_univ 1⟩ (show ({0} : Set (Fin 2)) ∈ {I | 0 ∈ I} from rfl))
      (by simp)
  · exact absurd (hmin ⟨Or.inl rfl, mem_univ 0⟩ (show ({1} : Set (Fin 2)) ∈ {I | 1 ∈ I} from rfl))
      (by simp)

-- (27): the upward-monotone propositions are bilaterally strongly stable, `Ici w` the strongest
-- true and `(Iic w)ᶜ` the weakest false one at `w`
theorem bilaterallyStronglyStable_isUpperSet {P : Type*} [Preorder P] :
    BilaterallyStronglyStable {φ : Set P | IsUpperSet φ} := by
  refine ⟨fun w ↦ ⟨Ici w, ⟨isUpperSet_Ici w, mem_Ici.2 le_rfl⟩, fun φ ⟨hφ, hw⟩ v hv ↦ hφ hv hw⟩,
    fun w ↦ ⟨(Iic w)ᶜᶜ, ⟨⟨(Iic w)ᶜ, (isLowerSet_Iic w).compl, rfl⟩, by simp⟩, ?_⟩⟩
  rintro _ ⟨⟨φ, hφ, rfl⟩, hw⟩ v hv
  simp only [compl_compl, mem_Iic] at hv
  exact fun hvφ ↦ hw (hφ hv hvφ)

-- fn. 24: the monotone propositions over two atoms fail [fox-2018]'s matching condition, since the
-- dominated `p ∨ q` exhaustifies to no cell
theorem not_qpm_isUpperSet :
    ¬ Fox2018.QPM (exh {φ : Set (Set (Fin 2)) | IsUpperSet φ}) {φ | IsUpperSet φ} univ := by
  have hup : ∀ i : Fin 2, IsUpperSet {I : Set (Fin 2) | i ∈ I} := fun _ _ _ hIJ h ↦ hIJ h
  exact fun h ↦ Fox2018.not_nonVacuity_exh_of_union (H := {φ | IsUpperSet φ})
    (q₁ := {I | 0 ∈ I}) (q₂ := {I | 1 ∈ I}) (hup 0) (hup 1) ((hup 0).union (hup 1))
    (fun h ↦ by simpa using h (show ({0} : Set (Fin 2)) ∈ {I | 0 ∈ I} from rfl))
    (fun h ↦ by simpa using h (show ({1} : Set (Fin 2)) ∈ {I | 1 ∈ I} from rfl)) h.2

/-! ### Two atoms -/

section Atoms

variable {A : Set (Set (Set ι))}

-- (32a): the conjunction of all atoms, at two atoms `∧`
theorem Ici_univ_mem_of_stronglyStable (hat : ∀ i, {I | i ∈ I} ∈ A) (h : StronglyStable A) :
    Ici univ ∈ A := by
  obtain ⟨σ, ⟨hσ, hu⟩, hmin⟩ := h univ
  convert hσ using 1
  exact subset_antisymm (fun I hI ↦ univ_subset_iff.1 (mem_Ici.1 hI) ▸ hu)
    fun I hI ↦ mem_Ici.2 fun i _ ↦ hmin ⟨hat i, mem_univ i⟩ hI

-- (32a): the disjunction of all atoms, at two atoms `∨`
theorem compl_Iic_empty_mem_of_stronglyStable (hat : ∀ i, {I | i ∈ I} ∈ A)
    (h : StronglyStable (compl '' A)) : (Iic ∅)ᶜ ∈ A := by
  obtain ⟨_, ⟨⟨χ, hχ, rfl⟩, h0⟩, hmin⟩ := h ∅
  convert hχ using 1
  refine subset_antisymm (fun I hI ↦ ?_) fun I hI hI0 ↦ h0 (subset_empty_iff.1 hI0 ▸ hI)
  obtain ⟨i, hi, -⟩ := not_subset.1 (show ¬ I ⊆ ∅ from hI)
  by_contra hIχ
  exact hmin ⟨⟨_, hat i, rfl⟩, notMem_empty i⟩ hIχ hi

private theorem Ici_mem (hat : ∀ i, {I | i ∈ I} ∈ A) (hup : ∀ φ ∈ A, IsUpperSet φ)
    (h : StronglyStable A) (I : Set ι) : Ici I ∈ A := by
  obtain ⟨σ, ⟨hσ, hIσ⟩, hmin⟩ := h I
  convert hσ using 1
  exact subset_antisymm (fun J hJ ↦ hup σ hσ hJ hIσ)
    fun J hJ ↦ mem_Ici.2 fun i hi ↦ hmin ⟨hat i, hi⟩ hJ

private theorem compl_Iic_mem (hat : ∀ i, {I | i ∈ I} ∈ A) (hup : ∀ φ ∈ A, IsUpperSet φ)
    (h : StronglyStable (compl '' A)) (I : Set ι) : (Iic I)ᶜ ∈ A := by
  obtain ⟨_, ⟨⟨χ, hχ, rfl⟩, hIχ⟩, hmin⟩ := h I
  convert hχ using 1
  refine subset_antisymm (fun J hJ ↦ ?_) fun J hJ hJI ↦ hIχ (hup χ hχ hJI hJ)
  obtain ⟨j, hjJ, hjI⟩ := not_subset.1 (show ¬ J ⊆ I from hJ)
  by_contra hJχ
  exact hmin ⟨⟨_, hat j, rfl⟩, hjI⟩ hJχ hjJ

-- a non-dominated atom is the strongest true member at its singleton
private theorem atom_subset_of_singleton_mem (hat : ∀ i, {I | i ∈ I} ∈ A) (h : StronglyStable A)
    {i : ι} (hdom : ¬ Dominated A {I | i ∈ I}) {ψ : Set (Set ι)} (hψ : ψ ∈ A) (hi : {i} ∈ ψ) :
    {I | i ∈ I} ⊆ ψ := by
  obtain ⟨w, hw⟩ := h.exists_isStrongestTrueAnswer ⟨hat i, hdom⟩
  obtain rfl : w = {i} := eq_singleton_iff_unique_mem.2 ⟨hw.1.2, fun j hj ↦ by
    simpa using hw.2 ⟨hat j, hj⟩ (show {i} ∈ {I | i ∈ I} from rfl)⟩
  exact hw.2 ⟨hψ, hi⟩

-- dually, a negated atom non-dominated among the negations is the weakest false member at the
-- complement of its singleton
private theorem subset_atom_of_compl_singleton_notMem (hat : ∀ i, {I | i ∈ I} ∈ A)
    (h : StronglyStable (compl '' A)) {i : ι} (hdom : ¬ Dominated (compl '' A) {I | i ∈ I}ᶜ)
    {χ : Set (Set ι)} (hχ : χ ∈ A) (hi : {i}ᶜ ∉ χ) : χ ⊆ {I | i ∈ I} := by
  obtain ⟨w, hw⟩ := h.exists_isStrongestTrueAnswer ⟨⟨_, hat i, rfl⟩, hdom⟩
  obtain rfl : w = {i}ᶜ := by
    ext j
    refine ⟨fun hj hji ↦ hw.1.2 (hji ▸ hj), fun hj ↦ by_contra fun hjw ↦ ?_⟩
    have := hw.2 ⟨⟨_, hat j, rfl⟩, hjw⟩ (show {j} ∈ {I | i ∈ I}ᶜ by simpa [eq_comm] using hj)
    simp at this
  exact fun I hI ↦ by_contra fun hIi ↦ hw.2 ⟨⟨χ, hχ, rfl⟩, hi⟩ hIi hI

end Atoms

private theorem fin_two_cases (I : Set (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = univ := by
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
  · exact .inr <| .inr <| .inr <| eq_univ_of_forall fun x ↦ by fin_cases x <;> assumption
  · exact .inr <| .inl <| ext fun x ↦ by fin_cases x <;> simp [h0, h1]
  · exact .inr <| .inr <| .inl <| ext fun x ↦ by fin_cases x <;> simp [h0, h1]
  · exact .inl <| ext fun x ↦ by fin_cases x <;> simp [h0, h1]

private theorem isUpperSet_fin_two {φ : Set (Set (Fin 2))} (hφ : IsUpperSet φ) :
    ∃ I, φ = Ici I ∨ φ = (Iic I)ᶜ := by
  have hu : ∀ {I}, I ∈ φ → univ ∈ φ := fun h ↦ hφ (subset_univ _) h
  by_cases hE : ∅ ∈ φ
  · exact ⟨∅, .inl <| ext fun J ↦ by simpa using hφ (empty_subset J) hE⟩
  by_cases h0 : ({0} : Set (Fin 2)) ∈ φ <;> by_cases h1 : ({1} : Set (Fin 2)) ∈ φ
  · refine ⟨∅, .inr <| ext fun J ↦ ?_⟩
    rcases fin_two_cases J with rfl | rfl | rfl | rfl <;> simp [hE, h0, h1, hu h0]
  · refine ⟨{0}, .inl <| ext fun J ↦ ?_⟩
    rcases fin_two_cases J with rfl | rfl | rfl | rfl <;> simp [hE, h0, h1, hu h0]
  · refine ⟨{1}, .inl <| ext fun J ↦ ?_⟩
    rcases fin_two_cases J with rfl | rfl | rfl | rfl <;> simp [hE, h0, h1, hu h1]
  · by_cases hU : univ ∈ φ
    · refine ⟨univ, .inl <| ext fun J ↦ ?_⟩
      rcases fin_two_cases J with rfl | rfl | rfl | rfl <;> simp [hE, h0, h1, hU]
    · refine ⟨univ, .inr <| ext fun J ↦ ?_⟩
      rcases fin_two_cases J with rfl | rfl | rfl | rfl <;> simp [hE, h0, h1, hU]

-- (32b), with the negated atoms also not dominated among the negations (Errata)
theorem eq_setOf_isUpperSet_of_bilaterallyStronglyStable {A : Set (Set (Set (Fin 2)))}
    (hat : ∀ i, {I | i ∈ I} ∈ A) (h : BilaterallyStronglyStable A)
    (hdom : ∀ i, ¬ Dominated A {I | i ∈ I})
    (hdom' : ∀ i, ¬ Dominated (compl '' A) {I | i ∈ I}ᶜ) : A = {φ | IsUpperSet φ} := by
  have hS : ∀ i, ∀ ψ ∈ A, {i} ∈ ψ → {I | i ∈ I} ⊆ ψ := fun i _ hψ hi ↦
    atom_subset_of_singleton_mem hat h.1 (hdom i) hψ hi
  have hF : ∀ i, ∀ χ ∈ A, {i}ᶜ ∉ χ → χ ⊆ {I | i ∈ I} := fun i _ hχ hi ↦
    subset_atom_of_compl_singleton_notMem hat h.2 (hdom' i) hχ hi
  have hc0 : ({0}ᶜ : Set (Fin 2)) = {1} := ext fun x ↦ by fin_cases x <;> simp
  have hc1 : ({1}ᶜ : Set (Fin 2)) = {0} := ext fun x ↦ by fin_cases x <;> simp
  have hup : ∀ φ ∈ A, IsUpperSet φ := by
    intro φ hφ I J hIJ hI
    have h01 : ∅ ∈ φ → ({0} : Set (Fin 2)) ∈ φ ∧ ({1} : Set (Fin 2)) ∈ φ := fun h0 ↦
      ⟨hc1 ▸ by_contra fun h ↦ notMem_empty 1 (hF 1 φ hφ h h0),
        hc0 ▸ by_contra fun h ↦ notMem_empty 0 (hF 0 φ hφ h h0)⟩
    rcases fin_two_cases I with rfl | rfl | rfl | rfl
    · rcases fin_two_cases J with rfl | rfl | rfl | rfl
      · exact hI
      · exact (h01 hI).1
      · exact (h01 hI).2
      · exact hS 0 φ hφ (h01 hI).1 (mem_univ 0)
    · exact hS 0 φ hφ hI (hIJ rfl)
    · exact hS 1 φ hφ hI (hIJ rfl)
    · exact univ_subset_iff.1 hIJ ▸ hI
  refine subset_antisymm hup fun φ hφ ↦ ?_
  obtain ⟨I, rfl | rfl⟩ := isUpperSet_fin_two hφ
  exacts [Ici_mem hat hup h.1 I, compl_Iic_mem hat hup h.2 I]

-- (32b) as printed: neither atom is dominated, yet *if q then p* is not monotone (Errata)
theorem exists_not_isUpperSet_of_bilaterallyStronglyStable :
    ∃ A : Set (Set (Set (Fin 2))), (∀ i, {I | i ∈ I} ∈ A) ∧ BilaterallyStronglyStable A ∧
      (∀ i, ¬ Dominated A {I | i ∈ I}) ∧ ∃ φ ∈ A, ¬ IsUpperSet φ := by
  refine ⟨{{I | 0 ∈ I}, {I | 1 ∈ I}, {I | 0 ∈ I} ∩ {I | 1 ∈ I}, {I | 0 ∈ I} ∪ {I | 1 ∈ I}, ∅,
    {I | 1 ∈ I}ᶜ ∪ {I | 0 ∈ I}}, fun i ↦ by fin_cases i <;> simp, ⟨fun w ↦ ?_, fun w ↦ ?_⟩,
    fun i hd ↦ ?_, {I | 1 ∈ I}ᶜ ∪ {I | 0 ∈ I}, by simp, fun h ↦ ?_⟩
  · by_cases h0 : (0 : Fin 2) ∈ w <;> by_cases h1 : (1 : Fin 2) ∈ w
    · refine ⟨{I | 0 ∈ I} ∩ {I | 1 ∈ I}, ⟨by simp, h0, h1⟩, ?_⟩
      rintro ψ ⟨hψ, hw⟩ v ⟨hv0, hv1⟩
      rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨{I | 0 ∈ I}, ⟨by simp, h0⟩, ?_⟩
      rintro ψ ⟨hψ, hw⟩ v hv
      rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨{I | 1 ∈ I}, ⟨by simp, h1⟩, ?_⟩
      rintro ψ ⟨hψ, hw⟩ v hv
      rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨{I | 1 ∈ I}ᶜ ∪ {I | 0 ∈ I}, ⟨by simp, Or.inl h1⟩, ?_⟩
      rintro ψ ⟨hψ, hw⟩ v hv
      rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · by_cases h0 : (0 : Fin 2) ∈ w <;> by_cases h1 : (1 : Fin 2) ∈ w
    · refine ⟨∅ᶜ, ⟨⟨∅, by simp, rfl⟩, notMem_empty w⟩, ?_⟩
      rintro _ ⟨⟨χ, hχ, rfl⟩, hw⟩ v -
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨{I | 1 ∈ I}ᶜ, ⟨⟨_, by simp, rfl⟩, h1⟩, ?_⟩
      rintro _ ⟨⟨χ, hχ, rfl⟩, hw⟩ v hv
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨({I | 1 ∈ I}ᶜ ∪ {I | 0 ∈ I})ᶜ, ⟨⟨_, by simp, rfl⟩, by simp [h0, h1]⟩, ?_⟩
      rintro _ ⟨⟨χ, hχ, rfl⟩, hw⟩ v hv
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · refine ⟨({I | 0 ∈ I} ∪ {I | 1 ∈ I})ᶜ, ⟨⟨_, by simp, rfl⟩, by simp [h0, h1]⟩, ?_⟩
      rintro _ ⟨⟨χ, hχ, rfl⟩, hw⟩ v hv
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · have hne := exh_eq_empty_of_dominated hd
    refine (eq_empty_iff_forall_notMem.1 hne {i}) ⟨rfl, fun q hq hiq ↦ ?_⟩
    fin_cases i <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · have := h (show (∅ : Set (Fin 2)) ≤ {1} from empty_subset _) (Or.inl (by simp))
    simp at this

/-! ### Symmetric functions -/

/-- (33): a proposition is symmetric when it is invariant under the permutations of the atoms. -/
def IsSymmetric (φ : Set (Set ι)) : Prop := ∀ (σ : Equiv.Perm ι) (I : Set ι), σ ⁻¹' I ∈ φ ↔ I ∈ φ

section Symmetric

variable {φ : Set (Set ι)}

-- a symmetric proposition that one atom entails holds wherever some atom holds
theorem IsSymmetric.mem_of_subset (hφ : IsSymmetric φ) {i j : ι} (h : {I | i ∈ I} ⊆ φ)
    {J : Set ι} (hj : j ∈ J) : J ∈ φ := by
  classical
  exact (hφ (Equiv.swap i j) J).1 (h (by simpa using hj))

-- a symmetric proposition true at a world where some atom fails entails no atom
theorem IsSymmetric.not_subset (hφ : IsSymmetric φ) {I : Set ι} (hI : I ∈ φ) (a : ι) {b : ι}
    (hb : b ∉ I) : ¬ φ ⊆ {J | a ∈ J} := by
  classical
  exact fun h ↦ hb (by simpa using h ((hφ (Equiv.swap a b) I).2 hI))

theorem IsSymmetric.compl (hφ : IsSymmetric φ) : IsSymmetric φᶜ := fun σ I ↦ not_congr (hφ σ I)

theorem IsSymmetric.union {ψ : Set (Set ι)} (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) :
    IsSymmetric (φ ∪ ψ) := fun σ I ↦ or_congr (hφ σ I) (hψ σ I)

theorem isSymmetric_singleton_empty : IsSymmetric ({∅} : Set (Set ι)) := fun σ _ ↦
  (preimage_injective.2 σ.surjective).eq_iff' preimage_empty

theorem isSymmetric_singleton_univ : IsSymmetric ({univ} : Set (Set ι)) := fun σ _ ↦
  (preimage_injective.2 σ.surjective).eq_iff' preimage_univ

end Symmetric

private theorem setOf_every_univ : {B : Set ι | Det.every univ B} = {univ} :=
  ext fun _ ↦ univ_subset_iff

private theorem setOf_no_univ : {B : Set ι | Det.no univ B} = {∅} :=
  ext fun B ↦ by simp [Det.no, univ_subset_iff]

private theorem setOf_some_univ : {B : Set ι | Det.some univ B} = {∅}ᶜ :=
  ext fun B ↦ by simp [Det.some, nonempty_iff_ne_empty]

section Corners

variable {A : Set (Set (Set ι))}

-- (34a): with three atoms or more, no strongest member where exactly two hold
theorem not_stronglyStable_of_isSymmetric [Finite ι] (h3 : 2 < Nat.card ι)
    (hat : ∀ i, {I | i ∈ I} ∈ A)
    (hsym : ∀ φ ∈ A, φ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) → IsSymmetric φ) :
    ¬ StronglyStable A := by
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card] at h3
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  intro h
  obtain ⟨σ, ⟨hσ, hI⟩, hmin⟩ := h {a, b}
  have hσa : σ ⊆ {I | a ∈ I} := hmin ⟨hat a, by simp⟩
  have hσb : σ ⊆ {I | b ∈ I} := hmin ⟨hat b, by simp⟩
  have hna : σ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) := by
    rintro ⟨k, rfl⟩
    have ha : a ∈ ({k} : Set ι) := hσa rfl
    have hb : b ∈ ({k} : Set ι) := hσb rfl
    exact hab (ha.trans hb.symm)
  exact (hsym σ hσ hna).not_subset hI a (show c ∉ ({a, b} : Set ι) by
    simp [hac.symm, hbc.symm]) hσa

-- (34b): only the universal, the existential, the negated existential and the disjunction of the
-- first and the last survive
theorem mem_corners_of_weaklyStable [Finite ι] (hat : ∀ i, {I | i ∈ I} ∈ A)
    (hsym : ∀ φ ∈ A, φ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) → IsSymmetric φ)
    (h : WeaklyStable (range fun i ↦ {I : Set ι | i ∈ I}) A) {φ : Set (Set ι)} (hφ : φ ∈ A)
    (hφa : φ ∉ range fun i ↦ {I : Set ι | i ∈ I}) :
    φ ∈ ({∅, univ, {B | Det.every univ B}, {B | Det.some univ B}, {B | Det.no univ B},
      {B | Det.every univ B} ∪ {B | Det.no univ B}} : Set (Set (Set ι))) := by
  -- true where some but not all atoms hold, `φ` holds wherever some atom does
  have hmid : ∀ I ∈ φ, I.Nonempty → I ≠ univ → ∀ J : Set ι, J.Nonempty → J ∈ φ := by
    intro I hI ⟨a, ha⟩ hIu J ⟨j, hj⟩
    by_contra hJ
    have hna : ∀ k, ¬ {I | k ∈ I} ⊆ φ := fun k hk ↦ hJ ((hsym φ hφ hφa).mem_of_subset hk hj)
    obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem I).1 hIu
    obtain ⟨ψ, hψφ, hψ⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ trueAnswers A I) φ ⟨hφ, hI⟩
    rcases h I with ⟨σ, hσ, hmin⟩ | hat'
    · have hσφ : σ ⊆ φ := hmin ⟨hφ, hI⟩
      have hσa : σ ∉ range fun i ↦ {I : Set ι | i ∈ I} := by
        rintro ⟨k, rfl⟩
        exact hna k hσφ
      exact (hsym σ hσ.1 hσa).not_subset hσ.2 a hb (hmin ⟨hat a, ha⟩)
    · obtain ⟨k, rfl⟩ := hat' ψ hψ
      exact hna k hψφ
  simp only [setOf_every_univ, setOf_some_univ, setOf_no_univ, mem_insert_iff, mem_singleton_iff]
  by_cases hm : ∃ I ∈ φ, I.Nonempty ∧ I ≠ univ
  · obtain ⟨I, hI, hne, hu⟩ := hm
    by_cases h0 : ∅ ∈ φ
    · exact .inr <| .inl <| eq_univ_of_forall fun J ↦
        J.eq_empty_or_nonempty.elim (fun hJ ↦ hJ ▸ h0) (hmid I hI hne hu J)
    · refine .inr <| .inr <| .inr <| .inl <| ext fun J ↦ ⟨fun hJ hJ0 ↦ h0 (hJ0 ▸ hJ), fun hJ ↦ ?_⟩
      exact hmid I hI hne hu J (nonempty_iff_ne_empty.2 hJ)
  · push Not at hm
    have hsub : φ ⊆ {∅, univ} := fun I hI ↦
      I.eq_empty_or_nonempty.elim .inl fun hne ↦ .inr (hm I hI hne)
    rcases subset_pair_iff_eq.1 hsub with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    · exact .inr <| .inr <| .inl rfl
    · exact .inr <| .inr <| .inr <| .inr <| .inr <| (insert_eq _ _).trans (union_comm _ _)

/-- (34c): over the atoms and symmetric functions of them, if the alternatives and their negations
are weakly stable, then besides the atoms only the contradiction, the tautology, *every* and *some*
over the atoms remain: the corners of the square of opposition other than *no* and the missing
O-corner. At two atoms this is [bar-lev-katzir-2025]'s result on binary connectives. -/
theorem mem_every_some_of_bilaterallyWeaklyStable [Finite ι] [Nontrivial ι]
    (hat : ∀ i, {I | i ∈ I} ∈ A)
    (hsym : ∀ φ ∈ A, φ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) → IsSymmetric φ)
    (h : BilaterallyWeaklyStable (range fun i ↦ {I : Set ι | i ∈ I}) A) {φ : Set (Set ι)}
    (hφ : φ ∈ A) (hφa : φ ∉ range fun i ↦ {I : Set ι | i ∈ I}) :
    φ ∈ ({∅, univ, {B | Det.every univ B}, {B | Det.some univ B}} : Set (Set (Set ι))) := by
  -- a member true where no atom holds is true wherever exactly one atom fails
  have hco : ∀ χ ∈ A, ∅ ∈ χ → ∀ i : ι, {i}ᶜ ∈ χ := by
    intro χ hχ h0 i
    by_contra hiχ
    obtain ⟨ψ, hψχ, hψ⟩ := exists_minimal_le_of_wellFoundedLT
      (· ∈ trueAnswers (compl '' A) {i}ᶜ) χᶜ ⟨⟨χ, hχ, rfl⟩, hiχ⟩
    rcases h.2 {i}ᶜ with ⟨_, ⟨⟨θ, hθ, rfl⟩, hiθ⟩, hmin⟩ | hat'
    · have hχθ : χ ⊆ θ := fun I hI ↦ by_contra fun hIθ ↦ hmin ⟨⟨χ, hχ, rfl⟩, hiχ⟩ hIθ hI
      have hiθ' : {I | i ∈ I} ⊆ θ := fun I hI ↦ by_contra fun hIθ ↦
        hmin ⟨⟨_, hat i, rfl⟩, by simp⟩ hIθ hI
      have hθa : θ ∉ range fun i ↦ {I : Set ι | i ∈ I} := by
        rintro ⟨k, rfl⟩
        exact notMem_empty k (hχθ h0)
      obtain ⟨j, hj⟩ := exists_ne i
      exact hiθ ((hsym θ hθ hθa).mem_of_subset hiθ' (mem_compl_singleton_iff.2 hj))
    · obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hat' ψ hψ
      exact hψχ (show ∅ ∈ {I | k ∈ I}ᶜ from notMem_empty k) h0
  have h6 := mem_corners_of_weaklyStable hat hsym h.1 hφ hφa
  simp only [setOf_every_univ, setOf_some_univ, setOf_no_univ, mem_insert_iff,
    mem_singleton_iff] at h6 ⊢
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have hj : j ∈ ({i}ᶜ : Set ι) := hij.symm
  rcases h6 with h6 | h6 | h6 | h6 | rfl | rfl
  · exact .inl h6
  · exact .inr (.inl h6)
  · exact .inr (.inr (.inl h6))
  · exact .inr (.inr (.inr h6))
  · exact absurd ((mem_singleton_iff.1 (hco _ hφ rfl i)) ▸ hj) (notMem_empty j)
  · rcases hco _ hφ (.inr rfl) i with h | h
    · exact absurd ((mem_singleton_iff.1 h).symm ▸ mem_univ i) (by simp)
    · exact absurd ((mem_singleton_iff.1 h) ▸ hj) (notMem_empty j)

-- the atoms with any of the contradiction, the tautology and the corners other than the O-corner
-- are weakly stable, as long as the tautology and *every* are among them
private theorem weaklyStable_corners [Nontrivial ι]
    (hA : A ⊆ range (fun i ↦ {I : Set ι | i ∈ I}) ∪
      {∅, univ, {B | Det.every univ B}, {B | Det.some univ B}, {B | Det.no univ B}})
    (hat : ∀ i, {I | i ∈ I} ∈ A) (hu : univ ∈ A) (he : {B | Det.every univ B} ∈ A) :
    WeaklyStable (range fun i ↦ {I : Set ι | i ∈ I}) A := by
  simp only [setOf_every_univ, setOf_some_univ, setOf_no_univ] at hA he
  intro w
  rcases w.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · by_cases hN : ({∅} : Set (Set ι)) ∈ A
    · exact .inl ⟨{∅}, ⟨hN, rfl⟩, fun ψ ⟨_, h0⟩ I hI ↦ (mem_singleton_iff.1 hI) ▸ h0⟩
    refine .inl ⟨univ, ⟨hu, mem_univ _⟩, fun ψ ⟨hψ, h0⟩ ↦ ?_⟩
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    rcases hA hψ with ⟨k, rfl⟩ | rfl | rfl | rfl | rfl | rfl
    · exact absurd h0 (notMem_empty k)
    · exact absurd h0 (notMem_empty _)
    · exact subset_rfl
    · exact absurd (mem_singleton_iff.1 h0 ▸ mem_univ i) (notMem_empty i)
    · exact absurd h0 (by simp)
    · exact absurd hψ hN
  by_cases hw : w = univ
  · subst hw
    exact .inl ⟨{univ}, ⟨he, rfl⟩, fun ψ ⟨_, hu⟩ I hI ↦ (mem_singleton_iff.1 hI) ▸ hu⟩
  refine .inr fun m ⟨⟨hm, hwm⟩, hmin⟩ ↦ ?_
  obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem w).1 hw
  have hab : b ≠ a := fun h ↦ hb (h ▸ ha)
  rcases hA hm with hm' | rfl | rfl | rfl | rfl | rfl
  · exact hm'
  · exact absurd hwm (notMem_empty w)
  · exact absurd (hmin ⟨hat a, ha⟩ (subset_univ _) (mem_univ ∅)) (notMem_empty a)
  · exact absurd (mem_singleton_iff.1 hwm) hw
  · have := hmin ⟨hat a, ha⟩ (fun I hI hI0 ↦ by simp_all) (show {b} ∈ ({∅}ᶜ : Set (Set ι)) by simp)
    exact absurd (mem_singleton_iff.1 this) hab.symm
  · exact absurd (mem_singleton_iff.1 hwm) (nonempty_iff_ne_empty.1 ⟨a, ha⟩)

-- the paper's verification for (34c): the atoms, the contradiction, the tautology, *every* and
-- *some* are bilaterally weakly stable
theorem bilaterallyWeaklyStable_every_some [Nontrivial ι] :
    BilaterallyWeaklyStable (range fun i ↦ {I : Set ι | i ∈ I})
      (range (fun i ↦ {I : Set ι | i ∈ I}) ∪
        {∅, univ, {B | Det.every univ B}, {B | Det.some univ B}}) := by
  refine ⟨weaklyStable_corners (union_subset_union_right _ (by simp [insert_subset_iff]))
    (fun i ↦ .inl ⟨i, rfl⟩) (by simp) (by simp), fun w ↦ ?_⟩
  simp only [setOf_every_univ, setOf_some_univ]
  rcases w.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · refine .inl ⟨{∅}, ⟨⟨{∅}ᶜ, by simp, compl_compl _⟩, rfl⟩, fun _ ⟨_, h0⟩ I hI ↦ ?_⟩
    exact (mem_singleton_iff.1 hI) ▸ h0
  by_cases hw : w = univ
  · subst hw
    refine .inl ⟨univ, ⟨⟨∅, by simp, compl_empty⟩, mem_univ _⟩, ?_⟩
    rintro _ ⟨⟨χ, hχ, rfl⟩, huχ⟩ I -
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    rcases hχ with ⟨k, rfl⟩ | rfl | rfl | rfl | rfl <;> simp_all
  refine .inr fun m ⟨⟨⟨χ, hχ, hm⟩, hwm⟩, hmin⟩ ↦ ?_
  subst hm
  obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem w).1 hw
  obtain ⟨c, hc⟩ := exists_ne b
  have hbc : ({b} : Set ι) ≠ univ := fun h ↦ hc (mem_singleton_iff.1 (h ▸ mem_univ c))
  rcases hχ with ⟨k, rfl⟩ | rfl | rfl | rfl | rfl
  · exact ⟨_, ⟨k, rfl⟩, rfl⟩
  · have := hmin ⟨⟨_, .inl ⟨b, rfl⟩, rfl⟩, hb⟩ (fun I _ ↦ notMem_empty I)
      (show univ ∈ (∅ : Set (Set ι))ᶜ from notMem_empty _)
    exact absurd this (by simp)
  · exact absurd hwm (by simp)
  · have := hmin ⟨⟨_, .inl ⟨b, rfl⟩, rfl⟩, hb⟩ (fun I hI hIu ↦ hI ((mem_singleton_iff.1 hIu) ▸
      mem_univ b)) (show {b} ∈ ({univ}ᶜ : Set (Set ι)) from hbc)
    exact absurd this (by simp)
  · exact absurd hwm (by simpa using nonempty_iff_ne_empty.1 ⟨a, ha⟩)

-- (34b) against (34c): *nobody* keeps the alternatives weakly stable but not their negations
theorem weaklyStable_and_not_bilaterallyWeaklyStable_no [Finite ι] [Nontrivial ι] :
    WeaklyStable (range fun i ↦ {I : Set ι | i ∈ I}) (range (fun i ↦ {I : Set ι | i ∈ I}) ∪
        {∅, univ, {B | Det.every univ B}, {B | Det.some univ B}, {B | Det.no univ B}}) ∧
      ¬ BilaterallyWeaklyStable (range fun i ↦ {I : Set ι | i ∈ I})
        (range (fun i ↦ {I : Set ι | i ∈ I}) ∪
          {∅, univ, {B | Det.every univ B}, {B | Det.some univ B}, {B | Det.no univ B}}) := by
  refine ⟨weaklyStable_corners subset_rfl (fun i ↦ .inl ⟨i, rfl⟩) (by simp) (by simp), fun h ↦ ?_⟩
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hsym : ∀ φ ∈ range (fun i ↦ {I : Set ι | i ∈ I}) ∪
      {∅, univ, {B | Det.every univ B}, {B | Det.some univ B}, {B | Det.no univ B}},
      φ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) → IsSymmetric φ := by
    simp only [setOf_every_univ, setOf_some_univ, setOf_no_univ]
    rintro φ (hφ | rfl | rfl | rfl | rfl | rfl) hφa
    · exact absurd hφ hφa
    · exact fun _ _ ↦ Iff.rfl
    · exact fun _ _ ↦ Iff.rfl
    · exact isSymmetric_singleton_univ
    · exact isSymmetric_singleton_empty.compl
    · exact isSymmetric_singleton_empty
  have hN := mem_every_some_of_bilaterallyWeaklyStable (fun i ↦ .inl ⟨i, rfl⟩) hsym h
    (φ := {B | Det.no univ B}) (by simp) (by
      rintro ⟨k, hk⟩
      simpa [setOf_no_univ] using (congrArg (∅ ∈ ·) hk))
  simp only [setOf_every_univ, setOf_some_univ, setOf_no_univ, mem_insert_iff,
    mem_singleton_iff] at hN
  have hu0 : (univ : Set ι) ≠ ∅ := nonempty_iff_ne_empty.1 ⟨i, mem_univ i⟩
  rcases hN with h | h | h | h
  · simpa using congrArg (∅ ∈ ·) h
  · simpa [hu0] using congrArg (univ ∈ ·) h
  · simpa [hu0.symm] using congrArg (∅ ∈ ·) h
  · simpa using congrArg (∅ ∈ ·) h

-- p. 714: the disjunction of the universal and the negated existential is dominated only because
-- the negated existential is an alternative too; without it, beside the atoms and the universal,
-- it is not dominated
theorem exists_not_dominated_every_union_no [Nonempty ι] :
    ∃ A : Set (Set (Set ι)), (∀ i, {I | i ∈ I} ∈ A) ∧
      (∀ φ ∈ A, φ ∉ range (fun i ↦ {I : Set ι | i ∈ I}) → IsSymmetric φ) ∧
      WeaklyStable (range fun i ↦ {I : Set ι | i ∈ I}) A ∧
      {B | Det.every univ B} ∪ {B | Det.no univ B} ∈ A ∧
      ¬ Dominated A ({B | Det.every univ B} ∪ {B | Det.no univ B}) := by
  simp only [setOf_every_univ, setOf_no_univ]
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hu0 : (univ : Set ι) ≠ ∅ := (nonempty_iff_ne_empty.1 ⟨i, mem_univ i⟩)
  refine ⟨range (fun i ↦ {I : Set ι | i ∈ I}) ∪ {{univ}, {univ} ∪ {∅}}, fun i ↦ .inl ⟨i, rfl⟩,
    ?_, fun w ↦ ?_, by simp, fun hd ↦ ?_⟩
  · rintro φ (hφ | rfl | rfl) hφa
    exacts [absurd hφ hφa, isSymmetric_singleton_univ,
      isSymmetric_singleton_univ.union isSymmetric_singleton_empty]
  · rcases w.eq_empty_or_nonempty with rfl | hne
    · refine .inl ⟨{univ} ∪ {∅}, ⟨by simp, .inr rfl⟩, fun ψ ⟨hψ, h0⟩ ↦ ?_⟩
      rcases hψ with ⟨k, rfl⟩ | rfl | rfl
      · exact absurd h0 (notMem_empty k)
      · exact absurd (mem_singleton_iff.1 h0).symm hu0
      · exact subset_rfl
    by_cases hw : w = univ
    · subst hw
      exact .inl ⟨{univ}, ⟨by simp, rfl⟩, fun ψ ⟨_, hu⟩ I hI ↦ (mem_singleton_iff.1 hI) ▸ hu⟩
    refine .inr fun m ⟨⟨hm, hwm⟩, _⟩ ↦ ?_
    rcases hm with hm | rfl | rfl
    · exact hm
    · exact absurd (mem_singleton_iff.1 hwm) hw
    · rcases hwm with h | h
      exacts [absurd (mem_singleton_iff.1 h) hw, absurd (mem_singleton_iff.1 h) hne.ne_empty]
  · obtain ⟨ψ, ⟨hψ, hψs⟩, h0⟩ := hd (show (∅ : Set ι) ∈ ({univ} ∪ {∅} : Set (Set ι)) from .inr rfl)
    rcases hψ with ⟨k, rfl⟩ | rfl | rfl
    · exact notMem_empty k h0
    · exact hu0 (mem_singleton_iff.1 h0).symm
    · exact hψs.ne rfl

end Corners

/-! ### Projectively symmetric functions -/

/-- (35): a proposition is projectively symmetric when it lives on a set of atoms and is symmetric
in them. -/
def IsProjectivelySymmetric (φ : Set (Set ι)) : Prop :=
  ∃ J : Set ι, LivesOn (· ∈ φ) J ∧ ∀ σ : Equiv.Perm ι, σ ⁻¹' J = J → ∀ I, σ ⁻¹' I ∈ φ ↔ I ∈ φ

theorem IsSymmetric.isProjectivelySymmetric {φ : Set (Set ι)} (h : IsSymmetric φ) :
    IsProjectivelySymmetric φ :=
  ⟨univ, fun B ↦ by rw [univ_inter], fun σ _ ↦ h σ⟩

theorem isProjectivelySymmetric_atom (i : ι) : IsProjectivelySymmetric {I | i ∈ I} :=
  ⟨{i}, fun B ↦ by simp, fun σ hσ B ↦ by
    have : σ i = i := by simpa using congrArg (i ∈ ·) hσ
    simp [this]⟩

-- p. 715: a conservative, quantity-invariant determiner with any restrictor
theorem isProjectivelySymmetric_setOf {d : Det ι} (hC : d.Conservative)
    (hQ : d.QuantityInvariant) (A : Set ι) : IsProjectivelySymmetric {B | d A B} :=
  ⟨A, hC.livesOn A, fun σ hσ B ↦ by simpa [hσ] using hQ σ A B⟩

-- conversely, every projectively symmetric proposition is such a determiner with a restrictor
theorem isProjectivelySymmetric_iff {φ : Set (Set ι)} : IsProjectivelySymmetric φ ↔
    ∃ d : Det ι, d.Conservative ∧ d.QuantityInvariant ∧ ∃ A, φ = {B | d A B} := by
  refine ⟨fun ⟨J, hJ, hinv⟩ ↦ ?_,
    fun ⟨d, hC, hQ, A, hφ⟩ ↦ hφ ▸ isProjectivelySymmetric_setOf hC hQ A⟩
  -- `d A B` when a permutation carries `J` onto `A` and the part of `A ∩ B` it lands on is in `φ`
  let d : Det ι := fun A B ↦ ∃ τ : Equiv.Perm ι, τ ⁻¹' A = J ∧ τ ⁻¹' (A ∩ B) ∈ φ
  have key : ∀ (σ : Equiv.Perm ι) A B, d A B → d (σ ⁻¹' A) (σ ⁻¹' B) := by
    rintro σ A B ⟨τ, hτ, hB⟩
    refine ⟨σ⁻¹ * τ, ?_, ?_⟩
    · rw [← hτ]; ext x; simp
    · convert hB using 1; ext x; simp
  have e : ∀ (σ : Equiv.Perm ι) X, (⇑σ⁻¹) ⁻¹' (σ ⁻¹' X) = X := fun σ X ↦ by ext; simp
  refine ⟨d, fun A B ↦ ?_, fun σ A B ↦ ⟨fun h ↦ ?_, key σ A B⟩, J, ext fun B ↦ ?_⟩
  · simp only [d, ← inter_assoc, inter_self]
  · simpa only [e] using key σ⁻¹ _ _ h
  · refine ⟨fun hB ↦ ⟨1, rfl, (hJ B).1 hB⟩, fun ⟨τ, hτ, hB⟩ ↦ (hJ B).2 ((hinv τ hτ _).1 hB)⟩

private theorem swap_preimage_eq [DecidableEq ι] {J : Set ι} {a b : ι} (ha : a ∈ J) (hb : b ∈ J) :
    Equiv.swap a b ⁻¹' J = J := by
  ext x
  rcases eq_or_ne x a with rfl | hxa
  · simp [ha, hb]
  rcases eq_or_ne x b with rfl | hxb
  · simp [ha, hb]
  · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb]

section Projective

variable {φ : Set (Set ι)} {J : Set ι}

-- the appendix's lemma for (37): a projectively symmetric proposition entailing an atom entails
-- the conjunction of its domain, which contains the atom
private theorem subset_of_subset_atom (hJ : LivesOn (· ∈ φ) J)
    (hinv : ∀ σ : Equiv.Perm ι, σ ⁻¹' J = J → ∀ I, σ ⁻¹' I ∈ φ ↔ I ∈ φ) {i : ι}
    (hi : φ ⊆ {I | i ∈ I}) {B : Set ι} (hB : B ∈ φ) : i ∈ J ∧ J ⊆ B := by
  classical
  have hX : J ∩ B ∈ φ := (hJ B).1 hB
  have hiX : i ∈ J ∩ B := hi hX
  refine ⟨hiX.1, fun a ha ↦ by_contra fun haB ↦ ?_⟩
  have := hi ((hinv (Equiv.swap i a) (swap_preimage_eq hiX.1 ha) _).2 hX)
  simp only [mem_ofPred_eq, mem_preimage, Equiv.swap_apply_left, mem_inter_iff] at this
  exact haB this.2

-- dually, a projectively symmetric proposition entailed by an atom fails only where its domain does
private theorem inter_eq_empty_of_atom_subset (hJ : LivesOn (· ∈ φ) J)
    (hinv : ∀ σ : Equiv.Perm ι, σ ⁻¹' J = J → ∀ I, σ ⁻¹' I ∈ φ ↔ I ∈ φ) {i : ι}
    (hi : {I | i ∈ I} ⊆ φ) {B : Set ι} (hB : B ∉ φ) : J ∩ B = ∅ := by
  classical
  have hX : J ∩ B ∉ φ := fun h ↦ hB ((hJ B).2 h)
  by_cases hiJ : i ∈ J
  · refine eq_empty_of_forall_notMem fun a ha ↦ hX ?_
    exact (hinv (Equiv.swap i a) (swap_preimage_eq hiJ ha.1) _).1 (hi (by simpa using ha))
  · have h1 : insert i (J ∩ B) ∈ φ := hi (mem_insert i _)
    have h2 : J ∩ insert i (J ∩ B) = J ∩ B := by
      rw [inter_insert_of_notMem hiJ, ← inter_assoc, inter_self]
    exact absurd (h2 ▸ (hJ _).1 h1) hX

end Projective

-- (37b), for at least two atoms (Errata): the conjunctions and disjunctions of atoms are
-- alternatives, and every alternative is upward monotone
theorem isUpperSet_of_bilaterallyStronglyStable [Nontrivial ι] {A : Set (Set (Set ι))}
    (hat : ∀ i, {I | i ∈ I} ∈ A) (hps : ∀ φ ∈ A, IsProjectivelySymmetric φ)
    (h : BilaterallyStronglyStable A) :
    (∀ I, Ici I ∈ A) ∧ (∀ I, (Iic I)ᶜ ∈ A) ∧ ∀ φ ∈ A, IsUpperSet φ := by
  -- at a nonempty `I` the strongest true member is the conjunction `Ici I`
  have hsta : ∀ I : Set ι, I.Nonempty → Ici I ∈ A ∧ ∀ ψ ∈ A, I ∈ ψ → Ici I ⊆ ψ := by
    intro I ⟨k, hk⟩
    obtain ⟨σ, ⟨hσ, hIσ⟩, hmin⟩ := h.1 I
    obtain ⟨J, hJ, hinv⟩ := hps σ hσ
    obtain rfl : J = I := subset_antisymm
      (subset_of_subset_atom hJ hinv (hmin ⟨hat k, hk⟩) hIσ).2
      fun i hi ↦ (subset_of_subset_atom hJ hinv (hmin ⟨hat i, hi⟩) hIσ).1
    have hσJ : σ = Ici J := subset_antisymm
      (fun B hB ↦ mem_Ici.2 (subset_of_subset_atom hJ hinv (hmin ⟨hat k, hk⟩) hB).2)
      fun B hB ↦ (hJ B).2 (by rwa [inter_eq_left.2 (mem_Ici.1 hB)])
    exact ⟨hσJ ▸ hσ, fun ψ hψ hJψ ↦ hσJ ▸ hmin ⟨hψ, hJψ⟩⟩
  -- at `I ≠ univ` the weakest false member is the disjunction `(Iic I)ᶜ`
  have hwfa : ∀ I : Set ι, I ≠ univ → (Iic I)ᶜ ∈ A ∧ ∀ ψ ∈ A, I ∉ ψ → ψ ⊆ (Iic I)ᶜ := by
    intro I hI
    obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem I).1 hI
    obtain ⟨_, ⟨⟨χ, hχ, rfl⟩, hIχ⟩, hmin⟩ := h.2 I
    have hle : ∀ ψ ∈ A, I ∉ ψ → ψ ⊆ χ := fun ψ hψ hIψ B hB ↦
      by_contra fun hBχ ↦ hmin ⟨⟨ψ, hψ, rfl⟩, hIψ⟩ hBχ hB
    obtain ⟨J, hJ, hinv⟩ := hps χ hχ
    have hχI : χ = (Iic I)ᶜ := by
      refine subset_antisymm (fun B hB hBI ↦ hIχ ?_) fun B hB ↦ ?_
      · have hJI := inter_eq_empty_of_atom_subset hJ hinv (hle _ (hat b) hb) hIχ
        have hJB : J ∩ B = ∅ := subset_empty_iff.1 (hJI ▸ inter_subset_inter_right J hBI)
        exact (hJ I).2 (hJI ▸ hJB ▸ (hJ B).1 hB)
      · obtain ⟨j, hjB, hjI⟩ := not_subset.1 (show ¬ B ⊆ I from hB)
        exact hle _ (hat j) hjI hjB
    exact ⟨hχI ▸ hχ, fun ψ hψ hIψ ↦ hχI ▸ hle ψ hψ hIψ⟩
  -- a member true where no atom holds is the tautology
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  have htaut : ∀ ψ ∈ A, ∅ ∈ ψ → ψ = univ := by
    intro ψ hψ h0
    have hne : ∀ I, I ≠ univ → I ∈ ψ := fun I hI ↦
      by_contra fun hIψ ↦ (hwfa I hI).2 ψ hψ hIψ h0 (empty_subset I)
    have hau : ({a} : Set ι) ≠ univ := fun h ↦ hab (mem_singleton_iff.1 (h ▸ mem_univ b)).symm
    exact eq_univ_of_forall fun B ↦ (eq_or_ne B univ).elim
      (fun hB ↦ hB ▸ (hsta {a} (singleton_nonempty a)).2 ψ hψ (hne _ hau) (subset_univ _)) (hne B)
  have hup : ∀ φ ∈ A, IsUpperSet φ := fun φ hφ I J hIJ hI ↦
    I.eq_empty_or_nonempty.elim (fun h0 ↦ htaut φ hφ (h0 ▸ hI) ▸ mem_univ J)
      fun hne ↦ (hsta I hne).2 φ hφ hI hIJ
  refine ⟨fun I ↦ I.eq_empty_or_nonempty.elim (fun h0 ↦ ?_) fun hne ↦ (hsta I hne).1,
    fun I ↦ (eq_or_ne I univ).elim (fun hu ↦ ?_) fun hne ↦ (hwfa I hne).1, hup⟩
  · obtain ⟨σ, ⟨hσ, h0σ⟩, -⟩ := h.1 ∅
    rw [h0, show Ici (∅ : Set ι) = univ from Ici_bot, ← htaut σ hσ h0σ]
    exact hσ
  · obtain ⟨_, ⟨⟨χ, hχ, rfl⟩, huχ⟩, -⟩ := h.2 univ
    have hχ0 : χ = ∅ := eq_empty_of_forall_notMem fun B hB ↦ huχ <|
      B.eq_empty_or_nonempty.elim (fun h0 ↦ htaut χ hχ (h0 ▸ hB) ▸ mem_univ _)
        fun hne ↦ (hsta B hne).2 χ hχ hB (subset_univ B)
    rw [hu, show (Iic (univ : Set ι))ᶜ = ∅ from (congrArg compl Iic_top).trans compl_univ, ← hχ0]
    exact hχ

-- (34c) and (37b) at a single atom: `p` and `¬p` (Errata)
theorem exists_isSymmetric_not_isUpperSet :
    ∃ A : Set (Set (Set Unit)), (∀ i, {I | i ∈ I} ∈ A) ∧
      (∀ φ ∈ A, IsSymmetric φ ∧ IsProjectivelySymmetric φ) ∧ BilaterallyStronglyStable A ∧
      BilaterallyWeaklyStable (range fun i ↦ {I : Set Unit | i ∈ I}) A ∧
      ∃ φ ∈ A, φ ∉ range (fun i ↦ {I : Set Unit | i ∈ I}) ∧ ¬ IsUpperSet φ := by
  have hsym : ∀ φ : Set (Set Unit), IsSymmetric φ := fun φ σ I ↦ by
    rw [Subsingleton.elim σ 1]; rfl
  have hA : BilaterallyStronglyStable ({{I | () ∈ I}, {I | () ∈ I}ᶜ} : Set (Set (Set Unit))) := by
    refine ⟨fun w ↦ ?_, fun w ↦ ?_⟩ <;> by_cases h : () ∈ w
    · exact ⟨_, ⟨.inl rfl, h⟩, by rintro ψ ⟨rfl | rfl, hw⟩ <;> simp_all⟩
    · exact ⟨_, ⟨.inr rfl, h⟩, by rintro ψ ⟨rfl | rfl, hw⟩ <;> simp_all⟩
    · exact ⟨_, ⟨⟨_, .inr rfl, compl_compl _⟩, h⟩, by
        rintro _ ⟨⟨_, rfl | rfl, rfl⟩, hw⟩ <;> simp_all⟩
    · exact ⟨_, ⟨⟨_, .inl rfl, rfl⟩, h⟩, by rintro _ ⟨⟨_, rfl | rfl, rfl⟩, hw⟩ <;> simp_all⟩
  refine ⟨_, fun _ ↦ .inl rfl, fun φ _ ↦ ⟨hsym φ, (hsym φ).isProjectivelySymmetric⟩, hA,
    ⟨hA.1.weaklyStable _, hA.2.weaklyStable _⟩, _, .inr rfl, fun ⟨_, h⟩ ↦ ?_,
    fun h ↦ h (empty_subset univ) (notMem_empty ()) (mem_univ ())⟩
  simpa using congrArg (univ ∈ ·) h

/-- (37b) read off a lexicon: if the atoms and the sentences that conservative, quantity-invariant
determiners form with any restrictor are bilaterally strongly stable, then, with at least two
atoms, every determiner in the lexicon is monotone in its scope. -/
theorem scopeMonotone_of_bilaterallyStronglyStable [Nontrivial ι] {D : Set (Det ι)}
    (hC : ∀ d ∈ D, d.Conservative) (hQ : ∀ d ∈ D, d.QuantityInvariant)
    (h : BilaterallyStronglyStable
      (range (fun i ↦ {B : Set ι | individual i B}) ∪ ⋃ d ∈ D, range fun A ↦ {B | d A B})) :
    ∀ d ∈ D, d.ScopeMonotone := by
  intro d hd A
  rw [← isUpperSet_setOfPred]
  refine (isUpperSet_of_bilaterallyStronglyStable (fun i ↦ .inl ⟨i, rfl⟩) ?_ h).2.2 _
    (.inr (mem_biUnion hd ⟨A, rfl⟩))
  rintro φ (⟨i, rfl⟩ | hφ)
  · exact isProjectivelySymmetric_atom i
  · obtain ⟨d', hd', A', rfl⟩ := mem_iUnion₂.1 hφ
    exact isProjectivelySymmetric_setOf (hC d' hd') (hQ d' hd') A'

-- conversely, a lexicon of scope-monotone determiners with *every* and *some* is bilaterally
-- strongly stable: *every* with restrictor `w` is strongest true, *some* with `wᶜ` weakest false
theorem bilaterallyStronglyStable_of_scopeMonotone {D : Set (Det ι)} (he : Det.every ∈ D)
    (hs : Det.some ∈ D) (hM : ∀ d ∈ D, d.ScopeMonotone) :
    BilaterallyStronglyStable
      (range (fun i ↦ {B : Set ι | individual i B}) ∪ ⋃ d ∈ D, range fun A ↦ {B | d A B}) := by
  have hup : ∀ φ ∈ range (fun i ↦ {B : Set ι | individual i B}) ∪
      ⋃ d ∈ D, range fun A ↦ {B | d A B}, IsUpperSet φ := by
    rintro φ (⟨i, rfl⟩ | hφ)
    · exact fun _ _ hIJ h ↦ hIJ h
    · obtain ⟨d, hd, A, rfl⟩ := mem_iUnion₂.1 hφ
      exact isUpperSet_setOfPred.2 (hM d hd A)
  have hsome : ∀ w : Set ι, {B | Det.some wᶜ B} = (Iic w)ᶜ := fun w ↦ ext fun B ↦ by
    simp [Det.some, not_subset, Set.Nonempty, and_comm]
  refine ⟨fun w ↦ ⟨Ici w, ⟨.inr (mem_biUnion he ⟨w, rfl⟩), mem_Ici.2 le_rfl⟩,
    fun ψ ⟨hψ, hwψ⟩ B hB ↦ hup ψ hψ hB hwψ⟩, fun w ↦ ⟨(Iic w)ᶜᶜ,
    ⟨⟨(Iic w)ᶜ, .inr (mem_biUnion hs ⟨wᶜ, hsome w⟩), rfl⟩, by simp⟩, ?_⟩⟩
  rintro _ ⟨⟨χ, hχ, rfl⟩, hwχ⟩ B hB hBχ
  exact hwχ (hup χ hχ (by simpa using hB) hBχ)

-- *no* breaks it
theorem not_bilaterallyStronglyStable_every_some_no [Nontrivial ι] :
    ¬ BilaterallyStronglyStable (range (fun i ↦ {B : Set ι | individual i B}) ∪
      ⋃ d ∈ ({Det.every, Det.some, Det.no} : Set (Det ι)), range fun A ↦ {B | d A B}) := by
  intro h
  have hm := scopeMonotone_of_bilaterallyStronglyStable
    (by rintro d (rfl | rfl | rfl); exacts [Det.conservative_every, Det.conservative_some,
      Det.conservative_no])
    (by rintro d (rfl | rfl | rfl); exacts [Det.quantityInvariant_every,
      Det.quantityInvariant_some, Det.quantityInvariant_no]) h _ (.inr (.inr rfl)) univ
    (empty_subset univ) (show Det.no univ ∅ by simp [Det.no])
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact absurd ((hm : univ ⊆ univᶜ) (mem_univ i)) (by simp)

-- *nobody* over the whole domain keeps the alternatives strongly stable but not their negations:
-- the indirect implicatures of Sect. 2.2
theorem stronglyStable_and_not_bilaterallyStronglyStable_nobody [Nontrivial ι] :
    StronglyStable (range (fun i ↦ {B : Set ι | individual i B}) ∪
        (⋃ d ∈ ({Det.every, Det.some} : Set (Det ι)), range fun A ↦ {B | d A B}) ∪
          {{B | Det.no univ B}}) ∧
      ¬ BilaterallyStronglyStable (range (fun i ↦ {B : Set ι | individual i B}) ∪
        (⋃ d ∈ ({Det.every, Det.some} : Set (Det ι)), range fun A ↦ {B | d A B}) ∪
          {{B | Det.no univ B}}) := by
  have hN : {B : Set ι | Det.no univ B} = {∅} := setOf_no_univ
  refine ⟨fun w ↦ ?_, fun h ↦ ?_⟩
  · rcases w.eq_empty_or_nonempty with rfl | hne
    · exact ⟨_, ⟨.inr rfl, by simp [Det.no]⟩, fun ψ ⟨_, h0⟩ I hI ↦
        (mem_singleton_iff.1 (hN ▸ hI)) ▸ h0⟩
    refine ⟨Ici w, ⟨.inl (.inr (mem_biUnion (.inl rfl) ⟨w, rfl⟩)), mem_Ici.2 le_rfl⟩, ?_⟩
    rintro ψ ⟨(⟨i, rfl⟩ | hψ) | hψ, hwψ⟩ B hB
    · exact mem_Ici.1 hB hwψ
    · obtain ⟨d, hd, A, rfl⟩ := mem_iUnion₂.1 hψ
      rcases hd with rfl | rfl
      · exact (mem_Ici.1 hB).trans' hwψ
      · exact hwψ.mono (inter_subset_inter_right _ (mem_Ici.1 hB))
    · rw [mem_singleton_iff.1 hψ, hN] at hwψ
      exact absurd (mem_singleton_iff.1 hwψ) hne.ne_empty
  · have hup := (isUpperSet_of_bilaterallyStronglyStable (fun i ↦ .inl (.inl ⟨i, rfl⟩)) ?_ h).2.2
      _ (.inr rfl)
    · obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      rw [hN] at hup
      exact absurd (mem_singleton_iff.1 (hup (empty_subset univ) rfl)) (nonempty_iff_ne_empty.1
        ⟨i, mem_univ i⟩)
    rintro φ ((⟨i, rfl⟩ | hφ) | hφ)
    · exact isProjectivelySymmetric_atom i
    · obtain ⟨d, hd, A, rfl⟩ := mem_iUnion₂.1 hφ
      rcases hd with rfl | rfl
      exacts [isProjectivelySymmetric_setOf Det.conservative_every Det.quantityInvariant_every A,
        isProjectivelySymmetric_setOf Det.conservative_some Det.quantityInvariant_some A]
    · rw [mem_singleton_iff.1 hφ]
      exact isProjectivelySymmetric_setOf Det.conservative_no Det.quantityInvariant_no univ

/-! ### Closed classes of functions -/

/-- (39): a clone gives, for each number of atoms, a set of propositions over them that contains the
atoms and is closed under composition. -/
structure IsClone (F : ∀ n : ℕ, Set (Set (Set (Fin n)))) : Prop where
  atom_mem : ∀ n (i : Fin n), {I | i ∈ I} ∈ F n
  comp_mem : ∀ n k (g : Set (Set (Fin k))) (f : Fin k → Set (Set (Fin n))), g ∈ F k →
    (∀ j, f j ∈ F n) → {I | {j | I ∈ f j} ∈ g} ∈ F n

private theorem sUnion_mem {S T : Set (Set W)} (h0 : ∅ ∈ S) (hu : ∀ a ∈ S, ∀ b ∈ S, a ∪ b ∈ S)
    (hT : T.Finite) (hTS : T ⊆ S) : ⋃₀ T ∈ S := by
  obtain ⟨t, rfl⟩ := hT.exists_finset_coe
  rw [← Finset.sup_id_set_eq_sUnion]
  exact Finset.sup_induction h0 hu fun a ha ↦ hTS ha

private theorem sInter_mem {S T : Set (Set W)} (h1 : univ ∈ S) (hi : ∀ a ∈ S, ∀ b ∈ S, a ∩ b ∈ S)
    (hT : T.Finite) (hTS : T ⊆ S) : ⋂₀ T ∈ S := by
  obtain ⟨t, rfl⟩ := hT.exists_finset_coe
  rw [← Finset.inf_id_set_eq_sInter]
  exact Finset.inf_induction h1 hi fun a ha ↦ hTS ha

-- with the atoms, conjunction and negation express every proposition over at least one atom
private theorem eq_univ_of_inter_compl {n : ℕ} {S : Set (Set (Set (Fin n)))} (hn : 0 < n)
    (hat : ∀ i : Fin n, {I | i ∈ I} ∈ S) (hi : ∀ a ∈ S, ∀ b ∈ S, a ∩ b ∈ S)
    (hc : ∀ a ∈ S, aᶜ ∈ S) : S = univ := by
  classical
  have hu : ∀ a ∈ S, ∀ b ∈ S, a ∪ b ∈ S := fun a ha b hb ↦ by
    simpa [compl_inter] using hc _ (hi _ (hc a ha) _ (hc b hb))
  have h0 : ∅ ∈ S := by simpa using hi _ (hat ⟨0, hn⟩) _ (hc _ (hat ⟨0, hn⟩))
  have h1 : univ ∈ S := by simpa using hc _ h0
  have hcell : ∀ I : Set (Fin n), ({I} : Set (Set (Fin n))) =
      ⋂₀ range fun i ↦ if i ∈ I then {J | i ∈ J} else {J | i ∈ J}ᶜ := by
    intro I; ext J
    simp only [mem_singleton_iff, mem_sInter, forall_mem_range]
    refine ⟨fun h i ↦ ?_, fun h ↦ ext fun i ↦ ?_⟩
    · subst h; split_ifs with hi <;> simpa
    · have := h i; split_ifs at this with hi <;> simp_all
  refine eq_univ_of_forall fun φ ↦ ?_
  rw [← biUnion_of_singleton φ, ← sUnion_image]
  refine sUnion_mem h0 hu (toFinite _) ?_
  rintro _ ⟨I, -, rfl⟩
  rw [hcell]
  refine sInter_mem h1 hi (finite_range _) ?_
  rintro _ ⟨i, rfl⟩
  dsimp only
  split_ifs
  exacts [hat i, hc _ (hat i)]

namespace IsClone

variable {F : ∀ n : ℕ, Set (Set (Set (Fin n)))} (hF : IsClone F)
include hF

theorem compl_mem (hneg : {J : Set (Fin 1) | 0 ∉ J} ∈ F 1) {n : ℕ} {φ : Set (Set (Fin n))}
    (hφ : φ ∈ F n) : φᶜ ∈ F n := by
  convert hF.comp_mem n 1 _ (fun _ ↦ φ) hneg fun _ ↦ hφ using 1
  ext I; simp

-- a clone with both constants that holds a function not monotone holds negation
theorem neg_mem (htop : univ ∈ F 1) (hbot : ∅ ∈ F 1) {n : ℕ} {φ : Set (Set (Fin n))}
    (hφ : φ ∈ F n) (hnm : ¬ IsUpperSet φ) : {J : Set (Fin 1) | 0 ∉ J} ∈ F 1 := by
  classical
  obtain ⟨I, J, hIJ, hI, hJ⟩ : ∃ I J, I ≤ J ∧ I ∈ φ ∧ J ∉ φ := by
    by_contra h
    push Not at h
    exact hnm fun I J hIJ hI ↦ h I J hIJ hI
  -- a step up by one atom out of `φ`
  obtain ⟨K, -, ⟨hKJ, hK⟩, hmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT (fun K ↦ K ≤ J ∧ K ∈ φ) I ⟨hIJ, hI⟩
  obtain ⟨j, hjJ, hjK⟩ := exists_of_ssubset (hKJ.lt_of_ne fun h ↦ hJ (h ▸ hK))
  have hjK' : insert j K ∉ φ := fun h ↦
    hjK (hmax ⟨insert_subset hjJ hKJ, h⟩ (subset_insert j K) (mem_insert j K))
  -- vary the atom `j`, hold the atoms of `K` true and the others false
  let g : Fin n → Set (Set (Fin 1)) := fun i ↦
    if i = j then {X | 0 ∈ X} else if i ∈ K then univ else ∅
  have hg : ∀ X : Set (Fin 1), {i | X ∈ g i} = if (0 : Fin 1) ∈ X then insert j K else K := by
    intro X; ext i
    by_cases hij : i = j
    · subst hij; split_ifs <;> simp_all [g]
    · by_cases hiK : i ∈ K <;> split_ifs <;> simp_all [g]
  convert hF.comp_mem 1 n φ g hφ (fun i ↦ by
    simp only [g]; split_ifs; exacts [hF.atom_mem 1 0, htop, hbot]) using 1
  ext X
  simp only [mem_ofPred_eq, hg X]
  split_ifs with h0 <;> simp [h0, hK, hjK']

end IsClone

-- the monotone functions form a clone, and a proper one
theorem isClone_isUpperSet : IsClone (fun n ↦ {φ : Set (Set (Fin n)) | IsUpperSet φ}) ∧
    ∀ n, 0 < n → {φ : Set (Set (Fin n)) | IsUpperSet φ} ≠ univ := by
  refine ⟨⟨fun n i I J hIJ (hI : i ∈ I) ↦ hIJ hI, fun n k g f hg hf I J hIJ hI ↦
    hg (fun j (hj : I ∈ f j) ↦ hf j hIJ hj) hI⟩, fun n hn h ↦ ?_⟩
  have : {I : Set (Fin n) | ⟨0, hn⟩ ∈ I}ᶜ ∈ {φ : Set (Set (Fin n)) | IsUpperSet φ} := h ▸ mem_univ _
  exact this (empty_subset {(⟨0, hn⟩ : Fin n)}) (notMem_empty (⟨0, hn⟩ : Fin n)) (mem_singleton _)

-- the propositions of the clone of all functions are bilaterally strongly stable, the cells the
-- strongest true and their complements the weakest false members: (40) needs the clone proper
theorem bilaterallyStronglyStable_univ : BilaterallyStronglyStable (univ : Set (Set W)) := by
  refine ⟨fun w ↦ ⟨{w}, ⟨trivial, rfl⟩, fun ψ ⟨_, hw⟩ ↦ singleton_subset_iff.2 hw⟩,
    fun w ↦ ⟨{w}, ⟨⟨{w}ᶜ, trivial, compl_compl _⟩, rfl⟩, fun ψ ⟨_, hw⟩ ↦ singleton_subset_iff.2 hw⟩⟩

-- (40a), with a true and a false member at every world (Errata)
theorem isUpperSet_of_isClone {F : ∀ n : ℕ, Set (Set (Set (Fin n)))} (hF : IsClone F)
    (hL : ∃ n, 0 < n ∧ F n ≠ univ) (hT : ∀ n, 0 < n → ∀ w, ∃ φ ∈ F n, w ∈ φ)
    (hF' : ∀ n, 0 < n → ∀ w, ∃ φ ∈ F n, w ∉ φ)
    (h : ∀ n, 0 < n → BilaterallyWeaklyStable (range fun i : Fin n ↦ {I | i ∈ I}) (F n)) :
    ∀ n, 0 < n → ∀ φ ∈ F n, IsUpperSet φ := by
  have hunary : ∀ φ : Set (Set (Fin 1)),
      φ = ∅ ∨ φ = {J | 0 ∉ J} ∨ φ = {J | 0 ∈ J} ∨ φ = univ := by
    intro φ
    have hJ : ∀ J : Set (Fin 1), J = ∅ ∨ J = univ := fun J ↦ J.eq_empty_or_nonempty.imp id
      fun ⟨x, hx⟩ ↦ eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx
    have hneg : ({J : Set (Fin 1) | 0 ∉ J}) = {∅} := ext fun J ↦ by
      simp [eq_empty_iff_forall_notMem, Fin.forall_fin_one]
    have hpos : ({J : Set (Fin 1) | 0 ∈ J}) = {univ} := ext fun J ↦ by
      simp [eq_univ_iff_forall, Fin.forall_fin_one]
    rw [hneg, hpos]
    rcases subset_pair_iff_eq.1 (fun J (_ : J ∈ φ) ↦ hJ J) with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (h.trans (eq_univ_of_forall fun J ↦ (hJ J).elim .inl .inr))))
  -- negation is not in the clone: with it `p ∧ ¬q`, so conjunction, so everything would be
  have hneg : {J : Set (Fin 1) | 0 ∉ J} ∉ F 1 := by
    intro hneg
    obtain ⟨n, hn, hFn⟩ := hL
    have hq : {I : Set (Fin 2) | 1 ∈ I}ᶜ ∈ F 2 := hF.compl_mem hneg (hF.atom_mem 2 1)
    obtain ⟨m, hmq, hm⟩ := exists_minimal_le_of_wellFoundedLT
      (· ∈ trueAnswers (F 2) {0}) _ ⟨hq, by simp⟩
    rcases (h 2 two_pos).1 {0} with ⟨σ, ⟨hσ, h0σ⟩, hmin⟩ | hat
    · have hσ0 : σ = {{0}} := by
        refine subset_antisymm (fun I hI ↦ ?_) (singleton_subset_iff.2 h0σ)
        have h0 : (0 : Fin 2) ∈ I := hmin ⟨hF.atom_mem 2 0, rfl⟩ hI
        have h1 : (1 : Fin 2) ∉ I := hmin ⟨hq, by simp⟩ hI
        exact ext fun x ↦ by fin_cases x <;> simp [h0, h1]
      refine hFn (eq_univ_of_inter_compl hn (hF.atom_mem n) (fun a ha b hb ↦ ?_)
        fun a ha ↦ hF.compl_mem hneg ha)
      convert hF.comp_mem n 2 σ ![a, bᶜ] hσ (Fin.forall_fin_two.2 ⟨ha, hF.compl_mem hneg hb⟩)
        using 1
      ext I
      simp [hσ0, Set.ext_iff, Fin.forall_fin_two]
    · obtain ⟨k, rfl⟩ := hat m hm
      exact absurd (hmq (show univ ∈ {I : Set (Fin 2) | k ∈ I} from mem_univ k)) (by simp)
  -- so both constants are
  obtain ⟨φ₁, hφ₁, h0φ₁⟩ := hT 1 one_pos ∅
  obtain ⟨φ₂, hφ₂, h1φ₂⟩ := hF' 1 one_pos univ
  have htop : univ ∈ F 1 := by
    rcases hunary φ₁ with rfl | rfl | rfl | rfl
    · exact absurd h0φ₁ (notMem_empty _)
    · exact absurd hφ₁ hneg
    · exact absurd h0φ₁ (notMem_empty 0)
    · exact hφ₁
  have hbot : ∅ ∈ F 1 := by
    rcases hunary φ₂ with rfl | rfl | rfl | rfl
    · exact hφ₂
    · exact absurd hφ₂ hneg
    · exact absurd (mem_univ 0) h1φ₂
    · exact absurd (mem_univ _) h1φ₂
  exact fun n _ φ hφ ↦ by_contra fun hnm ↦ hneg (hF.neg_mem htop hbot hφ hnm)

/-- (40b): a proper clone is bilaterally strongly stable at every number of atoms iff it is the
clone of upward-monotone functions. -/
theorem bilaterallyStronglyStable_iff_eq_isUpperSet {F : ∀ n : ℕ, Set (Set (Set (Fin n)))}
    (hF : IsClone F) (hL : ∃ n, 0 < n ∧ F n ≠ univ) :
    (∀ n, 0 < n → BilaterallyStronglyStable (F n)) ↔ ∀ n, 0 < n → F n = {φ | IsUpperSet φ} := by
  refine ⟨fun h ↦ ?_, fun h n hn ↦ h n hn ▸ bilaterallyStronglyStable_isUpperSet⟩
  have hup := isUpperSet_of_isClone hF hL (fun n hn w ↦ let ⟨σ, hσ, _⟩ := (h n hn).1 w; ⟨σ, hσ⟩)
    (fun n hn w ↦ let ⟨_, ⟨⟨χ, hχ, rfl⟩, hw⟩, _⟩ := (h n hn).2 w; ⟨χ, hχ, hw⟩)
    fun n hn ↦ ⟨(h n hn).1.weaklyStable _, (h n hn).2.weaklyStable _⟩
  have hor := compl_Iic_empty_mem_of_stronglyStable (hF.atom_mem 2) (h 2 two_pos).2
  intro n hn
  refine subset_antisymm (hup n hn) fun φ hφ ↦ ?_
  have hu : ∀ a ∈ F n, ∀ b ∈ F n, a ∪ b ∈ F n := fun a ha b hb ↦ by
    convert hF.comp_mem n 2 _ ![a, b] hor (Fin.forall_fin_two.2 ⟨ha, hb⟩) using 1
    ext I
    simp [subset_empty_iff, eq_empty_iff_forall_notMem, or_iff_not_imp_left]
  have h0 : ∅ ∈ F n := by
    have := compl_Iic_mem (hF.atom_mem n) (hup n hn) (h n hn).2 univ
    rwa [show (Iic (univ : Set (Fin n)))ᶜ = ∅ from (congrArg compl Iic_top).trans compl_univ]
      at this
  have hφ' : φ = ⋃₀ (Ici '' φ) := ext fun J ↦
    ⟨fun hJ ↦ ⟨Ici J, mem_image_of_mem _ hJ, mem_Ici.2 le_rfl⟩,
      fun ⟨_, ⟨I, hI, rfl⟩, hIJ⟩ ↦ hφ hIJ hI⟩
  rw [hφ']
  exact sUnion_mem h0 hu (toFinite _) (image_subset_iff.2 fun I _ ↦
    Ici_mem (hF.atom_mem n) (hup n hn) (h n hn).1 I)

-- (40a) as printed: the falsity-preserving functions form a proper clone, bilaterally weakly
-- stable, vacuously where no atom holds, that holds exclusive disjunction (Errata)
theorem exists_isClone_bilaterallyWeaklyStable_not_isUpperSet :
    ∃ F : ∀ n : ℕ, Set (Set (Set (Fin n))), IsClone F ∧ (∀ n, F n ≠ univ) ∧
      (∀ n, BilaterallyWeaklyStable (range fun i : Fin n ↦ {I | i ∈ I}) (F n)) ∧
      ({{0}, {1}} : Set (Set (Fin 2))) ∈ F 2 ∧ ¬ IsUpperSet ({{0}, {1}} : Set (Set (Fin 2))) := by
  refine ⟨fun n ↦ {φ | ∅ ∉ φ}, ⟨fun n i ↦ notMem_empty i, fun n k g f hg hf h0 ↦
    hg (eq_empty_of_forall_notMem (fun j hj ↦ hf j hj) ▸ h0)⟩, fun n h ↦ ?_,
    fun n ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, by simp, fun h ↦ ?_⟩
  · have h' : {φ : Set (Set (Fin n)) | ∅ ∉ φ} = univ := h
    exact (show (univ : Set (Set (Fin n))) ∈ {φ : Set (Set (Fin n)) | ∅ ∉ φ} by
      rw [h']; trivial) (mem_univ ∅)
  · by_cases hw : w = ∅
    · exact .inr fun φ hm ↦ absurd (hw ▸ hm.1.2) hm.1.1
    · exact .inl ⟨{w}, ⟨fun h ↦ hw (mem_singleton_iff.1 h).symm, rfl⟩,
        fun ψ ⟨_, hwψ⟩ ↦ singleton_subset_iff.2 hwψ⟩
  · refine .inl ⟨{∅, w}, ⟨⟨{∅, w}ᶜ, by simp, compl_compl _⟩, by simp⟩, ?_⟩
    rintro _ ⟨⟨θ, hθ, rfl⟩, hwθ⟩ I hI
    rcases hI with rfl | rfl
    exacts [hθ, hwθ]
  · have := h (subset_univ {0}) (by simp)
    rcases this with h1 | h1
    · simpa using congrArg ((1 : Fin 2) ∈ ·) h1
    · simpa using congrArg ((0 : Fin 2) ∈ ·) h1

/-! ### Bar-Lev and Katzir's communicative stability -/

section Stability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {U : Type*} [MeasurableSpace U]
  [Countable U] [MeasurableSingletonClass U] (sem : U → Set W)

/-- (57): at the prior `μ` the message `u` is optimal at `w`: it is true there, and its literal
listener gives `w` more mass than that of any true message with another meaning. -/
def IsOptimal (μ : Measure W) (w : W) (u : U) : Prop :=
  w ∈ sem u ∧ ∀ u', w ∈ sem u' → sem u' ≠ sem u →
    RSA.listener μ (RSA.truthful sem) u' {w} < RSA.listener μ (RSA.truthful sem) u {w}

/-- A.3: a message is optimal at `w` for some prior giving every world positive mass iff its
meaning is minimal among the meanings true at `w`, so that which message the pragmatic speaker
chooses does not depend on the prior exactly where a strongest true meaning exists. -/
theorem exists_prior_iff_minimal [Fintype W] {w : W} {u : U} :
    (∃ μ : Measure W, IsProbabilityMeasure μ ∧ (∀ v, μ {v} ≠ 0) ∧ IsOptimal sem μ w u) ↔
      Minimal (· ∈ trueAnswers (range sem) w) (sem u) := by
  -- the literal listener's mass at `w` falls as the prior mass of the meaning rises
  have key : ∀ (μ : Measure W) [IsFiniteMeasure μ], μ {w} ≠ 0 → ∀ {u u' : U}, w ∈ sem u →
      w ∈ sem u' → (RSA.listener μ (RSA.truthful sem) u' {w} <
        RSA.listener μ (RSA.truthful sem) u {w} ↔ μ (sem u) < μ (sem u')) := by
    intro μ _ hw u u' hu hu'
    rw [RSA.listener_truthful_apply_singleton μ sem hu,
      RSA.listener_truthful_apply_singleton μ sem hu',
      ENNReal.mul_lt_mul_iff_left hw (measure_ne_top μ _), ENNReal.inv_lt_inv]
  constructor
  · rintro ⟨μ, _, hpos, hu, hopt⟩
    refine ⟨⟨⟨u, rfl⟩, hu⟩, ?_⟩
    rintro _ ⟨⟨u', rfl⟩, hu'⟩ hle
    by_contra hne
    exact (measure_mono hle).not_gt
      ((key μ (hpos w) hu hu').1 (hopt u' hu' fun h ↦ hne (h ▸ le_rfl)))
  · rintro ⟨⟨_, hu⟩, hmin⟩
    -- the prior putting little mass inside the meaning of `u` and much outside it
    have hcount : ∀ s : Set W, Measure.count s ≠ ⊤ :=
      fun s ↦ (Measure.count_apply_lt_top.2 s.toFinite).ne
    set N : ℝ≥0∞ := Measure.count (univ : Set W) + 1
    set ν : Measure W := Measure.count + N • Measure.count.restrict (sem u)ᶜ
    have hν : ∀ s, ν s = Measure.count s + N * Measure.count (s ∩ (sem u)ᶜ) := fun s ↦ by
      simp [ν, Measure.restrict_apply .of_discrete]
    have hN : N ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hcount _, ENNReal.one_ne_top⟩
    have hνtop : ν univ ≠ ⊤ := by
      rw [hν]; exact ENNReal.add_ne_top.2 ⟨hcount _, ENNReal.mul_ne_top hN (hcount _)⟩
    have hν0 : ∀ v, ν {v} ≠ 0 := fun v ↦ by simp [hν]
    have hνu : ν univ ≠ 0 := fun h ↦ hν0 w (measure_mono_null (subset_univ _) h)
    set μ : Measure W := (ν univ)⁻¹ • ν
    have hμ : ∀ s, μ s = (ν univ)⁻¹ * ν s := fun s ↦ by simp [μ]
    have : IsProbabilityMeasure μ := ⟨by rw [hμ, ENNReal.inv_mul_cancel hνu hνtop]⟩
    refine ⟨μ, inferInstance, fun v ↦ ?_, hu, fun u' hu' hne ↦ ?_⟩
    · rw [hμ]; exact mul_ne_zero (ENNReal.inv_ne_zero.2 hνtop) (hν0 v)
    obtain ⟨v, hv, hvu⟩ := not_subset.1 fun h ↦
      hne (subset_antisymm h (hmin ⟨⟨u', rfl⟩, hu'⟩ h))
    rw [key μ (by rw [hμ]; exact mul_ne_zero (ENNReal.inv_ne_zero.2 hνtop) (hν0 w)) hu hu', hμ,
      hμ, ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 hνtop) (ENNReal.inv_ne_top.2 hνu),
      hν, hν, inter_compl_self, measure_empty, mul_zero, add_zero]
    calc Measure.count (sem u) ≤ Measure.count univ := measure_mono (subset_univ _)
      _ < N := ENNReal.lt_add_right (hcount _) one_ne_zero
      _ = N * Measure.count {v} := by rw [Measure.count_singleton, mul_one]
      _ ≤ N * Measure.count (sem u' ∩ (sem u)ᶜ) := by
        gcongr; exact singleton_subset_iff.2 ⟨hv, hvu⟩
      _ ≤ _ := le_add_self

-- (58b): strict stability in Bar-Lev and Katzir's sense, which the paper adds to theirs, that
-- priors never make messages with different meanings optimal at one world, is strong stability
-- when some message is true at every world
theorem stronglyStable_iff_isOptimal [Fintype W] (hcov : ∀ w, ∃ u, w ∈ sem u) :
    StronglyStable (range sem) ↔ ∀ (w : W) (u u' : U) (μ μ' : Measure W),
      IsProbabilityMeasure μ → IsProbabilityMeasure μ' → (∀ v, μ {v} ≠ 0) → (∀ v, μ' {v} ≠ 0) →
        IsOptimal sem μ w u → IsOptimal sem μ' w u' → sem u = sem u' := by
  constructor
  · intro h w u u' μ μ' hμ hμ' hp hp' ho ho'
    obtain ⟨l, hl⟩ := h w
    have e : ∀ {x}, Minimal (· ∈ trueAnswers (range sem) w) x → x = l :=
      fun hx ↦ le_antisymm (hx.2 hl.1 (hl.2 hx.1)) (hl.2 hx.1)
    exact (e ((exists_prior_iff_minimal sem).1 ⟨μ, hμ, hp, ho⟩)).trans
      (e ((exists_prior_iff_minimal sem).1 ⟨μ', hμ', hp', ho'⟩)).symm
  · intro h w
    obtain ⟨u, hu⟩ := hcov w
    obtain ⟨m, -, hm⟩ := exists_minimal_le_of_wellFoundedLT
      (· ∈ trueAnswers (range sem) w) (sem u) ⟨⟨u, rfl⟩, hu⟩
    refine ⟨m, hm.1, fun q hq ↦ ?_⟩
    obtain ⟨m', hm'q, hm'⟩ := exists_minimal_le_of_wellFoundedLT
      (· ∈ trueAnswers (range sem) w) q hq
    obtain ⟨⟨u₁, rfl⟩, -⟩ := hm.1
    obtain ⟨⟨u₂, rfl⟩, -⟩ := hm'.1
    obtain ⟨μ, hμ, hp, ho⟩ := (exists_prior_iff_minimal sem).2 hm
    obtain ⟨μ', hμ', hp', ho'⟩ := (exists_prior_iff_minimal sem).2 hm'
    exact (h w u₁ u₂ μ μ' hμ hμ' hp hp' ho ho').le.trans hm'q

-- (58a): Bar-Lev and Katzir's stability, the same for optimal messages whose meanings are not
-- atoms, is weak stability
theorem weaklyStable_iff_isOptimal [Fintype W] (atoms : Set (Set W)) :
    WeaklyStable atoms (range sem) ↔ ∀ (w : W) (u u' : U) (μ μ' : Measure W),
      IsProbabilityMeasure μ → IsProbabilityMeasure μ' → (∀ v, μ {v} ≠ 0) → (∀ v, μ' {v} ≠ 0) →
        sem u ∉ atoms → IsOptimal sem μ w u → IsOptimal sem μ' w u' → sem u = sem u' := by
  constructor
  · intro h w u u' μ μ' hμ hμ' hp hp' hua ho ho'
    have hm := (exists_prior_iff_minimal sem).1 ⟨μ, hμ, hp, ho⟩
    have hm' := (exists_prior_iff_minimal sem).1 ⟨μ', hμ', hp', ho'⟩
    rcases h w with ⟨l, hl⟩ | hat
    · have e : ∀ {x}, Minimal (· ∈ trueAnswers (range sem) w) x → x = l :=
        fun hx ↦ le_antisymm (hx.2 hl.1 (hl.2 hx.1)) (hl.2 hx.1)
      exact (e hm).trans (e hm').symm
    · exact absurd (hat _ hm) hua
  · intro h w
    by_cases hex : ∃ m, Minimal (· ∈ trueAnswers (range sem) w) m ∧ m ∉ atoms
    · obtain ⟨m, hm, hma⟩ := hex
      refine .inl ⟨m, hm.1, fun q hq ↦ ?_⟩
      obtain ⟨m', hm'q, hm'⟩ := exists_minimal_le_of_wellFoundedLT
        (· ∈ trueAnswers (range sem) w) q hq
      obtain ⟨⟨u₁, rfl⟩, -⟩ := hm.1
      obtain ⟨⟨u₂, rfl⟩, -⟩ := hm'.1
      obtain ⟨μ, hμ, hp, ho⟩ := (exists_prior_iff_minimal sem).2 hm
      obtain ⟨μ', hμ', hp', ho'⟩ := (exists_prior_iff_minimal sem).2 hm'
      exact (h w u₁ u₂ μ μ' hμ hμ' hp hp' hma ho ho').le.trans hm'q
    · push Not at hex
      exact .inr hex

-- where two independent atoms both hold, each is optimal for some prior: the speaker's choice there
-- depends on the prior, as strict stability forbids and weak stability allows
theorem exists_prior_isOptimal_atoms :
    (∃ μ : Measure (Fin 3), IsProbabilityMeasure μ ∧ (∀ v, μ {v} ≠ 0) ∧
        IsOptimal (![{0, 2}, {1, 2}] : Fin 2 → Set (Fin 3)) μ 2 0) ∧
      ∃ μ : Measure (Fin 3), IsProbabilityMeasure μ ∧ (∀ v, μ {v} ≠ 0) ∧
        IsOptimal (![{0, 2}, {1, 2}] : Fin 2 → Set (Fin 3)) μ 2 1 := by
  refine ⟨(exists_prior_iff_minimal _).2 ⟨⟨⟨0, rfl⟩, by simp⟩, ?_⟩,
    (exists_prior_iff_minimal _).2 ⟨⟨⟨1, rfl⟩, by simp⟩, ?_⟩⟩
  · rintro _ ⟨⟨k, rfl⟩, -⟩ hle
    fin_cases k
    · exact le_rfl
    · exact absurd (hle (show (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) by simp)) (by simp)
  · rintro _ ⟨⟨k, rfl⟩, -⟩ hle
    fin_cases k
    · exact absurd (hle (show (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)) (by simp)
    · exact le_rfl

end Stability

end Enguehard2025
