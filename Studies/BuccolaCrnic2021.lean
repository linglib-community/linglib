module

public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Polarity.Licenser
public import Studies.Chierchia2004
public import Linglib.Data.Examples.BuccolaCrnic2021

/-!
# Buccola and Crnič (2021): NPIs, intervention, and collectivity

This file models the Revised NPI Licensing Condition (`LicensingCondition`): a negative polarity
item is acceptable only in a sentence that is downward entailing with respect to it and that none
of its scalar alternatives entails. The condition is stated over the sentence and its
alternatives, not over the operators above the item. With *and* between *any NP* and another
plurality, the *or*-alternative entails the sentence whenever the predicate holds of the parts of
any plurality it holds of, so [conjoined *any* requires a predicate that is not
divisive](##not_div_of_licensingCondition), while [a collective predicate meets the
condition](##licensingCondition_wroteTogether). A numeral above *one*
[intervenes with a divisive predicate](##not_licensingCondition_notN) for the same reason, and a
universal quantifier over a nonempty domain [intervenes with any predicate of
individuals](##not_licensingCondition_notAll), since it entails its existential alternative.

Chierchia's Strong Application negates only the alternatives that asymmetrically entail a
sentence, so a collective conjunction under negation gets no implicature from its
*or*-alternative and stays downward entailing with respect to *any*, while exhaustification against
every alternative the sentence does not entail adds the implicature that the *or*-sentence holds
and [destroys that downward entailment](##strongApply_andNode_wroteTogether). The condition the
substrate places on the environment of a weak item, downward and not upward entailment, is the
first clause of the revised condition without the second, and
[holds of an environment that the revised condition rejects](##carries_weak_not_licensingCondition).

## Implementation notes

* Pluralities are sets of individuals, as in the paper's expository semantics, and conjunction
  forms their union. A predicate of pluralities is a function from pluralities to sets of worlds;
  it is divisive at a world when it holds of the parts of what it holds of
  (`Mereology.DIV`), which is antitonicity (`antitone_iff_forall_div`).
* The sentence is a function of the restrictor of the item, and the indefinite ranges over the
  nonempty pluralities of its restrictor. Downward entailment with respect to the item is checked
  under strengthening of the restrictor, replacing *some N* by *some N'* for `N' ⊆ N`. The scalar
  alternatives are supplied with the sentence, so restricting them to local ones is the caller's
  choice.
* The condition is necessary for acceptability; the paper also reasons from its satisfaction to
  acceptability, and `rows_licensing` pairs it with the judgments in both directions.
* Negation is complementation. The numerals' colleagues are every individual, there is a single
  paper, a numeral sentence denies that a plurality of exactly that many did it, and a numeral's
  alternatives are the other numerals from *one* up.
* The models instantiate the conjunctions of plural DPs; a judged row is read only when its
  sentence is one the models instantiate.
* The models are four individuals, two girls and two boys, with worlds recording who has a
  distributive property or which plurality did something together.

## Errata

* The interfering implicature of a collective conjunction is presented as following from
  Chierchia's (2004) core idea. It follows from the exhaustification the paper attributes to
  Chierchia (2013), not from the 2004 scalar assertion, which negates only the weakest alternative
  that asymmetrically entails the sentence; the paper's own observation is that the
  *or*-alternative of a collective conjunction does not, so on the 2004 definitions the
  implicature does not arise
  ([`strongApply_andNode_wroteTogether`](##strongApply_andNode_wroteTogether)).

## TODO

* The operator-based Revised Additional Restriction and its undergeneration and overgeneration
  under boolean, non-boolean and ambiguous conjunction; conjunctions of singular and mass DPs, whose
  *or*-alternative may be ill-formed; collective universal quantification; *always*; mixed
  predicates disambiguated to the collective reading; the movement-based accounts; the pruning
  constraints.

## References

* [buccola-crnic-2021]
* [linebarger-1987]
* [chierchia-2004]
* [chierchia-2013]
* [gajewski-2011]
-/

@[expose] public section

namespace BuccolaCrnic2021

open Set

variable {E P W : Type*}

/-! ### The Revised NPI Licensing Condition -/

/-- The Revised NPI Licensing Condition: the sentence, as a function `S` of the restrictor of the
item, is downward entailing with respect to the item at its restrictor `N` under strengthening of
the restrictor, and none of its scalar alternatives `ALT` entails it. -/
structure LicensingCondition (S : Set E → Set W) (N : Set E) (ALT : Set (Set W)) : Prop where
  /-- Replacing the item by a stronger indefinite weakens the sentence. -/
  de : ∀ ⦃N'⦄, N' ⊆ N → S N ⊆ S N'
  /-- No scalar alternative entails the sentence. -/
  not_entailed : ∀ φ ∈ ALT, ¬φ ⊆ S N

theorem antitone_iff_forall_div {VP : Set E → Set W} :
    Antitone VP ↔ ∀ w, Mereology.DIV (w ∈ VP ·) :=
  ⟨fun h _ _ _ hba ha ↦ h hba ha, fun h _ _ hab w hw ↦ h w hab hw⟩

/-! ### Conjunction -/

/-- *`G` and some `N` `VP`*: some nonempty plurality of members of `N` forms with `G` a plurality
that `VP` holds of. -/
def andSome (VP : Set E → Set W) (G N : Set E) : Set W :=
  {w | ∃ Y ⊆ N, Y.Nonempty ∧ w ∈ VP (G ∪ Y)}

/-- *`G` or some `N` `VP`*. -/
def orSome (VP : Set E → Set W) (G N : Set E) : Set W :=
  VP G ∪ {w | ∃ Y ⊆ N, Y.Nonempty ∧ w ∈ VP Y}

section Conjunction

variable {VP : Set E → Set W} {G N : Set E}

theorem monotone_andSome : Monotone (andSome VP G) := fun _ _ h _ ⟨Y, hY, hne, hw⟩ ↦
  ⟨Y, hY.trans h, hne, hw⟩

theorem monotone_orSome : Monotone (orSome VP G) := fun _ _ h _ hw ↦
  hw.imp_right fun ⟨Y, hY, hne, hw⟩ ↦ ⟨Y, hY.trans h, hne, hw⟩

-- (22a)
theorem andSome_subset_orSome (hVP : Antitone VP) : andSome VP G N ⊆ orSome VP G N :=
  fun _ ⟨_, _, _, hw⟩ ↦ Or.inl (hVP subset_union_left hw)

/-- Under negation, *any* conjoined with a plurality meets the Revised NPI Licensing Condition only
if the predicate is not divisive at some world, a weak form of (9) ((22), (25)). -/
theorem not_div_of_licensingCondition
    (h : LicensingCondition (fun N ↦ (andSome VP G N)ᶜ) N {(orSome VP G N)ᶜ}) :
    ¬∀ w, Mereology.DIV (w ∈ VP ·) := fun hVP ↦
  h.not_entailed _ rfl <|
    compl_subset_compl.2 (andSome_subset_orSome (antitone_iff_forall_div.2 hVP))

end Conjunction

/-! ### Numerals -/

/-- *I don't have `n` colleagues who `R` some `N`*: no plurality of exactly `n` individuals stands
in `R` to a member of `N`. -/
def notN (R : Set E → P → Set W) (n : ℕ) (N : Set P) : Set W :=
  {w | ¬∃ X : Set E, X.ncard = n ∧ ∃ y ∈ N, w ∈ R X y}

section Numerals

variable {R : Set E → P → Set W} {N : Set P} {m n : ℕ}

theorem notN_antitone (n : ℕ) : Antitone (notN R n) := fun _ _ h _ hw ⟨_, hX, y, hy, hR⟩ ↦
  hw ⟨_, hX, y, h hy, hR⟩

theorem notN_subset (hR : ∀ y, Antitone (R · y)) (hmn : m ≤ n) : notN R m N ⊆ notN R n N :=
  fun _ hw ⟨_, hX, y, hy, hR'⟩ ↦
    let ⟨X', hX', hc⟩ := exists_subset_card_eq (hX ▸ hmn)
    hw ⟨X', hc, y, hy, hR y hX' hR'⟩

/-- Under negation, a numeral above *one* fails the Revised NPI Licensing Condition with a
predicate divisive in its plural argument: the alternative with *one* entails the sentence ((32b),
(33)–(34)). -/
theorem not_licensingCondition_notN (hR : ∀ y w, Mereology.DIV (w ∈ R · y)) (hn : 2 ≤ n) :
    ¬LicensingCondition (notN R n) N ((notN R · N) '' {k | 1 ≤ k ∧ k ≠ n}) := fun h ↦
  h.not_entailed _ ⟨1, ⟨le_rfl, by omega⟩, rfl⟩
    (notN_subset (fun y ↦ antitone_iff_forall_div.2 (hR y)) (by omega))

end Numerals

/-! ### Universal quantifiers -/

/-- *Not all `D` `V` some `N`*. -/
def notAll (V : E → P → Set W) (D : Set E) (N : Set P) : Set W :=
  (⋂ x ∈ D, ⋃ y ∈ N, V x y)ᶜ

/-- *No `D` `V` some `N`*, the alternative of *not all*. -/
def notSome (V : E → P → Set W) (D : Set E) (N : Set P) : Set W :=
  (⋃ x ∈ D, ⋃ y ∈ N, V x y)ᶜ

/-- A universal quantifier over a nonempty domain fails the Revised NPI Licensing Condition with a
predicate of individuals: its existential alternative entails the sentence ((37a), (38)). -/
theorem not_licensingCondition_notAll {V : E → P → Set W} {D : Set E} {N : Set P}
    (hD : D.Nonempty) : ¬LicensingCondition (notAll V D) N {notSome V D N} := fun h ↦
  h.not_entailed _ rfl fun _ hw hall ↦
    let ⟨x, hx⟩ := hD
    hw (mem_biUnion hx (mem_iInter₂.1 hall x hx))

/-! ### The models -/

/-- The girls, individuals `0` and `1`. -/
def girls : Set (Fin 4) := {0, 1}

/-- The boys, individuals `2` and `3`. -/
def boys : Set (Fin 4) := {2, 3}

/-- *`X` have blue eyes*, at a world recording who has blue eyes. -/
def haveBlueEyes (X : Set (Fin 4)) : Set (Set (Fin 4)) := {w | X ⊆ w}

/-- *`X` wrote a paper together*, at a world recording the plurality that wrote one together. -/
def wroteTogether (X : Set (Fin 4)) : Set (Set (Fin 4)) := {w | w = X}

theorem antitone_haveBlueEyes : Antitone haveBlueEyes := fun _ _ h _ hw ↦ h.trans hw

theorem girls_union_boys : girls ∪ boys = univ := by
  ext x; fin_cases x <;> simp [girls, boys]

theorem not_mem_boys_of_mem_girls {x : Fin 4} (hx : x ∈ girls) : x ∉ boys := by
  simp only [girls, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [boys]

-- (26)–(28)
theorem not_licensingCondition_haveBlueEyes :
    ¬LicensingCondition (fun N ↦ (andSome haveBlueEyes girls N)ᶜ) boys
      {(orSome haveBlueEyes girls boys)ᶜ} :=
  fun h ↦ not_div_of_licensingCondition h (antitone_iff_forall_div.1 antitone_haveBlueEyes)

-- the plural counterpart of (4)
theorem licensingCondition_orSome_haveBlueEyes :
    LicensingCondition (fun N ↦ (orSome haveBlueEyes girls N)ᶜ) boys
      {(andSome haveBlueEyes girls boys)ᶜ} := by
  refine ⟨fun _ hN ↦ compl_subset_compl.2 (monotone_orSome hN), ?_⟩
  rintro _ rfl h
  have hw : girls ∈ (andSome haveBlueEyes girls boys)ᶜ := fun ⟨_, hY, ⟨y, hy⟩, hw⟩ ↦
    not_mem_boys_of_mem_girls (hw (Or.inr hy)) (hY hy)
  exact h hw (Or.inl (subset_refl girls))

theorem univ_mem_andSome_wroteTogether : univ ∈ andSome wroteTogether girls boys :=
  ⟨boys, subset_rfl, ⟨2, by simp [boys]⟩, girls_union_boys.symm⟩

theorem univ_not_mem_orSome_wroteTogether : univ ∉ orSome wroteTogether girls boys := by
  rintro (hg | ⟨Y, hY, -, hw⟩)
  · exact absurd (hg ▸ mem_univ (2 : Fin 4)) (by simp [girls])
  · exact absurd (hY (hw ▸ mem_univ (0 : Fin 4))) (by simp [boys])

theorem girls_nonempty : girls.Nonempty := ⟨0, by simp [girls]⟩

theorem girls_not_mem_andSome_wroteTogether {N : Set (Fin 4)} (hN : N ⊆ boys) :
    girls ∉ andSome wroteTogether girls N := fun ⟨_, hY, ⟨_, hy⟩, hw⟩ ↦
  not_mem_boys_of_mem_girls ((hw : girls = girls ∪ _) ▸ Or.inr hy) (hN (hY hy))

theorem singleton_three_not_mem_andSome_wroteTogether {N : Set (Fin 4)} :
    ({3} : Set (Fin 4)) ∉ andSome wroteTogether girls N := fun ⟨Y, _, _, hY⟩ ↦
  absurd ((hY : ({3} : Set (Fin 4)) = girls ∪ Y) ▸ Or.inl (by simp [girls]) :
    (0 : Fin 4) ∈ ({3} : Set (Fin 4))) (by simp)

-- (29)–(31)
theorem licensingCondition_wroteTogether :
    LicensingCondition (fun N ↦ (andSome wroteTogether girls N)ᶜ) boys
      {(orSome wroteTogether girls boys)ᶜ} := by
  refine ⟨fun _ hN ↦ compl_subset_compl.2 (monotone_andSome hN), ?_⟩
  rintro _ rfl h
  exact h univ_not_mem_orSome_wroteTogether univ_mem_andSome_wroteTogether

/-- *`X` read the paper*, at a world recording who read it. -/
def readPaper (X : Set (Fin 4)) (_ : Unit) : Set (Set (Fin 4)) := {w | X ⊆ w}

/-- *`X` wrote the paper together*, at a world recording the plurality that wrote it together. -/
def wrotePaperTogether (X : Set (Fin 4)) (_ : Unit) : Set (Set (Fin 4)) := {w | w = X}

-- (32b), (33)–(34)
theorem not_licensingCondition_readPaper :
    ¬LicensingCondition (notN readPaper 4) univ
      ((notN readPaper · univ) '' {k | 1 ≤ k ∧ k ≠ 4}) :=
  not_licensingCondition_notN (fun _ w _ _ hba ha ↦ hba.trans ha) (by norm_num)

-- (32c), (35)–(36)
theorem licensingCondition_wrotePaperTogether :
    LicensingCondition (notN wrotePaperTogether 4) univ
      ((notN wrotePaperTogether · univ) '' {k | 1 ≤ k ∧ k ≠ 4}) := by
  refine ⟨fun _ hN ↦ notN_antitone 4 hN, ?_⟩
  rintro _ ⟨k, ⟨-, hk⟩, rfl⟩ h
  have hu : (univ : Set (Fin 4)).ncard = 4 := by simp
  refine h (a := univ) (fun ⟨X, hX, _, _, hw⟩ ↦ hk ?_) ⟨univ, hu, (), trivial, rfl⟩
  rw [← hX, ← (hw : univ = X), hu]

-- (32a)
theorem licensingCondition_readPaper_one :
    LicensingCondition (notN readPaper 1) univ
      ((notN readPaper · univ) '' {k | 1 ≤ k ∧ k ≠ 1}) := by
  refine ⟨fun _ hN ↦ notN_antitone 1 hN, ?_⟩
  rintro _ ⟨k, ⟨hk1, hk⟩, rfl⟩ h
  refine h (a := {0}) (fun ⟨X, hX, _, _, hw⟩ ↦ ?_)
    ⟨{0}, ncard_singleton 0, (), trivial, show ({0} : Set (Fin 4)) ⊆ {0} from subset_rfl⟩
  have := ncard_le_ncard (hw : X ⊆ {0})
  rw [hX, ncard_singleton] at this
  omega

/-- *`x` did the homework*, at a world recording who did it. -/
def didHomework (x : Fin 4) (_ : Unit) : Set (Set (Fin 4)) := {w | x ∈ w}

-- (37a)
theorem not_licensingCondition_didHomework :
    ¬LicensingCondition (notAll didHomework univ) univ {notSome didHomework univ univ} :=
  not_licensingCondition_notAll ⟨0, trivial⟩

/-! ### Chierchia's Strong Application and exhaustification -/

open Chierchia2004 (doubt mem_doubt_strongApply_strong)

/-- The node *`G` and some `N` `VP`* with the scale of *and*, its *or*-alternative. -/
def andNode (VP : Set E → Set W) (G N : Set E) : Chierchia2004.Meaning (Set W) :=
  .lexical (andSome VP G N) {andSome VP G N, orSome VP G N}

section Exhaustification

variable {VP : Set E → Set W} {G N : Set E}

theorem strongApply_andNode_of_not_subset (h : ¬andSome VP G N ⊆ orSome VP G N) :
    (doubt.strongApply (andNode VP G N)).strong = (andSome VP G N)ᶜ := by
  ext v
  rw [mem_doubt_strongApply_strong]
  simp only [andNode, Chierchia2004.Meaning.lexical, forall_mem_insert, mem_singleton_iff,
    forall_eq]
  exact ⟨fun h' ↦ h'.1, fun hv ↦ ⟨hv, fun h' ↦ (h'.2 h'.1).elim, fun h' ↦ (h h'.1).elim⟩⟩

-- (48)
theorem strongApply_andNode_of_ssubset (h : andSome VP G N ⊂ orSome VP G N) :
    (doubt.strongApply (andNode VP G N)).strong = (andSome VP G N)ᶜ ∩ orSome VP G N := by
  ext v
  rw [mem_doubt_strongApply_strong]
  simp only [andNode, Chierchia2004.Meaning.lexical, forall_mem_insert, mem_singleton_iff,
    forall_eq]
  exact ⟨fun h' ↦ ⟨h'.1, h'.2.2 h⟩, fun hv ↦ ⟨hv.1, fun h' ↦ (h'.2 h'.1).elim, fun _ ↦ hv.2⟩⟩

-- (49)
theorem exh_andNode (h : ¬orSome VP G N ⊆ andSome VP G N) :
    Exhaustification.exh {(orSome VP G N)ᶜ} (andSome VP G N)ᶜ =
      (andSome VP G N)ᶜ ∩ orSome VP G N := by
  ext v
  simp only [Exhaustification.mem_exh, mem_singleton_iff, forall_eq, mem_inter_iff]
  exact and_congr_right fun _ ↦ ⟨fun h' ↦ by_contra fun hv ↦ h (compl_subset_compl.1 (h' hv)),
    fun hv h' ↦ (h' hv).elim⟩

end Exhaustification

theorem strongApply_andNode_eq_of_nonempty {N : Set (Fin 4)} (hN : N.Nonempty) (hNb : N ⊆ boys) :
    (doubt.strongApply (andNode wroteTogether girls N)).strong = (andSome wroteTogether girls N)ᶜ :=
  strongApply_andNode_of_not_subset fun h ↦ by
    obtain ⟨y, hy⟩ := hN
    have hw : girls ∪ {y} ∈ andSome wroteTogether girls N :=
      ⟨{y}, singleton_subset_iff.2 hy, singleton_nonempty y, rfl⟩
    rcases h hw with hg | ⟨Y, hY, -, hYw⟩
    · exact not_mem_boys_of_mem_girls ((hg : girls ∪ {y} = girls) ▸ Or.inr rfl) (hNb hy)
    · exact not_mem_boys_of_mem_girls (show (0 : Fin 4) ∈ girls by simp [girls])
        (hNb (hY ((hYw : girls ∪ {y} = Y) ▸ Or.inl (show (0 : Fin 4) ∈ girls by simp [girls]))))

-- (49)
theorem exh_andNode_wroteTogether :
    Exhaustification.exh {(orSome wroteTogether girls boys)ᶜ}
        (andSome wroteTogether girls boys)ᶜ =
      (andSome wroteTogether girls boys)ᶜ ∩ orSome wroteTogether girls boys :=
  exh_andNode fun h ↦ girls_not_mem_andSome_wroteTogether subset_rfl (h (Or.inl rfl))

-- UNVERIFIED: the 2004 scalar assertion is checked against the circulated manuscript, not the
-- published chapter the paper cites.
/-- Under negation, strengthening *any boys* to *boy `2`* in *the girls and any boys wrote a paper
together* weakens the sentence under Chierchia's Strong Application, which adds no implicature, but
not under exhaustification against every alternative the sentence does not entail, whose
implicature that the girls or some boys wrote one destroys the downward entailment ((49)). -/
theorem strongApply_andNode_wroteTogether :
    (doubt.strongApply (andNode wroteTogether girls boys)).strong ⊆
        (doubt.strongApply (andNode wroteTogether girls {2})).strong ∧
      ¬Exhaustification.exh {(orSome wroteTogether girls boys)ᶜ}
          (andSome wroteTogether girls boys)ᶜ ⊆
        Exhaustification.exh {(orSome wroteTogether girls {2})ᶜ}
          (andSome wroteTogether girls {2})ᶜ := by
  have h2 : ({2} : Set (Fin 4)) ⊆ boys := by simp [boys]
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [strongApply_andNode_eq_of_nonempty ⟨2, by simp [boys]⟩ subset_rfl,
      strongApply_andNode_eq_of_nonempty (singleton_nonempty 2) h2]
    exact compl_subset_compl.2 (monotone_andSome h2)
  · rw [exh_andNode_wroteTogether, exh_andNode fun h' ↦
      girls_not_mem_andSome_wroteTogether h2 (h' (Or.inl rfl))] at h
    -- boy `3` alone wrote a paper
    rcases (h ⟨singleton_three_not_mem_andSome_wroteTogether,
      Or.inr ⟨{3}, by simp [boys], singleton_nonempty 3, rfl⟩⟩).2 with hg | ⟨Y, hY, -, hw⟩
    · exact absurd ((hg : ({3} : Set (Fin 4)) = girls) ▸ mem_singleton (3 : Fin 4))
        (by simp [girls])
    · exact absurd (hY ((hw : ({3} : Set (Fin 4)) = Y) ▸ mem_singleton (3 : Fin 4))) (by simp)

/-! ### Clause (i) without clause (ii) -/

/-- The environment of (26), *I don't think that the girls and some `N` have blue eyes*, as an
operator on the restrictor of the item. -/
def haveBlueEyesEnvironment : PolarityItem.Licenser :=
  .classical
    { Param := PUnit.{2}
      Dom := fun _ ↦ Set (Fin 4)
      Cod := fun _ ↦ Set (Set (Fin 4))
      op := fun _ N ↦ (andSome haveBlueEyes girls N)ᶜ }

/-- The environment of (26) meets the substrate's condition on a weak item, downward and not upward
entailment, which is the first clause of the Revised NPI Licensing Condition without the second,
though it fails the revised condition. -/
theorem carries_weak_not_licensingCondition :
    haveBlueEyesEnvironment.Carries .weak ∧
      ¬LicensingCondition (fun N ↦ (andSome haveBlueEyes girls N)ᶜ) boys
        {(orSome haveBlueEyes girls boys)ᶜ} := by
  refine ⟨⟨fun _ _ _ h ↦ compl_subset_compl.2 (monotone_andSome h), fun h ↦ ?_⟩,
    not_licensingCondition_haveBlueEyes⟩
  have := h PUnit.unit (empty_subset boys)
    (show univ ∈ (andSome haveBlueEyes girls ∅)ᶜ from fun ⟨_, hY, ⟨_, hy⟩, _⟩ ↦ hY hy)
  exact this ⟨boys, subset_rfl, ⟨2, by simp [boys]⟩, subset_univ _⟩

/-! ### The judgments -/

/-- The Revised NPI Licensing Condition for the model of a row, read from its intervener, the number
of its conjoined DPs and the class of its predicate, for the sentences the models instantiate. -/
def licensing? (e : Datum) : Option Prop :=
  match e.feature? "coordination", e.feature? "number", e.feature? "numeral",
    e.feature? "quantifier", e.feature? "predicate" with
  | some "and", some "plural", none, none, some "distributive" => some <|
      LicensingCondition (fun N ↦ (andSome haveBlueEyes girls N)ᶜ) boys
        {(orSome haveBlueEyes girls boys)ᶜ}
  | some "and", some "plural", none, none, some "collective" => some <|
      LicensingCondition (fun N ↦ (andSome wroteTogether girls N)ᶜ) boys
        {(orSome wroteTogether girls boys)ᶜ}
  | none, none, some "one", none, some "distributive" => some <|
      LicensingCondition (notN readPaper 1) univ
        ((notN readPaper · univ) '' {k | 1 ≤ k ∧ k ≠ 1})
  | none, none, some "four", none, some "distributive" => some <|
      LicensingCondition (notN readPaper 4) univ
        ((notN readPaper · univ) '' {k | 1 ≤ k ∧ k ≠ 4})
  | none, none, some "four", none, some "collective" => some <|
      LicensingCondition (notN wrotePaperTogether 4) univ
        ((notN wrotePaperTogether · univ) '' {k | 1 ≤ k ∧ k ≠ 4})
  | none, none, none, some "all", none => some <|
      LicensingCondition (notAll didHomework univ) univ {notSome didHomework univ univ}
  | _, _, _, _, _ => none

theorem rows_licensing : ∀ e ∈ Examples.all, ∀ p ∈ licensing? e,
    (e.judgment.band = .accepted ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro p ⟨⟩ <;>
    first
      | exact iff_of_false (by decide) not_licensingCondition_haveBlueEyes
      | exact iff_of_true rfl licensingCondition_wroteTogether
      | exact iff_of_true rfl licensingCondition_readPaper_one
      | exact iff_of_false (by decide) not_licensingCondition_readPaper
      | exact iff_of_true rfl licensingCondition_wrotePaperTogether
      | exact iff_of_false (by decide) not_licensingCondition_didHomework

theorem readCount_licensing : Datum.ReadCount licensing? Examples.all 6 := by
  decide +kernel

end BuccolaCrnic2021
