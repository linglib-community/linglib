module

public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Polarity.Licenser
public import Linglib.Semantics.Polarity.Environment
public import Studies.Chierchia2004
public import Linglib.Data.Examples.BuccolaCrnic2021

/-!
# Buccola and Crnič (2021): NPIs, intervention, and collectivity

This file models the Revised NPI Licensing Condition (`LicensingCondition`): a negative polarity
item is acceptable only in a sentence that is downward entailing with respect to it and that none
of its scalar alternatives entails, so that the sentence is a strongest of its alternatives. The
condition is stated over a constituent with its alternatives (`WithAlternatives`), not over the
operators above the item, and [some constituent containing the item must meet it](##Licensed).
In the models the clause below negation is upward entailing with respect to the item, so [the
condition falls on the negated sentence](##licensed_negated_iff). Under negation it asks that the
positive sentence be a weakest of its alternatives
([`licensingCondition_compl_iff`](##licensingCondition_compl_iff)), the sentence-level
counterpart of a scalar term at the bottom of its scale.

With *and* between *any NP* and another plurality, the *or*-alternative entails the sentence
whenever the predicate holds of the parts of any plurality it holds of, so [conjoined *any*
requires a predicate that is not divisive](##not_div_of_licensingCondition), while
[a collective predicate meets the condition](##licensingCondition_sentence29). A numeral above
*one* [intervenes with a divisive predicate](##not_licensingCondition_numeral) for the same
reason, and a universal quantifier over a nonempty domain
[intervenes with any predicate of individuals](##not_licensingCondition_every), since it entails
its existential alternative.

Under *doubt*, the sentence is a strongest of its alternatives exactly when Chierchia's Strong
Application [gives it no implicature](##minimal_iff_strongApply_doubt). Strong Application
negates only the alternatives that asymmetrically entail a sentence, so a collective conjunction
stays downward entailing with respect to *any*, while exhaustification against every alternative
the sentence does not entail
[destroys that downward entailment](##strongApply_andNode_wroteTogether).
The condition the substrate places on the environment of a weak item, downward and not upward
entailment, is the first clause of the revised condition without the second, and
[holds of an environment that the revised condition rejects](##carries_weak_not_licensingCondition).

## Implementation notes

* Pluralities form a join semilattice with a bottom, conjunction is the join, and the indefinite
  ranges over the nonzero parts of its restrictor; the models take the finite sets of individuals.
  A predicate of pluralities is divisive at a world when it holds of the parts of what it holds of
  (`Mereology.DIV`), which is antitonicity (`antitone_iff_forall_div`).
* Downward entailment with respect to the item is checked under strengthening of its restrictor.
  The scalar alternatives come with the sentence, so restricting them to local ones is the
  caller's choice, and an alternative equivalent to the sentence does not entail it in the sense
  of the condition.
* The constituents containing the item are the domains of a path (`PolarityItem.Path`), whose
  layers apply to the alternatives of the clause. Each model's clause is upward entailing in the
  restrictor and empty at its bottom, so no clause without the negation meets the condition.
* The condition is necessary for acceptability; the paper also reasons from its satisfaction to
  acceptability, and `rows_licensing` pairs it with the judgments in both directions.
* Negation is complementation. A numeral sentence asserts a plurality of exactly that many, and a
  numeral's alternatives are the numerals from *one* up. The universal and existential
  determiners are the substrate's.
* The models instantiate the conjunctions of plural DPs; a judged row is read only when its
  sentence is one the models instantiate.

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

universe u

variable {α E P : Type*} {W : Type u}

/-! ### The Revised NPI Licensing Condition -/

/-- The Revised NPI Licensing Condition at the restrictor `n` of the item, for a sentence `S` given
as a function of that restrictor together with its scalar alternatives. -/
structure LicensingCondition [Preorder α] (S : α → WithAlternatives (Set W)) (n : α) : Prop where
  /-- Strengthening the restrictor of the item weakens the sentence. -/
  de : ∀ ⦃n'⦄, n' ≤ n → (S n).ordinary ⊆ (S n').ordinary
  /-- No scalar alternative entails the sentence: it is a strongest of its alternatives. -/
  minimal : Minimal (· ∈ (S n).alternatives) (S n).ordinary

theorem alternatives_compl (m : WithAlternatives (Set W)) :
    (compl <$> m).alternatives = compl '' m.alternatives := by
  ext; simp

theorem minimal_compl_iff {m : WithAlternatives (Set W)} :
    Minimal (· ∈ (compl <$> m).alternatives) (compl <$> m).ordinary ↔
      Maximal (· ∈ m.alternatives) m.ordinary := by
  simp only [alternatives_compl, WithAlternatives.ordinary_map, Minimal, Maximal,
    compl_injective.mem_set_image, forall_mem_image, compl_le_compl_iff_le]

-- under negation: the positive sentence is monotone in the restrictor and a weakest alternative
theorem licensingCondition_compl_iff [Preorder α] {T : α → WithAlternatives (Set W)} {n : α} :
    LicensingCondition (compl <$> T ·) n ↔
      (∀ ⦃n'⦄, n' ≤ n → (T n').ordinary ⊆ (T n).ordinary) ∧
        Maximal (· ∈ (T n).alternatives) (T n).ordinary := by
  refine ⟨fun ⟨hde, hmin⟩ ↦ ⟨fun _ h ↦ compl_subset_compl.1 (hde h), minimal_compl_iff.1 hmin⟩,
    fun ⟨hmono, hmax⟩ ↦ ⟨fun _ h ↦ compl_subset_compl.2 (hmono h), minimal_compl_iff.2 hmax⟩⟩

theorem maximal_pair_iff {p q : Set W} :
    Maximal (· ∈ ({p, q} : Set (Set W))) p ↔ (p ⊆ q → q ⊆ p) := by
  simp [Maximal]

theorem antitone_iff_forall_div [Preorder α] {VP : α → Set W} :
    Antitone VP ↔ ∀ w, Mereology.DIV (w ∈ VP ·) :=
  ⟨fun h _ _ _ hba ha ↦ h hba ha, fun h _ _ hab w hw ↦ h w hab hw⟩

theorem not_licensingCondition_of_monotone [Preorder α] {S : α → WithAlternatives (Set W)}
    {n n' : α} (hS : Monotone fun x ↦ (S x).ordinary) (h : n' ≤ n)
    (hne : (S n').ordinary ≠ (S n).ordinary) : ¬LicensingCondition S n := fun hc ↦
  hne (le_antisymm (hS h) (hc.de h))

/-! ### Domains -/

section Domains

open PolarityItem NaturalLogic

variable [Lattice α] [BoundedOrder α]

/-- The Revised NPI Licensing Condition over the domains of the item: some domain, with the
alternatives `A` of the minimal domain carried through the layers below it, meets the
condition. -/
def Licensed (p : Path α (Set W)) (A : α → Set (Set W)) (n : α) : Prop :=
  ∃ t ∈ p.layers.tails, LicensingCondition (p.withAlternatives A t) n

/-- The path of the item in a clause `S` monotone in its restrictor, under negation. -/
def negated (S : α → WithAlternatives (Set W)) (hS : Monotone fun x ↦ (S x).ordinary) :
    Path α (Set W) :=
  ⟨fun x ↦ (S x).ordinary, .mono, Signature.holdsFor_mono_iff.2 hS, [negation]⟩

-- a clause below negation that is not constant below the restrictor does not meet the condition
theorem licensed_negated_iff {S : α → WithAlternatives (Set W)}
    {hS : Monotone fun x ↦ (S x).ordinary} {n n' : α} (h : n' ≤ n)
    (hne : (S n').ordinary ≠ (S n).ordinary) :
    Licensed (negated S hS) (WithAlternatives.alternatives ∘ S) n ↔
      LicensingCondition (compl <$> S ·) n := by
  have h0 : (negated S hS).withAlternatives (WithAlternatives.alternatives ∘ S) [] = S :=
    funext fun _ ↦ by simp [negated]
  have h1 : (negated S hS).withAlternatives (WithAlternatives.alternatives ∘ S) [negation] =
      (compl <$> S ·) :=
    funext fun _ ↦ by simp [negated, negation]
  refine ⟨fun ⟨t, ht, hc⟩ ↦ ?_, fun hc ↦ ⟨[negation], by simp [negated], h1 ▸ hc⟩⟩
  simp [negated] at ht
  rcases ht with rfl | rfl
  · exact h1 ▸ hc
  · exact absurd (h0 ▸ hc) (not_licensingCondition_of_monotone hS h hne)

theorem licensed_negated_iff_of_eq_empty {S : α → WithAlternatives (Set W)}
    {hS : Monotone fun x ↦ (S x).ordinary} {n : α} (hbot : (S ⊥).ordinary = ∅)
    (hn : (S n).ordinary.Nonempty) :
    Licensed (negated S hS) (WithAlternatives.alternatives ∘ S) n ↔
      LicensingCondition (compl <$> S ·) n :=
  licensed_negated_iff bot_le (hbot ▸ hn.ne_empty.symm)

end Domains

/-! ### Conjunction -/

section Conjunction

variable [SemilatticeSup α] [OrderBot α] {VP : α → Set W} {g n : α}

/-- *`g` and some `n` `VP`*: some nonzero part of `n` forms with `g` a plurality that `VP` holds
of. -/
def andSome (VP : α → Set W) (g n : α) : Set W :=
  {w | ∃ y ≤ n, y ≠ ⊥ ∧ w ∈ VP (g ⊔ y)}

/-- *`g` or some `n` `VP`*. -/
def orSome (VP : α → Set W) (g n : α) : Set W :=
  VP g ∪ {w | ∃ y ≤ n, y ≠ ⊥ ∧ w ∈ VP y}

/-- *`g` and some `n` `VP`* with its *or*-alternative, the scale of *and*. -/
def conj (VP : α → Set W) (g n : α) : WithAlternatives (Set W) :=
  ⟨andSome VP g n, {andSome VP g n, orSome VP g n}⟩

/-- *`g` or some `n` `VP`* with its *and*-alternative. -/
def disj (VP : α → Set W) (g n : α) : WithAlternatives (Set W) :=
  ⟨orSome VP g n, {orSome VP g n, andSome VP g n}⟩

theorem monotone_andSome : Monotone (andSome VP g) := fun _ _ h _ ⟨y, hy, hne, hw⟩ ↦
  ⟨y, hy.trans h, hne, hw⟩

theorem andSome_bot (VP : α → Set W) (g : α) : andSome VP g ⊥ = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, hy, hne, _⟩ ↦ hne (le_bot_iff.1 hy)

theorem monotone_orSome : Monotone (orSome VP g) := fun _ _ h _ hw ↦
  hw.imp_right fun ⟨y, hy, hne, hw⟩ ↦ ⟨y, hy.trans h, hne, hw⟩

-- (22a)
theorem andSome_subset_orSome (hVP : Antitone VP) : andSome VP g n ⊆ orSome VP g n :=
  fun _ ⟨_, _, _, hw⟩ ↦ Or.inl (hVP le_sup_left hw)

theorem licensingCondition_conj_iff :
    LicensingCondition (compl <$> conj VP g ·) n ↔
      (andSome VP g n ⊆ orSome VP g n → orSome VP g n ⊆ andSome VP g n) :=
  licensingCondition_compl_iff.trans
    ⟨fun h ↦ maximal_pair_iff.1 h.2, fun h ↦ ⟨fun _ h' ↦ monotone_andSome h', maximal_pair_iff.2 h⟩⟩

theorem licensingCondition_disj_iff :
    LicensingCondition (compl <$> disj VP g ·) n ↔
      (orSome VP g n ⊆ andSome VP g n → andSome VP g n ⊆ orSome VP g n) :=
  licensingCondition_compl_iff.trans
    ⟨fun h ↦ maximal_pair_iff.1 h.2, fun h ↦ ⟨fun _ h' ↦ monotone_orSome h', maximal_pair_iff.2 h⟩⟩

/-- Under negation, *any* conjoined with a plurality meets the Revised NPI Licensing Condition only
if the predicate is not divisive at some world, unless the *or*-sentence entails the
*and*-sentence; this is a weak form of (9) ((22), (25)). -/
theorem not_div_of_licensingCondition (h : LicensingCondition (compl <$> conj VP g ·) n)
    (hor : ¬orSome VP g n ⊆ andSome VP g n) : ¬∀ w, Mereology.DIV (w ∈ VP ·) := fun hVP ↦
  hor (licensingCondition_conj_iff.1 h (andSome_subset_orSome (antitone_iff_forall_div.2 hVP)))

end Conjunction

/-! ### Numerals -/

section Numerals

variable {R : Finset E → P → Set W} {N : Set P} {m n : ℕ}

/-- *`n` individuals `R` some `N`*: a plurality of exactly `n` individuals stands in `R` to a member
of `N`. -/
def someN (R : Finset E → P → Set W) (n : ℕ) (N : Set P) : Set W :=
  {w | ∃ X : Finset E, X.card = n ∧ ∃ y ∈ N, w ∈ R X y}

/-- *`n` individuals `R` some `N`* with the other numerals from *one* up as alternatives. -/
def numeral (R : Finset E → P → Set W) (n : ℕ) (N : Set P) : WithAlternatives (Set W) :=
  ⟨someN R n N, (someN R · N) '' Ici 1⟩

theorem monotone_someN (n : ℕ) : Monotone (someN R n) := fun _ _ h _ ⟨X, hX, y, hy, hR⟩ ↦
  ⟨X, hX, y, h hy, hR⟩

theorem someN_empty (R : Finset E → P → Set W) (n : ℕ) : someN R n ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, _, _, hy, _⟩ ↦ hy

theorem someN_subset (hR : ∀ y, Antitone (R · y)) (hmn : m ≤ n) : someN R n N ⊆ someN R m N :=
  fun _ ⟨_, hX, y, hy, hR'⟩ ↦
    let ⟨X', hX', hc⟩ := Finset.exists_subset_card_eq (hX ▸ hmn)
    ⟨X', hc, y, hy, hR y hX' hR'⟩

/-- Under negation, a numeral above *one* fails the Revised NPI Licensing Condition with a
predicate divisive in its plural argument, unless the sentence with *one* entails the sentence:
the alternative with *one* entails it ((32b), (33)–(34)). -/
theorem not_licensingCondition_numeral (hR : ∀ y w, Mereology.DIV (w ∈ R · y)) (hn : 1 ≤ n)
    (hne : ¬someN R 1 N ⊆ someN R n N) : ¬LicensingCondition (compl <$> numeral R n ·) N :=
  fun h ↦ hne ((licensingCondition_compl_iff.1 h).2.2 ⟨1, mem_Ici.2 le_rfl, rfl⟩
    (someN_subset (fun y ↦ antitone_iff_forall_div.2 (hR y)) hn))

end Numerals

/-! ### Universal quantifiers -/

section Universal

open Quantifier

variable {V : E → P → Set W} {D : Set E} {N : Set P}

/-- *Every `D` `V` some `N`* with its existential alternative, the scale of *some* and *every*. -/
def every (V : E → P → Set W) (D : Set E) (N : Set P) : WithAlternatives (Set W) :=
  ⟨{w | Det.every D {x | ∃ y ∈ N, w ∈ V x y}},
    {{w | Det.every D {x | ∃ y ∈ N, w ∈ V x y}}, {w | Det.some D {x | ∃ y ∈ N, w ∈ V x y}}}⟩

theorem monotone_every (V : E → P → Set W) (D : Set E) :
    Monotone fun N ↦ (every V D N).ordinary := fun _ _ h _ hw _ hx ↦
  let ⟨y, hy, hV⟩ := hw hx
  ⟨y, h hy, hV⟩

theorem not_licensingCondition_every (hD : D.Nonempty)
    (hne : ¬{w | Det.some D {x | ∃ y ∈ N, w ∈ V x y}} ⊆
      {w | Det.every D {x | ∃ y ∈ N, w ∈ V x y}}) :
    ¬LicensingCondition (compl <$> every V D ·) N := fun h ↦
  hne (maximal_pair_iff.1 (licensingCondition_compl_iff.1 h).2 fun _ ↦ Det.subalternation_a_i hD)

end Universal

/-! ### The models -/

/-- The girls, individuals `0` and `1`. -/
def girls : Finset (Fin 4) := {0, 1}

/-- The boys, individuals `2` and `3`. -/
def boys : Finset (Fin 4) := {2, 3}

/-- *`X` have blue eyes*, at a world recording who has blue eyes. -/
def haveBlueEyes (X : Finset (Fin 4)) : Set (Finset (Fin 4)) := {w | X ⊆ w}

/-- *`X` wrote a paper together*, at a world recording the plurality that wrote one together. -/
def wroteTogether (X : Finset (Fin 4)) : Set (Finset (Fin 4)) := {w | w = X}

/-- (26) *I don't think that the girls and any boys have blue eyes*. -/
def sentence26 (n : Finset (Fin 4)) : WithAlternatives (Set (Finset (Fin 4))) :=
  compl <$> conj haveBlueEyes girls n

/-- (29) *I don't think that the girls and any boys have ever written a paper together*. -/
def sentence29 (n : Finset (Fin 4)) : WithAlternatives (Set (Finset (Fin 4))) :=
  compl <$> conj wroteTogether girls n

theorem antitone_haveBlueEyes : Antitone haveBlueEyes := fun _ _ h _ hw ↦ h.trans hw

-- (26)–(28)
theorem not_licensingCondition_sentence26 : ¬LicensingCondition sentence26 boys :=
  fun h ↦ not_div_of_licensingCondition h
    (fun h' ↦ absurd (h' (Or.inl (subset_refl girls))) (by
      simp only [andSome, haveBlueEyes, girls, boys, mem_ofPred_eq]; decide))
    (antitone_iff_forall_div.1 antitone_haveBlueEyes)

-- the plural counterpart of (4)
theorem licensingCondition_disj_haveBlueEyes :
    LicensingCondition (compl <$> disj haveBlueEyes girls ·) boys :=
  licensingCondition_disj_iff.2 fun h ↦ absurd (h (Or.inl (subset_refl girls))) (by
    simp only [andSome, haveBlueEyes, girls, boys, mem_ofPred_eq]; decide)

-- (29)–(31)
theorem licensingCondition_sentence29 : LicensingCondition sentence29 boys :=
  licensingCondition_conj_iff.2 fun h ↦ absurd (h (a := .univ) (by
    simp only [andSome, wroteTogether, girls, boys, mem_ofPred_eq]; decide)) (by
    simp only [orSome, wroteTogether, girls, boys, mem_union, mem_ofPred_eq]; decide)

/-- *`X` read paper `y`*, at a world recording who read which paper. -/
def readPaper (X : Finset (Fin 4)) (y : Fin 2) : Set (Finset (Fin 4 × Fin 2)) :=
  {w | ∀ x ∈ X, (x, y) ∈ w}

/-- *`X` wrote paper `y` together*, at a world recording the plurality that wrote a paper together
and the paper. -/
def wrotePaperTogether (X : Finset (Fin 4)) (y : Fin 2) : Set (Finset (Fin 4) × Fin 2) :=
  {w | w = (X, y)}

/-- *`x` did homework `y`*, at a world recording who did which homework. -/
def didHomework (x : Fin 4) (y : Fin 2) : Set (Finset (Fin 4 × Fin 2)) := {w | (x, y) ∈ w}

/-- (32a) *I don't have one colleague who has read any paper of mine*. -/
def sentence32a (N : Set (Fin 2)) : WithAlternatives (Set (Finset (Fin 4 × Fin 2))) :=
  compl <$> numeral readPaper 1 N

/-- (32b) *I don't have four colleagues who have read any paper of mine*. -/
def sentence32b (N : Set (Fin 2)) : WithAlternatives (Set (Finset (Fin 4 × Fin 2))) :=
  compl <$> numeral readPaper 4 N

/-- (32c) *I don't have four colleagues who have written any paper together*. -/
def sentence32c (N : Set (Fin 2)) : WithAlternatives (Set (Finset (Fin 4) × Fin 2)) :=
  compl <$> numeral wrotePaperTogether 4 N

/-- (37a) *Not all students did any homework*. -/
def sentence37a (N : Set (Fin 2)) : WithAlternatives (Set (Finset (Fin 4 × Fin 2))) :=
  compl <$> every didHomework univ N

theorem div_readPaper (y : Fin 2) (w : Finset (Fin 4 × Fin 2)) :
    Mereology.DIV (w ∈ readPaper · y) :=
  fun _ _ hba ha x hx ↦ ha x (hba hx)

-- (32b), (33)–(34)
theorem not_licensingCondition_sentence32b : ¬LicensingCondition sentence32b univ :=
  not_licensingCondition_numeral div_readPaper (by norm_num) fun h ↦ by
    obtain ⟨X, hX, y, -, hw⟩ := h (a := {(0, 0)}) ⟨{0}, rfl, 0, trivial, by simp [readPaper]⟩
    have hX0 : X ⊆ {0} := fun x hx ↦
      Finset.mem_singleton.2 (Prod.ext_iff.1 (Finset.mem_singleton.1 (hw x hx))).1
    have := Finset.card_le_card hX0
    simp [hX] at this

-- (32a)
theorem licensingCondition_sentence32a : LicensingCondition sentence32a univ := by
  refine licensingCondition_compl_iff.2
    ⟨fun _ h ↦ monotone_someN 1 h, ⟨⟨1, mem_Ici.2 le_rfl, rfl⟩, ?_⟩⟩
  rintro _ ⟨k, hk, rfl⟩ -
  exact someN_subset (fun y ↦ antitone_iff_forall_div.2 (div_readPaper y)) hk

-- (32c), (35)–(36)
theorem licensingCondition_sentence32c : LicensingCondition sentence32c univ := by
  refine licensingCondition_compl_iff.2 ⟨fun _ h ↦ monotone_someN 4 h, ⟨⟨4, by simp, rfl⟩, ?_⟩⟩
  rintro _ ⟨k, -, rfl⟩ h
  obtain ⟨X, hX, y, -, hw⟩ := h (a := (.univ, 0)) ⟨.univ, by simp, 0, trivial, rfl⟩
  obtain ⟨rfl, -⟩ := Prod.mk.inj (hw : ((.univ : Finset (Fin 4)), (0 : Fin 2)) = (X, y))
  subst hX
  simp only [Finset.card_univ, Fintype.card_fin]
  exact subset_rfl

-- (37a), (38)
theorem not_licensingCondition_sentence37a : ¬LicensingCondition sentence37a univ :=
  not_licensingCondition_every ⟨0, trivial⟩ fun h ↦ by
    have := h (a := {(0, 0)}) ⟨0, trivial, 0, trivial, by simp [didHomework]⟩
    simpa [Quantifier.Det.every, didHomework] using this (mem_univ 1)

/-! ### The domains of the models -/

/-- The domains of *any boys* in (26): the clause and the clause under negation. -/
def path26 : PolarityItem.Path (Finset (Fin 4)) (Set (Finset (Fin 4))) :=
  negated (conj haveBlueEyes girls) monotone_andSome

/-- The domains of *any boys* in (29). -/
def path29 : PolarityItem.Path (Finset (Fin 4)) (Set (Finset (Fin 4))) :=
  negated (conj wroteTogether girls) monotone_andSome

/-- The domains of *any paper* in (32a). -/
def path32a : PolarityItem.Path (Set (Fin 2)) (Set (Finset (Fin 4 × Fin 2))) :=
  negated (numeral readPaper 1) (monotone_someN 1)

/-- The domains of *any paper* in (32b). -/
def path32b : PolarityItem.Path (Set (Fin 2)) (Set (Finset (Fin 4 × Fin 2))) :=
  negated (numeral readPaper 4) (monotone_someN 4)

/-- The domains of *any paper* in (32c). -/
def path32c : PolarityItem.Path (Set (Fin 2)) (Set (Finset (Fin 4) × Fin 2)) :=
  negated (numeral wrotePaperTogether 4) (monotone_someN 4)

/-- The domains of *any homework* in (37a). -/
def path37a : PolarityItem.Path (Set (Fin 2)) (Set (Finset (Fin 4 × Fin 2))) :=
  negated (every didHomework univ) (monotone_every _ _)

open WithAlternatives (alternatives)

theorem licensed_path26_iff :
    Licensed path26 (alternatives ∘ conj haveBlueEyes girls) boys ↔
      LicensingCondition sentence26 boys :=
  licensed_negated_iff_of_eq_empty (andSome_bot _ _) ⟨.univ, by
    simp only [conj, andSome, haveBlueEyes, girls, boys, mem_ofPred_eq]; decide⟩

theorem licensed_path29_iff :
    Licensed path29 (alternatives ∘ conj wroteTogether girls) boys ↔
      LicensingCondition sentence29 boys :=
  licensed_negated_iff_of_eq_empty (andSome_bot _ _) ⟨girls ∪ {2}, by
    simp only [conj, andSome, wroteTogether, girls, boys, mem_ofPred_eq]; decide⟩

theorem licensed_path32a_iff :
    Licensed path32a (alternatives ∘ numeral readPaper 1) univ ↔
      LicensingCondition sentence32a univ :=
  licensed_negated_iff_of_eq_empty (someN_empty _ _)
    ⟨{(0, 0)}, {0}, rfl, 0, trivial, by simp [readPaper]⟩

theorem licensed_path32b_iff :
    Licensed path32b (alternatives ∘ numeral readPaper 4) univ ↔
      LicensingCondition sentence32b univ :=
  licensed_negated_iff_of_eq_empty (someN_empty _ _)
    ⟨.univ, .univ, by simp, 0, trivial, by simp [readPaper]⟩

theorem licensed_path32c_iff :
    Licensed path32c (alternatives ∘ numeral wrotePaperTogether 4) univ ↔
      LicensingCondition sentence32c univ :=
  licensed_negated_iff_of_eq_empty (someN_empty _ _)
    ⟨(.univ, 0), .univ, by simp, 0, trivial, rfl⟩

theorem licensed_path37a_iff :
    Licensed path37a (alternatives ∘ every didHomework univ) univ ↔
      LicensingCondition sentence37a univ :=
  licensed_negated_iff_of_eq_empty
    (eq_empty_of_forall_notMem fun _ hw ↦ by simpa using hw (mem_univ 0))
    ⟨.univ, fun x _ ↦ ⟨0, trivial, by simp [didHomework]⟩⟩

/-! ### Chierchia's Strong Application and exhaustification -/

open Chierchia2004 (doubt mem_doubt_strongApply_strong)

theorem strongApply_doubt_toWithAlternatives (x : Chierchia2004.Meaning (Set W)) :
    (doubt.strongApply x).toWithAlternatives = compl <$> x.toWithAlternatives := by
  rw [Chierchia2004.Meaning.strongApply_of_antitone (compl_antitone _)]
  refine WithAlternatives.ext rfl ?_
  rw [alternatives_compl]
  exact Chierchia2004.appAlternatives_of_given (F := doubt.toWithAlternatives) rfl

/-- Under *doubt*, the sentence is a strongest of its alternatives exactly when Chierchia's Strong
Application gives it no implicature, provided no alternative is trivial. -/
theorem minimal_iff_strongApply_doubt {x : Chierchia2004.Meaning (Set W)}
    (hx : x.ordinary ∈ x.alternatives) (hne : ∀ a ∈ x.alternatives, a ≠ univ) :
    Minimal (· ∈ (compl <$> x.toWithAlternatives).alternatives) x.ordinaryᶜ ↔
      (doubt.strongApply x).strong = x.ordinaryᶜ := by
  rw [alternatives_compl]
  refine ⟨fun hmin ↦ ?_, fun hs ↦ ⟨mem_image_of_mem _ hx, ?_⟩⟩
  · ext v
    rw [mem_doubt_strongApply_strong]
    exact ⟨fun h ↦ h.1, fun hv ↦ ⟨hv, fun a ha hlt ↦ (hlt.2 (compl_subset_compl.1
      (hmin.2 (mem_image_of_mem _ ha) (compl_subset_compl.2 hlt.1)))).elim⟩⟩
  · rintro _ ⟨a, ha, rfl⟩ hle
    by_contra hna
    have hlt : x.ordinary ⊂ a := ⟨compl_subset_compl.1 hle, fun h ↦ hna (compl_subset_compl.2 h)⟩
    refine hne a ha (eq_univ_of_forall fun v ↦ ?_)
    by_cases hv : v ∈ x.ordinary
    · exact hlt.1 hv
    · exact (mem_doubt_strongApply_strong.1 (hs ▸ hv : v ∈ (doubt.strongApply x).strong)).2 a ha hlt

/-- The node *`g` and some `n` `VP`* with the scale of *and*, before any implicature. -/
def andNode [SemilatticeSup α] [OrderBot α] (VP : α → Set W) (g n : α) :
    Chierchia2004.Meaning (Set W) :=
  { conj VP g n with strong := andSome VP g n }

-- (49)
theorem exh_conj [SemilatticeSup α] [OrderBot α] {VP : α → Set W} {g n : α}
    (h : ¬orSome VP g n ⊆ andSome VP g n) :
    Exhaustification.exh {(orSome VP g n)ᶜ} (andSome VP g n)ᶜ =
      (andSome VP g n)ᶜ ∩ orSome VP g n := by
  ext v
  simp only [Exhaustification.mem_exh, mem_singleton_iff, forall_eq, mem_inter_iff]
  exact and_congr_right fun _ ↦ ⟨fun h' ↦ by_contra fun hv ↦ h (compl_subset_compl.1 (h' hv)),
    fun hv h' ↦ (h' hv).elim⟩

theorem strongApply_andNode_wroteTogether_eq {n : Finset (Fin 4)}
    (h : LicensingCondition (compl <$> conj wroteTogether girls ·) n)
    (hand : ∅ ∉ andSome wroteTogether girls n) (hor : ∅ ∉ orSome wroteTogether girls n) :
    (doubt.strongApply (andNode wroteTogether girls n)).strong =
      (andSome wroteTogether girls n)ᶜ :=
  (minimal_iff_strongApply_doubt (x := andNode wroteTogether girls n) (Or.inl rfl) (by
    rintro a (rfl | rfl) ha
    exacts [hand (ha ▸ mem_univ _), hor (ha ▸ mem_univ _)])).1 h.minimal

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
  have h2 : ({2} : Finset (Fin 4)) ≤ boys := by decide
  have hLC2 : LicensingCondition (compl <$> conj wroteTogether girls ·) {2} :=
    licensingCondition_conj_iff.2 fun h ↦ absurd (h (a := girls ∪ {2}) (by
      simp only [andSome, wroteTogether, girls, mem_ofPred_eq]; decide)) (by
      simp only [orSome, wroteTogether, girls, mem_union, mem_ofPred_eq]; decide)
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [strongApply_andNode_wroteTogether_eq licensingCondition_sentence29
        (by simp only [andSome, wroteTogether, girls, boys, mem_ofPred_eq]; decide)
        (by simp only [orSome, wroteTogether, girls, boys, mem_union, mem_ofPred_eq]; decide),
      strongApply_andNode_wroteTogether_eq hLC2
        (by simp only [andSome, wroteTogether, girls, mem_ofPred_eq]; decide)
        (by simp only [orSome, wroteTogether, girls, mem_union, mem_ofPred_eq]; decide)]
    exact compl_subset_compl.2 (monotone_andSome h2)
  · rw [exh_conj (by
        intro h'
        exact absurd (h' (a := girls) (Or.inl rfl)) (by
          simp only [andSome, wroteTogether, girls, boys, mem_ofPred_eq]; decide)),
      exh_conj (by
        intro h'
        exact absurd (h' (a := girls) (Or.inl rfl)) (by
          simp only [andSome, wroteTogether, girls, mem_ofPred_eq]; decide))] at h
    -- boy `3` alone wrote a paper
    exact absurd (h (a := {3}) (by
      simp only [andSome, orSome, wroteTogether, girls, boys, mem_inter_iff, mem_compl_iff,
        mem_union, mem_ofPred_eq]; decide)) (by
      simp only [andSome, orSome, wroteTogether, girls, mem_inter_iff, mem_compl_iff, mem_union,
        mem_ofPred_eq]; decide)

/-! ### Clause (i) without clause (ii) -/

/-- The environment of (26), *I don't think that the girls and some `n` have blue eyes*, as an
operator on the restrictor of the item. -/
def haveBlueEyesEnvironment : PolarityItem.Licenser :=
  .classical
    { Param := PUnit.{2}
      Dom := fun _ ↦ Finset (Fin 4)
      Cod := fun _ ↦ Set (Finset (Fin 4))
      op := fun _ n ↦ (sentence26 n).ordinary }

/-- The environment of (26) meets the substrate's condition on a weak item, downward and not upward
entailment, which is the first clause of the Revised NPI Licensing Condition without the second,
though it fails the revised condition. -/
theorem carries_weak_not_licensingCondition :
    haveBlueEyesEnvironment.Carries .weak ∧ ¬LicensingCondition sentence26 boys := by
  refine ⟨⟨fun _ _ _ h ↦ compl_subset_compl.2 (monotone_andSome h), fun h ↦ ?_⟩,
    not_licensingCondition_sentence26⟩
  have hm := h PUnit.unit (bot_le : (⊥ : Finset (Fin 4)) ≤ boys)
  have hu : (Finset.univ : Finset (Fin 4)) ∈ (sentence26 ⊥).ordinary := by
    simp only [sentence26, conj, WithAlternatives.ordinary_map, andSome, haveBlueEyes,
      mem_compl_iff, mem_ofPred_eq]; decide
  exact hm hu (by simp only [conj, andSome, haveBlueEyes, girls, boys, mem_ofPred_eq]; decide)

/-! ### The judgments -/

/-- The Revised NPI Licensing Condition for the model of a row, read from its intervener, the number
of its conjoined DPs and the class of its predicate, for the sentences the models instantiate. -/
def licensing? (e : Datum) : Option Prop :=
  match e.feature? "coordination", e.feature? "number", e.feature? "numeral",
    e.feature? "quantifier", e.feature? "predicate" with
  | some "and", some "plural", none, none, some "distributive" =>
      some (Licensed path26 (alternatives ∘ conj haveBlueEyes girls) boys)
  | some "and", some "plural", none, none, some "collective" =>
      some (Licensed path29 (alternatives ∘ conj wroteTogether girls) boys)
  | none, none, some "one", none, some "distributive" =>
      some (Licensed path32a (alternatives ∘ numeral readPaper 1) univ)
  | none, none, some "four", none, some "distributive" =>
      some (Licensed path32b (alternatives ∘ numeral readPaper 4) univ)
  | none, none, some "four", none, some "collective" =>
      some (Licensed path32c (alternatives ∘ numeral wrotePaperTogether 4) univ)
  | none, none, none, some "all", none =>
      some (Licensed path37a (alternatives ∘ every didHomework univ) univ)
  | _, _, _, _, _ => none

theorem rows_licensing : ∀ e ∈ Examples.all, ∀ p ∈ licensing? e,
    (e.judgment.band = .accepted ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro p ⟨⟩ <;>
    first
      | exact iff_of_false (by decide) (licensed_path26_iff.not.2 not_licensingCondition_sentence26)
      | exact iff_of_true rfl (licensed_path29_iff.2 licensingCondition_sentence29)
      | exact iff_of_true rfl (licensed_path32a_iff.2 licensingCondition_sentence32a)
      | exact iff_of_false (by decide)
          (licensed_path32b_iff.not.2 not_licensingCondition_sentence32b)
      | exact iff_of_true rfl (licensed_path32c_iff.2 licensingCondition_sentence32c)
      | exact iff_of_false (by decide)
          (licensed_path37a_iff.not.2 not_licensingCondition_sentence37a)

theorem readCount_licensing : Datum.ReadCount licensing? Examples.all 6 := by
  decide +kernel

end BuccolaCrnic2021
