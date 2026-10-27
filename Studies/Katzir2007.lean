module

public import Linglib.Syntax.Cat
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Pragmatics.Competition

/-!
# Katzir (2007): Structurally-Defined Alternatives

This file formalizes the worked examples of Katzir's paper, which replaces the Horn scales of
neo-Gricean pragmatics by alternatives defined on parse trees: the alternatives of a sentence
are the trees obtainable from it by deletion, contraction, and substitution of constituents by
same-category items of the substitution source, the lexicon together with the sentence's own
subtrees (its definitions (19) to (21) and (41), the substrate `Alternatives`).
The conversational principle (21) then forbids asserting a sentence when a structural
alternative is strictly stronger and weakly assertable, the substrate's `Competition.Blocked`
over the weakly assertable structural alternatives.

The examples are the paper's Section 4 and 5 sentences over a small lexicon. For (25),
*all of the cake* is an alternative of the same complexity as *some of the cake*
(`all_mem_alternatives`), so a speaker obeying (21) implicates that it is not weakly assertable
(`primary_implicature_some`), while the symmetric *some but not all* is no alternative, since no
operation introduces the conjunction it needs (`someButNotAll_not_mem_alternatives`). For the
disjunction (26), the conjunction and each disjunct are alternatives (`and_mem_alternatives`,
`leftDisjunct_mem_alternatives`, `rightDisjunct_mem_alternatives`), which yields the primary
inferences (28) without Sauerland's L and R connectives
(`primary_inferences_or`). Deleting a modifier gives a strictly simpler alternative, (29)
(`justMan_mem_alternatives`), and the subtree clause of the substitution source (41) makes
*a little bit more than warm* substitutable for *warm* in (40), so that the more complex
sentence is an alternative of the simpler (`moreThanWarmYesterday_mem_alternatives`).

## Implementation notes

The truth conditions the paper takes for granted enter as meaning functions on three-way and
four-way world types; trees the paper does not interpret denote the contradiction, which
never witnesses the principle. Determiners inside the noun phrases are omitted from the trees,
and the symmetric alternative places the conjunction of quantifiers at the determiner.

## References

* [katzir-2007]
* [sauerland-2004], [kroch-1972]
-/

@[expose] public section

open PhraseStructure Tree Competition

namespace Katzir2007

/-- The vocabulary of the paper's examples. -/
inductive Word
  | john | ate | some_ | all_ | cake | apple | pear | or_ | and_ | but_ | not_ | tall | man
  | it | was | is | warm | yesterday | today | aLittleBitMoreThan
  deriving DecidableEq, Repr

/-- The lexicon lists the terminal items available for substitution. -/
def lexicon : Finset (Tree Cat Word) :=
  {.terminal .N .john, .terminal .V .ate, .terminal .Det .some_, .terminal .Det .all_,
    .terminal .N .cake, .terminal .N .apple, .terminal .N .pear, .terminal .Conj .or_,
    .terminal .Conj .and_, .terminal .Adj .tall, .terminal .N .man, .terminal .Pron .it,
    .terminal .Aux .was, .terminal .Aux .is, .terminal .Adj .warm, .terminal .Adv .yesterday,
    .terminal .Adv .today}

/-! ### Some, all, some but not all (Section 4.1) -/

/-- (25a) *John ate some of the cake*. -/
def someSentence : Tree Cat Word :=
  .node .S [.terminal .N .john,
    .node .V [.terminal .V .ate, .terminal .Det .some_, .terminal .N .cake]]

/-- (25b) *John ate all of the cake*. -/
def allSentence : Tree Cat Word :=
  .node .S [.terminal .N .john,
    .node .V [.terminal .V .ate, .terminal .Det .all_, .terminal .N .cake]]

/-- (25c) *John ate some but not all of the cake*, the symmetric alternative. -/
def someButNotAllSentence : Tree Cat Word :=
  .node .S [.terminal .N .john,
    .node .V [.terminal .V .ate,
      .node .Conj [.terminal .Det .some_, .terminal .Conj .but_,
        .node .Neg [.terminal .Neg .not_, .terminal .Det .all_]],
      .terminal .N .cake]]

-- (25b), (25a)
theorem leafSubst_some_all : someSentence.leafSubst .some_ .all_ .Det = allSentence := rfl

/-- (25b) is a structural alternative of (25a), since the determiners are same-category items of
the lexicon. -/
theorem all_mem_alternatives : allSentence ∈ structuralAlternatives lexicon someSentence :=
  leafSubst_some_all ▸ horn_alternatives_are_structural lexicon someSentence .some_ .all_ .Det
    (by simp [lexicon]) (by decide)

theorem some_all_equalComplexity :
    equalComplexity (substitutionSource lexicon someSentence) someSentence allSentence := by
  refine ⟨?_, ?_⟩ <;>
  · apply Relation.ReflTransGen.single
    apply StructuralOp.inChild ⟨1, by simp⟩
    apply StructuralOp.inChild ⟨1, by simp⟩
    apply StructuralOp.subst
    · rfl
    · simp [substitutionSource, lexicon]

-- (25a)
theorem source_lacks_conjP : ∀ t ∈ substitutionSource lexicon someSentence,
    ∀ s ∈ t.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = Cat.Conj) :=
  forall_mem_substitutionSource.2 ⟨by decide, by decide⟩

theorem someButNotAll_not_mem_alternatives :
    someButNotAllSentence ∉ structuralAlternatives lexicon someSentence := fun h ↦
  (by decide : ¬ ∀ s ∈ someButNotAllSentence.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = Cat.Conj))
    (phrase_preservation _ Cat.Conj source_lacks_conjP (by decide) h)

/-- How much of the cake John ate. -/
inductive Cake
  | none | part | whole
  deriving DecidableEq, Repr

/-- Under the truth conditions the paper assumes for (25), *some* holds of any eating, *all* of
the whole, and *some but not all* of a part; the other trees are not interpreted. -/
def cakeMeaning (t : Tree Cat Word) : Set Cake :=
  {c | (t = someSentence ∧ c ≠ .none) ∨ (t = allSentence ∧ c = .whole) ∨
    (t = someButNotAllSentence ∧ c = .part)}

/-- The alternatives of (21) are the structural alternatives that are weakly assertable. -/
def assertableAlts (wa : Tree Cat Word → Prop) (t : Tree Cat Word) : Set (Tree Cat Word) :=
  {t' ∈ structuralAlternatives lexicon t | wa t'}

theorem blocked_of_weaklyAssertable_all {wa : Tree Cat Word → Prop} (h : wa allSentence) :
    Blocked (assertableAlts wa) cakeMeaning someSentence :=
  ⟨allSentence, ⟨all_mem_alternatives, h⟩, LE.le.ssubset_of_not_superset
    (fun c hc ↦ by simp_all [cakeMeaning, someSentence, allSentence, someButNotAllSentence])
    (Set.not_subset.2 ⟨.part, by simp [cakeMeaning], by simp [cakeMeaning, someSentence,
      allSentence, someButNotAllSentence]⟩)⟩

/-- In the primary implicature of (25a), a speaker who obeys the principle has *all* not weakly
assertable; the symmetric alternative, being no alternative, licenses nothing. -/
theorem primary_implicature_some {wa : Tree Cat Word → Prop}
    (h : ¬ Blocked (assertableAlts wa) cakeMeaning someSentence) : ¬ wa allSentence :=
  fun hwa ↦ h (blocked_of_weaklyAssertable_all hwa)

/-! ### Disjunction (Section 4.2) -/

/-- (26a) *John ate the apple or the pear*. -/
def orSentence : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .apple]],
    .terminal .Conj .or_,
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .pear]]]

/-- (26b) *John ate the apple and the pear*. -/
def andSentence : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .apple]],
    .terminal .Conj .and_,
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .pear]]]

/-- (27a) *John ate the apple*, the left disjunct. -/
def leftDisjunct : Tree Cat Word :=
  .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .apple]]

/-- (27b) *John ate the pear*, the right disjunct. -/
def rightDisjunct : Tree Cat Word :=
  .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .pear]]

theorem leafSubst_or_and : orSentence.leafSubst .or_ .and_ .Conj = andSentence := rfl

theorem and_mem_alternatives : andSentence ∈ structuralAlternatives lexicon orSentence :=
  leafSubst_or_and ▸ horn_alternatives_are_structural lexicon orSentence .or_ .and_ .Conj
    (by simp [lexicon]) (by decide)

theorem leftDisjunct_mem_alternatives :
    leftDisjunct ∈ structuralAlternatives lexicon orSentence := by
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨2, by simp⟩) ?_
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨1, by simp [List.eraseIdx]⟩) ?_
  exact Relation.ReflTransGen.single (StructuralOp.contract (List.Mem.head _) rfl)

theorem rightDisjunct_mem_alternatives :
    rightDisjunct ∈ structuralAlternatives lexicon orSentence := by
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨0, by simp⟩) ?_
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨0, by simp [List.eraseIdx]⟩) ?_
  exact Relation.ReflTransGen.single (StructuralOp.contract (List.Mem.head _) rfl)

/-- Which of the two fruits John ate. -/
abbrev Fruits := Bool × Bool

/-- These are the truth conditions of (26) and (27), for the disjunction, the conjunction, and
each disjunct. -/
def fruitMeaning (t : Tree Cat Word) : Set Fruits :=
  {f | (t = orSentence ∧ (f.1 ∨ f.2)) ∨ (t = andSentence ∧ f.1 ∧ f.2) ∨
    (t = leftDisjunct ∧ f.1) ∨ (t = rightDisjunct ∧ f.2)}

/-- In the primary inferences (28), a speaker of the disjunction who obeys the principle has the
conjunction and each disjunct not weakly assertable. -/
theorem primary_inferences_or {wa : Tree Cat Word → Prop}
    (h : ¬ Blocked (assertableAlts wa) fruitMeaning orSentence) :
    ¬ wa andSentence ∧ ¬ wa leftDisjunct ∧ ¬ wa rightDisjunct := by
  refine ⟨fun hwa ↦ h ⟨andSentence, ⟨and_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(true, false), ?_, ?_⟩)⟩,
    fun hwa ↦ h ⟨leftDisjunct, ⟨leftDisjunct_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(false, true), ?_, ?_⟩)⟩,
    fun hwa ↦ h ⟨rightDisjunct, ⟨rightDisjunct_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(true, false), ?_, ?_⟩)⟩⟩ <;>
  simp_all [fruitMeaning, orSentence, andSentence, leftDisjunct, rightDisjunct]

/-! ### Strictly simpler alternatives (Section 4.3) -/

/-- (29a) *a tall man*, without its determiner. -/
def tallMan : Tree Cat Word := .node .N [.terminal .Adj .tall, .terminal .N .man]

/-- (29b) *a man*. -/
def justMan : Tree Cat Word := .node .N [.terminal .N .man]

/-- Deleting the modifier yields a strictly simpler structural alternative, giving an inference only
under downward entailment ((30) to (32)). -/
theorem justMan_mem_alternatives : justMan ∈ structuralAlternatives lexicon tallMan :=
  Relation.ReflTransGen.single (StructuralOp.delete ⟨0, by simp⟩)

/-! ### The subtrees of the sentence as substitution source (Section 5) -/

/-- *a little bit more than warm*, an adjective phrase. -/
def moreThanWarm : Tree Cat Word :=
  .node .Adj [.terminal .Adv .aLittleBitMoreThan, .terminal .Adj .warm]

/-- *it is a little bit more than warm today*. -/
def moreThanWarmToday : Tree Cat Word :=
  .node .S [.terminal .Pron .it, .terminal .Aux .is, moreThanWarm, .terminal .Adv .today]

/-- (40a) *It was warm yesterday, and it is a little bit more than warm today*. -/
def warmYesterday : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .Pron .it, .terminal .Aux .was, .node .Adj [.terminal .Adj .warm],
      .terminal .Adv .yesterday],
    .terminal .Conj .and_, moreThanWarmToday]

/-- (40b) *It was a little bit more than warm yesterday, and it is a little bit more than warm
today*. -/
def moreThanWarmYesterday : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .Pron .it, .terminal .Aux .was, moreThanWarm, .terminal .Adv .yesterday],
    .terminal .Conj .and_, moreThanWarmToday]

/-- Matsumoto's (40b) is a structural alternative of (40a), since its adjective phrase lies in the
substitution source (41). -/
theorem moreThanWarmYesterday_mem_alternatives :
    moreThanWarmYesterday ∈ structuralAlternatives lexicon warmYesterday :=
  Relation.ReflTransGen.single (StructuralOp.inChild ⟨0, by simp⟩
    (StructuralOp.inChild ⟨2, by simp⟩
      (StructuralOp.subst rfl (Set.mem_union_right _ (by decide)))))

end Katzir2007
