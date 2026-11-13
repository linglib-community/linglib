module

public import Linglib.Syntax.Cat
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Alternatives.Symmetric

/-!
# Katzir (2007): Structurally-Defined Alternatives

This file formalizes the worked examples of Katzir's paper, which replaces the Horn scales of
neo-Gricean pragmatics by alternatives defined on parse trees: the alternatives of a sentence
are the trees obtainable from it by deletion, contraction, and substitution of constituents by
same-category items of the substitution source, the lexicon together with the sentence's own
subtrees (its definitions (19) to (21) and (41), the substrate `Alternatives`).
The conversational principle (21) then forbids asserting a sentence when a structural
alternative is strictly stronger and weakly assertable (`Blocked`).

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

The paper's principle (21) compares the propositions two sentences denote by strict inclusion,
and takes the denotations of its examples as known: it gives them no lexical entries and no
composition. So the meaning of a tree is a parameter here, and each implicature is stated under
the inclusions the paper relies on. A noun phrase is labelled by its noun, and a connective forms
a clause with its second conjunct. The symmetric alternative places the conjunction of
quantifiers at the determiner.

## References

* [katzir-2007]
* [sauerland-2004], [kroch-1972]
-/

@[expose] public section

open PhraseStructure Tree

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
    .node .V [.terminal .V .ate, .node .N [.terminal .Det .some_, .terminal .N .cake]]]

/-- (25b) *John ate all of the cake*. -/
def allSentence : Tree Cat Word :=
  .node .S [.terminal .N .john,
    .node .V [.terminal .V .ate, .node .N [.terminal .Det .all_, .terminal .N .cake]]]

/-- (25c) *John ate some but not all of the cake*, the symmetric alternative. -/
def someButNotAllSentence : Tree Cat Word :=
  .node .S [.terminal .N .john,
    .node .V [.terminal .V .ate, .node .N [
      .node .Conj [.terminal .Det .some_, .node .Conj [.terminal .Conj .but_,
        .node .Neg [.terminal .Neg .not_, .terminal .Det .all_]]],
      .terminal .N .cake]]]

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
    apply RoseTree.Rewrites.set _ ⟨1, by simp⟩
    apply RoseTree.Rewrites.set _ ⟨1, by simp⟩
    apply RoseTree.Rewrites.set _ ⟨0, by simp⟩
    refine .here (StructuralOp.subst rfl ?_)
    simp [substitutionSource, lexicon]

-- (25a)
theorem source_lacks_conjP : ∀ t ∈ substitutionSource lexicon someSentence,
    ∀ s ∈ t.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = Cat.Conj) :=
  forall_mem_substitutionSource.2 ⟨by decide, by decide⟩

theorem someButNotAll_not_mem_alternatives :
    someButNotAllSentence ∉ structuralAlternatives lexicon someSentence := fun h ↦
  (by decide : ¬ ∀ s ∈ someButNotAllSentence.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = Cat.Conj))
    (phrase_preservation _ Cat.Conj source_lacks_conjP (by decide) h)

/-- The alternatives of (21) are the structural alternatives that are weakly assertable. -/
def assertableAlts (wa : Tree Cat Word → Prop) (t : Tree Cat Word) : Set (Tree Cat Word) :=
  {t' ∈ structuralAlternatives lexicon t | wa t'}

/-- Principle (21) forbids a sentence with a strictly stronger, weakly assertable alternative. -/
def Blocked {M : Type*} (wa : Tree Cat Word → Prop) (m : Tree Cat Word → Set M)
    (t : Tree Cat Word) : Prop :=
  ∃ t' ∈ assertableAlts wa t, m t' ⊂ m t

variable {M : Type*} {m : Tree Cat Word → Set M} {wa : Tree Cat Word → Prop}

theorem blocked_of_weaklyAssertable_all (hm : m allSentence ⊂ m someSentence)
    (h : wa allSentence) : Blocked wa m someSentence :=
  ⟨allSentence, ⟨all_mem_alternatives, h⟩, hm⟩

/-- In the primary implicature of (25a), with *all* strictly stronger than *some*, a speaker who
obeys the principle has *all* not weakly assertable; the symmetric alternative, being no
alternative, licenses nothing. -/
theorem primary_implicature_some (hm : m allSentence ⊂ m someSentence)
    (h : ¬ Blocked wa m someSentence) : ¬ wa allSentence :=
  fun hwa ↦ h (blocked_of_weaklyAssertable_all hm hwa)

-- (25c): *some but not all* is the symmetric alternative of *all*, whatever the sentences denote,
-- once it denotes what *some* does without what *all* does.
theorem isSymmetric_someButNotAll (hm : m allSentence ⊆ m someSentence)
    (hs : m someButNotAllSentence = m someSentence \ m allSentence) :
    Alternatives.IsSymmetric (m someSentence) (m allSentence) (m someButNotAllSentence) :=
  hs ▸ Alternatives.isSymmetric_sdiff hm

/-! ### Disjunction (Section 4.2) -/

/-- (26a) *John ate the apple or the pear*. -/
def orSentence : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .apple]],
    .node .S [.terminal .Conj .or_,
      .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .pear]]]]

/-- (26b) *John ate the apple and the pear*. -/
def andSentence : Tree Cat Word :=
  .node .S [
    .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .apple]],
    .node .S [.terminal .Conj .and_,
      .node .S [.terminal .N .john, .node .V [.terminal .V .ate, .terminal .N .pear]]]]

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
  refine Relation.ReflTransGen.head (.here (StructuralOp.delete ⟨1, by simp⟩)) ?_
  exact Relation.ReflTransGen.single (.here (StructuralOp.contract (List.Mem.head _) rfl))

theorem rightDisjunct_mem_alternatives :
    rightDisjunct ∈ structuralAlternatives lexicon orSentence := by
  refine Relation.ReflTransGen.head (.here (StructuralOp.contract
    (child := .node .S [.terminal .Conj .or_, rightDisjunct])
    (List.mem_cons_of_mem _ (List.Mem.head _)) rfl)) ?_
  refine Relation.ReflTransGen.head (.here (StructuralOp.delete ⟨0, by simp⟩)) ?_
  exact Relation.ReflTransGen.single (.here (StructuralOp.contract (List.Mem.head _) rfl))

/-- In the primary inferences (28), with the conjunction and each disjunct strictly stronger than
the disjunction, a speaker of the disjunction who obeys the principle has none of them weakly
assertable. -/
theorem primary_inferences_or (hand : m andSentence ⊂ m orSentence)
    (hl : m leftDisjunct ⊂ m orSentence) (hr : m rightDisjunct ⊂ m orSentence)
    (h : ¬ Blocked wa m orSentence) :
    ¬ wa andSentence ∧ ¬ wa leftDisjunct ∧ ¬ wa rightDisjunct :=
  ⟨fun hwa ↦ h ⟨andSentence, ⟨and_mem_alternatives, hwa⟩, hand⟩,
    fun hwa ↦ h ⟨leftDisjunct, ⟨leftDisjunct_mem_alternatives, hwa⟩, hl⟩,
    fun hwa ↦ h ⟨rightDisjunct, ⟨rightDisjunct_mem_alternatives, hwa⟩, hr⟩⟩

/-! ### Strictly simpler alternatives (Section 4.3) -/

/-- (29a) *a tall man*, without its determiner. -/
def tallMan : Tree Cat Word := .node .N [.terminal .Adj .tall, .terminal .N .man]

/-- (29b) *a man*. -/
def justMan : Tree Cat Word := .node .N [.terminal .N .man]

/-- Deleting the modifier yields a strictly simpler structural alternative, giving an inference only
under downward entailment ((30) to (32)). -/
theorem justMan_mem_alternatives : justMan ∈ structuralAlternatives lexicon tallMan :=
  Relation.ReflTransGen.single (.here (StructuralOp.delete ⟨0, by simp⟩))

/-! ### The subtrees of the sentence as substitution source (Section 5) -/

/-- *a tall tall man*, without its determiner. -/
def tallTallMan : Tree Cat Word := .node .N [.terminal .Adj .tall, tallMan]

-- (41)
theorem tallTallMan_mem_alternatives : tallTallMan ∈ structuralAlternatives lexicon tallMan :=
  Relation.ReflTransGen.single (RoseTree.Rewrites.set _ ⟨1, by simp⟩
    (.here (StructuralOp.subst (ψ := tallMan) rfl
      (Set.mem_union_right _ (by simp [tallMan, RoseTree.subtrees_node])))))


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
  Relation.ReflTransGen.single (RoseTree.Rewrites.set _ ⟨0, by simp⟩
    (RoseTree.Rewrites.set _ ⟨2, by simp⟩
      (.here (StructuralOp.subst rfl (Set.mem_union_right _ (by decide))))))

-- Under the first source (18), the lexicon alone, it is no alternative: that source bounds size.
theorem moreThanWarmYesterday_not_atMostAsComplex_lexicon :
    ¬ atMostAsComplex ↑lexicon moreThanWarmYesterday warmYesterday := fun h ↦
  absurd (h.numNodes_le (by decide)) (by decide)

end Katzir2007
