module

public import Linglib.Syntax.Cat
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Alternatives.Symmetric
public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Quantification.Basic

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

A sentence's truth conditions are its composition through `Tree.interp` over a lexicon reading a
three-way and a four-way world type (`cakeLex`, `fruitLex`), and trees a lexicon does not interpret
denote the contradiction, which never witnesses the principle. The engine composes binary nodes,
so the trees are binary: a noun phrase is labelled by its noun, and a connective forms a clause with
its second conjunct. The symmetric alternative places the conjunction of quantifiers at the
determiner.

## Errata

The final substitution source (41) holds the tree itself, so under (19) a tree can replace its own
constituent: [*tall (tall man)* is at most as complex as *tall man*](##tallTallMan_mem_alternatives)
and conversely. The relation bounds no size, and every *tall*ⁿ *man* has one complexity. The first
source (18), the lexicon alone, does bound size (`atMostAsComplex.numNodes_le`).

## References

* [katzir-2007]
* [sauerland-2004], [kroch-1972]
-/

@[expose] public section

open PhraseStructure Tree Montague

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
    apply StructuralOp.inChild ⟨1, by simp⟩
    apply StructuralOp.inChild ⟨1, by simp⟩
    apply StructuralOp.inChild ⟨0, by simp⟩
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

/-- The proposition a sentence denotes over the worlds its lexicon reads, the contradiction where
the lexicon does not interpret it. -/
def truth {E V : Type} (lx : Word → Option (Denotation E V (ReaderT V Id)))
    (g : Assignment E) (t : Tree Cat Word) : Set V :=
  {v | ∃ q : V → Prop, Tree.interp lx g t = some ⟨.t, q⟩ ∧ q v}

theorem mem_truth {E V : Type} {lx : Word → Option (Denotation E V (ReaderT V Id))}
    {g : Assignment E} {t : Tree Cat Word} {q : V → Prop} {v : V}
    (h : Tree.interp lx g t = some ⟨.t, q⟩) : v ∈ truth lx g t ↔ q v :=
  ⟨fun ⟨q', h', hv⟩ ↦ by
    have hq : q = q' := eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj (h.symm.trans h'))).2
    subst hq
    exact hv, fun hv ↦ ⟨q, h, hv⟩⟩

/-- How much of the cake John ate. -/
inductive Cake
  | none | part | whole
  deriving DecidableEq, Repr

/-- John and the two parts of the cake. -/
inductive Piece
  | john | left | right
  deriving DecidableEq, Repr

/-- The parts John ate. -/
def Cake.eaten : Cake → Set Piece
  | .none => ∅
  | .part => {.left}
  | .whole => {.left, .right}

/-- The words of (25), a transitive verb taking its object as a quantifier. -/
def cakeLex : Word → Option (Denotation Piece Cake (ReaderT Cake Id))
  | .john => some ⟨.e, fun _ ↦ .john⟩
  | .ate => some ⟨Ty.ett ⇒ Ty.et, fun c Q x ↦ x = .john ∧ Q c.eaten⟩
  | .some_ => some ⟨Ty.det, fun _ ↦ Quantifier.Det.some⟩
  | .all_ => some ⟨Ty.det, fun _ ↦ Quantifier.Det.every⟩
  | .cake => some ⟨Ty.et, fun _ y ↦ y ≠ .john⟩
  | .but_ => some ⟨Ty.det ⇒ Ty.det ⇒ Ty.det,
      fun _ D D' A B ↦ D A B ∧ D' A B⟩
  | .not_ => some ⟨Ty.det ⇒ Ty.det, fun _ D A B ↦ ¬ D A B⟩
  | _ => none

/-- The truth conditions of (25), by composition. -/
abbrev cakeMeaning : Tree Cat Word → Set Cake := truth cakeLex fun _ ↦ Piece.john

private theorem some_eaten_iff {c : Cake} :
    Quantifier.Det.some {y | y ≠ Piece.john} c.eaten ↔ c ≠ .none := by
  cases c
  · simp [Cake.eaten, Quantifier.Det.some]
  · exact iff_of_true ⟨.left, by simp, by simp [Cake.eaten]⟩ (by simp)
  · exact iff_of_true ⟨.left, by simp, by simp [Cake.eaten]⟩ (by simp)

private theorem every_eaten_iff {c : Cake} :
    Quantifier.Det.every {y | y ≠ Piece.john} c.eaten ↔ c = .whole := by
  cases c
  · exact iff_of_false (fun h ↦ by simpa [Cake.eaten] using h (show Piece.left ∈ _ by simp))
      (by simp)
  · exact iff_of_false (fun h ↦ by simpa [Cake.eaten] using h (show Piece.right ∈ _ by simp))
      (by simp)
  · exact iff_of_true (fun y hy ↦ by cases y <;> simp_all [Cake.eaten]) rfl

theorem mem_cakeMeaning_some {c : Cake} : c ∈ cakeMeaning someSentence ↔ c ≠ .none := by
  rw [mem_truth (q := fun c ↦ Piece.john = .john ∧ Quantifier.Det.some {y | y ≠ Piece.john} c.eaten)
    rfl]
  simp [some_eaten_iff]

theorem mem_cakeMeaning_all {c : Cake} : c ∈ cakeMeaning allSentence ↔ c = .whole := by
  rw [mem_truth (q := fun c ↦ Piece.john = .john ∧
    Quantifier.Det.every {y | y ≠ Piece.john} c.eaten) rfl]
  simp [every_eaten_iff]

-- (25a), (25b)
theorem isSymmetric_cakeMeaning : Alternatives.IsSymmetric (cakeMeaning someSentence)
    (cakeMeaning allSentence) (cakeMeaning someButNotAllSentence) := by
  have hmid {c : Cake} : c ∈ cakeMeaning someButNotAllSentence ↔ c = .part := by
    rw [mem_truth (q := fun c ↦ Piece.john = .john ∧
      (¬ Quantifier.Det.every {y | y ≠ Piece.john} c.eaten ∧
        Quantifier.Det.some {y | y ≠ Piece.john} c.eaten)) rfl]
    simp only [every_eaten_iff, some_eaten_iff]
    cases c <;> simp
  refine ⟨Set.ext fun c ↦ ?_, Set.disjoint_left.2 fun c h₁ h₂ ↦ ?_⟩
  · rw [Set.mem_union, mem_cakeMeaning_some, mem_cakeMeaning_all, hmid]
    cases c <;> simp
  · cases (mem_cakeMeaning_all.1 h₁).symm.trans (hmid.1 h₂)

/-- The alternatives of (21) are the structural alternatives that are weakly assertable. -/
def assertableAlts (wa : Tree Cat Word → Prop) (t : Tree Cat Word) : Set (Tree Cat Word) :=
  {t' ∈ structuralAlternatives lexicon t | wa t'}

/-- Principle (21) forbids a sentence with a strictly stronger, weakly assertable alternative. -/
def Blocked {M : Type*} (wa : Tree Cat Word → Prop) (m : Tree Cat Word → Set M)
    (t : Tree Cat Word) : Prop :=
  ∃ t' ∈ assertableAlts wa t, m t' ⊂ m t

theorem blocked_of_weaklyAssertable_all {wa : Tree Cat Word → Prop} (h : wa allSentence) :
    Blocked wa cakeMeaning someSentence :=
  ⟨allSentence, ⟨all_mem_alternatives, h⟩, LE.le.ssubset_of_not_superset
    (fun c hc ↦ mem_cakeMeaning_some.2 (by rw [mem_cakeMeaning_all.1 hc]; simp))
    (Set.not_subset.2 ⟨.part, mem_cakeMeaning_some.2 (by simp),
      fun hc ↦ by simpa using mem_cakeMeaning_all.1 hc⟩)⟩

/-- In the primary implicature of (25a), a speaker who obeys the principle has *all* not weakly
assertable; the symmetric alternative, being no alternative, licenses nothing. -/
theorem primary_implicature_some {wa : Tree Cat Word → Prop}
    (h : ¬ Blocked wa cakeMeaning someSentence) : ¬ wa allSentence :=
  fun hwa ↦ h (blocked_of_weaklyAssertable_all hwa)

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
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨1, by simp⟩) ?_
  exact Relation.ReflTransGen.single (StructuralOp.contract (List.Mem.head _) rfl)

theorem rightDisjunct_mem_alternatives :
    rightDisjunct ∈ structuralAlternatives lexicon orSentence := by
  refine Relation.ReflTransGen.head (StructuralOp.contract
    (child := .node .S [.terminal .Conj .or_, rightDisjunct])
    (List.mem_cons_of_mem _ (List.Mem.head _)) rfl) ?_
  refine Relation.ReflTransGen.head (StructuralOp.delete ⟨0, by simp⟩) ?_
  exact Relation.ReflTransGen.single (StructuralOp.contract (List.Mem.head _) rfl)

/-- Which of the two fruits John ate. -/
abbrev Fruits := Bool × Bool

/-- John and the two fruits. -/
inductive Fruit
  | john | apple | pear
  deriving DecidableEq, Repr

/-- The words of (26) and (27), the connectives coordinating clauses. -/
def fruitLex : Word → Option (Denotation Fruit Fruits (ReaderT Fruits Id))
  | .john => some ⟨.e, fun _ ↦ .john⟩
  | .apple => some ⟨.e, fun _ ↦ .apple⟩
  | .pear => some ⟨.e, fun _ ↦ .pear⟩
  | .ate => some ⟨.e ⇒ .e ⇒ .t, fun f y x ↦ x = .john ∧ (y = .apple ∧ f.1 ∨ y = .pear ∧ f.2)⟩
  | .or_ => some ⟨.t ⇒ .t ⇒ .t, fun _ p q ↦ p ∨ q⟩
  | .and_ => some ⟨.t ⇒ .t ⇒ .t, fun _ p q ↦ p ∧ q⟩
  | _ => none

/-- The truth conditions of (26) and (27), by composition. -/
abbrev fruitMeaning : Tree Cat Word → Set Fruits := truth fruitLex fun _ ↦ Fruit.john

private abbrev ateFruit (y : Fruit) (f : Fruits) : Prop :=
  Fruit.john = .john ∧ (y = .apple ∧ f.1 = true ∨ y = .pear ∧ f.2 = true)

theorem mem_fruitMeaning_left {f : Fruits} : f ∈ fruitMeaning leftDisjunct ↔ f.1 = true := by
  rw [mem_truth (q := ateFruit .apple) rfl]; simp [ateFruit]

theorem mem_fruitMeaning_right {f : Fruits} : f ∈ fruitMeaning rightDisjunct ↔ f.2 = true := by
  rw [mem_truth (q := ateFruit .pear) rfl]; simp [ateFruit]

theorem mem_fruitMeaning_or {f : Fruits} :
    f ∈ fruitMeaning orSentence ↔ f.1 = true ∨ f.2 = true := by
  rw [mem_truth (q := fun f ↦ ateFruit .pear f ∨ ateFruit .apple f) rfl]; simp [ateFruit, or_comm]

theorem mem_fruitMeaning_and {f : Fruits} :
    f ∈ fruitMeaning andSentence ↔ f.1 = true ∧ f.2 = true := by
  rw [mem_truth (q := fun f ↦ ateFruit .pear f ∧ ateFruit .apple f) rfl]; simp [ateFruit, and_comm]

/-- In the primary inferences (28), a speaker of the disjunction who obeys the principle has the
conjunction and each disjunct not weakly assertable. -/
theorem primary_inferences_or {wa : Tree Cat Word → Prop}
    (h : ¬ Blocked wa fruitMeaning orSentence) :
    ¬ wa andSentence ∧ ¬ wa leftDisjunct ∧ ¬ wa rightDisjunct := by
  refine ⟨fun hwa ↦ h ⟨andSentence, ⟨and_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(true, false), ?_, ?_⟩)⟩,
    fun hwa ↦ h ⟨leftDisjunct, ⟨leftDisjunct_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(false, true), ?_, ?_⟩)⟩,
    fun hwa ↦ h ⟨rightDisjunct, ⟨rightDisjunct_mem_alternatives, hwa⟩,
      LE.le.ssubset_of_not_superset ?_ (Set.not_subset.2 ⟨(true, false), ?_, ?_⟩)⟩⟩ <;>
  first
    | (intro f hf
       simp only [mem_fruitMeaning_or, mem_fruitMeaning_and, mem_fruitMeaning_left,
         mem_fruitMeaning_right] at hf ⊢
       tauto)
    | simp [mem_fruitMeaning_or, mem_fruitMeaning_and, mem_fruitMeaning_left,
        mem_fruitMeaning_right]

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

/-- *a tall tall man*, without its determiner. -/
def tallTallMan : Tree Cat Word := .node .N [.terminal .Adj .tall, tallMan]

-- (41)
theorem tallTallMan_mem_alternatives : tallTallMan ∈ structuralAlternatives lexicon tallMan :=
  Relation.ReflTransGen.single (StructuralOp.inChild ⟨1, by simp⟩
    (StructuralOp.subst (ψ := tallMan) rfl
      (Set.mem_union_right _ (by simp [tallMan, RoseTree.subtrees_node]))))


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

-- Under the first source (18), the lexicon alone, it is no alternative: that source bounds size.
theorem moreThanWarmYesterday_not_atMostAsComplex_lexicon :
    ¬ atMostAsComplex ↑lexicon moreThanWarmYesterday warmYesterday := fun h ↦
  absurd (h.numNodes_le (by decide)) (by decide)

end Katzir2007
