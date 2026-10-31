module

public import Linglib.Semantics.Quantification.Witness
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Data.Examples.PurverGinzburg2004
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Union
public import Linglib.Data.Examples.Readers

/-!
# Purver and Ginzburg (2004): Clarifying Noun Phrase Semantics

A reprise question repeats a phrase of the previous utterance to query it, as *Turkey?* does
after *We'll get the turkey out of the oven*. Purver and Ginzburg read what a noun phrase
denotes off the readings its reprises have. In the grammar of Ginzburg and Cooper a sign lists
its contextual parameters, the objects a hearer must identify in context, and a reprise can
query only these. The Reprise Content Hypothesis says that a reprise queries part of the content
of the reprised phrase, and in its strong version exactly that content. The paper takes a
quantified noun phrase to denote a witness set, a subset of the noun's extension that its
quantifier holds of, and its Definiteness Principle makes that content a contextual parameter
in a definite use and a member of the store of existentially quantified objects in an
indefinite one.

## Implementation notes

* A sign records which kinds of object it contributes, not their values, since the argument
  turns on what kind of object a reprise queries. A content is the set of its components, so
  that both members of a reference set and complement pair can be abstracted.
* `Sign.phrase` takes the parameters that the Definiteness Principle distributes as an optional
  argument, by default the content. It is set for attributive definites, where the paper asks
  for "a slightly different version" of the principle, and for the generalized-quantifier
  alternative.
* The rows carry the paper's classification of each use as a feature, and a referential use of
  an indefinite or a universal counts as definite, as in the paper. Every noun phrase gets the
  sign of a determiner with a noun, pronouns and bare *wh*-words included. Marginal readings
  make no claim.
* Quantifier scope, anaphora, the retrieval of stored objects and the corpus counts are not
  formalized.

## References

* [purver-ginzburg-2004]
* [ginzburg-cooper-2004]
* [barwise-cooper-1981]
-/

@[expose] public section

namespace PurverGinzburg2004

open Examples Quantifier

/-! ### Signs and the Definiteness Principle -/

/-- The kinds of semantic object a nominal sign contributes or abstracts. They are an individual
or witness set, a property, a determiner relation, a function to witness sets with its
situational argument, a generalized quantifier, and the complement set of a monotone decreasing
phrase. -/
inductive Kind
  | individual
  | property
  | relation
  | function
  | situation
  | quantifier
  | complement
  deriving DecidableEq, Repr

/-- A nominal sign carries the components of its content, the contextual parameters a reprise
can query, and the parameters stored for existential closure. -/
structure Sign where
  content : Finset Kind
  cparams : Finset Kind
  store : Finset Kind
  deriving DecidableEq

namespace Sign

variable {c s : Finset Kind} {head : Sign} {nonHead : Finset Sign}

/-- `Sign.word content store` is the sign of a word, whose contextual parameters are the content
it does not store (74). -/
def word (content store : Finset Kind) : Sign := ⟨content, content \ store, store⟩

/-- `Sign.phrase content store head nonHead` is the sign of a phrase (75). Its contextual
parameters are those of every daughter (73) with the parameters it does not store, and its store
adds that of the head daughter. The parameters are the content unless `params` is given. -/
def phrase (content store : Finset Kind) (head : Sign) (nonHead : Finset Sign)
    (params : Finset Kind := content) : Sign :=
  ⟨content, params \ store ∪ (insert head nonHead).biUnion (·.cparams), store ∪ head.store⟩

/-- The Definiteness Principle requires each component of the content to be a contextual
parameter or stored. -/
def DefinitenessPrinciple (s : Sign) : Prop := s.content ⊆ s.cparams ∪ s.store
deriving Decidable

/-- A sign holds the strong Reprise Content Hypothesis when a reprise can query its whole
content, every component being a contextual parameter. -/
def Strong (s : Sign) : Prop := s.content ⊆ s.cparams
deriving Decidable

theorem definitenessPrinciple_word : (word c s).DefinitenessPrinciple := le_sdiff_sup

theorem definitenessPrinciple_phrase : (phrase c s head nonHead).DefinitenessPrinciple :=
  le_sdiff_sup.trans (sup_le_sup le_sup_left le_sup_left)

/-- A word holds the strong hypothesis exactly when it stores none of its content (§4.5). -/
theorem strong_word_iff : (word c s).Strong ↔ Disjoint c s :=
  Finset.subset_sdiff.trans (and_iff_right subset_rfl)

-- §4.5
theorem strong_phrase (h : Disjoint c s) : (phrase c s head nonHead).Strong :=
  (Finset.sdiff_eq_self_of_disjoint h).ge.trans Finset.subset_union_left

-- (73)
theorem cparams_subset_cparams_phrase {d : Sign} {params : Finset Kind}
    (hd : d ∈ insert head nonHead) : d.cparams ⊆ (phrase c s head nonHead params).cparams :=
  (Finset.subset_biUnion_of_mem _ hd).trans Finset.subset_union_right

end Sign

/-! ### The signs of nouns and noun phrases -/

/-- A common noun contributes a property, which it abstracts (28). -/
def cn : Sign := .word {.property} ∅

/-- A determiner contributes a relation between sets, which it abstracts. -/
def det : Sign := .word {.relation} ∅

/-- A quantified noun phrase contributes the witness set its determiner picks out of the noun's
property (72). A definite use abstracts it and an indefinite use stores it. -/
def np : Definiteness → Sign
  | .definite => .phrase {.individual} ∅ cn {det}
  | .indefinite => .phrase {.individual} {.individual} cn {det}

/-- An attributive definite contributes the value of a function at a situation, and abstracts
the function and the situation in place of that value (48). -/
def attributive : Sign := .phrase {.individual} ∅ cn {det} (params := {.function, .situation})

/-- On the generalized-quantifier alternative the content is a quantifier, and a definite use
abstracts a witness set of it (66). -/
def gq : Definiteness → Sign
  | .definite => .phrase {.quantifier} ∅ cn {det} (params := {.individual})
  | .indefinite => .phrase {.quantifier} ∅ cn {det} (params := ∅)

/-- A monotone decreasing noun phrase contributes a reference set with its complement and
stores `store`. It stores both when existentially quantified (92) and neither when referential
(93), and the variant (94) stores the complement set alone. -/
def pair (store : Finset Kind) : Sign := .phrase {.individual, .complement} store cn {det}

-- §3.3
theorem strong_cn : cn.Strong := Sign.strong_word_iff.2 (Finset.disjoint_empty_right _)

/-- Definite noun phrases hold the strong hypothesis (§4.4.2). -/
theorem strong_np : (np .definite).Strong := Sign.strong_phrase (Finset.disjoint_empty_right _)

-- §4.2
theorem indefinite_no_referent : Kind.individual ∉ (np .indefinite).cparams := by decide

-- §4.4.1
theorem cparams_gq (d : Definiteness) : (gq d).cparams = (np d).cparams := by
  cases d <;> decide

/-- The generalized-quantifier alternative never lets a reprise query its content, so it holds
only the weak hypothesis (§4.4.1). -/
theorem not_strong_gq (d : Definiteness) : ¬ (gq d).Strong := by cases d <;> decide

-- §4.1.3
theorem not_strong_attributive : ¬ attributive.Strong := by decide

-- §4.5
theorem attributive_not_definitenessPrinciple : ¬ attributive.DefinitenessPrinciple := by decide

-- (93)
theorem strong_pair : (pair ∅).Strong := Sign.strong_phrase (Finset.disjoint_empty_right _)

/-! ### The corpus readings -/

/-- The sign of each use of a noun phrase the rows distinguish. Referential uses of indefinites
and universals have the sign of a definite, since the paper distinguishes definite uses by their
content being a contextual parameter (§4.2.2, §4.3). -/
def signOfNP : List (String × Sign) :=
  [("cn", cn), ("bareSingular", cn),
    ("demonstrative", np .definite), ("pronoun", np .definite), ("definite", np .definite),
    ("specificIndefinite", np .definite), ("universal", np .definite),
    ("indefinite", np .indefinite), ("negative", np .indefinite), ("wh", np .indefinite),
    ("attributiveDefinite", attributive), ("determiner", det),
    ("monotoneDecreasing", pair {.individual, .complement}),
    ("monotoneDecreasingReferential", pair ∅)]

/-- The kind of object each paraphrase reading queries. -/
def kindOfReading : List (String × Kind) :=
  [("referent", .individual), ("predicate", .property), ("determiner", .relation),
    ("functional", .function), ("domain", .situation), ("complement", .complement)]

/-- A sign predicts the readings of a row when each reading the paper judges possible queries
one of its contextual parameters and no reading the paper marks impossible does. -/
def Sign.Predicts (s : Sign) (r : Datum) : Prop :=
  ∀ p ∈ r.readings, ∃ k ∈ kindOfReading.lookup p.1,
    (p.2 = .acceptable → k ∈ s.cparams) ∧ (p.2 = .unacceptable → k ∉ s.cparams)
deriving Decidable

/-- The sign of each use of a noun phrase predicts the readings of its reprises, (25) to
(90). -/
theorem rows_predicted : ∀ r ∈ Examples.all, ∃ s ∈ r.parse? "np" signOfNP, s.Predicts r := by
  decide

-- (94), (90), (93)
theorem not_predicts_ex90 : ¬ (pair {.complement}).Predicts ex90 := by decide

/-! ### Witness sets and truth conditions -/

section Witness

variable {α : Type*} {Q : Quantifier α} {A X : Set α}

-- (85), §5.5
theorem witness_subset_of_empty (hQ : Q ∅) (X : Set α) : ∃ w, Witness Q A w ∧ w ⊆ X :=
  ⟨∅, ⟨Set.empty_subset A, hQ⟩, Set.empty_subset X⟩

-- (24)
theorem not_witness_iff_of_empty (hQ : Q ∅) (hX : ¬ Q X) :
    ¬ ∀ Y, Q Y ↔ ∃ w, Witness Q A w ∧ w ⊆ Y :=
  fun h ↦ hX ((h X).2 (witness_subset_of_empty hQ X))

/-- A quantifier living on `A` holds of `X` iff some witness set lies inside `X` and the rest of `A`
outside it (91). -/
theorem pair_apply_iff (h : LivesOn Q A) :
    Q X ↔ ∃ R, Witness Q A R ∧ R ⊆ X ∧ A \ R ⊆ Xᶜ := by
  refine h.apply_iff_witness.trans
    ⟨fun hw ↦ ⟨_, hw, Set.inter_subset_right, fun _ ⟨hA, hR⟩ hX ↦ hR ⟨hA, hX⟩⟩, ?_⟩
  rintro ⟨R, hR, hRX, hC⟩
  obtain rfl : R = A ∩ X := Set.Subset.antisymm (Set.subset_inter hR.1 hRX)
    fun _ ⟨hA, hX⟩ ↦ by_contra fun hR' ↦ hC ⟨hA, hR'⟩ hX
  exact hR

end Witness

end PurverGinzburg2004
