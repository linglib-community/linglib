module

public import Linglib.Semantics.Composition.Cont
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Data.Examples.Barker2002
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Infix
import all Init.Data.List.SplitOn.Basic  -- for unfolding `List.splitOn`

/-!
# Barker (2002): Continuations and the nature of quantification

This file formalizes Barker's continuized grammar. A continuation is what the rest of the
sentence does with a constituent's value, and continuizing a grammar hands every constituent its
continuation. Noun phrases then come out as generalized quantifiers, *everyone* and *someone* can
be stated in situ, and they take scope without movement, storage or type-shifting. A rule with
two daughters continuizes in two ways, one per priority order of the daughters, which is where
scope ambiguity comes from. A scope island hands its continuation the finished clause, and
coordination distributes its continuation over the conjuncts.

A derivation is a tree over the direct grammar with each binary node marked for priority.
`Deriv.continuize` is the Continuation Schema, `Deriv.direct` the meaning the direct grammar
assigns, and `Deriv.scopeOrder` the order in which the quantificational items take scope. The
Simulation Theorem (`Deriv.continuize_eq_pure`) says that a derivation the direct grammar
interprets denotes its direct meaning, and Integrity (`Deriv.Constituent.scopeOrder_isInfix`)
that the quantifiers of a constituent are contiguous in the scope order of the sentence.

## Implementation notes

* The paper states the schema for rules of any arity, with one continuized rule per permutation
  of the daughters. Its grammar has rules of arity at most two, and so does `Deriv`.
* The expository determiners, which apply to the continuized nominal, are `Deriv.bind` at a
  generalized-quantifier denotation. The determiners of the final grammar quantify over choice
  functions.
* Transitive verbs take the object first, so `saw m j` is *John saw Mary*.

## TODO

The paper calls the four scopings of *someone saw a friend of everyone* logically distinct. The
restrictor of *a* contains the variable that *everyone* binds, so by
`ChoiceFunction.exists_forall_apply_iff` the two scopings that differ in the order of
*a* and *everyone* are equivalent (`a_everyone_iff_everyone_a`), and the grammar gives the
sentence two truth conditions. A wide-scope *a friend* common to everyone is not among them.

## References

* [barker-2002]
* [partee-rooth-1983]
* [reinhart-1997]
-/

@[expose] public section

namespace Barker2002

variable {ι α β γ E : Type}

/-! ### Derivations and the Continuation Schema -/

/-- The daughter of a binary rule that takes priority, and with it scope over the other. -/
inductive Priority
  | left
  | right
  deriving DecidableEq, Fintype

/-- A derivation with quantificational items labelled in `ι` is a lexical item of the direct
grammar, a quantificational item stated only in continuized terms, a rule of arity one or two
applied to its daughters, a quantificational item applied to the value of its daughter, a clause
closed off as a scope island, or a coordination. -/
inductive Deriv (ι : Type) : Type → Type 1
  | lex {α : Type} (a : α) : Deriv ι α
  | quant {α : Type} (i : ι) (q : Cont Prop α) : Deriv ι α
  | unary {α β : Type} (M : α → β) (d : Deriv ι α) : Deriv ι β
  | binary {α β γ : Type} (M : α → β → γ) (p : Priority) (d₁ : Deriv ι α) (d₂ : Deriv ι β) :
      Deriv ι γ
  | bind {α β : Type} (i : ι) (q : α → Cont Prop β) (d : Deriv ι α) : Deriv ι β
  | island (d : Deriv ι Prop) : Deriv ι Prop
  | coord {α : Type} (d₁ d₂ : Deriv ι α) : Deriv ι α

namespace Deriv

/-- The Continuation Schema makes a lexical item a unit and has a rule nest the continuations
of its daughters in priority order. An island evaluates its clause, and coordination hands its
continuation to each conjunct. -/
def continuize : ∀ {α : Type}, Deriv ι α → Cont Prop α
  | _, lex a => pure a
  | _, quant _ q => q
  | _, unary M d => M <$> d.continuize
  | _, binary M .left d₁ d₂ => M <$> d₁.continuize <*> d₂.continuize
  | _, binary M .right d₁ d₂ => flip M <$> d₂.continuize <*> d₁.continuize
  | _, bind _ q d => d.continuize >>= q
  | _, island d => ContT.reset d.continuize
  | _, coord d₁ d₂ => fun k ↦ d₁.continuize k ∧ d₂.continuize k

/-- The sentence meaning is the continuized meaning at the trivial continuation. -/
def eval (d : Deriv ι Prop) : Prop := ContT.eval d.continuize

/-- The meaning the direct grammar assigns, where it assigns one. -/
def direct : ∀ {α : Type}, Deriv ι α → Option α
  | _, lex a => some a
  | _, unary M d => d.direct.map M
  | _, binary M _ d₁ d₂ => d₁.direct.bind fun x ↦ d₂.direct.map (M x)
  | _, island d => d.direct
  | _, quant _ _ | _, bind _ _ _ | _, coord _ _ => none

/-- The quantificational items in the order they take scope. Those of an island are trapped,
and those of a coordination are listed together although neither conjunct outscopes the
other. -/
def scopeOrder : ∀ {α : Type}, Deriv ι α → List ι
  | _, lex _ | _, island _ => []
  | _, quant i _ => [i]
  | _, unary _ d => d.scopeOrder
  | _, binary _ .left d₁ d₂ | _, coord d₁ d₂ => d₁.scopeOrder ++ d₂.scopeOrder
  | _, binary _ .right d₁ d₂ => d₂.scopeOrder ++ d₁.scopeOrder
  | _, bind i _ d => d.scopeOrder ++ [i]

/-! ### Simulation -/

/-- The lemma behind the Simulation Theorem says that a derivation the direct grammar interprets
denotes the unit at its direct meaning. -/
theorem continuize_eq_pure {d : Deriv ι α} {a : α} (h : d.direct = some a) :
    d.continuize = pure a := by
  induction d with
  | lex b => cases h; rfl
  | quant | bind | coord => cases h
  | unary M d ih =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [continuize, ih hb, map_pure]
  | binary M p d₁ d₂ ih₁ ih₂ =>
    simp only [direct, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    cases p <;> simp only [continuize, ih₁ hb₁, ih₂ hb₂] <;> rfl
  | island d ih => rw [continuize, ih h, ContT.reset_pure]

/-- The Simulation Theorem says that at the trivial continuation the continuized grammar
computes the direct meaning. -/
theorem eval_eq_of_direct {d : Deriv ι Prop} {p : Prop} (h : d.direct = some p) : d.eval = p := by
  rw [eval, continuize_eq_pure h]; rfl

/-- Closing a clause off as an island leaves its own meaning alone. -/
@[simp] theorem eval_island (d : Deriv ι Prop) : (island d).eval = d.eval :=
  ContT.eval_reset _

/-- Priority is idle next to a left daughter that the direct grammar interprets. -/
theorem continuize_binary_of_direct_left (M : α → β → γ) (p : Priority) {d₁ : Deriv ι α} {a : α}
    (h : d₁.direct = some a) (d₂ : Deriv ι β) :
    (binary M p d₁ d₂).continuize = M a <$> d₂.continuize := by
  cases p <;> simp only [continuize, continuize_eq_pure h] <;> rfl

/-- Priority is idle next to a right daughter that the direct grammar interprets. -/
theorem continuize_binary_of_direct_right (M : α → β → γ) (p : Priority) (d₁ : Deriv ι α)
    {d₂ : Deriv ι β} {b : β} (h : d₂.direct = some b) :
    (binary M p d₁ d₂).continuize = (M · b) <$> d₁.continuize := by
  cases p <;> simp only [continuize, continuize_eq_pure h] <;> rfl

/-! ### Integrity -/

/-- `Constituent d' d` says that `d'` is a constituent of `d` that no island separates from
it. -/
inductive Constituent : ∀ {α β : Type}, Deriv ι α → Deriv ι β → Prop
  | refl {α : Type} (d : Deriv ι α) : Constituent d d
  | unary {α β γ : Type} {d' : Deriv ι α} {d : Deriv ι β} (M : β → γ) :
      Constituent d' d → Constituent d' (unary M d)
  | binaryLeft {α β γ δ : Type} {d' : Deriv ι α} {d₁ : Deriv ι β} (M : β → γ → δ) (p : Priority)
      (d₂ : Deriv ι γ) : Constituent d' d₁ → Constituent d' (binary M p d₁ d₂)
  | binaryRight {α β γ δ : Type} {d' : Deriv ι α} {d₂ : Deriv ι γ} (M : β → γ → δ)
      (p : Priority) (d₁ : Deriv ι β) : Constituent d' d₂ → Constituent d' (binary M p d₁ d₂)
  | bind {α β γ : Type} {d' : Deriv ι α} {d : Deriv ι β} (i : ι) (q : β → Cont Prop γ) :
      Constituent d' d → Constituent d' (bind i q d)
  | coordLeft {α β : Type} {d' : Deriv ι α} {d₁ : Deriv ι β} (d₂ : Deriv ι β) :
      Constituent d' d₁ → Constituent d' (coord d₁ d₂)
  | coordRight {α β : Type} {d' : Deriv ι α} {d₂ : Deriv ι β} (d₁ : Deriv ι β) :
      Constituent d' d₂ → Constituent d' (coord d₁ d₂)

namespace Constituent

variable {d' : Deriv ι α} {d : Deriv ι β}

/-- Integrity says that the quantifiers of a constituent are contiguous in the scope order of
the whole, so an outside quantifier scopes over all of them or under all of them. -/
theorem scopeOrder_isInfix (h : Constituent d' d) : d'.scopeOrder <:+: d.scopeOrder := by
  induction h with
  | refl => exact List.infix_rfl
  | unary _ _ ih => exact ih
  | binaryLeft _ p _ _ ih =>
    cases p
    · exact ih.trans (List.prefix_append _ _).isInfix
    · exact ih.trans (List.suffix_append _ _).isInfix
  | binaryRight _ p _ _ ih =>
    cases p
    · exact ih.trans (List.suffix_append _ _).isInfix
    · exact ih.trans (List.prefix_append _ _).isInfix
  | bind _ _ _ ih => exact ih.trans (List.prefix_append _ _).isInfix
  | coordLeft _ _ ih => exact ih.trans (List.prefix_append _ _).isInfix
  | coordRight _ _ ih => exact ih.trans (List.suffix_append _ _).isInfix

/-- Integrity is a test on a scope order in which no item occurs twice, since the items of a
constituent are then an uninterrupted stretch of the order. -/
theorem filter_scopeOrder_isInfix [DecidableEq ι] (h : Constituent d' d)
    (hd : d.scopeOrder.Nodup) :
    d.scopeOrder.filter (· ∈ d'.scopeOrder) <:+: d.scopeOrder := by
  obtain ⟨s, t, hst⟩ := h.scopeOrder_isInfix
  rw [← hst] at hd ⊢
  have hs : s.filter (· ∈ d'.scopeOrder) = [] := List.filter_eq_nil_iff.mpr fun x hx ↦ by
    simpa using List.disjoint_of_nodup_append hd.of_append_left hx
  have ht : t.filter (· ∈ d'.scopeOrder) = [] := List.filter_eq_nil_iff.mpr fun x hx ↦ by
    simpa using fun hx' ↦ List.disjoint_of_nodup_append hd (List.mem_append_right _ hx') hx
  have hm : d'.scopeOrder.filter (· ∈ d'.scopeOrder) = d'.scopeOrder :=
    List.filter_eq_self.mpr (by simp)
  rw [List.filter_append, List.filter_append, hs, ht, hm]
  exact ⟨s, t, by simp⟩

end Constituent

end Deriv

/-! ### The grammar -/

open Deriv

/-- S → NP VP, `VP(NP)`. -/
def S (p : Priority) (np : Deriv ι E) (vp : Deriv ι (E → Prop)) : Deriv ι Prop :=
  binary (fun x P ↦ P x) p np vp

/-- VP → Vt NP, `Vt(NP)`. -/
def VP (p : Priority) (vt : Deriv ι (E → E → Prop)) (obj : Deriv ι E) : Deriv ι (E → Prop) :=
  binary (fun R x ↦ R x) p vt obj

/-- VP → Vs S, `Vs(S)`. -/
def VS (p : Priority) (vs : Deriv ι (Prop → E → Prop)) (s : Deriv ι Prop) :
    Deriv ι (E → Prop) :=
  binary (fun T q ↦ T q) p vs s

/-- NP → Det N, `Det(N)`, with determiners denoting choice functions. -/
def NP (p : Priority) (det : Deriv ι (ChoiceFunction E)) (n : Deriv ι (E → Prop)) : Deriv ι E :=
  binary (fun D P ↦ D P) p det n

/-- N → Nr PPof, `Nr(PP)`. -/
def N (p : Priority) (nr : Deriv ι (E → E → Prop)) (pp : Deriv ι E) : Deriv ι (E → Prop) :=
  binary (fun R x ↦ R x) p nr pp

/-- PPof → of NP, with a transparent preposition. -/
def PPof (np : Deriv ι E) : Deriv ι E := unary id np

/-- *everyone* is a universal over its continuation. -/
def everyone : Deriv String E := quant "everyone" fun k ↦ ∀ x, k x

/-- *someone* is an existential over its continuation. -/
def someone : Deriv String E := quant "someone" fun k ↦ ∃ x, k x

/-- The expository NP → Det N applies a generalized-quantifier determiner to the continuized
nominal, so the determiner scopes under whatever the nominal contains. -/
def NPgq (w : String) (Q : Quantifier.GQ E) (n : Deriv String (E → Prop)) : Deriv String E :=
  bind w (fun P ↦ Q P) n

/-- *every* quantifies universally over choice functions. -/
def every : Deriv String (ChoiceFunction E) := quant "every" fun D ↦ ∀ f, D f

/-- *a* quantifies existentially over choice functions. -/
def a : Deriv String (ChoiceFunction E) := quant "a" fun D ↦ ∃ f, D f

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' friendOf : E → E → Prop)
  (thought' : Prop → E → Prop) (the : ChoiceFunction E)

/-! ### Scope displacement and scope ambiguity -/

theorem john_left (p : Priority) : (S p (lex j) (lex left' : Deriv ι _)).eval = left' j :=
  eval_eq_of_direct (by cases p <;> rfl)

theorem everyone_left (p : Priority) : (S p everyone (lex left')).eval = ∀ x, left' x := by
  cases p <;> rfl

/-- A quantifier in object position takes scope over the clause, whatever determiner it has, as
in *John saw every man* and *John saw most men*. -/
theorem john_saw_NPgq (w : String) (Q : Quantifier.GQ E) (p p' : Priority) :
    (S p (lex j) (VP p' (lex saw') (NPgq w Q (lex man')))).eval = Q man' (saw' · j) := by
  cases p <;> cases p' <;> rfl

/-- *Every man saw a woman* with VP priority has the inverse reading. -/
theorem every_man_saw_a_woman_inverse (p : Priority) :
    (S .right (NPgq "every" Quantifier.GQ.every (lex man'))
      (VP p (lex saw') (NPgq "a" Quantifier.GQ.some (lex woman')))).eval =
      ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := by
  cases p <;> rfl

/-- With subject priority it has the surface reading. -/
theorem every_man_saw_a_woman_surface (p : Priority) :
    (S .left (NPgq "every" Quantifier.GQ.every (lex man'))
      (VP p (lex saw') (NPgq "a" Quantifier.GQ.some (lex woman')))).eval =
      ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := by
  cases p <;> rfl

/-- In *a man thought everyone saw Mary* the island traps *everyone* under every priority. -/
theorem a_man_thought_everyone_saw_mary (p₁ p₂ p₃ p₄ : Priority) :
    (S p₁ (NPgq "a" Quantifier.GQ.some (lex man'))
      (VS p₂ (lex thought') (island (S p₃ everyone (VP p₄ (lex saw') (lex m)))))).eval =
      ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := by
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases p₄ <;> rfl

/-- In *someone saw the friend of the friend of everyone* the embedded quantifier takes scope
from any depth, and the priority at S decides between the two scopings. -/
theorem someone_saw_the_friend_of_the_friend_of_everyone (p : Priority) :
    (S p someone (VP .left (lex saw') (NP .left (lex the) (N .left (lex friendOf)
      (PPof (NP .left (lex the) (N .left (lex friendOf) (PPof everyone)))))))).eval =
      match p with
      | .left => ∃ x, ∀ y, saw' (the (friendOf (the (friendOf y)))) x
      | .right => ∀ y, ∃ x, saw' (the (friendOf (the (friendOf y)))) x := by
  cases p <;> rfl

/-! ### Choice-function determiners -/

/-- *John saw every man* says that for every way of choosing a man, John saw him. -/
theorem john_saw_every_man (p₁ p₂ p₃ : Priority) :
    (S p₁ (lex j) (VP p₂ (lex saw') (NP p₃ every (lex man')))).eval =
      ∀ f : ChoiceFunction E, saw' (f man') j := by
  cases p₁ <;> cases p₂ <;> cases p₃ <;> rfl

/-- When there are men, the choice-function *every* and the generalized-quantifier *every*
give *John saw every man* the same truth conditions. -/
theorem john_saw_every_man_iff (hman : ∃ x, man' x) (p₁ p₂ p₃ : Priority) :
    (S p₁ (lex j) (VP p₂ (lex saw') (NP p₃ every (lex man')))).eval ↔
      Quantifier.GQ.every man' (saw' · j) := by
  rw [john_saw_every_man]
  exact ChoiceFunction.forall_apply_iff_every hman (saw' · j)

/-- When there are no men they come apart, since the choice-function sentence says that John
saw everyone and the generalized-quantifier sentence is vacuously true. -/
theorem john_saw_every_man_iff_of_not_exists (hman : ¬ ∃ x, man' x) (p₁ p₂ p₃ : Priority) :
    (S p₁ (lex j) (VP p₂ (lex saw') (NP p₃ every (lex man')))).eval ↔ ∀ x, saw' x j := by
  rw [john_saw_every_man]
  exact ChoiceFunction.forall_apply_iff_of_not_exists hman (saw' · j)

/-! ### The scopings of *someone saw a friend of everyone* -/

/-- The derivation, with a priority at the S, VP, NP and N nodes. -/
def someoneSawAFriendOfEveryone (pS pVP pNP pN : Priority) : Deriv String Prop :=
  S pS someone (VP pVP (lex saw') (NP pNP a (N pN (lex friendOf) (PPof everyone))))

/-- The priorities at S and NP fix the scope order. -/
theorem scopeOrder_someoneSawAFriendOfEveryone (pS pVP pNP pN : Priority) :
    (someoneSawAFriendOfEveryone saw' friendOf pS pVP pNP pN).scopeOrder =
      match pS, pNP with
      | .left, .left => ["someone", "a", "everyone"]
      | .left, .right => ["someone", "everyone", "a"]
      | .right, .left => ["a", "everyone", "someone"]
      | .right, .right => ["everyone", "a", "someone"] := by
  cases pS <;> cases pVP <;> cases pNP <;> cases pN <;> rfl

/-- The truth conditions follow the scope order. -/
theorem eval_someoneSawAFriendOfEveryone (pS pVP pNP pN : Priority) :
    (someoneSawAFriendOfEveryone saw' friendOf pS pVP pNP pN).eval =
      match pS, pNP with
      | .left, .left => ∃ y, ∃ f : ChoiceFunction E, ∀ x, saw' (f (friendOf x)) y
      | .left, .right => ∃ y, ∀ x, ∃ f : ChoiceFunction E, saw' (f (friendOf x)) y
      | .right, .left => ∃ f : ChoiceFunction E, ∀ x, ∃ y, saw' (f (friendOf x)) y
      | .right, .right => ∀ x, ∃ f : ChoiceFunction E, ∃ y, saw' (f (friendOf x)) y := by
  cases pS <;> cases pVP <;> cases pNP <;> cases pN <;> rfl

/-- The priority at NP orders the object's two quantifiers. -/
theorem scopeOrder_object (pNP pN : Priority) :
    (NP pNP a (N pN (lex friendOf) (PPof everyone))).scopeOrder =
      match pNP with
      | .left => ["a", "everyone"]
      | .right => ["everyone", "a"] := by
  cases pNP <;> cases pN <;> rfl

/-- The object noun phrase is a constituent of the sentence. -/
theorem constituent_object (pS pVP pNP pN : Priority) :
    Constituent (NP pNP a (N pN (lex friendOf) (PPof everyone)))
      (someoneSawAFriendOfEveryone saw' friendOf pS pVP pNP pN) :=
  .binaryRight _ _ _ (.binaryRight _ _ _ (.refl _))

/-- Integrity excludes the orders that split the object's quantifiers around the subject. -/
theorem no_split_scoping (pS pVP pNP pN : Priority) :
    (someoneSawAFriendOfEveryone saw' friendOf pS pVP pNP pN).scopeOrder ≠
        ["everyone", "someone", "a"] ∧
      (someoneSawAFriendOfEveryone saw' friendOf pS pVP pNP pN).scopeOrder ≠
        ["a", "someone", "everyone"] := by
  have h := (constituent_object saw' friendOf pS pVP pNP pN).scopeOrder_isInfix
  rw [scopeOrder_object] at h
  constructor <;> intro h' <;> rw [h'] at h <;> cases pNP <;> exact absurd h (by decide)

/-- The order of *a* and *everyone* makes no difference to the truth conditions, because the
restrictor of *a* contains the variable that *everyone* binds. -/
theorem a_everyone_iff_everyone_a [Nonempty E] (pS pVP pN pVP' pN' : Priority) :
    (someoneSawAFriendOfEveryone saw' friendOf pS pVP .left pN).eval ↔
      (someoneSawAFriendOfEveryone saw' friendOf pS pVP' .right pN').eval := by
  rw [eval_someoneSawAFriendOfEveryone, eval_someoneSawAFriendOfEveryone]
  cases pS
  · exact exists_congr fun y ↦ ChoiceFunction.exists_forall_apply_iff friendOf (saw' · y)
  · exact ChoiceFunction.exists_forall_apply_iff friendOf fun z ↦ ∃ y, saw' z y

/-! ### Generalized coordination -/

/-- With subject priority, coordinated verb phrases denote their pointwise conjunction, as in
Partee and Rooth's generalized conjunction. -/
theorem coord_VP_subject_priority (np : Deriv ι E) (P Q : E → Prop) :
    (S .left np (coord (lex P) (lex Q))).eval = (S .left np (lex (P ⊓ Q))).eval :=
  rfl

/-- With VP priority the conjunction distributes over the subject. -/
theorem coord_VP_priority (np : Deriv ι E) (P Q : E → Prop) :
    (S .right np (coord (lex P) (lex Q))).eval =
      ((S .right np (lex P)).eval ∧ (S .right np (lex Q)).eval) :=
  rfl

/-- Coordinated noun phrases need no conjoinable type, as in *John and Mary left*. -/
theorem john_and_mary_left (p : Priority) :
    (S p (coord (lex j) (lex m)) (lex left' : Deriv ι _)).eval = (left' j ∧ left' m) := by
  cases p <;> rfl

/-! ### The paper's examples -/

/-- The words of a string, split at a separator. -/
def wordsOn (c : Char) (s : String) : List String :=
  (s.toList.splitOn c).filterMap fun cs ↦
    let w := cs.filter (· ≠ ' ')
    if w = [] then none else some (String.ofList w)

/-- The readings the paper lists for *someone saw a friend of everyone* are exactly the scope
orders some prioritization of its derivation induces. -/
theorem rows_scopings : ∀ e ∈ Examples.all,
    e.feature? "derivation" = some "someone saw a friend of everyone" → ∀ r ∈ e.readings,
      (r.2 = .acceptable ↔ ∃ pS pVP pNP pN : Priority,
        (someoneSawAFriendOfEveryone (E := Unit) (fun _ _ ↦ True) (fun _ _ ↦ True)
          pS pVP pNP pN).scopeOrder = wordsOn '>' r.1) := by
  decide +kernel

/-- Wherever the paper names a constituent holding two of a sentence's quantifiers, the
readings it accepts are those that keep the two together, as
`Deriv.Constituent.filter_scopeOrder_isInfix` requires. -/
theorem rows_integrity : ∀ e ∈ Examples.all, ∀ c ∈ e.feature? "constituent",
    ∀ r ∈ e.readings, (r.2 = .acceptable ↔
      (wordsOn '>' r.1).filter (· ∈ wordsOn ' ' c) <:+: wordsOn '>' r.1) := by
  decide +kernel

end Barker2002
