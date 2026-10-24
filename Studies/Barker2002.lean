module

public import Linglib.Semantics.Composition.Cont
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Data.Examples.Barker2002
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Infix
import all Init.Data.List.SplitOn.Basic  -- for unfolding `List.splitOn`

/-!
# Barker (2002): Continuations and the nature of quantification

This file formalizes Barker's continuized grammar. A continuation is what the rest of the
sentence does with a constituent's value, and continuizing a grammar hands every constituent its
continuation. Noun phrases then come out as generalized quantifiers, *everyone* and *someone* can
be stated in situ, and they take scope without movement, storage or type-shifting. A rule with
`n` daughters continuizes in `n!` ways, one per order in which its daughters take scope, which is
where scope ambiguity comes from. A scope island hands its continuation the finished clause, and
coordination distributes its continuation over the conjuncts.

A derivation is a tree whose nodes are rules of the direct grammar, each marked with a permutation
of its daughters. `Deriv.continuize` is the Continuation Schema, `Deriv.direct` the meaning the
direct grammar assigns, and `Deriv.scopeOrder` the order in which the quantificational items take
scope. The Simulation Theorem (`Deriv.continuize_eq_pure`) says that a derivation the direct
grammar interprets denotes its direct meaning, and Integrity
(`Deriv.Constituent.scopeOrder_isInfix`) that the quantifiers of a constituent are contiguous in
the scope order of the sentence.

## Implementation notes

* A rule of arity `n` carries a permutation `σ` of its daughters, and the schema runs daughter
  `σ 0` first, so that it takes widest scope. A lexical item is a rule of arity zero, and the
  identity and the swap of `Fin 2` are the two priorities of a binary rule.
* The expository determiners, which apply to the continuized nominal, are `Deriv.bind` at a
  generalized-quantifier denotation. The determiners of the final grammar quantify over choice
  functions.
* Transitive verbs take the object first, so `saw m j` is *John saw Mary*.

## Errata

* The paper calls the four scopings of *someone saw a friend of everyone* logically distinct. The
  restrictor of *a* contains the variable that *everyone* binds, so by
  `ChoiceFunction.exists_forall_apply_iff` the two scopings that differ in the order of *a* and
  *everyone* are equivalent (`a_everyone_iff_everyone_a`), and the grammar gives the sentence two
  truth conditions.
* The choice-function determiners agree with the generalized quantifiers of the expository
  grammar only on a nonempty restrictor. A choice function may pick anything from the empty
  property, so without men *John saw every man* says that John saw everyone
  (`john_saw_every_man_iff_of_not_exists`).

## TODO

Derivations of (22a), (23a) and (26a), which need the rules N → N PP and PP → P NP, the
determiner *two*, and a ditransitive verb.

## References

* [barker-2002]
* [partee-rooth-1983]
* [reinhart-1997]
-/

@[expose] public section

namespace Barker2002

variable {ι α β γ E : Type}

/-! ### Running a tuple of computations -/

/-- `sequence c` runs the computations `c 0, c 1, …` in order and collects their values, the
`sequence` of a tuple whose entries may differ in type. -/
def sequence {m : Type → Type} [Monad m] : {n : ℕ} → {α : Fin n → Type} →
    ((i : Fin n) → m (α i)) → m ((i : Fin n) → α i)
  | 0, _, _ => pure finZeroElim
  | _ + 1, _, c => do
    let x ← c 0
    let xs ← sequence fun i ↦ c i.succ
    pure (Fin.cons x xs)

theorem sequence_pure {m : Type → Type} [Monad m] [LawfulMonad m] :
    {n : ℕ} → {α : Fin n → Type} → (a : (i : Fin n) → α i) →
    sequence (m := m) (fun i ↦ pure (a i)) = pure a
  | 0, _, _ => congrArg pure (funext fun i ↦ i.elim0)
  | _ + 1, _, a => by
    simp only [sequence, pure_bind, sequence_pure fun i ↦ a i.succ]
    exact congrArg pure (Fin.cons_self_tail a)

theorem sequence_eq_some : {n : ℕ} → {α : Fin n → Type} → {c : (i : Fin n) → Option (α i)} →
    {a : (i : Fin n) → α i} → sequence c = some a ↔ ∀ i, c i = some (a i)
  | 0, _, _, _ =>
    ⟨fun _ i ↦ i.elim0, fun _ ↦ congrArg some (funext fun i ↦ i.elim0)⟩
  | _ + 1, _, c, a => by
    simp only [sequence, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Fin.forall_fin_succ]
    constructor
    · rintro ⟨x, hx, xs, hxs, rfl⟩
      exact ⟨hx, fun i ↦ sequence_eq_some.mp hxs i⟩
    · rintro ⟨h₀, hs⟩
      exact ⟨a 0, h₀, fun i ↦ a i.succ, sequence_eq_some.mpr hs, Fin.cons_self_tail a⟩

/-! ### Derivations and the Continuation Schema -/

theorem perm_fin_two (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  decide +revert

/-- A derivation with quantificational items labelled in `ι` is a rule of the direct grammar of
some arity applied to its daughters in the order of a permutation, a quantificational item stated
only in continuized terms, a quantificational item applied to the value of its daughter, a clause
closed off as a scope island, or a coordination. -/
inductive Deriv (ι : Type) : Type → Type 1
  | node {n : ℕ} {α : Fin n → Type} {β : Type} (M : ((i : Fin n) → α i) → β)
      (σ : Equiv.Perm (Fin n)) (d : (i : Fin n) → Deriv ι (α i)) : Deriv ι β
  | quant {α : Type} (i : ι) (q : Cont Prop α) : Deriv ι α
  | bind {α β : Type} (i : ι) (q : α → Cont Prop β) (d : Deriv ι α) : Deriv ι β
  | island (d : Deriv ι Prop) : Deriv ι Prop
  | coord {α : Type} (d₁ d₂ : Deriv ι α) : Deriv ι α

namespace Deriv

/-- The Continuation Schema has a rule nest the continuations of its daughters in the order of
its permutation. An island evaluates its clause, and coordination hands its continuation to each
conjunct. -/
def continuize : ∀ {α : Type}, Deriv ι α → Cont Prop α
  | _, node (α := α) M σ d =>
    (M ∘ Equiv.piCongrLeft α σ) <$> sequence fun k ↦ (d (σ k)).continuize
  | _, quant _ q => q
  | _, bind _ q d => d.continuize >>= q
  | _, island d => ContT.reset d.continuize
  | _, coord d₁ d₂ => fun k ↦ d₁.continuize k ∧ d₂.continuize k

/-- The sentence meaning is the continuized meaning at the trivial continuation. -/
def eval (d : Deriv ι Prop) : Prop := ContT.eval d.continuize

/-- The meaning the direct grammar assigns, where it assigns one. -/
def direct : ∀ {α : Type}, Deriv ι α → Option α
  | _, node M _ d => M <$> sequence fun i ↦ (d i).direct
  | _, island d => d.direct
  | _, quant _ _ | _, bind _ _ _ | _, coord _ _ => none

/-- The quantificational items in the order they take scope. Those of an island are trapped,
and those of a coordination are listed together although neither conjunct outscopes the
other. -/
def scopeOrder : ∀ {α : Type}, Deriv ι α → List ι
  | _, node _ σ d => (List.ofFn fun k ↦ (d (σ k)).scopeOrder).flatten
  | _, quant i _ => [i]
  | _, bind i _ d => d.scopeOrder ++ [i]
  | _, island _ => []
  | _, coord d₁ d₂ => d₁.scopeOrder ++ d₂.scopeOrder

/-- A lexical item is a rule of arity zero. -/
abbrev lex (a : α) : Deriv ι α :=
  node (α := Fin.elim0) (fun _ ↦ a) 1 finZeroElim

/-- A rule of arity one. -/
abbrev unary (M : α → β) (d : Deriv ι α) : Deriv ι β :=
  node (n := 1) (α := fun _ ↦ α) (fun x ↦ M (x 0)) 1 fun _ ↦ d

/-- A rule of arity two, where the identity gives the left daughter priority and the swap the
right daughter. -/
abbrev binary (M : α → β → γ) (σ : Equiv.Perm (Fin 2)) (d₁ : Deriv ι α) (d₂ : Deriv ι β) :
    Deriv ι γ :=
  node (α := ![α, β]) (fun x ↦ M (x 0) (x 1)) σ (Fin.cons d₁ (Fin.cons d₂ finZeroElim))

theorem continuize_unary (M : α → β) (d : Deriv ι α) :
    (unary M d).continuize = M <$> d.continuize :=
  rfl

theorem continuize_binary_one (M : α → β → γ) (d₁ : Deriv ι α) (d₂ : Deriv ι β) :
    (binary M 1 d₁ d₂).continuize = M <$> d₁.continuize <*> d₂.continuize :=
  rfl

theorem continuize_binary_swap (M : α → β → γ) (d₁ : Deriv ι α) (d₂ : Deriv ι β) :
    (binary M (Equiv.swap 0 1) d₁ d₂).continuize = flip M <$> d₂.continuize <*> d₁.continuize :=
  rfl

/-! ### Simulation -/

theorem continuize_eq_pure {d : Deriv ι α} {a : α} (h : d.direct = some a) :
    d.continuize = pure a := by
  induction d with
  | quant | bind | coord => cases h
  | node M σ d ih =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    have ht := sequence_eq_some.mp ht
    simp only [continuize, fun k ↦ ih (σ k) (ht (σ k)), sequence_pure, map_pure,
      Function.comp_apply]
    congr 2
    exact (Equiv.piCongrLeft _ σ).apply_symm_apply t
  | island d ih => rw [continuize, ih h, ContT.reset_pure]

theorem eval_eq_of_direct {d : Deriv ι Prop} {p : Prop} (h : d.direct = some p) : d.eval = p := by
  rw [eval, continuize_eq_pure h]; rfl

@[simp] theorem eval_island (d : Deriv ι Prop) : (island d).eval = d.eval :=
  ContT.eval_reset _

theorem continuize_binary_of_direct_left (M : α → β → γ) (σ : Equiv.Perm (Fin 2))
    {d₁ : Deriv ι α} {a : α} (h : d₁.direct = some a) (d₂ : Deriv ι β) :
    (binary M σ d₁ d₂).continuize = M a <$> d₂.continuize := by
  rcases perm_fin_two σ with rfl | rfl <;>
    simp only [continuize_binary_one, continuize_binary_swap, continuize_eq_pure h] <;> rfl

theorem continuize_binary_of_direct_right (M : α → β → γ) (σ : Equiv.Perm (Fin 2))
    (d₁ : Deriv ι α) {d₂ : Deriv ι β} {b : β} (h : d₂.direct = some b) :
    (binary M σ d₁ d₂).continuize = (M · b) <$> d₁.continuize := by
  rcases perm_fin_two σ with rfl | rfl <;>
    simp only [continuize_binary_one, continuize_binary_swap, continuize_eq_pure h] <;> rfl

/-! ### Integrity -/

/-- `Constituent d' d` says that `d'` is a constituent of `d` that no island separates from
it. -/
inductive Constituent : ∀ {α β : Type}, Deriv ι α → Deriv ι β → Prop
  | refl {α : Type} (d : Deriv ι α) : Constituent d d
  | node {n : ℕ} {α : Fin n → Type} {β γ : Type} {d' : Deriv ι γ} (M : ((i : Fin n) → α i) → β)
      (σ : Equiv.Perm (Fin n)) (d : (i : Fin n) → Deriv ι (α i)) (i : Fin n) :
      Constituent d' (d i) → Constituent d' (node M σ d)
  | bind {α β γ : Type} {d' : Deriv ι α} {d : Deriv ι β} (i : ι) (q : β → Cont Prop γ) :
      Constituent d' d → Constituent d' (bind i q d)
  | coordLeft {α β : Type} {d' : Deriv ι α} {d₁ : Deriv ι β} (d₂ : Deriv ι β) :
      Constituent d' d₁ → Constituent d' (coord d₁ d₂)
  | coordRight {α β : Type} {d' : Deriv ι α} {d₂ : Deriv ι β} (d₁ : Deriv ι β) :
      Constituent d' d₂ → Constituent d' (coord d₁ d₂)

namespace Constituent

variable {d' : Deriv ι α} {d : Deriv ι β}

theorem scopeOrder_isInfix (h : Constituent d' d) : d'.scopeOrder <:+: d.scopeOrder := by
  induction h with
  | refl => exact List.infix_rfl
  | node _ σ d i _ ih =>
    refine ih.trans (List.infix_of_mem_flatten (List.mem_ofFn.mpr ⟨σ.symm i, ?_⟩))
    rw [σ.apply_symm_apply]
  | bind _ _ _ ih => exact ih.trans (List.prefix_append _ _).isInfix
  | coordLeft _ _ ih => exact ih.trans (List.prefix_append _ _).isInfix
  | coordRight _ _ ih => exact ih.trans (List.suffix_append _ _).isInfix

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
def S (σ : Equiv.Perm (Fin 2)) (np : Deriv ι E) (vp : Deriv ι (E → Prop)) : Deriv ι Prop :=
  binary (fun x P ↦ P x) σ np vp

/-- VP → Vt NP, `Vt(NP)`. -/
def VP (σ : Equiv.Perm (Fin 2)) (vt : Deriv ι (E → E → Prop)) (obj : Deriv ι E) :
    Deriv ι (E → Prop) :=
  binary (fun R x ↦ R x) σ vt obj

/-- VP → Vs S, `Vs(S)`. -/
def VS (σ : Equiv.Perm (Fin 2)) (vs : Deriv ι (Prop → E → Prop)) (s : Deriv ι Prop) :
    Deriv ι (E → Prop) :=
  binary (fun T q ↦ T q) σ vs s

/-- NP → Det N, `Det(N)`, with determiners denoting choice functions. -/
def NP (σ : Equiv.Perm (Fin 2)) (det : Deriv ι (ChoiceFunction E)) (n : Deriv ι (E → Prop)) :
    Deriv ι E :=
  binary (fun D P ↦ D P) σ det n

/-- N → Nr PPof, `Nr(PP)`. -/
def N (σ : Equiv.Perm (Fin 2)) (nr : Deriv ι (E → E → Prop)) (pp : Deriv ι E) :
    Deriv ι (E → Prop) :=
  binary (fun R x ↦ R x) σ nr pp

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

/-- *no* says that no choice function satisfies its continuation. -/
def no : Deriv String (ChoiceFunction E) := quant "no" fun D ↦ ¬ ∃ f, D f

/-- *most* quantifies over sets of choice functions that pick more than half of every
property. -/
def most : Deriv String (ChoiceFunction E) :=
  quant "most" fun D ↦ ∃ C : Set (ChoiceFunction E),
    (∀ P : E → Prop, {x | P x}.ncard < 2 * ((· P) '' C).ncard) ∧ ∀ f ∈ C, D f

variable (j m : E) (left' man' woman' : E → Prop) (saw' friendOf : E → E → Prop)
  (thought' : Prop → E → Prop) (the : ChoiceFunction E)

/-! ### Scope displacement and scope ambiguity -/

theorem john_left (σ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (lex left' : Deriv ι _)).eval = left' j :=
  eval_eq_of_direct rfl

theorem everyone_left (σ : Equiv.Perm (Fin 2)) :
    (S σ everyone (lex left')).eval = ∀ x, left' x := by
  rcases perm_fin_two σ with rfl | rfl <;> rfl

theorem john_saw_NPgq (w : String) (Q : Quantifier.GQ E) (σ τ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NPgq w Q (lex man')))).eval = Q man' (saw' · j) := by
  rw [eval, S, continuize_binary_of_direct_left _ _ rfl, VP,
    continuize_binary_of_direct_left _ _ rfl]
  rfl

theorem every_man_saw_a_woman_inverse (σ : Equiv.Perm (Fin 2)) :
    (S (Equiv.swap 0 1) (NPgq "every" Quantifier.GQ.every (lex man'))
      (VP σ (lex saw') (NPgq "a" Quantifier.GQ.some (lex woman')))).eval =
      ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := by
  rcases perm_fin_two σ with rfl | rfl <;> rfl

theorem every_man_saw_a_woman_surface (σ : Equiv.Perm (Fin 2)) :
    (S 1 (NPgq "every" Quantifier.GQ.every (lex man'))
      (VP σ (lex saw') (NPgq "a" Quantifier.GQ.some (lex woman')))).eval =
      ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := by
  rcases perm_fin_two σ with rfl | rfl <;> rfl

theorem a_man_thought_everyone_saw_mary (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 2)) :
    (S σ₁ (NPgq "a" Quantifier.GQ.some (lex man'))
      (VS σ₂ (lex thought') (island (S σ₃ everyone (VP σ₄ (lex saw') (lex m)))))).eval =
      ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := by
  rcases perm_fin_two σ₁ with rfl | rfl <;> rcases perm_fin_two σ₂ with rfl | rfl <;>
    rcases perm_fin_two σ₃ with rfl | rfl <;> rcases perm_fin_two σ₄ with rfl | rfl <;> rfl

/-- *the friend of* repeated `n` times before *everyone*, with the priorities `σ k` and `τ k` at
the NP and N nodes of the `k`-th repetition. -/
def theFriendOfEveryone (σ τ : ℕ → Equiv.Perm (Fin 2)) : ℕ → Deriv String E
  | 0 => everyone
  | n + 1 => NP (σ n) (lex the) (N (τ n) (lex friendOf) (PPof (theFriendOfEveryone σ τ n)))

theorem continuize_theFriendOfEveryone (σ τ : ℕ → Equiv.Perm (Fin 2)) (n : ℕ) :
    (theFriendOfEveryone friendOf the σ τ n).continuize =
      (fun y ↦ (fun z ↦ the (friendOf z))^[n] y) <$> everyone.continuize := by
  induction n with
  | zero => exact (id_map _).symm
  | succ n ih =>
    rw [theFriendOfEveryone, NP, continuize_binary_of_direct_left _ _ rfl, N,
      continuize_binary_of_direct_left _ _ rfl, PPof, continuize_unary, ih]
    simp only [Functor.map_map, Function.iterate_succ_apply']
    rfl

theorem someone_saw_theFriendOfEveryone_surface (σ τ : ℕ → Equiv.Perm (Fin 2))
    (υ : Equiv.Perm (Fin 2)) (n : ℕ) :
    (S 1 someone (VP υ (lex saw') (theFriendOfEveryone friendOf the σ τ n))).eval =
      ∃ x, ∀ y, saw' ((fun z ↦ the (friendOf z))^[n] y) x := by
  rw [eval, S, continuize_binary_one, VP, continuize_binary_of_direct_left _ _ rfl,
    continuize_theFriendOfEveryone]
  rfl

theorem someone_saw_theFriendOfEveryone_inverse (σ τ : ℕ → Equiv.Perm (Fin 2))
    (υ : Equiv.Perm (Fin 2)) (n : ℕ) :
    (S (Equiv.swap 0 1) someone (VP υ (lex saw') (theFriendOfEveryone friendOf the σ τ n))).eval =
      ∀ y, ∃ x, saw' ((fun z ↦ the (friendOf z))^[n] y) x := by
  rw [eval, S, continuize_binary_swap, VP, continuize_binary_of_direct_left _ _ rfl,
    continuize_theFriendOfEveryone]
  rfl

/-! ### Choice-function determiners -/

theorem john_saw_det (w : String) (Q : Cont Prop (ChoiceFunction E)) (σ τ υ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NP υ (quant w Q) (lex man')))).eval =
      Q fun f ↦ saw' (f man') j := by
  rw [eval, S, continuize_binary_of_direct_left _ _ rfl, VP,
    continuize_binary_of_direct_left _ _ rfl, NP, continuize_binary_of_direct_right _ _ _ rfl]
  rfl

theorem john_saw_every_man_iff (hman : ∃ x, man' x) (σ τ υ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NP υ every (lex man')))).eval ↔
      Quantifier.GQ.every man' (saw' · j) :=
  (john_saw_det j man' saw' _ _ σ τ υ).to_iff.trans
    (ChoiceFunction.forall_apply_iff_every hman (saw' · j))

theorem john_saw_every_man_iff_of_not_exists (hman : ¬ ∃ x, man' x)
    (σ τ υ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NP υ every (lex man')))).eval ↔ ∀ x, saw' x j :=
  (john_saw_det j man' saw' _ _ σ τ υ).to_iff.trans
    (ChoiceFunction.forall_apply_iff_of_not_exists hman (saw' · j))

theorem john_saw_no_man_iff (hman : ∃ x, man' x) (σ τ υ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NP υ no (lex man')))).eval ↔
      Quantifier.GQ.no man' (saw' · j) :=
  (john_saw_det j man' saw' _ _ σ τ υ).to_iff.trans <|
    (ChoiceFunction.exists_apply_iff_some hman (saw' · j)).not.trans
      (by simp [Quantifier.GQ.no, Quantifier.GQ.some])

/-- The sets of choice functions that pick more than half of every property, at a nonempty
restrictor in a finite domain, give the proportional *most*. -/
theorem exists_forall_mem_apply_iff_most [Finite E] {N : E → Prop} (hN : ∃ x, N x) (V : E → Prop) :
    (∃ C : Set (ChoiceFunction E),
      (∀ P : E → Prop, {x | P x}.ncard < 2 * ((· P) '' C).ncard) ∧ ∀ f ∈ C, V (f N)) ↔
      Quantifier.GQ.most N V := by
  classical
  rw [Quantifier.GQ.most_apply]
  have hNV : {x | N x}.ncard = {x | N x ∧ V x}.ncard + {x | N x ∧ ¬ V x}.ncard := by
    rw [← Set.ncard_union_eq (Set.disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx.2)]
    congr 1; ext x; by_cases V x <;> simp [*]
  refine ⟨fun ⟨C, hC, hV⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hsub : (· N) '' C ⊆ {x | N x ∧ V x} := by
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f.apply_of_exists hN, hV f hf⟩
    have := Set.ncard_le_ncard hsub
    have := hC N
    omega
  obtain ⟨s, hs, hVs⟩ : ∃ s, N s ∧ V s := by
    by_contra hne
    have : {x | N x ∧ V x} = (∅ : Set E) := Set.eq_empty_of_forall_notMem fun x hx ↦ hne ⟨x, hx⟩
    rw [this, Set.ncard_empty] at h
    omega
  have : Nonempty E := ⟨s⟩
  let C : Set (ChoiceFunction E) := {f | V (f N)}
  refine ⟨C, fun P ↦ ?_, fun f hf ↦ hf⟩
  by_cases hP : P = N
  · subst hP
    have hC : (fun f : ChoiceFunction E ↦ f P) '' C = {x | P x ∧ V x} := by
      ext x
      refine ⟨?_, fun ⟨hx, hVx⟩ ↦ ?_⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f.apply_of_exists hN, hf⟩
      · obtain ⟨f, rfl⟩ := ChoiceFunction.exists_apply_eq hx
        exact ⟨f, hVx, rfl⟩
    rw [hC]
    omega
  have hsup : {x | P x} ⊆ (fun f : ChoiceFunction E ↦ f P) '' C := fun x hx ↦ by
    let f : ChoiceFunction E := ⟨fun Q ↦ if Q = P then x else if Q = N then s else
      ChoiceFunction.epsilon Q, fun Q hQ ↦ by
        split_ifs with h₁ h₂
        exacts [h₁ ▸ hx, h₂ ▸ hs, ChoiceFunction.epsilon.apply_of_exists hQ]⟩
    exact ⟨f, by simpa [C, f, Ne.symm hP] using hVs, by simp [f]⟩
  have hne : ((fun f : ChoiceFunction E ↦ f P) '' C).Nonempty := by
    obtain ⟨f, hf⟩ := ChoiceFunction.exists_apply_eq hs
    exact ⟨f P, f, by simpa [C, hf] using hVs, rfl⟩
  have := Set.ncard_le_ncard hsup
  have := (Set.ncard_pos (Set.toFinite _)).mpr hne
  omega

theorem john_saw_most_men_iff [Finite E] (hman : ∃ x, man' x) (σ τ υ : Equiv.Perm (Fin 2)) :
    (S σ (lex j) (VP τ (lex saw') (NP υ most (lex man')))).eval ↔
      Quantifier.GQ.most man' (saw' · j) :=
  (john_saw_det j man' saw' _ _ σ τ υ).to_iff.trans
    (exists_forall_mem_apply_iff_most hman (saw' · j))

/-! ### The scopings of *someone saw a friend of everyone* -/

/-- The derivation, with a priority at the S, VP, NP and N nodes. -/
def someoneSawAFriendOfEveryone (σS σVP σNP σN : Equiv.Perm (Fin 2)) : Deriv String Prop :=
  S σS someone (VP σVP (lex saw') (NP σNP a (N σN (lex friendOf) (PPof everyone))))

theorem ex43a (σVP σN : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf 1 σVP 1 σN).scopeOrder =
      ["someone", "a", "everyone"] ∧
    (someoneSawAFriendOfEveryone saw' friendOf 1 σVP 1 σN).eval =
      ∃ y, ∃ f : ChoiceFunction E, ∀ x, saw' (f (friendOf x)) y := by
  rcases perm_fin_two σVP with rfl | rfl <;> rcases perm_fin_two σN with rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem ex43b (σVP σN : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf 1 σVP (Equiv.swap 0 1) σN).scopeOrder =
      ["someone", "everyone", "a"] ∧
    (someoneSawAFriendOfEveryone saw' friendOf 1 σVP (Equiv.swap 0 1) σN).eval =
      ∃ y, ∀ x, ∃ f : ChoiceFunction E, saw' (f (friendOf x)) y := by
  rcases perm_fin_two σVP with rfl | rfl <;> rcases perm_fin_two σN with rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem ex43c (σVP σN : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf (Equiv.swap 0 1) σVP 1 σN).scopeOrder =
      ["a", "everyone", "someone"] ∧
    (someoneSawAFriendOfEveryone saw' friendOf (Equiv.swap 0 1) σVP 1 σN).eval =
      ∃ f : ChoiceFunction E, ∀ x, ∃ y, saw' (f (friendOf x)) y := by
  rcases perm_fin_two σVP with rfl | rfl <;> rcases perm_fin_two σN with rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem ex43d (σVP σN : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf (Equiv.swap 0 1) σVP (Equiv.swap 0 1)
      σN).scopeOrder = ["everyone", "a", "someone"] ∧
    (someoneSawAFriendOfEveryone saw' friendOf (Equiv.swap 0 1) σVP (Equiv.swap 0 1)
      σN).eval = ∀ x, ∃ f : ChoiceFunction E, ∃ y, saw' (f (friendOf x)) y := by
  rcases perm_fin_two σVP with rfl | rfl <;> rcases perm_fin_two σN with rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem constituent_object (σS σVP σNP σN : Equiv.Perm (Fin 2)) :
    Constituent (NP σNP a (N σN (lex friendOf) (PPof everyone)))
      (someoneSawAFriendOfEveryone saw' friendOf σS σVP σNP σN) :=
  .node _ _ _ 1 (.node _ _ _ 1 (.refl _))

theorem scopeOrder_object (σNP σN : Equiv.Perm (Fin 2)) :
    (NP σNP a (N σN (lex friendOf) (PPof everyone))).scopeOrder = ["a", "everyone"] ∨
      (NP σNP a (N σN (lex friendOf) (PPof everyone))).scopeOrder = ["everyone", "a"] := by
  rcases perm_fin_two σNP with rfl | rfl <;> rcases perm_fin_two σN with rfl | rfl <;>
    first | exact .inl rfl | exact .inr rfl

theorem no_split_scoping (σS σVP σNP σN : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf σS σVP σNP σN).scopeOrder ≠
        ["everyone", "someone", "a"] ∧
      (someoneSawAFriendOfEveryone saw' friendOf σS σVP σNP σN).scopeOrder ≠
        ["a", "someone", "everyone"] := by
  have h := (constituent_object saw' friendOf σS σVP σNP σN).scopeOrder_isInfix
  constructor <;> intro h' <;> rw [h'] at h <;>
    rcases scopeOrder_object friendOf σNP σN with ho | ho <;> rw [ho] at h <;>
    exact absurd h (by decide)

theorem a_everyone_iff_everyone_a [Nonempty E] (σS σVP σN σVP' σN' : Equiv.Perm (Fin 2)) :
    (someoneSawAFriendOfEveryone saw' friendOf σS σVP 1 σN).eval ↔
      (someoneSawAFriendOfEveryone saw' friendOf σS σVP' (Equiv.swap 0 1) σN').eval := by
  rcases perm_fin_two σS with rfl | rfl
  · rw [(ex43a saw' friendOf σVP σN).2, (ex43b saw' friendOf σVP' σN').2]
    exact exists_congr fun y ↦ ChoiceFunction.exists_forall_apply_iff friendOf (saw' · y)
  · rw [(ex43c saw' friendOf σVP σN).2, (ex43d saw' friendOf σVP' σN').2]
    exact ChoiceFunction.exists_forall_apply_iff friendOf fun z ↦ ∃ y, saw' z y

/-! ### Generalized coordination -/

theorem coord_VP_subject_priority (np : Deriv ι E) (P Q : E → Prop) :
    (S 1 np (coord (lex P) (lex Q))).eval = (S 1 np (lex (P ⊓ Q))).eval :=
  rfl

theorem coord_VP_priority (np : Deriv ι E) (P Q : E → Prop) :
    (S (Equiv.swap 0 1) np (coord (lex P) (lex Q))).eval =
      ((S (Equiv.swap 0 1) np (lex P)).eval ∧ (S (Equiv.swap 0 1) np (lex Q)).eval) :=
  rfl

theorem john_and_mary_left (σ : Equiv.Perm (Fin 2)) :
    (S σ (coord (lex j) (lex m)) (lex left' : Deriv ι _)).eval = (left' j ∧ left' m) := by
  rcases perm_fin_two σ with rfl | rfl <;> rfl

/-! ### The paper's examples -/

/-- The words of a string, split at a separator. -/
def wordsOn (c : Char) (s : String) : List String :=
  (s.toList.splitOn c).filterMap fun cs ↦
    let w := cs.filter (· ≠ ' ')
    if w = [] then none else some (String.ofList w)

theorem rows_scopings : ∀ e ∈ Examples.all,
    e.feature? "derivation" = some "someone saw a friend of everyone" → ∀ r ∈ e.readings,
      (r.2 = .acceptable ↔ ∃ σS σVP σNP σN : Equiv.Perm (Fin 2),
        (someoneSawAFriendOfEveryone (E := Unit) (fun _ _ ↦ True) (fun _ _ ↦ True)
          σS σVP σNP σN).scopeOrder = wordsOn '>' r.1) := by
  decide +kernel

theorem rows_scopings_theFriendOfEveryone : ∀ e ∈ Examples.all,
    e.feature? "derivation" = some "someone saw the friend of the friend of everyone" →
    ∀ r ∈ e.readings, (r.2 = .acceptable ↔ ∃ σS υ σ τ : Equiv.Perm (Fin 2),
      (S σS someone (VP υ (lex fun _ _ ↦ True) (theFriendOfEveryone (E := Unit)
        (fun _ _ ↦ True) ChoiceFunction.epsilon (fun _ ↦ σ) (fun _ ↦ τ) 2))).scopeOrder =
        wordsOn '>' r.1) := by
  decide +kernel

theorem rows_integrity : ∀ e ∈ Examples.all, ∀ c ∈ e.feature? "constituent",
    ∀ r ∈ e.readings, (r.2 = .acceptable ↔
      (wordsOn '>' r.1).filter (· ∈ wordsOn ' ' c) <:+: wordsOn '>' r.1) := by
  decide +kernel

end Barker2002
