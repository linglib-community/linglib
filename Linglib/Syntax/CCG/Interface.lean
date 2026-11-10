module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Semantics.Composition.Interpreter.Effect
public import Linglib.Semantics.Composition.Interpreter.Basic

/-!
# The CCG syntax-semantics interface

A typing of the atoms extends to every category, sending `X/Y` and `X\Y` to the function type
from the type of `Y` to that of `X` and ignoring slash modalities, which control combinatory
potential rather than meaning. Since a `Derivation` is indexed by its category, its
interpretation needs no run-time category checks: a rule instance `X/Y Yβ ⇒ Xβ` composes its
daughters' meanings beneath the arguments `β`, Curry's combinator `Bⁿ` for `n` the length of `β`,
so application is function application and first-order composition is Steedman's `B`.
A lexical entry pairs a word and a category with a logical form, a function of what the constants
of a signature denote, so the lexicon is the same in every model. Type-raising and coordination
are lexical, so their logical forms (the Montague lift, generalized conjunction) are entries'
logical forms. The combinatory rules are the binary rules of a grammar over categories, and a
derivation's meaning is its value as a derivation of that grammar; a derivation over the lexicon
always has one.

## Main definitions

* `CCG.Cat.toTy`: the semantic type of a category under a typing of its atoms.
* `CCG.LexEntry`: a lexical entry, a word with a category and a logical form.
* `CCG.composeUnder`: composition beneath an argument sequence, Curry's `Bⁿ`.
* `CCG.grammar`: the combinatory rules of a rule system as a grammar over categories.
* `CCG.Derivation.interp`: the meaning of a derivation in an interpretation of the constants.

## Main statements

* `CCG.Derivation.isSome_interp`: a derivation over the lexicon has a meaning.
* `CCG.Derivation.interp_fcomp_assoc`, `CCG.Derivation.interp_fapp_fcomp` and their backward
  mirrors: in every rule system, reassociating a composition-application chain does not change
  its interpretation, the source of CCG's spurious ambiguity.

## TODO

* That the combinatory rules are derivable, composition and type raising being theorems of the
  Lambek calculus, belongs to the syntax of the calculus and is not stated here: the grammar
  takes the rules of a rule system as given.

## References

* [steedman-2000]
* [steedman-2019]
* [montague-1973]
* [karttunen-1989]
* [pareschi-steedman-1987]
-/

@[expose] public section

namespace CCG

open Interpreter ManySorted ManySorted.Language

variable {T α : Type*} {B : Type}

/-! ### Type correspondence -/

/-- `c.toTy τ` is the semantic type of the category `c` when each atom `a` has type `τ a`. -/
def Cat.toTy (τ : α → Ty B) : Cat α → Ty B
  | .atom a => τ a
  | .rslash x _ y => y.toTy τ ⇒ x.toTy τ
  | .lslash x _ y => y.toTy τ ⇒ x.toTy τ

@[simp] theorem Cat.toTy_forwardTypeRaise (τ : α → Ty B) (x t : Cat α) :
    (x.forwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

@[simp] theorem Cat.toTy_backwardTypeRaise (τ : α → Ty B) (x t : Cat α) :
    (x.backwardTypeRaise t).toTy τ = ((x.toTy τ ⇒ t.toTy τ) ⇒ t.toTy τ) := rfl

/-! ### Derivation interpretation -/

variable (T) in
/-- A lexical entry pairs a word with a category and a logical form, as [steedman-2000] writes an
entry `word := category : logical form`. The logical form is a function of what the constants `K`
denote, at whatever domains, so it is the same in every model. -/
structure LexEntry (τ : α → Ty B) (K : Ty B → Type*) where
  /-- The word. -/
  word : T
  /-- The category of the word. -/
  cat : Cat α
  /-- The logical form of the word at its category. -/
  lf : ∀ {D : B → Type}, (∀ {ty : Ty B}, K ty → ty.Dom D) → (cat.toTy τ).Dom D

namespace LexEntry

variable {τ : α → Ty B} {K : Ty B → Type*}

/-- The word and category of an entry, the pair a syntactic lexicon lists. -/
def toPair (e : LexEntry T τ K) : T × Cat α := (e.word, e.cat)

variable [DecidableEq T] [DecidableEq α] {D : B → Type}

/-- The value, when the constants denote by `I`, of the logical form of the first entry of `L`
for the word `t` at the category `c`. -/
def lookup (L : List (LexEntry T τ K)) (I : ∀ {ty : Ty B}, K ty → ty.Dom D) (t : T)
    (c : Cat α) : Option ((c.toTy τ).Dom D) :=
  L.findSome? fun e ↦ if h : e.word = t ∧ e.cat = c then some (h.2 ▸ e.lf I) else none

theorem isSome_lookup {L : List (LexEntry T τ K)} {I : ∀ {ty : Ty B}, K ty → ty.Dom D} {t : T}
    {c : Cat α} (h : (t, c) ∈ L.map toPair) : (lookup L I t c).isSome := by
  obtain ⟨e, he, hp⟩ := List.mem_map.1 h
  simp only [toPair, Prod.mk.injEq] at hp
  exact List.findSome?_isSome_iff.2 ⟨e, he, by simp [hp]⟩

end LexEntry

/-- `composeUnder τ β f g` composes `f` with `g` beneath the arguments `β`, Curry's combinator
`Bⁿ` for `n` the length of `β`: it takes the arguments of `g`, outermost first, and applies `f`
to the result. -/
def composeUnder (τ : α → Ty B) {D : B → Type} : (β : List (Cat.Arg α)) → {x y : Cat α} →
    (y.toTy τ ⇒ x.toTy τ).Dom D → ((y.pushArgs β).toTy τ).Dom D →
      ((x.pushArgs β).toTy τ).Dom D
  | [], _, _, f, g => f g
  | ⟨.right, m, z⟩ :: β, x, y, f, g =>
      composeUnder τ β (x := .rslash x m z) (y := .rslash y m z) (f ∘ ·) g
  | ⟨.left, m, z⟩ :: β, x, y, f, g =>
      composeUnder τ β (x := .lslash x m z) (y := .lslash y m z) (f ∘ ·) g

/-- `r.sem τ` is the meaning of the rule `r` as an operation on its daughters' meanings, the
primary composed with the secondary beneath the arguments the rule passes on. -/
def Rule.sem (τ : α → Ty B) {D : B → Type} {R : RuleSystem α} : {l r c : Cat α} → Rule R l r c →
    (l.toTy τ).Dom D → (r.toTy τ).Dom D → (c.toTy τ).Dom D
  | _, _, _, .forward β _, f, g => composeUnder τ β f g
  | _, _, _, .backward β _, g, f => composeUnder τ β f g

/-- The combinatory rules of a rule system as the binary rules of a grammar over categories, so
that a derivation is a derivation of that grammar. -/
@[reducible] def grammar (R : RuleSystem α) : ManySorted.Language (Cat α) :=
  .mk₂ (fun _ _ ↦ PEmpty) (Rule R)

/-- A category's values are the meanings of its type, or none where a word has no entry; a rule
combines the meanings of its daughters by `Rule.sem`. -/
instance (R : RuleSystem α) (τ : α → Ty B) (D : B → Type) :
    (grammar R).Structure fun c ↦ Option ((c.toTy τ).Dom D) :=
  .mk₂ nofun fun r a b ↦ do some (r.sem τ (← a) (← b))

/-- A derivation as a derivation of the grammar of its rule system, over its words. -/
def Derivation.toDeriv {R : RuleSystem α} : {c : Cat α} → Derivation T R c →
    Deriv (grammar R) (fun _ ↦ T) c
  | _, .lex t _ => .leaf t
  | _, .node r d₁ d₂ => .binary r d₁.toDeriv d₂.toDeriv

section Interp

variable [DecidableEq T] [DecidableEq α] {R : RuleSystem α} {τ : α → Ty B} {K : Ty B → Type*}
  {D : B → Type} (L : List (LexEntry T τ K)) (I : ∀ {ty : Ty B}, K ty → ty.Dom D)

/-- `d.interp L I` is the meaning of the derivation `d` over the lexicon `L` when the constants
denote by `I`: the value of `d` as a derivation of the grammar of its rules, a leaf denoting the
value of its logical form. -/
def Derivation.interp {c : Cat α} (d : Derivation T R c) : Option ((c.toTy τ).Dom D) :=
  d.toDeriv.realize (inferInstance : (grammar R).Structure fun c ↦
    Option ((c.toTy τ).Dom D)) fun {c} t ↦ LexEntry.lookup L I t c

@[simp] theorem Derivation.interp_lex (t : T) (c : Cat α) :
    (Derivation.lex t c : Derivation T R c).interp L I = LexEntry.lookup L I t c := rfl

@[simp] theorem Derivation.interp_node {l r c : Cat α} (ru : Rule R l r c) (d₁ : Derivation T R l)
    (d₂ : Derivation T R r) : (Derivation.node ru d₁ d₂).interp L I =
      (do some (ru.sem τ (← d₁.interp L I) (← d₂.interp L I))) := rfl

/-- A derivation whose leaves are entries of the lexicon has a meaning. -/
theorem Derivation.isSome_interp {c : Cat α} (d : Derivation T R c)
    (h : d.LexIn (L.map LexEntry.toPair)) : (d.interp L I).isSome := by
  induction d with
  | lex t c => simpa using LexEntry.isSome_lookup h
  | node ru d₁ d₂ ih₁ ih₂ =>
    obtain ⟨m₁, hm₁⟩ := Option.isSome_iff_exists.1 (ih₁ h.1)
    obtain ⟨m₂, hm₂⟩ := Option.isSome_iff_exists.1 (ih₂ h.2)
    simp [hm₁, hm₂]

end Interp

/-! ### Spurious ambiguity

Composition is associative, so left- and right-branching derivations of the same
composition-application chain receive the same interpretation, whatever the lexicon. This is
the local source of CCG's spurious ambiguity ([steedman-2000]). A chart parser may keep one
derivation per equivalence class, since reassociating `fcomp`/`fapp` (or `bcomp`/`bapp`)
nodes cannot change what a constituent means, and the matching-entry tests of
[karttunen-1989] and [pareschi-steedman-1987] exploit exactly this invariance. -/

section SpuriousAmbiguity

variable [DecidableEq T] [DecidableEq α] {R : RuleSystem α} {τ : α → Ty B} {K : Ty B → Type*}
  {D : B → Type} (L : List (LexEntry T τ K)) (I : ∀ {ty : Ty B}, K ty → ty.Dom D)

/-- Reassociating a forward-composition chain preserves its interpretation, since composition
is associative. -/
theorem Derivation.interp_fcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.rslash y n z))
    (d₃ : Derivation T R (.rslash z p w)) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ [⟨.right, p, w⟩]) (h₃ : R y ⟨.right, n, z⟩ [⟨.right, p, w⟩])
    (h₄ : R x ⟨.right, m, y⟩ [⟨.right, p, w⟩]) :
    (Derivation.fcomp (.fcomp d₁ d₂ h₁) d₃ h₂).interp L I
      = (Derivation.fcomp d₁ (.fcomp d₂ d₃ h₃) h₄).interp L I := by
  simp only [Derivation.interp_node]
  rcases d₁.interp L I with _ | m₁ <;> rcases d₂.interp L I with _ | m₂ <;>
    rcases d₃.interp L I with _ | m₃ <;> rfl

/-- Composing and then applying has the interpretation of applying twice, since
`(f ∘ g) x = f (g x)`. -/
theorem Derivation.interp_fapp_fcomp {x y z : Cat α} {m n : Modality}
    (d₁ : Derivation T R (.rslash x m y)) (d₂ : Derivation T R (.rslash y n z))
    (d₃ : Derivation T R z) (h₁ : R x ⟨.right, m, y⟩ [⟨.right, n, z⟩])
    (h₂ : R x ⟨.right, n, z⟩ []) (h₃ : R y ⟨.right, n, z⟩ []) (h₄ : R x ⟨.right, m, y⟩ []) :
    (Derivation.fapp (.fcomp d₁ d₂ h₁) d₃ h₂).interp L I
      = (Derivation.fapp d₁ (.fapp d₂ d₃ h₃) h₄).interp L I := by
  simp only [Derivation.interp_node]
  rcases d₁.interp L I with _ | m₁ <;> rcases d₂.interp L I with _ | m₂ <;>
    rcases d₃.interp L I with _ | m₃ <;> rfl

theorem Derivation.interp_bcomp_assoc {x y z w : Cat α} {m n p : Modality}
    (d₁ : Derivation T R (.lslash y p z)) (d₂ : Derivation T R (.lslash x n y))
    (d₃ : Derivation T R (.lslash w m x)) (h₁ : R x ⟨.left, n, y⟩ [⟨.left, p, z⟩])
    (h₂ : R w ⟨.left, m, x⟩ [⟨.left, p, z⟩]) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ [⟨.left, p, z⟩]) :
    (Derivation.bcomp (.bcomp d₁ d₂ h₁) d₃ h₂).interp L I
      = (Derivation.bcomp d₁ (.bcomp d₂ d₃ h₃) h₄).interp L I := by
  simp only [Derivation.interp_node]
  rcases d₁.interp L I with _ | m₁ <;> rcases d₂.interp L I with _ | m₂ <;>
    rcases d₃.interp L I with _ | m₃ <;> rfl

theorem Derivation.interp_bapp_bcomp {x y w : Cat α} {m n : Modality}
    (d₁ : Derivation T R y) (d₂ : Derivation T R (.lslash x n y))
    (d₃ : Derivation T R (.lslash w m x)) (h₁ : R x ⟨.left, n, y⟩ [])
    (h₂ : R w ⟨.left, m, x⟩ []) (h₃ : R w ⟨.left, m, x⟩ [⟨.left, n, y⟩])
    (h₄ : R w ⟨.left, n, y⟩ []) :
    (Derivation.bapp (.bapp d₁ d₂ h₁) d₃ h₂).interp L I
      = (Derivation.bapp d₁ (.bcomp d₂ d₃ h₃) h₄).interp L I := by
  simp only [Derivation.interp_node]
  rcases d₁.interp L I with _ | m₁ <;> rcases d₂.interp L I with _ | m₂ <;>
    rcases d₃.interp L I with _ | m₃ <;> rfl

end SpuriousAmbiguity

end CCG
