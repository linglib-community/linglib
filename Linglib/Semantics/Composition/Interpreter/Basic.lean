module

public import Linglib.Core.ModelTheory.ManySorted.Simulation
public import Mathlib.Data.Nat.Notation

/-!
# Type-driven interpreters

A type-driven grammar says how the meanings of constituents combine, knowing only their types: it
has binary rules, the modes of combination, and unary rules, the type shifts. It is a many-sorted
language whose symbols take one argument or a pair, a derivation is a term of that language over
typed lexical items, and a structure for it gives each derivation a value.

A derivation is all the semantics is given, and nothing is assumed of where it comes from: a
syntactic theory says which derivations its objects have. One way is type-driven: an interpreter
reads a bare structure, the words in their constituency and order with a label at each node, and
says which rules a node admits by its label and the types of its daughters, so that the
derivations over a bare structure are found from the types alone.

## Main definitions

* `Interpreter.Grammar`: the unary and binary rules over a type of semantic types.
* `Interpreter.Grammar.language`, `Interpreter.Grammar.structure`: the many-sorted language of a
  grammar, and the structure that operations for its rules make.
* `Interpreter.Grammar.sum`: two grammars together, with the structure a structure for each makes.
* `Interpreter.Grammar.LocallyFinite`, `Interpreter.typeDriven`: a grammar whose rules for given
  daughters can be listed, and the interpreter that admits every rule that applies.
* `Interpreter.Grammar.motherTypes`: the types the rules give the mother of two daughters.
* `Interpreter.Grammar.Deriv`: the derivations of a type over typed lexical items.
* `Interpreter.Grammar.Skeleton`, `Interpreter.Node`: a bare structure, and the labels a
  constituency tree gives its nodes.
* `Interpreter`: the rules a node admits by its label and its daughters' types.
* `Interpreter.derivs`, `Interpreter.values`: the derivations over a bare structure, and their
  values.

## Implementation notes

`Interpreter.derivs` matches on the derivations of the daughters and does not project from them:
a projection is unfolded again wherever it is inspected, which made checking a sentence's value
some fifty times dearer. A lexicon gives each word typed items and their values separately. With
the values inside the items, as `Interpreter.meanings` has them, a statement over a model with
variables in it is still slow to check, and `Interpreter.values` is the form to use there.

## References

* [bumford-charlow-2026]
* [klein-sag-1985]
* [montague-1970]
-/

@[expose] public section

universe u v w x

open MSFirstOrder

namespace Interpreter

/-- A type-driven grammar over semantic types `T`: its type shifts and its modes of combination,
each typed by what it takes and what it yields. -/
structure Grammar (T : Type u) where
  /-- The unary rules from one type to another. -/
  Unary : T → T → Type v
  /-- The binary rules combining a left and a right daughter into a mother. -/
  Binary : T → T → T → Type v

namespace Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {W : T → Type w} {D : T → Type x}

/-- The symbols of a grammar: a unary rule takes one argument and a binary rule a pair. -/
inductive Sym (G : Grammar.{u, v} T) : Signature T → T → Type (max u v)
  /-- A unary rule. -/
  | unary {a b : T} (s : G.Unary a b) : Sym G (.of a) b
  /-- A binary rule. -/
  | binary {a b c : T} (m : G.Binary a b c) : Sym G (.prod (.of a) (.of b)) c

/-- The many-sorted language of a grammar. -/
@[reducible] def language (G : Grammar.{u, v} T) : Language.{u, max u v} T := ⟨G.Sym⟩

/-- The structure for a grammar's language that operations for its rules make. -/
@[instance_reducible] def «structure» (unary : ∀ {a b : T}, G.Unary a b → D a → D b)
    (binary : ∀ {a b c : T}, G.Binary a b c → D a → D b → D c) : G.language.Structure D where
  funMap
    | .unary s, x => unary s x
    | .binary m, (x, y) => binary m x y

@[simp] theorem structure_funMap_unary (unary : ∀ {a b : T}, G.Unary a b → D a → D b)
    (binary : ∀ {a b c : T}, G.Binary a b c → D a → D b → D c) {a b : T} (s : G.Unary a b)
    (x : D a) : (Grammar.structure unary binary).funMap (.unary s) x = unary s x := rfl

@[simp] theorem structure_funMap_binary (unary : ∀ {a b : T}, G.Unary a b → D a → D b)
    (binary : ∀ {a b c : T}, G.Binary a b c → D a → D b → D c) {a b c : T} (m : G.Binary a b c)
    (p : D a × D b) : (Grammar.structure unary binary).funMap (.binary m) p = binary m p.1 p.2 :=
  rfl

/-- The rules of two grammars together. -/
@[reducible] def sum (G H : Grammar.{u, v} T) : Grammar.{u, v} T where
  Unary a b := G.Unary a b ⊕ H.Unary a b
  Binary a b c := G.Binary a b c ⊕ H.Binary a b c

/-- The structure for two grammars together that a structure for each makes. -/
instance sumStructure {H : Grammar.{u, v} T} [M : G.language.Structure D]
    [M' : H.language.Structure D] : (G.sum H).language.Structure D where
  funMap
    | .unary (.inl s), x => M.funMap (.unary s) x
    | .unary (.inr s), x => M'.funMap (.unary s) x
    | .binary (.inl m), p => M.funMap (.binary m) p
    | .binary (.inr m), p => M'.funMap (.binary m) p

/-- A grammar is locally finite when the rules that apply to given daughters can be listed. -/
class LocallyFinite (G : Grammar.{u, v} T) where
  /-- The unary rules that apply to a daughter of type `a`. -/
  unaryRules : (a : T) → List (Σ b, G.Unary a b)
  /-- The binary rules that apply to daughters of types `l` and `r`. -/
  binaryRules : (l r : T) → List (Σ u, G.Binary l r u)
  /-- Every unary rule is listed. -/
  mem_unaryRules {a b : T} (s : G.Unary a b) : ⟨b, s⟩ ∈ unaryRules a
  /-- Every binary rule is listed. -/
  mem_binaryRules {l r u : T} (m : G.Binary l r u) : ⟨u, m⟩ ∈ binaryRules l r

/-- The types of the mothers that the rules of a grammar give two daughters. -/
def motherTypes (G : Grammar.{u, v} T) [G.LocallyFinite] (l r : T) : List T :=
  (LocallyFinite.binaryRules (G := G) l r).map (·.1)

instance {H : Grammar.{u, v} T} [G.LocallyFinite] [H.LocallyFinite] : (G.sum H).LocallyFinite where
  unaryRules a := (LocallyFinite.unaryRules a).map (fun ⟨b, s⟩ ↦ ⟨b, .inl s⟩) ++
    (LocallyFinite.unaryRules a).map fun ⟨b, s⟩ ↦ ⟨b, .inr s⟩
  binaryRules l r := (LocallyFinite.binaryRules l r).map (fun ⟨u, m⟩ ↦ ⟨u, .inl m⟩) ++
    (LocallyFinite.binaryRules l r).map fun ⟨u, m⟩ ↦ ⟨u, .inr m⟩
  mem_unaryRules
    | .inl s => List.mem_append_left _
      (List.mem_map.2 ⟨_, LocallyFinite.mem_unaryRules s, rfl⟩)
    | .inr s => List.mem_append_right _
      (List.mem_map.2 ⟨_, LocallyFinite.mem_unaryRules s, rfl⟩)
  mem_binaryRules
    | .inl m => List.mem_append_left _
      (List.mem_map.2 ⟨_, LocallyFinite.mem_binaryRules m, rfl⟩)
    | .inr m => List.mem_append_right _
      (List.mem_map.2 ⟨_, LocallyFinite.mem_binaryRules m, rfl⟩)

/-- A derivation of a type from lexical items of the types `W` supplies. -/
abbrev Deriv (G : Grammar.{u, v} T) (W : T → Type w) (a : T) : Type (max u v w) :=
  G.language.Term W (.of a)

namespace Deriv

/-- A lexical item. -/
abbrev leaf {a : T} (x : W a) : Deriv G W a := .var x

/-- A unary rule applied to a derivation. -/
abbrev unary {a b : T} (s : G.Unary a b) (d : Deriv G W a) : Deriv G W b :=
  .func (L := G.language) (Sym.unary s) d

/-- A binary rule applied to two derivations. -/
abbrev binary {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a) (d₂ : Deriv G W b) :
    Deriv G W c :=
  .func (L := G.language) (Sym.binary m) (.prod d₁ d₂)

variable (M : G.language.Structure D) (ρ : ∀ {a : T}, W a → D a)

@[simp] theorem realize_leaf {a : T} (x : W a) : (leaf x : Deriv G W a).realize M ρ = ρ x := rfl

@[simp] theorem realize_unary {a b : T} (s : G.Unary a b) (d : Deriv G W a) :
    (unary s d).realize M ρ = M.funMap (.unary s) (d.realize M ρ) := rfl

@[simp] theorem realize_binary {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a)
    (d₂ : Deriv G W b) :
    (binary m d₁ d₂).realize M ρ = M.funMap (.binary m) (d₁.realize M ρ, d₂.realize M ρ) := rfl

end Deriv

/-- Induction on derivations: a property of every lexical item that the unary and the binary
rules preserve holds of every derivation. -/
theorem Deriv.induction {P : ∀ {a : T}, Deriv G W a → Prop}
    (leaf : ∀ {a : T} (x : W a), P (Deriv.leaf x))
    (unary : ∀ {a b : T} (s : G.Unary a b) (d : Deriv G W a), P d → P (Deriv.unary s d))
    (binary : ∀ {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a) (d₂ : Deriv G W b),
      P d₁ → P d₂ → P (Deriv.binary m d₁ d₂)) {a : T} (d : Deriv G W a) : P d := by
  have key : ∀ {σ : Signature T} (t : G.language.Term W σ),
      (∀ a (h : σ = .of a), P (h ▸ t)) ∧
        ∀ a b (h : σ = .prod (.of a) (.of b)),
          ∃ d₁ d₂, h ▸ t = Language.Term.prod d₁ d₂ ∧ P d₁ ∧ P d₂ := by
    intro σ t
    induction t with
    | var x => exact ⟨fun _ h ↦ by cases h; exact leaf x, fun _ _ h ↦ nomatch h⟩
    | func f r ih =>
      refine ⟨fun _ h ↦ ?_, fun _ _ h ↦ nomatch h⟩
      cases h
      cases f with
      | unary s => exact unary s r (ih.1 _ rfl)
      | binary m =>
        obtain ⟨d₁, d₂, rfl, h₁, h₂⟩ := ih.2 _ _ rfl
        exact binary m d₁ d₂ h₁ h₂
    | prod t₁ t₂ ih₁ ih₂ =>
      refine ⟨(fun _ h ↦ nomatch h), fun _ _ h ↦ ?_⟩
      cases h
      exact ⟨t₁, t₂, rfl, ih₁.1 _ rfl, ih₂.1 _ rfl⟩
    | nil => exact ⟨(fun _ h ↦ nomatch h), fun _ _ h ↦ nomatch h⟩
  exact (key d).1 a rfl

/-- A bare structure over node labels `N` and leaves `L`: what a type-driven interpreter asks of
the syntax. -/
inductive Skeleton (N : Type v) (L : Type w) : Type (max v w)
  /-- A leaf. -/
  | leaf (x : L) : Skeleton N L
  /-- A unary node. -/
  | unary (n : N) (s : Skeleton N L) : Skeleton N L
  /-- A binary node. -/
  | binary (n : N) (s₁ s₂ : Skeleton N L) : Skeleton N L

end Grammar

/-- What the semantics reads off a node of the syntax: a plain branching node, an island, or the
index a moved phrase leaves. -/
inductive Node where
  /-- A plain node. -/
  | branch
  /-- An island for continuations. -/
  | island
  /-- The index `n` of a moved phrase. -/
  | index (n : ℕ)
  deriving DecidableEq, Repr

end Interpreter

/-- A type-driven interpreter for a grammar: the rules a node admits, by its label and the types
of its daughters. -/
structure Interpreter {T : Type u} (G : Interpreter.Grammar.{u, v} T) (N : Type v) where
  /-- The unary rules a node labelled `n` over a daughter of type `a` admits. -/
  unary : N → (a : T) → List (Σ b, G.Unary a b)
  /-- The binary rules a node labelled `n` over daughters of types `l` and `r` admits. -/
  binary : N → (l r : T) → List (Σ u, G.Binary l r u)

namespace Interpreter

open Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {N : Type v} {L : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The type-driven interpreter of a grammar: a node admits every rule that applies to the
types of its daughters, whatever its label. -/
def typeDriven (G : Grammar.{u, v} T) [G.LocallyFinite] : Interpreter G N where
  unary _ := LocallyFinite.unaryRules
  binary _ := LocallyFinite.binaryRules

/-- The derivations over a bare structure that an interpreter admits, given the typed items each
word may be. -/
def derivs (I : Interpreter G N) (lex : L → List (Σ a, W a)) :
    Skeleton N L → List (Σ a, Deriv G W a)
  | .leaf x => (lex x).map fun ⟨a, w⟩ ↦ ⟨a, .leaf w⟩
  | .unary n s => (I.derivs lex s).flatMap fun ⟨a, d⟩ ↦
      (I.unary n a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩
  | .binary n s₁ s₂ => (I.derivs lex s₁).flatMap fun ⟨a, d₁⟩ ↦
      (I.derivs lex s₂).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary n a b).map fun ⟨c, m⟩ ↦ ⟨c, .binary m d₁ d₂⟩

/-- Where a node admits at most one rule for given daughters and a word is at most one item, a
bare structure has at most one derivation. -/
theorem length_derivs_le_one {I : Interpreter G N} {lex : L → List (Σ a, W a)}
    (hu : ∀ n a, (I.unary n a).length ≤ 1) (hb : ∀ n l r, (I.binary n l r).length ≤ 1)
    (hl : ∀ x, (lex x).length ≤ 1) : ∀ s : Skeleton N L, (I.derivs lex s).length ≤ 1
  | .leaf x => by simpa [derivs] using hl x
  | .unary n s => by
    have ih := length_derivs_le_one hu hb hl s
    match h : I.derivs lex s, ih with
    | [], _ => simp [derivs, h]
    | [⟨a, d⟩], _ => simpa [derivs, h] using hu n a
  | .binary n s₁ s₂ => by
    have ih₁ := length_derivs_le_one hu hb hl s₁
    have ih₂ := length_derivs_le_one hu hb hl s₂
    match h₁ : I.derivs lex s₁, h₂ : I.derivs lex s₂, ih₁, ih₂ with
    | [], _, _, _ => simp [derivs, h₁]
    | [_], [], _, _ => simp [derivs, h₁, h₂]
    | [⟨a, d₁⟩], [⟨b, d₂⟩], _, _ => simpa [derivs, h₁, h₂] using hb n a b

/-- The values of the derivations over a bare structure, for a lexicon of typed items whose
values `ρ` gives. The derivations are found from the types alone. -/
def values (I : Interpreter G N) [M : G.language.Structure D] (ρ : ∀ {a : T}, W a → D a)
    (lex : L → List (Σ a, W a)) (s : Skeleton N L) : List (Σ a, D a) :=
  (I.derivs lex s).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

/-- A value of a binary node is the value of a rule the node admits, at values of its
daughters. -/
theorem mem_values_binary {I : Interpreter G N} [M : G.language.Structure D]
    {ρ : ∀ {a : T}, W a → D a} {lex : L → List (Σ a, W a)} {n : N} {s₁ s₂ : Skeleton N L}
    {d : Σ a, D a} :
    d ∈ I.values ρ lex (.binary n s₁ s₂) ↔ ∃ d₁ ∈ I.values ρ lex s₁, ∃ d₂ ∈ I.values ρ lex s₂,
      ∃ m ∈ I.binary n d₁.1 d₂.1, d = ⟨m.1, M.funMap (.binary m.2) (d₁.2, d₂.2)⟩ := by
  simp only [values, derivs, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨_, ⟨⟨a, e₁⟩, h₁, ⟨b, e₂⟩, h₂, ⟨u, m⟩, hm, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨a, e₁⟩, h₁, rfl⟩, _, ⟨⟨b, e₂⟩, h₂, rfl⟩, ⟨u, m⟩, hm, rfl⟩
  · rintro ⟨_, ⟨⟨a, e₁⟩, h₁, rfl⟩, _, ⟨⟨b, e₂⟩, h₂, rfl⟩, ⟨u, m⟩, hm, rfl⟩
    exact ⟨_, ⟨⟨a, e₁⟩, h₁, ⟨b, e₂⟩, h₂, ⟨u, m⟩, hm, rfl⟩, rfl⟩

/-- The meanings of a bare structure, for a lexicon whose items are their values. -/
def meanings {D : T → Type w} (I : Interpreter G N) [G.language.Structure D]
    (lex : L → List (Σ a, D a)) : Skeleton N L → List (Σ a, D a) :=
  I.values id lex

end Interpreter
