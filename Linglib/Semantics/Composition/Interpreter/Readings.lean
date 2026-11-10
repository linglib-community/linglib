module

public import Linglib.Semantics.Composition.Interpreter.Constituency
public import Mathlib.Data.Set.Image

/-!
# Readings over a lexicon of sets

A word may have infinitely many items, as a coordinator has one at every conjoinable type. The
readings of a structure are then a set: the values of the rules its nodes admit at readings of
their daughters. Where each word has finitely many items they are [the values of the
derivations](##Interpreter.mem_readings_iff_mem_values).

## References

* [partee-rooth-1983]
-/

@[expose] public section

universe u v w x

namespace Interpreter

open Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {N : Type v} {L : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The values of a bare structure when a leaf may be any of a set of items. -/
def readings (I : Interpreter G N) [M : G.language.Structure D] (ρ : ∀ {a : T}, W a → D a)
    (lex : L → Set (Σ a, W a)) : Skeleton N L → Set (Σ a, D a)
  | .leaf x => (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex x
  | .unary n s => {d | ∃ d₁ ∈ I.readings ρ lex s, ∃ r ∈ I.unary n d₁.1,
      d = ⟨r.1, M.funMap (.unary r.2) d₁.2⟩}
  | .binary n s₁ s₂ => {d | ∃ d₁ ∈ I.readings ρ lex s₁, ∃ d₂ ∈ I.readings ρ lex s₂,
      ∃ m ∈ I.binary n d₁.1 d₂.1, d = ⟨m.1, M.funMap (.binary m.2) (d₁.2, d₂.2)⟩}

/-- Where each leaf has finitely many items, the readings are the values. -/
theorem mem_readings_iff_mem_values {I : Interpreter G N} [M : G.language.Structure D]
    {ρ : ∀ {a : T}, W a → D a} {lex : L → List (Σ a, W a)} {d : Σ a, D a} :
    ∀ {s : Skeleton N L}, d ∈ I.readings ρ (fun x ↦ {p | p ∈ lex x}) s ↔ d ∈ I.values ρ lex s
  | .leaf x => by simp [readings, values, derivs, eq_comm]
  | .unary n s => by
    simp only [readings, Set.mem_ofPred_eq, mem_readings_iff_mem_values (s := s)]
    simp only [values, derivs, List.mem_map, List.mem_flatMap]
    constructor
    · rintro ⟨_, ⟨⟨a, e⟩, h, rfl⟩, ⟨b, r⟩, hr, rfl⟩
      exact ⟨_, ⟨⟨a, e⟩, h, ⟨b, r⟩, hr, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, e⟩, h, ⟨b, r⟩, hr, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨a, e⟩, h, rfl⟩, ⟨b, r⟩, hr, rfl⟩
  | .binary n s₁ s₂ => by
    simp only [readings, Set.mem_ofPred_eq, mem_readings_iff_mem_values (s := s₁),
      mem_readings_iff_mem_values (s := s₂), mem_values_binary]

end Interpreter

namespace PhraseStructure.Tree

open Interpreter Interpreter.Grammar

variable {C L : Type} {T : Type} {G : Grammar T} {W D : T → Type}

/-- The values of a tree when a word or a trace may be any of a set of items. -/
def readings (I : Interpreter G Node) (M : G.language.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → Set (Σ a, W a)) (t : Tree C L) (island : C → Bool := fun _ ↦ false) :
    Set (Σ a, D a) :=
  match t.skeleton island with
  | some s => I.readings ρ lex s
  | none => ∅

variable (I : Interpreter G Node) (M : G.language.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → Set (Σ a, W a)) (island : C → Bool)

/-- A word's readings are the values of the items it may be. -/
@[simp] theorem readings_terminal (c : C) (w : L) :
    (terminal c w).readings I M ρ lex island = (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inl w) := rfl

variable {I M ρ lex island}

/-- A reading of a binary node is the value of a rule the node admits, at readings of its
daughters. -/
theorem mem_readings_phrase_binary {c : C} {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Σ a, D a} :
    d ∈ (phrase c k [t₁, t₂]).readings I M ρ lex island ↔
      ∃ d₁ ∈ t₁.readings I M ρ lex island, ∃ d₂ ∈ t₂.readings I M ρ lex island,
        ∃ m ∈ I.binary (if island c then .island else .branch) d₁.1 d₂.1,
          d = ⟨m.1, M.funMap (.binary m.2) (d₁.2, d₂.2)⟩ := by
  simp only [readings, skeleton]
  cases skeleton island t₁ <;> cases skeleton island t₂ <;> simp [Interpreter.readings]

/-- Under the type-driven interpreter, a reading of a binary node is the value of a rule of the
grammar at readings of its daughters. -/
theorem mem_readings_typeDriven_phrase_binary [G.LocallyFinite] {M : G.language.Structure D}
    {ρ : ∀ {a : T}, W a → D a} {lex : L ⊕ ℕ → Set (Σ a, W a)} {island : C → Bool} {c : C}
    {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Σ a, D a} :
    d ∈ (phrase c k [t₁, t₂]).readings (typeDriven G) M ρ lex island ↔
      ∃ d₁ ∈ t₁.readings (typeDriven G) M ρ lex island,
        ∃ d₂ ∈ t₂.readings (typeDriven G) M ρ lex island,
          ∃ (u : T) (m : G.Binary d₁.1 d₂.1 u), d = ⟨u, M.funMap (.binary m) (d₁.2, d₂.2)⟩ := by
  rw [mem_readings_phrase_binary]
  exact ⟨fun ⟨d₁, h₁, d₂, h₂, ⟨u, m⟩, _, h⟩ ↦ ⟨d₁, h₁, d₂, h₂, u, m, h⟩,
    fun ⟨d₁, h₁, d₂, h₂, u, m, h⟩ ↦ ⟨d₁, h₁, d₂, h₂, ⟨u, m⟩, LocallyFinite.mem_binaryRules m, h⟩⟩

end PhraseStructure.Tree
