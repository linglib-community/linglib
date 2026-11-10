module

public import Linglib.Semantics.Composition.Constituency
public import Mathlib.Data.Set.Image

/-!
# Readings over a lexicon of sets

A word may have infinitely many items, as a coordinator has one at every conjoinable type. The
derivations an interpreter admits over a structure are then a set, which says what the search
over a lexicon of lists is to find, and [it finds exactly those](##Interpreter.mem_derivs_iff).
The readings of a structure are the values of these derivations.

## References

* [partee-rooth-1983]
-/

@[expose] public section

universe u v w x

namespace Interpreter

open ManySorted ManySorted.Language

variable {T : Type u} {G : Language.{u, v} T} {N : Type v} {L : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The derivations an interpreter admits over a bare structure when a leaf may be any of a set
of items: the specification that `Interpreter.derivs` computes for a lexicon of lists. -/
def derivations (I : Interpreter G N) (lex : L → Set (Σ a, W a)) :
    Skeleton N L → Set (Σ a, Deriv G W a)
  | .leaf x => (fun p ↦ ⟨p.1, .leaf p.2⟩) '' lex x
  | .unary n s => {d | ∃ d₁ ∈ I.derivations lex s, ∃ r ∈ I.unary n d₁.1,
      d = ⟨r.1, .unary r.2 d₁.2⟩}
  | .binary n s₁ s₂ => {d | ∃ d₁ ∈ I.derivations lex s₁, ∃ d₂ ∈ I.derivations lex s₂,
      ∃ m ∈ I.binary n d₁.1 d₂.1, d = ⟨m.1, .binary m.2 d₁.2 d₂.2⟩}

/-- The derivations an interpreter finds are sound and complete: they are the derivations it
admits. -/
theorem mem_derivs_iff {I : Interpreter G N} {lex : L → List (Σ a, W a)}
    {d : Σ a, Deriv G W a} :
    ∀ {s : Skeleton N L}, d ∈ I.derivs lex s ↔ d ∈ I.derivations (fun x ↦ {p | p ∈ lex x}) s
  | .leaf x => by simp [derivs, derivations, eq_comm]
  | .unary n s => by
    simp only [derivs, derivations, List.mem_flatMap, List.mem_map, Set.mem_ofPred_eq,
      ← mem_derivs_iff (s := s), eq_comm]
  | .binary n s₁ s₂ => by
    simp only [derivs, derivations, List.mem_flatMap, List.mem_map, Set.mem_ofPred_eq,
      ← mem_derivs_iff (s := s₁), ← mem_derivs_iff (s := s₂), eq_comm]

/-- The readings of a bare structure when a leaf may be any of a set of items: the values of the
derivations over it. -/
def readings (I : Interpreter G N) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L → Set (Σ a, W a)) (s : Skeleton N L) : Set (Σ a, D a) :=
  (fun d ↦ ⟨d.1, d.2.realize M ρ⟩) '' I.derivations lex s

/-- The values an interpreter finds are the readings, for a lexicon of lists. -/
theorem mem_values_iff {I : Interpreter G N} {M : G.Structure D} {ρ : ∀ {a : T}, W a → D a}
    {lex : L → List (Σ a, W a)} {s : Skeleton N L} {d : Σ a, D a} :
    d ∈ I.values M ρ lex s ↔ d ∈ I.readings M ρ (fun x ↦ {p | p ∈ lex x}) s := by
  simp only [values, readings, List.mem_map, Set.mem_image, mem_derivs_iff]

variable {I : Interpreter G N} {M : G.Structure D} {ρ : ∀ {a : T}, W a → D a}
  {d : Σ a, D a}

@[simp] theorem readings_leaf (lex : L → Set (Σ a, W a)) (x : L) :
    I.readings M ρ lex (.leaf x) = (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex x := by
  simp [readings, derivations, Set.image_image]

/-- A reading of a unary node is the value of a rule the node admits, at a reading of its
daughter. -/
theorem mem_readings_unary {lex : L → Set (Σ a, W a)} {n : N} {s : Skeleton N L} :
    d ∈ I.readings M ρ lex (.unary n s) ↔
      ∃ d₁ ∈ I.readings M ρ lex s, ∃ r ∈ I.unary n d₁.1,
        d = ⟨r.1, M.funMap r.2 d₁.2⟩ := by
  simp only [readings, derivations, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨e, h, r, hr, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, h, rfl⟩, r, hr, rfl⟩
  · rintro ⟨_, ⟨e, h, rfl⟩, r, hr, rfl⟩
    exact ⟨_, ⟨e, h, r, hr, rfl⟩, rfl⟩

/-- A reading of a binary node is the value of a rule the node admits, at readings of its
daughters. -/
theorem mem_readings_binary {lex : L → Set (Σ a, W a)} {n : N} {s₁ s₂ : Skeleton N L} :
    d ∈ I.readings M ρ lex (.binary n s₁ s₂) ↔
      ∃ d₁ ∈ I.readings M ρ lex s₁, ∃ d₂ ∈ I.readings M ρ lex s₂,
        ∃ m ∈ I.binary n d₁.1 d₂.1, d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp only [readings, derivations, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨e₁, h₁, e₂, h₂, m, hm, rfl⟩, rfl⟩
    exact ⟨_, ⟨e₁, h₁, rfl⟩, _, ⟨e₂, h₂, rfl⟩, m, hm, rfl⟩
  · rintro ⟨_, ⟨e₁, h₁, rfl⟩, _, ⟨e₂, h₂, rfl⟩, m, hm, rfl⟩
    exact ⟨_, ⟨e₁, h₁, e₂, h₂, m, hm, rfl⟩, rfl⟩

end Interpreter

namespace PhraseStructure.Tree

open ManySorted ManySorted.Language Interpreter

variable {C L : Type} {T : Type} {G : Language T} {W D : T → Type}

/-- The values of a tree when a word or a trace may be any of a set of items. -/
def readings (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → Set (Σ a, W a)) (t : Tree C L) (island : C → Bool := fun _ ↦ false) :
    Set (Σ a, D a) :=
  match t.skeleton island with
  | some s => I.readings M ρ lex s
  | none => ∅

variable (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → Set (Σ a, W a)) (island : C → Bool)

/-- A word's readings are the values of the items it may be. -/
@[simp] theorem readings_terminal (c : C) (w : L) :
    (terminal c w).readings I M ρ lex island = (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inl w) :=
  Interpreter.readings_leaf _ _

/-- A trace's readings are the values of the items its index may be. -/
@[simp] theorem readings_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).readings I M ρ lex island =
      (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inr n) :=
  Interpreter.readings_leaf _ _

variable {I M ρ lex island}

/-- A reading of a binder is the value of a rule its index admits, at a reading of its body. -/
theorem mem_readings_bind {n : ℕ} {c : C} {t : Tree C L} {d : Σ a, D a} :
    d ∈ (bind n c t).readings I M ρ lex island ↔
      ∃ d₁ ∈ t.readings I M ρ lex island, ∃ r ∈ I.unary (.index n) d₁.1,
        d = ⟨r.1, M.funMap r.2 d₁.2⟩ := by
  simp only [readings, skeleton]
  cases skeleton island t <;> simp [Interpreter.mem_readings_unary]

/-- A reading of a binary node is the value of a rule the node admits, at readings of its
daughters. -/
theorem mem_readings_phrase_binary {c : C} {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Σ a, D a} :
    d ∈ (phrase c k [t₁, t₂]).readings I M ρ lex island ↔
      ∃ d₁ ∈ t₁.readings I M ρ lex island, ∃ d₂ ∈ t₂.readings I M ρ lex island,
        ∃ m ∈ I.binary (if island c then .island else .branch) d₁.1 d₂.1,
          d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp only [readings, skeleton]
  cases skeleton island t₁ <;> cases skeleton island t₂ <;> simp [Interpreter.mem_readings_binary]

/-- Under the type-driven interpreter, a reading of a binary node is the value of a rule of the
grammar at readings of its daughters. -/
theorem mem_readings_typeDriven_phrase_binary [G.LocallyFinite] {M : G.Structure D}
    {ρ : ∀ {a : T}, W a → D a} {lex : L ⊕ ℕ → Set (Σ a, W a)} {island : C → Bool} {c : C}
    {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Σ a, D a} :
    d ∈ (phrase c k [t₁, t₂]).readings (typeDriven G) M ρ lex island ↔
      ∃ d₁ ∈ t₁.readings (typeDriven G) M ρ lex island,
        ∃ d₂ ∈ t₂.readings (typeDriven G) M ρ lex island,
          ∃ (u : T) (m : G.Binary d₁.1 d₂.1 u), d = ⟨u, M.funMap m (d₁.2, d₂.2)⟩ := by
  simp [mem_readings_phrase_binary, Sigma.exists]

end PhraseStructure.Tree
