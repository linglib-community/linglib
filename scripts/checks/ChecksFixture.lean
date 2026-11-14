/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import ChecksFixtureDeps

/-!
# Fixture for the check hash

Declarations that differ in one respect each, for `python3 scripts/checks.py selftest`, which
checks that `checkClosure` gives them the same term exactly when the difference does not change
what they say: a change of statement, or of the type of a bound variable, changes the term, while
a change of proof, of the name of a bound variable or of a binder's annotation does not. Nor does
a switch from a constant's old name to its new one, once the rename is recorded.
-/

@[expose] public section

namespace ChecksFixture

/-! A bound variable's type, which the pretty-printer hides. -/

def unionOne (f : ℕ → ℕ) : Set ℕ := ⋃ (a : ℕ) (_ : f a = 1), {a}

def unionZero (f : ℕ → ℕ) : Set ℕ := ⋃ (a : ℕ) (_ : f a = 0), {a}

/-! The statement itself, and the names of bound variables. -/

def bounded (n : ℕ) : Prop := ∀ m, m ≤ n → m < n + 1

def boundedStrict (n : ℕ) : Prop := ∀ m, m < n → m < n + 1

def boundedRenamed (n : ℕ) : Prop := ∀ k, k ≤ n → k < n + 1

/-! A binder's annotation, and a theorem's proof. -/

theorem subset_explicit (f : ℕ → ℕ) : unionOne f ⊆ Set.univ := Set.subset_univ _

theorem subset_implicit {f : ℕ → ℕ} : unionOne f ⊆ Set.univ := Set.subset_univ _

theorem subset_otherProof (f : ℕ → ℕ) : unionOne f ⊆ Set.univ := fun _ _ ↦ trivial

/-! A proof inside a definition's body, and a lemma used only there. -/

theorem one_pos : 0 < 1 := Nat.one_pos

def positiveByDecide : {n : ℕ // 0 < n} := ⟨1, by decide⟩

def positiveByLemma : {n : ℕ // 0 < n} := ⟨1, one_pos⟩

/-! A proof inside a statement. -/

theorem val_byDecide : (⟨0, by decide⟩ : Fin 2).val = 0 := rfl

theorem val_byLemma : (⟨0, Nat.two_pos⟩ : Fin 2).val = 0 := rfl

/-! A renamed constant (`ChecksFixtureDeps`), under its old name, under its new name, and a
constant deprecated in favour of the new name without being an alias of it. -/

set_option linter.deprecated false in
def evenOld (n : ℕ) : Prop := ∃ m, n = ChecksFixtureDeps.twice m

def evenNew (n : ℕ) : Prop := ∃ m, n = ChecksFixtureDeps.double m

set_option linter.deprecated false in
def evenAddSelf (n : ℕ) : Prop := ∃ m, n = ChecksFixtureDeps.addSelf m

end ChecksFixture
