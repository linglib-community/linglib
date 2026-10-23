module

public import Linglib.Core.ModelTheory.Atom
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Factors of relational structures

A `k`-factor is a connected structure on at most `k` elements, presented by a set of atoms on
`Fin n` whose Gaifman graph is connected. It occurs in a structure when some assignment realizes
its atoms there, that is, when its canonical structure maps homomorphically into the structure.
Homomorphisms are the weak ones of mathlib, so a factor may leave a relation unsaid, and a factor
occurring in a structure occurs in every structure it maps into.

## Main definitions

* `FirstOrder.Language.Atom.gaifman`: the Gaifman graph of a set of atoms.
* `FirstOrder.Language.Factor`: connected sets of atoms on at most `k` variables.
* `FirstOrder.Language.Factor.Occurs`, `FirstOrder.Language.factors`: occurrence, and the
  `k`-factors of a structure.

## Main statements

* `FirstOrder.Language.Factor.occurs_iff_nonempty_hom`: a factor occurs exactly when its canonical
  structure maps homomorphically into the structure.
* `FirstOrder.Language.factors_mono`: a homomorphism carries the factors of its domain to
  factors of its codomain.

## References

* [libkin-2004]
* [rogers-lambert-2019]
-/

@[expose] public section

universe u v w x

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- The Gaifman graph of a set of atoms joins two distinct variables that an atom mentions
together. -/
def Atom.gaifman {α : Type w} (T : Set (L.Atom α)) : SimpleGraph α :=
  .fromRel fun x y ↦ ∃ a ∈ T, x ∈ Set.range a.args ∧ y ∈ Set.range a.args

variable (L) in
/-- A `k`-factor is a connected set of atoms on at most `k` variables, presenting a connected
structure on at most `k` elements. -/
structure Factor (k : ℕ) where
  /-- The number of variables. -/
  {n : ℕ}
  le : n ≤ k
  /-- The atoms. -/
  atoms : Set (L.Atom (Fin n))
  preconnected : (Atom.gaifman atoms).Preconnected

namespace Factor

variable {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N] {f : L.Factor k}

variable (M) in
/-- A factor occurs in a structure when some assignment realizes its atoms there. -/
def Occurs (f : L.Factor k) : Prop :=
  (Atom.realizers M f.atoms).Nonempty

theorem occurs_iff_nonempty_hom [L.IsRelational] :
    f.Occurs M ↔ Nonempty (Atom.Canonical f.atoms →[L] M) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨(Atom.Canonical.homEquiv _).symm ⟨v, hv⟩⟩,
    fun ⟨φ⟩ ↦ ⟨_, (Atom.Canonical.homEquiv _ φ).2⟩⟩

theorem Occurs.hom (φ : M →[L] N) : f.Occurs M → f.Occurs N :=
  fun ⟨v, hv⟩ ↦ ⟨φ ∘ v, Atom.comp_mem_realizers φ hv⟩

end Factor

variable (L) in
/-- The `k`-factors of a structure are the factors occurring in it. -/
def factors (k : ℕ) (M : Type w) [L.Structure M] : Set (L.Factor k) :=
  {f | f.Occurs M}

@[simp] theorem mem_factors {k : ℕ} {M : Type w} [L.Structure M] {f : L.Factor k} :
    f ∈ L.factors k M ↔ f.Occurs M :=
  .rfl

theorem factors_mono {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N]
    (φ : M →[L] N) : L.factors k M ⊆ L.factors k N :=
  fun _ ↦ Factor.Occurs.hom φ

end FirstOrder.Language
