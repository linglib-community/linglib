module

public import Linglib.Core.ModelTheory.Atom
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.UpperLower.Basic

/-!
# Factors of relational structures

A `k`-factor is a connected structure on at most `k` elements, presented by a set of atoms on
`Fin n` whose Gaifman graph is connected. It occurs in a structure when some assignment realizes
its atoms there, that is, when its canonical structure maps homomorphically into the structure.
Homomorphisms are the weak ones of mathlib, so a factor may leave a relation unsaid, and a factor
occurring in a structure occurs in every structure it maps into. One factor is a subfactor of
another when the structure it presents maps homomorphically into the other's; this preorder is the
subfactor order of Chandlee, Eyraud, Heinz, Jardine and Rawski, and the factors of a structure
form a lower set in it.

## Main definitions

* `FirstOrder.Language.Atom.gaifman`: the Gaifman graph of a set of atoms.
* `FirstOrder.Language.Factor`: connected sets of atoms on at most `k` variables, preordered by
  the subfactor relation.
* `FirstOrder.Language.Factor.Occurs`, `FirstOrder.Language.factors`: occurrence, and the
  `k`-factors of a structure.
* `FirstOrder.Language.Factor.castLE`, `FirstOrder.Language.Factor.castLEOrderEmb`: a `k`-factor
  as a `k'`-factor for `k ≤ k'`, an embedding of the subfactor orders.

## Main statements

* `FirstOrder.Language.Factor.occurs_iff_nonempty_hom`: a factor occurs exactly when its canonical
  structure maps homomorphically into the structure.
* `FirstOrder.Language.factors_mono`: a homomorphism carries the factors of its domain to
  factors of its codomain.
* `FirstOrder.Language.isLowerSet_factors`: the factors of a structure are closed under
  subfactors.

## References

* [libkin-2004]
* [rogers-lambert-2019]
* [chandlee-eyraud-heinz-jardine-rawski-2019]
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
  n_le : n ≤ k
  /-- The atoms. -/
  atoms : Set (L.Atom (Fin n))
  preconnected : (Atom.gaifman atoms).Preconnected

namespace Factor

variable {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N] {f g : L.Factor k}

variable (M) in
/-- A factor occurs in a structure when some assignment realizes its atoms there. -/
def Occurs (f : L.Factor k) : Prop :=
  (Atom.realizers M f.atoms).Nonempty

/-- A factor occurs exactly when its canonical structure maps homomorphically into the
structure. -/
theorem occurs_iff_nonempty_hom [L.IsRelational] :
    f.Occurs M ↔ Nonempty (Atom.Canonical f.atoms →[L] M) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨(Atom.Canonical.homEquiv _).symm ⟨v, hv⟩⟩,
    fun ⟨φ⟩ ↦ ⟨_, (Atom.Canonical.homEquiv _ φ).2⟩⟩

theorem Occurs.hom (φ : M →[L] N) : f.Occurs M → f.Occurs N :=
  fun ⟨v, hv⟩ ↦ ⟨φ ∘ v, Atom.comp_mem_realizers φ hv⟩

/-! ### The subfactor order -/

section Order

variable [L.IsRelational]

/-- One factor is a subfactor of another when the structure it presents maps homomorphically
into the structure the other presents. -/
instance : Preorder (L.Factor k) where
  le f g := Nonempty (Atom.Canonical f.atoms →[L] Atom.Canonical g.atoms)
  le_refl _ := ⟨Hom.id L _⟩
  le_trans _ _ _ := fun ⟨φ⟩ ⟨ψ⟩ ↦ ⟨ψ.comp φ⟩

theorem le_iff_occurs : f ≤ g ↔ f.Occurs (Atom.Canonical g.atoms) :=
  occurs_iff_nonempty_hom.symm

/-- A subfactor of a factor occurring in a structure occurs in it. -/
theorem Occurs.of_le (h : f ≤ g) (hg : g.Occurs M) : f.Occurs M :=
  let ⟨φ⟩ := h
  let ⟨ψ⟩ := occurs_iff_nonempty_hom.1 hg
  occurs_iff_nonempty_hom.2 ⟨ψ.comp φ⟩

end Order

/-- Over finitely many atoms on each number of variables, there are finitely many `k`-factors. -/
instance [∀ n, Finite (L.Atom (Fin n))] : Finite (L.Factor k) :=
  .of_injective (β := Σ n : Fin (k + 1), Set (L.Atom (Fin n)))
    (fun f ↦ ⟨⟨f.n, Nat.lt_succ_of_le f.n_le⟩, f.atoms⟩) <| by
      rintro ⟨_, A, _⟩ ⟨_, B, _⟩ h
      simp only [Sigma.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl

/-! ### Widening the bound -/

section CastLE

variable {k' : ℕ}

/-- A `k`-factor is a `k'`-factor for `k ≤ k'`. -/
def castLE (h : k ≤ k') (f : L.Factor k) : L.Factor k' where
  n_le := f.n_le.trans h
  atoms := f.atoms
  preconnected := f.preconnected

@[simp] theorem occurs_castLE (h : k ≤ k') : (f.castLE h).Occurs M ↔ f.Occurs M := .rfl

theorem castLE_injective (h : k ≤ k') : Function.Injective (castLE (L := L) h) := by
  rintro ⟨_, A, _⟩ ⟨_, B, _⟩ e
  simp only [castLE, mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  cases e
  rfl

/-- Widening the bound on the number of variables embeds the subfactor orders. -/
@[simps! apply]
def castLEOrderEmb [L.IsRelational] (h : k ≤ k') : L.Factor k ↪o L.Factor k' where
  toFun := castLE h
  inj' := castLE_injective h
  map_rel_iff' := .rfl

end CastLE

end Factor

variable (L) in
/-- The `k`-factors of a structure are the factors occurring in it. -/
def factors (k : ℕ) (M : Type w) [L.Structure M] : Set (L.Factor k) :=
  {f | f.Occurs M}

@[simp] theorem mem_factors {k : ℕ} {M : Type w} [L.Structure M] {f : L.Factor k} :
    f ∈ L.factors k M ↔ f.Occurs M :=
  .rfl

/-- The factor on no variables occurs in every structure. -/
theorem factors_nonempty (k : ℕ) (M : Type w) [L.Structure M] : (L.factors k M).Nonempty :=
  ⟨⟨Nat.zero_le k, ∅, fun a ↦ a.elim0⟩, fun i ↦ i.elim0, fun _ h ↦ (Set.notMem_empty _ h).elim⟩

/-- A homomorphism carries the factors of its domain to factors of its codomain. -/
theorem factors_mono {k : ℕ} {M : Type w} {N : Type x} [L.Structure M] [L.Structure N]
    (φ : M →[L] N) : L.factors k M ⊆ L.factors k N :=
  fun _ ↦ Factor.Occurs.hom φ

/-- The `k`-factors of a structure are those of its `k'`-factors on at most `k` variables. -/
@[simp] theorem preimage_castLE_factors {k k' : ℕ} (h : k ≤ k') (M : Type w) [L.Structure M] :
    Factor.castLE h ⁻¹' L.factors k' M = L.factors k M :=
  rfl

/-- The factors of a structure are closed under subfactors. -/
theorem isLowerSet_factors [L.IsRelational] {k : ℕ} {M : Type w} [L.Structure M] :
    IsLowerSet (L.factors k M) :=
  fun _ _ h ↦ Factor.Occurs.of_le h

end FirstOrder.Language
