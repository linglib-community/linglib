module

public import Linglib.Core.Computability.PartialMoore

/-!
# Feature structures

A *feature structure* describes a linguistic object by its features: the pronoun *she* has the
feature `PERSON` with the value *third* and `NUMBER` with the value *singular*. A value may have
features of its own, and two paths of features may lead to the same value, so a feature
structure is a rooted graph whose nodes carry types. We define it as a partial Moore machine,
with the features as letters and the types as outputs, and a root from which every state is
reached.

A feature structure `A` *subsumes* `B` when `B` contains all the information in `A`: a map of
nodes sends the root to the root, each node to a node of an equal or more specific type, and the
value of a feature to the value of the same feature. The *abstract feature structure* `A.abs`
keeps only the type at the end of each path and which paths lead to the same node. The main
result, `FeatureStructure.subsumes_iff_abs_le`, says that `A` subsumes `B` exactly when
`A.abs ≤ B.abs`.

## Implementation notes

In the order of types the more specific type is the greater, as in the orders of feature bundles
and flat slots. Subsumption is weaker than a map that keeps every type and every missing
feature: such a map preserves the truth of descriptions, including negative ones, and
subsumption does not.

## References

* [kasper-rounds-1990]
* [carpenter-1992]
-/

@[expose] public section

/-- A feature structure: nodes with a root, a type at each node and a partial function on nodes
for each feature, every node being reached from the root ([carpenter-1992], Definition 3.1). -/
structure FeatureStructure (Q F T : Type*) extends PartialMoore Q F T where
  /-- The root node. -/
  root : Q
  /-- Every node is reached from the root. -/
  rooted : ∀ q, toPartialMoore.Reaches root q

namespace PartialMoore

variable {σ α β : Type*} (M : PartialMoore σ α β) (s : σ)

/-- The machine on the states reached from `s`. -/
def reachable : PartialMoore {q // M.Reaches s q} α β where
  step q a :=
    match h : M.step q a with
    | some q' => some ⟨q', q.2.step h⟩
    | none => none
  out q := M.out q

theorem map_val_step_reachable (q : {q // M.Reaches s q}) (a : α) :
    ((M.reachable s).step q a).map Subtype.val = M.step q a := by
  unfold reachable
  dsimp only
  split <;> simp [*]

theorem map_val_evalFrom_reachable (q : {q // M.Reaches s q}) (x : List α) :
    ((M.reachable s).evalFrom q x).map Subtype.val = M.evalFrom q x := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih =>
    rw [evalFrom_cons, evalFrom_cons, ← map_val_step_reachable, Option.map_bind, Option.bind_map]
    exact congrArg _ (funext fun q' ↦ ih q')

/-- The feature structure of a state: the states reached from it, rooted at it. -/
def featureStructure : FeatureStructure {q // M.Reaches s q} α β where
  toPartialMoore := M.reachable s
  root := ⟨s, .refl M s⟩
  rooted q := by
    obtain ⟨x, hx⟩ := q.2
    obtain ⟨q', hq', e⟩ := Option.map_eq_some_iff.1
      ((M.map_val_evalFrom_reachable s ⟨s, .refl M s⟩ x).trans hx)
    exact ⟨x, hq'.trans (congrArg some (Subtype.ext e))⟩

end PartialMoore

namespace FeatureStructure

variable {Q Q' Q'' F T : Type*}

section Preorder

variable [Preorder T] (A : FeatureStructure Q F T) (B : FeatureStructure Q' F T)
  (C : FeatureStructure Q'' F T)

/-- `A` subsumes `B` when a map of nodes sends root to root, sends each node to one of an at
least as specific type, and preserves each feature where it is defined
([carpenter-1992], Definition 3.4). -/
def Subsumes : Prop := A.toPartialMoore.SimulatedBy B.toPartialMoore A.root B.root

variable {A B C}

theorem subsumes_iff_exists : A.Subsumes B ↔ ∃ h : Q → Q', h A.root = B.root ∧
    (∀ q, A.out q ≤ B.out (h q)) ∧ ∀ f q q', A.step q f = some q' → B.step (h q) f = some (h q') :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr
    (forall_congr' fun q ↦ imp_iff_right (A.rooted q))
    (forall₃_congr fun _ q _ ↦ imp_iff_right (A.rooted q))

theorem Subsumes.refl (A : FeatureStructure Q F T) : A.Subsumes A :=
  PartialMoore.SimulatedBy.refl _ _

theorem Subsumes.trans (h₁ : A.Subsumes B) (h₂ : B.Subsumes C) : A.Subsumes C :=
  PartialMoore.SimulatedBy.trans h₁ h₂

end Preorder

/-- An abstract feature structure gives the type at the end of each defined path and the pairs of
paths that lead to one node ([carpenter-1992], Definition 3.8). -/
@[ext] structure Abstract (F T : Type*) where
  /-- The type at the end of a path, where the path is defined. -/
  type : List F → Option T
  /-- Two paths lead to one node. -/
  Equiv : List F → List F → Prop

/-- An abstract feature structure is below another when the second defines every path the first
does, with an at least as specific type, and identifies every two paths the first does. -/
instance [PartialOrder T] : PartialOrder (Abstract F T) where
  le X Y := (∀ p a, X.type p = some a → ∃ b, Y.type p = some b ∧ a ≤ b) ∧
    ∀ p p', X.Equiv p p' → Y.Equiv p p'
  le_refl _ := ⟨fun _ a h ↦ ⟨a, h, le_rfl⟩, fun _ _ h ↦ h⟩
  le_trans _ _ _ h₁ h₂ := ⟨fun p a h ↦
    let ⟨b, hb, hle⟩ := h₁.1 p a h
    let ⟨c, hc, hle'⟩ := h₂.1 p b hb
    ⟨c, hc, hle.trans hle'⟩, fun p p' h ↦ h₂.2 p p' (h₁.2 p p' h)⟩
  le_antisymm X Y h₁ h₂ := by
    ext p a
    · constructor
      · intro hp
        obtain ⟨b, hb, hle⟩ := h₁.1 p a hp
        obtain ⟨c, hc, hle'⟩ := h₂.1 p b hb
        obtain rfl : c = a := Option.some.inj (hc.symm.trans hp)
        rw [hb, le_antisymm hle' hle]
      · intro hp
        obtain ⟨b, hb, hle⟩ := h₂.1 p a hp
        obtain ⟨c, hc, hle'⟩ := h₁.1 p b hb
        obtain rfl : c = a := Option.some.inj (hc.symm.trans hp)
        rw [hb, le_antisymm hle' hle]
    · exact ⟨h₁.2 p a, h₂.2 p a⟩

/-- The abstract feature structure of a feature structure. -/
def abs (A : FeatureStructure Q F T) : Abstract F T where
  type := A.output? A.root
  Equiv := A.Nerode A.root

variable [PartialOrder T] {A : FeatureStructure Q F T} {B : FeatureStructure Q' F T}

/-- Subsumption depends only on the abstract feature structures ([carpenter-1992],
Theorem 3.9). -/
theorem subsumes_iff_abs_le : A.Subsumes B ↔ A.abs ≤ B.abs :=
  PartialMoore.simulatedBy_iff

/-- Feature structures have the same abstract feature structure exactly when they subsume each
other. -/
theorem abs_eq_iff : A.abs = B.abs ↔ A.Subsumes B ∧ B.Subsumes A := by
  rw [subsumes_iff_abs_le, subsumes_iff_abs_le, le_antisymm_iff]

end FeatureStructure
