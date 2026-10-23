module

public import Linglib.Logic.CylindricAlgebra
public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Set.Function

/-!
# Register structures

A register structure is a type of states with registers, each register holding a value that can
be read (`val`) and updated (`extend`) according to the laws of `Function.update`. The canonical
example is a function type, whose coordinates are the registers. Muskens grafts discourse
representation theory onto type logic over such states: random assignment `[r]` resets a
register, and a box `[u₁ … uₙ | C]` resets its registers and tests `C`. The conditions over a
register structure form a cylindric algebra in the sense of Henkin, Monk and Tarski, in which
cylindrification is the weakest precondition of `[r]`.

## Main definitions

* `RegisterStructure R S E`, with its canonical instance at `V → E`.
* `RegisterStructure.cylindricAlgebra`: the cylindric algebra of conditions.
* `Update.randomAssign`, `Update.dexists`, `Update.dforall`: random assignment and the dynamic
  quantifiers.
* `Update.box`: the box `[u₁ … uₙ | C]` over a finite set of registers.
* `Update.Fixes`, `Update.maxAt`: an update leaves a register unchanged, and maximization over a
  register's value.

## Main results

* `Update.randomAssign_comp_self`, `Update.commute_randomAssign`: random assignments are
  idempotent and commute; with the `SetRel.IsRefl`, `IsSymm` and `IsTrans` instances, each is an
  equivalence.
* `Update.preimage_randomAssign`, `Update.core_randomAssign`, `Update.dom_dexists`: the weakest
  precondition of `[r]` is cylindrification and its dual the universal; an existential is true
  where the cylindrification of its scope's truth set is.
* `Update.commute_test_randomAssign_iff`: a test commutes with `[r]` exactly when `r` is outside
  the dimension set of its condition.
* `Update.box_comp_box`: two boxes in sequence are one box over the union of their registers
  when the second's registers lie outside the dimension set of the first's condition (Muskens's
  Merging Lemma).
* `Update.exists_box_map_iff`, `Update.mem_dom_box_map`: quantifying over the outputs of a box
  over distinct registers is quantifying over tuples of values, so a box whose condition reads
  only its registers is true iff some tuple satisfies it (Muskens's Unselective Binding Lemma).
* `Update.mem_box_iff`: at assignments, a box relates an assignment to those that agree with it
  off the box's registers and satisfy its condition.
* `RegisterStructure.dimSet_preimage_subset`: a condition read off registers in `s` has its
  dimension set inside `s`.

## Implementation notes

Muskens defines `i[r]j` as agreement on every register other than `r` and asserts that enough
states exist (AX1). Here `[r]` is the graph of `extend · r e`, which agrees with his relation when
a state is determined by its registers, as in every instance; it also serves states carrying
several sorts of registers (`Semantics/Dynamic/ICDRT.lean`), and its uniqueness gives the diagonal
axioms of the cylindric algebra. Constant registers (AX4) are constant functions of the state,
and AX3, that distinct referents denote distinct registers, is a hypothesis where it is used.

## References

* [R. Muskens, *Combining Montague semantics and discourse representation* (1996)][muskens-1996]
* [J. Groenendijk and M. Stokhof, *Dynamic predicate logic* (1991)][groenendijk-stokhof-1991]
* [L. Henkin, J. D. Monk and A. Tarski, *Cylindric algebras, part I*
  (1971)][henkin-monk-tarski-1971]
-/

@[expose] public section

namespace DynamicSemantics

/-- A register structure has registers `R` (Muskens's type `π`), a value function `val` (his `V`)
and a register-wise update `extend` satisfying the laws of `Function.update`. `extend`
skolemizes AX1. -/
class RegisterStructure (R S : Type*) (E : outParam Type*) where
  /-- The value of a register in a state (Muskens's `V`). -/
  val : R → S → E
  /-- Update a state at a register (AX1's witness). -/
  extend : S → R → E → S
  /-- The updated register holds the new value. -/
  val_extend_self (i : S) (r : R) (e : E) : val r (extend i r e) = e
  /-- Other registers are untouched. -/
  val_extend_of_ne (i : S) (r r' : R) (e : E) : r' ≠ r → val r' (extend i r e) = val r' i
  /-- Updating a register to its own value does nothing. -/
  extend_eq_self (i : S) (r : R) : extend i r (val r i) = i
  /-- A second update of a register overrides the first. -/
  extend_idem (i : S) (r : R) (e e' : E) : extend (extend i r e) r e' = extend i r e'
  /-- Updates of distinct registers commute. -/
  extend_comm (i : S) {r r' : R} (h : r ≠ r') (e e' : E) :
    extend (extend i r e) r' e' = extend (extend i r' e') r e

namespace RegisterStructure

/-- In the canonical register structure the registers are the coordinates of a function type and
update is `Function.update`. -/
instance instPi {V E : Type*} [DecidableEq V] : RegisterStructure V (V → E) E where
  val v g := g v
  extend g v e := Function.update g v e
  val_extend_self _ _ _ := Function.update_self ..
  val_extend_of_ne _ _ _ _ h := Function.update_of_ne h ..
  extend_eq_self _ _ := Function.update_eq_self ..
  extend_idem _ _ _ _ := Function.update_idem ..
  extend_comm _ _ _ h _ _ := Function.update_comm h ..

variable {R S E : Type*} [RegisterStructure R S E] {r r' : R} {i : S} {C : Set S}

/-- The conditions over a register structure form a cylindric algebra. Cylindrification along
`r` holds where some update of `r` satisfies the condition, and the diagonal of `r` and `r'`
holds where the two registers have the same value. -/
instance cylindricAlgebra : CylindricAlgebra R (Set S) where
  cyl r C := {i | ∃ e, extend i r e ∈ C}
  diag r r' := {i | val r i = val r' i}
  cyl_bot r := by ext; simp
  le_cyl r C i hi := ⟨val r i, by rwa [extend_eq_self]⟩
  cyl_inf_cyl r C D := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.inf_eq_inter, Set.mem_inter_iff, extend_idem]
    exact ⟨fun ⟨e, h, e', h'⟩ ↦ ⟨⟨e, h⟩, e', h'⟩, fun ⟨⟨e, h⟩, e', h'⟩ ↦ ⟨e, h, e', h'⟩⟩
  cyl_comm r r' C := by
    ext i
    obtain rfl | h := eq_or_ne r r'
    · rfl
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨e, e', h'⟩ ↦ ⟨e', e, by rwa [← extend_comm i h]⟩,
      fun ⟨e', e, h'⟩ ↦ ⟨e, e', by rwa [extend_comm i h]⟩⟩
  diag_self r := by ext; simp
  cyl_diag_inf_diag {r r' r''} h h' := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.inf_eq_inter, Set.mem_inter_iff,
      val_extend_of_ne _ _ _ _ (Ne.symm h), val_extend_of_ne _ _ _ _ (Ne.symm h'), val_extend_self]
    exact ⟨fun ⟨_, h₁, h₂⟩ ↦ h₁.trans h₂, fun h ↦ ⟨_, rfl, h⟩⟩
  disjoint_cyl_diag_inf {r r'} h C := by
    rw [Set.disjoint_iff]
    rintro i ⟨⟨e, h₁, hC⟩, e', h₁', hC'⟩
    simp only [Set.mem_ofPred_eq, val_extend_self, val_extend_of_ne _ _ _ _ (Ne.symm h)] at h₁ h₁'
    subst h₁ h₁'
    exact hC' hC

/-- At the canonical register structure the condition algebra is the cylindric set algebra,
reducibly. -/
example {V E : Type*} [DecidableEq V] :
    (cylindricAlgebra : CylindricAlgebra V (Set (V → E))) = CylindricAlgebra.instSetPi := by
  with_reducible_and_instances rfl

open CylindricAlgebra

@[simp] theorem mem_cyl : i ∈ cyl r C ↔ ∃ e, extend i r e ∈ C := Iff.rfl

@[simp] theorem mem_diag : i ∈ (diag r r' : Set S) ↔ val r i = val r' i := Iff.rfl

theorem notMem_dimSet_iff : r ∉ dimSet C ↔ ∀ i e, extend i r e ∈ C ↔ i ∈ C := by
  rw [notMem_dimSet]
  refine ⟨fun h i e ↦ ⟨fun hC ↦ h ▸ ⟨e, hC⟩, fun hi ↦ h ▸ ⟨val r i, ?_⟩⟩, fun h ↦ ?_⟩
  · rwa [extend_idem, extend_eq_self]
  · ext i
    exact ⟨fun ⟨e, he⟩ ↦ (h i e).1 he, fun hi ↦ ⟨val r i, by rwa [extend_eq_self]⟩⟩

theorem dimSet_preimage_subset {α : Type*} {s : Set R} (f : S → α)
    (hf : ∀ r ∉ s, ∀ i e, f (extend i r e) = f i) (P : Set α) : dimSet (f ⁻¹' P) ⊆ s :=
  fun r hr ↦ by_contra fun hrs ↦ (notMem_dimSet_iff.2 fun i e ↦ by
    simp only [Set.mem_preimage, hf r hrs]) hr

theorem dimSet_preimage_val_subset (u : R) (P : Set E) : dimSet (val u ⁻¹' P : Set S) ⊆ {u} :=
  dimSet_preimage_subset _ (fun _ hr _ _ ↦ val_extend_of_ne _ _ _ _ fun h ↦ hr (h ▸ rfl)) P

section Pi

variable {V E : Type*} [DecidableEq V]

@[simp] theorem extend_eq_update (g : V → E) (x : V) (e : E) :
    extend g x e = Function.update g x e := rfl

@[simp] theorem val_apply (g : V → E) (x : V) : val x g = g x := rfl

end Pi

end RegisterStructure

namespace Update

open SetRel RegisterStructure CylindricAlgebra

variable {R S E : Type*} [RegisterStructure R S E] {r r' : R} {i j : S} {C t : Condition S}

/-- Random assignment `[r]` gives the register `r` an arbitrary value. -/
def randomAssign (r : R) : Update S :=
  {(a, b) | ∃ e : E, b = extend a r e}

theorem mem_randomAssign : i ~[randomAssign r] j ↔ ∃ e : E, j = extend i r e := Iff.rfl

instance : (randomAssign r : Update S).IsRefl where
  refl i := ⟨val r i, (extend_eq_self i r).symm⟩

instance : (randomAssign r : Update S).IsSymm where
  symm i _ := by
    rintro ⟨e, rfl⟩
    exact ⟨val r i, by rw [extend_idem, extend_eq_self]⟩

instance : (randomAssign r : Update S).IsTrans where
  trans _ _ _ := by
    rintro ⟨e, rfl⟩ ⟨e', rfl⟩
    exact ⟨e', extend_idem ..⟩

@[simp] theorem randomAssign_comp_self :
    randomAssign r ○ randomAssign r = (randomAssign r : Update S) :=
  comp_eq_self

theorem commute_randomAssign (r r' : R) :
    Commute (randomAssign r : Update S) (randomAssign r') := by
  obtain rfl | h := eq_or_ne r r'
  · rfl
  ext ⟨i, k⟩
  exact ⟨fun ⟨_, ⟨e, hj⟩, e', hk⟩ ↦ ⟨_, ⟨e', rfl⟩, e, hk.trans (hj ▸ extend_comm i h e e')⟩,
    fun ⟨_, ⟨e', hj⟩, e, hk⟩ ↦ ⟨_, ⟨e, rfl⟩, e', hk.trans (hj ▸ (extend_comm i h e e').symm)⟩⟩

theorem preimage_randomAssign (r : R) (t : Condition S) :
    (randomAssign r).preimage t = cyl r t := by
  ext i
  exact ⟨fun ⟨_, hj, e, he⟩ ↦ ⟨e, he ▸ hj⟩, fun ⟨e, he⟩ ↦ ⟨_, he, e, rfl⟩⟩

theorem core_randomAssign (r : R) (t : Condition S) :
    (randomAssign r).core t = {i | ∀ e : E, extend i r e ∈ t} := by
  ext i
  exact ⟨fun h e ↦ h ⟨e, rfl⟩, by rintro h _ ⟨e, rfl⟩; exact h e⟩

theorem commute_test_randomAssign_iff : Commute (test C) (randomAssign r) ↔ r ∉ dimSet C := by
  rw [notMem_dimSet_iff, Commute, SemiconjBy, mul_def, mul_def]
  refine ⟨fun h i e ↦ ⟨fun hC ↦ ?_, fun hi ↦ ?_⟩, fun h ↦ ?_⟩
  · have : i ~[randomAssign r ○ test C] extend i r e := mem_comp_test.2 ⟨⟨e, rfl⟩, hC⟩
    exact (mem_test_comp.1 (h ▸ this)).1
  · have : i ~[test C ○ randomAssign r] extend i r e := mem_test_comp.2 ⟨hi, e, rfl⟩
    exact (mem_comp_test.1 (h ▸ this)).2
  · ext ⟨i, j⟩
    simp only [mem_test_comp, mem_comp_test]
    exact ⟨fun ⟨hi, e, hj⟩ ↦ ⟨⟨e, hj⟩, hj ▸ (h i e).2 hi⟩,
      fun ⟨⟨e, hj⟩, hC⟩ ↦ ⟨(h i e).1 (hj ▸ hC), e, hj⟩⟩

/-- The existential update `∃r(D)` is `[r]; D`. -/
def dexists (r : R) (D : Update S) : Update S :=
  randomAssign r ○ D

/-- The universal condition `∀r(D)` holds iff `D` has an output from every `r`-variant, which is
the clause of [groenendijk-stokhof-1991] for the universal. -/
def dforall (r : R) (D : Update S) : Condition S :=
  impl (randomAssign r) D

theorem mem_dexists {D : Update S} : i ~[dexists r D] j ↔ ∃ e, extend i r e ~[D] j :=
  ⟨by rintro ⟨_, ⟨e, rfl⟩, hD⟩; exact ⟨e, hD⟩, fun ⟨e, hD⟩ ↦ ⟨_, ⟨e, rfl⟩, hD⟩⟩

theorem mem_dforall {D : Update S} : i ∈ dforall r D ↔ ∀ e, extend i r e ∈ D.dom :=
  ⟨fun h e ↦ h ⟨e, rfl⟩, by rintro h _ ⟨e, rfl⟩; exact h e⟩

theorem dom_dexists (D : Update S) : (dexists r D).dom = cyl r D.dom := by
  rw [← preimage_univ_right, dexists, preimage_comp, preimage_univ_right, preimage_randomAssign]

/-! ### Frame conditions and maximization -/

/-- An update `D` fixes the register `r` if no output of `D` changes its value. -/
def Fixes (r : R) (D : Update S) : Prop :=
  ∀ i j, i ~[D] j → val r j = val r i

theorem Fixes.comp {D₁ D₂ : Update S} (h₁ : Fixes r D₁) (h₂ : Fixes r D₂) : Fixes r (D₁ ○ D₂) :=
  fun _ _ ⟨k, hk, hj⟩ ↦ (h₂ k _ hj).trans (h₁ _ k hk)

theorem fixes_id (r : R) : Fixes r (SetRel.id : Update S) :=
  fun _ _ h ↦ SetRel.mem_id.mp h ▸ rfl

theorem fixes_test (r : R) (C : Condition S) : Fixes r (test C) :=
  fun _ _ h ↦ h.1 ▸ rfl

theorem fixes_randomAssign_of_ne (h : r' ≠ r) : Fixes r' (randomAssign (S := S) r) :=
  fun _ _ ⟨e, he⟩ ↦ he ▸ val_extend_of_ne _ r r' e h

/-- Maximization over a register keeps the outputs of `D` at which no other output gives `r` a
strictly greater value. -/
abbrev maxAt [Preorder E] (r : R) (D : Update S) : Update S :=
  maxBy (val r) D

theorem Fixes.maxBy {α : Type*} [Preorder α] {f : S → α} {D : Update S} (h : Fixes r D) :
    Fixes r (maxBy f D) :=
  fun _ _ hD ↦ h _ _ hD.1

theorem maxAt_eq_of_fixes [Preorder E] {D : Update S} (h : Fixes r D) : maxAt r D = D :=
  maxBy_eq_self h

/-! ### Boxes -/

/-- The box `[u₁ … uₙ | C]` of [muskens-1996]'s ABB3 assigns the registers of `s` at random and
then tests `C`. Random assignments commute, so a box needs only the set of its registers. -/
def box (s : Finset R) (C : Condition S) : Update S :=
  s.noncommProd randomAssign (fun r _ r' _ _ ↦ commute_randomAssign r r') * test C

@[simp] theorem box_empty (C : Condition S) : box (∅ : Finset R) C = test C := by
  simp [box]

theorem box_singleton (r : R) (C : Condition S) : box {r} C = dexists r (test C) := by
  rw [box, Finset.noncommProd_singleton, mul_def, dexists]

theorem mem_box_singleton : i ~[box {r} C] j ↔ i ~[randomAssign r] j ∧ j ∈ C := by
  rw [box_singleton, dexists, mem_comp_test]

theorem commute_box_randomAssign (s : Finset R) (h : r ∉ dimSet C) :
    Commute (box s C) (randomAssign r) :=
  .mul_left (Finset.noncommProd_commute _ _ _ _ fun r' _ ↦ commute_randomAssign r r').symm
    (commute_test_randomAssign_iff.2 h)

theorem fixes_box {s : Finset R} (h : r ∉ s) (C : Condition S) : Fixes r (box s C) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fixes_test r C
  | insert r' s hr' ih =>
    rw [box, Finset.noncommProd_insert_of_notMem _ _ _ _ hr', mul_assoc, mul_def]
    exact (fixes_randomAssign_of_ne fun hr ↦ h (by simp [hr])).comp
      (ih fun hr ↦ h (Finset.mem_insert_of_mem hr))

variable [DecidableEq R]

theorem box_insert (r : R) (s : Finset R) (C : Condition S) :
    box (insert r s) C = randomAssign r ○ box s C := by
  by_cases hr : r ∈ s
  · rw [Finset.insert_eq_of_mem hr]
    have : box s C = randomAssign r ○ box (s.erase r) C := by
      conv_lhs => rw [← Finset.insert_erase hr]
      rw [box, Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase r s), mul_assoc,
        mul_def]
      rfl
    rw [this, ← comp_assoc, randomAssign_comp_self]
  · rw [box, Finset.noncommProd_insert_of_notMem _ _ _ _ hr, mul_assoc, mul_def]
    rfl

theorem mem_box_insert {s : Finset R} :
    i ~[box (insert r s) C] j ↔ ∃ e, extend i r e ~[box s C] j := by
  rw [box_insert, ← dexists, mem_dexists]

theorem mem_box_insert_of_mem {s : Finset R} {k : S} (hk : i ~[randomAssign r] k)
    (hj : k ~[box s C] j) : i ~[box (insert r s) C] j := by
  rw [box_insert]
  exact ⟨k, hk, hj⟩

theorem preimage_box_insert (r : R) (s : Finset R) (C t : Condition S) :
    (box (insert r s) C).preimage t = cyl r ((box s C).preimage t) := by
  rw [box_insert, preimage_comp, preimage_randomAssign]

theorem box_comp_box {s t : Finset R} {C' : Condition S} (h : ∀ r ∈ t, r ∉ dimSet C) :
    box s C ○ box t C' = box (s ∪ t) (C ∩ C') := by
  induction t using Finset.induction_on generalizing s with
  | empty => simp [box, ← test_comp_test, ← mul_def, mul_assoc]
  | insert r t hr ih =>
    have hc := commute_box_randomAssign s (h r (Finset.mem_insert_self ..))
    rw [box_insert, Finset.union_insert, box_insert, ← ih fun r' hr' ↦ h r'
      (Finset.mem_insert_of_mem hr'), ← mul_def, ← mul_def, ← mul_def, ← mul_assoc, hc.eq,
      mul_assoc]
    rfl

private theorem map_univ_succ {n : ℕ} (u : Fin (n + 1) ↪ R) :
    Finset.univ.map u = insert (u 0) (Finset.univ.map ((Fin.succEmb n).trans u)) := by
  ext r
  simp [Fin.exists_fin_succ, eq_comm]

theorem exists_box_map_iff {n : ℕ} (u : Fin n ↪ R) (φ : (Fin n → E) → Prop) (i : S) :
    (∃ j, i ~[box (Finset.univ.map u) Set.univ] j ∧ φ fun k ↦ val (u k) j) ↔ ∃ x, φ x := by
  induction n generalizing i with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.map_empty, box_empty, test_univ, SetRel.mem_id,
      exists_eq_left']
    exact ⟨fun h ↦ ⟨_, h⟩, fun ⟨x, h⟩ ↦ by rwa [Subsingleton.elim (fun k ↦ val (u k) i) x]⟩
  | succ n ih =>
    set u' := (Fin.succEmb n).trans u
    have h0 {e : E} {j : S} (hj : extend i (u 0) e ~[box (Finset.univ.map u') Set.univ] j) :
        Fin.cons e (fun k ↦ val (u' k) j) = fun k ↦ val (u k) j := by
      refine funext (Fin.cases ?_ fun _ ↦ rfl)
      have hu0 : u 0 ∉ Finset.univ.map u' := by
        simp [u', Fin.succ_ne_zero]
      rw [Fin.cons_zero, fixes_box hu0 _ _ _ hj, val_extend_self]
    rw [map_univ_succ, Fin.exists_fin_succ_pi]
    simp only [mem_box_insert]
    constructor
    · rintro ⟨j, ⟨e, hj⟩, hφ⟩
      exact ⟨e, (ih u' (fun y ↦ φ (Fin.cons e y)) _).1 ⟨j, hj, (h0 hj).symm ▸ hφ⟩⟩
    · rintro ⟨e, y, hφ⟩
      obtain ⟨j, hj, hφ⟩ := (ih u' (fun y ↦ φ (Fin.cons e y)) (extend i (u 0) e)).2 ⟨y, hφ⟩
      exact ⟨j, ⟨e, hj⟩, h0 hj ▸ hφ⟩

theorem mem_dom_box_map {n : ℕ} (u : Fin n ↪ R) (P : (Fin n → E) → Prop) (i : S) :
    i ∈ (box (Finset.univ.map u) {j | P fun k ↦ val (u k) j}).dom ↔ ∃ x, P x := by
  have : box (Finset.univ.map u) {j | P fun k ↦ val (u k) j} =
      box (Finset.univ.map u) Set.univ ○ test {j : S | P fun k ↦ val (u k) j} := by
    simp only [box, ← mul_def, test_univ, ← one_def, mul_one]
  rw [this, mem_dom, ← exists_box_map_iff u P i]
  simp only [mem_comp_test, Set.mem_ofPred_eq]

/-! ### The canonical register structure -/

section Pi

variable {V E : Type*} [DecidableEq V] {g h : V → E} {x : V}

theorem mem_box_iff {s : Finset V} {C : Condition (V → E)} :
    g ~[box s C] h ↔ (∀ y ∉ s, h y = g y) ∧ h ∈ C := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp [funext_iff, eq_comm]
  | insert x s hx ih =>
    simp only [mem_box_insert, ih, extend_eq_update, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨e, hh, hC⟩
      exact ⟨fun y ⟨hyx, hys⟩ ↦ (hh y hys).trans (Function.update_of_ne hyx e g), hC⟩
    · rintro ⟨hh, hC⟩
      refine ⟨h x, fun y hys ↦ ?_, hC⟩
      obtain rfl | hyx := eq_or_ne y x
      · simp
      · rw [hh y ⟨hyx, hys⟩, Function.update_of_ne hyx]

theorem mem_randomAssign_iff_eqOn : g ~[randomAssign x] h ↔ Set.EqOn g h {x}ᶜ :=
  ⟨by rintro ⟨e, rfl⟩ v hv; exact (Function.update_of_ne hv e g).symm,
    fun hk ↦ ⟨h x, (Function.update_eq_iff.mpr ⟨rfl, fun _ hv ↦ hk hv⟩).symm⟩⟩

end Pi

end Update

end DynamicSemantics
