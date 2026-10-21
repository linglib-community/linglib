module

public import Linglib.Core.Relation.SetRel
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Modal operators and frame conditions

This file defines the relational necessity and possibility of Kripke semantics over an
accessibility relation `R : SetRel W' W`, as operators on propositions `W → Prop`: `□[R] p w`
holds when `p` holds at every `R`-successor of `w`, `◇[R] p w` when it holds at some. They are
mathlib's `SetRel.core` and `SetRel.preimage` read on predicates (`box_iff_mem_core`,
`diamond_iff_mem_preimage`), in the way `Filter.Eventually` reads a filter on predicates, so
propositions stated as sets use the mathlib operators directly. Of the frame conditions of
correspondence theory, reflexivity, symmetry and transitivity are mathlib's `SetRel.IsRefl`,
`SetRel.IsSymm` and `SetRel.IsTrans`; this file adds seriality and the Euclidean property and
proves the axioms K, T, D, B, 4, 5 and Alt₁ over their frames, each axiom defining its frame
condition. Possibility along a relation is left adjoint to necessity along its converse
(`diamond_box_gc`), which gives monotonicity and the normality laws for a relation between any
two types, on sets mathlib's `SetRel.image_core_gc`, `SetRel.core_mono`, `SetRel.core_inter`,
`SetRel.core_univ` and `SetRel.preimage_union`. Along a composite relation necessity nests in
necessity (`box_comp`). Negation Swap, `□¬p ↔ ¬□p` for every `p`, defines functionality
(`box_not_iff_not_box_at_iff`): a modal that commutes with negation is necessity along the graph
of a function, which is precomposition (`box_compl_eq_iff`, `box_graph`).

## Main definitions

* `ModalLogic.Box`, `ModalLogic.Diamond`, with notation `□[R]` and `◇[R]`.
* `ModalLogic.IsSerial`, `ModalLogic.IsEuclidean`: the frame conditions of D and 5.

## References

* [kripke-1963] — relational semantics
* [blackburn-derijke-venema-2001] — Chapter 3, frame definability
-/

@[expose] public section

namespace ModalLogic

open SetRel

/-! ### Box and diamond -/

section Operators

variable {W W' : Type*} (R : SetRel W' W) (p : W → Prop) (w : W')

/-- Necessity along `R` holds of `p` at `w` when `p` holds at every `R`-successor of `w`. -/
def Box : Prop := ∀ v, w ~[R] v → p v

/-- Possibility along `R` holds of `p` at `w` when `p` holds at some `R`-successor of `w`. -/
def Diamond : Prop := ∃ v, w ~[R] v ∧ p v

@[inherit_doc] scoped notation:max "□[" R "]" => Box R
@[inherit_doc] scoped notation:max "◇[" R "]" => Diamond R

variable {R p w}

theorem box_iff : □[R] p w ↔ ∀ v, w ~[R] v → p v := .rfl

theorem diamond_iff : ◇[R] p w ↔ ∃ v, w ~[R] v ∧ p v := .rfl

/-- Necessity on predicates is the mathlib core on sets. -/
theorem box_iff_mem_core : □[R] p w ↔ w ∈ R.core {v | p v} := .rfl

/-- Possibility on predicates is the mathlib preimage on sets. -/
theorem diamond_iff_mem_preimage : ◇[R] p w ↔ w ∈ R.preimage {v | p v} :=
  exists_congr fun _ ↦ and_comm

@[simp] theorem not_box : ¬ □[R] p w ↔ ◇[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_forall]

@[simp] theorem not_diamond : ¬ ◇[R] p w ↔ □[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_and]

variable (R) in
/-- Necessity distributes over conjunction ([hintikka-1962]'s
`a believes A and B ↔ a believes A and a believes B`). -/
theorem box_and (q : W → Prop) : □[R] (fun v ↦ p v ∧ q v) w ↔ □[R] p w ∧ □[R] q w := by
  simp only [Box, imp_and, forall_and]

variable (R) in
/-- Necessity along a union of relations is necessity along each. -/
theorem box_iUnion {ι : Sort*} (R : ι → SetRel W' W) : □[⋃ i, R i] p w ↔ ∀ i, □[R i] p w := by
  simp only [Box, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

/-- Necessity depends only on the worlds accessed, so two worlds accessing the same worlds
carry the same box. -/
theorem box_congr_left {w'' : W'} (h : ∀ v, w ~[R] v ↔ w'' ~[R] v) : □[R] p w ↔ □[R] p w'' :=
  forall_congr' fun v ↦ imp_congr_left (h v)

end Operators

/-! ### The Galois connection and normality -/

section Galois

variable {W W' : Type*} (R : SetRel W' W) {p q : W → Prop}

/-- `◇` along `R` is left adjoint to `□` along the converse relation, the characteristic
adjunction of relational modality. -/
theorem diamond_box_gc : GaloisConnection ◇[R] □[R.inv] :=
  fun _ _ ↦ ⟨fun h v hp w hwv ↦ h w ⟨v, hwv, hp⟩, fun h w ⟨v, hwv, hp⟩ ↦ h v hp w hwv⟩

theorem box_mono : Monotone □[R] := by
  simpa using (diamond_box_gc R.inv).monotone_u

theorem diamond_mono : Monotone ◇[R] :=
  (diamond_box_gc R).monotone_l

theorem box_inf : □[R] (p ⊓ q) = □[R] p ⊓ □[R] q := by
  simpa using (diamond_box_gc R.inv).u_inf

theorem diamond_sup : ◇[R] (p ⊔ q) = ◇[R] p ⊔ ◇[R] q :=
  (diamond_box_gc R).l_sup

/-- Necessitation: `□⊤ = ⊤`. -/
theorem box_top : □[R] ⊤ = ⊤ := by
  simpa using (diamond_box_gc R.inv).u_top

/-- **Conversion** (Prior's tense axiom `A ⊃ G P A`), the unit of the adjunction: over any
relation, `p ≤ □_{R⁻¹} ◇_R p`. -/
theorem le_box_inv_diamond (p : W → Prop) : p ≤ □[R.inv] (◇[R] p) :=
  (diamond_box_gc R).le_u_l p

end Galois

variable {W : Type*} (R : SetRel W W)

/-- Necessity along a composite relation is necessity nested in necessity. -/
theorem box_comp (S : SetRel W W) (p : W → Prop) : □[R ○ S] p = □[R] (□[S] p) :=
  funext fun _ ↦ propext ⟨fun h _ hv _ hu ↦ h _ ⟨_, hv, hu⟩, fun h _ ⟨_, hv, hu⟩ ↦ h _ hv _ hu⟩

/-- Possibility along a composite relation is possibility nested in possibility. -/
theorem diamond_comp (S : SetRel W W) (p : W → Prop) : ◇[R ○ S] p = ◇[R] (◇[S] p) :=
  funext fun _ ↦ propext ⟨fun ⟨u, ⟨v, hv, hu⟩, hp⟩ ↦ ⟨v, hv, u, hu, hp⟩,
    fun ⟨v, hv, u, hu, hp⟩ ↦ ⟨u, ⟨v, hv, hu⟩, hp⟩⟩

/-! ### Frame conditions -/

/-- `R` is **serial** if every world accesses at least one world. -/
class IsSerial : Prop where
  serial : ∀ w, ∃ v, w ~[R] v

/-- `R` is **Euclidean** if any two `R`-successors of a world access each other. -/
class IsEuclidean : Prop where
  eucl : ∀ w v u, w ~[R] v → w ~[R] u → v ~[R] u

variable {R}

instance : IsEuclidean (.univ : SetRel W W) := ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Reflexive relations are serial. -/
instance [R.IsRefl] : IsSerial R := ⟨fun w ↦ ⟨w, R.rfl⟩⟩

/-- A composite of serial relations is serial. -/
instance {S : SetRel W W} [IsSerial R] [IsSerial S] : IsSerial (R ○ S) where
  serial w := let ⟨v, hv⟩ := IsSerial.serial (R := R) w; let ⟨u, hu⟩ := IsSerial.serial (R := S) v
    ⟨u, v, hv, hu⟩

/-- Reflexive and Euclidean implies symmetric. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsSymm where
  symm w v h := IsEuclidean.eucl w v w h R.rfl

/-- Reflexive and Euclidean implies transitive. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsTrans where
  trans w v u hwv hvu := IsEuclidean.eucl v w u (IsEuclidean.eucl w v w hwv R.rfl) hvu

/-- Symmetric and transitive implies Euclidean. -/
instance [R.IsSymm] [R.IsTrans] : IsEuclidean R where
  eucl _ _ _ hwv hwu := R.trans (R.symm hwv) hwu

/-! ### Axiom correspondence -/

variable {p q : W → Prop} {w : W}

/-- Axiom **K**, `□(p → q) → □p → □q`, holds over any relation. -/
theorem box_K (hpq : □[R] (fun v ↦ p v → q v) w) (hp : □[R] p w) : □[R] q w :=
  fun v hwv ↦ hpq v hwv (hp v hwv)

/-- Axiom **T**, `□p → p`, holds over a reflexive relation. -/
theorem box_T [R.IsRefl] (h : □[R] p w) : p w := h w R.rfl

/-- Axiom **D**, `□p → ◇p`, holds over a serial relation. -/
theorem box_D [IsSerial R] (h : □[R] p w) : ◇[R] p w :=
  let ⟨v, hwv⟩ := IsSerial.serial (R := R) w; ⟨v, hwv, h v hwv⟩

/-- Necessity along `R` gives possibility along a relation sharing an `R`-successor of the
world, and `box_D` is the case `S = R`. -/
theorem diamond_of_box {S : SetRel W W} (h : ◇[R] (w ~[S] ·) w) (hp : □[R] p w) : ◇[S] p w :=
  let ⟨v, hR, hS⟩ := h; ⟨v, hS, hp v hR⟩

/-- Axiom **B**, `p → □◇p`, holds over a symmetric relation. -/
theorem box_B [R.IsSymm] (h : p w) : □[R] (◇[R] p) w := fun _ hwv ↦ ⟨w, R.symm hwv, h⟩

/-- Axiom **4**, `□p → □□p`, holds over a transitive relation. -/
theorem box_four [R.IsTrans] (h : □[R] p w) : □[R] (□[R] p) w :=
  fun _ hwv u hvu ↦ h u (R.trans hwv hvu)

/-- Axiom **5**, `◇p → □◇p`, holds over a Euclidean relation. -/
theorem box_five [IsEuclidean R] (h : ◇[R] p w) : □[R] (◇[R] p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ ⟨u, IsEuclidean.eucl w v u hwv hwu, hpu⟩

/-- Over a Euclidean relation what is possibly necessary is necessary, `◇□p → □p`. -/
theorem box_of_diamond_box [IsEuclidean R] (h : ◇[R] (□[R] p) w) : □[R] p w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ hpu v (IsEuclidean.eucl w u v hwu hwv)

/-- Over a serial transitive relation, `□p → ◇□p`. -/
theorem diamond_box_of_box [IsSerial R] [R.IsTrans] (h : □[R] p w) : ◇[R] (□[R] p) w :=
  box_D (box_four h)

/-! ### Frame definability

Each axiom, read as an inequality between operators on `W → Prop`, characterizes its frame
condition. -/

/-- **T** defines reflexivity. -/
theorem box_T_iff : Box R ≤ id ↔ R.IsRefl where
  mp h := ⟨fun w ↦ h (w ~[R] ·) w fun _ hv ↦ hv⟩
  mpr _ _ _ := box_T

/-- Axiom **T** for the diamond, that what holds is possible, defines reflexivity. -/
theorem diamond_T_iff : id ≤ Diamond R ↔ R.IsRefl where
  mp h := ⟨fun w ↦ match h (· = w) w rfl with | ⟨_, hv, rfl⟩ => hv⟩
  mpr hR _ w hp := ⟨w, hR.refl w, hp⟩

/-- **D** defines seriality. -/
theorem box_D_iff : Box R ≤ Diamond R ↔ IsSerial R where
  mp h := ⟨fun w ↦ let ⟨v, hv, _⟩ := h (fun _ ↦ True) w fun _ _ ↦ trivial; ⟨v, hv⟩⟩
  mpr _ _ _ := box_D

/-- **B** defines symmetry. -/
theorem box_B_iff : id ≤ Box R ∘ Diamond R ↔ R.IsSymm where
  mp h := ⟨fun w v hwv ↦ match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩
  mpr _ _ _ := box_B

/-- **4** defines transitivity. -/
theorem box_four_iff : Box R ≤ Box R ∘ Box R ↔ R.IsTrans where
  mp h := ⟨fun w _ _ hwv hvu ↦ h (w ~[R] ·) w (fun _ hv ↦ hv) _ hwv _ hvu⟩
  mpr _ _ _ := box_four

/-- **5** defines the Euclidean property. -/
theorem box_five_iff : Diamond R ≤ Box R ∘ Diamond R ↔ IsEuclidean R where
  mp h := ⟨fun w v u hwv hwu ↦ match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩
  mpr _ _ _ := box_five

/-! ### Seriality and functionality at a world

Excluded middle and non-contradiction for necessity at a world, read for every prejacent, each
define a condition on the successors of the world, and Negation Swap defines their conjunction:
`□p ∨ □¬p` holds for every `p` iff the world sees at most one world (Alt₁), `¬(□p ∧ □¬p)` iff it
sees at least one (D), and `□¬p ↔ ¬□p` iff it sees exactly one. For possibility the two
conditions trade places. A relation satisfying Negation
Swap at every world is the graph of a function, and necessity along a graph is precomposition
with the function. -/

section Functional

variable {W W' : Type*} {R : SetRel W' W} {w : W'}

/-- Axiom **Alt₁**, `◇p → □p` for every `p`, holds at `w` iff `w` sees at most one world. -/
theorem diamond_le_box_at_iff :
    (∀ p : W → Prop, ◇[R] p w → □[R] p w) ↔ ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u where
  mp h v hv _ hu := (h (· = v) ⟨v, hv, rfl⟩ _ hu).symm
  mpr h _ := fun ⟨_, hu, hpu⟩ _ hv ↦ h hu hv ▸ hpu

/-- **Alt₁** defines partial functionality. -/
theorem diamond_le_box_iff :
    Diamond R ≤ Box R ↔ ∀ w ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u :=
  ⟨fun h _ ↦ diamond_le_box_at_iff.1 fun p ↦ h p _,
    fun h p _ ↦ diamond_le_box_at_iff.2 (h _) p⟩

/-- The excluded middle for every `p` at `w`, `□p ∨ □¬p`, holds iff `w` sees at most one
world. -/
theorem box_or_box_not_at_iff :
    (∀ p : W → Prop, □[R] p w ∨ □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← diamond_le_box_at_iff]
  refine forall_congr' fun p ↦ ?_
  rw [← not_diamond, or_comm, or_iff_not_imp_left, not_not]

/-- The neg-raising inference for every `p` at `w`, `¬□p → □¬p`, holds iff `w` sees at most
one world. -/
theorem box_not_of_not_box_at_iff :
    (∀ p : W → Prop, ¬ □[R] p w → □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← box_or_box_not_at_iff]
  exact forall_congr' fun p ↦ (or_iff_not_imp_left).symm

/-- Non-contradiction for every `p` at `w`, `¬(□p ∧ □¬p)`, holds iff `w` sees some world. -/
theorem not_box_and_box_not_at_iff :
    (∀ p : W → Prop, ¬ (□[R] p w ∧ □[R] (fun v ↦ ¬ p v) w)) ↔ ∃ v, w ~[R] v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ p ⟨h₁, h₂⟩ ↦ h₂ v hv (h₁ v hv)⟩
  by_contra hn
  exact h (fun _ ↦ True) ⟨fun _ _ ↦ trivial, fun v hv _ ↦ hn ⟨v, hv⟩⟩

/-- **Negation Swap** for every `p` at `w`, `□¬p ↔ ¬□p`, holds iff `w` sees exactly one world. -/
theorem box_not_iff_not_box_at_iff :
    (∀ p : W → Prop, □[R] (fun v ↦ ¬ p v) w ↔ ¬ □[R] p w) ↔ ∃! v, w ~[R] v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := not_box_and_box_not_at_iff.1 fun p ⟨h₁, h₂⟩ ↦ (h p).1 h₂ h₁
    exact ⟨v, hv, fun u hu ↦ box_or_box_not_at_iff.1 (fun p ↦ (em _).imp_right (h p).2) hu hv⟩
  · rintro ⟨v, hv, hu⟩ p
    have key (q : W → Prop) : □[R] q w ↔ q v := ⟨fun h ↦ h v hv, fun hq u hwu ↦ hu u hwu ▸ hq⟩
    rw [key, key]

/-- The excluded middle for possibility, `◇p ∨ ◇¬p` for every `p` at `w`, holds iff `w` sees
some world. -/
theorem diamond_or_diamond_not_at_iff :
    (∀ p : W → Prop, ◇[R] p w ∨ ◇[R] (fun v ↦ ¬ p v) w) ↔ ∃ v, w ~[R] v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ p ↦ ?_⟩
  · rcases h fun _ ↦ True with ⟨v, hv, -⟩ | ⟨v, hv, -⟩ <;> exact ⟨v, hv⟩
  · by_cases hp : p v
    exacts [.inl ⟨v, hv, hp⟩, .inr ⟨v, hv, hp⟩]

/-- Non-contradiction for possibility, `¬(◇p ∧ ◇¬p)` for every `p` at `w`, holds iff `w` sees
at most one world. -/
theorem not_diamond_and_diamond_not_at_iff :
    (∀ p : W → Prop, ¬ (◇[R] p w ∧ ◇[R] (fun v ↦ ¬ p v) w)) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← box_or_box_not_at_iff]
  refine forall_congr' fun p ↦ ?_
  rw [not_and_or, not_diamond, not_diamond, or_comm]
  simp only [not_not]

/-- Necessity along the graph of a function is precomposition with the function. -/
@[simp] theorem box_graph (f : W' → W) (p : W → Prop) : □[Function.graph f] p = p ∘ f :=
  funext fun _ ↦ propext ⟨fun h ↦ h _ rfl, fun h _ hv ↦ hv ▸ h⟩

/-- Negation Swap at every world holds iff the relation is the graph of a function. -/
theorem box_compl_eq_iff :
    (∀ p : W → Prop, □[R] pᶜ = (□[R] p)ᶜ) ↔ ∃ f : W' → W, Function.graph f = R := by
  have : (∀ p : W → Prop, □[R] pᶜ = (□[R] p)ᶜ) ↔ ∀ w, ∃! v, w ~[R] v := by
    simp only [← box_not_iff_not_box_at_iff, funext_iff, Pi.compl_apply, compl_iff_not,
      eq_iff_iff]
    exact forall_comm
  rw [this, ← R.exists_graph_eq_iff]
  exact ⟨fun ⟨f, hf, _⟩ ↦ ⟨f, hf⟩,
    fun ⟨f, hf⟩ ↦ ⟨f, hf, fun _ hg ↦ Function.graph_injective (hg.trans hf.symm)⟩⟩

end Functional

end ModalLogic
