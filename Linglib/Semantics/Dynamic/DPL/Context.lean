module

public import Linglib.Core.ModelTheory.Semantics
public import Linglib.Semantics.Dynamic.DPL.Semantics
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.Tauto

/-!
# Contexts for dynamic predicate logic

This file defines Visser's contexts, which type the relations of dynamic predicate logic by the
variables they touch. A context is a triple of finite sets of variables: the inputs `I` a
relation reads, the blocks `B` at which it cuts the link between input and output value, and
the outputs `O` it constrains, with `I` and `O` agreeing off `B`. A relation has a context when
it changes only the blocks and membership in it is invariant under agreement on the inputs, on
the outputs, and off the blocks. Contexts compose as relations do, so every formula gets a
context by recursion, and the formula's interpretation has it.

## Main definitions

* `DPL.Context`: contexts, a monoid under composition, partially ordered by information.
* `DPL.Context.test`, `DPL.Context.reset`: the contexts of a condition and of a random reset.
* `DPL.HasContext`: the relations a context types.
* `DPL.Formula.context`: the context of a formula.

## Main results

* `DPL.HasContext.mono`: a relation a context types is typed by every less informative context.
* `DPL.HasContext.patch`, `DPL.HasContext.patch_unique`: over an input agreeing on the inputs,
  a typed relation has exactly one output agreeing with a given output on the blocks.
* `DPL.HasContext.dependsOn_dom`: truth depends only on the inputs.
* `DPL.HasContext.comp`: composition is typed by the product of the contexts.
* `DPL.Formula.hasContext_eval`: a formula's interpretation has its context, whose inputs are
  the free variables and whose blocks are the active quantifier variables.
* `DPL.Formula.IsScopeBound.mem_dom_eval_iff`: on the scope-bound formulas dynamic truth is
  first-order satisfaction.

## Implementation notes

Coherence is stored in membership form, so that `Context V` needs no decidable equality; the
paper's `I ∪ B = O ∪ B` is `Context.union_blocks`. The patched output of Lemma 3.7 is
`Finset.piecewise` at the blocks. The only named contexts are the unit and the two generators,
the test at a set and the reset at a variable: the paper's implication context `c → d` is the
test at the inputs of `c * d`. The paper's language has neither disjunction nor primitive
negation and universal quantification; their contexts are those the paper's definitions of them
yield, tests at the inputs. The context of a formula is not always the least one its
interpretation has: `x ≐ x` reads `x` and denotes the identity.

## References

* [visser-1998]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

open DynamicSemantics Update SetRel

namespace DPL

variable {V E : Type*}

/-! ### Contexts (Definition 3.1) -/

/-- A DPL-context (Definition 3.1) has an input set `I` of variables the incoming assignment
is read at, a block set `B` of variables whose input-output link is cut, and an output set `O`
of variables the outgoing assignment is constrained at, with `I` and `O` agreeing off `B` (the
paper's `I ∪ B = O ∪ B`, `Context.union_blocks`). -/
@[ext] structure Context (V : Type*) where
  /-- The input set. -/
  I : Finset V
  /-- The block set is the barrier between past and future. -/
  B : Finset V
  /-- The output set. -/
  O : Finset V
  /-- Off the blocks, inputs and outputs coincide. -/
  coh : ∀ ⦃v⦄, v ∉ B → (v ∈ I ↔ v ∈ O)

namespace Context

instance : One (Context V) := ⟨⟨∅, ∅, ∅, fun _ _ ↦ Iff.rfl⟩⟩

@[simp] theorem I_one : (1 : Context V).I = ∅ := rfl
@[simp] theorem B_one : (1 : Context V).B = ∅ := rfl
@[simp] theorem O_one : (1 : Context V).O = ∅ := rfl

/-- The test context at `s` reads and writes `s` and blocks nothing, the context of the
conditions depending only on `s` (`hasContext_test_iff`). -/
def test (s : Finset V) : Context V := ⟨s, ∅, s, fun _ _ ↦ Iff.rfl⟩

@[simp] theorem I_test (s : Finset V) : (test s).I = s := rfl
@[simp] theorem B_test (s : Finset V) : (test s).B = ∅ := rfl
@[simp] theorem O_test (s : Finset V) : (test s).O = s := rfl

/-- The reset context at `x`, Definition 3.12's `c_{∃v}`, reads nothing, constrains no output,
and blocks `x`. -/
def reset (x : V) : Context V := ⟨∅, {x}, ∅, fun _ _ ↦ Iff.rfl⟩

@[simp] theorem I_reset (x : V) : (reset x).I = ∅ := rfl
@[simp] theorem B_reset (x : V) : (reset x).B = {x} := rfl
@[simp] theorem O_reset (x : V) : (reset x).O = ∅ := rfl

variable [DecidableEq V]

private theorem coh_mem (c : Context V) {v : V} : v ∈ c.I ∪ c.B ↔ v ∈ c.O ∪ c.B := by
  have := c.coh (v := v)
  grind

theorem union_blocks (c : Context V) : c.I ∪ c.B = c.O ∪ c.B :=
  Finset.ext fun _ ↦ c.coh_mem

/-- Contexts compose by `⟨I,B,O⟩ * ⟨I',B',O'⟩ = ⟨I ∪ (I'∖B), B ∪ B', (O∖B') ∪ O'⟩`
(Definition 3.1). -/
instance : Mul (Context V) where
  mul c d :=
    { I := c.I ∪ (d.I \ c.B)
      B := c.B ∪ d.B
      O := (c.O \ d.B) ∪ d.O
      coh := fun v hv ↦ by
        have := c.coh (v := v)
        have := d.coh (v := v)
        grind }

@[simp] theorem I_mul (c d : Context V) : (c * d).I = c.I ∪ (d.I \ c.B) := rfl
@[simp] theorem B_mul (c d : Context V) : (c * d).B = c.B ∪ d.B := rfl
@[simp] theorem O_mul (c d : Context V) : (c * d).O = (c.O \ d.B) ∪ d.O := rfl
/-- The contexts form a monoid (Theorem 3.3). -/
instance : Monoid (Context V) where
  mul_assoc c d e := by
    ext v <;> simp only [I_mul, B_mul, O_mul, Finset.mem_union,
      Finset.mem_sdiff] <;> tauto
  one_mul c := by ext v <;> simp
  mul_one c := by ext v <;> simp

/-- The information order on contexts (Definition 3.1): `c ≤ d` when `d` reads, writes and
blocks at least what `c` does, its new blocks among the variables it both reads and writes. The
smaller context is the more informative, typing fewer relations (`HasContext.mono`). -/
instance : LE (Context V) :=
  ⟨fun c d ↦ c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O)⟩

theorem le_def {c d : Context V} :
    c ≤ d ↔ c.I ⊆ d.I ∧ c.O ⊆ d.O ∧ c.B ⊆ d.B ∧ d.B ⊆ c.B ∪ (d.I ∩ d.O) :=
  Iff.rfl

instance : DecidableLE (Context V) := fun _ _ ↦ decidable_of_iff' _ le_def

/-- The information order is a partial order (Theorem 3.3). -/
instance : PartialOrder (Context V) where
  le := (· ≤ ·)
  le_refl c := ⟨subset_rfl, subset_rfl, subset_rfl, Finset.subset_union_left⟩
  le_trans c d e h h' := by grind [le_def]
  le_antisymm c d h h' := by
    obtain ⟨hI, hO, hB, -⟩ := h
    obtain ⟨hI', hO', hB', -⟩ := h'
    exact Context.ext (hI.antisymm hI') (hB.antisymm hB') (hO.antisymm hO')

end Context

/-! ### c-relations (Definition 3.4) -/

/-- A context `c` is a context for `R` (Definition 3.4) if `R` reads its input only at `c.I`,
constrains its output only at `c.O`, and changes values only at `c.B`. -/
structure HasContext (R : Update (V → E)) (c : Context V) : Prop where
  /-- Only blocked variables change. -/
  blocks : ∀ ⦃f g⦄, f ~[R] g → Set.EqOn f g (↑c.B)ᶜ
  /-- Membership is invariant under input agreement on `I`, output
  agreement on `O`, and preservation off `B`. -/
  stable : ∀ ⦃f f' g g'⦄, f ~[R] g → Set.EqOn f' f ↑c.I →
    Set.EqOn g g' ↑c.O → Set.EqOn f' g' (↑c.B)ᶜ → f' ~[R] g'

/-- A condition is typed by the test context at `s` exactly when it is an ⟨s⟩-condition of
Definition 2.2, depending only on `s` (noted after Definition 3.4). -/
theorem hasContext_test_iff {s : Finset V} {p : Set (V → E)} :
    HasContext (test p) (Context.test s) ↔ DependsOn (· ∈ p) (↑s : Set V) := by
  refine ⟨fun h ↦ ?_, fun hp ↦ ⟨fun f g hR v _ ↦ congrFun hR.1 v,
    fun f f' g g' hR hI hO hB ↦ ⟨funext fun v ↦ hB (by simp),
      (hp fun _ hv ↦ hO hv).to_iff.mp (hR.1 ▸ hR.2)⟩⟩⟩
  have key : ∀ ⦃f f' : V → E⦄, Set.EqOn f' f ↑s → f ∈ p → f' ∈ p :=
    fun f f' hs hf ↦ (h.stable ⟨rfl, hf⟩ hs hs.symm (Set.eqOn_refl _ _)).2
  exact fun f f' hs ↦ propext ⟨key fun v hv ↦ (hs v hv).symm, key fun v hv ↦ hs v hv⟩

theorem hasContext_id : HasContext (.id : Update (V → E)) 1 :=
  test_univ (S := V → E) ▸ hasContext_test_iff.mpr fun _ _ _ ↦ rfl

variable [DecidableEq V]

namespace HasContext

variable {c d : Context V} {R S : Update (V → E)} {f f' g g' : V → E}

/-! ### The order is sound for the typing (Theorem 3.5) -/

/-- Larger contexts type more relations (Theorem 3.5(1)), so if `c ≤ d` and `R` is a
`c`-relation, then `R` is a `d`-relation. -/
theorem mono (h : HasContext R c) (hcd : c ≤ d) : HasContext R d := by
  obtain ⟨hI, hO, hB, hBio⟩ := hcd
  refine ⟨fun f g hR ↦ (h.blocks hR).mono
      (Set.compl_subset_compl.mpr (Finset.coe_subset.mpr hB)),
    fun f f' g g' hR hI' hO' hB' ↦ h.stable hR
      (hI'.mono (Finset.coe_subset.mpr hI))
      (hO'.mono (Finset.coe_subset.mpr hO)) (fun v hv ↦ ?_)⟩
  have hb := h.blocks hR
  grind [Set.EqOn]

/-! ### The unique-output lemma (Lemma 3.7) -/

/-- The patch agrees with `g` at the blocks and wherever the inputs agree (Lemma 3.7,
transfer). -/
theorem patch_eqOn {J : Set V} (h : HasContext R c) (hR : f ~[R] g)
    (hJ : Set.EqOn f' f J) :
    Set.EqOn (c.B.piecewise g f') g (J ∪ ↑c.B) := by
  intro v hv
  have hb := h.blocks hR
  grind [Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-- If `f'` agrees with `f` on the inputs and `f R g`, then `R` relates `f'` to its patch by `g` at
the blocks (Lemma 3.7, existence). -/
theorem patch (h : HasContext R c) (hI : Set.EqOn f' f ↑c.I)
    (hR : f ~[R] g) : f' ~[R] c.B.piecewise g f' :=
  h.stable hR hI
    ((h.patch_eqOn hR hI).mono (fun v hv ↦ by
      have hc := c.coh_mem (v := v)
      grind)).symm
    (fun v hv ↦ (c.B.piecewise_eq_of_notMem _ _ hv).symm)

/-- The patch is the only output over `f'` agreeing with `g` on the blocks (Lemma 3.7,
uniqueness). -/
theorem patch_unique (h : HasContext R c) (hR : f' ~[R] g')
    (hB : Set.EqOn g' g ↑c.B) : g' = c.B.piecewise g f' := by
  have hb := h.blocks hR
  funext v
  grind [Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

/-! ### Composition and implication typing (Theorems 3.8–3.9) -/

/-- The composition of a `c`-relation and a `d`-relation is a `c * d`-relation (Theorem 3.8).
-/
theorem comp (hR : HasContext R c) (hS : HasContext S d) :
    HasContext (R ○ S) (c * d) where
  blocks := by
    rintro f g ⟨k, hfk, hkg⟩ v hv
    rw [Context.B_mul, Finset.coe_union, Set.compl_union] at hv
    exact (hR.blocks hfk hv.1).trans (hS.blocks hkg hv.2)
  stable := by
    rintro f f' g g' ⟨k, hfk, hkg⟩ hI hO hB
    -- Patch the intermediate assignment: keep it at `c.O ∪ d.I`, take
    -- the new output at the old blocks, the new input elsewhere.
    refine ⟨(c.O ∪ d.I).piecewise k (c.B.piecewise g' f'),
      hR.stable hfk (hI.mono (Finset.coe_subset.mpr Finset.subset_union_left))
        (fun v hv ↦ ((c.O ∪ d.I).piecewise_eq_of_mem _ _
          (Finset.mem_union_left _ hv)).symm) ?_,
      hS.stable hkg
        (fun v hv ↦ (c.O ∪ d.I).piecewise_eq_of_mem _ _
          (Finset.mem_union_right _ hv))
        (hO.mono (Finset.coe_subset.mpr Finset.subset_union_right)) ?_⟩
    all_goals
      intro v hv
      have hbR := hR.blocks hfk
      have hbS := hS.blocks hkg
      have hc := c.coh_mem (v := v)
      have hd := d.coh_mem (v := v)
      grind [Set.EqOn, Finset.piecewise_eq_of_mem,
        Finset.piecewise_eq_of_notMem, Context.I_mul, Context.O_mul,
        Context.B_mul]

end HasContext

/-! ### The DPL generators, typed -/

/-- The reset is typed at `⟨∅, {x}, ∅⟩`, Definition 3.12's `c_{∃v}`, which reads nothing,
constrains no output, and blocks `x`. -/
theorem hasContext_randomAssign (x : V) :
    HasContext (randomAssign (S := V → E) x) (Context.reset x) :=
  ⟨fun f g hR v hv ↦ mem_randomAssign_iff_eqOn.mp hR (by simpa using hv),
   fun f f' g g' _ _ _ hB ↦ mem_randomAssign_iff_eqOn.mpr fun v hv ↦ hB (by simpa using hv)⟩

/-! ### Truth depends on the inputs -/

namespace HasContext

variable {c d : Context V} {R S : Update (V → E)} {f g : V → E}

/-- The domain of a `c`-relation depends only on the inputs (noted after Lemma 3.7). -/
theorem dependsOn_dom (h : HasContext R c) : DependsOn (· ∈ R.dom) (↑c.I : Set V) := by
  have key : ∀ ⦃f f' : V → E⦄, Set.EqOn f' f ↑c.I → f ∈ R.dom → f' ∈ R.dom :=
    fun _ _ hI ⟨_, hR⟩ ↦ ⟨_, h.patch hI hR⟩
  exact fun f f' hI ↦ propext ⟨key fun v hv ↦ (hI v hv).symm, key fun v hv ↦ hI v hv⟩

theorem mem_dom_iff (hR : HasContext R c) (hS : HasContext S d) (hd : Disjoint c.B d.I)
    (hfg : f ~[R] g) : f ∈ S.dom ↔ g ∈ S.dom :=
  (hS.dependsOn_dom fun _ hv ↦ hR.blocks hfg (Finset.disjoint_right.mp hd hv)).to_iff

/-- A relation that blocks none of the inputs of another commutes with its truth, so the
sequence is true where both are. -/
theorem dom_comp (hR : HasContext R c) (hS : HasContext S d) (hd : Disjoint c.B d.I) :
    (R ○ S).dom = R.dom ∩ S.dom :=
  Set.ext fun _ ↦
    ⟨fun ⟨_, k, hk, hS'⟩ ↦ ⟨⟨k, hk⟩, (hR.mem_dom_iff hS hd hk).mpr ⟨_, hS'⟩⟩,
      fun ⟨⟨k, hk⟩, hf⟩ ↦
        let ⟨j, hj⟩ := (hR.mem_dom_iff hS hd hk).mp hf
        ⟨j, k, hk, hj⟩⟩

/-- The negation of a `c`-relation is a test at its inputs. -/
theorem neg (h : HasContext R c) : HasContext (test (Update.neg R)) (Context.test c.I) :=
  hasContext_test_iff.mpr fun _ _ hI ↦ congrArg Not (h.dependsOn_dom hI)

/-- The DPL implication of a `c`-relation and a `d`-relation is typed by the paper's `c → d`, the
test at the inputs of `c * d` (Theorem 3.9), by the typing of composition and negation. -/
theorem impl (hR : HasContext R c) (hS : HasContext S d) :
    HasContext (test (Update.impl R S)) (Context.test (c * d).I) := by
  rw [impl_eq_neg_comp_test_neg]
  exact (hR.comp hS.neg).neg

/-- The disjunction of a `c`-relation and a `d`-relation is a test at their inputs. -/
theorem disj (hR : HasContext R c) (hS : HasContext S d) :
    HasContext (test (Update.disj R S)) (Context.test (c.I ∪ d.I)) :=
  hasContext_test_iff.mpr fun _ _ hI ↦ by
    have h₁ := hR.dependsOn_dom fun v hv ↦ hI v (Finset.coe_subset.mpr Finset.subset_union_left hv)
    have h₂ := hS.dependsOn_dom fun v hv ↦ hI v (Finset.coe_subset.mpr Finset.subset_union_right hv)
    exact congrArg₂ Or h₁ h₂

end HasContext

/-! ### The context of a formula (Definition 3.12, Theorem 3.13) -/

open FirstOrder

namespace Formula

variable {L : Language} (M : Type*) [L.Structure M]

/-- The context of a formula (Definition 3.12). The paper's language has no disjunction and
defines negation and the universal; they are typed here as the definitions would be. -/
def context : Formula L V → Context V
  | top => 1
  | rel R ts => .test (rel R ts).fv
  | equal t₁ t₂ => .test (equal t₁ t₂).fv
  | neg φ => .test (context φ).I
  | conj φ ψ => context φ * context ψ
  | disj φ ψ => .test ((context φ).I ∪ (context ψ).I)
  | imp φ ψ => .test (context φ * context ψ).I
  | ex x φ => .reset x * context φ
  | all x φ => .test (.reset x * context φ).I

/-- The blocks of a formula's context are its active quantifier variables. -/
theorem context_B (φ : Formula L V) : φ.context.B = φ.aqv := by
  induction φ <;> simp_all [context, aqv]

/-- The inputs of a formula's context are its free variables. -/
theorem context_I (φ : Formula L V) : φ.context.I = φ.fv := by
  induction φ <;> simp_all [context, fv, context_B, Finset.sdiff_singleton_eq_erase]

/-- The interpretation of a formula is typed by its context (Theorem 3.13). -/
theorem hasContext_eval (φ : Formula L V) : HasContext (φ.eval M) φ.context := by
  induction φ with
  | top => exact hasContext_id
  | rel R ts =>
    refine hasContext_test_iff.mpr fun f f' h ↦ ?_
    have : (fun i ↦ (ts i).realize f) = fun i ↦ (ts i).realize f' := funext fun i ↦
      (ts i).dependsOn_realize fun v hv ↦ h v <| by
        simpa [fv] using ⟨i, hv⟩
    simp only [Set.mem_ofPred_eq, this]
  | equal t₁ t₂ =>
    refine hasContext_test_iff.mpr fun f f' h ↦ ?_
    have h₁ := t₁.dependsOn_realize (M := M) fun v hv ↦ h v (by simp [fv, hv])
    have h₂ := t₂.dependsOn_realize (M := M) fun v hv ↦ h v (by simp [fv, hv])
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    rw [h₁, h₂]
  | neg φ ih => exact ih.neg
  | conj φ ψ ihφ ihψ => exact ihφ.comp ihψ
  | disj φ ψ ihφ ihψ => exact ihφ.disj ihψ
  | imp φ ψ ihφ ihψ => exact ihφ.impl ihψ
  | ex x φ ih => exact (hasContext_randomAssign x).comp ih
  | all x φ ih => exact (hasContext_randomAssign x).impl ih

/-- A scope-bound formula is true under the dynamic interpretation exactly where it is
satisfied as a first-order formula ([groenendijk-stokhof-1991]'s Fact 19). -/
theorem IsScopeBound.mem_dom_eval_iff {φ : Formula L V} (h : φ.IsScopeBound) {g : V → M} :
    g ∈ (φ.eval M).dom ↔ φ.toFormula.Realize g := by
  induction φ generalizing g with
  | top => exact iff_of_true ⟨g, rfl⟩ (by simp [toFormula])
  | rel R ts => simp [toFormula]
  | equal t₁ t₂ => simp [toFormula]
  | neg φ ih => simp [toFormula, neg_eq_compl_dom, ih h]
  | conj φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ, hd⟩ := h
    rw [eval_conj, (φ.hasContext_eval M).dom_comp (ψ.hasContext_eval M)
      (by rwa [context_B, context_I])]
    simp [toFormula, ihφ hφ, ihψ hψ]
  | disj φ ψ ihφ ihψ => simp [toFormula, disj_eq_dom_union_dom, ihφ h.1, ihψ h.2]
  | imp φ ψ ihφ ihψ =>
    obtain ⟨hφ, hψ, hd⟩ := h
    rw [eval_imp, dom_test, impl_eq_neg_comp_test_neg, neg_eq_compl_dom,
      (φ.hasContext_eval M).dom_comp (ψ.hasContext_eval M).neg (by rwa [context_B, context_I]),
      dom_test, neg_eq_compl_dom]
    simp [toFormula, ihφ hφ, ihψ hψ]
  | ex x φ ih => simp [toFormula, dom_dexists, ih h]
  | all x φ ih => simp [toFormula, mem_dforall, ih h]

end Formula

end DPL
