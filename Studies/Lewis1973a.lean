module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Semantics.Conditionals.Basic

/-!
# Lewis (1973a): Causation

Lewis analyses causation through counterfactuals over comparative similarity: an event depends
causally on a distinct event when whether the one occurs depends counterfactually on whether the
other does, and causation is the ancestral of causal dependence among actual events. On a
deterministic causal model, every similarity that favours worlds keeping to the actual course of
events longer and violating fewer laws, however it weighs the two, makes [the counterfactual of
setting a variable the intervention](##mem_variablyStrictImp_iff_solve_update), which [does not
backtrack](##mem_variablyStrictImp_similarity_of_not_reflTransGen). Among actual events [causal
dependence is then the but-for test](##mem_dependsCausally_iff_of_actual), and the analysis
separates [a cause from its epiphenomena](##Epiphenomena.epiphenomena) and [a preempting cause from
the cause it preempts](##Preemption.preemption).

## Implementation notes

A world is an assignment to the variables of the model, the actual world of a context is its
solution, and the counterfactual is evaluated at the context. Time is rank in the causal order, the
model having no other temporal structure, so the direction of counterfactual dependence is read off
the causal graph rather than an independent direction of time, and in an acyclic model [no event
causes one of its causes](##Cause.asymm). The equations of variables without parents
record the circumstances the context fixes, and a world departing from them violates them.
`similarity` weighs late divergence before violations, one resolution of the weighting the paper
leaves open. An event is a Boolean variable, occurring where it is true. That `c₂` would have
caused `e` had `c₁` been absent is read in the context without `c₁`, which is the counterfactual
world since `c₁` has no parents. Nomic dependence and the regularity analysis are not formalized.

## TODO

* The barometer: counterfactual dependence between families of many alternatives, and its
  irreversibility.

## References

* [lewis-1973a]
* [lewis-1973b]
-/

@[expose] public section

namespace Lewis1973a

open CausalModel Conditional Relation

/-! ### Counterfactual and causal dependence -/

section Dependence

variable {I W ι : Type*} (access : I → Set W) (ord : I → Preorder W)

/-- The `C`'s depend counterfactually on the `A`'s at `i` (p. 561) when every counterfactual
`A k □→ C k` between corresponding propositions holds at `i`. The paper presupposes that each
family consists of possible propositions no two of which are compossible. -/
def dependsCounterfactually (A C : ι → Set W) : Set I :=
  ⋂ k, variablyStrictImp access ord (A k) (C k)

/-- For the propositions `c` and `e` that two distinct events occur, `e` depends causally on `c`
when the family `e`, `eᶜ` depends counterfactually on the family `c`, `cᶜ`: whether the
one event occurs depends on whether the other does (pp. 562–563). -/
def dependsCausally (c e : Set W) : Set I :=
  dependsCounterfactually access ord ![c, cᶜ] ![e, eᶜ]

variable {access ord} {i : I} {c e : Set W}

-- p. 563
theorem mem_dependsCausally :
    i ∈ dependsCausally access ord c e ↔
      i ∈ variablyStrictImp access ord c e ∧ i ∈ variablyStrictImp access ord cᶜ eᶜ := by
  simp [dependsCausally, dependsCounterfactually, Fin.forall_fin_two]

end Dependence

/-! ### Comparative similarity on a causal model -/

section Similarity

variable {U V : Type*} {α : V → Type*} [∀ v, Nonempty (α v)] (M : CausalModel U V α)
  [M.IsAcyclic] {u : U} {x : ∀ v, α v} {c : V}

/-- The time at which the world `x` departs from the actual course of events in the context `u`:
the least rank in the causal order of a variable where `x` differs from the actual world, and
`⊤` where it differs nowhere. -/
noncomputable def divergence (u : U) (x : ∀ v, α v) : WithTop Ordinal :=
  ⨅ (v) (_ : x v ≠ M.solve ⊥ u v), ↑(WellFounded.rank M.graph.Adj v)

/-- The variables whose law, the structural equation, the world `x` violates in the context
`u`. -/
def violations (u : U) (x : ∀ v, α v) : Set V :=
  {v | x v ≠ M.eqn v u x}

/-- The two respects in which a world resembles the actual world of the context `u`: how late it
departs from the actual course of events, and how many laws it violates. In the product order a
world scores lower than another when it is no worse in either respect and better in one. -/
noncomputable def score (u : U) (x : ∀ v, α v) : (WithTop Ordinal)ᵒᵈ × ℕ∞ :=
  (OrderDual.toDual (divergence M u x), (violations M u x).encard)

/-- A comparative similarity to the actual world of the context `u`: the later a world departs
from the actual course of events the closer it is, and of two worlds that depart at the same time
the one violating fewer laws is closer. -/
noncomputable abbrev similarity (u : U) : Preorder (∀ v, α v) :=
  Preorder.lift (toLex ∘ score M u)

variable {M}

theorem divergence_eq_top_iff : divergence M u x = ⊤ ↔ x = M.solve ⊥ u := by
  simp [divergence, funext_iff]

@[simp]
theorem divergence_solve_bot : divergence M u (M.solve ⊥ u) = ⊤ :=
  divergence_eq_top_iff.2 rfl

theorem divergence_le {v : V} (hv : x v ≠ M.solve ⊥ u v) :
    divergence M u x ≤ WellFounded.rank M.graph.Adj v :=
  iInf₂_le v hv

-- p. 567
theorem violations_eq_empty_iff : violations M u x = ∅ ↔ x = M.solve ⊥ u := by
  rw [Set.eq_empty_iff_forall_notMem, ← isFixedPt_iff_eq_solve, Function.IsFixedPt, funext_iff]
  simp [violations, step_apply, eq_comm]

-- p. 567
theorem mem_violations_of_le_divergence (hx : x c ≠ M.solve ⊥ u c)
    (h : ↑(WellFounded.rank M.graph.Adj c) ≤ divergence M u x) : c ∈ violations M u x := by
  have hpar : ∀ w ∈ {w | M.graph.Adj w c}, x w = M.solve ⊥ u w := fun w hw ↦
    by_contra fun hne ↦ (divergence_le hne).not_gt
      (WithTop.coe_lt_coe.2 (WellFounded.rank_lt_of_rel hw) |>.trans_le h)
  change x c ≠ M.eqn c u x
  rwa [M.dependsOn_eqn c u hpar, ← solve_of_eq_bot rfl u]

private theorem rank_le_of_reflTransGen {β : Type*} {r : β → β → Prop} [WellFounded r]
    {a b : β} (h : ReflTransGen r a b) : WellFounded.rank r a ≤ WellFounded.rank r b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans (WellFounded.rank_lt_of_rel h).le

theorem score_solve_bot_lt (hx : x ≠ M.solve ⊥ u) : score M u (M.solve ⊥ u) < score M u x := by
  refine Prod.lt_iff.2 (.inl ⟨?_, ?_⟩)
  · rw [score, score, OrderDual.toDual_lt_toDual, divergence_solve_bot]
    exact lt_top_iff_ne_top.2 (mt divergence_eq_top_iff.1 hx)
  · simp [score, violations_eq_empty_iff.2 rfl]

-- p. 560
theorem similarity_lt_of_ne (hx : x ≠ M.solve ⊥ u) : (similarity M u).lt (M.solve ⊥ u) x :=
  Prod.Lex.toLex_strictMono (score_solve_bot_lt hx)

-- p. 560
theorem similarity_total : Std.Total (similarity M u).le :=
  ⟨fun x y ↦ le_total (toLex (score M u x)) (toLex (score M u y))⟩

variable [DecidableEq V] {b : α c}

-- A world that sets `c` to `b` and obeys every other law is the intervention.
private theorem eq_solve_of_violations_subset (hx : x c = b) (h : violations M u x ⊆ {c}) :
    x = M.solve [c ← b] u :=
  eq_solve_of_isFixedPt <| funext fun v ↦ by
    rw [step_apply]
    rcases eq_or_ne v c with rfl | hv
    · rw [Function.update_self, Flat.unbotD_coe, hx]
    · rw [Function.update_of_ne hv]
      exact (not_not.1 fun hn ↦ hv (h hn)).symm

private theorem divergence_solve_update (hb : b ≠ M.solve ⊥ u c) :
    divergence M u (M.solve [c ← b] u) = WellFounded.rank M.graph.Adj c := by
  refine le_antisymm (divergence_le (by rwa [solve_update_self])) (le_iInf₂ fun v hv ↦ ?_)
  refine WithTop.coe_le_coe.2 (rank_le_of_reflTransGen (by_contra fun h ↦ hv ?_))
  exact solve_update_of_not_reflTransGen h ⊥ _ u

private theorem violations_solve_update (hb : b ≠ M.solve ⊥ u c) :
    violations M u (M.solve [c ← b] u) = {c} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_violations_of_le_divergence ?_ ?_, fun v hv ↦ ?_⟩
  · rwa [solve_update_self]
  · rw [divergence_solve_update hb]
  · by_contra hvc
    exact hv (solve_of_eq_bot (Function.update_of_ne hvc _ _) u)

-- Every other world where `c` is `b` departs no later than the intervention and violates no fewer
-- laws, and departs earlier or violates more.
theorem score_solve_update_lt (hx : x c = b) (hne : x ≠ M.solve [c ← b] u) :
    score M u (M.solve [c ← b] u) < score M u x := by
  rcases eq_or_ne b (M.solve ⊥ u c) with rfl | hb
  · rw [solve_update_of_solve_eq rfl] at hne ⊢
    exact score_solve_bot_lt hne
  have hxc : x c ≠ M.solve ⊥ u c := hx ▸ hb
  simp only [score, Prod.lt_iff, OrderDual.toDual_lt_toDual, OrderDual.toDual_le_toDual,
    divergence_solve_update hb, violations_solve_update hb, Set.encard_singleton]
  rcases (divergence_le hxc).lt_or_eq with h | h
  · refine .inl ⟨h, Set.one_le_encard_iff_nonempty.2 (Set.nonempty_iff_ne_empty.2 ?_)⟩
    exact mt violations_eq_empty_iff.1 fun h ↦ hxc (h ▸ rfl)
  · refine .inr ⟨h.le, Set.one_lt_encard_iff_nontrivial.2 ?_⟩
    exact (Set.nontrivial_iff_ne_singleton (mem_violations_of_le_divergence hxc h.ge)).2
      fun h ↦ hne (eq_solve_of_violations_subset hx h.le)

/-- Under any similarity that brings a world closer when it departs from the actual course of
events later or violates fewer laws, however it weighs the two, the counterfactual whose antecedent
sets the variable `c` to `b` holds exactly when its consequent holds in the world of the
intervention setting `c` to `b`. The closest such world keeps to the actual course of events until
the time of `c` and violates only the law of `c` (pp. 566–567). -/
theorem mem_variablyStrictImp_iff_solve_update {ord : U → Preorder (∀ v, α v)}
    (hord : ∀ x y, score M u x < score M u y → (ord u).lt x y) {C : Set (∀ v, α v)} :
    u ∈ variablyStrictImp (fun _ ↦ Set.univ) ord {x | x c = b} C ↔ M.solve [c ← b] u ∈ C := by
  let := ord u
  have hlt (x : ∀ v, α v) (hx : x c = b) (hne : x ≠ M.solve [c ← b] u) :
      M.solve [c ← b] u < x :=
    hord _ _ (score_solve_update_lt hx hne)
  have h : OrderingSemantics.necessityFilter (ord u) {x | x c = b} =
      pure (M.solve [c ← b] u) :=
    OrderingSemantics.necessityFilter_eq_pure (solve_update_self ⊥ c b u)
      (fun x hx ↦ by
        rcases eq_or_ne x (M.solve [c ← b] u) with rfl | hne
        exacts [le_rfl, (hlt x hx hne).le])
      (fun x hx hle ↦ by_contra fun hne ↦ (hlt x hx hne).not_ge hle)
  rw [mem_variablyStrictImp, Set.univ_inter, h, Filter.mem_pure]

theorem mem_variablyStrictImp_similarity_iff {C : Set (∀ v, α v)} :
    u ∈ variablyStrictImp (fun _ ↦ Set.univ) (similarity M) {x | x c = b} C ↔
      M.solve [c ← b] u ∈ C :=
  mem_variablyStrictImp_iff_solve_update fun _ _ ↦ (Prod.Lex.toLex_strictMono ·)

/-- Had `c` been other than it is, every event that `c` does not reach would have been as it
actually was: the counterfactual does not backtrack, and had an effect been absent its cause would
have occurred just as it did (p. 566). -/
theorem mem_variablyStrictImp_similarity_of_not_reflTransGen {v : V}
    (h : ¬ ReflTransGen M.graph.Adj c v) :
    u ∈ variablyStrictImp (fun _ ↦ Set.univ) (similarity M) {x | x c = b}
      {x | x v = M.solve ⊥ u v} :=
  mem_variablyStrictImp_similarity_iff.2 (solve_update_of_not_reflTransGen h ⊥ _ u)

end Similarity

/-! ### Causation -/

section Causation

variable {U V : Type*} (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic] {u : U} {c d e : V}

/-- `O(c)`, the proposition that the event `c` occurs. -/
def occurs (c : V) : Set (V → Bool) :=
  {x | x c = true}

/-- `c` is a cause of `e` in the context `u` (p. 563) when a causal chain leads from `c` to `e`:
a finite sequence of actual events, each distinct from the one before and depending causally on
it. -/
def Cause (u : U) : V → V → Prop :=
  TransGen fun c e ↦ c ≠ e ∧ M.solve ⊥ u c = true ∧ M.solve ⊥ u e = true ∧
    u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e)

variable {M}

theorem mem_dependsCausally_iff_solve [DecidableEq V] :
    u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e) ↔
      M.solve [c ← true] u e = true ∧ M.solve [c ← false] u e = false := by
  simp only [mem_dependsCausally, occurs, Set.compl_ofPred, Bool.not_eq_true,
    mem_variablyStrictImp_similarity_iff, Set.mem_ofPred_eq]

/-- Among actual events, `e` depends causally on `c` exactly when, had `c` not been, `e` would
not have been (p. 563). -/
theorem mem_dependsCausally_iff_of_actual [DecidableEq V] (hc : M.solve ⊥ u c = true)
    (he : M.solve ⊥ u e = true) :
    u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e) ↔
      M.solve [c ← false] u e = false := by
  rw [mem_dependsCausally_iff_solve, solve_update_of_solve_eq hc, he]
  exact and_iff_right rfl

-- p. 563
theorem mem_dependsCausally_iff_of_not_actual [DecidableEq V] (hc : M.solve ⊥ u c = false)
    (he : M.solve ⊥ u e = false) :
    u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e) ↔
      M.solve [c ← true] u e = true := by
  rw [mem_dependsCausally_iff_solve, solve_update_of_solve_eq hc, he]
  exact and_iff_left rfl

-- p. 563
theorem cause_of_mem_dependsCausally (hce : c ≠ e) (hc : M.solve ⊥ u c = true)
    (he : M.solve ⊥ u e = true)
    (h : u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e)) :
    Cause M u c e :=
  .single ⟨hce, hc, he, h⟩

-- p. 563
theorem Cause.trans (h : Cause M u c d) (h' : Cause M u d e) : Cause M u c e :=
  TransGen.trans h h'

theorem Cause.transGen_adj (h : Cause M u c e) : TransGen M.graph.Adj c e := by
  classical
  refine TransGen.closed (fun c e ⟨hce, hc, he, hdep⟩ ↦ ?_) _ _ h
  refine (reflTransGen_iff_eq_or_transGen.1 (by_contra fun hp ↦ ?_)).resolve_left hce.symm
  have h := (mem_dependsCausally_iff_of_actual hc he).1 hdep
  rw [solve_update_of_not_reflTransGen hp, he] at h
  exact Bool.noConfusion h

-- The paper does not rule out causal loops (p. 565); an acyclic model has none.
theorem Cause.asymm (h : Cause M u c e) : ¬ Cause M u e c := fun h' ↦
  _root_.asymm (r := TransGen M.graph.Adj) h.transGen_adj h'.transGen_adj

instance [DecidableEq V] [Fintype V] (u : U) (c e : V) :
    Decidable (u ∈ dependsCausally (fun _ ↦ Set.univ) (similarity M) (occurs c) (occurs e)) :=
  decidable_of_iff _ mem_dependsCausally_iff_solve.symm

instance [DecidableEq V] [Fintype V] (u : U) : DecidableRel (Cause M u) :=
  inferInstanceAs (DecidableRel (TransGen _))

end Causation

/-! ### Effects and epiphenomena -/

namespace Epiphenomena

/-! The event `c` causes first `e` and then, through `d`, `f`, `e` being an epiphenomenon of `c`.
Had `e` not occurred, `c` would not have been absent but would have failed to cause `e`, so
neither `c` nor `f` depends on `e`, although `e` precedes `f`. -/

inductive V | c | e | d | f
  deriving DecidableEq, Fintype, Repr

/-- `c` bears on `e` and on `d`, and `d` on `f`. -/
def edges : Finset (V × V) := {(.c, .e), (.c, .d), (.d, .f)}

/-- The context settles whether `c` occurs. -/
structure Context where
  c : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- `c` could not have failed to cause `e`, and `f` could not have been caused otherwise than by
`c`. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .c => fun u _ ↦ u.c | .e => fun _ x ↦ x .c | .d => fun _ x ↦ x .c | .f => fun _ x ↦ x .d

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The epiphenomenon `e` causes neither its cause `c` nor the later effect `f` of `c`, though `c`
causes both (pp. 565–566). -/
theorem epiphenomena :
    Cause sem ⟨true⟩ .c .e ∧ Cause sem ⟨true⟩ .c .f ∧ ¬ Cause sem ⟨true⟩ .e .c ∧
      ¬ Cause sem ⟨true⟩ .e .f := by
  decide

end Epiphenomena

/-! ### Preemption -/

namespace Preemption

/-! The events `c₁` and `c₂` both occur. `c₁` causes `e` through `d`, and `c₂` would have caused
`e` through `d₂` had `c₁` been absent, but `c₁` cuts that process off. Had `d` been absent, `c₁`
would still have been there to interfere with `c₂`, so `e` depends on `d`. -/

inductive V | c₁ | c₂ | d | d₂ | e
  deriving DecidableEq, Fintype, Repr

/-- `c₁` bears on `d` and on `d₂`, `c₂` on `d₂`, and both intermediates on `e`. -/
def edges : Finset (V × V) := {(.c₁, .d), (.c₁, .d₂), (.c₂, .d₂), (.d, .e), (.d₂, .e)}

/-- The context settles whether `c₁` and `c₂` occur. -/
structure Context where
  c₁ : Bool
  c₂ : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- `d` follows `c₁`, `d₂` follows `c₂` unless `c₁` interferes, and `e` follows either. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .c₁ => fun u _ ↦ u.c₁
    | .c₂ => fun u _ ↦ u.c₂
    | .d => fun _ x ↦ x .c₁
    | .d₂ => fun _ x ↦ x .c₂ && !x .c₁
    | .e => fun _ x ↦ x .d || x .d₂

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- `c₁` causes `e` through `d`, on which `e` depends, though `e` does not depend causally on
`c₁`; and the preempted `c₂`, from which no causal chain leads to `e`, is no cause of it, though it
is one where `c₁` is absent (p. 567). -/
theorem preemption :
    Cause sem ⟨true, true⟩ .c₁ .e ∧
      ⟨true, true⟩ ∈
        dependsCausally (fun _ ↦ Set.univ) (similarity sem) (occurs .d) (occurs .e) ∧
      ⟨true, true⟩ ∉
        dependsCausally (fun _ ↦ Set.univ) (similarity sem) (occurs .c₁) (occurs .e) ∧
      ¬ Cause sem ⟨true, true⟩ .c₂ .e ∧ Cause sem ⟨false, true⟩ .c₂ .e := by
  decide

-- p. 567: had `d` been absent, `c₁` would still have been there to interfere with `c₂`.
theorem c₁_of_not_d (u : Context) :
    u ∈ variablyStrictImp (fun _ ↦ Set.univ) (similarity sem) {x | x .d = false}
      {x | x .c₁ = sem.solve ⊥ u .c₁} :=
  mem_variablyStrictImp_similarity_of_not_reflTransGen (by decide)

end Preemption

/-! ### Symmetric overdetermination -/

namespace Overdetermination

/-! Two causes each sufficient for the effect both occur, a case footnote 12 sets aside as no
test of the analysis for want of firm naive opinions about it. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

/-- Both causes bear on the effect. -/
def edges : Finset (V × V) := {(.a, .e), (.b, .e)}

/-- The context settles the two causes. -/
structure Context where
  a : Bool
  b : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The effect occurs when either cause does. -/
def sem : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .a => fun u _ ↦ u.a | .b => fun u _ ↦ u.b | .e => fun _ x ↦ x .a || x .b

instance : DecidableRel sem.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

-- The analysis's verdict on the case fn. 12 sets aside.
theorem not_cause : ¬ Cause sem ⟨true, true⟩ .a .e ∧ ¬ Cause sem ⟨true, true⟩ .b .e := by
  decide

end Overdetermination

end Lewis1973a
