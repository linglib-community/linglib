module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Core.Order.PartialUnify
public import Mathlib.Logic.Function.Basic

/-!
# Possibilities

This file defines a *possibility* — a world paired with an assignment
of discourse referents — and the structure of its partial points, whose
assignments are `PartialAssign`s, `Flat`-valued: the descent order,
compatibility and union, restriction, and the classification of each
stratum as world–assignment pairs.

## References

- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [kamp-vangenabith-reyle-2011], Def. 0.22
- [heim-1982]
-/

@[expose] public section

namespace DynamicSemantics

/-- A possibility is a world paired with an assignment of discourse
referents to individuals. -/
@[ext] structure Possibility (W V M : Type*) where
  /-- The world coordinate. -/
  world : W
  /-- The assignment of discourse referents. -/
  assignment : V → M

namespace Possibility

variable {W V M : Type*} (p : Possibility W V M)

section Update

variable [DecidableEq V] (x : V) (e : M)

/-- Update the assignment at a single referent. -/
def update : Possibility W V M :=
  { p with assignment := Function.update p.assignment x e }

@[simp] theorem update_world : (p.update x e).world = p.world := rfl

@[simp] theorem update_assignment :
    (p.update x e).assignment = Function.update p.assignment x e := rfl

end Update

/-! ### Partial points -/

variable {p q r u : Possibility W V (Flat M)}

/-- `p ≤ q` iff `p` and `q` share their world and the assignments grow
pointwise in the order of partial values. -/
instance : PartialOrder (Possibility W V (Flat M)) where
  le p q := p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x
  le_refl _ := ⟨rfl, fun _ => le_rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, fun x => (hpq.2 x).trans (hqr.2 x)⟩
  le_antisymm _ _ hpq hqp :=
    Possibility.ext hpq.1 (funext fun x => (hpq.2 x).antisymm (hqp.2 x))

theorem le_def : p ≤ q ↔ p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x :=
  Iff.rfl

/-- The domain of a partial point is the set of referents it defines. -/
def domain (p : Possibility W V (Flat M)) : Set V :=
  PartialAssign.domain p.assignment

@[simp] theorem mem_domain {v : V} : v ∈ p.domain ↔ p.assignment v ≠ ⊥ := Iff.rfl

theorem domain_mono (h : p ≤ q) : p.domain ⊆ q.domain := fun v =>
  (ne_bot_of_le_ne_bot · (h.2 v))

theorem eq_of_le_of_domain_eq (h : p ≤ q) (hdom : p.domain = q.domain) : p = q :=
  Possibility.ext h.1 <| funext fun v =>
    Flat.eq_of_le (h.2 v) fun hd => hdom.superset hd

theorem domain_eq_empty_iff : p.domain = ∅ ↔ ∀ v, p.assignment v = ⊥ := by
  simp [Set.eq_empty_iff_forall_notMem]

section Update

variable [DecidableEq V] {x : V} {m : M}

theorem domain_update_coe : (p.update x ↑m).domain = insert x p.domain := by
  ext v
  by_cases hv : v = x <;> simp [hv, Function.update_of_ne]

theorem le_update_of_eq_bot (h : p.assignment x = ⊥) (e : Flat M) : p ≤ p.update x e :=
  ⟨rfl, fun v ↦ by
    by_cases hv : v = x
    · subst hv; simp [h]
    · simp [Function.update_of_ne hv]⟩

theorem eq_update_of_le (hpr : p ≤ r) (hdom : r.domain = insert x p.domain)
    (hm : r.assignment x = ↑m) : r = p.update x ↑m :=
  Possibility.ext hpr.1.symm <| funext fun v ↦ by
    by_cases hv : v = x
    · subst hv; simp [hm]
    · rw [update_assignment, Function.update_of_ne hv]
      refine (Flat.eq_of_le (hpr.2 v) fun hd ↦ ?_).symm
      have hv' : v ∈ r.domain := hd
      rw [hdom] at hv'
      exact hv'.resolve_left hv

end Update

/-- The union of two points, defined wherever either is, with the left
taking precedence; on compatible points the precedence is immaterial
(`union_comm`). -/
def union (p q : Possibility W V (Flat M)) : Possibility W V (Flat M) :=
  ⟨p.world, fun v => (p.assignment v).or (q.assignment v)⟩

@[simp] theorem union_world : (p.union q).world = p.world := rfl

@[simp] theorem union_assignment (v : V) :
    (p.union q).assignment v = (p.assignment v).or (q.assignment v) := rfl

theorem le_union_left : p ≤ p.union q :=
  ⟨rfl, fun _ => Flat.le_or_left _ _⟩

theorem union_le (hp : p ≤ u) (hq : q ≤ u) : p.union q ≤ u :=
  ⟨hp.1, fun v => Flat.or_le (hp.2 v) (hq.2 v)⟩

theorem compat_iff_forall : Compat p q ↔
    p.world = q.world ∧ ∀ v, Compat (p.assignment v) (q.assignment v) :=
  ⟨fun ⟨_, hu⟩ =>
    have ⟨hp, hq⟩ := mem_upperBounds_pair.mp hu
    ⟨hp.1.trans hq.1.symm, fun v => .of_le (hp.2 v) (hq.2 v)⟩,
   fun ⟨hw, hc⟩ => .of_le le_union_left
    ⟨hw.symm, fun v => Flat.le_or_right (hc v)⟩⟩

/-- Two partial points are compatible (`Compat`: bounded above in the
descent order) exactly when they share their world and agree wherever
both are defined — the requirement in [kamp-vangenabith-reyle-2011],
Def. 0.26, that the union of chosen points be a function. -/
theorem compat_iff : Compat p q ↔
    p.world = q.world ∧
      ∀ v (e e' : M), p.assignment v = ↑e → q.assignment v = ↑e' → e = e' := by
  simp only [compat_iff_forall, Flat.compat_iff]
  exact and_congr_right fun _ ↦ forall_congr' fun _ ↦
    ⟨fun h e e' he he' ↦ h e he e' he', fun h e he e' he' ↦ h e e' he he'⟩

theorem le_union_right (h : Compat p q) : q ≤ p.union q :=
  have h' := compat_iff_forall.mp h
  ⟨h'.1.symm, fun v => Flat.le_or_right (h'.2 v)⟩

theorem isLUB_union (h : Compat p q) : IsLUB {p, q} (p.union q) :=
  ⟨mem_upperBounds_pair.mpr ⟨le_union_left, le_union_right h⟩,
    fun _ hu =>
      have h := mem_upperBounds_pair.mp hu
      union_le h.1 h.2⟩

theorem isLUB_pair_iff : IsLUB {p, q} u ↔ Compat p q ∧ u = p.union q :=
  ⟨fun h =>
    have hc : Compat p q := ⟨u, h.1⟩
    ⟨hc, ((isLUB_union hc).unique h).symm⟩,
   fun ⟨hc, hu⟩ => hu ▸ isLUB_union hc⟩

open Classical in
/-- Unification of points is their union when they are compatible, and fails otherwise. The
instance is noncomputable, since compatibility is not decided. -/
noncomputable instance : PartialUnify (Possibility W V (Flat M)) where
  unify p q := if Compat p q then ↑(p.union q) else ⊤
  isLUB_of_unify_eq_coe {p q u} h := by
    split_ifs at h with hc
    · exact WithTop.coe_inj.mp h ▸ isLUB_union hc
    · exact absurd h WithTop.top_ne_coe
  unify_ne_top_of_bddAbove {p q} h := by
    rw [ite_eq_left h]
    exact WithTop.coe_ne_top

theorem unify_eq_coe_iff : PartialUnify.unify p q = ↑u ↔ Compat p q ∧ u = p.union q :=
  PartialUnify.unify_eq_coe_iff_isLUB.trans isLUB_pair_iff

theorem domain_union : (p.union q).domain = p.domain ∪ q.domain := by
  ext v
  cases h : p.assignment v <;> simp [h]

theorem eq_of_compat_of_domain_eq (h : Compat p q) (hdom : p.domain = q.domain) :
    p = q :=
  have hu : (p.union q).domain = p.domain := by rw [domain_union, ← hdom, Set.union_self]
  (eq_of_le_of_domain_eq le_union_left hu.symm).trans
    (eq_of_le_of_domain_eq (le_union_right h) (hdom.symm.trans hu.symm)).symm

theorem union_assoc : (p.union q).union r = p.union (q.union r) :=
  Possibility.ext rfl <| funext fun _ => Flat.or_assoc _ _ _

@[simp] theorem union_self : p.union p = p :=
  Possibility.ext rfl <| funext fun _ => Flat.or_self _

theorem union_comm (h : Compat p q) : p.union q = q.union p :=
  (isLUB_union h).unique (Set.pair_comm p q ▸ isLUB_union h.symm)

/-! ### The empty point -/

/-- The empty point at a world: no referent defined. -/
def bot (w : W) : Possibility W V (Flat M) :=
  ⟨w, fun _ => ⊥⟩

theorem bot_le : bot p.world ≤ p :=
  ⟨rfl, fun _ => _root_.bot_le⟩

theorem bot_le_of_compat {w : W} (h : Compat p (bot w)) : bot w ≤ p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨hpu, hbu⟩ := mem_upperBounds_pair.mp hu
  rw [show w = p.world from hbu.1.trans hpu.1.symm]
  exact bot_le

@[simp] theorem union_bot {w : W} : p.union (bot w) = p :=
  Possibility.ext rfl <| funext fun _ => Flat.or_bot _

@[simp] theorem domain_bot {w : W} : (bot w : Possibility W V (Flat M)).domain = ∅ :=
  domain_eq_empty_iff.mpr fun _ => rfl

/-! ### Restriction and the indexed classification -/

section Restrict

variable {X Y : Set V}

open Classical in
/-- Restrict a partial point to the referents in `X`. -/
noncomputable def restrict (X : Set V) (p : Possibility W V (Flat M)) :
    Possibility W V (Flat M) :=
  ⟨p.world, fun v => if v ∈ X then p.assignment v else ⊥⟩

@[simp] theorem restrict_world : (p.restrict X).world = p.world := rfl

open Classical in
theorem restrict_assignment (v : V) :
    (p.restrict X).assignment v = if v ∈ X then p.assignment v else ⊥ := rfl

theorem restrict_le : p.restrict X ≤ p :=
  ⟨rfl, fun v => by
    rw [restrict_assignment]
    split_ifs
    exacts [le_rfl, _root_.bot_le]⟩

theorem domain_restrict : (p.restrict X).domain = X ∩ p.domain := by
  ext v
  by_cases hv : v ∈ X <;> simp [restrict_assignment, hv]

theorem restrict_assignment_of_mem {v : V} (hv : v ∈ X) :
    (p.restrict X).assignment v = p.assignment v := by
  classical
  rw [restrict_assignment, ite_eq_left hv]

theorem le_iff_eq_restrict (hp : p.domain = X) :
    p ≤ q ↔ p = q.restrict X := by
  refine ⟨fun h => Possibility.ext h.1 (funext fun v => ?_), fun h => h ▸ restrict_le⟩
  rw [restrict_assignment]
  split_ifs with hv
  · exact Flat.eq_of_le (h.2 v) fun _ => hp.superset hv
  · by_contra hne
    exact hv (hp.subset hne)

theorem restrict_eq_self (hp : p.domain = X) : p.restrict X = p :=
  ((le_iff_eq_restrict hp).mp le_rfl).symm

theorem eq_union_restrict (hpr : p ≤ r)
    (hdom : r.domain = p.domain ∪ X) : r = p.union (r.restrict X) :=
  (eq_of_le_of_domain_eq (union_le hpr restrict_le) <| by
    rw [domain_union, domain_restrict, hdom, Set.inter_eq_left.mpr Set.subset_union_right]).symm

theorem restrict_restrict : (p.restrict Y).restrict X = p.restrict (X ∩ Y) :=
  Possibility.ext rfl <| funext fun v => by
    simp only [restrict_assignment, Set.mem_inter_iff]
    by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hx, hy]

open Classical in
/-- Partial points with domain `X` are exactly world–`X`-assignment
pairs. -/
noncomputable def domainEquiv (X : Set V) :
    {p : Possibility W V (Flat M) // p.domain = X} ≃ W × (X → M) where
  toFun p := (p.1.world, fun v => (p.1.assignment v.1).get (p.2.superset v.2))
  invFun e := ⟨⟨e.1, fun v => if h : v ∈ X then ↑(e.2 ⟨v, h⟩) else ⊥⟩, by
    ext v; by_cases h : v ∈ X <;> simp [h]⟩
  left_inv p := Subtype.ext <| Possibility.ext rfl <| funext fun v => by
    by_cases h : v ∈ X
    · simp only [h, dite_true]
      exact Flat.coe_get _ _
    · simp only [h, dite_false]
      by_contra hne
      exact h (p.2.subset (Ne.symm hne))
  right_inv _ := by ext <;> simp

theorem restrict_domainEquiv_symm (h : Y ⊆ X) (e : W × (X → M)) :
    ((domainEquiv X).symm e).1.restrict Y =
      ((domainEquiv Y).symm (e.1, fun v => e.2 ⟨v.1, h v.2⟩)).1 :=
  Possibility.ext rfl <| funext fun v => by
    simp only [domainEquiv, Equiv.coe_fn_symm_mk, restrict_assignment]
    by_cases hy : v ∈ Y
    · simp [hy, h hy]
    · simp [hy]

end Restrict

/-! ### Instantiations

Update systems share one form — states are sets of points, updates act
on states — and differ in the point. The parameters select the system:
worlds only gives propositional update semantics ([veltman-1996]; the
`∅`-fiber), assignments only gives lifted DPL, and the general form is
FCS/DRT's pairs. Propositional inquisitive semantics instead *iterates*
the construction — its points are sets of worlds — a level shift, not a
parameter choice. -/

/-- Worlds-only points are bare worlds — the points of propositional
update semantics. -/
def worldEquiv (W M : Type*) : Possibility W Empty M ≃ W where
  toFun p := p.world
  invFun w := ⟨w, Empty.elim⟩
  left_inv _ := Possibility.ext rfl (funext fun v => v.elim)
  right_inv _ := rfl

/-- Assignment-only points are bare assignments — the points of lifted
DPL. -/
def assignmentEquiv (V M : Type*) : Possibility Unit V M ≃ (V → M) where
  toFun p := p.assignment
  invFun g := ⟨(), g⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Possibility

end DynamicSemantics
