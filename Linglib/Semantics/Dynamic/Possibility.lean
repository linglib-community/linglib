module

public import Linglib.Core.Data.Part
public import Linglib.Semantics.Index
public import Linglib.Core.Order.Compat
public import Mathlib.Basic.Rel
public import Mathlib.Data.PFun
public import Mathlib.Logic.Function.Basic

/-!
# Possibilities

This file defines a *possibility*, a world paired with an assignment of discourse referents, the
relation on possibilities that a family of relations on assignments determines world by world
(`Possibility.liftRel`), with equality of two possibilities on a set of referents as an instance
(`Possibility.EqOn`), and the structure of the partial points, whose assignments are families of
partial values `V → Part M`: the descent order, compatibility and joins, restriction, and the
classification of each stratum as world–assignment pairs. Partial values form a forest, so two
compatible points have a join, the point that extends both and is defined only where one of them
is (`Possibility.isLUB_pair_iff`).

## References

- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
- [kamp-vangenabith-reyle-2011], Def. 22
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

/-! ### Relations world by world -/

section LiftRel

open scoped SetRel

variable {R S : W → SetRel (V → M) (V → M)} {a b : Possibility W V M}

/-- The relation on possibilities that a family of relations on assignments determines: the
world is kept, and the assignments are related by the relation at that world. -/
def liftRel (R : W → SetRel (V → M) (V → M)) : SetRel (Possibility W V M) (Possibility W V M) :=
  {(a, b) | a.world = b.world ∧ a.assignment ~[R a.world] b.assignment}

theorem mem_liftRel :
    a ~[liftRel R] b ↔ a.world = b.world ∧ a.assignment ~[R a.world] b.assignment := Iff.rfl

@[simp] theorem liftRel_id :
    liftRel (fun _ ↦ SetRel.id) = (SetRel.id : SetRel (Possibility W V M) (Possibility W V M)) := by
  ext ⟨a, b⟩
  exact Possibility.ext_iff.symm

theorem liftRel_comp (R S : W → SetRel (V → M) (V → M)) :
    liftRel (fun w ↦ R w ○ S w) = liftRel R ○ liftRel S := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨hw, g, h₁, h₂⟩
    exact ⟨⟨a.world, g⟩, ⟨rfl, h₁⟩, hw, h₂⟩
  · rintro ⟨c, ⟨hw₁, h₁⟩, hw₂, h₂⟩
    exact ⟨hw₁.trans hw₂, c.assignment, h₁, by rwa [hw₁]⟩

theorem mem_dom_liftRel : a ∈ (liftRel R).dom ↔ a.assignment ∈ (R a.world).dom :=
  ⟨fun ⟨b, _, h⟩ ↦ ⟨b.assignment, h⟩, fun ⟨g, h⟩ ↦ ⟨⟨a.world, g⟩, rfl, h⟩⟩

end LiftRel

/-! ### Equality on a set of referents -/

section EqOn

open scoped SetRel

variable {X Y : Set V} {p q r : Possibility W V M}

/-- Two possibilities are equal on the referents in `X` when they share their world and their
assignments take the same values on `X`. -/
structure EqOn (p q : Possibility W V M) (X : Set V) : Prop where
  /-- The possibilities share their world. -/
  world_eq : p.world = q.world
  /-- The assignments take the same values on `X`. -/
  assignment_eqOn : Set.EqOn p.assignment q.assignment X

theorem EqOn.refl (p : Possibility W V M) (X : Set V) : p.EqOn p X :=
  ⟨rfl, Set.eqOn_refl _ _⟩

@[symm] theorem EqOn.symm (h : p.EqOn q X) : q.EqOn p X := ⟨h.world_eq.symm, h.assignment_eqOn.symm⟩

theorem EqOn.trans (h : p.EqOn q X) (h' : q.EqOn r X) : p.EqOn r X :=
  ⟨h.world_eq.trans h'.world_eq, h.assignment_eqOn.trans h'.assignment_eqOn⟩

theorem EqOn.mono (hXY : X ⊆ Y) (h : p.EqOn q Y) : p.EqOn q X :=
  ⟨h.world_eq, h.assignment_eqOn.mono hXY⟩

theorem eqOn_comm : p.EqOn q X ↔ q.EqOn p X := ⟨.symm, .symm⟩

@[simp] theorem eqOn_empty : p.EqOn q ∅ ↔ p.world = q.world :=
  ⟨EqOn.world_eq, fun h ↦ ⟨h, Set.eqOn_empty _ _⟩⟩

@[simp] theorem eqOn_univ : p.EqOn q Set.univ ↔ p = q :=
  ⟨fun h ↦ Possibility.ext h.world_eq (funext fun v ↦ h.assignment_eqOn (Set.mem_univ v)),
    fun h ↦ h ▸ .refl _ _⟩

theorem eqOn_update [DecidableEq V] {x : V} (hx : x ∉ X) (m : M) : p.EqOn (p.update x m) X :=
  ⟨rfl, fun _ hv ↦ (Function.update_of_ne (ne_of_mem_of_not_mem hv hx) _ _).symm⟩

/-- Equality on `X` is the relation that equality of assignments on `X` determines world by
world. -/
theorem eqOn_iff_liftRel : p.EqOn q X ↔ p ~[liftRel fun _ ↦ {(g, h) | Set.EqOn g h X}] q :=
  ⟨fun h ↦ ⟨h.world_eq, h.assignment_eqOn⟩, fun ⟨hw, h⟩ ↦ ⟨hw, h⟩⟩

end EqOn

/-! ### Partial points -/

variable {p q r u : Possibility W V (Part M)}

/-- `p ≤ q` iff `p` and `q` share their world and the assignments grow
pointwise in the order of partial values. -/
instance : PartialOrder (Possibility W V (Part M)) where
  le p q := p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x
  le_refl _ := ⟨rfl, fun _ ↦ le_rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, fun x ↦ (hpq.2 x).trans (hqr.2 x)⟩
  le_antisymm _ _ hpq hqp :=
    Possibility.ext hpq.1 (funext fun x ↦ (hpq.2 x).antisymm (hqp.2 x))

theorem le_def : p ≤ q ↔ p.world = q.world ∧ ∀ x, p.assignment x ≤ q.assignment x :=
  Iff.rfl

/-- The domain of a partial point is the set of referents it defines. -/
def domain (p : Possibility W V (Part M)) : Set V :=
  PFun.Dom p.assignment

@[simp] theorem mem_domain {v : V} : v ∈ p.domain ↔ (p.assignment v).Dom := Iff.rfl

theorem domain_mono (h : p ≤ q) : p.domain ⊆ q.domain := fun v ↦ Part.Dom.mono (h.2 v)

theorem eq_of_le_of_domain_eq (h : p ≤ q) (hdom : p.domain = q.domain) : p = q :=
  Possibility.ext h.1 <| funext fun v ↦ Part.eq_of_le (h.2 v) fun hd ↦ hdom.superset hd

theorem domain_eq_empty_iff : p.domain = ∅ ↔ ∀ v, p.assignment v = ⊥ := by
  simp [Set.eq_empty_iff_forall_notMem, Part.eq_bot_iff_not_dom]

section Update

variable [DecidableEq V] {x : V} {m : M}

theorem domain_update_some : (p.update x (.some m)).domain = insert x p.domain := by
  ext v
  by_cases hv : v = x <;> simp [hv, Function.update_of_ne]

theorem le_update_of_notMem (h : x ∉ p.domain) (e : Part M) : p ≤ p.update x e :=
  ⟨rfl, fun v ↦ by
    by_cases hv : v = x
    · subst hv
      simp only [update_assignment, Function.update_self]
      exact fun a ha ↦ absurd ha.fst h
    · simp [Function.update_of_ne hv]⟩

theorem eq_update_of_le (hpr : p ≤ r) (hdom : r.domain = insert x p.domain)
    (hm : r.assignment x = .some m) : r = p.update x (.some m) :=
  Possibility.ext hpr.1.symm <| funext fun v ↦ by
    by_cases hv : v = x
    · subst hv; simp [hm]
    · rw [update_assignment, Function.update_of_ne hv]
      refine (Part.eq_of_le (hpr.2 v) fun hd ↦ ?_).symm
      have hv' : v ∈ r.domain := hd
      rw [hdom] at hv'
      exact hv'.resolve_left hv

end Update

/-! ### The empty point -/

/-- The empty point at a world: no referent defined. -/
def bot (w : W) : Possibility W V (Part M) :=
  ⟨w, fun _ ↦ ⊥⟩

theorem bot_le : bot p.world ≤ p :=
  ⟨rfl, fun _ ↦ _root_.bot_le⟩

theorem bot_le_of_compat {w : W} (h : Compat p (bot w)) : bot w ≤ p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨hpu, hbu⟩ := mem_upperBounds_pair.mp hu
  rw [show w = p.world from hbu.1.trans hpu.1.symm]
  exact bot_le

@[simp] theorem domain_bot {w : W} : (bot w : Possibility W V (Part M)).domain = ∅ :=
  domain_eq_empty_iff.mpr fun _ ↦ rfl

/-! ### Restriction -/

section Restrict

variable {X Y : Set V} {v : V}

/-- Restrict a partial point to the referents in `X`. -/
def restrict (X : Set V) (p : Possibility W V (Part M)) : Possibility W V (Part M) :=
  ⟨p.world, fun v ↦ Part.assert (v ∈ X) fun _ ↦ p.assignment v⟩

@[simp] theorem restrict_world : (p.restrict X).world = p.world := rfl

theorem restrict_assignment (v : V) :
    (p.restrict X).assignment v = Part.assert (v ∈ X) fun _ ↦ p.assignment v := rfl

@[simp] theorem restrict_assignment_of_mem (hv : v ∈ X) :
    (p.restrict X).assignment v = p.assignment v :=
  Part.assert_pos hv

@[simp] theorem restrict_assignment_of_notMem (hv : v ∉ X) : (p.restrict X).assignment v = ⊥ :=
  Part.assert_neg hv

theorem restrict_le : p.restrict X ≤ p :=
  ⟨rfl, fun _ _ ha ↦ (Part.mem_assert_iff.1 ha).snd⟩

theorem le_restrict (h : p ≤ q) (hX : p.domain ⊆ X) : p ≤ q.restrict X :=
  ⟨h.1, fun v a ha ↦ Part.mem_assert_iff.2 ⟨hX ha.fst, h.2 v a ha⟩⟩

theorem domain_restrict : (p.restrict X).domain = X ∩ p.domain :=
  Set.ext fun _ ↦ exists_prop

theorem le_iff_eq_restrict (hp : p.domain = X) : p ≤ q ↔ p = q.restrict X := by
  refine ⟨fun h ↦ Possibility.ext h.1 (funext fun v ↦ ?_), fun h ↦ h ▸ restrict_le⟩
  by_cases hv : v ∈ X
  · rw [restrict_assignment_of_mem hv]
    exact Part.eq_of_le (h.2 v) fun _ ↦ hp.superset hv
  · rw [restrict_assignment_of_notMem hv]
    exact Part.eq_bot_iff_not_dom.2 fun hd ↦ hv (hp.subset hd)

theorem restrict_eq_self (hp : p.domain = X) : p.restrict X = p :=
  ((le_iff_eq_restrict hp).mp le_rfl).symm

theorem restrict_restrict : (p.restrict Y).restrict X = p.restrict (X ∩ Y) :=
  Possibility.ext rfl <| funext fun v ↦ by
    by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hx, hy]

/-- Partial points with domain `X` are exactly world–`X`-assignment pairs. -/
def domainEquiv (X : Set V) :
    {p : Possibility W V (Part M) // p.domain = X} ≃ W × (X → M) where
  toFun p := (p.1.world, fun v ↦ (p.1.assignment v).get (p.2.symm.subset v.2))
  invFun e := ⟨⟨e.1, fun v ↦ ⟨v ∈ X, fun h ↦ e.2 ⟨v, h⟩⟩⟩, rfl⟩
  left_inv p := Subtype.ext <| Possibility.ext rfl <| funext fun v ↦
    Part.ext' (Set.ext_iff.mp p.2 v).symm fun _ _ ↦ rfl
  right_inv _ := rfl

theorem restrict_domainEquiv_symm (h : Y ⊆ X) (e : W × (X → M)) :
    ((domainEquiv X).symm e).1.restrict Y =
      ((domainEquiv Y).symm (e.1, fun v ↦ e.2 ⟨v.1, h v.2⟩)).1 :=
  Possibility.ext rfl <| funext fun _ ↦
    Part.ext' ⟨fun ⟨hy, _⟩ ↦ hy, fun hy ↦ ⟨hy, h hy⟩⟩ fun _ _ ↦ rfl

end Restrict

/-! ### Joins -/

theorem compat_iff_forall : Compat p q ↔
    p.world = q.world ∧ ∀ v, Compat (p.assignment v) (q.assignment v) :=
  ⟨fun ⟨_, hu⟩ ↦
    have ⟨hp, hq⟩ := mem_upperBounds_pair.mp hu
    ⟨hp.1.trans hq.1.symm, fun v ↦ .of_le (hp.2 v) (hq.2 v)⟩,
   fun ⟨hw, hc⟩ ↦ .of_le (u := ⟨p.world, fun v ↦ (hc v).choose⟩)
    ⟨rfl, fun v ↦ (mem_upperBounds_pair.mp (hc v).choose_spec).1⟩
    ⟨hw.symm, fun v ↦ (mem_upperBounds_pair.mp (hc v).choose_spec).2⟩⟩

/-- Two partial points are compatible iff they share their world and agree where both are defined
([kamp-vangenabith-reyle-2011], Def. 26). -/
theorem compat_iff : Compat p q ↔ p.world = q.world ∧
    ∀ v, ∀ e ∈ p.assignment v, ∀ e' ∈ q.assignment v, e = e' := by
  simp only [compat_iff_forall, Compat, Part.bddAbove_pair_iff]

/-- A partial point is the join of two others iff it extends both and defines only what one of
them defines. -/
theorem isLUB_pair_iff : IsLUB {p, q} u ↔ p ≤ u ∧ q ≤ u ∧ u.domain ⊆ p.domain ∪ q.domain := by
  refine ⟨fun h ↦ ?_, fun ⟨hp, hq, hdom⟩ ↦ ⟨mem_upperBounds_pair.mpr ⟨hp, hq⟩, fun u' hu' ↦ ?_⟩⟩
  · obtain ⟨hp, hq⟩ := mem_upperBounds_pair.mp h.1
    have hu := h.2 <| mem_upperBounds_pair.mpr
      ⟨le_restrict hp Set.subset_union_left, le_restrict hq Set.subset_union_right⟩
    exact ⟨hp, hq, fun v hv ↦ (domain_mono hu hv).fst⟩
  · obtain ⟨hp', hq'⟩ := mem_upperBounds_pair.mp hu'
    refine ⟨hp.1.symm.trans hp'.1, fun v e he ↦ ?_⟩
    rcases hdom he.fst with hv | hv
    · exact hp'.2 v e ((Part.eq_of_le (hp.2 v) fun _ ↦ hv).symm ▸ he)
    · exact hq'.2 v e ((Part.eq_of_le (hq.2 v) fun _ ↦ hv).symm ▸ he)

/-- Compatible points have a join: at each referent their values are comparable, since partial
values form a forest, and the join takes the larger. -/
theorem exists_isLUB (h : Compat p q) : ∃ u, IsLUB {p, q} u := by
  classical
  obtain ⟨hw, hc⟩ := compat_iff_forall.mp h
  refine ⟨⟨p.world, fun v ↦ if (p.assignment v).Dom then p.assignment v else q.assignment v⟩,
    isLUB_pair_iff.mpr ⟨⟨rfl, fun v ↦ ?_⟩, ⟨hw.symm, fun v ↦ ?_⟩, fun v hv ↦ ?_⟩⟩
  · dsimp only
    split_ifs with hv
    exacts [le_rfl, fun a ha ↦ absurd ha.fst hv]
  · dsimp only
    split_ifs with hv
    · obtain ⟨b, hb⟩ := hc v
      obtain ⟨hpb, hqb⟩ := mem_upperBounds_pair.mp hb
      exact (IsForestOrder.le_total_of_le_of_le hpb hqb).elim
        (fun hle ↦ (Part.eq_of_le hle fun _ ↦ hv).ge) id
    · exact le_rfl
  · simp only [mem_domain] at hv
    split_ifs at hv with hp
    exacts [.inl hp, .inr hv]

theorem domain_eq_of_isLUB (h : IsLUB {p, q} u) : u.domain = p.domain ∪ q.domain :=
  have ⟨hp, hq, hdom⟩ := isLUB_pair_iff.mp h
  hdom.antisymm (Set.union_subset (domain_mono hp) (domain_mono hq))

theorem eq_of_compat_of_domain_eq (h : Compat p q) (hdom : p.domain = q.domain) : p = q :=
  have ⟨u, hu⟩ := exists_isLUB h
  have ⟨hp, hq, _⟩ := isLUB_pair_iff.mp hu
  have hu' := domain_eq_of_isLUB hu
  (eq_of_le_of_domain_eq hp (by rw [hu', ← hdom, Set.union_self])).trans
    (eq_of_le_of_domain_eq hq (by rw [hu', hdom, Set.union_self])).symm

/-- A point extending `p` and defined on `p`'s domain and `X` is the join of `p` and its own
restriction to `X`. -/
theorem isLUB_restrict {X : Set V} (hpr : p ≤ r) (hdom : r.domain = p.domain ∪ X) :
    IsLUB {p, r.restrict X} r :=
  isLUB_pair_iff.mpr ⟨hpr, restrict_le, fun v hv ↦ (hdom ▸ hv : v ∈ p.domain ∪ X).imp_right
    fun hx ↦ ⟨hx, hv⟩⟩

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
