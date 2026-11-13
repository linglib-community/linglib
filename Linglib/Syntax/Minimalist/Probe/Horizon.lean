/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Syntax.Minimalist.Phase.Transfer
public import Mathlib.Data.Finset.Option
public import Mathlib.Order.Monotone.Defs

/-!
# Horizons

A probe's search stops at a node of its horizon category, and everything that node dominates is
beyond the probe's reach, the edge of the phrase included. Category features are inherited up an
extended projection, so a clause carries every head it projects and is transparent to a probe
exactly when it does not project the horizon. Larger clauses are then
[at least as opaque](##Minimalist.HorizonSetting.transparentTo_antitone), which is Upward
Entailment. A probe whose horizon lies in its own complement is vacuous: its search ends at its
sister. On an extended projection the horizon of a nonvacuous probe is therefore
[at or above its head](##Minimalist.HorizonSetting.extendsTo_of_not_isVacuousIn), the
Height–Locality Theorem.

On a tree, a node carries the [spine](##Minimalist.spineOf) of its extended projection, a phrase
[inheriting its complement's categories](##Minimalist.spineOf_le_spineOf_node), and the positions
[behind a probe's horizon](##Minimalist.HorizonSetting.cut) are those under a node the probe
c-commands that is [not transparent to it](##Minimalist.HorizonSetting.mem_cut_iff). A vacuous probe
[reaches nothing beyond its sister](##Minimalist.HorizonSetting.mem_cut_of_isVacuousIn).

## Implementation notes

Vacuity is relative to the spine that hosts the probe, and the probe's sister is
`ClauseSpine.below` of its head. On a spine that does not project the probe's head the complement
is the whole spine, so vacuity is meaningful only for a head the spine projects.

The spine of a tree is a fold over it, given the index of each tree's head daughter. A head
merged with a specifier and no complement has the specifier for sister, which it inherits from
only if the specifier belongs to its own extended projection. Traces carry no spine.

Unlike the domain Transfer seals, the complement of a phase head, a horizon closes the whole
phrase, so no element escapes through its edge.

## References

* [keine-2019]
* [keine-2020]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree SyntacticObject

/-- A probe's horizon setting is the head that hosts it and the category that terminates its
search, its horizon; a probe without horizon searches into any domain. -/
structure HorizonSetting where
  /-- The head that hosts the probe. -/
  head : Cat
  /-- The category that terminates the probe's search, if any. -/
  horizon : Option Cat
  deriving DecidableEq, Repr

namespace HorizonSetting

variable (p : HorizonSetting) {s t : ClauseSpine} {c d h : Cat} {o : Option Cat}

/-! ### Transparency -/

/-- A clause is transparent to `p` when its label is disjoint from the horizon of `p`. -/
def TransparentTo (s : ClauseSpine) : Prop := Disjoint p.horizon.toFinset s.label

instance : Decidable (p.TransparentTo s) := inferInstanceAs (Decidable (Disjoint _ _))

variable {p} in
theorem transparentTo_iff : p.TransparentTo s ↔ ∀ h ∈ p.horizon, h ∉ s := by
  simp [TransparentTo, Finset.disjoint_left]

@[simp] theorem transparentTo_mk_none : (HorizonSetting.mk c none).TransparentTo s := by
  simp [TransparentTo]

@[simp] theorem transparentTo_mk_some :
    (HorizonSetting.mk c (some h)).TransparentTo s ↔ h ∉ s := by
  simp [TransparentTo]

variable {p}

theorem TransparentTo.anti (hst : s ≤ t) (ht : p.TransparentTo t) : p.TransparentTo s :=
  ht.mono_right hst

variable (p) in
/-- Upward Entailment: a clause opaque to a probe stays opaque when it projects more structure,
since it inherits the horizon from the smaller clause. -/
theorem transparentTo_antitone : Antitone p.TransparentTo := fun _ _ ↦ TransparentTo.anti

/-! ### Vacuity -/

variable (p) in
/-- `p` is vacuous in `s` when its horizon lies in the complement of its head, so that its search
ends at its sister and it triggers no movement or agreement. -/
def IsVacuousIn (s : ClauseSpine) : Prop := ¬ p.TransparentTo (s.below p.head)

instance : Decidable (p.IsVacuousIn s) := inferInstanceAs (Decidable (¬ _))

theorem isVacuousIn_iff : p.IsVacuousIn s ↔ ∃ h ∈ p.horizon, h ∈ s.below p.head := by
  simp [IsVacuousIn, transparentTo_iff]

@[simp] theorem not_isVacuousIn_mk_none : ¬ (HorizonSetting.mk c none).IsVacuousIn s :=
  not_not_intro transparentTo_mk_none

@[simp] theorem isVacuousIn_mk_some :
    (HorizonSetting.mk c (some h)).IsVacuousIn s ↔ h ∈ s.below c := by
  simp [IsVacuousIn]

/-- A probe whose horizon is the category of its own head, its default horizon, is not vacuous. -/
theorem not_isVacuousIn_mk_self : ¬ (HorizonSetting.mk c (some c)).IsVacuousIn s := by
  simpa using s.notMem_below_self c

/-- The Height–Locality Theorem, from height to locality: a nonvacuous probe searches into every
clause that projects no more than its complement does. -/
theorem TransparentTo.of_not_isVacuousIn (hp : ¬ p.IsVacuousIn s) (ht : t ≤ s.below p.head) :
    p.TransparentTo t :=
  (not_not.1 hp).anti ht

/-- The Height–Locality Theorem, from locality to height: a horizon that makes a probe on `c`
vacuous makes vacuous a probe on any head above `c`. -/
theorem IsVacuousIn.of_mem_below (hp : (HorizonSetting.mk c o).IsVacuousIn s)
    (hc : c ∈ s.below d) : (HorizonSetting.mk d o).IsVacuousIn s :=
  fun ht ↦ hp (ht.anti (ClauseSpine.below_le_below hc))

/-- The Height–Locality Theorem on an extended projection: the horizon of a nonvacuous probe is at
or above the head that hosts it. -/
theorem extendsTo_of_not_isVacuousIn (hs : s.IsExtendedProjection) (hc : c ∈ s) (hh : h ∈ s)
    (hp : ¬ (HorizonSetting.mk c (some h)).IsVacuousIn s) : c.ExtendsTo h :=
  (hs.mem_below_or_extendsTo hc hh).resolve_left (isVacuousIn_mk_some.not.1 hp)

/-- A vacuous probe's horizon lies at or below the head that hosts it. -/
theorem IsVacuousIn.extendsTo (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hp : (HorizonSetting.mk c (some h)).IsVacuousIn s) : h.ExtendsTo c :=
  hs.extendsTo_of_mem_below hc (isVacuousIn_mk_some.1 hp)

end HorizonSetting

/-! ### Horizons on trees -/

variable (η : RoseTree Vertex → Option ℕ) (t : PlanarSyntacticObject)

/-- The lexical item at the root of a tree, if it is a pronounced leaf. -/
def rootToken? : RoseTree Vertex → Option LexicalItem.Token
  | .node (.inl tok) _ => tok
  | _ => none

/-- The spine of a tree, the heads of its extended projection, given the index `η` of the head
daughter of each tree: a head projects its category over the spine of its sister, and a phrase
keeps the spine of its head daughter ([keine-2019]'s Category Inheritance). -/
def spineOf : RoseTree Vertex → ClauseSpine
  | .node (.inl (some tok)) _ => ⟨[tok.item.cat]⟩
  | .node (.inl none) [l, r] =>
    match η (.node (.inl none) [l, r]) with
    | some 0 => (rootToken? l).elim (spineOf l) fun tok ↦ (spineOf r).project tok.item.cat
    | some 1 => (rootToken? r).elim (spineOf r) fun tok ↦ (spineOf l).project tok.item.cat
    | _ => ⟨[]⟩
  | _ => ⟨[]⟩

/-- The spine of the node at `p`. -/
def spineAt (p : TreePath) : ClauseSpine := t.toRoseTree[p]?.elim ⟨[]⟩ (spineOf η)

/-- The positions behind the horizon `c` of the probe at `a`, those dominated by a node the probe
c-commands whose spine contains `c` ([keine-2019]'s Horizons). -/
def horizon (a : TreePath) (c : Cat) : Set TreePath :=
  {q | ∃ x ∈ Finset.Iio q, t.toRoseTree.CCommands a x ∧ c ∈ spineAt η t x}

instance (a : TreePath) (c : Cat) : DecidablePred (· ∈ horizon η t a c) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The positions closed to the search of a probe with setting `p` at `a`, those behind its
horizon; none when it has no horizon. -/
def HorizonSetting.cut (p : HorizonSetting) (a : TreePath) : Set TreePath :=
  {q | ∃ c ∈ p.horizon, q ∈ Minimalist.horizon η t a c}

instance (p : HorizonSetting) (a : TreePath) : DecidablePred (· ∈ p.cut η t a) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {η t} {a q : TreePath} {c c' : Cat} {p : HorizonSetting} {l r : RoseTree Vertex}
  {tok : LexicalItem.Token}

/-- The spine of a tree is an extended projection. -/
theorem isExtendedProjection_spineOf (s : RoseTree Vertex) :
    (spineOf η s).IsExtendedProjection := by
  fun_induction spineOf η s
  case case1 => exact .singleton _
  case case2 ihl ihr | case3 ihl ihr =>
    cases rootToken? _ <;> first | assumption | exact .project ‹_› _
  all_goals exact .nil

theorem spineOf_node_zero (h : η (.node (.inl none) [l, r]) = some 0) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootToken? l).elim (spineOf η l) fun tok ↦ (spineOf η r).project tok.item.cat := by
  simp [spineOf, h]

theorem spineOf_node_one (h : η (.node (.inl none) [l, r]) = some 1) :
    spineOf η (.node (.inl none) [l, r]) =
      (rootToken? r).elim (spineOf η r) fun tok ↦ (spineOf η l).project tok.item.cat := by
  simp [spineOf, h]

/-- Horizon inheritance: the phrase of a head that inherits from its complement carries every
category the complement does, so it is a horizon for every probe the complement is. -/
theorem spineOf_le_spineOf_node (h : η (.node (.inl none) [l, r]) = some 0)
    (hl : rootToken? l = some tok) (hi : (spineOf η r).Inherits tok.item.cat) :
    spineOf η r ≤ spineOf η (.node (.inl none) [l, r]) := by
  simpa [spineOf_node_zero h, hl] using ClauseSpine.le_project hi

theorem isUpperSet_horizon : IsUpperSet (horizon η t a c) :=
  fun _ _ hqr ⟨x, hx, h⟩ ↦ ⟨x, Finset.mem_Iio.2 ((Finset.mem_Iio.1 hx).trans_le hqr), h⟩

@[simp] theorem HorizonSetting.cut_mk_none : (HorizonSetting.mk c' none).cut η t a = ∅ := by
  simp [HorizonSetting.cut]

@[simp] theorem HorizonSetting.cut_mk_some :
    (HorizonSetting.mk c' (some c)).cut η t a = Minimalist.horizon η t a c := by
  simp [HorizonSetting.cut]

/-- A position is behind a probe's horizon exactly when a node the probe c-commands dominates it
and is not transparent to the probe. -/
theorem HorizonSetting.mem_cut_iff :
    q ∈ p.cut η t a ↔ ∃ x < q, t.toRoseTree.CCommands a x ∧ ¬ p.TransparentTo (spineAt η t x) := by
  constructor
  · rintro ⟨c, hc, x, hx, ha, hm⟩
    exact ⟨x, Finset.mem_Iio.1 hx, ha, fun ht ↦ transparentTo_iff.1 ht c hc hm⟩
  · rintro ⟨x, hx, ha, hnt⟩
    obtain ⟨c, hc, hm⟩ : ∃ c ∈ p.horizon, c ∈ spineAt η t x := by
      simpa [transparentTo_iff] using hnt
    exact ⟨c, hc, x, Finset.mem_Iio.2 hx, ha, hm⟩

/-- A probe whose sister is not transparent to it reaches nothing beyond its sister: every
position it c-commands below the sister is behind its horizon. -/
theorem HorizonSetting.mem_cut_of_not_transparentTo (ha : a ∈ t.toRoseTree.validPaths) (ha0 : a ≠ ⊥)
    (hq : q ∈ t.toRoseTree.validPaths) (hc : t.toRoseTree.CCommands a q) (hne : q ≠ complement a)
    (hs : ¬ p.TransparentTo (spineAt η t (complement a))) : q ∈ p.cut η t a := by
  have hle : complement a ≤ q := (mem_cCommandDomain_iff_complement_le ha ha0 hq).1 hc
  have hv : complement a ∈ t.toRoseTree.validPaths := isLowerSet_validPaths _ hle hq
  exact mem_cut_iff.2 ⟨_, lt_of_le_of_ne hle (Ne.symm hne),
    (mem_cCommandDomain_iff_complement_le ha ha0 hv).2 le_rfl, hs⟩

/-- A vacuous probe reaches nothing beyond its sister: where the head of `p` inherits from its
sister and `p` is vacuous in the phrase it projects, every position it c-commands below the sister
is behind its horizon. -/
theorem HorizonSetting.mem_cut_of_isVacuousIn (ha : a ∈ t.toRoseTree.validPaths) (ha0 : a ≠ ⊥)
    (hq : q ∈ t.toRoseTree.validPaths) (hc : t.toRoseTree.CCommands a q) (hne : q ≠ complement a)
    (hi : (spineAt η t (complement a)).Inherits p.head)
    (hn : p.head ∉ spineAt η t (complement a))
    (hv : p.IsVacuousIn ((spineAt η t (complement a)).project p.head)) : q ∈ p.cut η t a :=
  mem_cut_of_not_transparentTo ha ha0 hq hc hne (by
    rwa [IsVacuousIn, ClauseSpine.below_project hi hn] at hv)

end Minimalist
