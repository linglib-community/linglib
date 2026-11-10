/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Syntax.Minimalist.Locality.Transfer
public import Mathlib.Order.Monotone.Defs

/-!
# Horizons

A probe's search stops at a node of its horizon category, and everything that node dominates is
beyond the probe's reach, the edge of the phrase included. Category features are inherited up an
extended projection, so a clause carries every head it projects and is transparent to a probe
exactly when it does not project the horizon. Larger clauses are then
[at least as opaque](##Minimalist.HorizonSetting.transparentTo_antitone), which is Upward
Entailment. A probe whose horizon lies in its own complement is vacuous: its search ends at its
sister. A nonvacuous probe therefore searches into
[every clause inside its complement](##Minimalist.HorizonSetting.TransparentTo.of_not_isVacuousIn),
and a horizon makes vacuous
[every probe hosted above it](##Minimalist.HorizonSetting.IsVacuousIn.of_mem_below), the two
halves of the Height–Locality Theorem.

On a tree, a node carries the [spine](##Minimalist.spineAt) of its extended projection, and the
positions [behind a probe's horizon](##Minimalist.HorizonSetting.cut) are those under a node the
probe c-commands that is [not transparent to it](##Minimalist.HorizonSetting.mem_cut_iff).

## Implementation notes

Vacuity is relative to the spine that hosts the probe, and the probe's sister is
`ClauseSpine.below` of its head. On a spine that does not project the probe's head the complement
is the whole spine, so vacuity is meaningful only for a head the spine projects.

The spine of a node is read off a head function: the category of the node's lexical head, over
the spine of that head's sister when the head is functional and its sister's highest category
extends to it, since a lexical head starts a new extended projection. A head merged with a
specifier and no complement has the specifier for sister, which inherits only if it belongs to
the head's own extended projection.

Unlike the domain Transfer seals, the complement of a phase head, a horizon closes the whole
phrase, so no element escapes through its edge.

## References

* [keine-2019]
* [keine-2020]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

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

/-- A clause is transparent to `p` when `p` has no horizon or the clause does not project it. -/
def TransparentTo (s : ClauseSpine) : Prop := ∀ h ∈ p.horizon, h ∉ s

instance : Decidable (p.TransparentTo s) := Option.decidableForallMem _

@[simp] theorem transparentTo_mk_none : (HorizonSetting.mk c none).TransparentTo s := by
  simp [TransparentTo]

@[simp] theorem transparentTo_mk_some : (HorizonSetting.mk c (some h)).TransparentTo s ↔ h ∉ s := by
  simp [TransparentTo]

variable {p}

theorem TransparentTo.anti (hst : s ≤ t) (ht : p.TransparentTo t) : p.TransparentTo s :=
  fun c hc hm ↦ ht c hc (ClauseSpine.le_iff_forall_mem.1 hst c hm)

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
  simp [IsVacuousIn, TransparentTo]

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

end HorizonSetting

/-! ### Horizons on trees -/

variable (hd : HeadFunction) (t : LinearizedSyntacticObject)

/-- The category of the pronounced head at a position. -/
def catAt (p : TreePath) : Option Cat := ((tokenList t.val).find? (·.1 = p)).map (·.2.item.cat)

/-- The heads of the extended projection of the phrase at `p`, bottom-up, to a bounded depth. -/
def spineHeads : ℕ → TreePath → List Cat
  | 0, _ => []
  | n + 1, p =>
    let h := lexicalHeadAt hd t p
    match catAt t h with
    | none => []
    | some c =>
      if h = p then [c] else
        let below := spineHeads n (complement h)
        (if c ≠ c.family.lexical ∧ ∃ d ∈ below.getLast?, d.ExtendsTo c then below else []) ++ [c]

/-- The spine of the node at `p`, the heads of its extended projection, whose categories it
inherits ([keine-2019]'s Category Inheritance). -/
def spineAt (p : TreePath) : ClauseSpine := ⟨spineHeads hd t t.val.subtrees.length p⟩

/-- The positions behind the horizon `c` of the probe at `a`, those dominated by a node the probe
c-commands whose spine contains `c` ([keine-2019]'s Horizons). -/
def horizon (a : TreePath) (c : Cat) : Set TreePath :=
  {q | ∃ x ∈ Finset.Iio q, t.val.CCommands a x ∧ c ∈ spineAt hd t x}

instance (a : TreePath) (c : Cat) : DecidablePred (· ∈ horizon hd t a c) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The positions closed to the search of a probe with setting `p` at `a`, those behind its
horizon; none when it has no horizon. -/
def HorizonSetting.cut (p : HorizonSetting) (a : TreePath) : Set TreePath :=
  {q | ∃ c ∈ p.horizon, q ∈ Minimalist.horizon hd t a c}

instance (p : HorizonSetting) (a : TreePath) : DecidablePred (· ∈ p.cut hd t a) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {hd t} {a q : TreePath} {c : Cat} {p : HorizonSetting}

theorem spineHeads_isChain (n : ℕ) (x : TreePath) :
    (spineHeads hd t n x).IsChain Cat.ExtendsTo := by
  induction n generalizing x with
  | zero => exact .nil
  | succ n ih =>
    rw [spineHeads]
    split
    · exact .nil
    · split
      · exact .singleton _
      · dsimp only
        split
        next h₂ =>
          obtain ⟨d, hd', hdc⟩ := h₂.2
          exact (ih _).append (.singleton _) fun e he b hb ↦ by
            obtain rfl : e = d := Option.some.inj (he.symm.trans hd')
            obtain rfl : _ = b := by simpa using hb
            exact hdc
        next => exact .singleton _

/-- The spine of a node is an extended projection. -/
theorem isExtendedProjection_spineAt (x : TreePath) : (spineAt hd t x).IsExtendedProjection :=
  spineHeads_isChain _ x

theorem isUpperSet_horizon : IsUpperSet (horizon hd t a c) :=
  fun _ _ hqr ⟨x, hx, h⟩ ↦ ⟨x, Finset.mem_Iio.2 ((Finset.mem_Iio.1 hx).trans_le hqr), h⟩

@[simp] theorem HorizonSetting.cut_mk_none {c' : Cat} :
    (HorizonSetting.mk c' none).cut hd t a = ∅ := by
  simp [HorizonSetting.cut]

@[simp] theorem HorizonSetting.cut_mk_some {c' : Cat} :
    (HorizonSetting.mk c' (some c)).cut hd t a = Minimalist.horizon hd t a c := by
  simp [HorizonSetting.cut]

/-- A position is behind a probe's horizon exactly when a node the probe c-commands dominates it
and is not transparent to the probe. -/
theorem HorizonSetting.mem_cut_iff :
    q ∈ p.cut hd t a ↔ ∃ x < q, t.val.CCommands a x ∧ ¬ p.TransparentTo (spineAt hd t x) := by
  constructor
  · rintro ⟨c, hc, x, hx, ha, hm⟩
    exact ⟨x, Finset.mem_Iio.1 hx, ha, fun ht ↦ ht c hc hm⟩
  · rintro ⟨x, hx, ha, hnt⟩
    obtain ⟨c, hc, hm⟩ : ∃ c ∈ p.horizon, c ∈ spineAt hd t x := by
      simpa [HorizonSetting.TransparentTo] using hnt
    exact ⟨c, hc, x, Finset.mem_Iio.2 hx, ha, hm⟩

end Minimalist
