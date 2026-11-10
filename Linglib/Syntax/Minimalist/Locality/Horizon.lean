/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Locality.Transfer
public import Linglib.Syntax.Minimalist.Probe.Profile

/-!
# Horizons

A probe's search stops at a node of its horizon category, and everything that node dominates is
beyond the probe's reach, the edge of the phrase included. Category features are inherited up an
extended projection, so a node carries the categories of the heads of its extended projection,
its [spine](##Minimalist.spineAt), and every projection above a head of the horizon category
within that extended projection is a horizon too. A lexical head starts a new extended
projection, so the verb phrase over a clausal complement does not inherit from it. The positions
[behind a probe's horizon](##Minimalist.Probe.Profile.cut) are thus those under a node the probe
c-commands whose spine is [not transparent to it](##Minimalist.Probe.Profile.mem_cut_iff).

## Implementation notes

The spine of a node is read off a head function: the category of the node's lexical head, over
the spine of that head's sister when the head is functional and its sister's highest category
extends to it. A head merged with a specifier and no complement has the specifier for sister,
which inherits only if it belongs to the head's own extended projection.

Unlike the domain Transfer seals, the complement of a phase head, a horizon closes the whole
phrase, so no element escapes through its edge.

## References

* [keine-2019]
* [keine-2020]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

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

/-- The positions closed to the search of a probe with profile `p` at `a`, those behind its
horizon; none when it has no horizon. -/
def Probe.Profile.cut (p : Probe.Profile) (a : TreePath) : Set TreePath :=
  {q | ∃ c ∈ p.horizon, q ∈ Minimalist.horizon hd t a c}

instance (p : Probe.Profile) (a : TreePath) : DecidablePred (· ∈ p.cut hd t a) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {hd t} {a q : TreePath} {c : Cat} {p : Probe.Profile}

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

@[simp] theorem Probe.Profile.cut_mk_none {head : Cat} :
    (Probe.Profile.mk head none).cut hd t a = ∅ := by
  simp [Probe.Profile.cut]

@[simp] theorem Probe.Profile.cut_mk_some {head : Cat} :
    (Probe.Profile.mk head (some c)).cut hd t a = Minimalist.horizon hd t a c := by
  simp [Probe.Profile.cut]

/-- A position is behind a probe's horizon exactly when a node the probe c-commands dominates it
and is not transparent to the probe. -/
theorem Probe.Profile.mem_cut_iff :
    q ∈ p.cut hd t a ↔ ∃ x < q, t.val.CCommands a x ∧ ¬ p.TransparentTo (spineAt hd t x) := by
  constructor
  · rintro ⟨c, hc, x, hx, ha, hm⟩
    exact ⟨x, Finset.mem_Iio.1 hx, ha, fun ht ↦ ht c hc hm⟩
  · rintro ⟨x, hx, ha, hnt⟩
    obtain ⟨c, hc, hm⟩ : ∃ c ∈ p.horizon, c ∈ spineAt hd t x := by
      simpa [Probe.Profile.TransparentTo] using hnt
    exact ⟨c, hc, x, Finset.mem_Iio.2 hx, ha, hm⟩

end Minimalist
