module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Minimal search over syntactic objects

This file instantiates probe search at the tree: a probe on the head at a position of a
linearized object searches the positions the head c-commands in some order, a key on positions.
Closest by the branching positions above them, it finds a goal that no other satisfier
asymmetrically c-commands: the Minimal Link Condition, with mutually c-commanding candidates
equidistant. Procedural search orders are in `Probe/Search.lean`. Positions closed to the search,
by the PIC or by a horizon, cut its domain. Agree and labeling are both this search; what Agree
then does to the features of the probe and the goal is `Minimalist.FeatureState.value`.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.goalsBy`, `goals`, `goalsUnder`: the terms a probe on a
  head finds under a search order, under closeness, and with some positions closed to it.
* `Minimalist.LinearizedSyntacticObject.leafProbe`, `phraseProbe`: the probes satisfied by the
  leaves of a category, and by the phrases its heads form.

## Main results

* `Minimalist.LinearizedSyntacticObject.not_finds_of_cCommands`: a satisfier that asymmetrically
  c-commands a position blocks the goal there.
* `Minimalist.LinearizedSyntacticObject.finds_above_branching_iff`: among satisfiers none of which
  dominates another, a probe finds those that no satisfier asymmetrically c-commands.
* `Minimalist.LinearizedSyntacticObject.mem_goals_leafProbe_map_iff`: a probe for the leaves of
  a category finds the same goals under an injective relabelling that keeps categories.

## References

* [chomsky-1995], [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

/-! ### Closest goals

A probe on the head at a position searches the positions the head c-commands, keyed by the
branching positions above each (`LinearizedSyntacticObject.above`), and finds a goal minimal under
the key, the Minimal Link Condition of [chomsky-1995]. -/

namespace LinearizedSyntacticObject

variable {t : LinearizedSyntacticObject} {p : Probe t.val.Positions} {s : Set t.val.Positions}
  {q g : t.val.Positions}

/-- A satisfier that asymmetrically c-commands a position blocks the goal there, whatever else the
probe's domain holds. -/
theorem not_finds_of_cCommands (hq : q ∈ s) (hsq : p.sat q) (hqg : t.val.CCommands q g)
    (hgq : ¬ t.val.CCommands g q) : ¬ p.Finds s (t.above t.branching) g := fun h ↦
  h.inspects.2 hq hsq (above_branching_lt_of_cCommands hqg hgq)

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
asymmetrically c-commands: mutually c-commanding candidates are equidistant. -/
theorem finds_above_branching_iff (hs : IsAntichain (· ≤ ·) {q | q ∈ s ∧ p.sat q}) :
    p.Finds s (t.above t.branching) g ↔ (g ∈ s ∧ p.sat g) ∧
      ∀ ⦃q⦄, q ∈ s → p.sat q → ¬ (t.val.CCommands q g ∧ ¬ t.val.CCommands g q) := by
  simpa only [Probe.Finds, and_imp] using minimalFor_iff_of_isAntichain hs (fun _ h ↦ h.2 h.1)
    fun _ _ ↦ above_branching_lt_iff

section Search

variable {β : Type*} [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]

variable (t) in
/-- The terms a probe on the head `h` finds when its search orders positions by `key`: those at
the first satisfying positions that an occurrence of `h` c-commands. -/
def goalsBy (p : Probe t.val.Positions) (h : SyntacticObject) (key : t.val.Positions → β) :
    Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q} key g).image t.termAt

theorem mem_goalsBy {h x : SyntacticObject} {key : t.val.Positions → β} :
    x ∈ t.goalsBy p h key ↔
      ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} key g ∧ t.termAt g = x := by
  simp only [goalsBy, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, ⟨a, ha, hg⟩, hx⟩ ↦ ⟨a, ha, g, hg, hx⟩,
    fun ⟨a, ha, g, hg, hx⟩ ↦ ⟨g, ⟨a, ha, hg⟩, hx⟩⟩

end Search

variable (t) in
/-- The terms a probe on the head `h` finds: those at the closest satisfying positions that an
occurrence of `h` c-commands. -/
def goals (p : Probe t.val.Positions) (h : SyntacticObject) : Finset SyntacticObject :=
  t.goalsBy p h (t.above t.branching)

theorem mem_goals {h x : SyntacticObject} : x ∈ t.goals p h ↔
    ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} (t.above t.branching) g ∧
      t.termAt g = x :=
  mem_goalsBy

variable (t) in
/-- The terms a probe on the head `h` finds when, at each occurrence `a` of `h`, the positions
`cut a` are closed to its search, by the PIC or by a horizon. -/
def goalsUnder (p : Probe t.val.Positions) (h : SyntacticObject)
    (cut : Core.Order.TreePath → Set Core.Order.TreePath) [∀ a, DecidablePred (· ∈ cut a)] :
    Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q ∧ q.val ∉ cut a.val} (t.above t.branching) g).image t.termAt

@[simp] theorem goalsUnder_empty {h : SyntacticObject} :
    t.goalsUnder p h (fun _ ↦ ∅) = t.goals p h := by
  simp only [goalsUnder, goals, goalsBy, Set.mem_empty_iff_false, not_false_eq_true, and_true]

theorem mem_goalsUnder_of_finds {h : SyntacticObject}
    {cut : Core.Order.TreePath → Set Core.Order.TreePath}
    [∀ a, DecidablePred (· ∈ cut a)] {a : t.val.Positions} (ha : t.termAt a = h)
    (hg : p.Finds {q | t.val.CCommands a q} (t.above t.branching) g) (hgc : g.val ∉ cut a.val) :
    t.termAt g ∈ t.goalsUnder p h cut := by
  simp only [goalsUnder, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨g, ⟨a, ha, hg.of_subset (fun _ hq ↦ hq.1) ⟨hg.mem, hgc⟩⟩, rfl⟩

variable (t) in
/-- The probe satisfied by the leaves of category `c`. -/
def leafProbe (c : Cat) : Probe t.val.Positions :=
  .relativized fun q ↦ decide (SyntacticObject.isLeafOf c (t.termAt q))

variable (t) in
/-- The probe satisfied by the phrases a head of category `c` forms with its sister, so that a
phrase in a specifier is closer than whatever its sister contains. -/
def phraseProbe (c : Cat) : Probe t.val.Positions :=
  .relativized fun q ↦
    decide (∃ e : t.val.Positions, e ≠ ⊥ ∧ e.val.parent = q.val ∧
      SyntacticObject.isLeafOf c (t.termAt e))

/-- A probe for the leaves of a category finds the relabelled goals in a relabelled object, under
an injective relabelling that keeps categories. -/
theorem mem_goals_leafProbe_map_iff {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) (hcat : ∀ t, (f t).item.cat = t.item.cat) {c : Cat}
    {h x : SyntacticObject} :
    x.map f ∈ (t.map f).goals ((t.map f).leafProbe c) (h.map f) ↔
      x ∈ t.goals (t.leafProbe c) h := by
  let e : t.val.Positions ≃ (t.map f).val.Positions :=
    Equiv.subtypeEquivRight fun p ↦ by simp only [val_map, RoseTree.validPaths_map]
  have hsub (q : t.val.Positions) :
      (e q).subtree = RoseTree.map (SyntacticObject.Vertex.map f) q.subtree :=
    Option.some.inj <| (e q).getElem?_eq.symm.trans <|
      (RoseTree.getElem?_map _ t.val q.val.toList).trans (by rw [q.getElem?_eq, Option.map_some])
  have hterm (q : t.val.Positions) : (t.map f).termAt (e q) = (t.termAt q).map f :=
    Subtype.ext <| show UnorderedTree.mk (e q).subtree = (UnorderedTree.mk q.subtree).map _ by
      rw [hsub, UnorderedTree.map_mk]
  have hcc (a q : t.val.Positions) : (t.map f).val.CCommands (e a) (e q) ↔ t.val.CCommands a q :=
    RoseTree.cCommands_map _ _ _ _
  have hkey (q : t.val.Positions) :
      (t.map f).above (t.map f).branching (e q) = t.above t.branching q :=
    Finset.filter_congr fun x _ ↦ RoseTree.isBranchingAt_map _ t.val x
  have hfinds (a g : t.val.Positions) :
      ((t.map f).leafProbe c).Finds {q | (t.map f).val.CCommands (e a) q}
          ((t.map f).above (t.map f).branching) (e g) ↔
        (t.leafProbe c).Finds {q | t.val.CCommands a q} (t.above t.branching) g := by
    simp only [Probe.Finds, MinimalFor, e.surjective.forall, Set.mem_ofPred_eq, hcc, hkey,
      leafProbe, Probe.relativized_sat, hterm, SyntacticObject.isLeafOf_map hcat]
  rw [mem_goals, mem_goals, e.surjective.exists]
  simp only [hterm, (SyntacticObject.map_injective hf).eq_iff, e.surjective.exists, hfinds]

end LinearizedSyntacticObject

end Minimalist
