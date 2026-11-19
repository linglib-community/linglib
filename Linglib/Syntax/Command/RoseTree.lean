module

public import Linglib.Syntax.Command
public import Linglib.Core.Data.RoseTree.Positions

/-!
# Command relations on the positions of a rose tree

The positions of a rose tree are a dominance order, so a set of them generates a command relation
(`Linglib/Syntax/Command.lean`). The branching positions, those with at least two children,
generate Barker and Pullum's c-command, `RoseTree.cCommand`, and between positions neither of
which dominates the other Reinhart's, `RoseTree.CCommands`, which is
[sisterhood plus dominance](##RoseTree.cCommands_iff_parent_lt). Both are read off the tree, so
they are decidable, and they are unchanged by relabelling and by replacing a subtree the
commander does not dominate.

## Implementation notes

The relations are stated on all of `GornAddress`, with the generators inside the tree, so that
they are decided by a walk up the commander's prefixes. On the subtype of positions the branching
positions are [the branching nodes of the order](##RoseTree.isBranching_iff_isBranchingAt), and
the two command relations [agree](##RoseTree.mem_commandRelation_isBranching_iff).

## References

* [barker-pullum-1990]
* [reinhart-1976]
-/

@[expose] public section

namespace PhraseStructure

open Order Set
open scoped SetRel

/-! ### Command relations on the positions of a tree

Membership in `commandRelation P` at concrete positions is decidable: the nodes properly
dominating a position are its proper prefixes, a finite list, so the defining universal is a
`List`-bounded one. -/

section Positions

open RoseTree

theorem mem_commandRelation_iff_inits (P : Set GornAddress) (a b : GornAddress) :
    a ~[commandRelation P] b ↔
      ∀ x ∈ a.inits, x ≠ a → x ∈ P → x ≤ b := by
  constructor
  · intro h x hx hne hP
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact h hP (lt_of_le_of_ne (GornAddress.le_def.mpr ((List.mem_inits _ _).mp hl)) hne)
  · intro h x hP hxa
    exact h x (List.mem_map.mpr
      ⟨x.toList, (List.mem_inits _ _).mpr (GornAddress.le_def.mp hxa.le), rfl⟩) hxa.ne hP

instance (P : Set GornAddress) [DecidablePred (· ∈ P)] (a b : GornAddress) :
    Decidable (a ~[commandRelation P] b) :=
  decidable_of_iff _ (mem_commandRelation_iff_inits P a b).symm

instance (P : Set GornAddress) [DecidablePred (· ∈ P)] (ab : GornAddress × GornAddress) :
    Decidable (ab ∈ mateRelation P) :=
  inferInstanceAs (Decidable (ab.1 ~[commandRelation P] ab.2 ∧ ab.2 ~[commandRelation P] ab.1))

end Positions

end PhraseStructure

/-! ### C-command on the positions of a rose tree -/

namespace RoseTree

open PhraseStructure
open scoped SetRel

variable {β : Type*}

/-- A position of `t` is **branching** when its subtree has at least two children, the
geometric reading of [reinhart-1976]'s "first branching node". -/
def IsBranchingAt (t : RoseTree β) (p : GornAddress) : Prop :=
  p ∈ positionsWhere (fun s ↦ 2 ≤ s.arity) t

instance (t : RoseTree β) (p : GornAddress) : Decidable (t.IsBranchingAt p) :=
  inferInstanceAs (Decidable (p ∈ positionsWhere _ t))

/-- Barker and Pullum's c-command on the positions of `t`, the command relation its branching
positions generate. It is reflexive and a position commands what it dominates, unlike
`RoseTree.CCommands`; it is read off the tree, so decidable. -/
abbrev cCommand (t : RoseTree β) : SetRel GornAddress GornAddress :=
  commandRelation {p | t.IsBranchingAt p}

/-- The branching nodes of the order of positions, the mothers of two distinct nodes, are the
positions with at least two children. -/
theorem isBranching_iff_isBranchingAt {t : RoseTree β} (p : t.Positions) :
    IsBranching p ↔ IsBranchingAt t p.val := by
  have hv : ∀ i < p.subtree.arity, p.val * .of i ∈ t.validPaths := fun i hi ↦
    mem_validPaths_append_singleton_iff.2 ⟨_, p.getElem?_eq, hi⟩
  rw [IsBranchingAt, mem_positionsWhere, p.getElem?_eq]
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left']
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨i, hi, hai⟩ := Positions.covBy_iff_exists_lt.1 ha
    obtain ⟨j, hj, hbj⟩ := Positions.covBy_iff_exists_lt.1 hb
    have hij : i ≠ j := fun h ↦ hab (Subtype.ext (hai.trans (h ▸ hbj.symm)))
    omega
  · intro h
    refine ⟨⟨_, hv 0 (by omega)⟩, Positions.covBy_iff_exists_lt.2 ⟨0, by omega, rfl⟩,
      ⟨_, hv 1 (by omega)⟩, Positions.covBy_iff_exists_lt.2 ⟨1, by omega, rfl⟩, fun e ↦ ?_⟩
    simpa using congrArg (fun q : t.Positions ↦ q.val.toList) e

/-- The command relation the branching nodes of the order of positions generate is
`RoseTree.cCommand`. -/
theorem mem_commandRelation_isBranching_iff {t : RoseTree β} (a b : t.Positions) :
    a ~[commandRelation {p | IsBranching p}] b ↔ a.val ~[t.cCommand] b.val := by
  rw [show {p : t.Positions | IsBranching p} = Subtype.val ⁻¹' {p | IsBranchingAt t p} from
    Set.ext isBranching_iff_isBranchingAt]
  exact mem_commandRelation_preimage_iff (OrderEmbedding.subtype (· ∈ t.validPaths))
    (fun a y hya ↦ .inl ⟨⟨y, isLowerSet_validPaths t hya.le a.2⟩, rfl⟩) _

/-- `a` c-commands `b` in `t` when neither dominates the other and every branching node properly
dominating `a` dominates `b`: [reinhart-1976]'s c-command, command under the branching positions.
The positions `a` c-commands are its c-command domain. -/
abbrev CCommands (t : RoseTree β) (a b : GornAddress) : Prop :=
  Commands {p | t.IsBranchingAt p} a b

/-- C-command is sisterhood plus dominance: a position whose parent branches c-commands exactly
the positions properly below its parent and not below itself. -/
theorem cCommands_iff_parent_lt {t : RoseTree β} {a b : GornAddress} (ha : a ≠ ⊥)
    (hp : IsBranchingAt t a.parent) : CCommands t a b ↔ a.parent < b ∧ ¬ a ≤ b := by
  refine commands_iff_lt_of_covBy ?_ hp
  rw [← GornAddress.pred_eq_parent]
  exact Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha)

theorem isBranchingAt_map {γ : Type*} (f : β → γ) (t : RoseTree β) (p : GornAddress) :
    IsBranchingAt (t.map f) p ↔ IsBranchingAt t p := by
  simp [IsBranchingAt, positionsWhere_map]

theorem cCommand_map {γ : Type*} (f : β → γ) (t : RoseTree β) :
    cCommand (t.map f) = cCommand t := by
  simp only [cCommand, isBranchingAt_map]

theorem cCommands_map {γ : Type*} (f : β → γ) (t : RoseTree β) (a b : GornAddress) :
    (t.map f).CCommands a b ↔ t.CCommands a b := by
  simp only [CCommands, isBranchingAt_map]

section Replace

variable {t new : RoseTree β} {a b c : GornAddress}

theorem isBranchingAt_replaceAt {x : GornAddress} (h : ¬ c ≤ x) :
    IsBranchingAt (t.replaceAt c new) x ↔ IsBranchingAt t x :=
  mem_positionsWhere_replaceAt (fun _ _ _ _ ↦ by simp [arity]) h new

theorem mem_cCommand_replaceAt (h : ¬ c < a) :
    a ~[cCommand (t.replaceAt c new)] b ↔ a ~[cCommand t] b :=
  mem_commandRelation_congr fun _ hxa ↦ isBranchingAt_replaceAt fun hcx ↦ h (hcx.trans_lt hxa)

theorem cCommands_replaceAt_of_le (hcb : c ≤ b) (hca : ¬ c ≤ a) (hac : ¬ a ≤ c) :
    CCommands (t.replaceAt c new) a b ↔ CCommands t a c := by
  have hlt : ¬ c < a := fun h ↦ hca h.le
  have hab : ¬ a ≤ b := fun h ↦ (IsForestOrder.le_total_of_le_of_le h hcb).elim hac hca
  have hba : ¬ b ≤ a := fun h ↦ hca (hcb.trans h)
  simp only [CCommands, commands_iff, IncompRel, mem_commandRelation_iff_of_le hcb hlt,
    mem_cCommand_replaceAt hlt, hab, hba, hac, hca, not_false_eq_true, and_true]

theorem cCommands_replaceAt_self : CCommands (t.replaceAt c new) c a ↔ CCommands t c a := by
  simp only [CCommands, commands_iff, mem_cCommand_replaceAt (lt_irrefl c)]

end Replace

end RoseTree
