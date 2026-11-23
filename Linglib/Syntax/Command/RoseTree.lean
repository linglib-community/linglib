module

public import Linglib.Syntax.Command.Basic
public import Linglib.Core.Data.RoseTree.Positions

/-!
# Command relations on the positions of a rose tree

The positions of a rose tree are a dominance order, so a set of them generates a command relation
(`Linglib/Syntax/Command/Basic.lean`). The branching positions, those with at least two children,
are `RoseTree.branching`. Between positions neither of which dominates the other they generate
c-command, `RoseTree.CCommands`, which is
[sisterhood plus dominance](##RoseTree.cCommands_iff_parent_lt). Both are read off the tree, so
they are decidable, and they are unchanged by relabelling and by replacing a subtree the
commander does not dominate. C-command between two positions of a subtree is c-command in the
tree, `RoseTree.cCommands_mul_iff`, so the positions of the subtree embed in those of the tree by
`RoseTree.cCommandsEmbedding`.

## Implementation notes

The relations are stated on all of `GornAddress`, with the generators inside the tree, so that
they are decided by a walk up the commander's prefixes. On the subtype of positions the branching
positions are [the branching nodes of the order](##RoseTree.isBranching_iff_mem_branching), and
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
    a ~[C[P]] b ↔
      ∀ x ∈ a.inits, x ≠ a → x ∈ P → x ≤ b := by
  constructor
  · intro h x hx hne hP
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact h hP (lt_of_le_of_ne (GornAddress.le_def.mpr ((List.mem_inits _ _).mp hl)) hne)
  · intro h x hP hxa
    exact h x (List.mem_map.mpr
      ⟨x.toList, (List.mem_inits _ _).mpr (GornAddress.le_def.mp hxa.le), rfl⟩) hxa.ne hP

instance (P : Set GornAddress) [DecidablePred (· ∈ P)] (a b : GornAddress) :
    Decidable (a ~[C[P]] b) :=
  decidable_of_iff _ (mem_commandRelation_iff_inits P a b).symm

instance (P : Set GornAddress) [DecidablePred (· ∈ P)] (ab : GornAddress × GornAddress) :
    Decidable (ab ∈ mateRelation P) :=
  inferInstanceAs (Decidable (ab.1 ~[C[P]] ab.2 ∧ ab.2 ~[C[P]] ab.1))

end Positions

end PhraseStructure

/-! ### C-command on the positions of a rose tree -/

namespace RoseTree

open PhraseStructure
open scoped SetRel

variable {β : Type*}

/-- The branching positions of `t`, those whose subtree has at least two children: the geometric
reading of [reinhart-1976]'s "first branching node", and the generators of c-command. -/
def branching (t : RoseTree β) : Set GornAddress := positionsWhere (fun s ↦ 2 ≤ s.arity) t

theorem mem_branching {t : RoseTree β} {p : GornAddress} :
    p ∈ t.branching ↔ ∃ s ∈ t[p.toList]?, 2 ≤ s.arity := Iff.rfl

instance (t : RoseTree β) : DecidablePred (· ∈ t.branching) :=
  inferInstanceAs (DecidablePred (· ∈ positionsWhere _ t))

/-- The branching nodes of the order of positions, the mothers of two distinct nodes, are the
positions with at least two children. -/
theorem isBranching_iff_mem_branching {t : RoseTree β} (p : t.Positions) :
    IsBranching p ↔ p.val ∈ t.branching := by
  have hv : ∀ i < p.subtree.arity, p.val * .of i ∈ t.validPaths := fun i hi ↦
    mem_validPaths_append_singleton_iff.2 ⟨_, p.getElem?_eq, hi⟩
  rw [mem_branching, p.getElem?_eq]
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

/-- The branching nodes of the order of positions and the branching positions of the tree
generate the same command relation. -/
theorem mem_commandRelation_isBranching_iff {t : RoseTree β} (a b : t.Positions) :
    a ~[C[{p | IsBranching p}]] b ↔ a.val ~[C[t.branching]] b.val := by
  rw [show {p : t.Positions | IsBranching p} = Subtype.val ⁻¹' t.branching from
    Set.ext isBranching_iff_mem_branching]
  exact mem_commandRelation_preimage_iff (OrderEmbedding.subtype (· ∈ t.validPaths))
    (fun a y hya ↦ .inl ⟨⟨y, isLowerSet_validPaths t hya.le a.2⟩, rfl⟩) _

/-- `a` c-commands `b` in `t` when neither dominates the other and every branching node properly
dominating `a` dominates `b`: [reinhart-1976]'s c-command, command under the branching positions.
The positions `a` c-commands are its c-command domain. -/
abbrev CCommands (t : RoseTree β) (a b : GornAddress) : Prop :=
  Commands t.branching a b

/-- C-command is sisterhood plus dominance: a position whose parent branches c-commands exactly
the positions properly below its parent and not below itself. -/
theorem cCommands_iff_parent_lt {t : RoseTree β} {a b : GornAddress} (ha : a ≠ ⊥)
    (hp : a.parent ∈ t.branching) : CCommands t a b ↔ a.parent < b ∧ ¬ a ≤ b := by
  refine commands_iff_lt_of_covBy ?_ hp
  rw [← GornAddress.pred_eq_parent]
  exact Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha)

theorem branching_map {γ : Type*} (f : β → γ) (t : RoseTree β) :
    (t.map f).branching = t.branching := by
  ext p
  simp [branching, positionsWhere_map]

theorem cCommands_map {γ : Type*} (f : β → γ) (t : RoseTree β) (a b : GornAddress) :
    (t.map f).CCommands a b ↔ t.CCommands a b := by
  simp only [CCommands, branching_map]

section Replace

variable {t new : RoseTree β} {a b c : GornAddress}

theorem mem_branching_replaceAt {x : GornAddress} (h : ¬ c ≤ x) :
    x ∈ (t.replaceAt c new).branching ↔ x ∈ t.branching :=
  mem_positionsWhere_replaceAt (fun _ _ _ _ ↦ by simp [arity]) h new

theorem mem_commandRelation_branching_replaceAt (h : ¬ c < a) :
    a ~[C[(t.replaceAt c new).branching]] b ↔ a ~[C[t.branching]] b :=
  mem_commandRelation_congr fun _ hxa ↦ mem_branching_replaceAt fun hcx ↦ h (hcx.trans_lt hxa)

theorem cCommands_replaceAt_of_le (hcb : c ≤ b) (hca : ¬ c ≤ a) (hac : ¬ a ≤ c) :
    CCommands (t.replaceAt c new) a b ↔ CCommands t a c := by
  have hlt : ¬ c < a := fun h ↦ hca h.le
  have hab : ¬ a ≤ b := fun h ↦ (IsForestOrder.le_total_of_le_of_le h hcb).elim hac hca
  have hba : ¬ b ≤ a := fun h ↦ hca (hcb.trans h)
  simp only [CCommands, commands_iff, IncompRel, mem_commandRelation_iff_of_le hcb hlt,
    mem_commandRelation_branching_replaceAt hlt, hab, hba, hac, hca, not_false_eq_true, and_true]

theorem cCommands_replaceAt_self : CCommands (t.replaceAt c new) c a ↔ CCommands t c a := by
  simp only [CCommands, commands_iff, mem_commandRelation_branching_replaceAt (lt_irrefl c)]

end Replace

/-! ### Subtrees and sisters -/

section Subtree

variable {t s : RoseTree β} {p q : GornAddress} {i j : ℕ}

theorem mul_mem_branching_iff (h : t[p]? = some s) {x : GornAddress} :
    p * x ∈ t.branching ↔ x ∈ s.branching := by
  rw [getElem?_gornAddress] at h
  simp [mem_branching, getElem?_append, h]

/-- C-command between two positions of a subtree is c-command in the tree. -/
theorem cCommands_mul_iff (h : t[p]? = some s) {a b : GornAddress} :
    t.CCommands (p * a) (p * b) ↔ s.CCommands a b := by
  have hf : ∀ a, ∀ y < GornAddress.mulLeft p a, y ∈ Set.range (GornAddress.mulLeft p) ∨
      y ∈ lowerBounds (Set.range (GornAddress.mulLeft p)) := fun a y hy ↦ by
    rcases GornAddress.le_mul_iff.1 hy.le with hyp | ⟨q, -, rfl⟩
    · exact .inr fun _ ⟨z, hz⟩ ↦ hz ▸ hyp.trans (GornAddress.le_mul_right p z)
    · exact .inl ⟨q, rfl⟩
  rw [CCommands, CCommands, ← GornAddress.mulLeft_apply, ← GornAddress.mulLeft_apply,
    ← commands_preimage_iff _ hf]
  congr! 1
  ext x
  exact mul_mem_branching_iff h

/-- The positions of a subtree embed in those of the tree, and the embedding preserves and
reflects c-command. -/
def cCommandsEmbedding (h : t[p]? = some s) : s.CCommands ↪r t.CCommands where
  toEmbedding := (GornAddress.mulLeft p).toEmbedding
  map_rel_iff' := cCommands_mul_iff h

@[simp] theorem cCommandsEmbedding_apply (h : t[p]? = some s) (a : GornAddress) :
    cCommandsEmbedding h a = p * a := rfl

theorem not_mul_of_le_mul_of (p : GornAddress) (hij : i ≠ j) : ¬ p * .of i ≤ p * .of j :=
  fun h ↦ hij (GornAddress.of_inj_of_mul_of_le h le_rfl)

/-- A daughter of a branching node c-commands what its sisters dominate. -/
theorem cCommands_mul_of (hp : p ∈ t.branching) (hij : i ≠ j) (q : GornAddress) :
    t.CCommands (p * .of i) (p * .of j * q) :=
  commands_of_covBy_of_lt (GornAddress.covBy_mul_of p i) hp (GornAddress.lt_mul_of p j)
    (not_mul_of_le_mul_of p hij) (GornAddress.le_mul_right _ _)

/-- A position properly below a branching daughter c-commands none of the daughter's sisters. -/
theorem not_cCommands_mul_of_mul (hp : p * .of j ∈ t.branching) (hij : i ≠ j) (hq : q ≠ 1) :
    ¬ t.CCommands (p * .of j * q) (p * .of i) :=
  not_commands_of_covBy_of_lt (GornAddress.covBy_mul_of p i) hp (GornAddress.lt_mul_of p j)
    (not_mul_of_le_mul_of p hij) (lt_of_le_of_ne (GornAddress.le_mul_right _ _)
      fun e ↦ hq (mul_left_cancel (e.symm.trans (mul_one _).symm)))

end Subtree

end RoseTree
