module

public import Linglib.Morphology.DistributedMorphology.Fusion
public import Linglib.Morphology.DistributedMorphology.Impoverishment

/-!
# The spell-out pipeline

The PF branch at the level of the word: the syntax hands over a string of terminals, the
postsyntactic operations rewrite it, and Vocabulary Insertion realizes each surviving terminal in
its neighborhood. The focus-level rules (`ImpoverishmentRule` and kin) rewrite one terminal; the
operations here remove, merge, move and copy terminals, each [at the first
neighborhood](##DistributedMorphology.rewriteFirst) where it applies. Obliteration [leaves a
sublist](##DistributedMorphology.ObliterationRule.apply_sublist) of the string and Fusion [never
lengthens it](##DistributedMorphology.FusionRule.length_applyFirstAdjacent_le). The linear
operations are stated in Generalized Reduplication: brackets copy a stretch of the string, less
its left part in the first copy and its right part in the second, so that Metathesis [permutes the
terminals](##DistributedMorphology.Reduplication.apply_perm), Doubling [adds
some](##DistributedMorphology.Reduplication.sublist_apply), and the two differ by one bracket.
Insertion has [one position for each terminal the operations
leave](##DistributedMorphology.Spellout.length_pf).

A focus-level rule can be timed against insertion: applied to the string before insertion, where
the terminals beside a rewritten one see it rewritten, or to each terminal at its own insertion
only, where they see it as it was. [The two timings give the same exponents where insertion reads
the focus alone](##DistributedMorphology.Spellout.pf_rewriteBefore_eq_pf_rewriteAt).

## Implementation notes

* Every operation here applies to the linearized string. [arregi-nevins-2012] order Linearization
  after Feature Markedness, where Obliteration applies, and [halle-marantz-1993] fuse sister
  nodes; on a string these are stated over a neighborhood and over adjacent terminals.
* The brackets of Generalized Reduplication are given by the lengths of the three stretches they
  delimit. The sources' rules place the two angled brackets at one juncture; here they may stand
  apart, each with the effect the sources give it alone.
* `Spellout.postsyntax` is one map, the modules composed in their order.

## TODO

* The operations before Linearization as maps of the hierarchical object, composed before the
  handover of `LateInsertion.lean`; Lowering before Linearization and Local Dislocation after it
  ([embick-noyer-2001]).
* The LF branch: an interpretation that reads the string the syntax hands over.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [J. Harris and M. Halle, *Unexpected plural inflections in Spanish*][harris-halle-2005]
* [D. Embick and R. Noyer, *Movement operations after syntax*][embick-noyer-2001]
-/

@[expose] public section

namespace DistributedMorphology

/-- A spell-out domain is the linear sequence of terminals the syntax hands over at
spell-out. -/
abbrev SpelloutDomain (Bundle : Type*) := List Bundle

variable {Bundle : Type*}

open Neighborhood

/-! ### Rewriting at the first neighborhood -/

/-- `rewriteFirst f d` replaces the domain `d` by the value of `f` at its first neighborhood,
scanning left to right, where `f` has one, and leaves it unchanged if there is none. Obliteration,
Generalized Reduplication, and the domain lift of Fusion are its instances. -/
def rewriteFirst (f : Neighborhood Bundle → Option (SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) : SpelloutDomain Bundle :=
  ((along d).findSome? f).getD d

section RewriteFirst

variable {f : Neighborhood Bundle → Option (SpelloutDomain Bundle)} {d : SpelloutDomain Bundle}

/-- What holds of a domain, and of every rewrite of a neighborhood that reassembles to it, holds
of the rewritten domain. -/
theorem rewriteFirst_induction {C : SpelloutDomain Bundle → Prop} (self : C d)
    (step : ∀ n l, n.toList = d → f n = some l → C l) : C (rewriteFirst f d) := by
  unfold rewriteFirst
  cases h : (along d).findSome? f with
  | none => exact self
  | some l =>
    obtain ⟨n, hn, hf⟩ := List.exists_of_findSome?_eq_some h
    exact step n l (toList_of_mem_along d hn) hf

theorem rewriteFirst_of_forall_eq_none (h : ∀ n ∈ along d, f n = none) : rewriteFirst f d = d := by
  rw [rewriteFirst, List.findSome?_eq_none_iff.2 h, Option.getD_none]

@[simp] theorem rewriteFirst_nil : rewriteFirst f [] = [] := rfl

end RewriteFirst

/-! ### Obliteration -/

/-- An obliteration rule, in the sense of [arregi-nevins-2012], removes outright the terminal
whose neighborhood satisfies `condition`. The focus-level `ImpoverishmentRule` deletes a feature
inside a terminal, and this rule deletes the terminal. -/
structure ObliterationRule (Bundle : Type*) where
  /-- The neighborhoods whose focus is removed. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]

namespace ObliterationRule

instance (rule : ObliterationRule Bundle) : DecidablePred rule.condition := rule.decCond

/-- Applying the rule drops the first terminal whose neighborhood satisfies its condition, and
otherwise leaves the domain unchanged. -/
def apply (rule : ObliterationRule Bundle) : SpelloutDomain Bundle → SpelloutDomain Bundle :=
  rewriteFirst fun n ↦ if rule.condition n then some (n.leftCtx.reverse ++ n.rightCtx) else none

/-- Obliteration only removes terminals. -/
theorem apply_sublist (rule : ObliterationRule Bundle) (d : SpelloutDomain Bundle) :
    (rule.apply d).Sublist d :=
  rewriteFirst_induction (C := (·.Sublist d)) (.refl d) fun n l hn hl ↦ by
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_right_eq_some.1 hl
    exact hn ▸ (List.sublist_cons_self _ _).append_left _

theorem length_apply_le (rule : ObliterationRule Bundle) (d : SpelloutDomain Bundle) :
    (rule.apply d).length ≤ d.length :=
  (rule.apply_sublist d).length_le

end ObliterationRule

/-! ### Generalized Reduplication -/

/-- The brackets of Generalized Reduplication, the formalism of [harris-halle-2005] in which
[arregi-nevins-2012] state the linear operations. Double brackets enclose the stretch of the
string that is copied; a right angled bracket inside them deletes what is to its left from the
first copy, and a left angled bracket deletes what is to its right from the second. The brackets
are given by the lengths of the three stretches they delimit, from the opening double bracket. -/
structure Reduplication where
  /-- The length of the stretch missing from the first copy. -/
  left : ℕ
  /-- The length of the stretch in both copies. -/
  mid : ℕ
  /-- The length of the stretch missing from the second copy. -/
  right : ℕ
  deriving DecidableEq, Repr

namespace Reduplication

variable {α : Type*} (b : Reduplication) (s : List α)

/-- Metathesis: the two angled brackets at one juncture, so that neither copy keeps what the
other has and the two stretches change places. -/
abbrev metathesis (left right : ℕ) : Reduplication := ⟨left, 0, right⟩

/-- Doubling: the right angled bracket alone, so that the stretch after it is pronounced before
the copied stretch and again inside it. -/
abbrev doubling (left mid : ℕ) : Reduplication := ⟨left, mid, 0⟩

/-- The string with the brackets opening at its left edge: the first copy, without the left
stretch, then the second, without the right stretch, then what follows the brackets. -/
def apply : List α :=
  (s.drop b.left).take (b.mid + b.right) ++ s.take (b.left + b.mid) ++
    s.drop (b.left + b.mid + b.right)

/-- Metathesis permutes the terminals. -/
theorem apply_perm (h : b.mid = 0) : (b.apply s).Perm s := by
  have hs : s.take b.left ++ (s.drop b.left).take b.right ++ s.drop (b.left + b.right) = s := by
    rw [← List.take_add, List.take_append_drop]
  simpa [apply, h] using (List.perm_append_comm.append_right _).trans (.of_eq hs)

/-- Doubling keeps every terminal where it was and adds the copies. -/
theorem sublist_apply (h : b.right = 0) : s.Sublist (b.apply s) := by
  simp [apply, h]

/-- Brackets within the string add the terminals in both copies. -/
theorem length_apply (h : b.left + b.mid + b.right ≤ s.length) :
    (b.apply s).length = s.length + b.mid := by
  simp only [apply, List.length_append, List.length_take, List.length_drop]
  omega

end Reduplication

/-- `reduplicateFirst sd` applies Generalized Reduplication at the first neighborhood for which
the structural description `sd` gives brackets, the opening double bracket standing before the
focus, and otherwise leaves the domain unchanged. -/
def reduplicateFirst (sd : Neighborhood Bundle → Option Reduplication) :
    SpelloutDomain Bundle → SpelloutDomain Bundle :=
  rewriteFirst fun n ↦ (sd n).map fun b ↦ n.leftCtx.reverse ++ b.apply (n.focus :: n.rightCtx)

/-- A rule of Metathesis permutes the terminals of the domain. -/
theorem reduplicateFirst_perm {sd : Neighborhood Bundle → Option Reduplication}
    (h : ∀ n, ∀ b ∈ sd n, b.mid = 0) (d : SpelloutDomain Bundle) :
    (reduplicateFirst sd d).Perm d :=
  rewriteFirst_induction (C := (·.Perm d)) (.refl d) fun n l hn hl ↦ by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact hn ▸ (b.apply_perm _ (h n b hb)).append_left _

theorem length_reduplicateFirst {sd : Neighborhood Bundle → Option Reduplication}
    (h : ∀ n, ∀ b ∈ sd n, b.mid = 0) (d : SpelloutDomain Bundle) :
    (reduplicateFirst sd d).length = d.length :=
  (reduplicateFirst_perm h d).length_eq

/-! ### Fusion -/

namespace FusionRule

variable {F : Type*} [DecidableEq F]

/-- The domain lift of Fusion fuses the first terminal that fuses with the terminal to its right,
and otherwise leaves the domain unchanged. -/
def applyFirstAdjacent (rule : FusionRule F) :
    SpelloutDomain (Finset F) → SpelloutDomain (Finset F) :=
  rewriteFirst fun
    | ⟨p, l, q :: r⟩ => (rule.apply p q).map fun pq ↦ l.reverse ++ pq :: r
    | _ => none

theorem length_applyFirstAdjacent_le (rule : FusionRule F) (d : SpelloutDomain (Finset F)) :
    (rule.applyFirstAdjacent d).length ≤ d.length :=
  rewriteFirst_induction (C := (·.length ≤ d.length)) le_rfl fun n l hn hl ↦ by
    obtain ⟨p, lc, _ | ⟨q, r⟩⟩ := n
    · exact absurd hl nofun
    · obtain ⟨pq, -, rfl⟩ := Option.map_eq_some_iff.1 hl
      simp [← hn, Neighborhood.toList]

end FusionRule

/-! ### The pipeline -/

/-- A PF-branch pipeline runs the postsyntactic modules over a spell-out domain, then Vocabulary
Insertion at each surviving position in its neighborhood. -/
structure Spellout (Bundle F : Type*) where
  /-- The postsyntactic modules, composed in their order. -/
  postsyntax : SpelloutDomain Bundle → SpelloutDomain Bundle := id
  /-- The exponents inserted at a position, which sees its neighbors. There is one, several
  under Fission, or none at a position that licenses none. -/
  insert : Neighborhood Bundle → List F

namespace Spellout

variable {F : Type*}

/-- The PF output has one insertion slot per surviving position. -/
def pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) : List (List F) :=
  (along (s.postsyntax d)).map s.insert

/-- Exponent slots equal terminals after the modules, so the exponent count diverges from the
syntactic terminal count only through the modules. -/
@[simp] theorem length_pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    (s.pf d).length = (s.postsyntax d).length := by
  simp [pf]

/-! ### The timing of a focus-level rule -/

variable (r : Neighborhood Bundle → Bundle) (s : Spellout Bundle F)

/-- `s.rewriteBefore r` applies the focus-level rule `r` to every terminal after the modules of
`s` and before insertion, so that a terminal beside a rewritten one sees it rewritten. -/
def rewriteBefore : Spellout Bundle F :=
  { s with postsyntax := fun d ↦ (along (s.postsyntax d)).map r }

/-- `s.rewriteAt r` applies the focus-level rule `r` to each terminal at its own insertion only,
so that a terminal beside it sees it as it was. -/
def rewriteAt : Spellout Bundle F :=
  { s with insert := fun n ↦ s.insert { n with focus := r n } }

@[simp] theorem postsyntax_rewriteBefore (d : SpelloutDomain Bundle) :
    (s.rewriteBefore r).postsyntax d = (along (s.postsyntax d)).map r := rfl

@[simp] theorem postsyntax_rewriteAt : (s.rewriteAt r).postsyntax = s.postsyntax := rfl

@[simp] theorem insert_rewriteBefore : (s.rewriteBefore r).insert = s.insert := rfl

@[simp] theorem insert_rewriteAt (n : Neighborhood Bundle) :
    (s.rewriteAt r).insert n = s.insert { n with focus := r n } := rfl

/-- The timing of a focus-level rule matters only to insertion that reads the context. Where
insertion reads the focus alone, the rule yields the same exponents applied before insertion and
at insertion. -/
theorem pf_rewriteBefore_eq_pf_rewriteAt (hs : s.insert.FactorsThrough focus)
    (d : SpelloutDomain Bundle) : (s.rewriteBefore r).pf d = (s.rewriteAt r).pf d := by
  rw [pf, pf, postsyntax_rewriteBefore, postsyntax_rewriteAt, insert_rewriteBefore,
    map_along_of_factorsThrough _ hs, List.map_map]
  exact List.map_congr_left fun _ _ ↦ hs rfl

end Spellout

end DistributedMorphology
