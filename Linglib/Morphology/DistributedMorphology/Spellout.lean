module

public import Linglib.Morphology.DistributedMorphology.Fusion
public import Linglib.Morphology.DistributedMorphology.Impoverishment

/-!
# The spell-out pipeline

The PF branch of the Y-model at the domain level: a spell-out domain is
the sequence of terminals the syntax hands over, the postsyntactic modules
transform it, and Vocabulary Insertion realizes what survives, each
position in its neighborhood; the module inventory and its ordering follow
the Basque morphotactics. The focus-level rule types
(`ImpoverishmentRule` and kin) rewrite one terminal inside
its `Neighborhood`; the operations here move, remove, and merge the
terminals themselves, which no focus-level rule can express. Each is a
rewrite of the domain at the first of its neighborhoods (`Neighborhood.along`)
that satisfies the rule's condition.

Each operation carries its position-count law, so terminal/exponent
misalignment is arithmetic: terminal metathesis preserves the count,
obliteration and fusion never increase it, and
`Spellout.length_pf` says insertion positions equal terminals after the
modules — Fission multiplies exponents within a position (`scansion`),
not positions. `winner?_retreat` (`VocabularyInsertion/Basic.lean`) supplies the
insertion-side ordering law.

A focus-level rule can also be timed against insertion: applied to the
domain before insertion, where the terminals beside a rewritten one see it
rewritten, or to each terminal at its own insertion only, where they see it
as it was. The two timings differ only for insertion that reads the context.

## Main definitions

* `SpelloutDomain`, `rewriteFirst`: the domain, and rewriting it at its first neighborhood
  satisfying a condition.
* `ObliterationRule`, `TerminalMetathesisRule`: whole-terminal deletion and adjacent-terminal
  swap, each a decidable condition on a neighborhood.
* `FusionRule.applyFirstAdjacent`: the domain lift of Fusion.
* `Spellout`, `Spellout.run`, `Spellout.pf`: the module sequence, then insertion in context.
* `Spellout.rewriteBefore`, `Spellout.rewriteAt`: a focus-level rule applied before insertion,
  and at each terminal's own insertion.

## Main results

* `length_rewriteFirst_le`, `length_rewriteFirst`: the count laws, which hold because each
  neighborhood reassembles to the domain (`Neighborhood.toList_of_mem_along`).
* `Spellout.length_pf`: insertion positions equal terminals after the modules.
* `Spellout.pf_rewriteBefore_eq_pf_rewriteAt`: the two timings of a focus-level rule give the
  same exponents where insertion reads the focus alone.

## TODO

* The LF branch: an `Interpreted` extension whose interpretation reads
  the input domain (the Y-model separation by type), seeded by the
  domain-level allosemy licensing of `Studies/Benz2025.lean`.
* Stratifying the module list by linearization — Lowering before,
  Local Dislocation after.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
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

/-- `rewriteFirst p f d` replaces the domain `d` by `f n` for its first neighborhood `n`
satisfying `p`, scanning left to right, and leaves it unchanged if there is none. Obliteration,
terminal metathesis, and the domain lift of Fusion are its instances. -/
def rewriteFirst (p : Neighborhood Bundle → Prop) [DecidablePred p]
    (f : Neighborhood Bundle → SpelloutDomain Bundle) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  ((along d).find? fun n ↦ decide (p n)).elim d f

section RewriteFirst

variable {p : Neighborhood Bundle → Prop} [DecidablePred p]
  {f : Neighborhood Bundle → SpelloutDomain Bundle}

theorem length_rewriteFirst_le (hf : ∀ n, (f n).length ≤ n.toList.length)
    (d : SpelloutDomain Bundle) : (rewriteFirst p f d).length ≤ d.length := by
  unfold rewriteFirst
  cases h : (along d).find? fun n ↦ decide (p n) with
  | none => exact le_rfl
  | some n => simpa [toList_of_mem_along d (List.mem_of_find?_eq_some h)] using hf n

theorem length_rewriteFirst (hf : ∀ n, (f n).length = n.toList.length)
    (d : SpelloutDomain Bundle) : (rewriteFirst p f d).length = d.length := by
  unfold rewriteFirst
  cases h : (along d).find? fun n ↦ decide (p n) with
  | none => rfl
  | some n => simpa [toList_of_mem_along d (List.mem_of_find?_eq_some h)] using hf n

end RewriteFirst

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
  rewriteFirst rule.condition fun n ↦ n.leftCtx.reverse ++ n.rightCtx

theorem length_apply_le (rule : ObliterationRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length ≤ d.length :=
  length_rewriteFirst_le (fun n ↦ by simp [Neighborhood.toList]) d

end ObliterationRule

/-- A terminal metathesis rule, the terminal-order metathesis of [arregi-nevins-2012]'s
Metathesis module, swaps the focus of a neighborhood satisfying `condition` with the terminal to
its right. -/
structure TerminalMetathesisRule (Bundle : Type*) where
  /-- The neighborhoods whose focus swaps with the terminal to its right. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]

namespace TerminalMetathesisRule

instance (rule : TerminalMetathesisRule Bundle) : DecidablePred rule.condition := rule.decCond

/-- Applying the rule swaps the first focus that has a terminal to its right and whose
neighborhood satisfies its condition with that terminal, and otherwise leaves the domain
unchanged. -/
def apply (rule : TerminalMetathesisRule Bundle) :
    SpelloutDomain Bundle → SpelloutDomain Bundle :=
  rewriteFirst (fun n ↦ n.rightCtx ≠ [] ∧ rule.condition n) fun
    | ⟨t₁, l, t₂ :: r⟩ => l.reverse ++ t₂ :: t₁ :: r
    | n => n.toList

@[simp] theorem length_apply (rule : TerminalMetathesisRule Bundle)
    (d : SpelloutDomain Bundle) : (rule.apply d).length = d.length :=
  length_rewriteFirst (fun | ⟨_, _, _ :: _⟩ => by simp [Neighborhood.toList]
                           | ⟨_, _, []⟩ => rfl) d

end TerminalMetathesisRule

namespace FusionRule

variable {F : Type*} [DecidableEq F]

/-- The domain lift of Fusion fuses the first terminal that fuses with the terminal to its right,
and otherwise leaves the domain unchanged. -/
def applyFirstAdjacent (rule : FusionRule F) :
    SpelloutDomain (Finset F) → SpelloutDomain (Finset F) :=
  rewriteFirst (fun n ↦ ∃ q ∈ n.rightCtx.head?, rule.condition n.focus q) fun
    | ⟨p, l, q :: r⟩ => l.reverse ++ (p ∪ q) :: r
    | n => n.toList

theorem length_applyFirstAdjacent_le (rule : FusionRule F) (d : SpelloutDomain (Finset F)) :
    (rule.applyFirstAdjacent d).length ≤ d.length :=
  length_rewriteFirst_le (fun | ⟨_, _, _ :: _⟩ => by simp [Neighborhood.toList]
                              | ⟨_, _, []⟩ => le_rfl) d

end FusionRule

/-- Run an ordered module sequence over a domain. The order of the list
is the theory's architectural claim ([arregi-nevins-2012]'s strict
sequence; the Basque ordering witness in `Studies/Middleton2026.lean`
shows reordering it has empirical content). -/
def runModules (modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) : SpelloutDomain Bundle :=
  modules.foldl (fun d m ↦ m d) d

theorem runModules_append
    (m₁ m₂ : List (SpelloutDomain Bundle → SpelloutDomain Bundle))
    (d : SpelloutDomain Bundle) :
    runModules (m₁ ++ m₂) d = runModules m₂ (runModules m₁ d) := by
  simp [runModules, List.foldl_append]

@[simp] theorem runModules_nil (d : SpelloutDomain Bundle) :
    runModules ([] : List (SpelloutDomain Bundle → SpelloutDomain Bundle)) d
      = d := rfl

/-- A PF-branch pipeline runs the ordered postsyntactic modules over a spell-out domain, then
Vocabulary Insertion at each surviving position in its neighborhood. -/
structure Spellout (Bundle F : Type*) where
  /-- The ordered postsyntactic module sequence. -/
  modules : List (SpelloutDomain Bundle → SpelloutDomain Bundle)
  /-- The exponents inserted at a position, which sees its neighbors. There is one, several
  under Fission, or none at a position that licenses none. -/
  insert : Neighborhood Bundle → List F

namespace Spellout

variable {F : Type*}

/-- The domain after the module sequence. -/
def run (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    SpelloutDomain Bundle :=
  runModules s.modules d

/-- The PF output has one insertion slot per surviving position. -/
def pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    List (List F) :=
  (along (s.run d)).map s.insert

@[simp] theorem length_pf (s : Spellout Bundle F) (d : SpelloutDomain Bundle) :
    (s.pf d).length = (s.run d).length := by
  simp [pf]

/-! ### The timing of a focus-level rule -/

variable (r : Neighborhood Bundle → Bundle) (s : Spellout Bundle F)

/-- `s.rewriteBefore r` applies the focus-level rule `r` to every terminal after the modules of
`s` and before insertion, so that a terminal beside a rewritten one sees it rewritten. -/
def rewriteBefore : Spellout Bundle F :=
  { s with modules := s.modules ++ [fun d ↦ (along d).map r] }

/-- `s.rewriteAt r` applies the focus-level rule `r` to each terminal at its own insertion only,
so that a terminal beside it sees it as it was. -/
def rewriteAt : Spellout Bundle F :=
  { s with insert := fun n ↦ s.insert { n with focus := r n } }

@[simp] theorem run_rewriteBefore (d : SpelloutDomain Bundle) :
    (s.rewriteBefore r).run d = (along (s.run d)).map r := by
  simp [run, rewriteBefore, runModules]

@[simp] theorem run_rewriteAt (d : SpelloutDomain Bundle) : (s.rewriteAt r).run d = s.run d := rfl

@[simp] theorem insert_rewriteBefore : (s.rewriteBefore r).insert = s.insert := rfl

@[simp] theorem insert_rewriteAt (n : Neighborhood Bundle) :
    (s.rewriteAt r).insert n = s.insert { n with focus := r n } := rfl

theorem pf_rewriteBefore_eq_pf_rewriteAt
    (hs : ∀ n n' : Neighborhood Bundle, n.focus = n'.focus → s.insert n = s.insert n')
    (d : SpelloutDomain Bundle) : (s.rewriteBefore r).pf d = (s.rewriteAt r).pf d := by
  have key (e : SpelloutDomain Bundle) :
      (along e).map s.insert = e.map fun b ↦ s.insert (ofBundle b) :=
    calc (along e).map s.insert
        = ((along e).map focus).map fun b ↦ s.insert (ofBundle b) := by
          rw [List.map_map]; exact List.map_congr_left fun n _ ↦ hs _ _ rfl
      _ = e.map fun b ↦ s.insert (ofBundle b) := by rw [map_focus_along]
  rw [pf, pf, run_rewriteBefore, run_rewriteAt, insert_rewriteBefore, key, List.map_map]
  exact List.map_congr_left fun n _ ↦ hs _ _ rfl

end Spellout

end DistributedMorphology
