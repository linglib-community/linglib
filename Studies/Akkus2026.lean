module

public import Linglib.Morphology.DistributedMorphology.LateInsertion
public import Studies.Harley2014

/-!
# Akkuş (2026): Late insertion

Under late insertion the syntax operates on terminals with no phonological content, and
Vocabulary Insertion supplies exponents on the PF branch, each terminal realized in its
neighborhood. The vignette's architecture runs end to end here: a Hiaki clause is built as a
linearized syntactic object with silent terminals, handed over as a spell-out domain, and
Harley's suppletive vocabulary realizes the verb by the Subset Principle, reading the internal
argument's number from the neighborhood (`pf_clause`). Root suppletion is the vignette's argument
that roots too are inserted late: under early insertion a root carries one listed form through
the syntax, so no assignment of forms to roots derives *vuite* ~ *tenne* (`no_early_insertion`).

## Implementation notes

* The clause is cut down to the internal argument and the verb, in that order, so the verb's
  pipeline neighborhood is Harley's insertion site; `pf_clause` says so for the four roots.
* Early insertion is `DistributedMorphology.earlySpellout` over the same terminal sequence, which
  realizes each token's listed form whatever its neighbors
  (`DistributedMorphology.pf_earlySpellout`).

## TODO

* The dissociated morphemes of §26.3 (theme vowels, AGR nodes), which add material at PF against
  Inclusiveness (6).

## References

* [akkus-2026]
* [harley-2014]
-/

@[expose] public section

namespace Akkus2026

open Minimalist DistributedMorphology Morphology.Exponence
open Clause.Arguments (unaccusative)

/-- The internal argument, a silent D head bearing `n`. -/
def subjTok (n : Number) : LexicalItem.Token :=
  ⟨.of .D [], match n with | .singular => 1001 | _ => 1002⟩

/-- The verb, a silent V head over the root `r`. -/
def verbTok (r : Root) : LexicalItem.Token := ⟨.of .V [.D], r.1⟩

/-- The Hiaki clause, the internal argument below the clause-final verb. -/
def clause (r : Root) (n : Number) : LinearizedSyntacticObject :=
  (subjTok n : LinearizedSyntacticObject) * verbTok r

/-- The feature bundles the terminals hand over: the verb its root's index, the argument its
number. -/
def feats (tok : LexicalItem.Token) : Finset Harley2014.SiteFeature :=
  match tok.item.cat with
  | .V => {.root ⟨tok.id⟩}
  | _ => {.internal (if tok.id = 1001 then .singular else .plural)}

/-- Late insertion over Harley's vocabulary: no postsyntactic modules, the Subset Principle at
each position. -/
def lateSpellout : Spellout (Finset Harley2014.SiteFeature) String :=
  ⟨[], fun n ↦ (subsetPrinciple Harley2014.vocabulary n).toList⟩

theorem pfPhon_clause : ∀ r ∈ [Harley2014.run, Harley2014.walk, Harley2014.kill, Harley2014.sing],
    ∀ n, pfPhon (clause r n) = [] := by decide

theorem pf_clause : ∀ r ∈ [Harley2014.run, Harley2014.walk, Harley2014.kill, Harley2014.sing],
    ∀ n, lateSpellout.pf (SpelloutDomain.ofLinearized feats (clause r n))
      = [[], (Harley2014.spellout (unaccusative n) r).toList] := by
  decide

/-- *vuite* and *tenne* from one silent syntax (5a). -/
example :
    lateSpellout.pf (SpelloutDomain.ofLinearized feats (clause Harley2014.run .singular))
        = [[], ["vuite"]] ∧
      lateSpellout.pf (SpelloutDomain.ofLinearized feats (clause Harley2014.run .plural))
        = [[], ["tenne"]] := by
  decide

/-- The verb with its form listed in the lexicon, early insertion's terminal. -/
def earlyVerbTok (phon : Root → String) (r : Root) : LexicalItem.Token :=
  ⟨.of .V [.D] (phon r), r.1⟩

theorem no_early_insertion :
    ¬ ∃ phon : Root → String, ∀ n,
      ((earlySpellout [subjTok n, earlyVerbTok phon Harley2014.run]).pf
          ([subjTok n, earlyVerbTok phon Harley2014.run].map ({·}))).flatten.filter (· ≠ "")
        = (Harley2014.spellout (unaccusative n) Harley2014.run).toList := by
  rintro ⟨phon, h⟩
  have hnd : ∀ n, ([subjTok n, earlyVerbTok phon Harley2014.run]).Nodup := by
    intro n
    refine List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩
    intro hmem
    have := congrArg (fun tok ↦ tok.item.cat) (List.mem_singleton.1 hmem)
    simp [subjTok, earlyVerbTok, LexicalItem.of] at this
  have key : ∀ n, (Harley2014.spellout (unaccusative n) Harley2014.run).toList
      = ["", phon Harley2014.run].filter (· ≠ "") := by
    intro n
    rw [← h n, pf_earlySpellout (hnd n)]
    rfl
  have h1 := key .singular
  have h2 := key .plural
  rw [Harley2014.run_sg] at h1
  rw [show Harley2014.spellout (unaccusative .plural) Harley2014.run = some "tenne" by decide]
    at h2
  exact absurd (h1.trans h2.symm) (by decide)

end Akkus2026
