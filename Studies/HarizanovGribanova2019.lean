module

public import Linglib.Syntax.Minimalist.Category
public import Linglib.Morphology.DistributedMorphology.Amalgamation
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Harizanov and Gribanova (2019): Whither head movement?

Harizanov and Gribanova divide the work of head movement between two operations. Words are
formed by postsyntactic amalgamation: a head whose feature is [M:+] Raises into the next head
up, a head whose feature is [M:−] Lowers into the nearest head below, and the result is a
head-adjunction structure in the position of the target. Displacement is syntactic movement of a
head to the root, which comes first and forms no word. How complex a verb is and where it is
pronounced therefore vary independently, the same verbal complex surfacing in T in French, in
Neg in Russian and in V in Danish.

## Implementation notes

* A spine lists the heads of an extended projection, lowest first, each with its [M] feature;
  specifiers and adjuncts, which are islands for amalgamation, are left out. A head that has
  moved in the syntax occupies two positions of the spine, the paper's multidominance.
* A complex head is an element of the free magma over the heads. The paper's adjunction
  structures are unordered; each product here lists the lower constituent first, so that the
  heads of a complex head, read off in order, are a stretch of the spine.
* Chain Reduction pronounces the highest occurrence, as in the paper's German, Danish and
  Russian derivations.
* The paper also places the English verbal complex in v, but takes T to join the English verb
  by an operation other than amalgamation, one that an intervening specifier blocks. No English
  derivation is given here.

## TODO

* The pronunciation of both occurrences of the verb in Hebrew bare-infinitive fronting.
* French nonfinite clauses, whose verbs stay low; the paper gives their [M] features no
  derivation.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
* [travis-1984]
-/

@[expose] public section

namespace HarizanovGribanova2019

open FreeMagma DistributedMorphology.Amalgamation
open DistributedMorphology

variable {H : Type*}

/-! ### The paper's derivations -/

theorem raising_and_lowering (x y z : H) :
    amalgamate ⟨[⟨z, some .raising⟩, ⟨y, none⟩, ⟨x, some .lowering⟩]⟩ =
      some [⟨y, of z * of y * of x⟩] :=
  rfl

theorem lowering_twice (x y z : H) :
    amalgamate ⟨[⟨z, none⟩, ⟨y, some .lowering⟩, ⟨x, some .lowering⟩]⟩ =
      some [⟨z, of z * of y * of x⟩] :=
  rfl

theorem lowering_without_target (x y z : H) :
    amalgamate ⟨[⟨z, some .raising⟩, ⟨y, some .lowering⟩, ⟨x, none⟩]⟩ = none :=
  rfl

/-! ### The clausal spine -/

open Minimalist.Cat

/-- The Russian clause, in which V, v and Asp Raise and T Lowers. -/
def russian : Spine (Terminal Minimalist.Cat) :=
  ⟨[⟨V, some .raising⟩, ⟨v, some .raising⟩, ⟨Asp, some .raising⟩, ⟨.Neg, none⟩,
    ⟨T, some .lowering⟩]⟩

/-- The Danish clause, in which v and T Lower. -/
def danish : Spine (Terminal Minimalist.Cat) :=
  ⟨[⟨V, none⟩, ⟨v, some .lowering⟩, ⟨T, some .lowering⟩]⟩

/-- The French finite clause, in which V, v and Neg Raise. The negator *pas* is a specifier and
not on the spine. -/
def french : Spine (Terminal Minimalist.Cat) :=
  ⟨[⟨V, some .raising⟩, ⟨v, some .raising⟩, ⟨.Neg, some .raising⟩, ⟨T, none⟩]⟩

/-- The German clause, in which V Raises into T. -/
def german : Spine (Terminal Minimalist.Cat) := ⟨[⟨V, some .raising⟩, ⟨T, none⟩]⟩

/-- The Hebrew clause with a topic, in which V Raises into T. -/
def hebrew : Spine (Terminal Minimalist.Cat) := ⟨[⟨V, some .raising⟩, ⟨T, none⟩, ⟨Top, none⟩]⟩

theorem russian_amalgamate :
    amalgamate russian = some [⟨.Neg, of V * of v * of Asp * of .Neg * of T⟩] :=
  rfl

theorem danish_amalgamate : amalgamate danish = some [⟨V, of V * of v * of T⟩] :=
  rfl

theorem french_amalgamate :
    amalgamate french = some [⟨T, of V * of v * of .Neg * of T⟩] :=
  rfl

/-! ### Syntactic movement of a head -/

theorem german_root :
    amalgamate (moveToRoot german T) = some [⟨T, of V * of T⟩, ⟨T, of T⟩] :=
  rfl

theorem danish_root :
    amalgamate (moveToRoot danish V) = some [⟨V, of V * of v * of T⟩, ⟨V, of V⟩] :=
  amalgamate_moveToRoot V danish_amalgamate

theorem russian_polarity_focus :
    amalgamate (moveToRoot russian .Neg) =
      some [⟨.Neg, of V * of v * of Asp * of .Neg * of T⟩, ⟨.Neg, of .Neg⟩] :=
  amalgamate_moveToRoot .Neg russian_amalgamate

theorem hebrew_fronting :
    amalgamate (moveToRoot hebrew V) = some [⟨T, of V * of T⟩, ⟨.Top, of .Top⟩, ⟨V, of V⟩] :=
  rfl

theorem skipping :
    amalgamate ⟨[⟨(0 : Fin 6), none⟩, ⟨5, some .lowering⟩, ⟨4, none⟩, ⟨3, none⟩,
        ⟨2, some .raising⟩, ⟨1, some .raising⟩, ⟨0, none⟩]⟩ =
      some [⟨0, of 0 * of 5⟩, ⟨4, of 4⟩, ⟨3, of 3⟩, ⟨0, of 2 * of 1 * of 0⟩] :=
  rfl

-- In the French clause every position is pronounced at T.
theorem french_hosts :
    (amalgamate french).map MorphosyntacticWord.hosts = some [T, T, T, T] :=
  rfl

-- With a head occurring twice, the positions pronounced at it need not be a stretch of the spine.
theorem skipping_hosts :
    ∀ out ∈ amalgamate ⟨[⟨(0 : Fin 6), none⟩, ⟨5, some .lowering⟩, ⟨4, none⟩, ⟨3, none⟩,
        ⟨2, some .raising⟩, ⟨1, some .raising⟩, ⟨0, none⟩]⟩,
      ¬ IsContiguous (MorphosyntacticWord.hosts out).get := by
  decide

/-! ### Verb placement -/

/-- `spine? r` is the spine of the clause of `r`, a French or Russian finite clause, a Danish
embedded clause, or a Danish root clause, in which V has moved. -/
def spine? (r : Datum) : Option (Spine (Terminal Minimalist.Cat)) :=
  List.lookup (r.language, r.feature? "clause")
    [((.french, none), french), ((.russian, none), russian),
      ((.danish, some "embedded"), danish), ((.danish, some "root"), moveToRoot danish V)]

/-- The canonical tests for verb movement place a finite verb before a low adverb, sentential
negation or a floating quantifier exactly when it is pronounced in T or above. The paper's
examples of French, Danish and Russian finite clauses are acceptable in exactly the order that
the position of the verbal complex predicts. -/
theorem verb_placement :
    ∀ r ∈ Examples.all, r.feature? "phenomenon" = some "finiteVerbPlacement" →
      r.feature? "diagnostic" ≠ some "coordination" →
        ∃ s ∈ spine? r, ∃ b ∈ r.parse? "verbPrecedes" [("true", true), ("false", false)],
          (r.judgment = .acceptable ↔ (b = true ↔ PronouncedFrom s V T)) := by
  decide +kernel

end HarizanovGribanova2019
