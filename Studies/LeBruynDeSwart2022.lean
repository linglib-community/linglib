module

public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Quantification.Individual
public import Linglib.Data.Examples.LeBruynDeSwart2022

/-!
# Le Bruyn and de Swart (2022): Exceptional Wide Scope of Bare Nominals

Bare plurals take narrow scope across languages, which Chierchia's kinds approach derives: the
bare plural denotes its kind, and derived kind predication introduces an existential over the
kind's instances where the kind meets the verb. Le Bruyn and de Swart observe that Dutch bare
plurals scrambled over negation take wide scope while keeping their kind reading. A kind takes no
scope, as a name takes none (Chierchia's §4.2), so the kinds approach still gives narrow scope
after scrambling, while Krifka's existential shift makes the bare plural a quantifier that takes
wide scope when scrambled.

## Main results

* `LeBruynDeSwart2022.chierchiaScrambled_iff`: on the kinds approach scrambling changes nothing.
* `LeBruynDeSwart2022.books_example`: on a two-book model of (35), Krifka's scrambled
  existential is true and both narrow readings are false.

## Implementation notes

* Individuals are Link's nonempty sets of atoms, `Mereology.Individual`, so no empty
  plurality satisfies a distributive predicate vacuously. Both derivations quantify over all
  pluralities of books, the instances of the kind; the plural noun's own extension, without the
  atoms, would change no truth value on the model.
* The attested examples are rows of `Data/Examples/LeBruynDeSwart2022.json`.

## References

* [le-bruyn-de-swart-2022]
* [chierchia-1998]
* [krifka-2003]
-/

@[expose] public section

namespace LeBruynDeSwart2022

open Mereology Quantifier

/-- A book of the attested example (35) is either finished or unfinished. -/
inductive Book
  | finished
  | unfinished
  deriving DecidableEq, Nonempty

/-- *books* holds of every plurality of books, singular or plural. -/
def books : Unit → Set (Individual Book) := fun _ ↦ Set.univ

/-- A plurality was read to the end, distributively, when every book in it was finished. -/
def read (x : Individual Book) : Prop := x.1 ⊆ {Book.finished}

/-- With Krifka's existential shift in place (40), no book was read. -/
def krifkaUnscrambled : Prop := ¬ GQ.some (books ()) read

/-- With Krifka's existential shift scrambled over negation (41), some book was not read. -/
def krifkaScrambled : Prop := GQ.some (books ()) readᶜ

/-- On the kinds approach (38), the bare plural shifts to its kind, and derived kind predication
introduces the existential over its instances below negation. -/
def chierchiaUnscrambled : Prop :=
  ¬ GQ.some ((iota (IsGreatest (books ()))).elim (∅ : Set _) Set.Iic) read

/-- On the kinds approach with the kind scrambled over negation, the kind binds a kind-level
trace below negation. -/
def chierchiaScrambled : Prop :=
  NP.individual (fun s ↦ iota (IsGreatest (books s)))
    (fun k : Unit → Option (Individual Book) ↦ GQ.some ((k ()).elim (∅ : Set _) Set.Iic) read)ᶜ

/-- Scrambling a kind over negation changes nothing, since a kind takes no scope, as a name
takes none, so the kinds approach gives narrow scope at either position. -/
theorem chierchiaScrambled_iff : chierchiaScrambled ↔ chierchiaUnscrambled :=
  NP.individual_compl _ _

theorem not_read_unfinished : ¬ read (Individual.atom .unfinished) := fun h ↦
  Book.noConfusion (Set.mem_singleton_iff.1 (h (Set.mem_singleton _)))

theorem read_finished : read (Individual.atom .finished) := subset_rfl

/-- On the two-book model of (35), Krifka's scrambled existential is true, while his in-place
reading and the kinds approach's scrambled one are false. -/
theorem books_example : krifkaScrambled ∧ ¬ krifkaUnscrambled ∧ ¬ chierchiaScrambled := by
  refine ⟨⟨Individual.atom .unfinished, trivial, not_read_unfinished⟩,
    not_not.2 ⟨Individual.atom .finished, trivial, read_finished⟩, ?_⟩
  rw [chierchiaScrambled_iff, chierchiaUnscrambled, not_not]
  have hd : iota (IsGreatest (books ())) = some ⟨Set.univ, Set.univ_nonempty⟩ :=
    iota_isGreatest_eq_some_iff.2 ⟨trivial, fun x _ ↦ (Set.subset_univ x.1 : x ≤ _)⟩
  rw [hd]
  exact ⟨Individual.atom .finished, (Set.subset_univ _ : Individual.atom Book.finished ≤ _),
    read_finished⟩

end LeBruynDeSwart2022
