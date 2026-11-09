module

public import Linglib.Syntax.Tree.QuantifierRaising
public import Linglib.Syntax.Cat
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.Barker2027

/-!
# Barker (2027): Scope

Barker's survey takes Quantifier Raising as the general theory of scope and asks what restricts
it. On the classic account a tensed clause is a scope island for a universal: *everyone* scopes
over the subject from an infinitival complement, [not from a tensed
one](##Barker2027.tensedClause_ex18). Barker sets beside this the universals that do leave a
tensed clause, with *each*. The fragment gives *every* and *each* one reading, so [no theory that
sees a scope-taker through its readings fits both](##Barker2027.not_fits_ofReadings), which is the
survey's point that a constraint on scope depends on the identity of the scope-taker; [a theory
that names the determiner fits](##Barker2027.rows_everyIsland).

## Implementation notes

* A tree's words are determiner entries of the English fragment and other words as strings, and
  *everyone* is the determiner *every* with the noun *one*.
* A tensed clause has the category `S`; an infinitival clause is a projection of *to*, a
  particle. An adjunction to a clause is a segment of the clause, so a constituent raised to the
  edge of an island is still inside it.
* The inverse reading of a row is available when the embedded quantifier can raise to the edge of
  the sentence. The article's examples of relative and adjunct clauses, (19) and (20a), are in the
  rows and are not given trees.

## TODO

That an island confines a scope-taker under every sequence of steps, and not only the one step to
the edge of the sentence, is not proved.

## References

* [barker-2027]
* [may-1985]
-/

@[expose] public section

namespace Barker2027

open PhraseStructure PhraseStructure.Tree English.Determiners

/-- A word is a determiner entry of the fragment or another word. -/
abbrev Word := QuantificationalDeterminer ⊕ String

/-- The determiners in a constituent. -/
def determiners (a : Tree Cat Word) : List QuantificationalDeterminer :=
  a.yield.filterMap Sum.getLeft?

/-! ### Theories of islands -/

/-- The island theories that see a scope-taker through the readings of its determiners and a
subtree through its category: a subtree whose category satisfies `Q` is an island for a
constituent with a determiner whose readings satisfy `P`. -/
def ofReadings (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop)
    (a b : Tree Cat Word) : Prop :=
  (∃ d ∈ determiners a, P d.readings) ∧ Q b.cat

instance (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop) [DecidablePred P]
    [DecidablePred Q] (a b : Tree Cat Word) : Decidable (ofReadings P Q a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The classic theory: a tensed clause is an island for a universal. -/
def tensedClause : Tree Cat Word → Tree Cat Word → Prop :=
  ofReadings (.every ∈ ·) (· = .S)

instance (a b : Tree Cat Word) : Decidable (tensedClause a b) :=
  inferInstanceAs (Decidable (ofReadings _ _ a b))

/-- A tensed clause is an island for *every*, and not for *each*. -/
def everyIsland (a b : Tree Cat Word) : Prop :=
  every ∈ determiners a ∧ b.cat = .S

instance (a b : Tree Cat Word) : Decidable (everyIsland a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The examples -/

/-- A row with its tree and the embedded quantifier. -/
structure Case where
  /-- The article's example. -/
  row : Datum
  /-- The sentence as it is pronounced. -/
  tree : Tree Cat Word
  /-- The embedded quantifier. -/
  mover : Tree Cat Word

/-- The address of the embedded quantifier in the sentence. -/
def Case.address (c : Case) : List ℕ := (c.tree.addressOf? c.mover).getD []

/-- The embedded quantifier can raise to the edge of the sentence, where it outscopes the
subject. -/
def Case.InverseScope (I : Tree Cat Word → Tree Cat Word → Prop) (c : Case) : Prop :=
  c.tree.PassesNoIsland I c.address

instance (I : Tree Cat Word → Tree Cat Word → Prop) [∀ a b, Decidable (I a b)] (c : Case) :
    Decidable (c.InverseScope I) :=
  inferInstanceAs (Decidable (c.tree.PassesNoIsland I c.address))

/-- A word that is not a determiner entry is its string. -/
local instance : Coe String Word := ⟨.inr⟩

/-- *Everyone*, the determiner *every* with *one*. -/
def everyone : Tree Cat Word := ltree% [N [Det ⟨.inl every⟩] [N "one"]]

/-- *Each speaker*. -/
def eachSpeaker : Tree Cat Word := ltree% [N [Det ⟨.inl each⟩] [N "speaker"]]

/-- (18a) *Someone asked [everyone to leave]*. -/
def ex18a : Case where
  row := Examples.ex_18a
  tree := ltree% [S [Pron "someone"] [V [V "asked"] [Neg (everyone) [Neg [Neg "to"] [V "leave"]]]]]
  mover := everyone

/-- (18b) *Someone thought [everyone left]*. -/
def ex18b : Case where
  row := Examples.ex_18b
  tree := ltree% [S [Pron "someone"] [V [V "thought"] [S (everyone) [V "left"]]]]
  mover := everyone

/-- (20b) *A student made sure that [each speaker had a ride]*. -/
def ex20b : Case where
  row := Examples.ex_20b
  tree := ltree% [S [N [Det "a"] [N "student"]]
    [V [V "made"] [Adj "sure"]
      [C [C "that"] [S (eachSpeaker) [V [V "had"] [N [Det "a"] [N "ride"]]]]]]]
  mover := eachSpeaker

/-- The examples with trees. -/
def cases : List Case := [ex18a, ex18b, ex20b]

/-! ### What the theories predict -/

/-- The classic contrast: on the theory that tensed clauses are islands for universals,
*everyone* outscopes the subject from the infinitival complement of *asked* and not from the tensed
complement of *thought*. -/
theorem tensedClause_ex18 :
    ex18a.InverseScope tensedClause ∧ ¬ ex18b.InverseScope tensedClause := by
  decide

/-- Without islands the universal of (18b) raises out of its clause. -/
theorem inverseScope_bot_ex18b : ex18b.InverseScope ⊥ :=
  passesNoIsland_bot _ _

/-- No island theory that sees a scope-taker through the readings of its determiners keeps
*everyone* in the tensed clause of (18b) and lets *each speaker* out of the tensed clause of
(20b), since *every* and *each* have one reading. -/
theorem not_fits_ofReadings (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop) :
    ¬ (¬ ex18b.InverseScope (ofReadings P Q) ∧ ex20b.InverseScope (ofReadings P Q)) := by
  rintro ⟨h18, h20⟩
  refine h18 fun a ha k hk hk0 b hb hI ↦ ?_
  obtain rfl : everyone = a := Option.some.inj ha
  obtain ⟨⟨d, hd, hP⟩, hQ⟩ := hI
  obtain rfl : d = every := by simpa [determiners, everyone] using hd
  have hP' : ∃ d ∈ determiners eachSpeaker, P d.readings :=
    ⟨each, by simp [determiners, eachSpeaker], hP⟩
  have hk3 : k < 3 := hk
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · obtain rfl := Option.some.inj hb
    exact h20 _ rfl 1 (by decide) (by decide) _ rfl ⟨hP', hQ⟩
  · obtain rfl := Option.some.inj hb
    exact h20 _ rfl 3 (by decide) (by decide) _ rfl ⟨hP', hQ⟩

/-- The theory on which a tensed clause is an island for *every* and not for *each* gives each
example its judgment: the inverse reading is acceptable exactly when the embedded quantifier
passes no island. -/
theorem rows_everyIsland : ∀ c ∈ cases,
    (c.row.readings.lookup "∀ > ∃" = some .acceptable ↔ c.InverseScope everyIsland) := by
  decide

/-- Under that theory the tree of (20b) with *each speaker* raised to its edge is one of its
logical forms. -/
theorem isLogicalForm_ex20b :
    IsLogicalForm everyIsland ex20b.tree (ex20b.tree.raiseOf 1 eachSpeaker) :=
  (IsLogicalForm.refl _).raiseOf (p := ex20b.address) rfl (by decide) 1

end Barker2027
