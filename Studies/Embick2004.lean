module

public import Linglib.Data.Examples.Embick2004
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Syntax.Tree.Projection

/-!
# Embick (2004): On the structure of resultative participles in English

The verbalizer v[FIENT] denotes a transition toward a state, and a Root combines with it in one of
two ways. As its complement, the Root names the state the transition reaches, so *The metal is
flattened* is the state of having become flat. Merged with it in a single complex head, Direct
Merge, the Root names the means of the transition, so *John hammered the metal flat* is becoming
flat by hammering, the complement of v[FIENT] then being a full aP. The Root is v[FIENT]'s sister
either way, so sisterhood does not tell the two apart: the complement is projected over, the
directly merged Root adjoined. A condition that the complement of every v[FIENT] be predicated of
the DP in its specifier derives the Direct Object Restriction and the gaps among resultative
participles.

Of the configurations in which Distributed Morphology lets a categorizer categorize a Root, as its
complement or as a modifier merged with it, this analysis uses both. Head movement brings a Root
complement into the head, where it forms the complex head that Direct Merge builds, so Vocabulary
Insertion, which realizes complex heads, cannot tell the two configurations apart: only their
interpretation does.

## Main statements

* `headDaughter?_moveRoot`: head movement of a Root complement builds the complex head of Direct
  Merge, so every vocabulary realizes v[FIENT] alike in the two (`realize_moveRoot`).
* `isSegment_directMerge`: the Root is v[FIENT]'s sister in both structures, projected over as a
  complement and adjoined under Direct Merge.
* `interp_directMerge`: a directly merged Root is the means and the aP the result.
* `acceptable_iff_interpretable`: the condition on v[FIENT] and the argument structure of Roots
  derive the judgments.

## Implementation notes

* The domain of v[FIENT] is recorded by the DP in its specifier, a Root directly merged with it,
  and its complement, a bare Root, an aP, or a resultative participle with its own v[FIENT].
  Event variables are left out, as the paper leaves them out, and the `FIENT(P)(x)` of the means
  rule is read as `FIENT(P(x))`, as its application to *hammer flat* does.
* Which half of the means rule applies, whether the merged Root takes the DP as its argument,
  depends on the example, so each row records it. Argument taking is recorded only for the Roots
  that the rows put in complement position.

## TODO

The dative gap (*John is given a book*), the Asp heads that make participles stative, and the
diagnostics separating resultative from stative participles are not formalized.

## References

* [embick-2004]
-/

@[expose] public section

namespace Embick2004

open PhraseStructure
open DistributedMorphology (ComplexHead VocabularyItem subsetPrinciple)
open scoped DistributedMorphology

/-! ### Roots -/

/-- The Roots of the examples. -/
inductive Root
  | hammer | flat | laugh | hoarse | freeze | solid | smoke | thin | kick | «open»
  deriving DecidableEq, Repr

/-- The DPs of the examples. -/
inductive DP
  | john | theMetal | theRiver | theDoor | himself
  deriving DecidableEq, Repr

/-- √HAMMER and √FLAT take an argument and √LAUGH takes none (§4.1). -/
def TakesArgument (r : Root) : Prop := r = .hammer ∨ r = .flat

instance : DecidablePred TakesArgument := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### The two configurations -/

/-- The categories are the verbalizer, the Root's own, the adjectivizer, aspect and determiner
phrases. -/
inductive Cat
  | v | root | a | asp | d
  deriving DecidableEq, Repr

/-- The terminals are v[FIENT], Roots, the adjectivizer, AspR and DPs. -/
inductive Word
  | fient | root (r : Root) | adj | aspR | dp (x : DP)
  deriving DecidableEq, Repr

/-- The Root complement structure (47), v[FIENT] taking the Root as its complement. -/
def rootComplement (r : Root) : Tree Cat Word :=
  .node .v [.terminal .v .fient, .terminal .root (.root r)]

/-- The complex head that Direct Merge builds (48), the Root adjoined to v[FIENT]. -/
def directMerge (r : Root) : Tree Cat Word :=
  .adjoin .v [.terminal .root (.root r), .terminal .v .fient]

theorem children_perm (r : Root) : (rootComplement r).children.Perm (directMerge r).children :=
  List.Perm.swap _ _ []

theorem headIndex?_rootComplement (r : Root) : (rootComplement r).headIndex? = some 0 := rfl

theorem headIndex?_directMerge (r : Root) : (directMerge r).headIndex? = some 1 := rfl

/-- What tells the structures apart is how v[FIENT] heads them: a Root complement is projected
over, while a directly merged Root makes the mother a further segment of v[FIENT]. -/
theorem isSegment_directMerge (r : Root) :
    ¬ (rootComplement r).value.IsSegment ∧ (directMerge r).value.IsSegment :=
  ⟨id, trivial⟩

/-! ### Head movement and Vocabulary Insertion -/

/-- Head movement of a bare Root complement adjoins the Root to the head it is the complement of,
leaving a trace. -/
def moveRoot : Tree Cat Word → Tree Cat Word
  | .node c [h, .terminal .root w] => .node c [.adjoin h.cat [.terminal .root w, h], .trace 0 .root]
  | t => t

/-- The head daughter of a tree. -/
def headDaughter? (t : Tree Cat Word) : Option (Tree Cat Word) :=
  t.headIndex?.bind (t.children[·]?)

/-- Head movement of a Root complement builds exactly the complex head of Direct Merge. -/
theorem headDaughter?_moveRoot (r : Root) :
    headDaughter? (moveRoot (rootComplement r)) = some (directMerge r) := rfl

/-- A complex head of v[FIENT] with a Root adjoined, read as the Root with the head above it. -/
def complexHead? : Tree Cat Word → Option (ComplexHead Root Word)
  | .adjoin .v [.terminal .root (.root r), .terminal .v w] => some ⟨r, [w]⟩
  | _ => none

/-- The features Vocabulary Items mention, v[FIENT] and the identity of a Root. -/
inductive Feature
  | fient | root (r : Root)
  deriving DecidableEq, Repr

/-- The exponent a vocabulary inserts at v[FIENT] in a complex head, with the Root as its inner
context. -/
def realize (vocab : List (VocabularyItem Feature String)) (w : ComplexHead Root Word) :
    Option String :=
  subsetPrinciple vocab ⟨{.fient}, [{.root w.root}], []⟩

/-- v[FIENT] is spelled out as *-en* next to √FLAT and as null next to √HAMMER (fn. 24). -/
def vocabulary : List (VocabularyItem Feature String) :=
  [⟨{(0, .fient), (-1, .root .flat)}, "-en"⟩, {.fient} ⟷ ""]

theorem realize_flat : realize vocabulary ⟨.flat, [.fient]⟩ = some "-en" := by decide

theorem realize_hammer : realize vocabulary ⟨.hammer, [.fient]⟩ = some "" := by decide

/-- Every vocabulary realizes v[FIENT] alike whether its Root moved from complement position or
was directly merged, so *hammer-ed* has the null v[FIENT] of *hammer-ed flat*. -/
theorem realize_moveRoot (vocab : List (VocabularyItem Feature String)) (r : Root) :
    ((headDaughter? (moveRoot (rootComplement r))).bind complexHead?).map (realize vocab) =
      (complexHead? (directMerge r)).map (realize vocab) := by
  rw [headDaughter?_moveRoot, Option.bind_some]

/-! ### Interpretation -/

/-- The means rule (49) has two halves, as the directly merged Root takes the DP in the specifier
as its argument or takes none. -/
inductive MeansRule
  | argument | noArgument
  deriving DecidableEq, Repr

/-- The complement of v[FIENT] is a bare Root, an aP over a Root, or a resultative participle, AspR
over a lower v[FIENT] with its own specifier and Root complement (58). -/
inductive Complement
  | root (r : Root)
  | aP (r : Root)
  | participle (spec : Option DP) (r : Root)
  deriving DecidableEq, Repr

/-- The domain of v[FIENT] (41) records the DP in its specifier, the Root directly merged with it
if any, its complement, and the half of the means rule that interprets a merged Root. -/
structure FientP where
  spec : Option DP
  merged : Option Root
  comp : Complement
  means : Option MeansRule
  deriving DecidableEq, Repr

/-- A model supplies the transition FIENT, the means relation BY, `BY X Y` saying that `Y` comes
about by `X`, the content of each Root with an argument and without one, and the referents of the
DPs. -/
structure Model (E : Type*) where
  fient : Prop → Prop
  by_ : Prop → Prop → Prop
  pred : Root → E → Prop
  prop : Root → Prop
  dp : DP → E

namespace FientP

/-- **Condition (54).** The complement of every v[FIENT] is predicated of a DP in its specifier, so
a resultative participle complement, with a v[FIENT] of its own, needs a DP in each specifier. -/
def SatisfiesFient : FientP → Prop
  | ⟨spec, _, .participle inner _, _⟩ => spec.isSome ∧ inner.isSome
  | ⟨spec, _, _, _⟩ => spec.isSome

variable {E : Type*} (M : Model E)

/-- The interpretation of the domain of v[FIENT], `none` where there is none. A Root complement is
the state the transition reaches and must take the DP in the specifier as its argument (44). A
directly merged Root is the means by which the state of the aP comes about (49). Any other
structure leaves a bare Root uncategorized or a v[FIENT] without a DP in its specifier. -/
def interp : FientP → Option Prop
  | ⟨some x, none, .root r, _⟩ =>
    if TakesArgument r then some (M.fient (M.pred r (M.dp x))) else none
  | ⟨some x, some m, .aP a, some .argument⟩ =>
    some (M.by_ (M.pred m (M.dp x)) (M.fient (M.pred a (M.dp x))))
  | ⟨some x, some m, .aP a, some .noArgument⟩ =>
    some (M.by_ (M.prop m) (M.fient (M.pred a (M.dp x))))
  | _ => none

/-- The structures that have an interpretation. -/
def Interpretable : FientP → Prop
  | ⟨some _, none, .root r, _⟩ => TakesArgument r
  | ⟨some _, some _, .aP _, some _⟩ => True
  | _ => False

instance : DecidablePred Interpretable
  | ⟨some _, none, .root r, _⟩ => inferInstanceAs (Decidable (TakesArgument r))
  | ⟨some _, some _, .aP _, some _⟩ => isTrue trivial
  | ⟨none, _, _, _⟩ | ⟨some _, none, .aP _, _⟩ | ⟨some _, none, .participle _ _, _⟩
  | ⟨some _, some _, .root _, _⟩ | ⟨some _, some _, .participle _ _, _⟩
  | ⟨some _, some _, .aP _, none⟩ => isFalse id

theorem isSome_interp_iff (p : FientP) : (p.interp M).isSome ↔ p.Interpretable := by
  rcases p with ⟨_ | x, _ | m, _ | _ | _, _ | _ | _⟩ <;>
    simp only [interp, Interpretable] <;> (try split_ifs) <;> simp_all

theorem Interpretable.satisfiesFient {p : FientP} (h : p.Interpretable) : p.SatisfiesFient := by
  rcases p with ⟨_ | x, _ | m, _ | _ | _, _ | _ | _⟩ <;> simp_all [Interpretable, SatisfiesFient]

/-- A resultative participle with a single DP violates the condition on v[FIENT] wherever the DP is
generated (57b). -/
theorem not_satisfiesFient_participle (x : DP) (m : Option Root) (r : Root)
    (μ : Option MeansRule) :
    ¬ (⟨some x, m, .participle none r, μ⟩ : FientP).SatisfiesFient ∧
      ¬ (⟨none, m, .participle (some x) r, μ⟩ : FientP).SatisfiesFient := by
  simp [SatisfiesFient]

/-- A Root complement names the state the transition reaches: *The metal is hammered* is
`FIENT(Hammer(the metal))` (44). -/
theorem interp_rootComplement (x : DP) {r : Root} (hr : TakesArgument r) (μ : Option MeansRule) :
    interp M ⟨some x, none, .root r, μ⟩ = some (M.fient (M.pred r (M.dp x))) := by
  simp [interp, hr]

/-- A directly merged Root names the means and the aP the result, so *John hammered the metal flat*
is `BY(Hammer(the metal), FIENT(Flat(the metal)))` (50). -/
theorem interp_directMerge (x : DP) (m a : Root) :
    interp M ⟨some x, some m, .aP a, some .argument⟩ =
      some (M.by_ (M.pred m (M.dp x)) (M.fient (M.pred a (M.dp x)))) := rfl

/-- A Root merged without an argument is no predicate of the DP, so *John smoked himself thin* is
`BY(Smoke, FIENT(Thin(himself)))` (52). -/
theorem interp_directMerge_noArgument (x : DP) (m a : Root) :
    interp M ⟨some x, some m, .aP a, some .noArgument⟩ =
      some (M.by_ (M.prop m) (M.fient (M.pred a (M.dp x)))) := rfl

end FientP

/-! ### The examples -/

/-- The Roots as named in the rows. -/
def rootTable : List (String × Root) :=
  [("hammer", .hammer), ("flat", .flat), ("laugh", .laugh), ("hoarse", .hoarse),
    ("freeze", .freeze), ("solid", .solid), ("smoke", .smoke), ("thin", .thin), ("kick", .kick),
    ("open", .«open»)]

/-- The DPs as named in the rows. -/
def dpTable : List (String × DP) :=
  [("john", .john), ("theMetal", .theMetal), ("theRiver", .theRiver), ("theDoor", .theDoor),
    ("himself", .himself)]

/-- The value of an optional feature, `none` when the row writes `"none"`. -/
def optional? {α : Type*} (d : Datum) (key : String) (table : List (String × α)) :
    Option (Option α) :=
  if d.feature? key = some "none" then some none else (d.parse? key table).map some

/-- The domain of v[FIENT] an example is analysed with. -/
def FientP.ofDatum (d : Datum) : Option FientP := do
  let r ← d.parse? "compRoot" rootTable
  let comp ← match d.feature? "comp" with
    | some "root" => some (Complement.root r)
    | some "aP" => some (.aP r)
    | some "participle" => (optional? d "innerSpec" dpTable).map (.participle · r)
    | _ => none
  pure ⟨← optional? d "spec" dpTable, ← optional? d "merged" rootTable, comp,
    ← optional? d "means" [("argument", MeansRule.argument), ("noArgument", .noArgument)]⟩

/-- The examples with their analyses and judgments. -/
def data : List (FientP × Judgment) :=
  Examples.all.filterMap fun d ↦ (FientP.ofDatum d).map (·, d.judgment)

theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- An example is acceptable exactly when its analysis is interpretable: *The metal is hammered*
and *John laughed himself hoarse* are, *John is laughed*, *John laughed hoarse* and *John kicked
the door opened* are not. -/
theorem acceptable_iff_interpretable :
    ∀ p ∈ data, p.2 = .acceptable ↔ p.1.Interpretable := by
  decide +kernel

end Embick2004
