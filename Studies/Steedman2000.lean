module

public import Linglib.Data.Examples.Steedman2000
public import Studies.HeimKratzer1998
public import Linglib.Fragments.English.Coordination
public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Syntax.CCG.Derivation
public import Linglib.Syntax.CCG.Grammar
public import Linglib.Syntax.CCG.Interface
public import Linglib.Syntax.CCG.Intonation
public import Linglib.Syntax.WordOrder
public import Studies.BeckmanPierrehumbert1986
public import Linglib.Data.Examples.Readers

/-!
# Steedman (2000): The Syntactic Process

In Steedman's combinatory categorial grammar the slash directions of lexical categories fix
word order, and composition and type-raising make strings such as a subject and a
transitive verb into constituents. This file derives the book's analyses of non-constituent
coordination, gapping, Dutch cross-serial dependencies, scope in verb clusters and
intonational phrasing over the library's CCG, and interprets the derivations over the toy
model of `Studies/HeimKratzer1998`.

## Implementation notes

* Type-raising and coordination are lexical in the library's CCG, so the book's raising rules
  appear as raised entries and its coordination rule `<Φ>` as a conjunction of category
  `(X\⋆X)/⋆X`. A raised name denotes the Montague lift, and coordination at `S/NP` is Partee and
  Rooth's generalized conjunction.
* The toy categories drop the book's features (subordination, case, agreement), so Dutch
  crossed composition is restricted to `VP` complements rather than the book's `VP_{-SUB}`.
* The revealing rule (61) is a unary decomposition outside the binary derivations, so it enters
  only as the condition on the categories it reveals (`RevealedResidue`).
* The tunes follow Pierrehumbert's decomposition of an intonation phrase into pitch accent,
  phrase accent and boundary tone, which Beckman and Pierrehumbert supply (`ipToTune`).

## References

* [steedman-2000]
* [ross-1970]
* [bayer-1996]
* [kayne-1998]
* [haegeman-van-riemsdijk-1986]
* [haegeman-1992]
* [selkirk-1984]
* [partee-rooth-1983]
* [beckman-pierrehumbert-1986]
-/

@[expose] public section

namespace Steedman2000

open CCG
open scoped Montague

/-! ### Categories -/

/-- The atomic categories of the toy English fragment, without the book's features. -/
inductive Atom where
  /-- Sentence. -/
  | S
  /-- Noun phrase. -/
  | NP
  deriving Repr, DecidableEq

def S : Cat Atom := .atom .S

def NP : Cat Atom := .atom .NP

/-- The intransitive verb category `S\NP`, the book's `VP`. -/
def IV : Cat Atom := S \ NP

/-- The transitive verb category `(S\NP)/NP`. -/
def TV : Cat Atom := (S \ NP) / NP

/-- The semantic type of an atom, truth values for sentences and entities for noun phrases. -/
def atomTy : Atom → Montague.Ty
  | .S => .t
  | .NP => .e

example : TV.toTy atomTy = (.e ⇒ .e ⇒ .t) := rfl

/-! ### Word order

Slash direction encodes word order: `TV = (S\NP)/NP` looks right for the object and the
resulting `S\NP` left for the subject, which enforces SVO. -/

def john_sleeps : Derivation String (.multimodal 2) S :=
  .bapp (.lex "John" NP) (.lex "sleeps" IV)

def john_sees_mary : Derivation String (.multimodal 2) S :=
  .bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "Mary" NP))

/-! ### Non-constituent coordination -/

section Coordination

open Montague HeimKratzer1998

/-- The type-raised subject "John" is a lexical leaf of category `S/(S\NP)`. -/
def john_tr : Derivation String (.multimodal 2) (S / (S \ NP)) := .lex "John" (S / (S \ NP))

def mary_tr : Derivation String (.multimodal 2) (S / (S \ NP)) := .lex "Mary" (S / (S \ NP))

/-- "John sees" is the type-raised subject composed with the transitive verb, a constituent of
category `S/NP`. -/
def john_sees : Derivation String (.multimodal 2) (S / NP) := .fcomp john_tr (.lex "sees" TV)

def mary_eats : Derivation String (.multimodal 2) (S / NP) := .fcomp mary_tr (.lex "eats" TV)

/-- `conj c` is the category `(c \⋆ c) /⋆ c` of a conjunction coordinating constituents of
category `c`. Its `star` slashes confine it to application. -/
def conj (c : Cat Atom) : Cat Atom := (c \⋆ c) /⋆ c

-- The `star` slash also blocks composing into the conjunction: no primary composes `S\⋆S`.
example (m : Modality) : ¬ RuleSystem.multimodal 2 S ⟨.right, m, S⟩ [⟨.left, .star, S⟩] :=
  RuleSystem.not_multimodal_of_star_mem List.mem_cons_self rfl

/-- "John sees and Mary eats" coordinates two `S/NP` constituents through the lexical
conjunction, as in the book's "Anna married, and I detest". -/
def john_sees_and_mary_eats : Derivation String (.multimodal 2) (S / NP) :=
  .bapp john_sees (.fapp (.lex "and" (conj (S / NP))) mary_eats)

def john_sees_and_mary_eats_pizza : Derivation String (.multimodal 2) S :=
  .fapp john_sees_and_mary_eats (.lex "pizza" NP)

theorem john_sees_and_mary_eats_pizza_yield :
    john_sees_and_mary_eats_pizza.yield = ["John", "sees", "and", "Mary", "eats", "pizza"] :=
  rfl

/-- `semLexicon` interprets the toy English fragment. It gives meanings to names, type-raised
names, verbs, and conjunctions at `S` and at `S/NP`. -/
def semLexicon : SemLexicon String atomTy ToyEntity Unit := fun word cat ↦
  match word, cat with
  | "John", .atom .NP => some ToyEntity.john
  | "Mary", .atom .NP => some ToyEntity.mary
  | "pizza", .atom .NP => some ToyEntity.pizza
  | "book", .atom .NP => some ToyEntity.book
  | "John", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (Quantifier.individual ToyEntity.john)
  | "Mary", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) =>
      some (Quantifier.individual ToyEntity.mary)
  | "sleeps", .lslash (.atom .S) _ (.atom .NP) => some Toy.sleeps
  | "laughs", .lslash (.atom .S) _ (.atom .NP) => some Toy.laughs
  | "sees", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.sees
  | "eats", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.eats
  | "reads", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) =>
      some Toy.reads
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (fun q p ↦ p ∧ q)
  | "and", .rslash (.lslash (.rslash (.atom .S) _ (.atom .NP)) _
        (.rslash (.atom .S) _ (.atom .NP))) _ (.rslash (.atom .S) _ (.atom .NP)) =>
      some (fun q p x ↦ p x ∧ q x)
  | _, _ => none

/-- "John sees Mary" with a type-raised subject produces the same truth value as the
canonical derivation. -/
def john_sees_mary_via_tr : Derivation String (.multimodal 2) S :=
  .fapp john_tr (.fapp (.lex "sees" TV) (.lex "Mary" NP))

theorem interp_john_sees_mary_via_tr :
    john_sees_mary_via_tr.interp semLexicon = john_sees_mary.interp semLexicon := rfl

theorem coord_interp_pointwise (e : ToyEntity) :
    (john_sees_and_mary_eats.interp semLexicon).map (· e) =
      (match john_sees.interp semLexicon, mary_eats.interp semLexicon with
        | some m₁, some m₂ => some (m₁ e ∧ m₂ e)
        | _, _ => none) := rfl

/-- The spelled-out paraphrase is "John sees pizza and Mary eats pizza". -/
def john_sees_pizza_and_mary_eats_pizza : Derivation String (.multimodal 2) S :=
  .bapp (.bapp (.lex "John" NP) (.fapp (.lex "sees" TV) (.lex "pizza" NP)))
    (.fapp (.lex "and" (conj S))
      (.bapp (.lex "Mary" NP) (.fapp (.lex "eats" TV) (.lex "pizza" NP))))

/-- The non-constituent coordination and its spelled-out paraphrase receive the same truth
conditions, since the composed derivation yields the canonical predicate-argument
structure. -/
theorem nonConstituentCoord_eq_spelledOut :
    john_sees_and_mary_eats_pizza.interp semLexicon =
      john_sees_pizza_and_mary_eats_pizza.interp semLexicon := rfl

/-- A lexicon in which sentence `p` is true and `q` false, with the English coordinators
interpreted by the Boolean operation of their role. -/
def pqLex : SemLexicon String atomTy Unit Unit := fun w c ↦
  match w, c with
  | "p", .atom .S => some True
  | "q", .atom .S => some False
  | "and", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p ↦ English.Coordination.and_.denote {p, q})
  | "or", .rslash (.lslash (.atom .S) _ (.atom .S)) _ (.atom .S) =>
      some (show Prop → Prop → Prop from
        fun q p ↦ English.Coordination.or_.denote {p, q})
  | _, _ => none

def dp : Derivation String (.multimodal 2) S := .lex "p" S
def dq : Derivation String (.multimodal 2) S := .lex "q" S

theorem coord_role_load_bearing :
    (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex ≠
    (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex := by
  have hand : (Derivation.bapp dp (.fapp (.lex "and" (conj S)) dq)).interp pqLex
      = some (True ∧ False) := congrArg some (sInf_pair (a := True) (b := False))
  have hor : (Derivation.bapp dp (.fapp (.lex "or" (conj S)) dq)).interp pqLex
      = some (True ∨ False) := congrArg some (sSup_pair (a := True) (b := False))
  rw [hand, hor]
  exact fun h ↦ ((iff_of_eq (Option.some.inj h)).mpr (Or.inl trivial)).2

end Coordination

/-! ### Gapping

The arguments of a verb, raised order-preservingly over the functions that seek them, compose
into a cluster that coordinates with other clusters and then combines with the verb. Over a
verb-final verb the cluster looks rightward for it, so the verb follows the coordinated clusters
(backward gapping); over a verb-initial verb it looks leftward (forward gapping); over a
verb-medial verb the arguments raise in opposite directions and form no cluster. -/

section Gapping

open WordOrder

/-- `raiseArg c` raises the argument of the function category `c` order-preservingly over
`c`. The argument of `X\A` raises to `X/(X\A)` and that of `X/A` to `X\(X/A)`. -/
def raiseArg : Cat Atom → Option (Cat Atom)
  | .lslash x _ a => some (Cat.forwardTypeRaise a x)
  | .rslash x _ a => some (Cat.backwardTypeRaise a x)
  | .atom _ => none

/-- `hcomp` is harmonic composition, the order-preserving rules `>B` and `<B`. -/
def hcomp : Cat Atom → Cat Atom → Option (Cat Atom)
  | .rslash x _ y, .rslash y' n z => if y = y' then some (.rslash x n z) else none
  | .lslash y' n z, .lslash x _ y => if y = y' then some (.lslash x n z) else none
  | _, _ => none

/-- `cluster v` is the category of the argument cluster over the transitive verb category
`v`. The verb's two arguments are raised over the functions that seek them and composed
harmonically, in whichever order the rules allow. -/
def cluster (v : Cat Atom) : Option (Cat Atom) :=
  match v with
  | .lslash inner _ _ | .rslash inner _ _ => do
      let r₁ ← raiseArg inner
      let r₂ ← raiseArg v
      hcomp r₁ r₂ <|> hcomp r₂ r₁
  | .atom _ => none

/-- The verb-final transitive verb category `(S\NP)\NP`, the book's `tazuneta` (chapter 7
(2)). -/
def sovTV : Cat Atom := (S \ NP) \ NP

/-- The verb-initial transitive verb category `(S/NP)/NP`, the book's `chonaic` (chapter 7
(17)), which Dutch main-clause verbs share and which English gapping reveals. -/
def vsoTV : Cat Atom := (S / NP) / NP

-- (3b)
theorem cluster_sov : cluster sovTV = some (S / sovTV) := by decide

-- (18b)
theorem cluster_vso : cluster vsoTV = some (S \ vsoTV) := by decide

theorem cluster_svo : cluster TV = none := by decide

/-- The backward-gapped conjunct "Ken-ga Naomi-o" of chapter 7 (3b), by forward raising and
forward composition. -/
def backwardGappedConjunct : Derivation String (.multimodal 2) (S / sovTV) :=
  .fcomp (.lex "Ken-ga" (S / (S \ NP))) (.lex "Naomi-o" ((S \ NP) / sovTV))

theorem backwardGappedConjunct_yield :
    backwardGappedConjunct.yield = ["Ken-ga", "Naomi-o"] := rfl

/-- The forward-gapped English conjunct "Warren, potatoes" of chapter 7 (67), a cluster over a
virtual verb-initial verb, by backward raising and backward composition. -/
def gappedConjunct : Derivation String (.multimodal 2) (S \ vsoTV) :=
  .bcomp (.lex "Warren" ((S / NP) \ vsoTV)) (.lex "potatoes" (S \ (S / NP)))

theorem gappedConjunct_yield : gappedConjunct.yield = ["Warren", "potatoes"] := rfl

/-! #### Ross's generalization over the basic orders -/

/-- The transitive verb category of the basic order `a`, whose slash for each argument looks to
the edge of the verb on which `a` puts it, the object first as in the English `(S\NP)/NP`. Which
argument comes first matters to the category only when the two slashes look different ways. -/
def transitiveCat (a : Arrangement Constituent 3) : Cat Atom :=
  (S.push ⟨(a.headDirection .verb .subject).dependentEdge, .dot, NP⟩).push
    ⟨(a.headDirection .verb .object).dependentEdge, .dot, NP⟩

theorem transitiveCat_sov : transitiveCat .sov = sovTV := by decide

theorem transitiveCat_vso : transitiveCat .vso = vsoTV := by decide

theorem transitiveCat_svo : transitiveCat .svo = TV := by decide

/-- The two directions of gapping. Forward gapping keeps the verb in the first conjunct and
backward gapping in the last. -/
inductive GappingDirection where
  | forward
  | backward
  deriving DecidableEq, Repr

/-- The direction of gapping over the verb category `v`, read off the cluster of its arguments,
is backward when the cluster looks rightward for the verb and forward when it looks leftward. -/
def gappingDirection (v : Cat Atom) : Option GappingDirection :=
  (cluster v).map fun
    | .rslash .. => .backward
    | _ => .forward

-- (77)
theorem gappingDirection_transitiveCat (a : Arrangement Constituent 3) :
    gappingDirection (transitiveCat a) =
      if a.IsFinal .verb then some .backward else if a.IsInitial .verb then some .forward
      else none := by
  revert a; decide

/-! #### The revealing rule -/

/-- `RightwardInto t c` holds when `c` is `t` or a rightward function into `t`, a member of the
book's `t/$`. -/
def RightwardInto (t : Cat Atom) : Cat Atom → Prop
  | .rslash x m y => Cat.rslash x m y = t ∨ RightwardInto t x
  | c => c = t

/-- `RightwardInto t` is decided by recursion on the category. -/
def RightwardInto.decidable (t : Cat Atom) : ∀ c, Decidable (RightwardInto t c)
  | .rslash x m y =>
    have := RightwardInto.decidable t x
    inferInstanceAs (Decidable (Cat.rslash x m y = t ∨ RightwardInto t x))
  | .lslash x m y => inferInstanceAs (Decidable (Cat.lslash x m y = t))
  | .atom a => inferInstanceAs (Decidable (Cat.atom a = t))

instance (t : Cat Atom) : DecidablePred (RightwardInto t) := RightwardInto.decidable t

/-- The virtual conjunct-revealing rule of chapter 7 (61) decomposes a sentence into a revealed
`Y = S/$` and the residue `S\Y`. `RevealedResidue c` says `c` is such a residue. -/
def RevealedResidue : Cat Atom → Prop
  | .lslash x _ y => x = S ∧ RightwardInto S y
  | _ => False

instance : DecidablePred RevealedResidue
  | .lslash x _ y => inferInstanceAs (Decidable (x = S ∧ RightwardInto S y))
  | .rslash .. | .atom _ => isFalse id

-- (62)
theorem rightwardInto_transitiveCat_iff (a : Arrangement Constituent 3) :
    RightwardInto S (transitiveCat a) ↔ a.IsInitial .verb := by
  revert a; decide

/-- A clause of basic order `a` gaps in the direction of the cluster over its verb, or, when the
verb has none, in that of the cluster over the verb-initial verb the revealing rule exposes. -/
def predictedDirection (a : Arrangement Constituent 3) : Option GappingDirection :=
  gappingDirection (transitiveCat a) <|> gappingDirection vsoTV

/-- The gapping examples of chapter 7. -/
def gappingData : List Datum := Examples.all.filter (·.feature? "phenomenon" = some "gapping")

/-- In every gapping example of chapter 7, the construction is acceptable exactly when it gaps in
the direction its clause's basic order predicts. -/
theorem gapping_acceptable_iff :
    ∀ ex ∈ gappingData, ex.judgment = .acceptable ↔
      ex.parse? "gappingDirection" [("forward", .forward), ("backward", .backward)] =
        ((ex.feature? "wordOrder").bind Arrangement.ofLabel?).bind predictedDirection := by
  decide

/-! #### Other elliptical constructions -/

/-- The book's elliptical constructions. -/
inductive EllipsisType
  /-- "Dexter eats bread, and Warren, potatoes" (chapter 7 (62)). -/
  | gapping
  /-- "Dexter ran away, and Warren (too)" (chapter 7 (78a)). -/
  | stripping
  /-- "Dexter did something with the beans, but I don't know what" (chapter 7 (84a)). -/
  | sluicing
  /-- "Somebody has to do the job, but I know that I won't" (chapter 7 (84b)). -/
  | vpEllipsis
  deriving DecidableEq, Repr

/-- The category of the right conjunct each construction coordinates with a full sentence, as in
the gapped "Warren, potatoes" (67), the stripped "Warren" (81), and the sluiced and VP-elided
conjuncts (84). -/
def elidedConjunct : EllipsisType → Cat Atom
  | .gapping => S \ vsoTV
  | .stripping => S \ (S / NP)
  | .sluicing => S / (S / NP)
  | .vpEllipsis => S / IV

theorem revealedResidue_elidedConjunct_iff (e : EllipsisType) :
    RevealedResidue (elidedConjunct e) ↔ e = .gapping ∨ e = .stripping := by
  cases e <;> decide

end Gapping

/-! ### Cross-serial dependencies

In the Dutch fragment of chapter 6 a subordinate-clause raising verb takes its NP arguments
leftward and its infinitival complement rightward (12), and the one crossing rule, forward
crossed composition restricted to VP complements (14), builds the verb cluster, so the NPs
precede the whole cluster in the cross-serial order. -/

section CrossSerial

/-- The rules of the Dutch fragment are application and the Dutch forward crossed composition
of chapter 6 (14), `X/Y (Y\Z)$ ⇒ (X\Z)$` with `Y = VP`. -/
def dutchRules : RuleSystem Atom := fun _ a β ↦
  β = [] ∨ (a.side = .right ∧ a.cat = IV ∧ β.head?.map (·.side) = some .left)

instance (x : Cat Atom) (a : Cat.Arg Atom) (β : List (Cat.Arg Atom)) :
    Decidable (dutchRules x a β) :=
  inferInstanceAs (Decidable (β = [] ∨
    (a.side = .right ∧ a.cat = IV ∧ β.head?.map (·.side) = some .left)))

/-- The lexicon of chapter 6 (12), without the book's subordination feature. `zag` 'saw' and
`helpen` 'help' take their infinitival complement rightward and their NP arguments leftward. -/
def dutchLexicon : List (String × Cat Atom) :=
  [("ik", NP), ("Cecilia", NP), ("Henk", NP), ("de nijlpaarden", NP),
   ("zag", ((S \ NP) \ NP) / IV), ("helpen", (IV \ NP) / IV), ("voeren", IV \ NP)]

/-- In "(dat) ik Cecilia de nijlpaarden zag voeren" (chapter 6 (15)) `zag` crossed-composes with
`voeren`, and the NPs combine with the cluster by backward application. -/
def zagVoeren : Derivation String dutchRules S :=
  .bapp (.lex "ik" NP) (.bapp (.lex "Cecilia" NP) (.bapp (.lex "de nijlpaarden" NP)
    (.fcompx (.lex "zag" (((S \ NP) \ NP) / IV)) (.lex "voeren" (IV \ NP)))))

/-- In "(dat) ik Cecilia Henk de nijlpaarden zag helpen voeren" (chapter 6 (16)) `helpen`
crossed-composes with `voeren` and `zag` with the result at degree 2, so each NP is the argument
of the verb in the same position of the cluster, the cross-serial dependency. -/
def zagHelpenVoeren : Derivation String dutchRules S :=
  .bapp (.lex "ik" NP) (.bapp (.lex "Cecilia" NP) (.bapp (.lex "Henk" NP)
    (.bapp (.lex "de nijlpaarden" NP)
      (.node (r := (IV \ NP) \ NP) (c := (((S \ NP) \ NP) \ NP) \ NP)
        (.forward [⟨.left, .dot, NP⟩, ⟨.left, .dot, NP⟩] (by decide))
        (.lex "zag" (((S \ NP) \ NP) / IV))
        (.fcompx (.lex "helpen" ((IV \ NP) / IV)) (.lex "voeren" (IV \ NP)))))))

theorem crossSerial_derived :
    (zagVoeren.LexIn dutchLexicon ∧
      zagVoeren.yield = ["ik", "Cecilia", "de nijlpaarden", "zag", "voeren"]) ∧
    (zagHelpenVoeren.LexIn dutchLexicon ∧
      zagHelpenVoeren.yield =
        ["ik", "Cecilia", "Henk", "de nijlpaarden", "zag", "helpen", "voeren"]) := by
  decide

-- (14)
theorem not_dutchRules_raised :
    ¬ dutchRules (S \ NP) ⟨.right, .dot, (S \ NP) \ NP⟩ [⟨.left, .dot, NP⟩] := by
  decide

end CrossSerial

/-! ### Verb clusters and quantifier scope

A quantified argument takes scope over the tensed verb when it combines, as a functor, with a
constituent containing that verb (chapter 6, on (96) and (97)). In the verb-raising order the
verbs compose into such a constituent first. In the verb-projection-raising order the quantified
object must combine with the embedded verb before anything combines with the tensed one, so it
never takes the tensed verb in its scope, though the tensed verb can still compose. -/

section Quantification

/-- `VerbOrder` is the word order of a West Germanic verb cluster. -/
inductive VerbOrder
  /-- The object precedes the whole verb cluster. -/
  | verbRaising
  /-- The object follows the matrix verb. -/
  | verbProjectionRaising
  deriving DecidableEq, Repr, Inhabited

variable {R : RuleSystem Atom}

/-- The node `ru` over daughters spelling out `u` and `w` has a primary functor spelling out `q`
and a secondary containing `v`. -/
def FunctorOver {l r c : Cat Atom} (q : List String) (v : String) :
    Rule R l r c → List String → List String → Prop
  | .forward .., u, w => u = q ∧ v ∈ w
  | .backward .., u, w => w = q ∧ v ∈ u

instance {l r c : Cat Atom} (q : List String) (v : String) :
    ∀ (ru : Rule R l r c) (u w : List String), Decidable (FunctorOver q v ru u w)
  | .forward .., u, w => inferInstanceAs (Decidable (u = q ∧ v ∈ w))
  | .backward .., u, w => inferInstanceAs (Decidable (w = q ∧ v ∈ u))

/-- `ScopesOver q v d` holds when some node of `d` combines a functor spelling out `q` with a
constituent containing `v`, the configuration in which `q` takes scope over `v`. -/
def ScopesOver (q : List String) (v : String) : {c : Cat Atom} → Derivation String R c → Prop
  | _, .lex _ _ => False
  | _, .node ru d₁ d₂ =>
    FunctorOver q v ru d₁.yield d₂.yield ∨ ScopesOver q v d₁ ∨ ScopesOver q v d₂

instance ScopesOver.decidable (q : List String) (v : String) :
    ∀ {c : Cat Atom} (d : Derivation String R c), Decidable (ScopesOver q v d)
  | _, .lex _ _ => isFalse id
  | _, .node _ d₁ d₂ =>
    have := ScopesOver.decidable q v d₁
    have := ScopesOver.decidable q v d₂
    inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem ScopesOver.mem_yield {q : List String} {v : String} {c : Cat Atom}
    {d : Derivation String R c} (h : ScopesOver q v d) :
    (∀ x ∈ q, x ∈ d.yield) ∧ v ∈ d.yield := by
  induction d with
  | lex => exact h.elim
  | node ru d₁ d₂ ih₁ ih₂ =>
    simp only [Derivation.yield, List.mem_append]
    rcases h with h | h | h
    · cases ru <;> obtain ⟨rfl, hv⟩ := h <;> exact ⟨fun x hx ↦ by simp [hx], by simp [hv]⟩
    · exact ⟨fun x hx ↦ .inl ((ih₁ h).1 x hx), .inl (ih₁ h).2⟩
    · exact ⟨fun x hx ↦ .inr ((ih₂ h).1 x hx), .inr (ih₂ h).2⟩

/-- The verbs and the quantified object of the Dutch examples (99). The tensed equi verb
"probeert" 'tries' takes its infinitival complement rightward, "te zingen" 'to sing' its object
leftward, and "veel liederen" 'many songs' is raised order-preservingly over the verbs that take
it leftward. -/
def scopeLexicon : List (String × Cat Atom) :=
  [("probeert", IV / IV), ("veel liederen", NP.forwardTypeRaise IV), ("te zingen", IV \ NP)]

/-- The string of the example (99) in each verb order. -/
def orderString : VerbOrder → List String
  | .verbRaising => ["veel liederen", "probeert", "te zingen"]
  | .verbProjectionRaising => ["probeert", "veel liederen", "te zingen"]

/-- The quantified object takes scope over the tensed verb "probeert". -/
abbrev ObjectOutscopesTense {c : Cat Atom} (d : Derivation String R c) : Prop :=
  ScopesOver ["veel liederen"] "probeert" d

/-- The inverse reading of the order `o` is available when some derivation of its string over
the lexicon lets the quantified object take scope over the tensed verb. -/
def InverseAvailable (o : VerbOrder) : Prop :=
  ∃ e : Derivation String (.multimodal 2) IV,
    e.LexIn scopeLexicon ∧ e.yield = orderString o ∧ ObjectOutscopesTense e

/-- In the verb-raising order (99a) the cluster "probeert te zingen" forms by crossed
composition and the raised object applies to it. -/
def verbRaisingDeriv : Derivation String (.multimodal 2) IV :=
  .fapp (.lex "veel liederen" (NP.forwardTypeRaise IV))
    (.fcompx (.lex "probeert" (IV / IV)) (.lex "te zingen" (IV \ NP)))

/-- In the verb-projection-raising order (99b) the tensed verb can compose with the raised
object, but then the object is the tensed verb's secondary, not a functor over it. -/
def verbProjectionRaisingComposed : Derivation String (.multimodal 2) IV :=
  .fapp (.fcomp (.lex "probeert" (IV / IV)) (.lex "veel liederen" (NP.forwardTypeRaise IV)))
    (.lex "te zingen" (IV \ NP))

theorem verbProjectionRaisingComposed_hasComp_not_outscopes :
    verbProjectionRaisingComposed.LexIn scopeLexicon ∧
      verbProjectionRaisingComposed.yield = orderString .verbProjectionRaising ∧
      verbProjectionRaisingComposed.HasComp ∧
      ¬ ObjectOutscopesTense verbProjectionRaisingComposed := by
  decide

private theorem eq_or_eq_of_append_eq {a b c : String} {l₁ l₂ : List String}
    (h : l₁ ++ l₂ = [a, b, c]) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    (l₁ = [a] ∧ l₂ = [b, c]) ∨ (l₁ = [a, b] ∧ l₂ = [c]) := by
  rcases l₁ with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> simp_all

theorem not_outscopes_of_verbProjectionRaising {c : Cat Atom} (e : Derivation String R c)
    (hl : e.LexIn scopeLexicon) (hy : e.yield = orderString .verbProjectionRaising) :
    ¬ ObjectOutscopesTense e := by
  rcases e with ⟨t, c⟩ | ⟨ru, d₁, d₂⟩
  · simp [Derivation.yield, orderString] at hy
  simp only [Derivation.yield, orderString] at hy
  have hs := eq_or_eq_of_append_eq hy d₁.yield_ne_nil d₂.yield_ne_nil
  rintro (h | h | h)
  · cases ru <;> obtain ⟨h₁, -⟩ := h <;> rcases hs with ⟨hd₁, hd₂⟩ | ⟨hd₁, hd₂⟩ <;> simp_all
  · rcases hs with ⟨hd₁, -⟩ | ⟨hd₁, -⟩
    · simpa [hd₁] using h.mem_yield.1
    rcases d₁ with ⟨t, c⟩ | ⟨ru', a, b⟩
    · simp [Derivation.yield] at hd₁
    simp only [Derivation.yield] at hd₁
    have hab : a.yield = ["probeert"] ∧ b.yield = ["veel liederen"] := by
      rcases ha : a.yield with _ | ⟨x, _ | ⟨y, r⟩⟩
      · exact absurd ha a.yield_ne_nil
      · simp_all
      · have := b.yield_ne_nil
        simp_all
    rcases h with h | h | h
    · cases ru' with
      | forward => simp_all [FunctorOver]
      | backward =>
        obtain rfl := Derivation.eq_lex_of_yield_eq_singleton hab.2
        simp [Derivation.LexIn, scopeLexicon, Cat.forwardTypeRaise, IV] at hl
    · simpa [hab.1] using h.mem_yield.1
    · simpa [hab.2] using h.mem_yield.2
  · rcases hs with ⟨-, hd₂⟩ | ⟨-, hd₂⟩ <;> simpa [hd₂] using h.mem_yield.2

theorem inverseAvailable_iff (o : VerbOrder) : InverseAvailable o ↔ o = .verbRaising := by
  cases o
  · exact iff_of_true ⟨verbRaisingDeriv, by decide, rfl, by decide⟩ rfl
  · exact iff_of_false (fun ⟨e, hl, hy, h⟩ ↦ not_outscopes_of_verbProjectionRaising e hl hy h)
      (by decide)

/-- `scopeData` pairs each scope example's word order with the judgment on its inverse
reading, on which the quantified object outscopes the tensed verb. -/
def scopeData : List (VerbOrder × Judgment) :=
  Examples.all.filterMap fun ex ↦
    (ex.parse? "wordOrder" [("verbRaising", .verbRaising),
      ("verbProjectionRaising", .verbProjectionRaising)]).bind
      fun vo ↦ (ex.readings.lookup "inverse").map (vo, ·)

/-- The inverse reading is acceptable exactly where the quantified object can combine with a
constituent containing the tensed verb (examples (96) to (100); [bayer-1996], [kayne-1998],
[haegeman-van-riemsdijk-1986], [haegeman-1992]). -/
theorem inverse_acceptable_iff_available :
    ∀ d ∈ scopeData, d.2 = .acceptable ↔ InverseAvailable d.1 := by
  have key : ∀ d ∈ scopeData, d.2 = .acceptable ↔ d.1 = .verbRaising := by decide
  exact fun d hd ↦ (key d hd).trans (inverseAvailable_iff d.1).symm

theorem exists_verbProjectionRaising_unacceptable :
    ∃ d ∈ scopeData, d.1 = .verbProjectionRaising ∧ d.2 = .unacceptable := by
  decide

end Quantification

/-! ### Intonation and information structure

Alternative derivations of one string are alternative information structures, disambiguated
by tune: "(ANNA married)(MANNY)" (chapter 5 (14)) carves the composed derivation into a theme and
a rheme, and its mirror "(ANNA)(married MANNY)" (13) the applicative one. Prosodic phrases are
tune-marked constituents, so only constituents of the grammar can be phrases, the Sense Unit
Condition of [selkirk-1984]. -/

section Intonation

open CCG.Intonation Prosody

/-- The accents of "(ANNA married)(MANNY)" are a theme accent on "Anna" and a rheme accent on
"Manny", with "married" unaccented. -/
def annaMannyAccents : AccentAssignment String := fun w ↦
  match w with
  | "Anna" => some (.leading .L .H)
  | "Manny" => some (.mono .H)
  | _ => none

/-- "ANNA married" is the composed theme constituent, of category `S/NP`. -/
def anna_married : Derivation String (.multimodal 2) (S / NP) :=
  .fcomp (.lex "Anna" (S / (S \ NP))) (.lex "married" TV)

theorem anna_married_theme :
    anna_married.infoFeature annaMannyAccents = some .θ := rfl

theorem manny_rheme :
    (Derivation.lex (R := .multimodal 2) "Manny" NP).infoFeature annaMannyAccents = some .ρ :=
  rfl

/-- Folding the rheme into the theme's constituent clashes. The whole sentence projects no
single marking, so the tune forces the phrasing "[Anna married][Manny]". -/
theorem theme_rheme_clash :
    (Derivation.fapp anna_married (.lex "Manny" NP)).infoFeature annaMannyAccents
      = none := rfl

/-- The mirror answer "(ANNA)(married MANNY)" of chapter 5 (13) has a rheme accent on "Anna"
and a theme accent on "Manny". -/
def mannyThemeAccents : AccentAssignment String := fun w ↦
  match w with
  | "Anna" => some (.mono .H)
  | "Manny" => some (.leading .L .H)
  | _ => none

-- (14)
theorem married_manny_theme :
    (Derivation.fapp (R := .multimodal 2) (.lex "married" TV) (.lex "Manny" NP)).infoFeature
        mannyThemeAccents = some .θ ∧
      anna_married.infoFeature mannyThemeAccents = some .ρ :=
  ⟨rfl, rfl⟩

/-- The utterance consists of two tune-marked phrases. -/
def annaMannyUtterance : List (ProsodicPhrase String (RuleSystem.multimodal (α := Atom) 2)) :=
  [⟨_, anna_married, themeTune⟩, ⟨_, .lex "Manny" NP, rhemeTune⟩]

theorem annaMannyUtterance_infoStructure :
    (extractInfoStructure annaMannyUtterance).map (fun i ↦ (i.theme.map (·.cat), i.rheme.cat))
      = some (some (S / NP), NP) := rfl

end Intonation

/-! ### Truth conditions

Derivations interpreted compositionally over the toy model: a true sentence and a false one. -/

section TruthConditions

def mary_sleeps : Derivation String (.multimodal 2) S := .bapp (.lex "Mary" NP) (.lex "sleeps" IV)

theorem ccg_predicts_john_sleeps : ∃ p, john_sleeps.interp semLexicon = some p ∧ p :=
  ⟨_, rfl, rfl⟩

theorem ccg_predicts_mary_sleeps : ∃ p, mary_sleeps.interp semLexicon = some p ∧ ¬ p :=
  ⟨_, rfl, nofun⟩

theorem ccg_predicts_john_sees_mary : ∃ p, john_sees_mary.interp semLexicon = some p ∧ p :=
  ⟨_, rfl, .inl ⟨rfl, rfl⟩⟩

end TruthConditions

/-! ### The tune terminal as an intonation-phrase terminal -/

section BPTerminal

open Prosody BeckmanPierrehumbert1986 CCG.Intonation

/-- `ipToTune ip accent` is the tune with pitch accent `accent` whose terminal contour is the
final phrase accent and boundary tone of the intonation phrase `ip`. -/
def ipToTune (ip : IntonationPhrase) (accent : PitchAccent) : Tune :=
  ⟨accent, ip.terminalContour⟩

/-- A declarative intonation phrase has an L phrase accent and an L% boundary. -/
def declarativeIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .L }

/-- A continuation-rise intonation phrase has an L phrase accent and an H% boundary. -/
def continuationIP : IntonationPhrase :=
  { ips := [{ aps := [accentedAP], phraseAccent := .L }], boundaryTone := .H }

theorem ipToTune_eq_tunes :
    ipToTune declarativeIP (.mono .H) = rhemeTune ∧
      ipToTune continuationIP (.leading .L .H) = themeTune := by
  decide

end BPTerminal

end Steedman2000
