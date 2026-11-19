module

public import Linglib.Data.Examples.Steedman2000
public import Linglib.Fragments.English.Coordination
public import Linglib.Semantics.Coordinator
public import Linglib.Syntax.CCG.Derivation
public import Linglib.Syntax.CCG.Grammar
public import Linglib.Syntax.CCG.Semantics
public import Linglib.Syntax.CCG.Invariant
public import Linglib.Syntax.CCG.Intonation
public import Linglib.Syntax.WordOrder
public import Mathlib.GroupTheory.Perm.Basic
public import Linglib.Data.Examples.Readers

/-!
# Steedman (2000): The Syntactic Process

In Steedman's combinatory categorial grammar the slash directions of lexical categories fix
word order, and composition and type-raising make strings such as a subject and a
transitive verb into constituents. This file derives the book's analyses of non-constituent
coordination, gapping, Dutch cross-serial dependencies, scope in verb clusters and
intonational phrasing over the library's CCG, and interprets the derivations in every model
of their constants.

## Implementation notes

* Type-raising and coordination are lexical in the library's CCG, so the book's raising rules
  appear as raised entries and its coordination rule `<Φ>` as a conjunction of category
  `(X\⋆X)/⋆X`. A logical form is a function of what its constants denote: a raised name has
  the Montague lift, and coordination at `S/NP` Partee and Rooth's generalized conjunction.
* The toy categories drop the book's features (subordination, case, agreement), so Dutch
  crossed composition is restricted to `VP` complements rather than the book's `VP_{-SUB}`.
* The revealing rule (61) is a unary decomposition outside the binary derivations, so it enters
  only as the condition on the categories it reveals (`RevealedResidue`).
* Boundary tones are not elements of the strings: an utterance's division into prosodic phrases
  is given, and each phrase projects the INFORMATION feature of its accents.

## References

* [steedman-2000]
* [pentus-1993]
* [ross-1970]
* [bayer-1996]
* [kayne-1998]
* [haegeman-van-riemsdijk-1986]
* [haegeman-1992]
* [selkirk-1984]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Steedman2000

open CCG Interpreter

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
def atomTy : Atom → Ty Unit
  | .S => .t
  | .NP => .base ()

example : TV.toTy atomTy = (.base () ⇒ .base () ⇒ .t) := rfl

/-! ### The lexicon

The toy English fragment. Names, verbs and the coordinator at `S` translate to constants. -/

/-- The type of individuals. -/
abbrev ind : Ty Unit := .base ()

/-- The constants of the logical forms: the names, the verbs and sentential conjunction. -/
inductive Const : Ty Unit → Type
  | john : Const ind
  | mary : Const ind
  | pizza : Const ind
  | sleeps : Const (ind ⇒ .t)
  | sees : Const (ind ⇒ ind ⇒ .t)
  | eats : Const (ind ⇒ ind ⇒ .t)
  | conj : Const (.t ⇒ .t ⇒ .t)

/-- `conj c` is the category `(c \⋆ c) /⋆ c` of a conjunction coordinating constituents of
category `c`. Its `star` slashes confine it to application. -/
def conj (c : Cat Atom) : Cat Atom := (c \⋆ c) /⋆ c

local notation "Entry" => LexEntry String atomTy Const

namespace Lex

def john : Entry NP := ⟨"John", fun I ↦ I .john⟩

def mary : Entry NP := ⟨"Mary", fun I ↦ I .mary⟩

def pizza : Entry NP := ⟨"pizza", fun I ↦ I .pizza⟩

/-- A raised name has the Montague lift `λP.P a`. -/
def johnT : Entry (S / (S \ NP)) := ⟨"John", fun I P ↦ P (I .john)⟩

def maryT : Entry (S / (S \ NP)) := ⟨"Mary", fun I P ↦ P (I .mary)⟩

def sleeps : Entry IV := ⟨"sleeps", fun I ↦ I .sleeps⟩

def sees : Entry TV := ⟨"sees", fun I ↦ I .sees⟩

def eats : Entry TV := ⟨"eats", fun I ↦ I .eats⟩

def and : Entry (conj S) := ⟨"and", fun I ↦ I .conj⟩

/-- The coordinator at `S/NP` has the generalized conjunction `λQλPλx.P x ∧ Q x` of
[partee-rooth-1983]. -/
def andSNP : Entry (conj (S / NP)) := ⟨"and", fun I Q P x ↦ I .conj (Q x) (P x)⟩

end Lex

/-! ### Word order

Slash direction encodes word order: `TV = (S\NP)/NP` looks right for the object and the
resulting `S\NP` left for the subject, which enforces SVO. -/

def john_sleeps : Derivation Entry (.multimodal 2) S :=
  .bapp (.lex NP Lex.john) (.lex IV Lex.sleeps)

def john_sees_mary : Derivation Entry (.multimodal 2) S :=
  .bapp (.lex NP Lex.john) (.fapp (.lex TV Lex.sees) (.lex NP Lex.mary))

-- The canonical derivation is harmonic, with the verb between its arguments.
example : john_sees_mary.IsHarmonic ∧ john_sees_mary.cats = [NP, TV, NP] := by decide

/-- Slash direction enforces word order: no harmonic derivation of a sentence, in any rule system
and over any lexicon, has the transitive verb before both of its arguments. The categories
`TV`, `NP`, `NP` have the counts of a sentence, and it is their order that rules them out. -/
theorem cats_ne_verb_initial {W : Cat Atom → Type*} {R : RuleSystem Atom} (d : Derivation W R S)
    (h : d.IsHarmonic) : d.cats ≠ [TV, NP, NP] := fun hc ↦ by
  have := d.eval_eq_prod_cats (G := Equiv.Perm (Fin 3))
    (fun | .S => Equiv.swap 0 1 | .NP => Equiv.swap 1 2) h
  rw [hc] at this
  exact absurd this (by decide)

/-! ### Non-constituent coordination -/

section Coordination

/-- The type-raised subject "John" is a lexical leaf of category `S/(S\NP)`. -/
def john_tr : Derivation Entry (.multimodal 2) (S / (S \ NP)) := .lex (S / (S \ NP)) Lex.johnT

def mary_tr : Derivation Entry (.multimodal 2) (S / (S \ NP)) := .lex (S / (S \ NP)) Lex.maryT

/-- "John sees" is the type-raised subject composed with the transitive verb, a constituent of
category `S/NP`. -/
def john_sees : Derivation Entry (.multimodal 2) (S / NP) := .fcomp john_tr (.lex TV Lex.sees)

def mary_eats : Derivation Entry (.multimodal 2) (S / NP) := .fcomp mary_tr (.lex TV Lex.eats)

-- The `star` slash also blocks composing into the conjunction: no primary composes `S\⋆S`.
example (m : Modality) : ¬ RuleSystem.multimodal 2 S ⟨.right, m, S⟩ [⟨.left, .star, S⟩] :=
  RuleSystem.not_multimodal_of_star_mem List.mem_cons_self rfl

/-- "John sees and Mary eats" coordinates two `S/NP` constituents through the lexical
conjunction, as in the book's "Anna married, and I detest". -/
def john_sees_and_mary_eats : Derivation Entry (.multimodal 2) (S / NP) :=
  .bapp john_sees (.fapp (.lex (conj (S / NP)) Lex.andSNP) mary_eats)

def john_sees_and_mary_eats_pizza : Derivation Entry (.multimodal 2) S :=
  .fapp john_sees_and_mary_eats (.lex NP Lex.pizza)

theorem john_sees_and_mary_eats_pizza_yield :
    john_sees_and_mary_eats_pizza.words.yield =
      ["John", "sees", "and", "Mary", "eats", "pizza"] :=
  rfl

variable {D : Unit → Type} (I : ∀ {ty : Ty Unit}, Const ty → ty.Dom D)

/-- "John sees Mary" with a type-raised subject produces the same truth value as the
canonical derivation. -/
def john_sees_mary_via_tr : Derivation Entry (.multimodal 2) S :=
  .fapp john_tr (.fapp (.lex TV Lex.sees) (.lex NP Lex.mary))

theorem interp_john_sees_mary_via_tr :
    john_sees_mary_via_tr.interp I = john_sees_mary.interp I := rfl

theorem coord_interp_pointwise (e : D ()) :
    john_sees_and_mary_eats.interp I e =
      I .conj (mary_eats.interp I e) (john_sees.interp I e) := rfl

/-- The spelled-out paraphrase is "John sees pizza and Mary eats pizza". -/
def john_sees_pizza_and_mary_eats_pizza : Derivation Entry (.multimodal 2) S :=
  .bapp (.bapp (.lex NP Lex.john) (.fapp (.lex TV Lex.sees) (.lex NP Lex.pizza)))
    (.fapp (.lex (conj S) Lex.and)
      (.bapp (.lex NP Lex.mary) (.fapp (.lex TV Lex.eats) (.lex NP Lex.pizza))))

/-- The non-constituent coordination and its spelled-out paraphrase receive the same truth
conditions, since the composed derivation yields the canonical predicate-argument
structure. -/
theorem nonConstituentCoord_eq_spelledOut :
    john_sees_and_mary_eats_pizza.interp I = john_sees_pizza_and_mary_eats_pizza.interp I := rfl

/-- The constants of a coordination fragment: two sentences and the two coordinators. -/
inductive PQ : Ty Unit → Type
  | p : PQ .t
  | q : PQ .t
  | conj : PQ (.t ⇒ .t ⇒ .t)
  | disj : PQ (.t ⇒ .t ⇒ .t)

/-- An interpretation of the coordination fragment in which `p` is true and `q` false, and the
English coordinators denote the Boolean operation of their role. -/
def pqConst : {ty : Ty Unit} → PQ ty → ty.Dom fun _ ↦ Unit
  | _, .p => True
  | _, .q => False
  | _, .conj => show Prop → Prop → Prop from fun q p ↦ English.Coordination.and_.denote {p, q}
  | _, .disj => show Prop → Prop → Prop from fun q p ↦ English.Coordination.or_.denote {p, q}

/-- "p and q" and "p or q" over the coordination fragment. -/
def pAndQ : Derivation (LexEntry String atomTy PQ) (.multimodal 2) S :=
  .bapp (.lex S ⟨"p", fun I ↦ I .p⟩)
    (.fapp (.lex (conj S) ⟨"and", fun I ↦ I .conj⟩) (.lex S ⟨"q", fun I ↦ I .q⟩))

def pOrQ : Derivation (LexEntry String atomTy PQ) (.multimodal 2) S :=
  .bapp (.lex S ⟨"p", fun I ↦ I .p⟩)
    (.fapp (.lex (conj S) ⟨"or", fun I ↦ I .disj⟩) (.lex S ⟨"q", fun I ↦ I .q⟩))

theorem coord_role_load_bearing : pAndQ.interp pqConst ≠ pOrQ.interp pqConst := by
  have hand : pAndQ.interp pqConst = (True ∧ False) := sInf_pair (a := True) (b := False)
  have hor : pOrQ.interp pqConst = (True ∨ False) := sSup_pair (a := True) (b := False)
  rw [hand, hor]
  exact fun h ↦ ((iff_of_eq h).mpr (Or.inl trivial)).2

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
  | .slash .left x _ a => some (Cat.forwardTypeRaise a x)
  | .slash .right x _ a => some (Cat.backwardTypeRaise a x)
  | .atom _ => none

/-- `hcomp` is harmonic composition, the order-preserving rules `>B` and `<B`. -/
def hcomp : Cat Atom → Cat Atom → Option (Cat Atom)
  | .slash .right x _ y, .slash .right y' n z => if y = y' then some (.slash .right x n z) else none
  | .slash .left y' n z, .slash .left x _ y => if y = y' then some (.slash .left x n z) else none
  | _, _ => none

/-- `cluster v` is the category of the argument cluster over the transitive verb category
`v`. The verb's two arguments are raised over the functions that seek them and composed
harmonically, in whichever order the rules allow. -/
def cluster (v : Cat Atom) : Option (Cat Atom) :=
  match v with
  | .slash .left inner _ _ | .slash .right inner _ _ => do
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
def backwardGappedConjunct : Derivation (fun _ ↦ String) (.multimodal 2) (S / sovTV) :=
  .fcomp (.lex (S / (S \ NP)) "Ken-ga") (.lex ((S \ NP) / sovTV) "Naomi-o")

theorem backwardGappedConjunct_yield :
    backwardGappedConjunct.yield = ["Ken-ga", "Naomi-o"] := rfl

/-- The forward-gapped English conjunct "Warren, potatoes" of chapter 7 (67), a cluster over a
virtual verb-initial verb, by backward raising and backward composition. -/
def gappedConjunct : Derivation (fun _ ↦ String) (.multimodal 2) (S \ vsoTV) :=
  .bcomp (.lex ((S / NP) \ vsoTV) "Warren") (.lex (S \ (S / NP)) "potatoes")

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
    | .slash .right .. => .backward
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
  | .slash .right x m y => Cat.slash .right x m y = t ∨ RightwardInto t x
  | c => c = t

/-- `RightwardInto t` is decided by recursion on the category. -/
def RightwardInto.decidable (t : Cat Atom) : ∀ c, Decidable (RightwardInto t c)
  | .slash .right x m y =>
    have := RightwardInto.decidable t x
    inferInstanceAs (Decidable (Cat.slash .right x m y = t ∨ RightwardInto t x))
  | .slash .left x m y => inferInstanceAs (Decidable (Cat.slash .left x m y = t))
  | .atom a => inferInstanceAs (Decidable (Cat.atom a = t))

instance (t : Cat Atom) : DecidablePred (RightwardInto t) := RightwardInto.decidable t

/-- The virtual conjunct-revealing rule of chapter 7 (61) decomposes a sentence into a revealed
`Y = S/$` and the residue `S\Y`. `RevealedResidue c` says `c` is such a residue. -/
def RevealedResidue : Cat Atom → Prop
  | .slash .left x _ y => x = S ∧ RightwardInto S y
  | _ => False

instance : DecidablePred RevealedResidue
  | .slash .left x _ y => inferInstanceAs (Decidable (x = S ∧ RightwardInto S y))
  | .slash .right .. | .atom _ => isFalse id

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
def zagVoeren : Derivation (fun _ ↦ String) dutchRules S :=
  .bapp (.lex NP "ik") (.bapp (.lex NP "Cecilia") (.bapp (.lex NP "de nijlpaarden")
    (.fcompx (.lex (((S \ NP) \ NP) / IV) "zag") (.lex (IV \ NP) "voeren"))))

/-- In "(dat) ik Cecilia Henk de nijlpaarden zag helpen voeren" (chapter 6 (16)) `helpen`
crossed-composes with `voeren` and `zag` with the result at degree 2, so each NP is the argument
of the verb in the same position of the cluster, the cross-serial dependency. -/
def zagHelpenVoeren : Derivation (fun _ ↦ String) dutchRules S :=
  .bapp (.lex NP "ik") (.bapp (.lex NP "Cecilia") (.bapp (.lex NP "Henk")
    (.bapp (.lex NP "de nijlpaarden")
      (.node (r := (IV \ NP) \ NP) (c := (((S \ NP) \ NP) \ NP) \ NP)
        (.forward [⟨.left, .dot, NP⟩, ⟨.left, .dot, NP⟩] (by decide))
        (.lex (((S \ NP) \ NP) / IV) "zag")
        (.fcompx (.lex ((IV \ NP) / IV) "helpen") (.lex (IV \ NP) "voeren"))))))

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
def ScopesOver (q : List String) (v : String) :
    {c : Cat Atom} → Derivation (fun _ ↦ String) R c → Prop
  | _, .lex _ _ => False
  | _, .node ru d₁ d₂ =>
    FunctorOver q v ru d₁.yield d₂.yield ∨ ScopesOver q v d₁ ∨ ScopesOver q v d₂

instance ScopesOver.decidable (q : List String) (v : String) :
    ∀ {c : Cat Atom} (d : Derivation (fun _ ↦ String) R c), Decidable (ScopesOver q v d)
  | _, .lex _ _ => isFalse id
  | _, .node _ d₁ d₂ =>
    have := ScopesOver.decidable q v d₁
    have := ScopesOver.decidable q v d₂
    inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem ScopesOver.mem_yield {q : List String} {v : String} {c : Cat Atom}
    {d : Derivation (fun _ ↦ String) R c} (h : ScopesOver q v d) :
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
abbrev ObjectOutscopesTense {c : Cat Atom} (d : Derivation (fun _ ↦ String) R c) : Prop :=
  ScopesOver ["veel liederen"] "probeert" d

/-- The inverse reading of the order `o` is available when some derivation of its string over
the lexicon lets the quantified object take scope over the tensed verb. -/
def InverseAvailable (o : VerbOrder) : Prop :=
  ∃ e : Derivation (fun _ ↦ String) (.multimodal 2) IV,
    e.LexIn scopeLexicon ∧ e.yield = orderString o ∧ ObjectOutscopesTense e

/-- In the verb-raising order (99a) the cluster "probeert te zingen" forms by crossed
composition and the raised object applies to it. -/
def verbRaisingDeriv : Derivation (fun _ ↦ String) (.multimodal 2) IV :=
  .fapp (.lex (NP.forwardTypeRaise IV) "veel liederen")
    (.fcompx (.lex (IV / IV) "probeert") (.lex (IV \ NP) "te zingen"))

/-- In the verb-projection-raising order (99b) the tensed verb can compose with the raised
object, but then the object is the tensed verb's secondary, not a functor over it. -/
def verbProjectionRaisingComposed : Derivation (fun _ ↦ String) (.multimodal 2) IV :=
  .fapp (.fcomp (.lex (IV / IV) "probeert") (.lex (NP.forwardTypeRaise IV) "veel liederen"))
    (.lex (IV \ NP) "te zingen")

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

theorem not_outscopes_of_verbProjectionRaising {c : Cat Atom} (e : Derivation (fun _ ↦ String) R c)
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
by intonation: "(ANNA married)(MANNY)" (chapter 5 (14)) carves the composed derivation into a
theme and a rheme, and its mirror "(ANNA)(married MANNY)" (13) the applicative one. A prosodic
phrase is a constituent of the grammar, the Sense Unit Condition of [selkirk-1984], and its
words must agree on the INFORMATION feature. -/

section Intonation

open Prosody

/-- The marking of "(ANNA married)(MANNY)": the theme accent on "Anna", the rheme accent on
"Manny" and the null tone on "married". -/
def annaMannyMark : String → InfoFeature
  | "Anna" => .θ
  | "Manny" => .ρ
  | _ => ⊥

/-- "Anna married" is the composed constituent of category `S/NP`. -/
def anna_married : Derivation (fun _ ↦ String) (.multimodal 2) (S / NP) :=
  .fcomp (.lex (S / (S \ NP)) "Anna") (.lex TV "married")

-- (14): the theme accent spreads over the unaccented verb
theorem anna_married_theme :
    anna_married.infoFeature annaMannyMark = ((.θ : InfoFeature) : WithTop InfoFeature) := rfl

theorem manny_rheme :
    (Derivation.lex (R := .multimodal 2) NP "Manny").infoFeature annaMannyMark
      = ((.ρ : InfoFeature) : WithTop InfoFeature) := rfl

/-- Under the accents of (14) no derivation of "Anna married Manny", of any category and by
any rules, is a single prosodic phrase: the theme accent and the rheme accent clash, so the
utterance divides into phrases. -/
theorem anna_married_manny_clash {c : Cat Atom} (d : Derivation (fun _ ↦ String) (.multimodal 2) c)
    (h : d.yield = ["Anna", "married", "Manny"]) : d.infoFeature annaMannyMark = ⊤ :=
  Derivation.infoFeature_eq_top_of_not_compat (t := "Anna") (u := "Manny") (by simp [h])
    (by simp [h]) (by
      rw [show annaMannyMark "Anna" = .θ from rfl, show annaMannyMark "Manny" = .ρ from rfl]
      simp)

/-- The marking of the mirror answer "(ANNA)(married MANNY)": the rheme accent on "Anna" and
the theme accent on "Manny". -/
def mannyThemeMark : String → InfoFeature
  | "Anna" => .ρ
  | "Manny" => .θ
  | _ => ⊥

-- (13)
theorem married_manny_theme :
    (Derivation.fapp (R := .multimodal 2) (.lex TV "married") (.lex NP "Manny")).infoFeature
        mannyThemeMark = ((.θ : InfoFeature) : WithTop InfoFeature) ∧
      (Derivation.lex (R := .multimodal 2) (S / (S \ NP)) "Anna").infoFeature mannyThemeMark
        = ((.ρ : InfoFeature) : WithTop InfoFeature) :=
  ⟨rfl, rfl⟩

end Intonation

/-! ### Meanings

In every model of the constants, a derivation over the lexicon means what its predicate-argument
structure says. -/

section TruthConditions

variable {D : Unit → Type} (I : ∀ {ty : Ty Unit}, Const ty → ty.Dom D)

def mary_sleeps : Derivation Entry (.multimodal 2) S :=
  .bapp (.lex NP Lex.mary) (.lex IV Lex.sleeps)

theorem interp_john_sleeps : john_sleeps.interp I = I .sleeps (I .john) := rfl

theorem interp_mary_sleeps : mary_sleeps.interp I = I .sleeps (I .mary) := rfl

theorem interp_john_sees_mary : john_sees_mary.interp I = I .sees (I .mary) (I .john) := rfl

end TruthConditions

end Steedman2000
