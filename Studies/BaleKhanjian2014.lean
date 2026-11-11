module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Mode.Basic
public import Linglib.Semantics.Composition.CallByValue
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.LiftRel
public import Mathlib.Data.PFun
public import Linglib.Semantics.Plurality.Number
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Semantics.Reference.Iota
public import Linglib.Data.Examples.BaleKhanjian2014
public import Linglib.Data.Examples.Readers

/-!
# Bale and Khanjian 2014: syntactic complexity and competition in Western Armenian

Western Armenian singular nouns have general number and plurals are strictly plural, yet a
definite singular denotes a single individual. The singular indefinite is a bare noun phrase, so
the plural indefinite, which has a determiner phrase, is [no structural
alternative](##pluralIndefinite_not_mem_structuralAlternatives) to it and does not compete. In a
definite the marker *-n* applies *sup* to the number phrase, and Maximize Presupposition there,
against the plural alternative, [makes the singular strictly singular](##strengthen_numPStar_sg).
Under a numeral the two definites presuppose the same, but at the number phrase Maximize
Presupposition [still rules out the singular](##minimalFor_defined_numPStar_iff). The purely
syntactic account, whose null singular is $[+\text{atomic}]$, leaves [a numeral on a singular
nothing to count](##numeral_atomsOf_eq_empty).

## Implementation notes

Denotations are the paper's: a noun is a set of individuals, the number heads and the numeral are
functions on sets, and *sup* and the choice function are partial functions, the only two. A tree
is interpreted by functional application over worlds that are sets of boys, a function applied
to an undefined argument being undefined, and a tree's presupposition is the set of worlds where
it has a defined value.
The plural is Harbour's $[-\text{atomic}]$, the paper's *sup* is the set of greatest members, and
the null determiner +DEF is `iota`, the factoring of `Linglib/Semantics/Reference/Iota.lean`. The
allomorphs *-n* and *-ə* are one morpheme and the verb's agreement is spelled out with the subject,
so a plural alternative replaces the number head alone, as the paper derives it. The number head,
the numeral and the adjoined definite marker have their own categories; the paper leaves the last
two unlabelled, and as a determiner the marker could be replaced by +DEF.

The paper puts Maximize Presupposition below the determiner to separate the numeral definites. With
the marker adjoined to the number phrase, that placement is needed for the bare singular definite
too: at the determiner phrase, +DEF over the bare number phrase is an alternative presupposing
exactly one boy, and [strengthening against it leaves nothing](##strengthen_definiteDP_sg_eq_empty).

## TODO

The scope of indefinites under negation, which motivates the structures, the plural in a
restrictor and in a bound possessive, and competition by informativeness are not modelled.

## References

* [bale-khanjian-2014]
* [katzir-2007]
* [bliss-2004]
* [singh-2011]
* [winter-2001b]
* [link-1983]
* [harbour-2014]
* [donabedian-1993]
-/

@[expose] public section

namespace BaleKhanjian2014

open Mereology Number Presupposition PhraseStructure Tree Interpreter

/-! ### Denotations -/

section Denotations

variable {α : Type*} {B x : Finset α}

/-- *dəgha* 'boy' over the boys `B` denotes every nonempty group of them, general number (9a):
Link's `*` of the boys, by `Mereology.algClosure_image_singleton`. -/
def boy (B : Finset α) : Set (Finset α) := Set.Ioc ∅ B

theorem mem_boy : x ∈ boy B ↔ x ⊆ B ∧ 1 ≤ x.card := by
  rw [boy, Set.mem_Ioc, Finset.empty_ssubset, Finset.one_le_card, and_comm]

/-- The head of the number phrase: the null singular *-∅* or the plural *-ner*. -/
inductive NumberHead
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

/-- A number head restricts the noun it heads: *-ner* to its non-atoms, Harbour's
$[-\text{atomic}]$ (19), and the null singular, on this analysis, to nothing. -/
def NumberHead.denote {E : Type*} [PartialOrder E] : NumberHead → Set E → Set E
  | .sg, X => X
  | .pl, X => {x | nonAtomsOf (· ∈ X) x}

-- (15b): the singular noun holds of the groups of one or more boys
theorem denote_sg_boy : NumberHead.sg.denote (boy B) = {x | x ⊆ B ∧ 1 ≤ x.card} :=
  Set.ext fun _ ↦ mem_boy

-- (16b): the plural noun holds of the groups of two or more
theorem denote_pl_boy : NumberHead.pl.denote (boy B) = {x | x ⊆ B ∧ 2 ≤ x.card} := by
  ext x
  simp only [NumberHead.denote, Set.mem_ofPred_eq, nonAtomsOf, mem_boy, atom_finset_iff_card_eq_one,
    and_assoc]
  exact and_congr_right fun _ ↦ by omega

/-- A numeral restricts a noun to its groups of that many (p. 16): *meg* 'one', *yergu* 'two'. -/
def numeral (k : ℕ) (X : Set (Finset α)) : Set (Finset α) := {x ∈ X | x.card = k}

-- (34), (35): under a numeral the singular and the plural mean the same
theorem numeral_denote_boy {k : ℕ} (hk : 2 ≤ k) (n : NumberHead) :
    numeral k (n.denote (boy B)) = numeral k (boy B) := by
  cases n
  · rfl
  · ext x
    simp only [numeral, denote_pl_boy, mem_boy, Set.mem_ofPred_eq, and_assoc]
    exact and_congr_right fun _ ↦ by omega

/-- On the purely syntactic account, whose null singular restricts the noun to its atoms (19), a
numeral other than *meg* 'one' on a singular number phrase denotes nothing, which is why that
account needs the numeral *yergu* to be ambiguous (p. 13). -/
theorem numeral_atomsOf_eq_empty {k : ℕ} (hk : k ≠ 1) (X : Set (Finset α)) :
    numeral k {x | atomsOf (· ∈ X) x} = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨⟨_, ha⟩, hc⟩ ↦ hk (hc ▸ atom_finset_iff_card_eq_one.1 ha)

end Denotations

/-! ### The supremum -/

section Sup

variable {E : Type*} [PartialOrder E] {X : Set E}

/-- *sup* (37) sends a set to its members that bound it: the singleton of the supremum it
contains, or nothing. The definite is the choice function `iota` after it (p. 20). -/
def sup (X : Set E) : Set E := X ∩ upperBounds X

theorem mem_sup {x : E} : x ∈ sup X ↔ IsGreatest X x := .rfl

theorem sup_subsingleton : (sup X).Subsingleton := fun _ ha _ hb ↦ IsGreatest.unique ha hb

-- the choice function adds no presupposition to that of *sup*
@[simp] theorem iota_sup_isSome_iff : (iota (sup X)).isSome ↔ (sup X).Nonempty :=
  sup_subsingleton.iota_isSome_iff

variable {α : Type*} {B : Finset α} {k : ℕ}

theorem sup_card_le : sup {x | x ⊆ B ∧ k ≤ x.card} = {x | x = B ∧ k ≤ B.card} := by
  ext x
  refine ⟨fun ⟨⟨hxB, hk⟩, hub⟩ ↦ ?_, ?_⟩
  · have hB : k ≤ B.card := hk.trans (Finset.card_le_card hxB)
    exact ⟨subset_antisymm hxB (hub ⟨subset_rfl, hB⟩), hB⟩
  · rintro ⟨rfl, hk⟩
    exact ⟨⟨subset_rfl, hk⟩, fun _ hy ↦ hy.1⟩

theorem nonempty_sup_card_le : (sup {x | x ⊆ B ∧ k ≤ x.card}).Nonempty ↔ k ≤ B.card := by
  rw [sup_card_le]
  exact ⟨fun ⟨_, h⟩ ↦ h.2, fun h ↦ ⟨B, rfl, h⟩⟩

end Sup

/-! ### Structures -/

/-- The categories of the paper's trees: the noun, the number head, the numeral, the adjoined
definite marker, the determiner, the verb, and the clause. -/
inductive Cat
  | N
  | Num
  | Numeral
  | Def
  | D
  | V
  | S
  deriving DecidableEq, Repr

/-- The morphemes of the paper's trees. -/
inductive Morpheme
  /-- *dəgha* 'boy'. -/
  | boy
  /-- A number head. -/
  | num (n : NumberHead)
  /-- The definite marker, *-n* after vowels and *-ə* after consonants (fn. 11). -/
  | def_
  /-- The null determiner +DEF of (37a). -/
  | plusDef
  /-- The null existential determiner of (20). -/
  | exists_
  /-- *yergu* 'two'. -/
  | two
  /-- *vaze-ts* 'ran'. -/
  | run
  deriving DecidableEq, Fintype, Repr

/-- The category of a morpheme. -/
def Morpheme.cat : Morpheme → Cat
  | .boy => .N
  | .num _ => .Num
  | .two => .Numeral
  | .def_ => .Def
  | .plusDef | .exists_ => .D
  | .run => .V

/-- The lexicon the substitutions draw on: every morpheme under its category. -/
def lexicon : Finset (Tree Cat Morpheme) :=
  Finset.univ.image fun m ↦ .terminal m.cat m

/-- The number phrase over *dəgha* with head `n` (19). -/
def numP (n : NumberHead) : Tree Cat Morpheme :=
  .node .Num [.node .N [.terminal .N .boy], .terminal .Num (.num n)]

/-- NumP*, the definite marker adjoined to the number phrase (37a). -/
def numPStar (n : NumberHead) : Tree Cat Morpheme :=
  .adjoin .Num [numP n, .terminal .Def .def_]

/-- The definite *dəgha-n* 'the boy' (11b) and its plural, +DEF over NumP* (37a). -/
def definiteDP (n : NumberHead) : Tree Cat Morpheme :=
  .node .D [numPStar n, .terminal .D .plusDef]

/-- +DEF over the bare number phrase, the definite marker deleted. -/
def bareDP (n : NumberHead) : Tree Cat Morpheme :=
  .node .D [numP n, .terminal .D .plusDef]

/-- *Yergu dəgha-n* (14a) and *yergu dəgha-ner-ə* (14b), the numeral above NumP* (39). -/
def numeralDP (n : NumberHead) : Tree Cat Morpheme :=
  .node .D [.adjoin .Num [.terminal .Numeral .two, numPStar n], .terminal .D .plusDef]

/-- *Dəgha vaze-ts* (3), a bare noun phrase whose existential force the verb supplies (21). -/
def singularIndefinite : Tree Cat Morpheme :=
  .node .S [.node .N [.terminal .N .boy], .node .V [.terminal .V .run]]

/-- *Dəgha-ner vaze-ts-in* (7), a determiner phrase with the null existential (20). -/
def pluralIndefinite : Tree Cat Morpheme :=
  .node .S [.node .D [.terminal .D .exists_, numP .pl], .node .V [.terminal .V .run]]

/-- *Yergu dəgha vaze-ts* (10a) and *yergu dəgha-ner vaze-ts-in* (10b), determiner phrases with
the null existential (33). -/
def numeralIndefinite (n : NumberHead) : Tree Cat Morpheme :=
  .node .S [.node .D [.terminal .D .exists_, .adjoin .Num [.terminal .Numeral .two, numP n]],
    .node .V [.terminal .V .run]]

/-- The singular indefinite does not compete with the plural indefinite: the plural has a
determiner phrase, and neither the singular nor the lexicon has one (p. 16). -/
theorem pluralIndefinite_not_mem_structuralAlternatives :
    pluralIndefinite ∉ structuralAlternatives lexicon singularIndefinite := fun h ↦
  (by decide : ¬ ∀ s ∈ pluralIndefinite.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = .D))
    (phrase_preservation _ .D (forall_mem_substitutionSource.2 ⟨by decide, by decide⟩)
      (by decide) h)

-- p. 17: replacing the number head gives the plural alternative
theorem leafSubst_mem_structuralAlternatives {t : NumberHead → Tree Cat Morpheme}
    (ht : t .pl = (t .sg).leafSubst (.num .sg) (.num .pl) .Num) (hwf : (t .sg).IsWellFormed) :
    t .pl ∈ structuralAlternatives lexicon (t .sg) :=
  ht ▸ horn_alternatives_are_structural lexicon (t .sg) _ _ _
    (Finset.mem_image.2 ⟨.num .pl, Finset.mem_univ _, rfl⟩) hwf

-- (33): with a numeral the plural indefinite is an alternative, but it means the same
theorem numeralIndefinite_mem_structuralAlternatives :
    numeralIndefinite .pl ∈ structuralAlternatives lexicon (numeralIndefinite .sg) :=
  leafSubst_mem_structuralAlternatives (by decide) (by decide)

/-! ### Interpretation -/

section Interpretation

variable {α : Type} {B : Finset α} {n : NumberHead}

/-- The type of a set of individuals. -/
abbrev setTy : Ty Unit := .base () ⇒ .t

/-- The domains: the one base sort is the individuals, the sets of the atoms `α`. -/
abbrev Dom (α : Type) : Unit → Type := fun _ ↦ Finset α

/-- The interpreted morphemes by type. The noun is a set and the number heads and the numeral
are functions on sets; *sup* and the choice function are partial. The verb and the existential
are not interpreted. -/
inductive Item : Ty Unit → Type
  | boy : Item (.comp .M setTy)
  | num (n : NumberHead) : Item (.comp .M (setTy ⇒ setTy))
  | two : Item (.comp .M (setTy ⇒ setTy))
  | def_ : Item (.comp .M (setTy ⇒ .comp .M setTy))
  | plusDef : Item (.comp .M (setTy ⇒ .comp .M (.base ())))

/-- The item a leaf is, if it is interpreted. -/
def items : Morpheme ⊕ ℕ → List (Σ a, Item a)
  | .inl .boy => [⟨_, .boy⟩]
  | .inl (.num n) => [⟨_, .num n⟩]
  | .inl .two => [⟨_, .two⟩]
  | .inl .def_ => [⟨_, .def_⟩]
  | .inl .plusDef => [⟨_, .plusDef⟩]
  | _ => []

/-- The denotations of the morphemes over the boys `B`: *sup* is defined at a set that contains
its supremum, and the choice function +DEF at a set with one member. -/
noncomputable def Item.val (B : Finset α) : {a : Ty Unit} → Item a → a.Dom (Dom α)
  | _, .boy => .some (BaleKhanjian2014.boy B)
  | _, .num n => .some n.denote
  | _, .two => .some (numeral 2)
  | _, .def_ => .some fun X ↦ Part.restrict (sup X).Nonempty (.some (sup X)) fun _ ↦ trivial
  | _, .plusDef => .some fun X ↦ ↑(iota X)

/-- The meanings of a tree over the boys `B`: every constituent is a partial value, and a
function applies to its sister where both are defined. -/
noncomputable def meanings (B : Finset α) (t : Tree Cat Morpheme) :
    List (Σ a : Ty Unit, a.Dom (Dom α)) :=
  t.values (partialValued application) (D := Ty.Dom (Dom α)) inferInstance (Item.val B) items

/-- A partial value that is defined. -/
def IsDefined : (Σ a : Ty Unit, a.Dom (Dom α)) → Prop
  | ⟨.comp .M _, x⟩ => x.Dom
  | _ => False

/-- The presupposition of a tree: the sets of boys over which it has a defined value. -/
def defined (t : Tree Cat Morpheme) : Set (Finset α) :=
  {B | ∃ d ∈ meanings B t, IsDefined d}

/-- A total function applied to the partial value on its left. -/
abbrev back (a b : Ty Unit) : Mode (application (B := Unit)).Binary
    (.comp .M a) (.comp .M (a ⇒ b)) (.comp .M b) :=
  .ap (.basic .ba)

/-- A total function applied to the partial value on its right. -/
abbrev forth (a b : Ty Unit) : Mode (application (B := Unit)).Binary
    (.comp .M (a ⇒ b)) (.comp .M a) (.comp .M b) :=
  .ap (.basic .fa)

/-- A partial function applied to the partial value on its left. -/
abbrev backPartial (a b : Ty Unit) : Mode (application (B := Unit)).Binary
    (.comp .M a) (.comp .M (a ⇒ .comp .M b)) (.comp .M b) :=
  .join (.ap (.basic .ba))

theorem eval_back {a b : Ty Unit} (x : Part (a.Dom (Dom α)))
    (f : Part (a.Dom (Dom α) → b.Dom (Dom α))) :
    (back a b).eval (Dom α) x f = x.bind fun v ↦ f.map fun g ↦ g v := by
  rw [Mode.eval_ap_basic]; rfl

theorem eval_forth {a b : Ty Unit} (f : Part (a.Dom (Dom α) → b.Dom (Dom α)))
    (x : Part (a.Dom (Dom α))) :
    (forth a b).eval (Dom α) f x = f.bind fun g ↦ x.map fun v ↦ g v := by
  rw [Mode.eval_ap_basic]; rfl

theorem eval_backPartial {a b : Ty Unit} (x : Part (a.Dom (Dom α)))
    (f : Part (a.Dom (Dom α) → Part (b.Dom (Dom α)))) :
    (backPartial a b).eval (Dom α) x f = x.bind fun v ↦ f.bind fun g ↦ g v := by
  rw [Mode.eval_join_ap_basic]; rfl

/-- The value of the number phrase. -/
noncomputable def numPVal (B : Finset α) (n : NumberHead) : Part (Set (Finset α)) :=
  (back setTy setTy).eval (Dom α) (Item.val B .boy) (Item.val B (.num n))

/-- The value of NumP*. -/
noncomputable def numPStarVal (B : Finset α) (n : NumberHead) : Part (Set (Finset α)) :=
  (backPartial setTy setTy).eval (Dom α) (numPVal B n) (Item.val B .def_)

theorem numPVal_eq : numPVal B n = .some (n.denote (boy B)) := by
  simp [numPVal, eval_back, Item.val]

theorem numPStarVal_eq : numPStarVal B n =
    Part.restrict (sup (n.denote (boy B))).Nonempty (.some (sup (n.denote (boy B))))
      fun _ ↦ trivial := by
  simp [numPStarVal, numPVal_eq, eval_backPartial, Item.val]

theorem meanings_numP : meanings B (numP n) = [⟨.comp .M setTy, .some (n.denote (boy B))⟩] :=
  (show meanings B (numP n) = [⟨.comp .M setTy, numPVal B n⟩] from rfl).trans
    (by rw [numPVal_eq])

theorem meanings_numPStar : meanings B (numPStar n) = [⟨.comp .M setTy,
    Part.restrict (sup (n.denote (boy B))).Nonempty (.some (sup (n.denote (boy B))))
      fun _ ↦ trivial⟩] :=
  (show meanings B (numPStar n) = [⟨.comp .M setTy, numPStarVal B n⟩] from rfl).trans
    (by rw [numPStarVal_eq])

theorem meanings_definiteDP : meanings B (definiteDP n) = [⟨.comp .M (.base ()),
    (backPartial setTy (.base ())).eval (Dom α) (numPStarVal B n) (Item.val B .plusDef)⟩] :=
  rfl

theorem meanings_bareDP : meanings B (bareDP n) = [⟨.comp .M (.base ()),
    (backPartial setTy (.base ())).eval (Dom α) (numPVal B n) (Item.val B .plusDef)⟩] :=
  rfl

theorem meanings_numeralDP : meanings B (numeralDP n) = [⟨.comp .M (.base ()),
    (backPartial setTy (.base ())).eval (Dom α)
      ((forth setTy setTy).eval (Dom α) (Item.val B .two) (numPStarVal B n))
      (Item.val B .plusDef)⟩] :=
  rfl

theorem mem_defined_numPStar : B ∈ defined (numPStar n) ↔ (sup (n.denote (boy B))).Nonempty := by
  simp [defined, meanings_numPStar, IsDefined, Part.restrict]

-- p. 22: the singular NumP* presupposes a boy, the plural two
theorem defined_numPStar_sg : defined (α := α) (numPStar .sg) = {B | 1 ≤ B.card} :=
  Set.ext fun _ ↦ mem_defined_numPStar.trans (by rw [denote_sg_boy, nonempty_sup_card_le]; rfl)

theorem defined_numPStar_pl : defined (α := α) (numPStar .pl) = {B | 2 ≤ B.card} :=
  Set.ext fun _ ↦ mem_defined_numPStar.trans (by rw [denote_pl_boy, nonempty_sup_card_le]; rfl)

theorem defined_numPStar_pl_ssubset [Nonempty α] :
    defined (α := α) (numPStar .pl) ⊂ defined (numPStar .sg) := by
  rw [defined_numPStar_sg, defined_numPStar_pl]
  refine ⟨fun _ h ↦ (by omega : 1 ≤ 2).trans h, fun h ↦ ?_⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  have : 2 ≤ ({a} : Finset α).card := h (by simp)
  simp at this

-- the determiner adds no presupposition to NumP*
theorem defined_definiteDP : defined (α := α) (definiteDP n) = defined (numPStar n) := by
  ext B
  simp [defined, meanings_definiteDP, meanings_numPStar, numPStarVal_eq, eval_backPartial,
    IsDefined, Item.val, Part.restrict]

theorem defined_bareDP_sg : defined (α := α) (bareDP .sg) = {B | B.card = 1} := by
  ext B
  simp only [defined, Set.mem_ofPred_eq]
  simp [meanings_bareDP, numPVal_eq, eval_backPartial, IsDefined, Item.val, iota_isSome_iff,
    denote_sg_boy, Finset.card_eq_one]
  constructor
  · rintro ⟨x, ⟨hxB, hx⟩, huniq⟩
    have hB := huniq B ⟨subset_rfl, hx.mono hxB⟩
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, hB.trans
      (huniq {a} ⟨Finset.singleton_subset_iff.2 (hxB ha), Finset.singleton_nonempty a⟩).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨{a}, ⟨subset_rfl, Finset.singleton_nonempty a⟩, fun y ⟨hy, hy1⟩ ↦
      (Finset.subset_singleton_iff.1 hy).resolve_left hy1.ne_empty⟩

-- p. 22: either numeral definite presupposes exactly two boys
theorem defined_numeralDP : defined (α := α) (numeralDP n) = {B | B.card = 2} := by
  ext B
  have hsub {X : Set (Finset α)} : (numeral 2 (sup X)).Subsingleton :=
    sup_subsingleton.anti fun _ h ↦ h.1
  have hk : ∃ k ≤ 2, n.denote (boy B) = {x | x ⊆ B ∧ k ≤ x.card} := by
    cases n
    exacts [⟨1, by omega, denote_sg_boy⟩, ⟨2, le_rfl, denote_pl_boy⟩]
  obtain ⟨k, hk2, hden⟩ := hk
  simp [defined, meanings_numeralDP, numPStarVal_eq, eval_backPartial, eval_forth, IsDefined,
    Item.val, Part.restrict, hsub.iota_isSome_iff, hden, sup_card_le]
  exact ⟨fun ⟨_, _, ⟨rfl, _⟩, h⟩ ↦ h, fun h ↦ ⟨⟨B, rfl, by omega⟩, B, ⟨rfl, by omega⟩, h⟩⟩

/-! ### Symmetry

A permutation of the individuals carries each world to another of the same size, and the lexicon
over the one to the lexicon over the other, morpheme by morpheme, so every tree has the same
definedness in both (`Interpreter.effectGrammar.isLogicalRel`). -/

section Symmetry

variable (σ : Equiv.Perm α)

/-- `X'` is `X` carried along `σ`. -/
private def Transports (X X' : Set (Finset α)) : Prop :=
  ∀ x, x ∈ X ↔ x.map σ.toEmbedding ∈ X'

private theorem map_symm_map (x : Finset α) :
    (x.map σ.toEmbedding).map σ.symm.toEmbedding = x := by
  simp [Finset.map_map]

private theorem map_map_symm (x : Finset α) :
    (x.map σ.symm.toEmbedding).map σ.toEmbedding = x := by
  simp [Finset.map_map]

variable {σ} {X X' : Set (Finset α)}

private theorem Transports.mem_iff' (h : Transports σ X X') (y : Finset α) :
    y ∈ X' ↔ y.map σ.symm.toEmbedding ∈ X := by
  rw [h, map_map_symm]

private theorem transports_boy (B : Finset α) :
    Transports σ (boy B) (boy (B.map σ.toEmbedding)) := fun x ↦ by
  simp only [mem_boy, Finset.map_subset_map, Finset.card_map]

private theorem Transports.denote (h : Transports σ X X') (n : NumberHead) :
    Transports σ (n.denote X) (n.denote X') := fun x ↦ by
  cases n
  · exact h x
  · simp only [NumberHead.denote, Set.mem_ofPred_eq, nonAtomsOf, atom_finset_iff_card_eq_one,
      Finset.card_map]
    exact and_congr_left' (h x)

private theorem Transports.numeral (h : Transports σ X X') (k : ℕ) :
    Transports σ (numeral k X) (numeral k X') := fun x ↦ by
  simp only [BaleKhanjian2014.numeral, Set.mem_sep_iff, Finset.card_map]
  exact and_congr_left' (h x)

private theorem Transports.sup (h : Transports σ X X') : Transports σ (sup X) (sup X') := by
  intro x
  refine ⟨fun ⟨hx, hub⟩ ↦ ⟨(h x).1 hx, fun y hy ↦ ?_⟩, fun ⟨hx, hub⟩ ↦ ⟨(h x).2 hx, fun y hy ↦ ?_⟩⟩
  · rw [← map_map_symm σ y]
    exact Finset.map_subset_map.2 (hub ((h.mem_iff' y).1 hy))
  · exact Finset.map_subset_map.1 (hub ((h y).1 hy))

private theorem Transports.iota (h : Transports σ X X') :
    (_root_.iota X).map (·.map σ.toEmbedding) = _root_.iota X' := by
  rcases hX : _root_.iota X with _ | x
  · refine (iota_eq_none_iff.2 fun ⟨y, hy, huniq⟩ ↦ iota_eq_none_iff.1 hX ⟨_, (h.mem_iff' y).1 hy,
      fun z hz ↦ ?_⟩).symm
    rw [← map_symm_map σ z, huniq _ ((h z).1 hz)]
  · obtain ⟨hx, huniq⟩ := iota_eq_some_iff.1 hX
    refine (iota_eq_some_iff.2 ⟨(h x).1 hx, fun y hy ↦ ?_⟩).symm
    rw [← map_map_symm σ y, huniq _ ((h.mem_iff' y).1 hy)]

/-- Individuals related along `σ`. -/
private def rel (σ : Equiv.Perm α) : ∀ _ : Unit, Finset α → Finset α → Prop :=
  fun _ x y ↦ y = x.map σ.toEmbedding

private theorem liftRel_set (h : Transports σ X X') : Ty.LiftRel (rel σ) setTy X X' := by
  rintro x _ rfl
  exact h x

private theorem transports_of_liftRel (h : Ty.LiftRel (rel σ) setTy X X') : Transports σ X X' :=
  fun _ ↦ h rfl

-- The lexicon over the boys and the lexicon over the boys carried along `σ` are related,
-- morpheme by morpheme.
private theorem liftRel_val (B : Finset α) : ∀ {a : Ty Unit} (i : Item a),
    Ty.LiftRel (rel σ) a (Item.val B i) (Item.val (B.map σ.toEmbedding) i)
  | _, .boy => ⟨Iff.rfl, fun _ _ ↦ liftRel_set (transports_boy B)⟩
  | _, .num n => ⟨Iff.rfl, fun _ _ _ _ hX ↦ liftRel_set ((transports_of_liftRel hX).denote n)⟩
  | _, .two => ⟨Iff.rfl, fun _ _ _ _ hX ↦ liftRel_set ((transports_of_liftRel hX).numeral 2)⟩
  | _, .def_ => ⟨Iff.rfl, fun _ _ X X' hX ↦
      have hsup := (transports_of_liftRel hX).sup
      ⟨⟨fun ⟨x, hx⟩ ↦ ⟨_, (hsup x).1 hx⟩, fun ⟨y, hy⟩ ↦ ⟨_, (hsup.mem_iff' y).1 hy⟩⟩,
        fun _ _ ↦ liftRel_set hsup⟩⟩
  | _, .plusDef => ⟨Iff.rfl, fun _ _ X X' hX ↦ by
      have hi := (transports_of_liftRel hX).iota
      show Eff.RelWith .M _ (rel σ ()) (↑(iota X) : Part (Finset α)) ↑(iota X')
      rw [← hi]
      cases iota X
      · exact ⟨Iff.rfl, fun h ↦ absurd h Part.not_none_dom⟩
      · exact ⟨Iff.rfl, fun _ _ ↦ rfl⟩⟩

private theorem mem_defined_of_map {B : Finset α} {t : Tree Cat Morpheme}
    (h : B.map σ.toEmbedding ∈ defined t) : B ∈ defined t := by
  simp only [defined, meanings, Tree.values, Set.mem_ofPred_eq, List.mem_map] at h ⊢
  obtain ⟨_, ⟨⟨a, d⟩, hd, rfl⟩, hdef⟩ := h
  refine ⟨_, ⟨⟨a, d⟩, hd, rfl⟩, ?_⟩
  have hrel : Ty.LiftRel (rel σ) a _ _ :=
    (effectGrammar.isLogicalRel (r := rel σ) (G := application)
      application.isLogicalRel).realize (fun i ↦ liftRel_val (σ := σ) B i) d
  match a, d, hrel, hdef with
  | .comp .M _, _, hrel, hdef => exact hrel.1.2 hdef

end Symmetry

-- a tree's presupposition depends on the boys only through their number
theorem mem_defined_iff_of_card_eq {B' : Finset α} (h : B.card = B'.card)
    (t : Tree Cat Morpheme) : B ∈ defined t ↔ B' ∈ defined t := by
  obtain ⟨σ, rfl⟩ := Equiv.Perm.exists_map_finset_eq B B' h
  refine ⟨fun hB ↦ mem_defined_of_map (σ := σ.symm) ?_, mem_defined_of_map (σ := σ)⟩
  rwa [map_symm_map]

end Interpretation

/-! ### The alternatives of NumP* -/

section Alternatives

variable {α : Type} {B : Finset α} {n : NumberHead}

/-- The labels of the number phrase: phrases of the noun, the number head and the definite marker,
and *dəgha*, the number heads and the definite marker under their categories. -/
def IsNominalLabel : Label Cat Morpheme → Prop
  | .terminal .N .boy | .terminal .Num (.num _) | .terminal .Def .def_ => True
  | .phrase c _ => c = .N ∨ c = .Num ∨ c = .Def
  | _ => False

instance : DecidablePred IsNominalLabel := fun l ↦ by
  unfold IsNominalLabel; split <;> infer_instance

theorem IsNominalLabel.cat {l : Label Cat Morpheme} (h : IsNominalLabel l) :
    l.cat = .N ∨ l.cat = .Num ∨ l.cat = .Def := by
  unfold IsNominalLabel at h; split at h <;> simp_all [Label.cat]

-- no operation brings a determiner, a numeral or a verb into NumP*
theorem licensed_of_mem_structuralAlternatives {ψ : Tree Cat Morpheme}
    (h : ψ ∈ structuralAlternatives lexicon (numPStar n)) : ψ.Licensed fun l _ ↦ IsNominalLabel l :=
  licensed_of_atMostAsComplex_of_cat (K := fun c ↦ c = .N ∨ c = .Num ∨ c = .Def)
    (fun _ _ h ↦ h.cat) (forall_mem_substitutionSource.2 ⟨by decide, by cases n <;> decide⟩)
    (fun _ _ _ _ h ↦ h) (fun _ _ _ _ _ _ _ h ↦ h) (fun _ _ _ _ _ h ↦ h) (by cases n <;> decide) h

/-- A set is good over the boys `B` when it contains `B` and only parts of `B`. -/
structure GoodPred (B : Finset α) (X : Set (Finset α)) : Prop where
  self : B ∈ X
  le : ∀ x ∈ X, x ⊆ B

/-- A value is good over the boys `B` when it is a good set, or a function on sets, total or
partial, that takes good sets to good sets. -/
inductive Good (B : Finset α) : (Σ a : Ty Unit, a.Dom (Dom α)) → Prop
  | pred {X : Set (Finset α)} : GoodPred B X → Good B ⟨.comp .M setTy, .some X⟩
  | modifier {F : Set (Finset α) → Set (Finset α)} :
      (∀ X, GoodPred B X → GoodPred B (F X)) → Good B ⟨.comp .M (setTy ⇒ setTy), .some F⟩
  | partialModifier {F : Set (Finset α) → Part (Set (Finset α))} :
      (∀ X, GoodPred B X → ∃ Y, F X = .some Y ∧ GoodPred B Y) →
        Good B ⟨.comp .M (setTy ⇒ .comp .M setTy), .some F⟩

theorem Good.isDefined {d : Σ a : Ty Unit, a.Dom (Dom α)} (h : Good B d) : IsDefined d := by
  cases h <;> trivial

/-- A partial function applied to the partial value on its right. -/
abbrev forthPartial (a b : Ty Unit) : Mode (application (B := Unit)).Binary
    (.comp .M (a ⇒ .comp .M b)) (.comp .M a) (.comp .M b) :=
  .join (.ap (.basic .fa))

theorem eval_forthPartial {a b : Ty Unit} (f : Part (a.Dom (Dom α) → Part (b.Dom (Dom α))))
    (x : Part (a.Dom (Dom α))) :
    (forthPartial a b).eval (Dom α) f x = f.bind fun g ↦ x.bind fun v ↦ g v := by
  rw [Mode.eval_join_ap_basic]; rfl

/-- The rules of the partial-valued interpreter. -/
abbrev rules : Interpreter (effectGrammar (application (B := Unit))) ℕ :=
  partialValued application

theorem Good.combine {d₁ d₂ : Σ a : Ty Unit, a.Dom (Dom α)} (h₁ : Good B d₁) (h₂ : Good B d₂)
    {m : Σ u, Mode (application (B := Unit)).Binary d₁.1 d₂.1 u}
    (hm : m ∈ rules.binary d₁.1 d₂.1) :
    Good B ⟨m.1, m.2.eval (Dom α) d₁.2 d₂.2⟩ := by
  rcases h₁ with @⟨X, hX⟩ | @⟨F, hF⟩ | @⟨F, hF⟩ <;>
    rcases h₂ with @⟨Y, hY⟩ | @⟨G, hG⟩ | @⟨G, hG⟩
  · exact absurd hm List.not_mem_nil
  · obtain rfl : m = ⟨_, back setTy setTy⟩ := List.mem_singleton.1 hm
    rw [eval_back, Part.bind_some, Part.map_some]
    exact .pred (hG X hX)
  · obtain rfl : m = ⟨_, backPartial setTy setTy⟩ := List.mem_singleton.1 hm
    obtain ⟨Z, hZ, hgood⟩ := hG X hX
    rw [eval_backPartial, Part.bind_some, Part.bind_some, hZ]
    exact .pred hgood
  · obtain rfl : m = ⟨_, forth setTy setTy⟩ := List.mem_singleton.1 hm
    rw [eval_forth, Part.bind_some, Part.map_some]
    exact .pred (hF Y hY)
  · exact absurd hm List.not_mem_nil
  · exact absurd hm List.not_mem_nil
  · obtain rfl : m = ⟨_, forthPartial setTy setTy⟩ := List.mem_singleton.1 hm
    obtain ⟨Z, hZ, hgood⟩ := hF Y hY
    rw [eval_forthPartial, Part.bind_some, Part.bind_some, hZ]
    exact .pred hgood
  · exact absurd hm List.not_mem_nil
  · exact absurd hm List.not_mem_nil

theorem good_val (hB : 2 ≤ B.card) {c : Cat} {w : Morpheme}
    (hw : IsNominalLabel (.terminal c w)) {i : Σ a, Item a} (hi : i ∈ items (.inl w)) :
    Good B ⟨i.1, Item.val B i.2⟩ := by
  have hB' : B ∈ boy B := mem_boy.2 ⟨subset_rfl, by omega⟩
  cases w with
  | boy =>
    obtain rfl := List.mem_singleton.1 hi
    exact .pred ⟨hB', fun x hx ↦ (mem_boy.1 hx).1⟩
  | num m =>
    obtain rfl := List.mem_singleton.1 hi
    refine .modifier fun X hX ↦ ⟨?_, fun x hx ↦ ?_⟩
    · cases m
      · exact hX.self
      · simpa [NumberHead.denote, nonAtomsOf, atom_finset_iff_card_eq_one, hX.self] using
          (by omega : B.card ≠ 1)
    · cases m <;> simp [NumberHead.denote, nonAtomsOf] at hx
      · exact hX.le x hx
      · exact hX.le x hx.1
  | def_ =>
    obtain rfl := List.mem_singleton.1 hi
    refine .partialModifier fun X hX ↦ ?_
    have hsup : B ∈ sup X := ⟨hX.self, fun x hx ↦ hX.le x hx⟩
    exact ⟨sup X, Part.eq_some_iff.2 ⟨⟨B, hsup⟩, rfl⟩, hsup, fun x hx ↦ hX.le x hx.1⟩
  | plusDef | exists_ | two | run => cases c <;> simp [IsNominalLabel] at hw

theorem good_of_licensed (hB : 2 ≤ B.card) {t : Tree Cat Morpheme}
    (ht : t.Licensed fun l _ ↦ IsNominalLabel l) :
    ∀ d ∈ meanings B t, Good B d := by
  induction t using Tree.rec' with
  | terminal c w =>
    intro d hd
    obtain ⟨⟨a, e⟩, he, rfl⟩ := List.mem_map.1 hd
    rw [Tree.derivs_terminal] at he
    obtain ⟨⟨b, i⟩, hi, heq⟩ := List.mem_map.1 he
    cases heq
    exact good_val hB ht.rel_root hi
  | phrase c k cs ih =>
    match cs, ih, ht with
    | [t], ih, ht => exact ih t (by simp) (ht.of_mem (by simp))
    | [t₁, t₂], ih, ht =>
      intro d hd
      have ih₁ := ih t₁ (by simp) (ht.of_mem (by simp))
      have ih₂ := ih t₂ (by simp) (ht.of_mem (by simp))
      simp only [meanings, Tree.values_eq_fold, RoseTree.fold_node, List.map_cons, List.map_nil,
        Tree.nodeValues] at hd ih₁ ih₂
      obtain ⟨d₁, hd₁, d₂, hd₂, m, hm, rfl⟩ := Interpreter.mem_binaryValues.1 hd
      exact (ih₁ d₁ hd₁).combine (ih₂ d₂ hd₂) hm
    | [], _, _ =>
      exact fun _ hd ↦ by simp [meanings, Tree.values_eq_fold, Tree.nodeValues] at hd
    | _ :: _ :: _ :: _, _, _ =>
      exact fun _ hd ↦ by simp [meanings, Tree.values_eq_fold, Tree.nodeValues] at hd
  | trace n c => exact absurd ht.rel_root id
  | bind n c t _ => exact absurd ht.rel_root id
  | junk l cs hl _ =>
    intro d hd
    cases l with
    | terminal c w =>
      cases cs with
      | nil => simp [Label.Licenses] at hl
      | cons => simp [meanings, Tree.values_eq_fold, Tree.nodeValues] at hd
    | phrase c k => simp [Label.Licenses] at hl
    | trace n c => exact absurd ht.rel_root id
    | bind n c => exact absurd ht.rel_root id

-- every alternative of NumP* is uninterpretable, or defined wherever there are two boys
theorem defined_eq_empty_or_subset {ψ : Tree Cat Morpheme}
    (h : ψ ∈ structuralAlternatives lexicon (numPStar n)) :
    defined (α := α) ψ = ∅ ∨ {B : Finset α | 2 ≤ B.card} ⊆ defined ψ := by
  have hlen (B B' : Finset α) : (meanings B ψ).length = (meanings B' ψ).length := by
    simp [meanings, Tree.values]
  by_cases hu : meanings (∅ : Finset α) ψ = []
  · refine .inl (Set.eq_empty_of_forall_notMem fun B ⟨d, hd, _⟩ ↦ ?_)
    have := hlen B ∅
    rw [hu, List.length_nil] at this
    exact List.ne_nil_of_mem hd (List.length_eq_zero_iff.1 this)
  · refine .inr fun B hB ↦ ?_
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil (meanings B ψ) fun h0 ↦
      hu ((List.length_eq_zero_iff (l := meanings (∅ : Finset α) ψ)).1
        (by rw [hlen ∅ B, h0, List.length_nil]))
    exact ⟨d, hd, (good_of_licensed hB (licensed_of_mem_structuralAlternatives h) d hd).isDefined⟩

end Alternatives

/-! ### Maximize Presupposition -/

section Competition

variable {α : Type}

/-- At NumP*, strengthened against its alternatives, the singular definite *dəgha-n* presupposes a
single boy (11b). -/
theorem strengthen_numPStar_sg [Nonempty α] :
    strengthen (structuralAlternatives lexicon) defined (numPStar .sg) =
      {B : Finset α | B.card = 1} := by
  have hpl : numPStar .pl ∈ structuralAlternatives lexicon (numPStar .sg) :=
    leafSubst_mem_structuralAlternatives (by decide) (by decide)
  ext B
  rw [mem_strengthen_iff, defined_numPStar_sg]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h⟩
    have h2 : ¬ 2 ≤ B.card := fun h2 ↦ h _ hpl (by rw [defined_numPStar_pl]; exact h2)
      (by rw [← defined_numPStar_sg]; exact defined_numPStar_pl_ssubset)
    omega
  · intro h1
    refine ⟨h1.ge, fun ψ hψ hB hss ↦ ?_⟩
    rcases defined_eq_empty_or_subset hψ with h0 | h2
    · rw [h0] at hB; exact hB
    · refine hss.not_subset fun B' (hB' : 1 ≤ B'.card) ↦ ?_
      rcases hB'.eq_or_lt with h' | h'
      · exact (mem_defined_iff_of_card_eq (h1.trans h') ψ).1 hB
      · exact h2 (show 2 ≤ B'.card from h')

/-- Maximize Presupposition at NumP* rules out the singular under a numeral on a definite (14a)
and keeps the plural (14b): wherever the definite numeral phrase is defined, so is the plural's
stronger local presupposition (p. 23). -/
theorem minimalFor_defined_numPStar_iff [Nonempty α] {c : Set (Finset α)} {n : NumberHead}
    (hc : c ⊆ defined (numeralDP n)) (hne : c.Nonempty) :
    MinimalFor (· ∈ insert (numPStar n) (structuralAlternatives lexicon (numPStar n)) ∩
      defined (α := α) ⁻¹' Set.Ici c) (defined (α := α)) (numPStar n) ↔ n = .pl := by
  rw [defined_numeralDP] at hc
  have hpl : c ⊆ defined (numPStar .pl) := hc.trans fun B h ↦ by
    rw [defined_numPStar_pl]; exact h.ge
  rw [minimalFor_preimage_Ici_iff]
  cases n
  · simp only [reduceCtorEq, iff_false, not_and, not_forall]
    exact fun _ ↦ ⟨numPStar .pl, leafSubst_mem_structuralAlternatives (by decide) (by decide),
      defined_numPStar_pl_ssubset, fun h ↦ h hpl⟩
  · refine iff_of_true ⟨hpl, fun ψ hψ hss hcψ ↦ ?_⟩ rfl
    rcases defined_eq_empty_or_subset hψ with h0 | h2
    · obtain ⟨B, hB⟩ := hne
      rw [h0] at hcψ; exact hcψ hB
    · exact hss.not_subset (by rw [defined_numPStar_pl]; exact h2)

/-- At the determiner phrase, Maximize Presupposition over the structures of the final analysis
would leave the singular definite no context: its alternatives include the plural, presupposing
two boys, and +DEF over the bare number phrase, presupposing exactly one. -/
theorem strengthen_definiteDP_sg_eq_empty [Nontrivial α] :
    strengthen (structuralAlternatives lexicon) defined (definiteDP .sg) =
      (∅ : Set (Finset α)) := by
  classical
  have hpl : definiteDP .pl ∈ structuralAlternatives lexicon (definiteDP .sg) :=
    leafSubst_mem_structuralAlternatives (by decide) (by decide)
  have hbare : bareDP .sg ∈ structuralAlternatives lexicon (definiteDP .sg) :=
    .single (StructuralOp.inChild ⟨0, by simp⟩
      (StructuralOp.contract (child := numP .sg) (by simp) rfl))
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hpair : ({a, b} : Finset α).card = 2 := Finset.card_pair hab
  refine Set.eq_empty_of_forall_notMem fun B hB ↦ ?_
  rw [mem_strengthen_iff, defined_definiteDP, defined_numPStar_sg] at hB
  obtain ⟨h1 : 1 ≤ B.card, h⟩ := hB
  rcases h1.eq_or_lt with h' | h'
  · refine h _ hbare (by rw [defined_bareDP_sg]; exact h'.symm)
      ⟨fun B' hB' ↦ ?_, fun hss ↦ ?_⟩
    · rw [defined_bareDP_sg] at hB'
      exact (show B'.card = 1 from hB').ge
    · have := hss (show 1 ≤ ({a, b} : Finset α).card by omega)
      rw [defined_bareDP_sg] at this
      exact absurd (show ({a, b} : Finset α).card = 1 from this) (by omega)
  · refine h _ hpl (by rw [defined_definiteDP, defined_numPStar_pl]; exact h') ?_
    rw [defined_definiteDP, ← defined_numPStar_sg]
    exact defined_numPStar_pl_ssubset

end Competition

/-! ### The rows -/

/-- The boys of the predicative sentences (4)–(6). -/
inductive Boy
  | john
  | brad
  deriving DecidableEq, Fintype, Inhabited, Repr

instance (n : NumberHead) (B : Finset Boy) : DecidablePred (· ∈ n.denote (boy B)) := fun x ↦
  match n with
  | .sg => decidable_of_iff _ (Set.ext_iff.1 denote_sg_boy x).symm
  | .pl => decidable_of_iff _ (Set.ext_iff.1 denote_pl_boy x).symm

instance {k : ℕ} {X : Set (Finset Boy)} [DecidablePred (· ∈ X)] :
    DecidablePred (· ∈ numeral k X) := fun x ↦ inferInstanceAs (Decidable (x ∈ X ∧ x.card = k))

/-- A predicative sentence of (4)–(6): its subject, John or John and Brad, the number head of the
predicate noun, and its numeral. -/
def predicative? (r : Datum) : Option (Finset Boy × NumberHead × Option ℕ) :=
  if r.feature? "construction" = some "predicative" then
    (r.parse? "subject" [("atom", {.john}), ("group", {.john, .brad})]).bind fun s ↦
      (r.parse? "number" [("SG", .sg), ("PL", .pl)]).map fun n ↦
        (s, n, r.parse? "numeral" [("one", 1), ("two", 2)])
  else none

/-- The predicate a number head and numeral make of *dəgha* over the two boys. -/
def predicate : NumberHead × Option ℕ → Finset Boy → Judgment.Band
  | (n, none), s => .ofProp (s ∈ n.denote (boy .univ))
  | (n, some k), s => .ofProp (s ∈ numeral k (n.denote (boy .univ)))

-- (4)–(6): a predicative sentence is acceptable when its subject is in its predicate
theorem rows_predicative :
    Datum.Checks predicative? (fun (s, nk) ↦ predicate nk s) Examples.all 6 := by
  decide +kernel

/-- The definite numeral phrases of (14). -/
def numeralDefinite? (r : Datum) : Option NumberHead :=
  if r.feature? "construction" = some "definite" ∧ r.feature? "numeral" = some "two" then
    r.parse? "number" [("SG", .sg), ("PL", .pl)]
  else none

-- (14): with John and Brad the boys, the rows fit Maximize Presupposition at NumP*
theorem rows_numeralDefinite :
    (∀ r ∈ Examples.all, ∀ n ∈ numeralDefinite? r,
      (MinimalFor (· ∈ insert (numPStar n) (structuralAlternatives lexicon (numPStar n)) ∩
        defined (α := Boy) ⁻¹' Set.Ici {.univ}) (defined (α := Boy)) (numPStar n) ↔
          r.judgment = .acceptable)) ∧
    Datum.ReadCount numeralDefinite? Examples.all 2 := by
  refine ⟨fun r hr n hn ↦ ?_, by decide +kernel⟩
  rw [minimalFor_defined_numPStar_iff (by rw [defined_numeralDP]; rintro _ rfl; decide)
    (Set.singleton_nonempty _)]
  revert n
  revert r
  decide +kernel

end BaleKhanjian2014
