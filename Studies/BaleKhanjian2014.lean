module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Composition.Partial
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

Trees are interpreted by the partial engine of `Linglib/Semantics/Composition/Partial.lean`, over
worlds that are sets of boys, and a tree's presupposition is the set of worlds where it is defined.
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

open Mereology Number Presupposition PhraseStructure Tree Montague

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

/-- The partial denotations of the morphemes over the boys `B`. The number heads, *sup* and the
numeral modify a predicate through its extension; *sup* is defined where the extension contains its
supremum, and +DEF where it has one member. The verb and the existential are not interpreted. -/
noncomputable def lex (B : Finset α) : Morpheme → Option (PDenotation (Finset α) Unit) :=
  open scoped Classical in fun
  | .boy => some ⟨.e ⇒ .t, .some (PFun.lift (· ∈ boy B))⟩
  | .num n => some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
      .some fun P ↦ .some (PFun.lift (· ∈ n.denote {x | True ∈ P x}))⟩
  | .def_ => some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, .some fun P ↦
      if (sup {x | True ∈ P x}).Nonempty then .some (PFun.lift (· ∈ sup {x | True ∈ P x}))
      else .none⟩
  | .plusDef => some ⟨(.e ⇒ .t) ⇒ .e, .some fun P ↦ ↑(iota {x | True ∈ P x})⟩
  | .two => some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
      .some fun P ↦ .some (PFun.lift (· ∈ numeral 2 {x | True ∈ P x}))⟩
  | .exists_ | .run => none

/-- The presupposition of a tree: the sets of boys over which it has a defined value. -/
def defined (t : Tree Cat Morpheme) : Set (Finset α) :=
  {B | ∃ d, interpPartial (lex B) (fun _ ↦ ∅) t = some d ∧ d.2.Dom}

theorem mem_defined_of_eq {t : Tree Cat Morpheme} {d : PDenotation (Finset α) Unit}
    (h : interpPartial (lex B) (fun _ ↦ ∅) t = some d) : B ∈ defined t ↔ d.2.Dom :=
  ⟨fun ⟨_, h', hd⟩ ↦ (Option.some.inj (h.symm.trans h')) ▸ hd, fun hd ↦ ⟨d, h, hd⟩⟩

theorem interpPartial_numP :
    interpPartial (lex B) (fun _ ↦ ∅) (numP n) =
      some ⟨.e ⇒ .t, .some (PFun.lift (· ∈ n.denote (boy B)))⟩ := by
  simp [numP, lex, Mode.evalKleisli, Part.bind_eq_bind]

open scoped Classical in
theorem interpPartial_numPStar :
    interpPartial (lex B) (fun _ ↦ ∅) (numPStar n) = some ⟨.e ⇒ .t,
      if (sup (n.denote (boy B))).Nonempty then .some (PFun.lift (· ∈ sup (n.denote (boy B))))
      else .none⟩ := by
  simp [numPStar, interpPartial_numP, lex, Mode.evalKleisli, Part.bind_eq_bind]

theorem interpPartial_numPStar_of_nonempty (h : (sup (n.denote (boy B))).Nonempty) :
    interpPartial (lex B) (fun _ ↦ ∅) (numPStar n) =
      some ⟨.e ⇒ .t, .some (PFun.lift (· ∈ sup (n.denote (boy B))))⟩ := by
  rw [interpPartial_numPStar, ite_eq_left h]

theorem interpPartial_numPStar_of_not (h : ¬ (sup (n.denote (boy B))).Nonempty) :
    interpPartial (lex B) (fun _ ↦ ∅) (numPStar n) = some ⟨.e ⇒ .t, .none⟩ := by
  rw [interpPartial_numPStar, ite_eq_right h]

theorem mem_defined_numPStar : B ∈ defined (numPStar n) ↔ (sup (n.denote (boy B))).Nonempty := by
  rw [mem_defined_of_eq interpPartial_numPStar]
  split_ifs with h <;> simp [h]

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
  rw [mem_defined_numPStar]
  by_cases h : (sup (n.denote (boy B))).Nonempty
  · rw [mem_defined_of_eq (d := ⟨.e, ↑(iota (sup (n.denote (boy B))))⟩) (by
      simp [definiteDP, interpPartial_numPStar_of_nonempty h, lex, Mode.evalKleisli,
        Part.bind_eq_bind])]
    exact (Part.ofOption_dom _).trans sup_subsingleton.iota_isSome_iff
  · rw [mem_defined_of_eq (d := ⟨.e, .none⟩) (by
      simp [definiteDP, interpPartial_numPStar_of_not h, lex, Mode.evalKleisli,
        Part.bind_eq_bind])]
    exact iff_of_false Part.not_none_dom h

theorem defined_bareDP_sg : defined (α := α) (bareDP .sg) = {B | B.card = 1} := by
  ext B
  rw [mem_defined_of_eq (d := ⟨.e, ↑(iota (NumberHead.sg.denote (boy B)))⟩) (by
    simp [bareDP, interpPartial_numP, lex, Mode.evalKleisli, Part.bind_eq_bind])]
  refine (Part.ofOption_dom _).trans (iota_isSome_iff.trans ?_)
  rw [denote_sg_boy, Set.mem_ofPred_eq, Finset.card_eq_one]
  constructor
  · rintro ⟨x, ⟨hxB, hx⟩, huniq⟩
    have hB := huniq B ⟨subset_rfl, hx.trans (Finset.card_le_card hxB)⟩
    obtain ⟨a, ha⟩ := Finset.one_le_card.1 hx
    exact ⟨a, ((huniq {a} ⟨Finset.singleton_subset_iff.2 (hxB ha), by simp⟩).trans hB.symm).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨{a}, ⟨subset_rfl, by simp⟩, fun y ⟨hy, hy1⟩ ↦
      (Finset.subset_singleton_iff.1 hy).resolve_left (Finset.one_le_card.1 hy1).ne_empty⟩

-- p. 22: either numeral definite presupposes exactly two boys
theorem defined_numeralDP : defined (α := α) (numeralDP n) = {B | B.card = 2} := by
  ext B
  have hsub {X : Set (Finset α)} : (numeral 2 (sup X)).Subsingleton :=
    sup_subsingleton.anti fun _ h ↦ h.1
  have hk : ∃ k ≤ 2, n.denote (boy B) = {x | x ⊆ B ∧ k ≤ x.card} := by
    cases n
    exacts [⟨1, by omega, denote_sg_boy⟩, ⟨2, le_rfl, denote_pl_boy⟩]
  obtain ⟨k, hk2, hden⟩ := hk
  by_cases h : (sup (n.denote (boy B))).Nonempty
  · rw [mem_defined_of_eq (d := ⟨.e, ↑(iota (numeral 2 (sup (n.denote (boy B)))))⟩) (by
      simp [numeralDP, interpPartial_numPStar_of_nonempty h, lex, Mode.evalKleisli,
        Part.bind_eq_bind])]
    refine (Part.ofOption_dom _).trans (hsub.iota_isSome_iff.trans ?_)
    rw [hden, sup_card_le]
    exact ⟨fun ⟨_, ⟨rfl, _⟩, h⟩ ↦ h, fun (h : B.card = 2) ↦ ⟨B, ⟨rfl, by omega⟩, h⟩⟩
  · rw [mem_defined_of_eq (d := ⟨.e, .none⟩) (by
      simp [numeralDP, interpPartial_numPStar_of_not h, lex, Mode.evalKleisli,
        Part.bind_eq_bind])]
    rw [hden, nonempty_sup_card_le] at h
    exact iff_of_false Part.not_none_dom fun (h2 : B.card = 2) ↦ h (by omega)

/-! ### Symmetry

A permutation of the individuals carries each world to another of the same size, and the lexicon
over the one to the lexicon over the other, morpheme by morpheme, so the engine gives every tree
the same definedness in both (`PhraseStructure.Tree.interpPartial_rel`). -/

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
private def rel (σ : Equiv.Perm α) : Ty.BaseRel (Finset α) (Finset α) Unit Unit {} {} :=
  ⟨fun x y ↦ y = x.map σ.toEmbedding, Eq, Eq, Eq⟩

private theorem transports_of_liftRel {P P' : Finset α →. Prop}
    (h : Ty.LiftRel PartRel (rel σ) (.e ⇒ .t) P P') :
    Transports σ {x | True ∈ P x} {x | True ∈ P' x} := fun _ ↦
  (h rfl).true_mem_iff

private theorem liftRel_lift (h : Transports σ X X') :
    Ty.LiftRel PartRel (rel σ) (.e ⇒ .t) (PFun.lift (· ∈ X)) (PFun.lift (· ∈ X')) := by
  rintro x _ rfl
  exact ⟨Iff.rfl, fun _ _ ↦ h x⟩

private theorem partRel_some {ty : Ty} {a a' : Ty.PDomain (Finset α) Unit ty}
    (h : Ty.LiftRel PartRel (rel σ) ty a a') : PartRel (Ty.LiftRel PartRel (rel σ) ty) (.some a)
      (.some a') :=
  ⟨Iff.rfl, fun _ _ ↦ h⟩

private theorem partRel_none {ty : Ty} :
    PartRel (Ty.LiftRel PartRel (rel σ) ty) (Part.none : Part (Ty.PDomain (Finset α) Unit ty))
      Part.none :=
  ⟨Iff.rfl, fun h ↦ absurd h Part.not_none_dom⟩

private theorem lex_rel (B : Finset α) (w : Morpheme) (d' : PDenotation (Finset α) Unit)
    (h : lex (B.map σ.toEmbedding) w = some d') :
    ∃ c, lex B w = some ⟨d'.1, c⟩ ∧ PartRel (Ty.LiftRel PartRel (rel σ) d'.1) c d'.2 := by
  cases w <;> cases h
  · exact ⟨_, rfl, partRel_some (liftRel_lift (transports_boy B))⟩
  · exact ⟨_, rfl, partRel_some fun _ _ hP ↦
      partRel_some (liftRel_lift ((transports_of_liftRel hP).denote _))⟩
  · refine ⟨_, rfl, partRel_some fun P P' hP ↦ ?_⟩
    have hsup := (transports_of_liftRel hP).sup
    have hne : (sup {x | True ∈ P x}).Nonempty ↔ (sup {x | True ∈ P' x}).Nonempty :=
      ⟨fun ⟨x, hx⟩ ↦ ⟨_, (hsup x).1 hx⟩, fun ⟨y, hy⟩ ↦ ⟨_, (hsup.mem_iff' y).1 hy⟩⟩
    dsimp only
    split_ifs with h₁ h₂ h₂
    · exact partRel_some (liftRel_lift hsup)
    · exact absurd (hne.1 h₁) h₂
    · exact absurd (hne.2 h₂) h₁
    · exact partRel_none
  · refine ⟨_, rfl, partRel_some fun P P' hP ↦ ?_⟩
    have hi := (transports_of_liftRel hP).iota
    dsimp only
    rcases hX : iota {x | True ∈ P x} with _ | _
    · rw [← hi, hX]; exact partRel_none
    · rw [← hi, hX]; exact partRel_some rfl
  · exact ⟨_, rfl, partRel_some fun _ _ hP ↦
      partRel_some (liftRel_lift ((transports_of_liftRel hP).numeral 2))⟩

private theorem mem_defined_of_map {B : Finset α} {t : Tree Cat Morpheme}
    (h : B.map σ.toEmbedding ∈ defined t) : B ∈ defined t := by
  obtain ⟨d', hd', hdom⟩ := h
  obtain ⟨c, hc, hrel⟩ := interpPartial_rel (r := rel σ) (lex_rel (σ := σ) B) (g := fun _ ↦ ∅)
    (g' := fun _ ↦ ∅) (fun _ ↦ (Finset.map_empty _).symm) t hd'
  exact ⟨_, hc, hrel.1.2 hdom⟩

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

/-- A predicate is good over the boys `B` when it is total, true of `B`, and true only of parts of
`B`. -/
structure GoodPred (B : Finset α) (P : Finset α →. Prop) : Prop where
  dom : ∀ x, (P x).Dom
  self : True ∈ P B
  le : ∀ x, True ∈ P x → x ⊆ B

/-- A value is good over the boys `B` when it is a good predicate, or a modifier taking good
predicates to good predicates. -/
inductive Good (B : Finset α) : PDenotation (Finset α) Unit → Prop
  | pred {P : Finset α →. Prop} : GoodPred B P → Good B ⟨.e ⇒ .t, .some P⟩
  | modifier {F : (Finset α →. Prop) → Part (Finset α →. Prop)} :
      (∀ P, GoodPred B P → ∃ Q, F P = .some Q ∧ GoodPred B Q) →
        Good B ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, .some F⟩

theorem Good.dom {d : PDenotation (Finset α) Unit} (h : Good B d) : d.2.Dom := by
  cases h <;> trivial

theorem Good.combine? {d₁ d₂ d : PDenotation (Finset α) Unit} (h₁ : Good B d₁) (h₂ : Good B d₂)
    (h : Mode.combine? Mode.evalPartial d₁ d₂ = some d) : Good B d := by
  rcases h₁ with @⟨P, hP⟩ | @⟨F, hF⟩ <;> rcases h₂ with @⟨Q, hQ⟩ | @⟨G, hG⟩
  · rw [Mode.combine?_evalPartial_predicateModification] at h
    cases h
    refine .pred ⟨fun x ↦ ⟨hP.dom x, hQ.dom x⟩, ?_, fun x hx ↦ ?_⟩
    · exact Part.mem_bind_iff.2 ⟨True, hP.self, (Part.mem_map_iff _).2 ⟨True, hQ.self, by simp⟩⟩
    · obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.1 hx
      obtain ⟨b, -, hab⟩ := (Part.mem_map_iff _).1 hm
      exact hP.le x ((eq_true (of_eq_true hab).1) ▸ ha)
  · rw [Mode.combine?_evalPartial_fn_right] at h
    obtain ⟨R, hR, hgood⟩ := hG P hP
    cases h
    rw [hR]
    exact .pred hgood
  · rw [Mode.combine?_evalPartial_fn_left] at h
    obtain ⟨R, hR, hgood⟩ := hF Q hQ
    cases h
    rw [hR]
    exact .pred hgood
  · cases h

theorem good_lex (hB : 2 ≤ B.card) {c : Cat} {w : Morpheme}
    (hw : IsNominalLabel (.terminal c w)) {d : PDenotation (Finset α) Unit}
    (h : lex B w = some d) : Good B d := by
  have hB' : B ∈ boy B := mem_boy.2 ⟨subset_rfl, by omega⟩
  cases w with
  | boy =>
    cases h
    exact .pred ⟨fun _ ↦ trivial, by simpa using hB', fun x hx ↦ (mem_boy.1 (by simpa using hx)).1⟩
  | num m =>
    cases h
    refine .modifier fun P hP ↦ ⟨_, rfl, fun _ ↦ trivial, ?_, fun x hx ↦ ?_⟩
    · cases m
      · exact (PFun.true_mem_lift _ _).2 hP.self
      · simpa [NumberHead.denote, nonAtomsOf, atom_finset_iff_card_eq_one, hP.self] using
          (by omega : B.card ≠ 1)
    · cases m <;> simp [NumberHead.denote, nonAtomsOf] at hx
      · exact hP.le x hx
      · exact hP.le x hx.1
  | def_ =>
    cases h
    refine .modifier fun P hP ↦ ?_
    have hsup : B ∈ sup {x | True ∈ P x} := ⟨hP.self, fun x hx ↦ hP.le x hx⟩
    exact ⟨PFun.lift (· ∈ sup {x | True ∈ P x}), ite_eq_left ⟨B, hsup⟩, fun _ ↦ trivial,
      by simpa using hsup, fun x hx ↦ hP.le x (show x ∈ sup {x | True ∈ P x} by simpa using hx).1⟩
  | plusDef | exists_ | two | run => cases c <;> simp [IsNominalLabel] at hw

theorem good_of_licensed (hB : 2 ≤ B.card) {t : Tree Cat Morpheme}
    (ht : t.Licensed fun l _ ↦ IsNominalLabel l) {d : PDenotation (Finset α) Unit}
    (h : interpPartial (lex B) (fun _ ↦ ∅) t = some d) : Good B d := by
  induction t using Tree.rec' generalizing d with
  | terminal c w =>
    rw [interpPartial_terminal] at h
    exact good_lex hB ht.rel_root h
  | phrase c k cs ih =>
    match cs, ih, ht, h with
    | [t], ih, ht, h =>
      rw [interpPartial_phrase_unary] at h
      exact ih t (by simp) (ht.of_mem (by simp)) h
    | [t₁, t₂], ih, ht, h =>
      rw [interpPartial_phrase_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.1 h
      exact (ih t₁ (by simp) (ht.of_mem (by simp)) h₁).combine?
        (ih t₂ (by simp) (ht.of_mem (by simp)) h₂) h
    | [], _, _, h => cases h
    | _ :: _ :: _ :: _, _, _, h => cases h
  | trace n c => exact absurd ht.rel_root id
  | bind n c t _ => exact absurd ht.rel_root id
  | junk l cs hl _ => rw [interpPartial_junk _ _ hl] at h; cases h

-- every alternative of NumP* is uninterpretable, or defined wherever there are two boys
theorem defined_eq_empty_or_subset {ψ : Tree Cat Morpheme}
    (h : ψ ∈ structuralAlternatives lexicon (numPStar n)) :
    defined (α := α) ψ = ∅ ∨ {B : Finset α | 2 ≤ B.card} ⊆ defined ψ := by
  have htypes (B B' : Finset α) (w : Morpheme) :
      (lex B w).map (·.1) = (lex B' w).map (·.1) := by
    cases w <;> rfl
  by_cases hu : Uninterpretable (lex (∅ : Finset α)) (fun _ ↦ ∅) ψ
  · refine .inl (Set.eq_empty_of_forall_notMem fun B ⟨d, hd, _⟩ ↦ ?_)
    have := (uninterpretable_congr _ (lex B) _ (fun _ ↦ ∅) (htypes ∅ B) ψ).1 hu
    rw [Uninterpretable, hd] at this
    cases this
  · refine .inr fun B hB ↦ ?_
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1
      ((uninterpretable_congr _ (lex B) _ (fun _ ↦ ∅) (htypes ∅ B) ψ).not.1 hu)
    exact ⟨d, hd, (good_of_licensed hB (licensed_of_mem_structuralAlternatives h) hd).dom⟩

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
