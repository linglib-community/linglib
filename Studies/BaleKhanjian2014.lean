module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Alternatives.Structural
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
alternative](##pluralIndefinite_not_mem_structuralAlternatives) to it and does not compete. The
singular and plural definites differ in the number head alone, and Maximize Presupposition against
the plural [makes the singular definite strictly singular](##strengthen_presup_sg). Under a
numeral the two heads mean the same, but applied where the definite marker meets the number phrase
Maximize Presupposition [still rules out the singular](##minimalFor_presup_iff). The purely syntactic
account, whose null singular is $[+\text{atomic}]$, leaves [a numeral on a singular nothing to
count](##numeral_atomsOf_eq_empty).

## Implementation notes

A world is the set of boys, and a presupposition the set of worlds where a constituent is
defined. The plural is Harbour's $[-\text{atomic}]$, and the paper's *sup* is the set of greatest
members, so that the definite, its σ, is `iota` after *sup*, the factoring of
`Linglib/Semantics/Reference/Iota.lean`. The definite marker is the number-phrase modifier of the
paper's final analysis, which it shows to be interpreted as the determiner of its first analysis
is. The allomorphs *-n* and *-ə* are one morpheme and the verb's agreement is spelled out with the
subject, so a plural alternative replaces the number head and nothing else, as the paper derives
it. The number head and the numeral have their own categories; the paper leaves the numeral and the
adjoined definite marker unlabelled, and the marker is `D` here, as where the paper labels it.

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

open Mereology Number Presupposition PhraseStructure Tree

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

/-! ### The definite -/

section Definite

variable {E : Type*} [PartialOrder E] {X : Set E}

/-- *sup* (37) sends a set to its members that bound it: the singleton of the supremum it
contains, or nothing. The definite is the choice function `iota` after it (p. 20). -/
def sup (X : Set E) : Set E := X ∩ upperBounds X

theorem mem_sup {x : E} : x ∈ sup X ↔ IsGreatest X x := .rfl

theorem sup_subsingleton : (sup X).Subsingleton := fun _ ha _ hb ↦ IsGreatest.unique ha hb

-- the choice function adds no presupposition to that of *sup*
theorem iota_sup_isSome_iff : (iota (sup X)).isSome ↔ (sup X).Nonempty :=
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

/-- The presupposition of NumP* (39), the definite marker on the number phrase with head `n`:
the sets of boys over which the number phrase contains its supremum. -/
def presup (n : NumberHead) : Set (Finset α) := {B | (sup (n.denote (boy B))).Nonempty}

-- p. 22: at least one boy for the singular, at least two for the plural
theorem presup_sg : presup (α := α) .sg = {B | 1 ≤ B.card} :=
  Set.ext fun _ ↦ by rw [presup, Set.mem_ofPred_eq, denote_sg_boy, nonempty_sup_card_le]; rfl

theorem presup_pl : presup (α := α) .pl = {B | 2 ≤ B.card} :=
  Set.ext fun _ ↦ by rw [presup, Set.mem_ofPred_eq, denote_pl_boy, nonempty_sup_card_le]; rfl

theorem presup_pl_ssubset_presup_sg [Nonempty α] : presup (α := α) .pl ⊂ presup .sg := by
  rw [presup_sg, presup_pl]
  refine ⟨fun _ h ↦ (by omega : 1 ≤ 2).trans h, fun h ↦ ?_⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  have : 2 ≤ ({a} : Finset α).card := h (by simp)
  simp at this

/-- The presupposition of the definite numeral phrase (39): `iota` applies to the groups of two
in NumP*. -/
def numeralPresup (n : NumberHead) : Set (Finset α) :=
  {B | (iota (numeral 2 (sup (n.denote (boy B))))).isSome}

-- p. 22: either way, exactly two boys
theorem numeralPresup_eq (n : NumberHead) : numeralPresup (α := α) n = {B | B.card = 2} := by
  ext B
  have hsub {X : Set (Finset α)} : (numeral 2 (sup X)).Subsingleton :=
    sup_subsingleton.anti fun _ h ↦ h.1
  have key {k : ℕ} (hk : k ≤ 2) :
      (numeral 2 (sup {x | x ⊆ B ∧ k ≤ x.card})).Nonempty ↔ B.card = 2 := by
    rw [sup_card_le]
    exact ⟨fun ⟨_, ⟨rfl, _⟩, h⟩ ↦ h, fun h ↦ ⟨B, ⟨rfl, by omega⟩, h⟩⟩
  rw [numeralPresup, Set.mem_ofPred_eq, hsub.iota_isSome_iff]
  cases n
  · rw [denote_sg_boy]; exact key (by omega)
  · rw [denote_pl_boy]; exact key le_rfl

end Definite

/-! ### Structures -/

/-- The categories of the paper's trees: the noun, the number head, the numeral, the determiner,
the verb, and the clause. -/
inductive Cat
  | N
  | Num
  | Numeral
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
  | .def_ | .plusDef | .exists_ => .D
  | .run => .V

/-- The lexicon the substitutions draw on: every morpheme under its category. -/
def lexicon : Finset (Tree Cat Morpheme) :=
  Finset.univ.image fun m ↦ .terminal m.cat m

/-- The number phrase over *dəgha* with head `n` (19). -/
def numP (n : NumberHead) : Tree Cat Morpheme :=
  .node .Num [.node .N [.terminal .N .boy], .terminal .Num (.num n)]

/-- NumP*, the definite marker adjoined to the number phrase (37a). -/
def numPStar (n : NumberHead) : Tree Cat Morpheme :=
  .adjoin .Num [numP n, .terminal .D .def_]

/-- *Dəgha-n vaze-ts* 'the boy ran' (11b), (37a), and its plural. -/
def definite (n : NumberHead) : Tree Cat Morpheme :=
  .node .S [.node .D [numPStar n, .terminal .D .plusDef], .node .V [.terminal .V .run]]

/-- *Yergu dəgha-n vaze-ts* (14a) and *yergu dəgha-ner-ə vaze-ts-in* (14b), the numeral above
NumP* (39). -/
def numeralDefinite (n : NumberHead) : Tree Cat Morpheme :=
  .node .S [.node .D [.adjoin .Num [.terminal .Numeral .two, numPStar n], .terminal .D .plusDef],
    .node .V [.terminal .V .run]]

/-- *Yergu dəgha vaze-ts* (10a) and *yergu dəgha-ner vaze-ts-in* (10b), determiner phrases with
the null existential (33). -/
def numeralIndefinite (n : NumberHead) : Tree Cat Morpheme :=
  .node .S [.node .D [.terminal .D .exists_, .adjoin .Num [.terminal .Numeral .two, numP n]],
    .node .V [.terminal .V .run]]

/-- *Dəgha vaze-ts* (3), a bare noun phrase whose existential force the verb supplies (21). -/
def singularIndefinite : Tree Cat Morpheme :=
  .node .S [.node .N [.terminal .N .boy], .node .V [.terminal .V .run]]

/-- *Dəgha-ner vaze-ts-in* (7), a determiner phrase with the null existential (20). -/
def pluralIndefinite : Tree Cat Morpheme :=
  .node .S [.node .D [.terminal .D .exists_, numP .pl], .node .V [.terminal .V .run]]

/-- The singular indefinite does not compete with the plural indefinite: the plural has a
determiner phrase, and neither the singular nor the lexicon has one (p. 16). -/
theorem pluralIndefinite_not_mem_structuralAlternatives :
    pluralIndefinite ∉ structuralAlternatives lexicon singularIndefinite := fun h ↦
  (by decide : ¬ ∀ s ∈ pluralIndefinite.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = .D))
    (phrase_preservation _ .D (forall_mem_substitutionSource.2 ⟨by decide, by decide⟩)
      (by decide) h)

/-- The number heads that compete with `n` in the construction `t`: those whose structure is a
structural alternative of the structure with `n`. -/
def alts (t : NumberHead → Tree Cat Morpheme) (n : NumberHead) : Set NumberHead :=
  t ⁻¹' structuralAlternatives lexicon (t n)

-- p. 17: replacing the number head gives the alternative
theorem alts_eq_univ {t : NumberHead → Tree Cat Morpheme}
    (ht : ∀ n m, t m = (t n).leafSubst (.num n) (.num m) .Num) (hwf : ∀ n, (t n).IsWellFormed)
    (n : NumberHead) : alts t n = Set.univ :=
  Set.eq_univ_of_forall fun m ↦ by
    rw [alts, Set.mem_preimage, ht n m]
    exact horn_alternatives_are_structural lexicon (t n) _ _ _
      (Finset.mem_image.2 ⟨.num m, Finset.mem_univ _, rfl⟩) (hwf n)

theorem alts_numPStar : alts numPStar = fun _ ↦ Set.univ :=
  funext <| alts_eq_univ (by decide) (by decide)

theorem alts_definite : alts definite = fun _ ↦ Set.univ :=
  funext <| alts_eq_univ (by decide) (by decide)

theorem alts_numeralDefinite : alts numeralDefinite = fun _ ↦ Set.univ :=
  funext <| alts_eq_univ (by decide) (by decide)

theorem alts_numeralIndefinite : alts numeralIndefinite = fun _ ↦ Set.univ :=
  funext <| alts_eq_univ (by decide) (by decide)

/-! ### Maximize Presupposition -/

section Competition

variable {α : Type*}

/-- Strengthened against the plural definite, the singular definite *dəgha-n* presupposes a
single boy (11b). -/
theorem strengthen_presup_sg [Nonempty α] :
    strengthen (alts definite) presup .sg = {B : Finset α | B.card = 1} := by
  rw [strengthen_eq_sdiff (ψ := .pl) (by simp [alts_definite]) presup_pl_ssubset_presup_sg
    fun χ _ h ↦ by cases χ; exacts [absurd rfl h.ne, le_rfl], presup_sg, presup_pl]
  ext B
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  omega

-- p. 22: the numeral definites presuppose the same, so competition over the whole phrase is inert
theorem strengthen_numeralPresup (n : NumberHead) :
    strengthen (alts numeralDefinite) numeralPresup n = numeralPresup (α := α) n :=
  strengthen_eq_self fun m _ h ↦ h.ne (by rw [numeralPresup_eq, numeralPresup_eq])

/-- Maximize Presupposition applied at NumP* rules out the singular under a numeral on a definite
(14a) and keeps the plural (14b): wherever the definite numeral phrase is defined, so is the
plural's stronger local presupposition (p. 23). -/
theorem minimalFor_presup_iff [Nonempty α] {c : Set (Finset α)} {n : NumberHead}
    (hc : c ⊆ numeralPresup n) :
    MinimalFor (· ∈ insert n (alts numPStar n) ∩ presup ⁻¹' Set.Ici c) (presup (α := α)) n ↔
      n = .pl := by
  rw [numeralPresup_eq] at hc
  have hpl : c ⊆ presup .pl := hc.trans fun B h ↦ by rw [presup_pl]; exact h.ge
  rw [minimalFor_preimage_Ici_iff, alts_numPStar]
  cases n
  · simp only [reduceCtorEq, iff_false, not_and, not_forall]
    exact fun _ ↦ ⟨.pl, trivial, presup_pl_ssubset_presup_sg, fun h ↦ h hpl⟩
  · refine iff_of_true ⟨hpl, fun m _ h ↦ ?_⟩ rfl
    cases m
    · exact absurd presup_pl_ssubset_presup_sg.subset h.not_subset
    · exact absurd rfl h.ne

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

-- (14): the rows fit Maximize Presupposition at NumP*, in any context for a group of two
theorem rows_numeralDefinite {c : Set (Finset Boy)} (hc : c ⊆ {B | B.card = 2}) :
    (∀ r ∈ Examples.all, ∀ n ∈ numeralDefinite? r,
      (MinimalFor (· ∈ insert n (alts numPStar n) ∩ presup ⁻¹' Set.Ici c) (presup (α := Boy)) n ↔
        r.judgment = .acceptable)) ∧
    Datum.ReadCount numeralDefinite? Examples.all 2 := by
  refine ⟨fun r hr n hn ↦ ?_, by decide +kernel⟩
  rw [minimalFor_presup_iff (by rwa [numeralPresup_eq])]
  revert n
  revert r
  decide +kernel

end BaleKhanjian2014
