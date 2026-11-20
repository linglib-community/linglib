module

public import Linglib.Morphology.Nanosyntax.Lexicon
public import Linglib.Data.Wordlist.DeClercqEtAl2025

/-!
# De Clercq, Caha, Starke and Vanden Wyngaerd (2025): root size and root shape

A root of nanosyntax is the lexical entry that lexicalizes the bottom of a functional sequence.
Its *size* is the spine it stores. A sequence that spine reaches is lexicalized without movement
and pronounced as the root alone (`Morphology.Nanosyntax.exponents_cons_of_eq_some`), and each
feature above it needs a suffix, an entry whose foot the evacuated root has left alone.

A root may also store the object evacuation builds, the Merge `s * r` of a spine `s` and a remnant
`r` with another foot. Such an entry matches the spines on its foot up to `s`, and the whole
object, and no spine between the two
(`Morphology.Nanosyntax.merge_spine_containsOrEq_spine_iff`). A lexicon none of whose entries
stores an unlabelled node cannot give a sequence one exponent and an initial part of it two
(`Morphology.Nanosyntax.exists_exponents_eq_singleton_of_prefix`), so a noun with a suffix in the
singular and none in the plural, or a verb with a suffix in the second person alone, has a root
of this shape.

The file runs the lexicalization algorithm on the lexicons of four case studies, the degrees of
comparison of English, Czech and Armenian, two Czech declensions, number in Kalenjin and the
present tense of Tualis Friulian, and compares its exponents with those of the lexicalization
tables in `DeClercqEtAl2025.Wordlist`.

## Implementation notes

* A prefix is built in a workspace of its own, which the algorithm of
  `Morphology.Nanosyntax.lexicalize` does not model. The Czech superlative prefix *nej-* is
  therefore outside its reach, and `exponents_inteligent_sup` records that the movement steps
  alone do not derive the superlative.
* The entry of English *bad* is given the size of *tall*, which the comparison with *worse*
  presupposes.
* The Kalenjin plural suffix *-tiin* of *kipaw* 'rhino' has no entry in the source, so that noun
  has rows in the data and no lexicon here.
* An exponent is the underlying form of the lexicalization tables: *pata* in *pat-een*, *chytr*
  and *-ějš* in *chytř-ejš-í*.

## TODO

* The comparison with matching by feature sets and with spans: under either, an entry that
  lexicalizes the plural lexicalizes the singular. `not_derives_peel_of_labelled` is the
  corresponding statement for constituent matching without stored evacuation.

## References

* [declercq-et-al-2025]
* [starke-2018]
-/

@[expose] public section

namespace DeClercqEtAl2025

open Morphology.Nanosyntax Morphology
open Minimalist (PlanarSyntacticObject)

variable {F : Type} [DecidableEq F]

/-- The algorithm gives each analysed form the exponents of its row in a lexicalization table,
for the feature sequence `seq` assigns to the form's cell. -/
abbrev Derives (L : RuleSet (LexicalEntry F String)) (seq : Wordlist.Cell → List F)
    (rows : List Wordlist.Analysis) : Prop :=
  ∀ a ∈ rows, exponents (spellout L) (seq a.form.cell) = some a.exponents

/-! ### Degrees of comparison -/

/-- The features of the adjectival sequence are the adjective, gradability, the comparative
and the superlative. -/
inductive Deg where
  | a | q | cmpr | sprl
  deriving DecidableEq, Repr

/-- The sequence of a degree, each degree containing the one below it. -/
def degreeSeq (c : Wordlist.Cell) : List Deg :=
  match c.degree with
  | .some .Pos => [.a, .q]
  | .some .Cmp => [.a, .q, .cmpr]
  | .some .Sup => [.a, .q, .cmpr, .sprl]
  | _ => []

/-- (20a), (21a), (22a): English *tall* stores the gradable adjective, *-er* the comparative
alone and *-est* the superlative over the comparative. -/
def tall : RuleSet (LexicalEntry Deg String) :=
  [⟨spine .a [.q], "tall"⟩, ⟨spine .cmpr [], "er"⟩, ⟨spine .cmpr [.sprl], "est"⟩]

/-- English *bad* beside *worse*, a root storing the comparative. -/
def bad : RuleSet (LexicalEntry Deg String) :=
  [⟨spine .a [.q], "bad"⟩, ⟨spine .a [.q, .cmpr], "worse"⟩, ⟨spine .cmpr [], "er"⟩]

/-- (17): Armenian *partsrahasag* 'tall' stores the superlative. -/
def partsrahasag : RuleSet (LexicalEntry Deg String) :=
  [⟨spine .a [.q, .cmpr, .sprl], "partsrahasag"⟩]

/-- (31): Czech *inteligent-* stores the bare adjective, with the adjectivizer *-n* and the
comparative *-ějš* storing one feature each. -/
def inteligent : RuleSet (LexicalEntry Deg String) :=
  [⟨spine .a [], "inteligent"⟩, ⟨spine .q [], "n"⟩, ⟨spine .cmpr [], "ějš"⟩]

/-- Czech *chytr-* 'smart' stores the gradable adjective. -/
def chytr : RuleSet (LexicalEntry Deg String) :=
  [⟨spine .a [.q], "chytr"⟩, ⟨spine .cmpr [], "ějš"⟩]

/-- The size of the root decides the number of suffixes. *tall* takes *-er*, and *-est* overrides
it; *worse* needs no evacuation, so the comparative is not *badd-er*; *partsrahasag* has one form
in all degrees; *inteligent-* takes a suffix more than *chytr-*. -/
theorem derives_degrees :
    Derives tall degreeSeq [Wordlist.tall.analysis, Wordlist.taller.analysis,
        Wordlist.tallest.analysis] ∧
      Derives bad degreeSeq [Wordlist.bad.analysis, Wordlist.worse.analysis] ∧
      Derives partsrahasag degreeSeq [Wordlist.partsrahasag_pos.analysis,
        Wordlist.partsrahasag_cmp.analysis, Wordlist.partsrahasag_sup.analysis] ∧
      Derives inteligent degreeSeq [Wordlist.inteligentni.analysis,
        Wordlist.inteligentnejsi.analysis] ∧
      Derives chytr degreeSeq [Wordlist.chytry.analysis, Wordlist.chytrejsi.analysis] := by
  decide

-- Section 1.4.4
theorem exponents_inteligent_sup :
    exponents (spellout inteligent) (degreeSeq Wordlist.nejinteligentnejsi.cell) = none := by
  decide

/-! ### Czech declension -/

/-- The features of the nominal sequence are the noun, the singular, and one each for the
nominative, the accusative and the genitive. -/
inductive Case where
  | n | sg | k1 | k2 | k3
  deriving DecidableEq, Repr

/-- The sequence of a case of the singular, each case containing the one below it. -/
def caseSeq (c : Wordlist.Cell) : List Case :=
  match c.case with
  | .some .Nom => [.n, .sg, .k1]
  | .some .Acc => [.n, .sg, .k1, .k2]
  | .some .Gen => [.n, .sg, .k1, .k2, .k3]
  | _ => []

/-- (32c): The suffix *-a* stores the genitive down to the singular. -/
def suffixA : LexicalEntry Case String := ⟨spine .sg [.k1, .k2, .k3], "a"⟩

/-- (32a): *chleb-* 'bread' stores the bare noun. -/
def chleb : RuleSet (LexicalEntry Case String) := [⟨spine .n [], "chleb"⟩, suffixA]

/-- (32b): *jazyk* 'tongue' stores the accusative. -/
def jazyk : RuleSet (LexicalEntry Case String) :=
  [⟨spine .n [.sg, .k1, .k2], "jazyk"⟩, suffixA]

-- Table 1.5
theorem derives_declension :
    Derives chleb caseSeq [Wordlist.chleba_nom.analysis, Wordlist.chleba_acc.analysis,
        Wordlist.chleba_gen.analysis] ∧
      Derives jazyk caseSeq [Wordlist.jazyk_nom.analysis, Wordlist.jazyk_acc.analysis,
        Wordlist.jazyka_gen.analysis] := by
  decide

/-- In the genitive the root *jazyk* cannot grow, and no entry lexicalizes the genitive feature
alone, so the derivation goes back to the merger of the singular and evacuates the noun there.
Its structure is then that of *chleb-a*, the bare noun beside the phrase *-a* stores. -/
theorem lexicalize_jazyk_gen :
    (lexicalize (spellout jazyk) (caseSeq Wordlist.gen)).map (·.toSyntacticObject) =
        some (spine .n [] * suffixA.tree) ∧
      (lexicalize (spellout chleb) (caseSeq Wordlist.gen)).map (·.toSyntacticObject) =
        some (spine .n [] * suffixA.tree) := by
  decide

/-! ### Inverse number marking -/

/-- The features of the number sequence are the noun, the singular and the plural. -/
inductive Num where
  | n | sg | pl
  deriving DecidableEq, Repr

/-- The sequence of a number, the plural containing the singular. -/
def numSeq (c : Wordlist.Cell) : List Num :=
  match c.number with
  | .some .Sing => [.n, .sg]
  | .some .Plur => [.n, .sg, .pl]
  | _ => []

/-- The Kalenjin singular suffix *-yaan* stores the singular alone and the plural suffix *-een*
the plural over it. -/
def numberSuffixes : RuleSet (LexicalEntry Num String) :=
  [⟨spine .sg [], "yaan"⟩, ⟨spine .sg [.pl], "een"⟩]

/-- (34a): *peel* 'elephant' stores the noun beside the plural phrase it has evacuated from. -/
def peelEntry : LexicalEntry Num String :=
  ⟨spine .n [] * spine .sg [.pl], "peel"⟩

/-- The lexicon of *peel*. -/
def peel : RuleSet (LexicalEntry Num String) := peelEntry :: numberSuffixes

/-- *pata* 'duck' stores the bare noun. -/
def pata : RuleSet (LexicalEntry Num String) := ⟨spine .n [], "pata"⟩ :: numberSuffixes

-- (35b)
theorem matches_peelEntry_iff (gs : List Num) : peelEntry.Matches (spine .n gs) ↔ gs = [] :=
  (merge_spine_containsOrEq_spine_iff (by decide)).trans List.prefix_nil

/-- *peel-yaan*, *peel* and *pata-yaan*, *pat-een*. The entry of *peel* contains the bare noun and
no singular phrase over a noun, so the singular needs *-yaan*. -/
theorem derives_number :
    Derives peel numSeq [Wordlist.peelyaan_sg.analysis, Wordlist.peel_pl.analysis] ∧
      Derives pata numSeq [Wordlist.patayaan_sg.analysis, Wordlist.pateen_pl.analysis] := by
  decide

-- (38)
theorem lexicalize_peel_pl :
    (lexicalize (spellout peel) (numSeq Wordlist.pl)).map (·.toSyntacticObject) =
        some peelEntry.tree ∧
      (lexicalize (spellout pata) (numSeq Wordlist.pl)).map (·.toSyntacticObject) =
        some peelEntry.tree := by
  decide

/-- No lexicon without a stored unlabelled node derives the paradigm of *peel*: a root that
lexicalizes the plural by itself would lexicalize the singular by itself. -/
theorem not_derives_peel_of_labelled {L : RuleSet (LexicalEntry Num String)}
    (hL : ∀ e ∈ L, ¬ HasUnlabelled e.tree) :
    ¬ Derives L numSeq [Wordlist.peelyaan_sg.analysis, Wordlist.peel_pl.analysis] := fun h ↦ by
  have hpl : exponents (spellout L) [.n, .sg, .pl] = some ["peel"] := h _ (.tail _ (.head _))
  have hsg : exponents (spellout L) [.n, .sg] = some ["peel", "yaan"] := h _ (.head _)
  obtain ⟨y, hy⟩ := exists_exponents_eq_singleton_of_prefix (isLowerSpellout_spellout L)
    (fun _ ↦ not_hasUnlabelled_of_isSome hL) (gs := [.sg]) ⟨[.pl], rfl⟩ hpl
  simp [hsg] at hy

/-! ### The Friulian present -/

/-- (39): The features of the verbal sequence are tense, number, person, participant and speaker. -/
inductive Phi where
  | t | num | π | part | spkr
  deriving DecidableEq, Repr

/-- The sequence of a person of the singular: the third person has the person feature, the
second the participant over it and the first the speaker over that. -/
def personSeq (c : Wordlist.Cell) : List Phi :=
  match c.person with
  | .some .third => [.t, .num, .π]
  | .some .second => [.t, .num, .π, .part]
  | .some .first => [.t, .num, .π, .part, .spkr]
  | _ => []

/-- (40b): The second-person suffix *-s* stores the participant alone. -/
def suffixS : LexicalEntry Phi String := ⟨spine .part [], "s"⟩

/-- (40a): Tualis Friulian *bat-* 'hit' stores the person phrase beside the speaker phrase it has
evacuated from. -/
def batEntry : LexicalEntry Phi String :=
  ⟨spine .t [.num, .π] * spine .part [.spkr], "bat"⟩

/-- The lexicon of *bati*. -/
def bat : RuleSet (LexicalEntry Phi String) := [batEntry, suffixS]

/-- (46a): The suffix *-iʃ* stores the speaker over a person phrase stranded beside the
participant. -/
def suffixIS : LexicalEntry Phi String :=
  ⟨phrase .spkr (spine .π [] * spine .part []), "iʃ"⟩

/-- (46b): *fin-* 'finish' stores number over tense. -/
def fin : RuleSet (LexicalEntry Phi String) :=
  [⟨spine .t [.num], "fin"⟩, suffixIS, suffixS]

-- (41)
theorem matches_batEntry_iff (gs : List Phi) :
    batEntry.Matches (spine .t gs) ↔ gs <+: [.num, .π] :=
  merge_spine_containsOrEq_spine_iff (by decide)

/-- *bat*, *bat-s*, *bat* and *fin-iʃ*, *fin-iʃ-s*, *fin-iʃ*. The entry of *bat-* contains the
third-person phrase and no participant phrase over it, so the second person needs *-s*. -/
theorem derives_present :
    Derives bat personSeq [Wordlist.bat_1.analysis, Wordlist.bats_2.analysis,
        Wordlist.bat_3.analysis] ∧
      Derives fin personSeq [Wordlist.finis_1.analysis, Wordlist.finiss_2.analysis,
        Wordlist.finis_3.analysis] := by
  decide

-- (42b), (49c)
theorem lexicalize_p1 :
    (lexicalize (spellout bat) (personSeq Wordlist.p1)).map (·.toSyntacticObject) =
        some batEntry.tree ∧
      (lexicalize (spellout fin) (personSeq Wordlist.p1)).map (·.toSyntacticObject) =
        some (spine .t [.num] * suffixIS.tree) := by
  decide

-- Table 1.8
theorem not_derives_bati_of_labelled {L : RuleSet (LexicalEntry Phi String)}
    (hL : ∀ e ∈ L, ¬ HasUnlabelled e.tree) :
    ¬ Derives L personSeq [Wordlist.bat_1.analysis, Wordlist.bats_2.analysis,
      Wordlist.bat_3.analysis] := fun h ↦ by
  have h₁ : exponents (spellout L) [.t, .num, .π, .part, .spkr] = some ["bat"] := h _ (.head _)
  have h₂ : exponents (spellout L) [.t, .num, .π, .part] = some ["bat", "s"] :=
    h _ (.tail _ (.head _))
  obtain ⟨y, hy⟩ := exists_exponents_eq_singleton_of_prefix (isLowerSpellout_spellout L)
    (fun _ ↦ not_hasUnlabelled_of_isSome hL) (gs := [.num, .π, .part]) ⟨[.spkr], rfl⟩ h₁
  simp [h₂] at hy

end DeClercqEtAl2025
