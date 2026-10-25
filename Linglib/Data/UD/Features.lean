module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.Flat

/-!
# Universal Dependencies: morphological features

The universal features of Universal Dependencies v2, an inductive of the values of each, and the
annotation record `UD.MorphFeatures`, which gives each feature a value or `⊥`, and each feature
whose one value is `Yes` a `Bool`. The analytical inventories of person, number and case realize
as these tags and ingest from them in `Morphology/Word/UD.lean`; the other tags serve as the
values of a token's features until an analytical inventory exists.

## Implementation notes

* The features and values are those of the source's Table 2 (p. 263), in its order, with the
  glosses of the guidelines of the same date. `NounClass` is left out: its values are per
  language family (`Bantu1` to `Bantu23`, `Wol1` to `Wol12`, and more), an open list.
* The layers of a feature, such as the possessor's number `Number[psor]` of a possessive
  (pp. 264–265), are not represented.
* Later guidelines tag the Hungarian sublative `Sbl` and use `Sub` for the subessive, and add the
  cases `Sbe` and `Spl`, the degrees `Dim` and `Aug` and the mood `Int`; the tags here are
  Table 2's, under which `Sub` is the sublative. Neither the guidelines of 2021 nor the later
  ones document `Tense=Nfut`, which Table 2 lists.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace UD

/-! ### Lexical features -/

/-- Pronominal type, the values of `PronType`. -/
inductive PronType where
  | Art    -- article
  | Dem    -- demonstrative pronoun, determiner, numeral or adverb
  | Emp    -- emphatic determiner
  | Exc    -- exclamative determiner
  | Ind    -- indefinite pronoun, determiner, numeral or adverb
  | Int    -- interrogative pronoun, determiner, numeral or adverb
  | Neg    -- negative pronoun, determiner or adverb
  | Prs    -- personal or possessive personal pronoun or determiner
  | Rcp    -- reciprocal pronoun
  | Rel    -- relative pronoun, determiner, numeral or adverb
  | Tot    -- total (collective) pronoun, determiner or adverb
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeral type, the values of `NumType`. -/
inductive NumType where
  | Card   -- cardinal
  | Dist   -- distributive
  | Frac   -- fraction
  | Mult   -- multiplicative
  | Ord    -- ordinal
  | Range  -- range of values
  | Sets   -- number of sets of things, collective
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Nominal features -/

/-- Gender, the values of `Gender`. -/
inductive Gender where
  | Com    -- common
  | Fem    -- feminine
  | Masc   -- masculine
  | Neut   -- neuter
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Animacy, the values of `Animacy`. -/
inductive Animacy where
  | Anim   -- animate
  | Hum    -- human
  | Inan   -- inanimate
  | Nhum   -- non-human
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Number, the values of `Number`. -/
inductive Number where
  | Coll   -- collective, mass, singulare tantum
  | Count  -- count plural
  | Dual   -- dual
  | Grpa   -- greater paucal
  | Grpl   -- greater plural
  | Inv    -- inverse
  | Pauc   -- paucal
  | Plur   -- plural
  | Ptan   -- plurale tantum
  | Sing   -- singular
  | Tri    -- trial
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Case, the values of `Case`: the core, the non-core and the local cases, as the guidelines
group them and Table 2 rows them. -/
inductive Case where
  | Abs    -- absolutive
  | Acc    -- accusative, oblique
  | Erg    -- ergative
  | Nom    -- nominative, direct

  | Abe    -- abessive
  | Ben    -- benefactive, destinative
  | Cau    -- causative, motivative, purposive
  | Cmp    -- comparative
  | Cns    -- considerative
  | Com    -- comitative, associative
  | Dat    -- dative
  | Dis    -- distributive
  | Equ    -- equative
  | Gen    -- genitive
  | Ins    -- instrumental, instructive
  | Par    -- partitive
  | Tem    -- temporal
  | Tra    -- translative, factive
  | Voc    -- vocative

  | Abl    -- ablative
  | Add    -- additive
  | Ade    -- adessive
  | All    -- allative
  | Del    -- delative
  | Ela    -- elative
  | Ess    -- essive, prolative
  | Ill    -- illative
  | Ine    -- inessive
  | Lat    -- lative, directional allative
  | Loc    -- locative
  | Per    -- perlative
  | Sub    -- sublative
  | Sup    -- superessive
  | Ter    -- terminative, terminal allative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Definiteness, the values of `Definite`. -/
inductive Definite where
  | Com    -- complex, of the improper annexation of Arabic
  | Cons   -- construct state, reduced definiteness
  | Def    -- definite
  | Ind    -- indefinite
  | Spec   -- specific indefinite
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Comparison, the values of `Degree`. -/
inductive Degree where
  | Abs    -- absolute superlative
  | Cmp    -- comparative
  | Equ    -- equative
  | Pos    -- positive
  | Sup    -- superlative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Verbal features -/

/-- Verbal form, the values of `VerbForm`. -/
inductive VerbForm where
  | Conv   -- converb, adverbial participle
  | Fin    -- finite
  | Gdv    -- gerundive
  | Ger    -- gerund
  | Inf    -- infinitive
  | Part   -- participle, verbal adjective
  | Sup    -- supine
  | Vnoun  -- verbal noun, masdar
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Mood, the values of `Mood`. -/
inductive Mood where
  | Adm    -- admirative
  | Cnd    -- conditional
  | Des    -- desiderative
  | Imp    -- imperative
  | Ind    -- indicative, realis
  | Irr    -- irrealis
  | Jus    -- jussive, injunctive
  | Nec    -- necessitative
  | Opt    -- optative
  | Pot    -- potential
  | Prp    -- purposive
  | Qot    -- quotative
  | Sub    -- subjunctive, conjunctive
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Tense, the values of `Tense`. -/
inductive Tense where
  | Fut    -- future
  | Imp    -- imperfect
  | Nfut   -- non-future
  | Past   -- past, preterite, aorist
  | Pqp    -- pluperfect
  | Pres   -- present, non-past
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Aspect, the values of `Aspect`. -/
inductive Aspect where
  | Hab    -- habitual
  | Imp    -- imperfect
  | Iter   -- iterative, frequentative
  | Perf   -- perfect
  | Prog   -- progressive
  | Prosp  -- prospective
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Voice, the values of `Voice`. -/
inductive Voice where
  | Act    -- active, actor focus
  | Antip  -- antipassive
  | Bfoc   -- beneficiary focus
  | Cau    -- causative
  | Dir    -- direct
  | Inv    -- inverse
  | Lfoc   -- location focus
  | Mid    -- middle
  | Pass   -- passive, patient focus
  | Rcp    -- reciprocal
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Evidentiality, the values of `Evident`. -/
inductive Evident where
  | Fh     -- firsthand
  | Nfh    -- non-firsthand
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Polarity, the values of `Polarity`. -/
inductive Polarity where
  | Neg    -- negative
  | Pos    -- positive, affirmative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Person, the values `0` to `4` of `Person`. -/
inductive Person where
  | zero   -- zero person, impersonal
  | first
  | second
  | third
  | fourth -- a third person distinguished from another third person
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Politeness, the values of `Polite`. -/
inductive Polite where
  | Elev   -- referent elevating
  | Form   -- formal register
  | Humb   -- speaker humbling
  | Infm   -- informal register
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Clusivity, the values of `Clusivity`. -/
inductive Clusivity where
  | In     -- inclusive
  | Ex     -- exclusive
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Annotation -/

/-- A morphological annotation, a value or `⊥` in each feature, and `true` in each feature whose
one value is `Yes` where it has that value. -/
structure MorphFeatures where
  pronType  : Flat PronType  := ⊥
  numType   : Flat NumType   := ⊥
  poss      : Bool           := false
  reflex    : Bool           := false
  foreign   : Bool           := false
  abbr      : Bool           := false
  typo      : Bool           := false
  gender    : Flat Gender    := ⊥
  animacy   : Flat Animacy   := ⊥
  number    : Flat Number    := ⊥
  case      : Flat Case      := ⊥
  definite  : Flat Definite  := ⊥
  degree    : Flat Degree    := ⊥
  verbForm  : Flat VerbForm  := ⊥
  mood      : Flat Mood      := ⊥
  tense     : Flat Tense     := ⊥
  aspect    : Flat Aspect    := ⊥
  voice     : Flat Voice     := ⊥
  evident   : Flat Evident   := ⊥
  polarity  : Flat Polarity  := ⊥
  person    : Flat Person    := ⊥
  polite    : Flat Polite    := ⊥
  clusivity : Flat Clusivity := ⊥
  deriving DecidableEq, Repr, Inhabited

end UD
