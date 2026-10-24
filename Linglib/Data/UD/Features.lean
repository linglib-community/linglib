module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.Flat

/-!
# Universal Dependencies: morphological features
[de-marneffe-zeman-2021]

The morphological feature tags of UD v2, nominal, pronominal and verbal, and the annotation
record `MorphFeatures`, a tag or `⊥` in each feature. The analytical inventories of person,
number, gender and case realize as these tags and ingest from them in `Morphology/Word/UD.lean`;
the remaining tags serve as the value types of a token's features until an analytical
inventory exists.

Official site: <https://universaldependencies.org/>
-/

@[expose] public section


namespace UD

-- Nominal Features

/-- Grammatical number -/
inductive Number where
  | Sing   -- singular: cat, I
  | Plur   -- plural: cats, we
  | Dual   -- dual (two): eyes (in some languages)
  | Tri    -- trial (three)
  | Pauc   -- paucal (few)
  | Grpa   -- greater paucal
  | Grpl   -- greater plural
  | Inv    -- inverse number
  | Coll   -- collective
  | Count  -- count form
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical gender -/
inductive Gender where
  | Masc   -- masculine
  | Fem    -- feminine
  | Neut   -- neuter
  | Com    -- common (masc or fem)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Grammatical case (UD `Case` feature, https://universaldependencies.org/u/feat/Case.html).

    Battle-tested annotation tagset shared across all UD treebanks. The 28
    constructors below cover the standard UD values. This is the
    *realization* vocabulary; the canonical analytical inventory is the
    root-namespace `Case` (`Syntax/Case/Basic.lean`), realized and ingested in
    `Morphology/Word/UD.lean`. -/
inductive Case where
  | Nom    -- nominative: subject
  | Acc    -- accusative: direct object
  | Gen    -- genitive: possessor
  | Dat    -- dative: indirect object
  | Ins    -- instrumental
  | Loc    -- locative
  | Voc    -- vocative
  | Abl    -- ablative
  | Erg    -- ergative
  | Abs    -- absolutive
  -- Additional cases for specific languages
  | Par    -- partitive
  | Ess    -- essive
  | Tra    -- translative
  | Com    -- comitative
  | Ade    -- adessive
  | Ine    -- inessive
  | Ill    -- illative
  | Ela    -- elative
  | All    -- allative
  | Sub    -- sublative
  | Sup    -- superessive
  | Del    -- delative
  | Ter    -- terminative
  | Tem    -- temporal
  | Cau    -- causative
  | Ben    -- benefactive
  | Per    -- perlative: path, motion through
  | Abe    -- abessive/privative: 'without X'
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Definiteness -/
inductive Definite where
  | Def    -- definite: the cat
  | Ind    -- indefinite: a cat
  | Spec   -- specific indefinite
  | Cons   -- construct state
  deriving DecidableEq, Repr, Inhabited

/-- Degree of comparison (for adjectives/adverbs) -/
inductive Degree where
  | Pos    -- positive: big
  | Cmp    -- comparative: bigger
  | Sup    -- superlative: biggest
  | Abs    -- absolute superlative
  | Equ    -- equative
  deriving DecidableEq, Repr, Inhabited

-- Pronominal Features

/-- Pronoun type -/
inductive PronType where
  | Prs    -- personal: I, you, he
  | Rcp    -- reciprocal: each other
  | Art    -- article
  | Int    -- interrogative: who, what
  | Rel    -- relative: who, which
  | Dem    -- demonstrative: this, that
  | Emp    -- emphatic
  | Tot    -- total/collective: all, every
  | Neg    -- negative: nobody, nothing
  | Ind    -- indefinite: somebody, something
  | Exc    -- exclamative
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical person -/
inductive Person where
  | first  -- 1st person: I, we
  | second -- 2nd person: you
  | third  -- 3rd person: he, she, it, they
  | zero   -- 0 person (impersonal)
  deriving DecidableEq, Repr, Inhabited

-- Verbal Features

/-- Verb form -/
inductive VerbForm where
  | Fin    -- finite
  | Inf    -- infinitive
  | Part   -- participle
  | Ger    -- gerund
  | Gdv    -- gerundive
  | Sup    -- supine
  | Conv   -- converb/adverbial participle
  | Vnoun  -- verbal noun (masdar)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical tense -/
inductive Tense where
  | Past   -- past: walked
  | Pres   -- present: walks
  | Fut    -- future: will walk
  | Imp    -- imperfect
  | Pqp    -- pluperfect
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical aspect -/
inductive Aspect where
  | Imp    -- imperfective
  | Perf   -- perfective
  | Prog   -- progressive
  | Prosp  -- prospective
  | Hab    -- habitual
  | Iter   -- iterative
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical mood -/
inductive Mood where
  | Ind    -- indicative
  | Sub    -- subjunctive
  | Imp    -- imperative
  | Cnd    -- conditional
  | Opt    -- optative
  | Jus    -- jussive
  | Pot    -- potential
  | Qot    -- quotative
  | Adm    -- admirative
  | Nec    -- necessitative
  | Irr    -- irrealis
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical voice -/
inductive Voice where
  | Act    -- active
  | Pass   -- passive
  | Mid    -- middle
  | Rcp    -- reciprocal
  | Cau    -- causative
  | Antip  -- antipassive
  | Dir    -- direct
  | Inv    -- inverse
  | Lfoc   -- location-focus
  | Bfoc   -- beneficiary-focus
  deriving DecidableEq, Repr, Inhabited

/-- Polarity -/
inductive Polarity where
  | Pos    -- positive/affirmative
  | Neg    -- negative
  deriving DecidableEq, Repr, Inhabited

-- Feature Bundle

/-- A morphological annotation record, a tag or `⊥` in each feature. -/
structure MorphFeatures where
  number   : Flat Number   := ⊥
  gender   : Flat Gender   := ⊥
  case_    : Flat Case     := ⊥
  definite : Flat Definite := ⊥
  degree   : Flat Degree   := ⊥
  pronType : Flat PronType := ⊥
  /-- Reflexive, `Reflex=Yes`; `false` when the feature is absent. -/
  reflex   : Bool          := false
  person   : Flat Person   := ⊥
  verbForm : Flat VerbForm := ⊥
  tense    : Flat Tense    := ⊥
  aspect   : Flat Aspect   := ⊥
  mood     : Flat Mood     := ⊥
  voice    : Flat Voice    := ⊥
  polarity : Flat Polarity := ⊥
  deriving DecidableEq, Repr, Inhabited


end UD
