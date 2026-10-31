module

public import Linglib.Data.Examples.Bresnan1973
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.Readers

/-!
# Bresnan (1973): Syntax of the comparative clause construction in English

Every English comparative is built on a quantifier phrase, a Det of *as*, *too*, *that*, *so*,
*-er* or *-est* over a Q drawn from *much*, *many*, *little*, *few* and *enough*, so that *more*
is *-er much* or *-er many* and *taller* derives from *[[much-er] tall]* (Bresnan). Three
ordered rules derive the head: *-er* Encliticizing moves the clitic onto Q and leaves the Det
empty; Much Deletion then removes an unprotected *much* directly before the adjective of its
AP, so *as much tall* becomes *as tall* while *much-er tall* survives to become *taller*; and
QP Raising, on the empty Det alone, feeds AP Shift, *a more reliable man* beside *too reliable
a man* and *\*a too reliable man*. The clause is related to the head by Comparative Formation:
every *than* and *as* phrase is a full clause from which a constituent nondistinct from the
head, a QP, an AP or an NP, is deleted, the remainder positioned to the head's right. The four
puzzles of the introduction turn on the identity of the head and of the deleted constituent:
whether the clause predicates *a man* of the standard (A), whether the clause has a partitive
to match a partitive head (B), whether the QP is AP-internal so that the synthetic form can
arise (C), and whether the identity of a Q with a definite measure phrase is consistent with
the privative adjective it modifies (D).

## Implementation notes

Each row carries the paper's analysis of its example as features, the Det and Q of the QP
and its position, or the head's category and site and the constituent the clause supplies;
acceptability is derived from the rules. The anomaly of (242d) is read off the lexical gender
of *mother* and *man* in the English fragment, privativeness off the polarity of *short*. QP
recursion and QP Shift (1.4), *so* and *such* (1.5), *of* Insertion, Enough Permutation and
the ambiguities of 1.8 beyond the homophony of *more* are not formalized.

## References

* [bresnan-1973]
* [ross-1967]
-/

@[expose] public section

namespace Bresnan1973


/-! ### The quantifier phrase (1.1–1.3) -/

/-- The particles of the Det position (108), and the negative-dependent *any* and *no* that
share it with *-er* (117)–(127). -/
inductive Particle
  | as_ | too | that_ | so | any_ | no_
  deriving DecidableEq, Repr

/-- The determiners that encliticize onto Q: *-er* by (20) and the indefinite superlative
*-est* (223). -/
inductive Clitic
  | er | est
  deriving DecidableEq, Repr

/-- The Det of a QP: a particle, a clitic, or *any* or *no* beside *-er*. -/
structure Det where
  particle : Option Particle := none
  clitic : Option Clitic := none
  deriving DecidableEq, Repr

/-- A clitic shares the Det only with *any* or *no*: `*as more`, `*too most` (224). -/
def Det.WellFormed (d : Det) : Prop :=
  d.clitic.isSome → ∀ p ∈ d.particle, p = .any_ ∨ p = .no_

instance : DecidablePred Det.WellFormed := λ _ => by unfold Det.WellFormed; infer_instance

/-- The Q position (6): *much*, *little* and *enough* select mass nouns, *many* and *few*
indefinite plurals, *enough* both (1.3). -/
inductive Q
  | much | many | little | few | enough
  deriving DecidableEq, Repr

/-- The Qs that select mass nouns, and with them adjectives and adverbs. -/
def Q.SelectsMass (q : Q) : Prop := q = .much ∨ q = .little ∨ q = .enough

instance : DecidablePred Q.SelectsMass := λ _ => by unfold Q.SelectsMass; infer_instance

/-- The Qs that select indefinite plurals. -/
def Q.SelectsCount (q : Q) : Prop := q = .many ∨ q = .few ∨ q = .enough

instance : DecidablePred Q.SelectsCount := λ _ => by unfold Q.SelectsCount; infer_instance

/-- A QP (6), (146c): `(Det) Q`. -/
structure QP where
  det : Det
  q : Q
  deriving DecidableEq, Repr

/-- (107)–(109): *enough* is subcategorized for the null Det, `*so enough`, `*enougher`;
with (224), the closed Det inventory of (4) and (5). -/
def QP.WellFormed (qp : QP) : Prop := qp.det.WellFormed ∧ (qp.q = .enough → qp.det = {})

instance : DecidablePred QP.WellFormed := λ _ => by unfold QP.WellFormed; infer_instance

/-- The suppletive forms of (7) and (223). -/
inductive Form
  | more | less | fewer | most | least | fewest
  deriving DecidableEq, Repr

/-- (7), (223): a clitic on Q surfaces suppletively, `much + -er = more`,
`little + -est = least`; *enough* takes no clitic (107). -/
def suppletion : Clitic → Q → Option Form
  | .er, .much | .er, .many => some .more
  | .er, .little => some .less
  | .er, .few => some .fewer
  | .est, .much | .est, .many => some .most
  | .est, .little => some .least
  | .est, .few => some .fewest
  | _, .enough => none

/-- The suppletive surface of a QP, if any. -/
def QP.suppletion (qp : QP) : Option Form :=
  qp.det.clitic.bind (Bresnan1973.suppletion · qp.q)

-- (232), (7)
theorem more_ambiguous :
    ∃ q q' : Q, q.SelectsCount ∧ ¬ q.SelectsMass ∧ q'.SelectsMass ∧ ¬ q'.SelectsCount ∧
      suppletion .er q = suppletion .er q' :=
  ⟨.many, .much, by decide⟩

/-! ### Much Deletion and the simple comparative (1.1) -/

/-- Where a QP stands: as the left branch of its AP (146a), of its NP, the partitive, or of
another QP (140a); as a modifier of a VP or S, the adverbial and substantive uses (257),
(272); or, in a comparative clause, as a term of an identity with a definite measure phrase,
`six feet = x much` (286a), or with a phrase, `two friends = that many friends` (287c). -/
inductive Position
  | adjective | noun | quantifier | phrase | measure | term
  deriving DecidableEq, Repr

/-- A term of one of the identities of (286)–(287). -/
def Position.InIdentity (p : Position) : Prop := p = .measure ∨ p = .term

instance : DecidablePred Position.InIdentity := λ _ => by
  unfold Position.InIdentity; infer_instance

/-- (10) Much Deletion, `much → ∅ / [… _ A]_AP`, ordered after *-er* Encliticizing (20): an
uncliticized *much* directly before the adjective of its AP deletes, and only there (278);
the clitic intervenes in `[[much-er] tall]`, so `*as much tall` reduces to *as tall* while
*more tall* survives (21). -/
def MuchDeletes (qp : QP) (p : Position) : Prop :=
  qp.q = .much ∧ qp.det.clitic = none ∧ p = .adjective

instance (qp : QP) (p : Position) : Decidable (MuchDeletes qp p) := by
  unfold MuchDeletes; infer_instance

/-- (21d): the simple comparative *taller* from the compound `[[much-er] tall]`, so only for
the QP that is the left branch of its AP (277). -/
def Synthetic (qp : QP) (p : Position) : Prop :=
  qp.q = .much ∧ qp.det.clitic = some .er ∧ p = .adjective

instance (qp : QP) (p : Position) : Decidable (Synthetic qp p) := by
  unfold Synthetic; infer_instance

theorem Synthetic.not_muchDeletes {qp : QP} {p : Position} (h : Synthetic qp p) :
    ¬ MuchDeletes qp p :=
  λ h' => Option.some_ne_none _ (h.2.1.symm.trans h'.2.1)

/-- The surface of a QP before what it modifies: Q overt, *much* deleted, or the synthetic
comparative. -/
inductive Surface
  | analytic | deleted | synthetic
  deriving DecidableEq, Repr

/-- Much Deletion is obligatory where it applies, and the synthetic form needs the
AP-internal compound. -/
def Surface.Licit (s : Surface) (qp : QP) (p : Position) : Prop :=
  (s = .deleted ↔ MuchDeletes qp p) ∧ (s = .synthetic → Synthetic qp p)

instance (s : Surface) (qp : QP) (p : Position) : Decidable (s.Licit qp p) := by
  unfold Surface.Licit; infer_instance

/-! ### QP Raising and AP Shift (1.6) -/

/-- (205) QP Raising needs the Det of Q empty: after *-er* Encliticizing, *more*, *less* and
*enough* raise (207), while a particle, alone or beside *-er*, keeps the QP in place
(208)–(209). -/
def QPRaises (qp : QP) : Prop := qp.det.particle = none

instance : DecidablePred QPRaises := λ _ => by unfold QPRaises; infer_instance

/-- The order of the AP and the indefinite article in a predicative NP (111)–(116). -/
inductive Order
  | prearticle | postarticle
  deriving DecidableEq, Repr

/-- (206) AP Shift moves the raised AP around the article, *a more reliable man*; an unraised
QP keeps the AP before the article, *too reliable a man*, `*a too reliable man`
(217)–(218). -/
def Order.Licit (o : Order) (qp : QP) : Prop := o = .postarticle → QPRaises qp

instance (o : Order) (qp : QP) : Decidable (o.Licit qp) := by unfold Order.Licit; infer_instance

/-! ### Comparative Formation (Section 2) -/

/-- The categories over which the identities of (286)–(287) and deletion under
nondistinctness are stated. -/
inductive Cat
  | qp | ap | np
  deriving DecidableEq, Repr

/-- Same or similar categories: QP and AP are interchangeable (1.4), `six feet = that tall`
(286c), while an NP equates with no measure category, `*Bill = that much` (286b). -/
def Cat.Similar (a b : Cat) : Prop := a = b ∨ (a = .qp ∧ b = .ap) ∨ (a = .ap ∧ b = .qp)

instance : DecidableRel Cat.Similar := λ _ _ => by unfold Cat.Similar; infer_instance

theorem Cat.Similar.symm {a b : Cat} : a.Similar b → b.Similar a
  | .inl h => .inl h.symm
  | .inr (.inl ⟨ha, hb⟩) => .inr (.inr ⟨hb, ha⟩)
  | .inr (.inr ⟨ha, hb⟩) => .inr (.inl ⟨hb, ha⟩)

/-- The head of the construction (Section 1): the constituent the clause must match, the
position of its governing QP, and the polarity of the adjective that QP modifies, if any. -/
structure Head where
  cat : Cat
  site : Position
  polarity : Option Polarity
  deriving DecidableEq, Repr

/-- (296): privative adjectives such as *short* admit no modifier of definite measurement,
`*five feet short`. -/
def Head.Privative (h : Head) : Prop := h.polarity = some .negative

instance : DecidablePred Head.Privative := λ _ => by unfold Head.Privative; infer_instance

/-- What the clause supplies in the head's place: the category of the matching constituent
and the position of its QP. -/
structure Supply where
  cat : Cat
  site : Position
  deriving DecidableEq, Repr

/-- Comparative Formation: something in the clause is deleted under nondistinctness from the
head. The clause must supply a constituent of the same or a similar category; a matched QP
must be a term of an identity or the adverbial matching an adverbial head, since a left branch
of an NP or AP cannot be factored out ((301), [ross-1967]); and a Q nondistinct from the
modifier of a privative adjective cannot be equated with a definite measure phrase (297). -/
def Formation (h : Head) (c : Supply) : Prop :=
  c.cat.Similar h.cat ∧
    (h.cat = .qp → c.site.InIdentity ∨ (c.site = .phrase ∧ h.site = .phrase)) ∧
    (h.cat = .qp → c.site = .measure → ¬ h.Privative)

instance (h : Head) (c : Supply) : Decidable (Formation h c) := by unfold Formation; infer_instance

-- (286b), (287b)
theorem not_formation_of_np {h : Head} {c : Supply} (hh : h.cat = .qp) (hc : c.cat = .np) :
    ¬ Formation h c :=
  λ ⟨hs, _, _⟩ => by simp [Cat.Similar, hh, hc] at hs

-- (297)
theorem not_formation_of_privative {h : Head} {c : Supply} (hh : h.cat = .qp)
    (hp : h.Privative) (hc : c.site = .measure) : ¬ Formation h c :=
  λ ⟨_, _, hm⟩ => hm hh hc hp

-- (296b)
theorem formation_ap_measure (site : Position) (polarity : Option Polarity) :
    Formation ⟨.ap, site, polarity⟩ ⟨.ap, .measure⟩ :=
  ⟨.inl rfl, λ h => Cat.noConfusion h, λ h => Cat.noConfusion h⟩

/-- Tensed-auxiliary contraction is inhibited directly before a removal site (264)–(266): the
deleted constituent abuts the copula when the head's QP is AP-internal (274), not when it
modifies the sentence (272). -/
def ContractionLicit (h : Head) : Prop := h.site ≠ .adjective

instance : DecidablePred ContractionLicit := λ _ => by unfold ContractionLicit; infer_instance

/-! ### The rows -/

def particleOf : String → Option Particle
  | "as" => some .as_
  | "too" => some .too
  | "that" => some .that_
  | "so" => some .so
  | "any" => some .any_
  | "no" => some .no_
  | _ => none

def cliticOf : String → Option Clitic
  | "er" => some .er
  | "est" => some .est
  | _ => none

def qOf : String → Option Q
  | "much" => some .much
  | "many" => some .many
  | "little" => some .little
  | "few" => some .few
  | "enough" => some .enough
  | _ => none

def positionOf : String → Option Position
  | "adjective" => some .adjective
  | "noun" => some .noun
  | "quantifier" => some .quantifier
  | "phrase" => some .phrase
  | "measure" => some .measure
  | "term" => some .term
  | _ => none

def catOf : String → Option Cat
  | "qp" => some .qp
  | "ap" => some .ap
  | "np" => some .np
  | _ => none

open English.Adjectives in
def adjectiveOf : String → Option Degree.GradableAdjective
  | "tall" => some tall
  | "short" => some short
  | "high" => some high
  | "long" => some long
  | _ => none

open English.Nouns in
def nounOf : String → Option English.Nouns.Noun
  | "man" => some man
  | "father" => some father
  | "mother" => some mother
  | _ => none

/-- The rows of one of the paper's paradigms. -/
def rows (set : String) : List Datum :=
  Examples.all.filter (·.feature? "set" = some set)

/-- A row's QP. -/
def qpOf (e : Datum) : Option QP :=
  ((e.feature? "q").bind qOf).map λ q =>
    ⟨⟨(e.feature? "particle").bind particleOf, (e.feature? "clitic").bind cliticOf⟩, q⟩

/-- The position of a row's QP. -/
def positionOfRow (e : Datum) : Option Position :=
  (e.feature? "position").bind positionOf

/-- A row's surface form. -/
def surfaceOf (e : Datum) : Option Surface :=
  match e.feature? "surface" with
  | some "analytic" => some .analytic
  | some "deleted" => some .deleted
  | some "synthetic" => some .synthetic
  | _ => none

/-- A row's order of AP and article. -/
def orderOf (e : Datum) : Option Order :=
  match e.feature? "order" with
  | some "prearticle" => some .prearticle
  | some "postarticle" => some .postarticle
  | _ => none

/-- A row's head. -/
def headOf (e : Datum) : Option Head := do
  let cat ← (e.feature? "head").bind catOf
  let site ← (e.feature? "head_site").bind positionOf
  pure ⟨cat, site, ((e.feature? "adjective").bind adjectiveOf).map (·.polarity)⟩

/-- What a row's clause supplies. -/
def supplyOf (e : Datum) : Option Supply := do
  let cat ← (e.feature? "clause").bind catOf
  let site ← (e.feature? "clause_site").bind positionOf
  pure ⟨cat, site⟩

/-- The paper's star. -/
def Starred (e : Datum) : Prop := e.judgment = .ungrammatical

instance : DecidablePred Starred := λ _ => by unfold Starred; infer_instance

/-- The clause's tensed auxiliary is contracted. -/
def Contracted (e : Datum) : Prop := e.feature? "contraction" = some "yes"

instance : DecidablePred Contracted := λ _ => by unfold Contracted; infer_instance

/-- The sentence carries an anomalous implication. -/
def Anomalous (e : Datum) : Prop := e.feature? "anomalous" = some "yes"

instance : DecidablePred Anomalous := λ _ => by unfold Anomalous; infer_instance

-- (4), (5), (107), (117), (119), (224)
theorem det_rows : ∀ e ∈ rows "det", ¬ Starred e ↔ ∃ qp ∈ qpOf e, qp.WellFormed := by
  decide +kernel

-- (1), (19), (84), (85), (275), (279)
theorem surface_rows :
    ∀ e ∈ rows "surface", ¬ Starred e ↔
      ∃ qp ∈ qpOf e, ∃ p ∈ positionOfRow e, ∃ s ∈ surfaceOf e, s.Licit qp p := by
  decide +kernel

-- (111), (116), (125), (127), (217), (218)
theorem shift_rows :
    ∀ e ∈ rows "shift",
      ¬ Starred e ↔ ∃ qp ∈ qpOf e, ∃ o ∈ orderOf e, o.Licit qp := by
  decide +kernel

-- (242), (300), (252), (255), (280), (283)
theorem formation_rows :
    ∀ e ∈ rows "formation", ¬ Starred e ↔
      ∃ h ∈ headOf e, ∃ c ∈ supplyOf e,
        Formation h c ∧ (Contracted e → ContractionLicit h) := by
  decide +kernel

-- (242d), (243), (251)
theorem taller_man_rows :
    ∀ e ∈ rows "formation", Anomalous e ↔
      ∃ h ∈ headOf e, h.cat = .np ∧
        ∃ s ∈ (e.feature? "standard").bind nounOf, ∃ n ∈ (e.feature? "noun").bind nounOf,
          s.referentGender ≠ n.referentGender := by
  decide +kernel

end Bresnan1973
