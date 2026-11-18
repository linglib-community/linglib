module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.Romance.Spanish.Determiners
public import Linglib.Fragments.Romance.Spanish.Pronouns
public import Linglib.Fragments.Slavic.Russian.Determiners
public import Linglib.Fragments.Slavic.Russian.Pronouns
public import Linglib.Data.Statistics.GundelHedbergZacharski1993

/-!
# Gundel, Hedberg and Zacharski (1993): Cognitive status and the form of referring expressions

A referring form signals a cognitive status of its referent, and the six statuses of the Givenness
Hierarchy are nested, so a form fits any referent at or above its status. Across Chinese, English,
Japanese, Russian and Spanish, corresponding forms [require the same status, except the
demonstrative determiners](##required_eq_of_forall_ne_demonstrativeN). In discourse the forms [meet
their necessary conditions](##meets_of_spanish) and [occur at every status that meets
them](##attested_iff), and the maxim of Quantity governs which: [an in-focus referent mostly takes
the most restrictive form](##inFocus_mostFrequent), [a familiar full noun phrase the
least](##familiar_mostFrequent).

## Implementation notes

* The forms Table 1 aligns across languages are `Form.Kind`s. A printed form of Tables 2–6 has
  the kinds it may be: one, except a Spanish personal pronoun, which was not coded for stress, and
  which requires the weaker of the two statuses.
* A demonstrative's deixis is the participant sets of its anchors, read off its fragment entry
  (Chinese *nèi* is *nà*, and the masculine singular stands for each paradigm). Spanish *ese*,
  usable at any distance from the speaker, covers every participant set without the speaker, and
  Japanese *so-* the listener's alone, its further reading slightly removed from both
  participants unrecorded. Harbour takes Modern Japanese *ko–so–a* to have become distance-based,
  while Terenghi lists it as person-oriented and treats Spanish *ese* as also denoting
  intermediate distance from the speaker.
* Japanese *kare*, listed under activated, is a stressed pronoun here, since the paper takes
  Japanese to have no unstressed personal pronoun.

## References

* [gundel-hedberg-zacharski-1993]
* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

namespace GundelHedbergZacharski1993

open SpeechAct

/-! ### The Givenness Hierarchy -/

/-- A cognitive status is a tier of the Givenness Hierarchy, a condition on a referent that a
referring form signals. A referent with a status has every lower one. -/
inductive CognitiveStatus where
  /-- The referent is at the current center of attention, as zero and unstressed pronouns
  require. -/
  | inFocus
  /-- The referent is represented in current short-term memory (*that*, *this*, *this N*). -/
  | activated
  /-- The addressee already has a representation of the referent in memory, long-term or
  short-term, and so can uniquely identify it (*that N*). -/
  | familiar
  /-- The addressee can identify the speaker's intended referent from the nominal alone
  (*the N*). -/
  | uniquelyIdentifiable
  /-- The speaker intends to refer to a particular object (indefinite *this N*). -/
  | referential
  /-- The addressee can access a representation of the type of object described (*a N*). -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The rank of a status, higher for the more restrictive. -/
def CognitiveStatus.rank : CognitiveStatus → ℕ
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

-- p. 276: each status entails every lower one.
instance : LinearOrder CognitiveStatus := LinearOrder.lift' CognitiveStatus.rank (by decide)

/-! ### Table 1 -/

/-- A kind of referring form: the forms of different languages that Table 1 aligns. -/
inductive Form.Kind where
  /-- A zero pronominal. -/
  | zero
  /-- An unstressed personal pronoun. -/
  | pronoun
  /-- A stressed personal pronoun. -/
  | stressedPronoun
  /-- A demonstrative pronoun, with the participant sets of its anchors. -/
  | demonstrative (deixis : Finset (Finset Role))
  /-- A demonstrative determiner with a noun, with the participant sets of its anchors. -/
  | demonstrativeN (deixis : Finset (Finset Role))
  /-- The definite article with a noun. -/
  | definiteN
  /-- Indefinite *this* with a noun. -/
  | indefiniteThisN
  /-- The indefinite article with a noun. -/
  | indefiniteN
  /-- A bare noun. -/
  | bareN
  deriving DecidableEq, Fintype

/-- Table 1: the forms of a language, each with the highest status it is listed under. -/
def table1 : Language → List (Form.Kind × CognitiveStatus)
  | .chinese =>
    [(.zero, .inFocus), (.pronoun, .inFocus), (.stressedPronoun, .activated),
     (.demonstrative Mandarin.Determiners.zhe.deixis, .activated),
     (.demonstrative Mandarin.Determiners.na.deixis, .activated),
     (.demonstrativeN Mandarin.Determiners.zhe.deixis, .activated),
     (.demonstrativeN Mandarin.Determiners.na.deixis, .uniquelyIdentifiable),
     (.indefiniteN, .typeIdentifiable), (.bareN, .typeIdentifiable)]
  | .english =>
    [(.pronoun, .inFocus), (.stressedPronoun, .activated),
     (.demonstrative English.Pronouns.this_.deixis, .activated),
     (.demonstrative English.Pronouns.that_.deixis, .activated),
     (.demonstrativeN English.Determiners.this.deixis, .activated),
     (.demonstrativeN English.Determiners.that.deixis, .familiar),
     (.definiteN, .uniquelyIdentifiable), (.indefiniteThisN, .referential),
     (.indefiniteN, .typeIdentifiable)]
  | .japanese =>
    [(.zero, .inFocus), (.stressedPronoun, .activated),
     (.demonstrative Japanese.Pronouns.kore.deixis, .activated),
     (.demonstrative Japanese.Pronouns.sore.deixis, .activated),
     (.demonstrative Japanese.Pronouns.are.deixis, .activated),
     (.demonstrativeN Japanese.Determiners.kono.deixis, .activated),
     (.demonstrativeN Japanese.Determiners.sono.deixis, .activated),
     (.demonstrativeN Japanese.Determiners.ano.deixis, .familiar), (.bareN, .typeIdentifiable)]
  | .russian =>
    [(.zero, .inFocus), (.pronoun, .inFocus), (.stressedPronoun, .activated),
     (.demonstrative Russian.Pronouns.ètot.deixis, .activated),
     (.demonstrative Russian.Pronouns.tot.deixis, .activated),
     (.demonstrativeN Russian.Determiners.ètot.deixis, .familiar),
     (.demonstrativeN Russian.Determiners.tot.deixis, .familiar), (.bareN, .typeIdentifiable)]
  | .spanish =>
    [(.zero, .inFocus), (.pronoun, .inFocus), (.stressedPronoun, .activated),
     (.demonstrative Spanish.Pronouns.este.deixis, .activated),
     (.demonstrative Spanish.Pronouns.ese.deixis, .activated),
     (.demonstrative Spanish.Pronouns.aquel.deixis, .activated),
     (.demonstrativeN Spanish.Determiners.este.deixis, .activated),
     (.demonstrativeN Spanish.Determiners.ese.deixis, .familiar),
     (.demonstrativeN Spanish.Determiners.aquel.deixis, .familiar),
     (.definiteN, .uniquelyIdentifiable), (.indefiniteN, .typeIdentifiable),
     (.bareN, .typeIdentifiable)]

/-- The status a form of a language requires, if Table 1 lists it. -/
def required (l : Language) (k : Form.Kind) : Option CognitiveStatus := (table1 l).lookup k

/-- Corresponding forms of the five languages require the same status, unless they are
demonstrative determiners. -/
theorem required_eq_of_forall_ne_demonstrativeN :
    ∀ k : Form.Kind, (∀ d, k ≠ .demonstrativeN d) → ∀ l l' : Language,
      ∀ s ∈ required l k, ∀ s' ∈ required l' k, s = s' := by
  decide +kernel

-- p. 287
theorem required_demonstrativeN_proximal (l : Language) :
    required l (.demonstrativeN Person.first.participantSets) = some .activated ↔
      l ≠ .russian := by
  revert l
  decide +kernel

-- p. 285
theorem activated_le_of_pronominal :
    ∀ l k, k = .zero ∨ k = .pronoun ∨ k = .stressedPronoun ∨ (∃ d, k = .demonstrative d) →
      ∀ s ∈ required l k, .activated ≤ s := by
  decide +kernel

-- p. 285
theorem required_eq_inFocus :
    ∀ l k, required l k = some .inFocus → k = .zero ∨ k = .pronoun := by
  decide +kernel

-- fn. 4: a noun phrase is definite when its form requires a uniquely identifiable referent, so
-- every English form is definite but *a N* and indefinite *this N*, as the fragment marks *the*
-- and *a*.
theorem uniquelyIdentifiable_le_iff_english :
    (∀ k, ∀ s ∈ required .english k,
      .uniquelyIdentifiable ≤ s ↔ k ≠ .indefiniteN ∧ k ≠ .indefiniteThisN) ∧
    (∀ s ∈ required .english .definiteN,
      .uniquelyIdentifiable ≤ s ↔ .definite ∈ English.Determiners.the.definiteness) ∧
    ∀ s ∈ required .english .indefiniteN,
      .uniquelyIdentifiable ≤ s ↔ .definite ∈ English.Determiners.a.definiteness := by
  decide +kernel

/-! ### The corpus -/

/-- The kinds a printed form may be: one, except a Spanish personal pronoun, whose stress the
coding left open. -/
def Form.kinds : Form → List Form.Kind
  | .zero => [.zero]
  | .bare => [.bareN]
  | .ta | .it | .ono => [.pronoun]
  | .stressedHe | .kare | .stressedOno => [.stressedPronoun]
  | .elSubj | .elNonsubj => [.pronoun, .stressedPronoun]
  | .zhe => [.demonstrative Mandarin.Determiners.zhe.deixis]
  | .nei => [.demonstrative Mandarin.Determiners.na.deixis]
  | .zheN => [.demonstrativeN Mandarin.Determiners.zhe.deixis]
  | .neiN => [.demonstrativeN Mandarin.Determiners.na.deixis]
  | .thisPronoun => [.demonstrative English.Pronouns.this_.deixis]
  | .thatPronoun => [.demonstrative English.Pronouns.that_.deixis]
  | .thisN => [.demonstrativeN English.Determiners.this.deixis]
  | .thatN => [.demonstrativeN English.Determiners.that.deixis]
  | .kore => [.demonstrative Japanese.Pronouns.kore.deixis]
  | .sore => [.demonstrative Japanese.Pronouns.sore.deixis]
  | .are => [.demonstrative Japanese.Pronouns.are.deixis]
  | .konoN => [.demonstrativeN Japanese.Determiners.kono.deixis]
  | .sonoN => [.demonstrativeN Japanese.Determiners.sono.deixis]
  | .anoN => [.demonstrativeN Japanese.Determiners.ano.deixis]
  | .eto => [.demonstrative Russian.Pronouns.ètot.deixis]
  | .tot => [.demonstrative Russian.Pronouns.tot.deixis]
  | .etoN => [.demonstrativeN Russian.Determiners.ètot.deixis]
  | .toN => [.demonstrativeN Russian.Determiners.tot.deixis]
  | .este => [.demonstrative Spanish.Pronouns.este.deixis]
  | .ese => [.demonstrative Spanish.Pronouns.ese.deixis]
  | .aquel => [.demonstrative Spanish.Pronouns.aquel.deixis]
  | .esteN => [.demonstrativeN Spanish.Determiners.este.deixis]
  | .eseN => [.demonstrativeN Spanish.Determiners.ese.deixis]
  | .aquelN => [.demonstrativeN Spanish.Determiners.aquel.deixis]
  | .theN | .elN => [.definiteN]
  | .indefiniteThisN => [.indefiniteThisN]
  | .yiN | .aN | .unN => [.indefiniteN]

/-- The status a column records. -/
def Status.toCognitiveStatus : Status → CognitiveStatus
  | .inFocus => .inFocus
  | .activated => .activated
  | .familiar => .familiar
  | .unique => .uniquelyIdentifiable
  | .referential => .referential
  | .typeIdentifiable => .typeIdentifiable

/-- The status a printed form requires in a language, the weakest its kinds require. -/
def requiredOf (l : Language) (f : Form) : Option CognitiveStatus :=
  (f.kinds.filterMap (required l)).min?

/-- The referent of a cell meets the status its form requires. -/
def Cell.Meets (c : Cell) : Prop :=
  ∀ r ∈ requiredOf c.language c.form, r ≤ c.status.toCognitiveStatus

instance : DecidablePred Cell.Meets := fun c ↦
  inferInstanceAs (Decidable (∀ r ∈ requiredOf c.language c.form, _))

/-- Every Spanish form met its necessary condition. -/
theorem meets_of_spanish : ∀ c ∈ distribution, c.language = .spanish → c.Meets := by
  decide +kernel

-- (40)
theorem english_not_meets :
    distribution.filter (fun c ↦ c.language = .english ∧ ¬ c.Meets) =
      [⟨.english, .it, .activated, 1⟩] := by
  decide +kernel

/-- A form occurs in a language with a referent whose highest status is `s`. -/
def Attested (l : Language) (f : Form) (s : Status) : Prop :=
  ∃ c ∈ distribution, c.language = l ∧ c.form = f ∧ c.status = s

instance (l : Language) (f : Form) (s : Status) : Decidable (Attested l f s) :=
  inferInstanceAs (Decidable (∃ c ∈ distribution, _))

/-- *the N* and *that* in English and a bare noun and *èto N* in Russian occur at every status
that meets their requirement, and only there. -/
theorem attested_iff :
    ∀ p ∈ [(Language.english, Form.theN), (.english, .thatPronoun), (.russian, .bare),
      (.russian, .etoN)], ∀ s : Status,
        Attested p.1 p.2 s ↔ ∀ r ∈ requiredOf p.1 p.2, r ≤ s.toCognitiveStatus := by
  decide +kernel

/-- The tokens of the cells satisfying `p`. -/
def tokens (p : Cell → Prop) [DecidablePred p] : ℕ :=
  ((distribution.filter p).map (·.tokens)).sum

/-- In every language the most frequent form for an in-focus referent requires it to be in
focus. -/
theorem inFocus_mostFrequent (l : Language) :
    ∃ c ∈ distribution, c.language = l ∧ c.status = .inFocus ∧
      requiredOf l c.form = some .inFocus ∧
        ∀ c' ∈ distribution, c'.language = l → c'.status = .inFocus → c'.tokens ≤ c.tokens := by
  revert l
  decide +kernel

/-- A form is the most restrictive, a zero or an unstressed pronoun. -/
def Form.Restrictive (f : Form) : Prop := .zero ∈ f.kinds ∨ .pronoun ∈ f.kinds

instance : DecidablePred Form.Restrictive := fun f ↦
  inferInstanceAs (Decidable (.zero ∈ f.kinds ∨ .pronoun ∈ f.kinds))

-- p. 297
theorem japanese_lt_russian :
    tokens (fun c ↦ c.language = .japanese ∧ c.status = .inFocus ∧ c.form.Restrictive) *
        tokens (fun c ↦ c.language = .russian ∧ c.status = .inFocus) <
      tokens (fun c ↦ c.language = .russian ∧ c.status = .inFocus ∧ c.form.Restrictive) *
        tokens (fun c ↦ c.language = .japanese ∧ c.status = .inFocus) := by
  decide +kernel

/-- A form is a full noun phrase. -/
def Form.Full (f : Form) : Prop :=
  ∀ k ∈ f.kinds, k ∉ [.zero, .pronoun, .stressedPronoun] ∧ ∀ d, k ≠ .demonstrative d

instance : DecidablePred Form.Full := fun f ↦
  inferInstanceAs (Decidable (∀ k ∈ f.kinds, _))

/-- The tokens of a form in a language whose referent is at least familiar. -/
def familiarTokens (l : Language) (f : Form) : ℕ :=
  tokens fun c ↦ c.language = l ∧ c.form = f ∧ .familiar ≤ c.status.toCognitiveStatus

/-- In every language the most frequent full noun phrase for a familiar referent is the least
restrictive one with a definite reading, the definite article where the language has one and a
bare noun where it does not. -/
theorem familiar_mostFrequent (l : Language) :
    ∃ f, (f.kinds = [.definiteN] ∨ f.kinds = [.bareN]) ∧
      ∀ g : Form, g.Full → familiarTokens l g ≤ familiarTokens l f := by
  revert l
  decide +kernel

/-- The tokens of full noun phrases in a language whose referent is at least familiar. -/
def fullFamiliarTokens (l : Language) : ℕ :=
  tokens fun c ↦ c.language = l ∧ c.form.Full ∧ .familiar ≤ c.status.toCognitiveStatus

-- p. 299
theorem familiar_share_gt :
    ∀ l ∈ [Language.english, .spanish, .russian], ∃ f : Form,
      (f.kinds = [.definiteN] ∨ f.kinds = [.bareN]) ∧
        85 * fullFamiliarTokens l < 100 * familiarTokens l f := by
  decide +kernel

-- p. 300, printed 59%
theorem japanese_bare_share :
    200 * familiarTokens .japanese .bare < 117 * fullFamiliarTokens .japanese := by
  decide +kernel

end GundelHedbergZacharski1993
