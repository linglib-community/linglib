module

public import Mathlib.Data.Fintype.Sum
public import Linglib.Discourse.Givenness
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

* The forms Table 1 aligns across languages are `Form.Kind`s, demonstratives by the paper's
  distance terms. A printed form of Tables 2–6 has the kinds it may be: one, except a Spanish
  personal pronoun, which was not coded for stress, and which requires the weaker of the two
  statuses.
* Japanese *kare*, listed under activated, is a stressed pronoun here, since the paper takes
  Japanese to have no unstressed personal pronoun.

## Errata

* The indefinite article is listed among the forms whose required status differs across
  languages, but Table 1 and the paper's own discussion of the article give it the same status,
  type identifiable, in Chinese, English and Spanish; [only the demonstrative determiners
  differ](##required_eq_of_forall_ne_demonstrativeN).
* The share of in-focus referents coded by the most restrictive form is said to range from 71%
  (Russian) to 87% (English), but Japanese, with 87 of 125, [codes a smaller share than
  Russian](##japanese_lt_russian).
* The share of familiar full noun phrases that are bare in Japanese is printed as 59%, but Table 4
  gives 63 of 108, [under 58.5%](##japanese_bare_share).

## References

* [gundel-hedberg-zacharski-1993]
-/

@[expose] public section

namespace GundelHedbergZacharski1993

open Discourse

/-! ### Table 1 -/

/-- The distance a demonstrative marks. -/
inductive Distance where
  | proximal
  | medial
  | distal
  deriving DecidableEq, Repr, Fintype

/-- A kind of referring form: the forms of different languages that Table 1 aligns. -/
inductive Form.Kind where
  /-- A zero pronominal. -/
  | zero
  /-- An unstressed personal pronoun. -/
  | pronoun
  /-- A stressed personal pronoun. -/
  | stressedPronoun
  /-- A demonstrative pronoun. -/
  | demonstrative (d : Distance)
  /-- A demonstrative determiner with a noun. -/
  | demonstrativeN (d : Distance)
  /-- The definite article with a noun. -/
  | definiteN
  /-- Indefinite *this* with a noun. -/
  | indefiniteThisN
  /-- The indefinite article with a noun. -/
  | indefiniteN
  /-- A bare noun. -/
  | bareN
  deriving DecidableEq, Repr, Fintype

/-- Table 1: the status a form of a language requires, the highest it is listed under. -/
def required : Language → Form.Kind → Option GivennessStatus
  | .chinese, k => match k with
    | .zero | .pronoun => some .inFocus
    | .stressedPronoun | .demonstrative .proximal | .demonstrative .distal
    | .demonstrativeN .proximal => some .activated
    | .demonstrativeN .distal => some .uniquelyIdentifiable
    | .indefiniteN | .bareN => some .typeIdentifiable
    | _ => none
  | .english, k => match k with
    | .pronoun => some .inFocus
    | .stressedPronoun | .demonstrative .proximal | .demonstrative .distal
    | .demonstrativeN .proximal => some .activated
    | .demonstrativeN .distal => some .familiar
    | .definiteN => some .uniquelyIdentifiable
    | .indefiniteThisN => some .referential
    | .indefiniteN => some .typeIdentifiable
    | _ => none
  | .japanese, k => match k with
    | .zero => some .inFocus
    | .stressedPronoun | .demonstrative _ | .demonstrativeN .proximal
    | .demonstrativeN .medial => some .activated
    | .demonstrativeN .distal => some .familiar
    | .bareN => some .typeIdentifiable
    | _ => none
  | .russian, k => match k with
    | .zero | .pronoun => some .inFocus
    | .stressedPronoun | .demonstrative .proximal | .demonstrative .distal => some .activated
    | .demonstrativeN .proximal | .demonstrativeN .distal => some .familiar
    | .bareN => some .typeIdentifiable
    | _ => none
  | .spanish, k => match k with
    | .zero | .pronoun => some .inFocus
    | .stressedPronoun | .demonstrative _ | .demonstrativeN .proximal => some .activated
    | .demonstrativeN .medial | .demonstrativeN .distal => some .familiar
    | .definiteN => some .uniquelyIdentifiable
    | .indefiniteN | .bareN => some .typeIdentifiable
    | _ => none

/-- Corresponding forms of the five languages require the same status, unless they are
demonstrative determiners. -/
theorem required_eq_of_forall_ne_demonstrativeN :
    ∀ k : Form.Kind, (∀ d, k ≠ .demonstrativeN d) → ∀ l l' : Language,
      ∀ s ∈ required l k, ∀ s' ∈ required l' k, s = s' := by
  decide +kernel

-- p. 287
theorem required_demonstrativeN_proximal (l : Language) :
    required l (.demonstrativeN .proximal) = some .activated ↔ l ≠ .russian := by
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

/-! ### The corpus -/

/-- The kinds a printed form may be: one, except a Spanish personal pronoun, whose stress the
coding left open. -/
def Form.kinds : Form → List Form.Kind
  | .zero => [.zero]
  | .bare => [.bareN]
  | .ta | .it | .ono => [.pronoun]
  | .stressedHe | .kare | .stressedOno => [.stressedPronoun]
  | .elSubj | .elNonsubj => [.pronoun, .stressedPronoun]
  | .zhe | .thisPronoun | .kore | .eto | .este => [.demonstrative .proximal]
  | .sore | .ese => [.demonstrative .medial]
  | .nei | .thatPronoun | .are | .tot | .aquel => [.demonstrative .distal]
  | .zheN | .thisN | .konoN | .etoN | .esteN => [.demonstrativeN .proximal]
  | .sonoN | .eseN => [.demonstrativeN .medial]
  | .neiN | .thatN | .anoN | .toN | .aquelN => [.demonstrativeN .distal]
  | .theN | .elN => [.definiteN]
  | .indefiniteThisN => [.indefiniteThisN]
  | .yiN | .aN | .unN => [.indefiniteN]

/-- The status a column records. -/
def Status.toGivennessStatus : Status → GivennessStatus
  | .inFocus => .inFocus
  | .activated => .activated
  | .familiar => .familiar
  | .unique => .uniquelyIdentifiable
  | .referential => .referential
  | .typeIdentifiable => .typeIdentifiable

/-- The status a printed form requires in a language, the weakest its kinds require. -/
def requiredOf (l : Language) (f : Form) : Option GivennessStatus :=
  (f.kinds.filterMap (required l)).min?

/-- The referent of a cell meets the status its form requires. -/
def Cell.Meets (c : Cell) : Prop :=
  ∀ r ∈ requiredOf c.language c.form, r ≤ c.status.toGivennessStatus

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
        Attested p.1 p.2 s ↔ ∀ r ∈ requiredOf p.1 p.2, r ≤ s.toGivennessStatus := by
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
  tokens fun c ↦ c.language = l ∧ c.form = f ∧ .familiar ≤ c.status.toGivennessStatus

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
  tokens fun c ↦ c.language = l ∧ c.form.Full ∧ .familiar ≤ c.status.toGivennessStatus

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
