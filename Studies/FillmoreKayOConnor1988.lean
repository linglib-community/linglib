module

public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.ConstructionGrammar.Basic
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Data.Examples.FillmoreKayOConnor1988
public import Linglib.Data.Examples.Readers

/-!
# Fillmore, Kay & O'Connor (1988): Regularity and idiomaticity in grammatical constructions

This file formalizes Fillmore, Kay and O'Connor's semantics of the *let alone*
construction. A *let alone* sentence F ⟨X A Y let alone B⟩ (20) asserts the two
propositions F′(X A Y) and F′(X B Y) (24) and presupposes a scalar model in which they are
distinct points, the full clause the stronger (§2.3). The Appendix defines the model in five
steps: an argument space, the product of at least two linearly ordered dimensions (A1), with its
product order as "lower than" (A2, `lower_iff`); a propositional function `P` such that, for
distinct points, `P b` entails `P a` exactly when `a` is lower than `b` (A3, `IsScalarModel`);
the same for the negated propositions (A4, `IsScalarModel.not_le_not_iff`); and informativeness
as one-way entailment (A5), the strict order on propositions, which A3 turns into the order on
points (`IsScalarModel.lt_iff`, `IsScalarModel.not_lt_not_iff`). The states of affairs of Tables
1–4, where truth propagates from the one-corner and falsity from the zero-corner, are the lower
sets of the argument space, and every lower-set state space is a scalar model
(`isScalarModel_mem`). The semantic conditions of §2.3.2 — one model, one polarity, the full
clause stronger (`Felicitous`) — thus reduce to an order on the foci: under negation A is lower
than B, under positive polarity higher (`felicitous_negative_iff`, `felicitous_positive_iff`).
Hence a fragment naming the lowest point of its scale is anomalous, (107) against (106)
(`not_felicitous_of_isBot`), and exchanging the foci of one dimension between points that
differ on two leaves them incomparable, (122) against (121) (`swap_incomparable`). The ranks of
(21), (106)–(107) and (130)–(132), the linguists and languages of Tables 1–4 and (109)–(112),
and the four dimensions of (121)–(122) instantiate the theory; the paper's judgments are the
rows of `Data/Examples/FillmoreKayOConnor1988.json`, and `rankRows_predicted` and
`focusRows_predicted` check them against `Felicitous` and the order in which the conjunction
presents the stronger clause (p. 533).

The construction itself is a formal idiom, a lexically open one in the sense of §1.1.3
(`letAloneConstruction_isFormalIdiom`). Its syntax (§2.2) — a
coordination that neither topicalizes nor clefts as a unit (31)–(34), admits no VP ellipsis
because the INFL-complex belongs to the trigger F (39)–(41), and is licensed in the affective
environments of Klima (62)–(70) yet attested under positive polarity when the fragment
denies the context proposition (71)–(73) — and its pragmatics (§2.4), the fragment answering
Relevance and the full clause Quantity, are the rows' comments and the docstrings below. Scales
are pragmatic, in the tradition of Fauconnier rather than the semantic scales of Horn and
Gazdar, and a scalar model needs a second dimension to bear its degrees (fn. 16, after
Cresswell).

## Implementation notes

* `IsScalarModel` is stated over any partial order; the product order of (A1)–(A2) enters
  through `lower_iff`, and the stipulation of at least two dimensions (fn. 16) is not part of the
  predicate. The one-dimensional rank chain is therefore treated as the slice of the persons ×
  ranks model that fn. 16 envisages, and a slice of a scalar model is a scalar model
  (`IsScalarModel.slice`).
* A state of affairs is a `LowerSet` of the argument space and the propositional function is
  membership: "he made colonel" holds in a career exactly when colonel is among the ranks
  reached. The paper's Tables 2 and 4 draw four such states; `table2c` is the one that
  separates *Brilliant can read English* from *Brilliant can read Greek*.
* `force` renders F′ as negation or identity. The paper leaves open why only the negative part
  of *barely* reaches the fragment (§2.3.3, (118)–(119)); the *barely* rows are judgment data
  without a model, as are the constituency and licensing rows of §2.2.
* The ranks are the three the paper names; *a commissioned officer* in (106)–(107) is "made the
  lowest commissioned rank", since in a lower-set state holding some rank is holding the lowest.
* The (104)/(105) contrast rests on the two-dimension stipulation and on a lottery model the
  paper describes but does not build; (104) is a row without a model.

## TODO

- The §1 typology of idioms (decoding and encoding, grammatical and extragrammatical, and §1.2's
  familiarity of pieces and of arrangement), once rows classify idioms by it. Its fourth cell,
  unfamiliar pieces familiarly arranged, is excluded by the argument of §1.2.1 that unique pieces
  have no standard principles of arrangement, which the typology should derive rather than omit.

## References

* [fillmore-kay-oconnor-1988]
* [klima-1964]
* [fauconnier-1975]
* [horn-1972]
* [gazdar-1979]
* [cresswell-1976]
-/

@[expose] public section

namespace FillmoreKayOConnor1988

open ConstructionGrammar

/-! ### Scalar models (Appendix) -/

section ScalarModel

variable {D S : Type*} [PartialOrder D] {P : D → S → Prop} {a b : D}

theorem lower_iff {ι : Type*} {δ : ι → Type*} [∀ i, LinearOrder (δ i)] (a b : ∀ i, δ i) :
    a < b ↔ (∀ i, a i ≤ b i) ∧ ∃ i, a i < b i := by
  rw [Pi.lt_def, Pi.le_def]

/-- By (A3), `⟨S, T, Dˣ, P⟩` is a scalar model iff, for distinct points `a` and `b`, `P b` entails
`P a` just in case `a` is lower than `b`. Propositions are ordered by entailment, the pointwise
order on `S → Prop`. -/
def IsScalarModel (P : D → S → Prop) : Prop := ∀ ⦃a b : D⦄, a ≠ b → (P b ≤ P a ↔ a < b)

theorem IsScalarModel.not_le_not_iff (h : IsScalarModel P) (hab : a ≠ b) :
    (¬ P a ·) ≤ (¬ P b ·) ↔ a < b := by
  rw [← h hab, Pi.le_def, Pi.le_def]
  exact forall_congr' fun _ ↦ not_imp_not

theorem IsScalarModel.lt_iff (h : IsScalarModel P) : P b < P a ↔ a < b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · rw [lt_iff_le_not_ge, h hab, h hab.symm]
    exact and_iff_left_of_imp lt_asymm

theorem IsScalarModel.not_lt_not_iff (h : IsScalarModel P) :
    (¬ P a ·) < (¬ P b ·) ↔ a < b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · rw [lt_iff_le_not_ge, h.not_le_not_iff hab, h.not_le_not_iff hab.symm]
    exact and_iff_left_of_imp lt_asymm

/-- Fixing a coordinate of a scalar model leaves a scalar model, so the bearers of a degree
(fn. 16) may be held fixed. -/
theorem IsScalarModel.slice {E : Type*} [PartialOrder E] {P : D × E → S → Prop}
    (h : IsScalarModel P) (d : D) : IsScalarModel fun e ↦ P (d, e) := fun _ _ hne ↦
  (h fun h' ↦ hne (Prod.mk.inj h').2).trans Prod.mk_lt_mk_iff_right

/-- With membership as propositional function, the lower sets of an argument space form a scalar
model (Tables 1–4). -/
theorem isScalarModel_mem : IsScalarModel fun (d : D) (s : LowerSet D) ↦ d ∈ s := fun _ b hab ↦
  ⟨fun hle ↦ lt_of_le_of_ne
      (LowerSet.mem_Iic_iff.1 (hle (LowerSet.Iic b) (LowerSet.mem_Iic_iff.2 le_rfl))) hab,
    fun hlt s hb ↦ s.lower hlt.le hb⟩

/-! ### The semantic conditions on *let alone* sentences (§2.3.2) -/

/-- F′ of (24), the semantic operator derived from the trigger F, is negation under negative
polarity and identity under positive. -/
def force : Polarity → (S → Prop) → S → Prop
  | .negative, p => (¬ p ·)
  | .positive, p => p

/-- The conditions of §2.3.2 on a *let alone* sentence with foci `a` and `b` are that F′(X A Y) and
F′(X B Y) are propositions of one scalar model and one polarity, and that the full clause F′(X A Y)
is the more informative (A5). -/
def Felicitous (P : D → S → Prop) (pol : Polarity) (a b : D) : Prop :=
  force pol (P a) < force pol (P b)

/-- Under negation the full clause is the stronger exactly when A is the lower point, as in *he
didn't make colonel, let alone general*. -/
theorem felicitous_negative_iff (h : IsScalarModel P) : Felicitous P .negative a b ↔ a < b :=
  h.not_lt_not_iff

/-- Under positive polarity, the full clause is the stronger iff A is the higher point (71). -/
theorem felicitous_positive_iff (h : IsScalarModel P) : Felicitous P .positive a b ↔ b < a :=
  h.lt_iff

/-- A fragment naming the lowest point of the scale is anomalous (107). -/
theorem not_felicitous_of_isBot (h : IsScalarModel P) (hb : IsBot b) :
    ¬ Felicitous P .negative a b :=
  fun hf ↦ not_lt_of_ge (hb a) ((felicitous_negative_iff h).1 hf)

/-- Exchanging the foci of one dimension between two points that differ on two dimensions leaves
the points incomparable, so neither clause is the stronger (122). -/
theorem swap_incomparable {ι : Type*} [DecidableEq ι] {δ : ι → Type*} [∀ i, Preorder (δ i)]
    {a b : ∀ i, δ i} {j k : ι} (hjk : j ≠ k) (hj : a j < b j) (hk : a k < b k) :
    ¬ Function.update a j (b j) < Function.update b j (a j) ∧
      ¬ Function.update b j (a j) < Function.update a j (b j) :=
  ⟨fun h ↦ hj.not_ge (by simpa using h.le j), fun h ↦ hk.not_ge (by simpa [hjk.symm] using h.le k)⟩

end ScalarModel

/-! ### The construction (§2.1) -/

/-- In the *let alone* construction F ⟨X A Y let alone B⟩ (20a) the paired foci A and B flank
*let alone*; the shared material X and Y and the trigger F are elided from the typed form. -/
def letAloneConstruction : Construction Unit :=
  { form := [{ filler := .open_ .NOUN }, { filler := .fixed "let" }, { filler := .fixed "alone" },
      { filler := .open_ .NOUN }]
    meaning := ()
    pragmaticPoint := true }

/-- *Let alone* is a formal idiom, lexically open in form (§2.1). -/
theorem letAloneConstruction_isFormalIdiom : letAloneConstruction.IsFormalIdiom := by decide

/-- The incredulity type *Him be a doctor?* (14h), §1.1.4's formal idiom that exists "in the
service of specific pragmatic or rhetorical purposes": a non-nominative subject with a bare-stem
predicate. -/
def incredulityResponse : Construction Unit :=
  { form := [{ filler := .open_ .PRON, gf := some .subj },
      { filler := .phrasal }]
    meaning := ()
    pragmaticPoint := true }

/-! ### The conjunction family (p. 533) -/

/-- The fragment-taking conjunctions that presuppose a scale relating their conjuncts: *let alone*,
*much less* and *not to mention* present the stronger clause first, *in fact* and *if not* present
it second (130)–(132). -/
inductive Conjunction where
  | letAlone
  | muchLess
  | notToMention
  | inFact
  | ifNot
  deriving DecidableEq, Repr

/-- Whether the conjunction presents the stronger clause first. -/
def Conjunction.StrongerFirst : Conjunction → Prop
  | .letAlone | .muchLess | .notToMention => True
  | .inFact | .ifNot => False

instance : DecidablePred Conjunction.StrongerFirst := fun c ↦ by
  unfold Conjunction.StrongerFirst; split <;> infer_instance

/-! ### The paper's judgments -/

section Rows

variable {D : Type} {S : Type*} [PartialOrder D]

/-- A sentence of the family with its conjunction, the polarity of its trigger, the points of its
two foci and the paper's judgment. -/
structure Row (D : Type) where
  conj : Conjunction
  pol : Polarity
  a : D
  b : D
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The point of the clause the conjunction presents as the stronger. -/
def Row.stronger (r : Row D) : D := if r.conj.StrongerFirst then r.a else r.b

/-- The point of the clause the conjunction presents as the weaker. -/
def Row.weaker (r : Row D) : D := if r.conj.StrongerFirst then r.b else r.a

/-- The conditions of §2.3.2 on the row, the conjunction fixing which clause must be the
stronger. -/
def Row.Predicted (P : D → S → Prop) (r : Row D) : Prop := Felicitous P r.pol r.stronger r.weaker

/-- The conditions order the foci so that the stronger clause's point is the lower under negation
and the higher under positive polarity. -/
def Row.FociOrdered (r : Row D) : Prop :=
  match r.pol with
  | .negative => r.stronger < r.weaker
  | .positive => r.weaker < r.stronger

instance [DecidableLT D] (r : Row D) : Decidable r.FociOrdered := by
  unfold Row.FociOrdered; split <;> infer_instance

theorem Row.predicted_iff {P : D → S → Prop} (h : IsScalarModel P) :
    ∀ r : Row D, r.Predicted P ↔ r.FociOrdered
  | ⟨_, .negative, _, _, _⟩ => felicitous_negative_iff h
  | ⟨_, .positive, _, _, _⟩ => felicitous_positive_iff h

def conjunctionTable : List (String × Conjunction) :=
  [("letAlone", .letAlone), ("muchLess", .muchLess), ("notToMention", .notToMention),
    ("inFact", .inFact), ("ifNot", .ifNot)]

def polarityTable : List (String × Polarity) := [("negative", .negative), ("positive", .positive)]

/-- A row from an example, given a reading of its foci as points. -/
def Row.ofDatum (foci? : Datum → Option (D × D)) (ex : Datum) :
    Option (Row D) := do
  let conj ← ex.parse? "conjunction" conjunctionTable
  let pol ← ex.parse? "polarity" polarityTable
  let (a, b) ← foci? ex
  pure ⟨conj, pol, a, b, ex.judgment⟩

end Rows

/-! ### Military rank: (21), (106)–(107), (130)–(132) -/

/-- The commissioned ranks the paper names, second lieutenant "the lowest commissioned rank"
(§2.3.2). -/
inductive Rank where
  | secondLieutenant
  | colonel
  | general
  deriving DecidableEq, Repr, Fintype

def Rank.idx : Rank → ℕ
  | .secondLieutenant => 0
  | .colonel => 1
  | .general => 2

instance : LinearOrder Rank := .lift' Rank.idx (by decide)

/-- *He made rank `r`* holds in a career, the lower set of the ranks reached, when `r` is in it. -/
abbrev MadeRank : Rank → LowerSet Rank → Prop := (· ∈ ·)

theorem isBot_secondLieutenant : IsBot Rank.secondLieutenant := fun _ ↦ Nat.zero_le _

-- (107)
theorem anomaly_107 : ¬ Felicitous MadeRank .negative .secondLieutenant .secondLieutenant :=
  not_felicitous_of_isBot isScalarModel_mem isBot_secondLieutenant

def rankTable : List (String × Rank) :=
  [("secondLieutenant", .secondLieutenant), ("colonel", .colonel), ("general", .general)]

def rankFoci? (ex : Datum) : Option (Rank × Rank) := do
  let a ← ex.parse? "a" rankTable
  let b ← ex.parse? "b" rankTable
  pure (a, b)

def rankRows : List (Row Rank) := Examples.all.filterMap (Row.ofDatum rankFoci?)

/-- Among (21), (106)–(107) and (130)–(132), the acceptable sentences are exactly those meeting the
conditions of §2.3.2 with the conjunction's ordering of the stronger clause. -/
theorem rankRows_predicted : ∀ r ∈ rankRows, (r.judgment = .acceptable ↔ r.Predicted MadeRank) := by
  simp only [Row.predicted_iff isScalarModel_mem]
  decide

/-! ### Linguists and languages: Tables 1–4, (109)–(112) -/

/-- The professors of Indo-European linguistics in order of erudition: "Apotheosis knows every
language that Brilliant knows, Brilliant knows every language that Competent knows, and Competent
knows every language that Dimm knows". -/
inductive Linguist where
  | apotheosis
  | brilliant
  | competent
  | dimm
  deriving DecidableEq, Repr, Fintype

def Linguist.idx : Linguist → ℕ
  | .apotheosis => 0
  | .brilliant => 1
  | .competent => 2
  | .dimm => 3

instance : LinearOrder Linguist := .lift' Linguist.idx (by decide)

/-- The languages are ordered by accessibility, so that "anyone who knows Hittite knows Greek,
anyone who knows Greek knows French, and anyone who knows French knows English". -/
inductive Lang where
  | english
  | french
  | greek
  | hittite
  deriving DecidableEq, Repr, Fintype

def Lang.idx : Lang → ℕ
  | .english => 0
  | .french => 1
  | .greek => 2
  | .hittite => 3

instance : LinearOrder Lang := .lift' Lang.idx (by decide)

instance : DecidableLT (Linguist × Lang) := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ ¬ _))

/-- *Professor `p.1` can read language `p.2`* in a state of affairs. -/
abbrev CanRead : Linguist × Lang → LowerSet (Linguist × Lang) → Prop := (· ∈ ·)

/-- In Table 2c, Apotheosis reads English and French, and Brilliant reads English. -/
def table2c : LowerSet (Linguist × Lang) :=
  .Iic (.apotheosis, .french) ⊔ .Iic (.brilliant, .english)

-- Table 2c
theorem brilliant_english_greek :
    CanRead (.brilliant, .english) table2c ∧ ¬ CanRead (.brilliant, .greek) table2c ∧
      CanRead (.brilliant, .greek) < CanRead (.brilliant, .english) :=
  ⟨LowerSet.mem_sup_iff.2 (.inr (LowerSet.mem_Iic_iff.2 le_rfl)),
    fun h ↦ by
      rcases LowerSet.mem_sup_iff.1 h with h | h <;>
        exact absurd (LowerSet.mem_Iic_iff.1 h) (by decide),
    isScalarModel_mem.lt_iff.2 (by decide)⟩

-- Table 1
theorem corners (p : Linguist × Lang) :
    CanRead (.dimm, .hittite) ≤ CanRead p ∧
      (¬ CanRead (.apotheosis, .english) ·) ≤ (¬ CanRead p ·) :=
  have h₁ : p ≤ (.dimm, .hittite) := by revert p; decide
  have h₀ : (.apotheosis, .english) ≤ p := by revert p; decide
  ⟨fun s h ↦ s.lower h₁ h, fun s h hp ↦ h (s.lower h₀ hp)⟩

-- (109), (112)
theorem informativeness_109_112 :
    CanRead (.brilliant, .hittite) < CanRead (.brilliant, .french) ∧
      (¬ CanRead (.brilliant, .french) ·) < (¬ CanRead (.brilliant, .hittite) ·) ∧
      CanRead (.competent, .hittite) < CanRead (.brilliant, .french) ∧
      (¬ CanRead (.brilliant, .french) ·) < (¬ CanRead (.competent, .french) ·) :=
  ⟨isScalarModel_mem.lt_iff.2 (by decide), isScalarModel_mem.not_lt_not_iff.2 (by decide),
    isScalarModel_mem.lt_iff.2 (by decide), isScalarModel_mem.not_lt_not_iff.2 (by decide)⟩

/-! ### Complex scales: (121)–(122) -/

/-- The four dimensions of (121), each with the two values its paired foci name, the lower value
the one that makes the hiring the likelier: poor < rich, wash < wax, car < truck, $2 < $1. -/
inductive Dim where
  | wealth
  | task
  | vehicle
  | fee
  deriving DecidableEq, Repr, Fintype

/-- A point of the four-dimensional argument space. -/
abbrev Point := Dim → Fin 2

instance : DecidableLE Point := fun x y ↦ inferInstanceAs (Decidable (∀ d, x d ≤ y d))

instance : DecidableLT Point := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ ¬ _))

/-- *You could get a `wealth` man to `task` your `vehicle` for `fee`* in a state of affairs. -/
abbrev CanGet : Point → LowerSet Point → Prop := (· ∈ ·)

def Point.mk (w t v f : Fin 2) : Point
  | .wealth => w
  | .task => t
  | .vehicle => v
  | .fee => f

def wealthTable : List (String × (Fin 2 × Fin 2)) := [("poor rich", (0, 1)), ("rich poor", (1, 0))]

def taskTable : List (String × (Fin 2 × Fin 2)) := [("wash wax", (0, 1)), ("wax wash", (1, 0))]

def vehicleTable : List (String × (Fin 2 × Fin 2)) := [("car truck", (0, 1)), ("truck car", (1, 0))]

def feeTable : List (String × (Fin 2 × Fin 2)) := [("$2 $1", (0, 1)), ("$1 $2", (1, 0))]

/-- The foci of a row, one pair per dimension in the order A B. -/
def focusFoci? (ex : Datum) : Option (Point × Point) := do
  let w ← ex.parse? "wealth" wealthTable
  let t ← ex.parse? "task" taskTable
  let v ← ex.parse? "vehicle" vehicleTable
  let f ← ex.parse? "fee" feeTable
  pure (.mk w.1 t.1 v.1 f.1, .mk w.2 t.2 v.2 f.2)

def focusRows : List (Row Point) := Examples.all.filterMap (Row.ofDatum focusFoci?)

/-- In (121)–(122) the sentence with the likelier hiring in the full clause is acceptable and each
exchange of one dimension's foci is not. -/
theorem focusRows_predicted : ∀ r ∈ focusRows, (r.judgment = .acceptable ↔ r.Predicted CanGet) := by
  simp only [Row.predicted_iff isScalarModel_mem]
  decide

theorem featured_rows_parse : ∀ ex ∈ Examples.all, (ex.feature? "conjunction").isSome →
    (Row.ofDatum rankFoci? ex).isSome ∨ (Row.ofDatum focusFoci? ex).isSome := by
  decide

end FillmoreKayOConnor1988
