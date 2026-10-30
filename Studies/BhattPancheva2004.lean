module

public import Linglib.Data.Examples.BhattPancheva2004
public import Linglib.Semantics.Degree.HeimKennedy
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command
public import Linglib.Syntax.Minimalist.LateMerger
public import Linglib.Data.Examples.Readers

/-!
# Bhatt and Pancheva (2004): Late Merger of Degree Clauses

Bhatt and Pancheva propose that a degree clause, the *than*- or *as*-phrase, is merged as the
complement of the degree head only after the head has moved to its scope, and is pronounced where
it is merged. Trace Conversion reads the copy of a moved quantifier as a definite restricted by
what the copy carries, which [leaves the quantifier's meaning unchanged exactly when it is
conservative](##conservative_iff_traceConversion). The comparative *-er* is not conservative, so a
copy that carries its clause makes the comparison a contradiction: [the comparison takes scope
where its clause is merged, or with the noun phrase that carries it](##LF.scope_eq_max_of_licit),
while [a relative clause may be merged anywhere below the scope of its source](##rows_relative).
With the Heim–Kennedy constraint this [predicts the readings of extraposed degree
clauses](##rows_degree). A late-merged degree clause [escapes a pronoun exactly when the comparison
scopes over it](##lateMergerBleeds_iff), so [ellipsis and coreference into a degree clause track
where it is merged](##rows_ellipsis).

## Implementation notes

* The definite of Trace Conversion is the Russellian `Quantifier.Det.the`, false where its
  description is empty; the scope it hands the quantifier is the one the paper obtains by
  presupposition projection.
* An `LF` records heights on the spine: where the clause is merged, where the quantifier starts
  moving by itself, its `host`, and where it takes scope. In a comparative noun phrase the degree
  head scopes inside the noun phrase and its clause is merged there; the noun phrase then moves,
  and `host` is its landing site. The paper does not discuss the copy the noun phrase leaves; that
  it is harmless is `conservative_iff_traceConversion` for its conservative determiner.
* The extraposition rows put the operator at height `1` and record the side of it where the clause
  is merged and what moves. Under *required* the mover is the degree phrase alone, as in the
  paper's simplified LFs; the noun phrase *fewer papers* stays under *required*.
* Condition C bleeding is `Minimalist.LateMergerBleeds`, with the merger sites that Trace
  Conversion admits on the chain of the degree head.
* `Degree.IsHeimKennedy` is evaluated on the order of heights for the extraposition rows and on
  c-command for the LF trees, which are category-free at the paper's bracketing, with
  non-branching and elided material written as one leaf. Of the readings the paper excludes by
  the constraint, those whose clause is merged under the *before*-clause are also excluded by its
  merger site; only the extraposed ones need the constraint.
* The scope of degree phrases under intensional verbs is [heim-2000]'s result and is formalized in
  `Studies/Heim2001.lean`.

## TODO

* If *fewer papers than that number* could move over *required* as *more books* moves over the
  *before*-clause in (45), the model would give (53a) and (54a) the comparison over *required*,
  which they lack; the paper's LFs move the degree phrase alone and do not say what keeps the noun
  phrase under *required*.
* The crossing degree abstractions of (48) to (52) are recorded as rows only, and the trapped
  ellipsis of Section 6.3 is not encoded.
* Degree phrases of the form *than n* need not be extraposed and allow split scope under
  *required*, which the paper sets aside (fn. 31) and the model does not cover.
* Late merger of the complement of a noun, (91a), leaves the lower copy of the noun at another
  type than the higher one, (92); stating it needs typed LFs.

## References

* [bhatt-pancheva-2004]
* [fox-2002]
* [fox-nissenbaum-1999]
* [heim-2000]
* [reinhart-1976]
* [williams-1974]
-/

@[expose] public section

namespace BhattPancheva2004

open Core.Order Degree Quantifier Quantifier.Det Set PhraseStructure PhraseStructure.Tree
open RoseTree (cCommand)

/-! ### The Heim–Kennedy constraint (Section 4.1) -/

/-- An LF for the reading (22a) of *every girl is exactly 1 inch taller than that*, with the
quantifier over the DegP, `[every girl [λx [[DegP exactly 1 inch -er than that] [λd [x is
d-tall]]]]]`. -/
def lf22a : Tree Unit String :=
  bin (leaf "every girl") (binder 1 (bin (bin (leaf "exactly 1 inch -er") (leaf "than that"))
    (binder 2 (bin (leaf "x is") (bin (tr 2) (leaf "tall"))))))

/-- An LF for the reading (22b) puts the DegP over the quantifier,
`[[DegP exactly 1 inch -er than that] [λd [every girl [λx [x is d-tall]]]]]`. -/
def lf22b : Tree Unit String :=
  bin (bin (leaf "exactly 1 inch -er") (leaf "than that"))
    (binder 2 (bin (leaf "every girl") (binder 1 (bin (leaf "x is") (bin (tr 2) (leaf "tall"))))))

open Examples in
-- (22), (24), (25): the quantifier's scope in (22b) holds the degree trace but not the DegP
theorem rows_hkc :
    (IsHeimKennedy (cCommand lf22a) ⟨[0]⟩ ⟨[1, 0, 0]⟩ ⟨[1, 0, 1, 0, 1, 0]⟩ ↔
      bp2004_22.readings.lookup "every > -er" = some .acceptable) ∧
    (IsHeimKennedy (cCommand lf22b) ⟨[1, 0, 0]⟩ ⟨[0]⟩ ⟨[1, 0, 1, 0, 1, 0]⟩ ↔
      bp2004_22.readings.lookup "-er > every" = some .acceptable) := by
  decide

/-! ### Trace Conversion (Section 7.1) -/

section TraceConversion

variable {α : Type*} {Q : Det α} {R A B : Set α}

/-- Trace Conversion (80), [fox-2002]'s interpretation of copies, reads the copy that a moved
quantifier leaves, carrying the restrictor material `R`, as the definite `the [R λy (y = x)]`, so
the remnant `B` of its position holds of `x` when the `R` that is `x` is in `B`. -/
def traceConversion (R B : Set α) : Set α := {x | the (R ∩ {x}) B}

theorem traceConversion_eq_inter : traceConversion R B = R ∩ B := by
  ext x
  refine ⟨fun ⟨y, hy, hB⟩ ↦ ?_, fun ⟨hR, hB⟩ ↦ ⟨x, fun y ↦ ⟨And.right, fun h ↦ ⟨h ▸ hR, h⟩⟩, hB⟩⟩
  obtain ⟨hR, rfl⟩ := (hy y).2 rfl
  exact ⟨hR, hB⟩

@[simp]
theorem traceConversion_univ : traceConversion univ B = B := by
  rw [traceConversion_eq_inter, univ_inter]

/-- Trace Conversion of a copy that carries the restrictor leaves a quantifier's meaning unchanged
for every restrictor and scope exactly when the quantifier is conservative; (82) is the forward
direction. -/
theorem conservative_iff_traceConversion :
    Q.Conservative ↔ ∀ A B, Q A (traceConversion A B) ↔ Q A B := by
  simp only [traceConversion_eq_inter]
  exact forall₂_congr fun _ _ ↦ Iff.comm

/-- *Only* holds when its scope lies inside its restrictor. -/
def only : Det α := fun A B ↦ B ⊆ A

-- (83)
theorem only_traceConversion : only A (traceConversion A B) :=
  traceConversion_eq_inter.subset.trans inter_subset_left

theorem not_conservative_only [Nonempty α] : ¬ (only : Det α).Conservative := fun h ↦
  univ_nonempty.ne_empty <| subset_empty_iff.1 <|
    (conservative_iff_traceConversion.1 h ∅ univ).1 only_traceConversion

end TraceConversion

/-! ### The semantics of *-er* (Section 7.2) -/

section Comparative

variable {D : Type*} {A B : Set D}

/-- The comparative degree quantifier (84) holds when its first argument, the degree clause, is a
proper subset of its second. -/
def er : Det D := fun A B ↦ A ⊂ B

-- (85): on degree sets, which are lower sets, some degree of the second is not in the first
theorem er_iff_not_subset [LinearOrder D] (hA : IsLowerSet A) (hB : IsLowerSet B) :
    er A B ↔ ¬ B ⊆ A :=
  ⟨not_subset_of_ssubset, fun h ↦ ssubset_of_subset_not_subset ((hA.total hB).resolve_right h) h⟩

-- (86b), (87c)
theorem not_er_traceConversion : ¬ er A (traceConversion A B) := fun h ↦
  not_subset_of_ssubset h (traceConversion_eq_inter.subset.trans inter_subset_left)

theorem not_conservative_er [Nonempty D] : ¬ (er : Det D).Conservative := fun h ↦
  not_er_traceConversion ((conservative_iff_traceConversion.1 h ∅ univ).2
    (empty_ssubset.2 univ_nonempty))

end Comparative

/-! ### Late merger (Section 7.3) -/

/-- An LF of a quantifier and its clause, by heights on the spine: the clause is merged at `merge`,
the quantifier starts moving by itself at `host`, its base or the landing site of a noun phrase
that pied-pipes it, and it takes scope at `scope`. -/
structure LF (ι : Type*) where
  merge : ι
  host : ι
  scope : ι

namespace LF

variable {ι α D : Type*} [LinearOrder ι] (lf : LF ι) {Q : Det α} {A B : Set α} {q : Prop} {o : ι}

/-- The copy that the quantifier leaves on moving by itself carries the clause when the clause was
merged before that move, below the scope. -/
def Carries : Prop := max lf.merge lf.host < lf.scope

/-- The truth condition of the LF with clause `A` and remnant `B`: Trace Conversion (80) restricts
the remnant by the clause when the copy below the scope carries it, (87c), and by nothing when it
does not, (88d). -/
def Truth (Q : Det α) (A B : Set α) : Prop := Q A (traceConversion {x | lf.Carries → x ∈ A} B)

-- (82): a conservative quantifier means the same wherever below its scope its clause is merged
theorem truth_iff_of_conservative (hQ : Q.Conservative) : lf.Truth Q A B ↔ Q A B := by
  simp only [Truth, traceConversion_eq_inter]
  rw [hQ, hQ A B]
  exact iff_of_eq <| congrArg (Q A) <| by ext; simp +contextual

-- (88), (89)
theorem truth_er_iff {A B : Set D} : lf.Truth er A B ↔ ¬ lf.Carries ∧ er A B := by
  by_cases h : lf.Carries
  · simpa [Truth, h] using not_er_traceConversion
  · simp [Truth, h]

/-- An LF is licit under an operator at height `o` when the clause is merged and the quantifier
starts moving at or below its scope, countercyclic merger (38), some clause and remnant make it
true, and, when the operator is quantificational, the operator does not separate the quantifier
from its host, the Heim–Kennedy constraint (24). -/
def Licit (Q : Det α) (q : Prop) (o : ι) : Prop :=
  lf.merge ≤ lf.scope ∧ lf.host ≤ lf.scope ∧ (∃ A B, lf.Truth Q A B) ∧
    (q → IsHeimKennedy {p | p.2 < p.1} o lf.scope lf.host)

/-- Degree clauses can only be merged in their ultimate scope position (90): on a licit LF the
comparison takes scope exactly at the higher of the clause's merger site and its host, the
landing site of a noun phrase that carries it. An extraposed degree clause thus marks the scope
of its degree head (39). -/
theorem scope_eq_max_of_licit (h : lf.Licit (er : Det D) q o) :
    lf.scope = max lf.merge lf.host :=
  let ⟨hm, hh, ⟨_, _, hT⟩, _⟩ := h
  le_antisymm (not_lt.1 ((lf.truth_er_iff).1 hT).1) (max_le hm hh)

theorem licit_er_iff [Nonempty D] :
    lf.Licit (er : Det D) q o ↔
      lf.scope = max lf.merge lf.host ∧ (q → lf.host < o → lf.scope < o) := by
  refine ⟨fun h ↦ ⟨lf.scope_eq_max_of_licit h, h.2.2.2⟩, fun ⟨h, hq⟩ ↦ ?_⟩
  refine ⟨(le_max_left _ _).trans_eq h.symm, (le_max_right _ _).trans_eq h.symm, ⟨∅, univ, ?_⟩,
    hq⟩
  exact (lf.truth_er_iff).2 ⟨fun hc ↦ hc.ne' h, empty_ssubset.2 univ_nonempty⟩

theorem licit_iff_of_conservative (hQ : Q.Conservative) (hne : ∃ A B, Q A B) :
    lf.Licit Q q o ↔
      lf.merge ≤ lf.scope ∧ lf.host ≤ lf.scope ∧ (q → lf.host < o → lf.scope < o) := by
  simp only [Licit, lf.truth_iff_of_conservative hQ, hne, true_and]
  rfl

end LF

/-! ### The Extraposition-Scope Generalization (Section 5.2) -/

/-- The heights, against an operator at height `1`, on the side of it where a row's clause is
merged: below it, `low`, or above it, `high`. -/
def siteHeights : Option String → Set ℕ
  | some "low" => Iio 1
  | some "high" => Ioi 1
  | _ => univ

/-- The heights from which a row's mover takes scope by itself: a bare DegP from its degree
predicate under the operator, a noun phrase from wherever it lands. -/
def hostHeights : Option String → Set ℕ
  | some "DegP" => Iio 1
  | _ => univ

/-- A reading of the row `e` for the quantifier `Q` under an operator at height `1`,
quantificational when `q`: some licit LF with the clause merged on the side of the operator that
`e` records and the host where its mover allows satisfies `reading`. -/
def Available {α : Type*} (Q : Det α) (q : Prop) (e : Datum) (reading : LF ℕ → Prop) : Prop :=
  ∃ lf : LF ℕ, lf.merge ∈ siteHeights (e.feature? "site") ∧
    lf.host ∈ hostHeights (e.feature? "mover") ∧ lf.Licit Q q 1 ∧ reading lf

open Examples in
/-- A relative clause merged above the *before*-clause fixes the scope of its source above it, and
one merged below leaves the scope free, (41) against (42): [fox-nissenbaum-1999]'s account of
[williams-1974]'s generalization, on which *every* being conservative lets the clause be merged
below the scope. -/
theorem rows_relative :
    (Available (every : Det ℕ) False bp2004_41 (·.scope < 1) ↔
      bp2004_41.readings.lookup "before > every" = some .acceptable) ∧
    (Available (every : Det ℕ) False bp2004_41 (1 < ·.scope) ↔
      bp2004_41.readings.lookup "every > before" = some .acceptable) ∧
    (Available (every : Det ℕ) False bp2004_42 (·.scope < 1) ↔
      bp2004_42.readings.lookup "before > every" = some .acceptable) ∧
    (Available (every : Det ℕ) False bp2004_42 (1 < ·.scope) ↔
      bp2004_42.readings.lookup "every > before" = some .acceptable) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp +decide [Available, Datum.feature?, siteHeights, hostHeights, List.lookup, bp2004_41,
      bp2004_42, LF.licit_iff_of_conservative _ (Q := (every : Det ℕ)) conservative_every
        ⟨∅, ∅, empty_subset _⟩] <;>
    first
    | omega
    | (refine ⟨⟨0, 0, 0⟩, ?_⟩; decide)
    | (refine ⟨⟨0, 0, 2⟩, ?_⟩; decide)
    | (refine ⟨⟨2, 0, 2⟩, ?_⟩; decide)

open Examples in
/-- A bare degree head takes scope exactly where its clause is merged: under the *before*-clause or
*required* when the clause is merged under it and over *required* when it is merged over it, while
over the quantificational *before*-clause the Heim–Kennedy constraint leaves the sentence no LF
((43), (44), (53), (54)). -/
theorem rows_degree :
    (Available (er : Det ℕ) True bp2004_43 (·.scope < 1) ↔
      bp2004_43.readings.lookup "before > -er" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_43 (1 < ·.scope) ↔
      bp2004_43.readings.lookup "-er > before" = some .acceptable) ∧
    (¬ Available (er : Det ℕ) True bp2004_44 (fun _ ↦ True) ↔
      bp2004_44.judgment.band = .rejected) ∧
    (Available (er : Det ℕ) False bp2004_53a (·.scope < 1) ↔
      bp2004_53a.readings.lookup "required > fewer" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_53a (1 < ·.scope) ↔
      bp2004_53a.readings.lookup "fewer > required" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_53b (·.scope < 1) ↔
      bp2004_53b.readings.lookup "required > fewer" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_53b (1 < ·.scope) ↔
      bp2004_53b.readings.lookup "fewer > required" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_54a (·.scope < 1) ↔
      bp2004_54a.readings.lookup "required > exactly 5 more" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_54a (1 < ·.scope) ↔
      bp2004_54a.readings.lookup "exactly 5 more > required" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_54b (·.scope < 1) ↔
      bp2004_54b.readings.lookup "required > exactly 5 more" = some .acceptable) ∧
    (Available (er : Det ℕ) False bp2004_54b (1 < ·.scope) ↔
      bp2004_54b.readings.lookup "exactly 5 more > required" = some .acceptable) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp +decide [Available, Datum.feature?, siteHeights, hostHeights, List.lookup, bp2004_43,
      bp2004_44, bp2004_53a, bp2004_53b, bp2004_54a, bp2004_54b, LF.licit_er_iff] <;>
    first
    | omega
    | (refine ⟨⟨0, 0, 0⟩, ?_⟩; decide)
    | (refine ⟨⟨2, 0, 2⟩, ?_⟩; decide)

-- (44): without the Heim–Kennedy constraint the comparison would scope over the *before*-clause
example : Available (er : Det ℕ) False Examples.bp2004_44 (1 < ·.scope) := by
  simp +decide [Available, Datum.feature?, siteHeights, hostHeights, List.lookup,
    Examples.bp2004_44, LF.licit_er_iff]
  exact ⟨⟨2, 0, 2⟩, by decide⟩

open Examples in
-- (45), (46): a comparative noun phrase whose clause is merged inside it scopes under or over the
-- *before*-clause, one whose clause is merged above it only over it, and its degree head never
-- leaves it across the *before*-clause
theorem rows_comparativeDP :
    (Available (er : Det ℕ) True bp2004_45 (·.scope < 1) ↔
      bp2004_45.readings.lookup "before > -er d-many books" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_45 (1 < ·.host) ↔
      bp2004_45.readings.lookup "-er d-many books > before" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_45 (fun lf ↦ lf.host < 1 ∧ 1 < lf.scope) ↔
      bp2004_45.readings.lookup "-er > before > d-many books" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_46 (·.scope < 1) ↔
      bp2004_46.readings.lookup "before > -er d-many books" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_46 (1 < ·.host) ↔
      bp2004_46.readings.lookup "-er d-many books > before" = some .acceptable) ∧
    (Available (er : Det ℕ) True bp2004_46 (fun lf ↦ lf.host < 1 ∧ 1 < lf.scope) ↔
      bp2004_46.readings.lookup "-er > before > d-many books" = some .acceptable) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp +decide [Available, Datum.feature?, siteHeights, hostHeights, List.lookup, bp2004_45,
      bp2004_46, LF.licit_er_iff] <;>
    first
    | omega
    | (refine ⟨⟨0, 0, 0⟩, ?_⟩; decide)
    | (refine ⟨⟨0, 2, 2⟩, ?_⟩; decide)
    | (refine ⟨⟨2, 2, 2⟩, ?_⟩; decide)

/-! ### Ellipsis and Condition C mark the scope of the comparison (Section 6) -/

open Minimalist (LateMergerBleeds) in
-- (69), (70): on a chain above its host, late merger of a degree clause bleeds Condition C for a
-- binder exactly when the comparison scopes above the binder
theorem lateMergerBleeds_iff {D : Type*} [Nonempty D] {chain : List ℕ} {h s b o : ℕ} {q : Prop}
    (hc : ∀ m ∈ chain, h ≤ m) :
    LateMergerBleeds (fun m ↦ (⟨m, h, s⟩ : LF ℕ).Licit (er : Det D) q o) id chain b ↔
      s ∈ chain ∧ b < s ∧ (q → h < o → s < o) := by
  simp only [LateMergerBleeds, LF.licit_er_iff, id]
  constructor
  · rintro ⟨m, hm, ⟨hs, hq⟩, hb⟩
    rw [max_eq_left (hc m hm)] at hs
    subst hs
    exact ⟨hm, hb, hq⟩
  · rintro ⟨hs, hb, hq⟩
    exact ⟨s, hs, ⟨(max_eq_left (hc s hs)).symm, hq⟩, hb⟩

/-- An LF of a sentence of the form *her father tells her to work harder than Mary's boss does*,
(60) to (70): the tree and the positions of the DegP, the remnant of the degree clause, the matrix
subject and object, the verb *tells*, and the matrix and embedded VPs. -/
structure TellLF where
  tree : Tree Unit String
  degP : TreePath
  clause : TreePath
  subject : TreePath
  object : TreePath
  tells : TreePath
  matrixVP : TreePath
  embeddedVP : TreePath

/-- With the clause merged at the embedded clause, the LF is (69a),
`[her father [tells [her [[λd PRO to work d-hard] [-er than Mary's boss does]]]]]`, with the
subject, the object and the remnant of the degree clause as given. -/
def low (subject object clause : String) : TellLF where
  tree := bin (leaf subject) (bin (leaf "tells") (bin (leaf object)
    (bin (binder 1 (bin (leaf "PRO to work") (bin (tr 1) (leaf "hard"))))
      (bin (leaf "-er") (bin (leaf "than") (leaf clause))))))
  degP := ⟨[1, 1, 1, 1]⟩
  clause := ⟨[1, 1, 1, 1, 1, 1]⟩
  subject := ⟨[0]⟩
  object := ⟨[1, 1, 0]⟩
  tells := ⟨[1, 0]⟩
  matrixVP := ⟨[1]⟩
  embeddedVP := ⟨[1, 1, 1, 0, 0]⟩

/-- With the clause merged at the matrix clause, the LF is (69c),
`[[λd her father tells her to work d-hard] [-er than Mary's boss does]]`. -/
def high (subject object clause : String) : TellLF where
  tree := bin (binder 1 (bin (leaf subject) (bin (leaf "tells") (bin (leaf object)
    (bin (leaf "PRO to work") (bin (tr 1) (leaf "hard")))))))
    (bin (leaf "-er") (bin (leaf "than") (leaf clause)))
  degP := ⟨[1]⟩
  clause := ⟨[1, 1, 1]⟩
  subject := ⟨[0, 0, 0]⟩
  object := ⟨[0, 0, 1, 1, 0]⟩
  tells := ⟨[0, 0, 1, 0]⟩
  matrixVP := ⟨[0, 0, 1]⟩
  embeddedVP := ⟨[0, 0, 1, 1, 1]⟩

/-- The LFs of a sentence of the form (60), its degree clause merged at the embedded or at the
matrix clause. -/
def tellLFs (subject object clause : String) : List TellLF :=
  [low subject object clause, high subject object clause]

/-- A reading of a sentence with the LFs `lfs`, the comparison over *tells* when `wide` and its
elided VP resolved to `antecedent`: some LF with that scope has the antecedent c-commanded by the
DegP, the Ellipsis-Scope Generalization (59), and no `pronoun` c-commanding the `name` it corefers
with, Condition C. C-command is [reinhart-1976]'s, without dominance, so an antecedent inside the
DegP is not in its scope. -/
def TellLF.Reading (lfs : List TellLF) (wide : Prop) (antecedent pronoun name : TellLF → TreePath) :
    Prop :=
  ∃ lf ∈ lfs, (lf.tree.CCommands lf.degP lf.tells ↔ wide) ∧
    lf.tree.CCommands lf.degP (antecedent lf) ∧ ¬ lf.tree.CCommands (pronoun lf) (name lf)

instance {lfs : List TellLF} {wide : Prop} [Decidable wide] {antecedent pronoun name} :
    Decidable (TellLF.Reading lfs wide antecedent pronoun name) :=
  inferInstanceAs (Decidable (∃ lf ∈ lfs, _))

open Examples TellLF in
/-- The elided VP of a degree clause can be the matrix VP, and a name in it can corefer with the
matrix object, only when the comparison scopes over *tells*: a degree clause merged under *tells*
has only the embedded VP in the scope of its DegP and lies in the c-command domain of the object
((60), (61), (63), (64)). -/
theorem rows_ellipsis :
    let s60 := tellLFs "Mary's father" "her" "her boss does"
    let s61 := tellLFs "Mary's father" "her" "her boss tells her to"
    let s63 := tellLFs "her father" "her" "Mary's boss does"
    let s64a := tellLFs "her father" "her" "Mary's boss tells her to"
    let s64b := tellLFs "her father" "Mary" "her boss tells her to"
    (Reading s60 False embeddedVP object subject ↔
      bp2004_60.readings.lookup "tell > -er, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s60 False matrixVP object subject ↔
      bp2004_60.readings.lookup "tell > -er, elided VP: tell her to work d-hard" =
        some .acceptable) ∧
    (Reading s60 True embeddedVP object subject ↔
      bp2004_60.readings.lookup "-er > tell, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s60 True matrixVP object subject ↔
      bp2004_60.readings.lookup "-er > tell, elided VP: tell her to work d-hard" =
        some .acceptable) ∧
    (Reading s61 False embeddedVP object subject ↔
      bp2004_61.readings.lookup "tell > -er, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s61 True embeddedVP object subject ↔
      bp2004_61.readings.lookup "-er > tell, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s63 False embeddedVP object clause ↔
      bp2004_63.readings.lookup "tell > -er, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s63 False matrixVP object clause ↔
      bp2004_63.readings.lookup "tell > -er, elided VP: tell her to work d-hard" =
        some .acceptable) ∧
    (Reading s63 True embeddedVP object clause ↔
      bp2004_63.readings.lookup "-er > tell, elided VP: work d-hard" = some .acceptable) ∧
    (Reading s63 True matrixVP object clause ↔
      bp2004_63.readings.lookup "-er > tell, elided VP: tell her to work d-hard" =
        some .acceptable) ∧
    (Reading s64a False embeddedVP object clause ↔
      bp2004_64a.readings.lookup "tell > -er" = some .acceptable) ∧
    (Reading s64a True embeddedVP object clause ↔
      bp2004_64a.readings.lookup "-er > tell" = some .acceptable) ∧
    (Reading s64b False embeddedVP clause object ↔
      bp2004_64b.readings.lookup "tell > -er" = some .acceptable) ∧
    (Reading s64b True embeddedVP clause object ↔
      bp2004_64b.readings.lookup "-er > tell" = some .acceptable) := by
  decide

end BhattPancheva2004
