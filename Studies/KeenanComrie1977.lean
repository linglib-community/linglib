module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.OrdConnected
public import Linglib.Syntax.Clause.Relative
public import Linglib.Fragments.English.Relativization
public import Linglib.Fragments.Welsh.Relativization
public import Linglib.Fragments.Arabic.ModernStandard.Relativization
public import Linglib.Fragments.Hebrew.Relativization
public import Linglib.Fragments.TobaBatak.Relativization
public import Linglib.Fragments.TobaBatak.Voice
public import Linglib.Fragments.Korean.Relativization
public import Linglib.Fragments.Finnish.Relativization
public import Linglib.Fragments.Malagasy.Relativization
public import Linglib.Fragments.Mandarin.Relativization
public import Linglib.Fragments.Basque.Relativization
public import Linglib.Fragments.German.Relativization
public import Linglib.Fragments.HindiUrdu.Relativization
public import Linglib.Fragments.Japanese.Relativization
public import Linglib.Fragments.Romance.French.Relativization
public import Linglib.Fragments.Slavic.Russian.Relativization
public import Linglib.Fragments.Tagalog.Relativization
public import Linglib.Fragments.Turkish.Relativization

/-!
# Keenan and Comrie (1977): Noun Phrase Accessibility and Universal Grammar

This file formalizes Keenan and Comrie's Hierarchy Constraints on the Accessibility Hierarchy,
subject > direct object > indirect object > oblique > genitive > object of comparison, and
checks them on the languages of Table 1 that the fragments record. A strategy is a placement of
the clause together with ±case, and the positions it covers are derived from a language's
relativizers. Toba Batak, whose two strategies leave the direct object between them, refutes the
stronger constraint on languages and satisfies its weakening by promotion.

## Main definitions

* `clauses`, `relativizable`: the relative clauses a language forms, and the positions it
  relativizes.
* `Strategy`, `Strategy.positions`: a strategy and the positions it covers in a language.
* `SatisfiesHC1`, `SatisfiesHC2`, `SatisfiesPRC`: the Hierarchy Constraints and the Primary
  Relativization Constraint.
* `SatisfiesHCPromotion`, `Promotes`: the strong constraint with promotion, and promotion to
  subject by a voice system.
* `retention`, `RetainsDownward`: pronoun retention and its downward closure.

## Implementation notes

* Continuity is order-connectedness in the substrate's `Position` order. A relative pronoun
  agreeing with the head, English *who* (p. 65), leaves the relativized position a gap, so case
  coding is a property of what occupies that position (`IsCaseCoding`).
* The sample takes Classical Arabic by the Modern Standard Arabic relativizer, the paper
  considering only definite relative clauses (p. 64), and leaves out Yoruba, whose fragment
  follows Awobuluyi rather than Table 1. Entries +/− and +? count as +, and a blank, which marks
  missing data, as −, as for Toba Batak's object of comparison. Table 1 classes Hindi's
  correlative as internally headed.
* Promotion is read off pivot selection, which suits Toba Batak's symmetrical voices.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace KeenanComrie1977

open Relativization Finset

/-! ### Strategies (Section 1.1) -/

/-- Case coding (p. 65): the element at the relativized position expresses which position it is,
as a relative pronoun marked for it or a retained personal pronoun does (p. 66); a gap
expresses none. -/
def IsCaseCoding (x : NPRel) : Prop := x ≠ .gap

instance : DecidablePred IsCaseCoding := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The relative clauses a language forms, each a relativized position with the placement of the
clause and what occupies the position. -/
def clauses (L : List Relativizer) : Finset (Position × Placement × NPRel) :=
  univ.filter fun c ↦ ∃ r ∈ L, r.placement = c.2.1 ∧ c.2.2 ∈ r.realize c.1

/-- The positions a language relativizes. -/
def relativizable (L : List Relativizer) : Finset Position := (clauses L).image Prod.fst

/-- An RC-forming strategy (p. 65): relative clauses are formed by different strategies when
their heads are placed differently or one is case-coding and the other not. -/
structure Strategy where
  /-- The placement of the clause relative to its head. -/
  placement : Placement
  /-- Whether the strategy is case-coding, the paper's ±case. -/
  caseCoding : Bool
  deriving DecidableEq, Fintype

namespace Strategy

/-- The strategy forming a relative clause with a placement and an occupant of the relativized
position. -/
def of (c : Placement × NPRel) : Strategy := ⟨c.1, decide (IsCaseCoding c.2)⟩

variable (s : Strategy) (L : List Relativizer)

/-- The positions a language relativizes by a strategy, those of the clauses it forms. -/
def positions : Finset Position := ((clauses L).filter (of ·.2 = s)).image Prod.fst

/-- A strategy is primary when it relativizes subjects. -/
def IsPrimary : Prop := ⊤ ∈ s.positions L

instance : Decidable (s.IsPrimary L) := inferInstanceAs (Decidable (_ ∈ _))

end Strategy

/-- A language relativizes a position iff one of its strategies does. -/
theorem relativizable_eq_biUnion (L : List Relativizer) :
    relativizable L = univ.biUnion (Strategy.positions · L) := by
  rw [relativizable, ← biUnion_filter_eq_of_maps_to (s := clauses L) (t := univ)
    (f := (Strategy.of ·.2)) fun _ _ ↦ mem_univ _, biUnion_image]
  rfl

/-! ### The Hierarchy Constraints (Section 1.2) -/

/-- HC₁ (p. 67): a language must be able to relativize subjects. -/
def SatisfiesHC1 (L : List Relativizer) : Prop := ⊤ ∈ relativizable L

instance (L : List Relativizer) : Decidable (SatisfiesHC1 L) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- HC₂ (p. 67): every strategy covers a continuous segment of the hierarchy. -/
def SatisfiesHC2 (L : List Relativizer) : Prop :=
  ∀ s : Strategy, (s.positions L : Set Position).OrdConnected

instance (L : List Relativizer) : Decidable (SatisfiesHC2 L) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The Primary Relativization Constraint (p. 68): a language has a primary strategy, and a
primary strategy covers an upper set of the hierarchy. Its third clause, that a primary strategy
may cut off at any point, constrains no language. -/
structure SatisfiesPRC (L : List Relativizer) : Prop where
  exists_isPrimary : ∃ s : Strategy, s.IsPrimary L
  isUpperSet_positions : ∀ s : Strategy, s.IsPrimary L → IsUpperSet (s.positions L : Set Position)

/-- The first clause of the Primary Relativization Constraint restates HC₁. -/
theorem satisfiesHC1_iff_exists_isPrimary {L : List Relativizer} :
    SatisfiesHC1 L ↔ ∃ s : Strategy, s.IsPrimary L := by
  simp [SatisfiesHC1, relativizable_eq_biUnion, Strategy.IsPrimary]

/-- The Primary Relativization Constraint follows from the Hierarchy Constraints, its second
clause from HC₂ and the definition of primary. -/
theorem SatisfiesHC2.satisfiesPRC {L : List Relativizer} (h₂ : SatisfiesHC2 L)
    (h₁ : SatisfiesHC1 L) : SatisfiesPRC L :=
  ⟨satisfiesHC1_iff_exists_isPrimary.1 h₁, fun s hp ↦ (h₂ s).isUpperSet_of_top_mem hp⟩

theorem SatisfiesHC2.positions_eq_Icc_top {L : List Relativizer} (h : SatisfiesHC2 L)
    {s : Strategy} (hp : s.IsPrimary L) : s.positions L = Icc ((s.positions L).min' ⟨⊤, hp⟩) ⊤ :=
  eq_Icc_top_of_ordConnected_coe (h s) hp

/-! ### The sample (Table 1)

The seventeen languages of Table 1 whose fragments follow it. -/

abbrev english := English.Relativization.relativizers
abbrev welsh := Welsh.relativizers
/-- Table 1's Classical Arabic, by the Modern Standard Arabic relativizer. -/
abbrev arabic : List Relativizer := [Arabic.ModernStandard.relativizer]
abbrev hebrew := Hebrew.relativizers
abbrev tobaBatak := TobaBatak.relativizers
abbrev korean := Korean.relativizers
abbrev finnish := Finnish.relativizers
abbrev malagasy := Malagasy.relativizers
/-- Table 1's Chinese, spoken Pekingese. -/
abbrev mandarin := Mandarin.relativizers
abbrev basque := Basque.relativizers
abbrev french := French.relativizers
abbrev german := German.relativizers
/-- Table 1's Hindi. -/
abbrev hindi := HindiUrdu.relativizers
abbrev japanese := Japanese.relativizers
abbrev russian := Russian.relativizers
abbrev tagalog := Tagalog.relativizers
abbrev turkish := Turkish.relativizers

/-- The sample. -/
def sample : List (List Relativizer) :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy, mandarin, basque,
    french, german, hindi, japanese, russian, tagalog, turkish]

/-- Rows of Table 1 (pp. 76–78, Sections 1.3.2 and 1.3.4) and Table 2 (p. 93). -/
theorem hebrew_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions hebrew = {.subject, .directObject} ∧
      (⟨.postNominal, true⟩ : Strategy).positions hebrew = Iic .directObject := by
  decide

theorem arabic_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions arabic = {.subject} ∧
      (⟨.postNominal, true⟩ : Strategy).positions arabic = {.subject}ᶜ := by
  decide

theorem satisfiesHC1_of_mem_sample {L : List Relativizer} (h : L ∈ sample) :
    SatisfiesHC1 L := by
  revert L; decide

/-- The sample obeys HC₂ and retains pronouns downward (p. 92). -/
theorem satisfiesHC2_of_mem_sample {L : List Relativizer} (h : L ∈ sample) :
    SatisfiesHC2 L := by
  revert L; decide

theorem satisfiesPRC_of_mem_sample {L : List Relativizer} (h : L ∈ sample) : SatisfiesPRC L :=
  (satisfiesHC2_of_mem_sample h).satisfiesPRC (satisfiesHC1_of_mem_sample h)

/-- Every position from the genitive up is the cut-off of some primary strategy in the sample
(Section 1.3). -/
theorem exists_positions_eq_Icc {p : Position} (hp : .genitive ≤ p) :
    ∃ L ∈ sample, ∃ s : Strategy, s.positions L = Icc p .subject := by
  revert p; decide

/-! ### Gaps and promotion (Section 1.2.2) -/

/-- The strong constraint with promotion (p. 69): every position above one a language relativizes
is relativized directly or promoted along `R` to a position relativized directly. -/
def SatisfiesHCPromotion (L : List Relativizer) (R : Position → Position → Prop) : Prop :=
  ∀ q ∈ upperClosure (relativizable L : Set Position),
    q ∈ relativizable L ∨ ∃ q' ∈ relativizable L, R q q'

instance (L : List Relativizer) (R : Position → Position → Prop) [DecidableRel R] :
    Decidable (SatisfiesHCPromotion L R) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- Without promotion the constraint is the stronger one the paper rejects, that a language
relativizes an upper set of the hierarchy. -/
theorem satisfiesHCPromotion_bot_iff {L : List Relativizer} :
    SatisfiesHCPromotion L ⊥ ↔ IsUpperSet (relativizable L : Set Position) :=
  ⟨fun h _ _ hpq hp ↦ (h _ ⟨_, hp, hpq⟩).resolve_right fun ⟨_, _, h⟩ ↦ h,
    fun h _ ⟨_, hp, hpq⟩ ↦ .inl (h hpq hp)⟩

/-- A voice system promotes a position to subject when one of its voices selects as pivot the
term role that `role` gives the position's noun phrase. -/
def Promotes (S : Voice.System) (role : Position → Option Voice.TermRole) (p q : Position) :
    Prop :=
  q = ⊤ ∧ ∃ r ∈ role p, some r ∈ S.pivotRoles

instance (S : Voice.System) (role : Position → Option Voice.TermRole) :
    DecidableRel (Promotes S role) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The term role of the noun phrase at each position of a Toba Batak clause: A for the subject
and P for the direct object of the actor voice, X for an indirect object or oblique, which a
preposition governs (p. 69), and none for a genitive or an object of comparison, which is no
term of the verb. -/
def tobaBatakRole : Position → Option Voice.TermRole
  | .subject => some .A
  | .directObject => some .P
  | .indirectObject | .oblique => some .X
  | .genitive | .objComparison => none

/-- Toba Batak relativizes indirect objects but not direct objects, refuting the stronger
constraint. -/
theorem not_isUpperSet_relativizable_tobaBatak :
    ¬ IsUpperSet (relativizable tobaBatak : Set Position) := fun h ↦
  absurd (h (show Position.indirectObject ≤ .directObject by decide) (by decide)) (by decide)

/-- Toba Batak satisfies the constraint with promotion, its object voice promoting the direct
object to subject. -/
theorem satisfiesHCPromotion_tobaBatak :
    SatisfiesHCPromotion tobaBatak (Promotes TobaBatak.voices tobaBatakRole) := by
  decide

/-- Toba Batak relativizes directly the subject and exactly the positions its voices cannot
promote, the object of comparison aside. -/
theorem mem_relativizable_tobaBatak_iff {p : Position} (hp : p ≠ .objComparison) :
    p ∈ relativizable tobaBatak ↔
      p = .subject ∨ ¬ Promotes TobaBatak.voices tobaBatakRole p .subject := by
  revert p; decide

/-! ### Strategies by their relativized position (Section 1.3) -/

theorem korean_genitive_retention :
    (⟨.preNominal, false⟩ : Strategy).positions korean = Icc .oblique .subject ∧
      ∀ r ∈ korean, r.realize .genitive = {.resumptive} := by
  decide

theorem finnish_plus_case_is_primary :
    (⟨.preNominal, false⟩ : Strategy).positions finnish ⊂
        (⟨.postNominal, true⟩ : Strategy).positions finnish ∧
      (⟨.preNominal, false⟩ : Strategy).IsPrimary finnish ∧
      (⟨.postNominal, true⟩ : Strategy).IsPrimary finnish := by
  decide

/-! ### Pronoun retention (Section 2.2.2) -/

/-- The positions at which a language retains a personal pronoun, its row of Table 2 (p. 93);
pronouns of verb agreement are excluded (p. 92). -/
def retention (L : List Relativizer) : Finset Position :=
  ((clauses L).filter (·.2.2 = .resumptive)).image Prod.fst

/-- "Once a language begins to retain pronouns it must do so for as long as relativization is
possible at all" (p. 92). -/
def RetainsDownward (L : List Relativizer) : Prop :=
  ∀ p ∈ retention L, ∀ q ∈ relativizable L, q ≤ p → q ∈ retention L

instance (L : List Relativizer) : Decidable (RetainsDownward L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

theorem arabic_table2 : retention arabic = {.subject}ᶜ := by decide

theorem retainsDownward_of_mem_sample {L : List Relativizer} (h : L ∈ sample) :
    RetainsDownward L := by
  revert L; decide

end KeenanComrie1977
