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

* `Strategy`, `Strategy.positions`: a strategy and the positions it covers in a language.
* `SatisfiesHC1`, `SatisfiesHC2`, `SatisfiesPRC`: the Hierarchy Constraints and the Primary
  Relativization Constraint.
* `SatisfiesHCPromotion`, `Promotes`: the strong constraint with promotion, and promotion to
  subject by a voice system.
* `retention`, `RetainsDownward`: pronoun retention and its downward closure.

## Main statements

* `prc_of_hc2`: the Primary Relativization Constraint follows from HC₂.
* `hc1_verified`, `hc2_verified`, `retention_verified`: the constraints hold of the sample.
* `each_upper_cutoff_attested`: each position down to the genitive is a cut-off.
* `tobaBatak_needs_promotion`, `mem_relativizable_tobaBatak_iff`: Toba Batak needs promotion,
  and relativizes directly the subject and the positions its voices cannot promote.

## Implementation notes

* Continuity is order-connectedness in the substrate's `Position` order. A relative pronoun
  agreeing with the head, English *who* (p. 65), leaves the relativized position a gap, so case
  coding is a property of what occupies that position (`IsCaseCoding`).
* The sample takes Classical Arabic by the Modern Standard Arabic relativizer of a definite
  antecedent (p. 64) and leaves out Yoruba, whose fragment follows Awobuluyi rather than
  Table 1. Entries +/− and +? count as +, and a blank, which marks missing data, as −, as for
  Toba Batak's object of comparison. Table 1 classes Hindi's correlative as internally headed.
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

/-- An RC-forming strategy (p. 65): relative clauses are formed by different strategies when
their heads are placed differently or one is case-coding and the other not. -/
structure Strategy where
  /-- The placement of the clause relative to its head. -/
  placement : Placement
  /-- Whether the strategy is case-coding, the paper's ±case. -/
  caseCoding : Bool
  deriving DecidableEq, Fintype

namespace Strategy

variable (s : Strategy) (L : List Relativizer)

/-- The positions a language relativizes by a strategy: those some relativizer with its
placement realizes with an element of its case coding. -/
def positions : Finset Position :=
  univ.filter fun p ↦ ∃ r ∈ L, r.placement = s.placement ∧
    ∃ x ∈ r.realize p, decide (IsCaseCoding x) = s.caseCoding

/-- A strategy is primary when it relativizes subjects. -/
def IsPrimary : Prop := ⊤ ∈ s.positions L

instance : Decidable (s.IsPrimary L) := inferInstanceAs (Decidable (_ ∈ _))

end Strategy

/-! ### The Hierarchy Constraints (Section 1.2) -/

/-- HC₁: some strategy relativizes subjects. -/
def SatisfiesHC1 (L : List Relativizer) : Prop := ∃ s : Strategy, s.IsPrimary L

instance (L : List Relativizer) : Decidable (SatisfiesHC1 L) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- HC₂: every strategy covers a continuous segment of the hierarchy. -/
def SatisfiesHC2 (L : List Relativizer) : Prop :=
  ∀ s : Strategy, (s.positions L : Set Position).OrdConnected

instance (L : List Relativizer) : Decidable (SatisfiesHC2 L) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The Primary Relativization Constraint: a primary strategy covers an upper set of the
hierarchy, every position above one it reaches. -/
def SatisfiesPRC (L : List Relativizer) : Prop :=
  ∀ s : Strategy, s.IsPrimary L → IsUpperSet (s.positions L : Set Position)

/-- The Primary Relativization Constraint follows from HC₂ and the definition of primary, as
the paper derives it: a continuous strategy that relativizes subjects covers an upper set. -/
theorem prc_of_hc2 {L : List Relativizer} (h : SatisfiesHC2 L) : SatisfiesPRC L :=
  fun s hp ↦ Set.OrdConnected.isUpperSet_of_top_mem (h s) hp

/-! ### The sample (Table 1)

The seventeen languages of Table 1 whose relativizers the fragments record. -/

abbrev english := English.Relativization.relativizers
abbrev welsh := Welsh.relativizers
/-- Table 1's Classical Arabic, by the Modern Standard Arabic relativizer of a definite
antecedent, the paper considering only definite restrictive relative clauses (p. 64). -/
abbrev arabic : List Relativizer := [Arabic.ModernStandard.relativizer .definite]
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

/-- Table 1's Hebrew (p. 77): the −case strategy covers subjects and direct objects and the
+case strategy everything from direct objects down, the direct object shared between them. -/
theorem hebrew_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions hebrew = {.subject, .directObject} ∧
      (⟨.postNominal, true⟩ : Strategy).positions hebrew = Iic .directObject := by
  decide

/-- Table 1's Arabic (p. 76): the −case strategy covers the subject alone and the +case strategy
every other position. -/
theorem arabic_table1 :
    (⟨.postNominal, false⟩ : Strategy).positions arabic = {⊤} ∧
      (⟨.postNominal, true⟩ : Strategy).positions arabic = {⊤}ᶜ := by
  decide

/-- HC₁ holds of every language in the sample. -/
theorem hc1_verified : ∀ L ∈ sample, SatisfiesHC1 L := by decide

/-- HC₂ holds of every strategy in the sample. -/
theorem hc2_verified : ∀ L ∈ sample, SatisfiesHC2 L := by decide

/-- Hence so does the Primary Relativization Constraint. -/
theorem prc_verified : ∀ L ∈ sample, SatisfiesPRC L :=
  fun _ h ↦ prc_of_hc2 (hc2_verified _ h)

/-- In the sample every primary strategy covers exactly the closed interval from its cut-off up
to the subject, by HC₂ and `Finset.eq_Icc_top_of_ordConnected_coe`: what Table 1 records as a
run of `+` entries ending at the subject. -/
theorem primary_positions_eq_Icc_top :
    ∀ L ∈ sample, ∀ s : Strategy, (hp : s.IsPrimary L) →
      s.positions L = Icc ((s.positions L).min' ⟨⊤, hp⟩) ⊤ :=
  fun _ h s hp ↦ eq_Icc_top_of_ordConnected_coe (hc2_verified _ h s) hp

/-- Every position from subject to genitive is the cut-off of some primary strategy in the
sample, which covers exactly the interval from there up to the subject: the Section 1.3 argument
that each point of the hierarchy is a possible cut-off. The paper's witnesses for the object of
comparison are not among the fragments. -/
theorem each_upper_cutoff_attested :
    ∀ p ∈ [Position.subject, .directObject, .indirectObject, .oblique, .genitive],
      ∃ L ∈ sample, ∃ s : Strategy, s.positions L = Icc p ⊤ := by
  decide

/-! ### Gaps and promotion (Section 1.2.2) -/

/-- The positions a language relativizes. -/
def relativizable (L : List Relativizer) : Finset Position :=
  univ.filter fun p ↦ ∃ r ∈ L, (r.realize p).Nonempty

/-- The strong constraint with promotion (p. 69): a language relativizing a position relativizes
every higher one, directly or by promoting it along `R` to a position it relativizes directly. -/
def SatisfiesHCPromotion (L : List Relativizer) (R : Position → Position → Prop) : Prop :=
  ∀ p ∈ relativizable L, ∀ q, p ≤ q → q ∈ relativizable L ∨ ∃ q' ∈ relativizable L, R q q'

instance (L : List Relativizer) (R : Position → Position → Prop) [DecidableRel R] :
    Decidable (SatisfiesHCPromotion L R) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Without promotion the constraint is the stronger one the paper rejects (p. 68): a language
relativizes an upper set of the hierarchy. -/
theorem satisfiesHCPromotion_bot_iff {L : List Relativizer} :
    SatisfiesHCPromotion L ⊥ ↔ IsUpperSet (relativizable L : Set Position) :=
  ⟨fun h _ _ hpq hp ↦ (h _ hp _ hpq).resolve_right fun ⟨_, _, h⟩ ↦ h,
    fun h _ hp _ hpq ↦ .inl (h hpq hp)⟩

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
constraint (p. 68), and satisfies the constraint with promotion, its object voice promoting the
direct object to subject (p. 69). -/
theorem tobaBatak_needs_promotion :
    ¬ SatisfiesHCPromotion tobaBatak ⊥ ∧
      SatisfiesHCPromotion tobaBatak (Promotes TobaBatak.voices tobaBatakRole) :=
  ⟨satisfiesHCPromotion_bot_iff.not.2 fun h ↦
    absurd (h (show Position.indirectObject ≤ .directObject by decide) (by decide)) (by decide),
    by decide⟩

/-- Toba Batak relativizes directly the subject and just the positions its voices cannot promote
(p. 69): a direct object is relativized as a promoted subject, and a noun phrase governed by a
preposition by the +case strategy. The object of comparison, on which Table 1 has no data, is
set aside. -/
theorem mem_relativizable_tobaBatak_iff {p : Position} (hp : p ≠ ⊥) :
    p ∈ relativizable tobaBatak ↔ p = ⊤ ∨ ¬ Promotes TobaBatak.voices tobaBatakRole p ⊤ := by
  revert p; decide

/-! ### Strategies by their relativized position (Section 1.3) -/

/-- Korean (Section 1.3.4, Table 1 p. 78): the −case strategy stops at obliques and a genitive
requires a retained pronoun. -/
theorem korean_genitive_retention :
    (⟨.preNominal, false⟩ : Strategy).positions korean = Icc .oblique ⊤ ∧
      ∀ r ∈ korean, r.realize .genitive = {.resumptive} := by
  decide

/-- Finnish (Section 1.3.2): the case-coding strategy of *joka* is the broader one, the
participle covering subject and direct object only, both primary. -/
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
  univ.filter fun p ↦ ∃ r ∈ L, .resumptive ∈ r.realize p

/-- "Once a language begins to retain pronouns it must do so for as long as relativization is
possible at all" (p. 92). -/
def RetainsDownward (L : List Relativizer) : Prop :=
  ∀ p ∈ retention L, ∀ q ∈ relativizable L, q ≤ p → q ∈ retention L

instance (L : List Relativizer) : Decidable (RetainsDownward L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Table 2's Arabic (p. 93): pronouns are retained everywhere but the subject. -/
theorem arabic_table2 : retention arabic = {⊤}ᶜ := by decide

/-- Every language of the sample retains pronouns downward. -/
theorem retention_verified : ∀ L ∈ sample, RetainsDownward L := by decide

end KeenanComrie1977
