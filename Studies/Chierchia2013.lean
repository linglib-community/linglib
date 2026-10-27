module

public import Linglib.Logic.Natural.Soundness
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Fragments.Romance.Italian.PolarityItems
public import Linglib.Data.Examples.Chierchia2013

/-!
# Chierchia (2013): Logic in Grammar

This file formalizes the opening chapter of Chierchia's book, where the preferred reading of
*or* and the distribution of *any* and *ever* are shown to track one logical property of a
position. *Or* is exclusive in an upward-entailing position and inclusive in a
downward-entailing one, because Maximize Strength adds the not-both implicature only where it
strengthens, and an implicature strengthens under a monotone embedding and weakens under an
antitone one. *Any* and *ever* are grammatical in the downward-entailing positions and out
elsewhere, because their subdomain alternatives are obligatorily active and must be
exhaustified: under an antitone context every subdomain alternative is entailed and
exhaustification is vacuous, while at the existential itself no witness is entailed and
exhaustification is a contradiction. *Any* alone extends to the free-choice positions, a
possibility modal or an imperative, the divide between it and *ever* and between Italian
*qualsiasi* and *alcuno*. The positions are the paper's easy and hard columns, the hard column
being the licensing contexts whose licensers fix their polarity, and the readings and judgments
are rows: the theorems derive each reading from Maximize Strength and each judgment from the
licensing relation applied to the Fragment entries, and every row must name its position.

## References

* [chierchia-2013]
* [ladusaw-1979]
-/

@[expose] public section

namespace Chierchia2013

open NaturalLogic PolarityItem Exhaustification

/-! ### Maximize Strength -/

section MaximizeStrength

variable {W : Type*} (p q : Set W)

/-- *Or* has an inclusive and an exclusive reading. -/
inductive DisjunctionReading where
  | inclusive
  | exclusive
  deriving DecidableEq, Repr

/-- A reading assigns to *p or q* the disjunction, or the disjunction with the not-both
implicature added. -/
def DisjunctionReading.denotation : DisjunctionReading → Set W
  | .inclusive => p ∪ q
  | .exclusive => (p ∪ q) \ (p ∩ q)

/-- The name of a reading in the example rows. -/
def DisjunctionReading.key : DisjunctionReading → String
  | .inclusive => "inclusive"
  | .exclusive => "exclusive"

theorem exclusive_subset_inclusive :
    DisjunctionReading.exclusive.denotation p q ⊆ DisjunctionReading.inclusive.denotation p q :=
  Set.sdiff_subset

/-- By Maximize Strength a reading is preferred in a position when the position's embedding of
it is at least as strong as its embedding of the other reading. -/
def IsStrongest (C : Set W → Set W) (r : DisjunctionReading) : Prop :=
  ∀ r' : DisjunctionReading, C (r.denotation p q) ⊆ C (r'.denotation p q)

theorem isStrongest_exclusive {C : Set W → Set W} (hC : Monotone C) :
    IsStrongest p q C .exclusive
  | .inclusive => hC (exclusive_subset_inclusive p q)
  | .exclusive => subset_rfl

theorem isStrongest_inclusive {C : Set W → Set W} (hC : Antitone C) :
    IsStrongest p q C .inclusive
  | .inclusive => subset_rfl
  | .exclusive => hC (exclusive_subset_inclusive p q)

/-- The reading Maximize Strength selects from the polarity of a position; a non-monotone
position selects neither. -/
def maximizeStrength : SignType → Option DisjunctionReading
  | .pos => some .exclusive
  | .neg => some .inclusive
  | .zero => none

theorem isStrongest_maximizeStrength {φ : Signature} {C : Set W → Set W} (hφ : φ.SoundFor C) :
    ∀ r ∈ maximizeStrength φ.sign, IsStrongest p q C r := by
  intro r hr
  cases hpol : φ.sign <;> rw [hpol] at hr <;>
    simp only [maximizeStrength, Option.mem_def, Option.some.injEq, reduceCtorEq] at hr
  · exact hr ▸ isStrongest_inclusive p q (hφ.antitone hpol)
  · exact hr ▸ isStrongest_exclusive p q (hφ.monotone hpol)

end MaximizeStrength

/-! ### Exhaustifying obligatory subdomain alternatives -/

section Exhaustification

variable {W E : Type*} (D : Finset E) (P : E → Set W)

theorem exh_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    exh (C '' supClosure (P '' D)) (C (⋃ a ∈ D, P a)) = C (⋃ a ∈ D, P a) :=
  exh_eq_self <| by
    rintro _ ⟨_, hq, rfl⟩
    obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
    exact hC (Set.biUnion_subset_biUnion_left hS)

theorem exh_supClosure_eq_empty (h : ∀ a ∈ D, ¬ (⋃ b ∈ D, P b) ⊆ P a) :
    exh (supClosure (P '' D)) (⋃ a ∈ D, P a) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun w ⟨hw, hall⟩ ↦ ?_
  obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
  exact h a ha (hall _ (subset_supClosure (Set.mem_image_of_mem P ha)) hPa)

end Exhaustification

/-! ### The positions -/

/-- The paper's positions. In the easy column *or* is exclusive and *any* is out, in the hard
column of [ladusaw-1979]'s licensing contexts *or* is inclusive and *any* is in, and in the
free-choice positions *any* alone survives. -/
inductive Position where
  /-- A positive sentence. -/
  | matrix
  /-- The consequent of a conditional. -/
  | conditionalConsequent
  /-- The second argument of *every*. -/
  | everyScope
  /-- The scope of a positive quantifier such as *somebody*. -/
  | positiveQuantifierScope
  | conditionalAntecedent
  /-- The first argument of *every*. -/
  | universalRestrictor
  | negation
  | nobody
  /-- The complement of *doubt*. -/
  | doubtVerb
  | modalPossibility
  | imperative
  deriving DecidableEq, Repr

/-- The licensing context a position is, if it is one. -/
def Position.context : Position → Option LicensingContext
  | .conditionalAntecedent => some .conditionalAntecedent
  | .universalRestrictor => some .universalRestrictor
  | .negation => some .negation
  | .nobody => some .nobody
  | .doubtVerb => some .doubtVerb
  | .modalPossibility => some .modalPossibility
  | .imperative => some .imperative
  | .matrix | .conditionalConsequent | .everyScope | .positiveQuantifierScope => none

theorem carries_weak_conditionalAntecedent :
    LicensingContext.conditionalAntecedent.licenser.Carries .weak :=
  ⟨LicensingContext.isStrawsonDE_conditionalAntecedent,
    LicensingContext.not_isStrawsonUE_conditionalAntecedent⟩

theorem carries_weak_universalRestrictor :
    LicensingContext.universalRestrictor.licenser.Carries .weak :=
  Licenser.carries_classical_iff.2 ⟨(LicensingContext.holds_universalRestrictor_iff (s := .weak)).2
    (by decide), LicensingContext.not_isStrawsonUE_universalRestrictor⟩

theorem carries_weak_negation : LicensingContext.negation.licenser.Carries .weak :=
  Licenser.carries_classical_iff.2
    ⟨LicensingContext.holds_negation .weak, LicensingContext.not_isStrawsonUE_negation⟩

theorem carries_weak_nobody : LicensingContext.nobody.licenser.Carries .weak :=
  Licenser.carries_classical_iff.2 ⟨(LicensingContext.holds_nobody_iff (s := .weak)).2 (by decide),
    LicensingContext.not_isStrawsonUE_nobody⟩

theorem carries_weak_doubtVerb : LicensingContext.doubtVerb.licenser.Carries .weak :=
  Licenser.carries_classical_iff.2
    ⟨LicensingContext.holds_doubtVerb_iff.2 le_rfl, LicensingContext.not_isStrawsonUE_doubtVerb⟩

theorem not_carries_weak_modalPossibility :
    ¬ LicensingContext.modalPossibility.licenser.Carries .weak := fun h ↦ h.1

theorem not_carries_weak_imperative : ¬ LicensingContext.imperative.licenser.Carries .weak :=
  fun h ↦ h.1

/-- A position is downward entailing when it is a licensing context whose licenser carries weak
strength. -/
def Position.Downward (p : Position) : Prop := ∃ c ∈ p.context, c.licenser.Carries .weak

instance : DecidablePred Position.Downward
  | .conditionalAntecedent => isTrue ⟨_, rfl, carries_weak_conditionalAntecedent⟩
  | .universalRestrictor => isTrue ⟨_, rfl, carries_weak_universalRestrictor⟩
  | .negation => isTrue ⟨_, rfl, carries_weak_negation⟩
  | .nobody => isTrue ⟨_, rfl, carries_weak_nobody⟩
  | .doubtVerb => isTrue ⟨_, rfl, carries_weak_doubtVerb⟩
  | .modalPossibility => isFalse fun ⟨_, h, hc⟩ ↦
      not_carries_weak_modalPossibility (Option.some_inj.1 h ▸ hc)
  | .imperative => isFalse fun ⟨_, h, hc⟩ ↦ not_carries_weak_imperative (Option.some_inj.1 h ▸ hc)
  | .matrix | .conditionalConsequent | .everyScope | .positiveQuantifierScope =>
    isFalse fun ⟨_, h, _⟩ ↦ nomatch h

/-- A downward-entailing position is antitone, any other upward entailing. -/
def Position.polarity (p : Position) : SignType := if p.Downward then -1 else 1

/-- A position licenses an item when it is a licensing context that licenses it. -/
def Position.Licenses (p : Position) (e : PolarityItem) : Prop :=
  ∃ c ∈ p.context, c.licenser.Licenses e

theorem Position.licenses_iff {p : Position} {c : LicensingContext} (h : p.context = some c)
    {e : PolarityItem} : p.Licenses e ↔ c.licenser.Licenses e := by
  simp [Position.Licenses, h]

instance : ∀ p : Position, DecidablePred p.Licenses
  | .conditionalAntecedent | .universalRestrictor | .negation | .nobody | .doubtVerb
  | .modalPossibility | .imperative => fun _ ↦ decidable_of_iff' _ (Position.licenses_iff rfl)
  | .matrix | .conditionalConsequent | .everyScope | .positiveQuantifierScope =>
    fun _ ↦ isFalse fun ⟨_, h, _⟩ ↦ nomatch h

theorem licenses_ever_of_downward (pos : Position) (h : pos.polarity = -1) :
    pos.Licenses English.PolarityItems.ever := by
  by_cases hd : pos.Downward
  · obtain ⟨c, hc, hw⟩ := hd
    exact ⟨c, hc, .inl ⟨.weak, rfl, hw⟩⟩
  · simp [Position.polarity, hd] at h

theorem licenses_any_not_ever_iff (c : LicensingContext) :
    c.licenser.Licenses English.PolarityItems.any ∧
        ¬ c.licenser.Licenses English.PolarityItems.ever ↔
      c.licenser.LicensesFreeChoice := by
  have hfc : c.licenser.LicensesFreeChoice →
      ¬ c.licenser.Carries .weak ∧ ¬ c.licenser.LicensesByRelevance := by
    generalize c.licenser = L
    cases L with
    | modal => exact fun _ ↦ ⟨fun h ↦ h.1, id⟩
    | classical | scalar | strawson | question => exact fun h ↦ (h : False).elim
  have ha : c.licenser.Licenses English.PolarityItems.any ↔ c.licenser.Carries .weak ∨
      c.licenser.LicensesFreeChoice ∨ c.licenser.LicensesByRelevance := by
    simp [PolarityItem.Licenser.Licenses, English.PolarityItems.any, PolarityItem.IsFCI]
  have he : c.licenser.Licenses English.PolarityItems.ever ↔ c.licenser.Carries .weak ∨
      c.licenser.LicensesByRelevance := by
    simp [PolarityItem.Licenser.Licenses, English.PolarityItems.ever, PolarityItem.IsFCI]
  rw [ha, he]
  refine ⟨fun ⟨h, hn⟩ ↦ h.elim (fun h' ↦ absurd (.inl h') hn) fun h' ↦
    h'.resolve_right fun h'' ↦ hn (.inr h''), fun h ↦ ⟨.inr (.inl h), ?_⟩⟩
  rintro (h' | h')
  exacts [(hfc h).1 h', (hfc h).2 h']

/-! ### The rows -/

/-- The position a row names. -/
def Position.ofKey : String → Option Position
  | "matrix" => some .matrix
  | "conditionalConsequent" => some .conditionalConsequent
  | "everyScope" => some .everyScope
  | "positiveQuantifierScope" => some .positiveQuantifierScope
  | "conditionalAntecedent" => some .conditionalAntecedent
  | "universalRestrictor" => some .universalRestrictor
  | "negation" => some .negation
  | "nobody" => some .nobody
  | "doubtVerb" => some .doubtVerb
  | "modalPossibility" => some .modalPossibility
  | "imperative" => some .imperative
  | _ => none

/-- The Fragment entry a row names. -/
noncomputable def item : String → Option PolarityItem
  | "any" => some English.PolarityItems.any
  | "ever" => some English.PolarityItems.ever
  | "alcuno" => some Italian.PolarityItems.alcuno
  | "qualsiasi" => some Italian.PolarityItems.qualsiasi
  | _ => none

theorem or_rows :
    ∀ e ∈ Examples.all, e.feature? "item" = some "or" → e.feature? "forced" = none →
      ∃ pos ∈ (e.feature? "position").bind Position.ofKey,
        e.feature? "reading" = (maximizeStrength pos.polarity).map DisjunctionReading.key := by
  decide +kernel

theorem exclusive_under_nobody_forced :
    ∃ e ∈ Examples.all, e.feature? "forced" = some "true" ∧
      e.feature? "position" = some "nobody" ∧ e.feature? "reading" = some "exclusive" := by
  decide

theorem polarity_rows :
    ∀ e ∈ Examples.all, e.feature? "item" ≠ some "or" →
      ∃ i ∈ (e.feature? "item").bind item, ∃ pos ∈ (e.feature? "position").bind Position.ofKey,
        (e.judgment = .acceptable ↔ pos.Licenses i) := by
  decide +kernel

end Chierchia2013
