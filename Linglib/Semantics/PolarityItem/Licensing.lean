/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Polarity licensing

A context licenses a polarity item when the licenser it places over the item carries the strength of
negation the item needs, after Ladusaw, Zwarts and Gajewski; when it is a modal licenser licensing
free choice and the item is a free choice item, after Kadmon and Landman and Chierchia; or when it
is a question and the item a weak negative polarity item, after van Rooy. It anti-licenses an item
when its licenser holds outright the strength that blocks it, after van der Wouden and Szabolcsi.
What each context carries is a theorem about the operators it denotes
(`Semantics/PolarityItem/LicensingContext.lean`), so what it licenses follows from what it means,
and each fragment checks the theory against the contexts its entries are attested and excluded in.

## Main declarations

* `PolarityItem.Licenser.Licenses`, `AntiLicenses`, `Admits`: licensing is a property of the
  operator over the item's position, so a study can state it of a licenser of its own.
* `PolarityItem.LicensingContext.licenses_nobody`, …: what each named context licenses, as a
  condition on the item, and the `Decidable` instances built from these lemmas by cases on the
  context, so that `decide` checks an item against any named context.

## Main results

* `Licenser.licenses_iff_carries`: an item needing a strength above weak, and not a free choice
  item, is licensed exactly by the licensers carrying that strength, so an item needing
  anti-morphic strength is licensed by clausal negation and by no other named context.
* `LicensingContext.antiLicenses_negation`: clausal negation blocks every positive polarity item,
  van der Wouden's (169).
* `Licenser.antiLicenses_iff_licenses`: a classical licenser blocks the positive polarity items of
  a class exactly where it licenses the negative polarity items of that class, the mirror image of
  van der Wouden's (181).

## References

* [ladusaw-1979]
* [kadmon-landman-1993]
* [zwarts-1998]
* [vanderwouden-1997]
* [von-fintel-1999]
* [gajewski-2011]
* [szabolcsi-2004]
* [van-rooy-2003-npi]
* [chierchia-2006]
-/

@[expose] public section

namespace PolarityItem.Licenser

open NaturalLogic Licenser

variable (L : Licenser) (e : PolarityItem)

/-- A context **licenses** an item when its licenser carries the item's licensor, licenses free
choice and the item is a free choice item, or licenses by relevance and the item is a weak negative
polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, L.Carries r) ∨ (L.LicensesFreeChoice ∧ e.IsFCI) ∨
    (L.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds outright the strength that blocks
the item. -/
def AntiLicenses : Prop := ∃ r ∈ e.antiLicensor, L.Holds r.toSignature

/-- A context **admits** an item when it licenses the item, if the item needs licensing, and does
not anti-license it. -/
def Admits : Prop := (e.IsNPI ∨ e.IsFCI → L.Licenses e) ∧ ¬ L.AntiLicenses e

variable {L e}

theorem admits_iff_licenses (h : e.antiLicensor = none) (he : e.IsNPI ∨ e.IsFCI) :
    L.Admits e ↔ L.Licenses e := by
  simp [Admits, AntiLicenses, h, he]

theorem admits_iff_not_antiLicenses (hn : ¬ e.IsNPI) (hf : ¬ e.IsFCI) :
    L.Admits e ↔ ¬ L.AntiLicenses e := by
  simp [Admits, hn, hf]

/-! ### The profiles of the licensers -/

private theorem licenses_of_carries_iff {s₀ : Negation.Strength}
    (hfc : ¬ L.LicensesFreeChoice) (hrel : ¬ L.LicensesByRelevance)
    (h : ∀ s, L.Carries s ↔ s ≤ s₀) : L.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ s₀ := by
  simp only [Licenses, h, hfc, hrel, false_and, or_false]

private theorem licenses_classical {F : OperatorFamily} {s₀ : Negation.Strength}
    (hc : L = .classical F) (hn : ¬ L.IsStrawsonUE)
    (h : ∀ s, L.Holds s.toSignature ↔ s ≤ s₀) :
    L.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ s₀ := by
  refine licenses_of_carries_iff (by rw [hc]; exact id) (by rw [hc]; exact id) fun s ↦ ?_
  rw [← h, hc, carries_classical_iff, and_iff_left (hc ▸ hn)]

private theorem licenses_weak (hfc : ¬ L.LicensesFreeChoice)
    (hrel : ¬ L.LicensesByRelevance) (hde : L.IsStrawsonDE)
    (hn : ¬ L.IsStrawsonUE) (hx : ¬ L.exhaustified.Holds .anti) :
    L.Licenses e ↔ e.licensor = some .weak := by
  rw [licenses_of_carries_iff hfc hrel fun _ ↦
    (carries_iff_eq_weak hde hn hx).trans Negation.Strength.le_weak_iff.symm]
  simp only [Negation.Strength.le_weak_iff, exists_eq_right, Option.mem_def]

private theorem antiLicenses_classical {s₀ : Negation.Strength}
    (h : ∀ s, L.Holds s.toSignature ↔ s ≤ s₀) :
    L.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ s₀ := by
  simp only [AntiLicenses, h]

private theorem not_antiLicenses (h : ¬ L.Holds .anti) : ¬ L.AntiLicenses e :=
  fun ⟨_, _, hr⟩ ↦ not_holds_toSignature h hr

private theorem licenses_modal {F : ModalFamily} (hc : L = .modal F)
    (h : L.LicensesFreeChoice) : L.Licenses e ↔ e.IsFCI := by
  refine ⟨fun hl ↦ ?_, fun hf ↦ .inr (.inl ⟨h, hf⟩)⟩
  rcases hl with ⟨r, _, hr⟩ | ⟨_, hf⟩ | ⟨hq, _⟩
  · rw [hc] at hr
    exact hr.weak.1.elim
  · exact hf
  · rw [hc] at hq
    exact False.elim hq

@[simp] theorem not_antiLicenses_modal {F : ModalFamily} (hc : L = .modal F) :
    ¬ L.AntiLicenses e :=
  not_antiLicenses (by rw [hc]; exact id)

instance [DecidablePred L.Licenses] [DecidablePred L.AntiLicenses] : DecidablePred L.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### The theory -/

/-- An item needing a strength above weak, and not a free choice item, is licensed exactly by the
contexts whose licenser carries that strength. -/
theorem licenses_iff_carries {r : Negation.Strength} (he : e.licensor = some r) (hr : r ≠ .weak)
    (hf : ¬ e.IsFCI) : L.Licenses e ↔ L.Carries r := by
  refine ⟨?_, fun h ↦ .inl ⟨r, he, h⟩⟩
  rintro (⟨s, hs, hc⟩ | ⟨_, hfc⟩ | ⟨_, hw⟩)
  · rw [he, Option.mem_def, Option.some_inj] at hs
    exact hs ▸ hc
  · exact absurd hfc hf
  · rw [he, Option.some_inj] at hw
    exact absurd hw hr

/-- A non-trivial classical context anti-licenses a class's PPIs exactly where it licenses its NPIs
(mirroring [vanderwouden-1997]'s (181)). -/
theorem antiLicenses_iff_licenses {e' : PolarityItem} {F : OperatorFamily}
    (hc : L = .classical F) (hn : ¬ L.IsStrawsonUE)
    (h : e.antiLicensor = e'.licensor) : L.AntiLicenses e ↔ L.Licenses e' := by
  unfold AntiLicenses Licenses
  rw [hc] at hn ⊢
  rw [h]
  simp only [carries_classical_iff, and_iff_left hn, LicensesFreeChoice, LicensesByRelevance,
    false_and, or_false]

/-- A context licensing an item licenses every item with a weaker licensor that is a free choice
item if the first is. -/
theorem Licenses.of_licensor_le {e' : PolarityItem} {r r' : Negation.Strength}
    (he : e.licensor = some r) (he' : e'.licensor = some r') (hr : r' ≤ r)
    (hf : e.IsFCI → e'.IsFCI) (hl : L.Licenses e) :
    L.Licenses e' := by
  rcases hl with ⟨s, hs, hc⟩ | ⟨hc, hfc⟩ | ⟨hc, hw⟩
  · rw [he, Option.mem_def, Option.some_inj] at hs
    exact .inl ⟨r', he', hc.of_le (hs ▸ hr)⟩
  · exact .inr (.inl ⟨hc, hf hfc⟩)
  · rw [he, Option.some_inj] at hw
    subst hw
    exact .inr (.inr ⟨hc, by
      rw [he']; congr; cases r' <;> first | rfl | exact absurd hr (by decide)⟩)

end PolarityItem.Licenser

namespace PolarityItem.LicensingContext

open NaturalLogic Licenser

variable {e : PolarityItem}

@[simp] theorem licenses_negation : negation.licenser.Licenses e ↔ e.IsNPI := by
  rw [licenses_classical (L := negation.licenser) (s₀ := .antiMorphic) rfl
    not_isStrawsonUE_negation fun s ↦ iff_of_true (holds_negation s) le_top]
  exact ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩,
    fun h ↦ let ⟨r, hr⟩ := Option.isSome_iff_exists.1 h; ⟨r, hr, le_top⟩⟩

@[simp] theorem antiLicenses_negation_iff : negation.licenser.AntiLicenses e ↔ e.IsPPI := by
  rw [antiLicenses_classical (s₀ := .antiMorphic) fun s ↦
    iff_of_true (holds_negation s) le_top]
  exact ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩,
    fun h ↦ let ⟨r, hr⟩ := Option.isSome_iff_exists.1 h; ⟨r, hr, le_top⟩⟩

@[simp] theorem licenses_nobody :
    nobody.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_nobody fun _ ↦ holds_nobody_iff

@[simp] theorem antiLicenses_nobody :
    nobody.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_nobody_iff

@[simp] theorem licenses_few : few.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_of_carries_iff id id fun _ ↦
    (carries_iff_eq_weak (isStrawsonDE_of_holds_anti (holds_few_iff.2 le_rfl)) not_isStrawsonUE_few
      not_holds_exhaustified_few).trans Negation.Strength.le_weak_iff.symm

@[simp] theorem antiLicenses_few : few.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_few_iff

@[simp] theorem licenses_atMost : atMost.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_of_carries_iff id id fun _ ↦
    (carries_iff_eq_weak (isStrawsonDE_of_holds_anti (holds_atMost_iff.2 le_rfl))
      not_isStrawsonUE_atMost not_holds_exhaustified_atMost).trans Negation.Strength.le_weak_iff.symm

@[simp] theorem antiLicenses_atMost :
    atMost.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_atMost_iff

@[simp] theorem licenses_universalRestrictor :
    universalRestrictor.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_universalRestrictor fun _ ↦ holds_universalRestrictor_iff

@[simp] theorem antiLicenses_universalRestrictor :
    universalRestrictor.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_universalRestrictor_iff

@[simp] theorem licenses_withoutClause :
    withoutClause.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_withoutClause fun _ ↦ holds_withoutClause_iff

@[simp] theorem antiLicenses_withoutClause :
    withoutClause.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_withoutClause_iff

@[simp] theorem licenses_beforeClause :
    beforeClause.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_beforeClause fun _ ↦ holds_beforeClause_iff

@[simp] theorem antiLicenses_beforeClause :
    beforeClause.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_beforeClause_iff

@[simp] theorem licenses_clausalComparative :
    clausalComparative.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_exceedsFamily fun _ ↦ holds_clausalComparative_iff

@[simp] theorem antiLicenses_clausalComparative :
    clausalComparative.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_clausalComparative_iff

@[simp] theorem licenses_tooTo : tooTo.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_exceedsFamily fun _ ↦ holds_tooTo_iff

@[simp] theorem antiLicenses_tooTo :
    tooTo.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_tooTo_iff

@[simp] theorem licenses_doubtVerb : doubtVerb.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .weak :=
  licenses_classical rfl not_isStrawsonUE_doubtVerb fun _ ↦ holds_doubtVerb_iff

@[simp] theorem antiLicenses_doubtVerb :
    doubtVerb.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .weak :=
  antiLicenses_classical fun _ ↦ holds_doubtVerb_iff

@[simp] theorem licenses_denyVerb :
    denyVerb.licenser.Licenses e ↔ ∃ r ∈ e.licensor, r ≤ .antiAdditive :=
  licenses_classical rfl not_isStrawsonUE_denyVerb fun _ ↦ holds_denyVerb_iff

@[simp] theorem antiLicenses_denyVerb :
    denyVerb.licenser.AntiLicenses e ↔ ∃ r ∈ e.antiLicensor, r ≤ .antiAdditive :=
  antiLicenses_classical fun _ ↦ holds_denyVerb_iff

@[simp] theorem licenses_onlyFocus : onlyFocus.licenser.Licenses e ↔ e.licensor = some .weak :=
  licenses_weak id id isStrawsonDE_onlyFocus not_isStrawsonUE_onlyFocus not_holds_onlyFocus

@[simp] theorem not_antiLicenses_onlyFocus : ¬ onlyFocus.licenser.AntiLicenses e :=
  not_antiLicenses not_holds_onlyFocus

@[simp] theorem licenses_adversative : adversative.licenser.Licenses e ↔ e.licensor = some .weak :=
  licenses_weak id id isStrawsonDE_adversative not_isStrawsonUE_adversative not_holds_adversative

@[simp] theorem not_antiLicenses_adversative : ¬ adversative.licenser.AntiLicenses e :=
  not_antiLicenses not_holds_adversative

@[simp] theorem licenses_superlative : superlative.licenser.Licenses e ↔ e.licensor = some .weak :=
  licenses_weak id id isStrawsonDE_superlative not_isStrawsonUE_superlative not_holds_superlative

@[simp] theorem not_antiLicenses_superlative : ¬ superlative.licenser.AntiLicenses e :=
  not_antiLicenses not_holds_superlative

@[simp] theorem licenses_conditionalAntecedent :
    conditionalAntecedent.licenser.Licenses e ↔ e.licensor = some .weak :=
  licenses_weak id id isStrawsonDE_conditionalAntecedent not_isStrawsonUE_conditionalAntecedent
    not_holds_conditionalAntecedent

@[simp] theorem not_antiLicenses_conditionalAntecedent :
    ¬ conditionalAntecedent.licenser.AntiLicenses e :=
  not_antiLicenses not_holds_conditionalAntecedent

@[simp] theorem licenses_sinceTemporal :
    sinceTemporal.licenser.Licenses e ↔ e.licensor = some .weak :=
  licenses_weak id id isStrawsonDE_sinceTemporal not_isStrawsonUE_sinceTemporal
    not_holds_sinceTemporal

@[simp] theorem not_antiLicenses_sinceTemporal : ¬ sinceTemporal.licenser.AntiLicenses e :=
  not_antiLicenses not_holds_sinceTemporal

@[simp] theorem licenses_question : question.licenser.Licenses e ↔ e.licensor = some .weak := by
  refine ⟨fun h ↦ ?_, fun h ↦ .inr (.inr ⟨Licenser.licensesByRelevance_question, h⟩)⟩
  rcases h with ⟨r, _, hr⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exact hr.weak.1.elim
  · exact False.elim h
  · exact h

@[simp] theorem not_antiLicenses_question : ¬ question.licenser.AntiLicenses e :=
  not_antiLicenses id

@[simp] theorem licenses_modalPossibility : modalPossibility.licenser.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_modalPossibility

@[simp] theorem licenses_modalNecessity : modalNecessity.licenser.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_imperative : imperative.licenser.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_generic : generic.licenser.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem licenses_freeRelative : freeRelative.licenser.Licenses e ↔ e.IsFCI :=
  licenses_modal rfl licensesFreeChoice_necessityFamily

@[simp] theorem not_antiLicenses_modalPossibility : ¬ modalPossibility.licenser.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_modalNecessity : ¬ modalNecessity.licenser.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_imperative : ¬ imperative.licenser.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_generic : ¬ generic.licenser.AntiLicenses e :=
  not_antiLicenses_modal rfl

@[simp] theorem not_antiLicenses_freeRelative : ¬ freeRelative.licenser.AntiLicenses e :=
  not_antiLicenses_modal rfl

/-! ### Deciding licensing at the named contexts

What a named context licenses and anti-licenses is decided by the item, through the lemmas
above. -/

instance (c : LicensingContext) : DecidablePred c.licenser.Licenses := fun _ ↦
  match c with
  | negation => decidable_of_iff' _ licenses_negation
  | nobody => decidable_of_iff' _ licenses_nobody
  | few => decidable_of_iff' _ licenses_few
  | atMost => decidable_of_iff' _ licenses_atMost
  | universalRestrictor => decidable_of_iff' _ licenses_universalRestrictor
  | withoutClause => decidable_of_iff' _ licenses_withoutClause
  | beforeClause => decidable_of_iff' _ licenses_beforeClause
  | clausalComparative => decidable_of_iff' _ licenses_clausalComparative
  | tooTo => decidable_of_iff' _ licenses_tooTo
  | doubtVerb => decidable_of_iff' _ licenses_doubtVerb
  | denyVerb => decidable_of_iff' _ licenses_denyVerb
  | onlyFocus => decidable_of_iff' _ licenses_onlyFocus
  | adversative => decidable_of_iff' _ licenses_adversative
  | superlative => decidable_of_iff' _ licenses_superlative
  | conditionalAntecedent => decidable_of_iff' _ licenses_conditionalAntecedent
  | sinceTemporal => decidable_of_iff' _ licenses_sinceTemporal
  | question => decidable_of_iff' _ licenses_question
  | modalPossibility => decidable_of_iff' _ licenses_modalPossibility
  | modalNecessity => decidable_of_iff' _ licenses_modalNecessity
  | imperative => decidable_of_iff' _ licenses_imperative
  | generic => decidable_of_iff' _ licenses_generic
  | freeRelative => decidable_of_iff' _ licenses_freeRelative

instance (c : LicensingContext) : DecidablePred c.licenser.AntiLicenses := fun _ ↦
  match c with
  | negation => decidable_of_iff' _ antiLicenses_negation_iff
  | nobody => decidable_of_iff' _ antiLicenses_nobody
  | few => decidable_of_iff' _ antiLicenses_few
  | atMost => decidable_of_iff' _ antiLicenses_atMost
  | universalRestrictor => decidable_of_iff' _ antiLicenses_universalRestrictor
  | withoutClause => decidable_of_iff' _ antiLicenses_withoutClause
  | beforeClause => decidable_of_iff' _ antiLicenses_beforeClause
  | clausalComparative => decidable_of_iff' _ antiLicenses_clausalComparative
  | tooTo => decidable_of_iff' _ antiLicenses_tooTo
  | doubtVerb => decidable_of_iff' _ antiLicenses_doubtVerb
  | denyVerb => decidable_of_iff' _ antiLicenses_denyVerb
  | onlyFocus => isFalse not_antiLicenses_onlyFocus
  | adversative => isFalse not_antiLicenses_adversative
  | superlative => isFalse not_antiLicenses_superlative
  | conditionalAntecedent => isFalse not_antiLicenses_conditionalAntecedent
  | sinceTemporal => isFalse not_antiLicenses_sinceTemporal
  | question => isFalse not_antiLicenses_question
  | modalPossibility => isFalse not_antiLicenses_modalPossibility
  | modalNecessity => isFalse not_antiLicenses_modalNecessity
  | imperative => isFalse not_antiLicenses_imperative
  | generic => isFalse not_antiLicenses_generic
  | freeRelative => isFalse not_antiLicenses_freeRelative

/-- Admission at a named context is decided without computing its licenser. -/
instance (c : LicensingContext) : DecidablePred c.licenser.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Clausal negation blocks every positive polarity item, since its licenser holds the top of the
chain ([vanderwouden-1997]'s (169)). -/
theorem antiLicenses_negation (h : e.IsPPI) : negation.licenser.AntiLicenses e :=
  antiLicenses_negation_iff.mpr h

end PolarityItem.LicensingContext
