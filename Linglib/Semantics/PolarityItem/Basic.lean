/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Negation.Strength

/-!
# Polarity items

A *polarity item* is a lexical item with a defective distribution, graded by Zwarts's strengths of
negation: a negative polarity item needs at least some strength and a positive polarity item is
blocked by at least some strength, so that Dutch *ooit* 'ever', having both, is bipolar. A context
*licenses* an item when the licenser it places over the item carries the strength the item needs,
licenses free choice and the item is a free choice item, or is a question and the item a weak
negative polarity item; it *anti-licenses* an item when its licenser holds the blocking strength
outright. A non-trivial classical context [blocks the positive polarity items of a strength exactly
where it licenses the negative ones](##PolarityItem.Licenser.antiLicenses_iff_licenses), and an
antimorphic context [blocks them all](##PolarityItem.Licenser.antiLicenses_iff_isPPI).

## Implementation notes

* Licensing reads the meaning modulo presupposition and with its direct implicature, after von
  Fintel and Gajewski; anti-licensing reads the plain meaning, as van der Wouden and Szabolcsi state
  it, for whom presuppositional operators such as *only* and *regret* rescue a positive polarity
  item rather than block it.
* The record also holds the contexts in which the item is attested and attested to be out, the data
  against which each fragment checks the theory.

## References

* [ladusaw-1979]
* [zwarts-1998]
* [vanderwouden-1997]
* [kadmon-landman-1993]
* [dayal-1996]
* [von-fintel-1999]
* [gajewski-2011]
* [szabolcsi-2004]
* [van-rooy-2003-npi]
* [chierchia-2006]
-/

@[expose] public section

/-- A polarity-sensitive lexical item: its form, the weakest strength of negation that licenses
it and the weakest that blocks it, whether the generic contexts license it, and the contexts in
which it is attested and attested to be out. -/
structure PolarityItem where
  /-- The surface form. -/
  form : String
  /-- The weakest strength of negation that licenses the item, if it is a negative polarity
  item. A negative concord item that needs clausemate negation carries `antiMorphic`, the
  strength of clausal negation alone. -/
  licensor : Option Negation.Strength := none
  /-- The weakest strength of negation that blocks the item, if it is a positive polarity
  item. -/
  antiLicensor : Option Negation.Strength := none
  /-- Whether the generic contexts license the item. -/
  freeChoice : Bool := false
  /-- The contexts in which the item is attested. -/
  licensingContexts : List PolarityItem.LicensingContext := []
  /-- The contexts in which the item is attested to be out. -/
  excludedContexts : List PolarityItem.LicensingContext := []

namespace PolarityItem

/-- An item is a **negative polarity item** when some strength of negation licenses it. -/
abbrev IsNPI (e : PolarityItem) : Prop := e.licensor.isSome

/-- An item is a **positive polarity item** when some strength of negation blocks it. -/
abbrev IsPPI (e : PolarityItem) : Prop := e.antiLicensor.isSome

/-- An item is a **free choice item** when the generic contexts license it. -/
abbrev IsFCI (e : PolarityItem) : Prop := e.freeChoice = true

end PolarityItem

/-! ### Licensing -/

namespace PolarityItem.Licenser

open NaturalLogic

variable (L : Licenser) (e : PolarityItem)

/-- A context **licenses** an item when its licenser carries the item's licensor, licenses free
choice and the item is a free choice item, or licenses by relevance and the item is a weak negative
polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, L.Carries r) ∨ (L.LicensesFreeChoice ∧ e.IsFCI) ∨
    (L.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds outright, on its plain meaning, the
strength that blocks the item ([vanderwouden-1997]'s laws (180), [szabolcsi-2004]'s (42)). -/
def AntiLicenses : Prop := ∃ r ∈ e.antiLicensor, L.Holds r.toProjectivitySignature

/-- A context **admits** an item when it licenses the item, if the item needs licensing, and does
not anti-license it. -/
def Admits : Prop := (e.IsNPI ∨ e.IsFCI → L.Licenses e) ∧ ¬ L.AntiLicenses e

variable {L e} {e' : PolarityItem} {F : OperatorFamily} {r r' : Negation.Strength}

instance [DecidablePred L.Licenses] [DecidablePred L.AntiLicenses] : DecidablePred L.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem admits_iff_licenses (h : e.antiLicensor = none) (he : e.IsNPI ∨ e.IsFCI) :
    L.Admits e ↔ L.Licenses e := by
  simp [Admits, AntiLicenses, h, he]

theorem admits_iff_not_antiLicenses (hn : ¬ e.IsNPI) (hf : ¬ e.IsFCI) :
    L.Admits e ↔ ¬ L.AntiLicenses e := by
  simp [Admits, hn, hf]

theorem admits_of_carries (he : e.licensor = some r) (ha : e.antiLicensor = none)
    (h : L.Carries r) : L.Admits e :=
  (admits_iff_licenses ha (.inl (by simp [IsNPI, he]))).2 (.inl ⟨r, he, h⟩)

theorem admits_of_not_holds (he : e.licensor = none) (hf : ¬ e.IsFCI)
    (ha : e.antiLicensor = some r) (h : ¬ L.Holds r.toProjectivitySignature) : L.Admits e :=
  (admits_iff_not_antiLicenses (by simp [IsNPI, he]) hf).2 fun ⟨_, hr, hh⟩ ↦
    h (Option.some_inj.1 (hr.symm.trans ha) ▸ hh)

/-- An item needing a strength above weak, and not a free choice item, is licensed exactly by the
contexts whose licenser carries that strength. -/
theorem licenses_iff_carries (he : e.licensor = some r) (hr : r ≠ .weak) (hf : ¬ e.IsFCI) :
    L.Licenses e ↔ L.Carries r := by
  simp [Licenses, he, hr, hf]

theorem antiLicenses_iff_holds (he : e.antiLicensor = some r) :
    L.AntiLicenses e ↔ L.Holds r.toProjectivitySignature := by
  simp [AntiLicenses, he]

theorem Licenses.of_licensor_le (he : e.licensor = some r) (he' : e'.licensor = some r')
    (hr : r' ≤ r) (hf : e.IsFCI → e'.IsFCI) : L.Licenses e → L.Licenses e' := by
  rintro (⟨s, hs, hc⟩ | ⟨hc, hfc⟩ | ⟨hc, hw⟩)
  · obtain rfl : s = r := Option.some_inj.1 (hs.symm.trans he)
    exact .inl ⟨r', he', hc.of_le hr⟩
  · exact .inr (.inl ⟨hc, hf hfc⟩)
  · obtain rfl : r = .weak := Option.some_inj.1 (he.symm.trans hw)
    exact .inr (.inr ⟨hc, he'.trans (congrArg _ (Negation.Strength.le_weak_iff.1 hr))⟩)

/-- A non-trivial classical context blocks the positive polarity items of a strength exactly where
it licenses the negative polarity items of that strength, the mirror image of
[vanderwouden-1997]'s (181) and table (182). -/
theorem antiLicenses_iff_licenses (hn : ¬ (classical F).IsStrawsonUE)
    (h : e.antiLicensor = e'.licensor) :
    (classical F).AntiLicenses e ↔ (classical F).Licenses e' := by
  simp only [AntiLicenses, Licenses, h, carries_classical_iff, and_iff_left hn, LicensesFreeChoice,
    LicensesByRelevance, false_and, or_false]

/-- An antimorphic context blocks every positive polarity item, [vanderwouden-1997]'s (169). -/
theorem antiLicenses_iff_isPPI (h : L.Holds .antiAddMult) : L.AntiLicenses e ↔ e.IsPPI :=
  ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩, fun he ↦
    let ⟨r, hr⟩ := Option.isSome_iff_exists.1 he
    ⟨r, hr, h.toProjectivitySignature_of_le (t := .antiMorphic) le_top⟩⟩

end PolarityItem.Licenser

/-! ### Deciding licensing at the named contexts

The instances are indexed by the context rather than its licenser, so that a computable definition
deciding an item against a named context does not compute the licenser. -/

namespace PolarityItem.LicensingContext

instance (c : LicensingContext) : DecidablePred c.licenser.Licenses :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance (c : LicensingContext) : DecidablePred c.licenser.AntiLicenses :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (c : LicensingContext) : DecidablePred c.licenser.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

end PolarityItem.LicensingContext
