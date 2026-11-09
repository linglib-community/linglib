/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Polarity licensing

A context *licenses* a polarity item when the licenser it places over the item carries the
strength of negation the item needs, after Ladusaw, Zwarts and Gajewski; when it is a modal
licenser licensing free choice and the item is a free choice item, after Kadmon and Landman and
Chierchia; or when it is a question and the item a weak negative polarity item, after van Rooy. It
*anti-licenses* an item when its licenser holds outright the strength that blocks it, after van der
Wouden and Szabolcsi. A non-trivial classical context [blocks the positive polarity items of a
strength exactly where it licenses the negative
ones](##PolarityItem.Licenser.antiLicenses_iff_licenses), and an antimorphic context [blocks every
positive polarity item](##PolarityItem.Licenser.antiLicenses_iff_isPPI).

## TODO

* `PolarityItem.Acceptable` in `Environment.lean` restates `Admits` but blocks by what the operator
  carries rather than holds; the two differ only for strong positive polarity items under
  presuppositional licensers, which no entry records.

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

open NaturalLogic

variable (L : Licenser) (e : PolarityItem)

/-- A context **licenses** an item when its licenser carries the item's licensor, licenses free
choice and the item is a free choice item, or licenses by relevance and the item is a weak negative
polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, L.Carries r) ∨ (L.LicensesFreeChoice ∧ e.IsFCI) ∨
    (L.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds outright the strength that blocks
the item. -/
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
