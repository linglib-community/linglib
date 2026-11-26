module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Feature.Person.Decomposition

/-!
# The Person Case Constraint

The Person Case Constraint restricts which combinations of indirect and direct object person a
clitic cluster can realize, the classic ban of French *me lui*. A combination is a scenario
(`Clause.Scenario`) of the indirect over the direct object, and a variety of the constraint is a
predicate on scenarios. The four varieties of the descriptive literature are `PCC.Strong`,
`PCC.Ultrastrong`, `PCC.Weak` and `PCC.MeFirst`. Each is
[upward closed](##PCC.strong_mono) in the scenario order over the person lattice, which raises
the indirect object and lowers the direct object, and Strong
[entails](##PCC.Strong.ultrastrong) Ultrastrong, which
[entails](##PCC.Ultrastrong.weak) Weak and Me-first.

## Implementation notes

Which mechanism enforces the constraint is left open: a morphological filter, φ-Agree and
perspectival semantics have all been proposed, and each account is formalized in its study and
compared there with these varieties. The literature states the varieties over combinations of
distinct persons; on a reflexive combination Ultrastrong is stated here as Strong and Me-first
as licit.

## References

* [bonet-1991]
* [nevins-2007]
* [pancheva-zubizarreta-2018]
* [coon-keine-2021]
* [deal-2024]
-/

@[expose] public section

namespace PCC

open Clause (Scenario)

variable {s t : Scenario Person}

/-! ### The varieties -/

/-- The Strong constraint: the direct object is third person. -/
def Strong (s : Scenario Person) : Prop := s.low = .third

/-- The Ultrastrong constraint: the direct object is third person, or the indirect object
outranks it on 1 > 2 > 3. -/
def Ultrastrong (s : Scenario Person) : Prop :=
  s.low = .third ∨ s.low.prominence < s.high.prominence

/-- The Weak constraint: under a third person indirect object the direct object is third
person. -/
def Weak (s : Scenario Person) : Prop := s.high = .third → s.low = .third

/-- The Me-first constraint: a first person direct object has a first person indirect object. -/
def MeFirst (s : Scenario Person) : Prop := s.low.IncludesSpeaker → s.high.IncludesSpeaker

instance : DecidablePred Strong := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Ultrastrong := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred Weak := fun _ ↦ inferInstanceAs (Decidable (_ → _))
instance : DecidablePred MeFirst := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-! ### Upward closure -/

theorem strong_mono : Monotone Strong := fun _ _ h hs ↦ eq_bot_iff.2 (h.2.trans_eq hs)

theorem ultrastrong_mono : Monotone Ultrastrong := fun _ _ h hs ↦
  hs.imp (fun hs ↦ eq_bot_iff.2 (h.2.trans_eq hs)) fun hs ↦
    (Person.prominence_mono h.2).trans_lt (hs.trans_le (Person.prominence_mono h.1))

theorem weak_mono : Monotone Weak := fun _ _ h hs hh ↦
  eq_bot_iff.2 (h.2.trans_eq (hs (eq_bot_iff.2 (h.1.trans_eq hh))))

theorem meFirst_mono : Monotone MeFirst := fun _ _ h hs hl ↦ (hs (hl.mono h.2)).mono h.1

/-- An upward closed restriction that licenses some direct object under an indirect object
licenses a third person under it. -/
theorem third_of_monotone {R : Scenario Person → Prop} (hR : Monotone R) {p q : Person}
    (h : R ⟨p, q⟩) : R ⟨p, .third⟩ :=
  hR (show (⟨p, q⟩ : Scenario Person) ≤ ⟨p, .third⟩ from ⟨le_rfl, bot_le⟩) h

/-! ### Entailments among the varieties -/

theorem strong_third (p : Person) : Strong ⟨p, .third⟩ := by revert p; decide

theorem Strong.ultrastrong (h : Strong s) : Ultrastrong s := .inl h

theorem Ultrastrong.weak : Ultrastrong s → Weak s := by revert s; decide

theorem Ultrastrong.meFirst : Ultrastrong s → MeFirst s := by revert s; decide

theorem Strong.weak (h : Strong s) : Weak s := h.ultrastrong.weak

theorem Strong.meFirst (h : Strong s) : MeFirst s := h.ultrastrong.meFirst

/-! ### The combinations of the standard tripartition -/

/-- The persons of the standard tripartition, over which the typology is stated. -/
def persons : Finset Person := {.first, .second, .third}

/-- The combinations of the standard tripartition. -/
def cliticPairs : Finset (Scenario Person) :=
  (persons ×ˢ persons).map Scenario.equivProd.symm.toEmbedding

/-- The combinations of distinct persons, without the reflexive diagonal. -/
def distinctPairs : Finset (Scenario Person) :=
  persons.offDiag.map Scenario.equivProd.symm.toEmbedding

end PCC
