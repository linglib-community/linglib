module

public import Linglib.Semantics.Modality.Typology
public import Linglib.Data.Examples.Matthewson2013
public import Linglib.Fragments.Gitksan.Modals
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.Statimcets.Modals
public import Linglib.Fragments.Javanese.Paciran.Modals
public import Studies.Condoravdi2002
public import Studies.Deal2011

/-!
# Matthewson (2013): Gitksan Modals

This file formalizes the description of the Gitksan modal system in Matthewson (2013). Gitksan
is a mixed system (Fig. 1): every modal is specified for modality type, epistemic or
circumstantial, and modal strength is encoded among the circumstantial modals, *da'aḵhlxw* and
*anooḵ* for possibility against *sgi* for (weak) necessity, but not among the epistemic clitics
*ima('a)* and *g̱at*, which are compatible with necessity and possibility contexts alike
(Peterson 2010). With the paper's lexical forces, existential for all but *sgi*,
Deal's account of modals without scales predicts every modal's uses: the epistemics
share a force and so form no scale, and are used for both, while *sgi* is the scalemate of
*da'aḵhlxw* and *anooḵ*, and each circumstantial modal is used for its own force. The system
fills the empty diagonal of the classification of modal systems
by selectivity for type and for strength (Fig. 2), whose other cells English, St'át'imcets and
Javanese occupy in the fragments.

Each modal's force and flavours predict its judgments in the paper's contexts, with one
exception: *sgi* is rejected in the sneeze case, pure circumstantial strong necessity, though
volunteered for *we must all die*, of the same force and flavour. No set of force-flavour pairs
predicts the gap, so it is not one of modal strength, and the paper suggests *sgi* needs a
non-empty ordering source.

Gitksan modals are not inherently future-oriented, against the English analysis of
Condoravdi (2002): the prospective *dim* is present exactly when the prejacent is
future-oriented, and it is obligatory with the circumstantial modals because they are
future-oriented. Every cell of Fig. 4, perspective by orientation, is attested. The
circumstantial possibility modal has no actuality entailment, its obligatory *dim* keeping it
out of the perfective configuration of Hacquard (2006).

## Implementation notes

* The paper is agnostic between Peterson's analysis of *ima('a)* as a possibility modal
  strengthened by an ordering source and a possibility modal without a scale, as Deal (2011)
  analyses Nez Perce *o'qa*, the negation diagnostic (30) not separating them, and adopts what
  the two share, an existential quantifier over worlds. The prediction of the modals' uses
  follows Deal's mechanism, which the paper raises for the circumstantial modals
  (§5.1); forces are compared on Fig. 1's two columns, weak necessity counting as necessity.
* The rows record the paper's flavour labels; its pure circumstantial and teleological readings
  are the library's circumstantial flavour. A row's force is recorded only where the paper
  labels the context's strength.
* The primed rows are the *dim*-less variants that the paper's #(dim) marks as infelicitous.
* Fig. 2's Javanese cell is checked on the Paciran Javanese inventory of Vander Klok (2013).
  Fig. 3 summarizes an earlier description by Vander Klok, whose possibility modals *ento* and
  *mungkin* are not in that inventory.

## References

* [matthewson-2013]
* [peterson-2010]
* [deal-2011]
* [condoravdi-2002]
* [hacquard-2006]
* [rullmann-matthewson-davis-2008]
* [vander-klok-2013a]
-/

@[expose] public section

namespace Matthewson2013

open Modality Gitksan

/-! ### The modal system (Fig. 1) -/

/-- `lexicalForce m` is the force the paper assigns to `m`. *ima('a)* and *g̱at* introduce an
existential quantifier over worlds (§3.1–3.2), *da'aḵhlxw* and *anooḵ* are possibility modals,
and *sgi* is a (weak) necessity modal (§4). -/
def lexicalForce (m : ModalItem) : ModalForce := if m = sgi then .necessity else .possibility

-- Fig. 1 [deal-2011]
theorem forces_usable : ∀ m ∈ modals, ∀ g, g.classical ∈ m.classical.forces ↔
    Deal2011.Usable .positive (lexicalForce m) (ModalItem.HasScalemate lexicalForce modals m)
      g := by
  decide

theorem hasScalemate_iff : ∀ m ∈ modals,
    ModalItem.HasScalemate lexicalForce modals m ↔ m.Circumstantial := by
  decide

/-! ### Rows -/

/-- `modalTable` keys the fragment's modals by their forms. -/
def modalTable : List (String × ModalItem) := modals.map fun m ↦ (m.form, m)

/-- `forceTable` maps a row's force label to the force its context supports. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("weak necessity", .weakNecessity), ("necessity", .necessity)]

/-- `flavorTable` maps a row's flavour label to a flavour, reading the pure circumstantial and
teleological labels as circumstantial. -/
def flavorTable : List (String × ModalFlavor) :=
  [("epistemic", .epistemic), ("deontic", .deontic), ("bouletic", .bouletic),
    ("circumstantial", .circumstantial), ("pure circumstantial", .circumstantial),
    ("teleological", .circumstantial)]

theorem rows_resolve :
    ∀ e ∈ Examples.all, ∀ s ∈ e.feature? "modal", s ≠ "dim" →
      (e.parse? "modal" modalTable).isSome := by
  decide

/-! ### Force and flavour (§3, §4) -/

-- (66), (79), (80)
theorem rows_meaning :
    ∀ e ∈ Examples.all, e.feature? "test" ≠ some "sneeze" →
      ∀ m ∈ e.parse? "modal" modalTable, ∀ fo ∈ e.parse? "force" forceTable,
        ∀ fl ∈ e.parse? "flavor" flavorTable,
          (e.judgment = .acceptable ↔ (fo, fl) ∈ m.meaning) := by
  decide

-- (89), (90), (92), (100)
theorem sgi_attested :
    (∀ fo ∈ sgi.forces, ∃ e ∈ Examples.all, e.parse? "modal" modalTable = some sgi ∧
      e.parse? "force" forceTable = some fo ∧ e.judgment = .acceptable) ∧
    ∀ fl ∈ sgi.flavors, ∃ e ∈ Examples.all, e.parse? "modal" modalTable = some sgi ∧
      e.parse? "flavor" flavorTable = some fl ∧ e.judgment = .acceptable := by
  decide

-- (95), (96)
theorem sneeze_rows :
    ∀ e ∈ Examples.all, e.feature? "test" = some "sneeze" →
      (e.judgment = .acceptable ↔ e.feature? "modal" ≠ some "sgi") := by
  decide

-- (96), (100)
theorem sneeze_gap :
    ¬ ∃ M : Finset ForceFlavor, ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some sgi →
      ∀ fo ∈ e.parse? "force" forceTable, ∀ fl ∈ e.parse? "flavor" flavorTable,
        (e.judgment = .acceptable ↔ (fo, fl) ∈ M) := by
  rintro ⟨M, hM⟩
  have h96 := hM Examples.ex96 (by decide) (by decide) .necessity (by decide) .circumstantial
    (by decide)
  have h100 := hM Examples.ex100a (by decide) (by decide) .necessity (by decide) .circumstantial
    (by decide)
  exact absurd (h96.2 (h100.1 rfl)) (by decide)

/-! ### Modal systems (Fig. 2) -/

/-- An inventory selects modality type when each of its modals is epistemic or circumstantial. -/
def TypeSelective (L : List ModalItem) : Prop := ∀ m ∈ L, m.Epistemic ∨ m.Circumstantial

/-- An inventory selects modal strength when none of its modals varies between necessity and
possibility, weak necessity counting as necessity. -/
def StrengthSelective (L : List ModalItem) : Prop := ∀ m ∈ L, ¬ m.classical.VariesForce

instance (L : List ModalItem) : Decidable (TypeSelective L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _ ∨ _))

instance (L : List ModalItem) : Decidable (StrengthSelective L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ¬ _))

/-- A mixed system selects type throughout and strength among its circumstantial modals only. -/
def Mixed (L : List ModalItem) : Prop :=
  TypeSelective L ∧ StrengthSelective (L.filter (·.Circumstantial)) ∧
    ¬ StrengthSelective (L.filter (·.Epistemic))

instance (L : List ModalItem) : Decidable (Mixed L) := inferInstanceAs (Decidable (_ ∧ _ ∧ ¬ _))

theorem gitksan_mixed : Mixed modals := by decide

-- Fig. 2, Fig. 3 [rullmann-matthewson-davis-2008]
theorem fig2 :
    (StrengthSelective (English.Auxiliaries.modals.map ModalAuxiliary.toModalItem) ∧
        ¬ TypeSelective (English.Auxiliaries.modals.map ModalAuxiliary.toModalItem)) ∧
      (TypeSelective Statimcets.modals ∧
        ¬ StrengthSelective Statimcets.modals) ∧
      TypeSelective Javanese.Paciran.modals ∧
        StrengthSelective Javanese.Paciran.modals := by
  decide

/-! ### Modal–temporal interaction (§3.3, §4, §5.3, Fig. 4) -/

/-- `orientationOf` reads the orientation a row records. -/
def orientationOf : String → Option TemporalOrientation
  | "past" => some .past
  | "present" => some .present
  | "future" => some .future
  | _ => none

/-- `perspectiveOf` reads the perspective a row records. -/
def perspectiveOf : String → Option TemporalPerspective
  | "past" => some .past
  | "present" => some .present
  | _ => none

-- (38), (48), (53), (56), (73), (83)
theorem dim_rows :
    ∀ e ∈ Examples.all, ∀ o ∈ (e.feature? "orientation").bind orientationOf,
      (e.judgment = .acceptable ↔ (e.feature? "prospective" = some "true" ↔ o = .future)) := by
  decide

-- §4
theorem circumstantial_future :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable, m.Circumstantial →
      ∀ o ∈ (e.feature? "orientation").bind orientationOf, o = .future := by
  decide

theorem dim_circumstantial :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable, m.Circumstantial →
      ∀ o ∈ (e.feature? "orientation").bind orientationOf,
        (e.judgment = .acceptable ↔ e.feature? "prospective" = some "true") := by
  intro e he m hm hc o ho
  simpa [circumstantial_future e he m hm hc o ho] using dim_rows e he o ho

-- Fig. 4
theorem fig4 :
    ∀ p : TemporalPerspective, ∀ o : TemporalOrientation, ∃ e ∈ Examples.all,
      e.parse? "modal" modalTable = some imaa ∧
        (e.feature? "perspective").bind perspectiveOf = some p ∧
        (e.feature? "orientation").bind orientationOf = some o ∧ e.judgment = .acceptable := by
  decide

-- (35), (39) [condoravdi-2002]
theorem unmarked_orientation :
    Condoravdi2002.Scope.modal.orientation = .future ∧
      ∀ e ∈ Examples.all, e.feature? "prospective" = some "false" → e.judgment = .acceptable →
        ∀ o ∈ (e.feature? "orientation").bind orientationOf, o ≠ .future :=
  ⟨rfl, fun e he hp ha o ho hf ↦ by simpa [hp, hf] using (dim_rows e he o ho).1 ha⟩

-- (62)
theorem no_actuality_entailment :
    ∀ e ∈ Examples.all, e.feature? "actualityEntailment" = some "false" →
      e.parse? "modal" modalTable = some daakhlxw ∧ e.feature? "prospective" = some "true" ∧
        e.judgment = .acceptable := by
  decide

end Matthewson2013
