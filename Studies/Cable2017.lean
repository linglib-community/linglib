module

public import Studies.Deal2011
public import Linglib.Fragments.Tlingit.Modals
public import Linglib.Fragments.Statimcets.Modals
public import Linglib.Fragments.Washo.Modals

/-!
# Cable (2017): The Expression of Modality in Tlingit: A Paucity of Grammatical Devices

Cable examines how Tlingit expresses epistemic, deontic and circumstantial modality of each
force. Only three kinds of expression have a dedicated modal meaning, each with one force and
one flavor: the dubitative particles express epistemic possibility, the potential mode
circumstantial possibility and the future mode circumstantial necessity. No expression encodes
epistemic necessity, deontic possibility or deontic necessity; speakers convey these indirectly.

Speakers translate an English epistemic necessity claim with a dubitative, but never a
circumstantial necessity claim with the potential mode. Cable explains the contrast with Deal's
account of Nez Perce *o'qa*: a possibility modal serves for necessity in an upward-entailing
context when no stronger modal shares its flavor, and the future mode is the potential mode's
scalemate while the dubitatives have none. The dubitatives thus side with *o'qa*, inherently
weak modals without a strong counterpart, and not with St'át'imcets *k'a* or Washo *-eʔ*,
whose meanings vary in force. The same account makes the past potential weak in the
restriction of a universal: *ldakát ḵwax̱aayi át* is 'everything I could have eaten', never
'everything I would have eaten'.

## Main statements

* `expressed_iff`: Tlingit encodes epistemic possibility and circumstantial possibility and
  necessity, and nothing else.
* `servesFor_necessity`: a dubitative serves for epistemic necessity, the potential mode not
  for circumstantial necessity.
* `dubitatives_fixed_force`: the dubitatives serve for both forces with one force in their
  meaning, where *k'a* and *-eʔ* have two.

## Implementation notes

* Cable's deontic flavor includes the teleological and bouletic ones, and his circumstantial
  flavor, the metaphysical one, is the library's circumstantial; no Tlingit modal is affected.
* A modal's lexical force is necessity if its meaning has necessity and possibility otherwise.
* The past potential has the potential mode's force, and the restriction of *ldakát* 'all' is
  downward-entailing, as the restriction of a universal is in Deal's account.

## References

* [cable-2017]
* [deal-2011]
* [rullmann-matthewson-davis-2008]
* [bochnak-2015b]
-/

@[expose] public section

namespace Cable2017

open Modality Deal2011 Tlingit

/-- The dubitative particles. -/
def dubitatives : List ModalItem := [gwál, gíwé, shákdé]

/-! ### The expressed categories -/

/-- A force-flavor pair is encoded by some Tlingit modal iff it is epistemic possibility,
circumstantial possibility or circumstantial necessity (§6, Table 1). -/
theorem expressed_iff (ff : ForceFlavor) :
    (∃ m ∈ Tlingit.modals, ff ∈ m.meaning) ↔ ff ∈ ({(.possibility, .epistemic),
      (.possibility, .circumstantial), (.necessity, .circumstantial)} : Finset ForceFlavor) := by
  revert ff
  decide

/-- A modal's lexical force: necessity if its meaning has necessity, possibility otherwise. -/
def lexicalForce (m : ModalItem) : ModalForce :=
  if .necessity ∈ m.forces then .necessity else .possibility

/-- Table 2: each Tlingit modal has one force, its lexical force, and one flavor. -/
theorem forces_eq : ∀ m ∈ Tlingit.modals, m.forces = {lexicalForce m} ∧ m.flavors.card = 1 := by
  decide

/-! ### Scales -/

theorem scalemates :
    ModalItem.Scalemates lexicalForce potentialMode futureMode ∧
      ∀ m ∈ dubitatives, ¬ ModalItem.HasScalemate lexicalForce Tlingit.modals m := by
  decide

/-- In upward-entailing contexts the dubitatives serve for necessity ((21)–(24)), but the potential
mode does not ((48)–(49)), nor the future mode for possibility (41). -/
theorem servesFor_necessity :
    (∀ m ∈ dubitatives, ServesIn lexicalForce Tlingit.modals .positive m .necessity) ∧
      ¬ ServesIn lexicalForce Tlingit.modals .positive potentialMode .necessity ∧
      ¬ ServesIn lexicalForce Tlingit.modals .positive futureMode .possibility := by
  simp only [ServesIn, servesFor_iff]
  decide

/-- The dubitatives serve for both forces in an upward-entailing context with a single-force
meaning, unlike St'át'imcets *k'a* and Washo *-eʔ* (§6). -/
theorem dubitatives_fixed_force :
    (∀ m ∈ dubitatives,
        (∀ g, ServesIn lexicalForce Tlingit.modals .positive m g) ∧ ¬ m.VariesForce) ∧
      Statimcets.kaInfer.VariesForce ∧ Washo.modalEq.VariesForce := by
  simp only [ServesIn, flexible_iff]
  decide

/-- In the restriction of *ldakát* 'all', the past potential serves for possibility and not for
necessity ((54) and (55)). -/
theorem potential_universal_restriction :
    ServesIn lexicalForce Tlingit.modals .negative potentialMode .possibility ∧
      ¬ ServesIn lexicalForce Tlingit.modals .negative potentialMode .necessity := by
  simp only [ServesIn, servesFor_iff]
  decide

end Cable2017
