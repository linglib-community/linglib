module

public import Linglib.Semantics.Modality.Universals
public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Data.Examples.MocnikAbramovitz2019

/-!
# Močnik and Abramovitz (2019): a variable-force variable-flavor attitude verb in Koryak

Močnik and Abramovitz document the Koryak attitude verb *ivək*, translated 'say' out of
context, which also means 'think' and 'allow for the possibility that'. It varies in force and
in flavor, against Nauze's universal that a modal varies on one axis only.

Their entry (15) quantifies universally over the worlds a subset selection function picks from
a domain, after Rullmann, Matthewson and Davis, and closes the function existentially over a
cover that the context resolves either to the identity, the default, or to all nonempty
selections (`Cover`). The identity cover gives the box over the domain and the full cover the
diamond (`Frame.ivek_identity_iff`, `Frame.ivek_all_iff`), so the force varies with the cover.
A modal-base-like variable sets the domain to the holder's belief worlds or to the worlds
compatible with what the holder says (`Flavor`), so the flavor varies with it. The two are
independent parameters, and the entry's force-flavor pairs are the product of two forces and
two flavors (`meaning_eq`), varying on both axes (`not_singleAxis_meaning`). The pairs the
paper attests vary on both axes too (`not_singleAxis_attested`).

The cover accounts for the conjunctions of §2. *ivək* of two incompatible complements is
contradictory on the identity cover (`Frame.not_ivek_identity_and`) and consistent on the full
cover (`Frame.ivek_all_and_iff`), the contrast between the necessity and possibility readings
of (6) and (8a). The felicitous reading of (8b) is the negated box, and its full-cover reading
is the one on which the ball is neither white nor black (`Frame.ex8b_all_iff`), false in the
context of (8) (`Frame.ex8b_all_false`). The flavor accounts for §3: the two *ivək*s of (14),
set apart by an adverb, are consistent on different flavors (`ex14_consistent`), while one
*ivək* over clauses that contradict each other, (20), is false on every reading
(`Frame.not_ivek_and_not`). On the doxastic flavor and the identity cover *ivək* is the
non-veridical *believe* of Hintikka (`Frame.ivek_doxastic_identity_iff_holdsAt`).

## Implementation notes

* The entry's domain is a set of worlds; here it is the set accessible from the evaluation
  world by the holder's belief or sayings relation.
* (13) writes the second colour of (8b) as the negation of the first, which makes its
  full-cover reading contradictory in every context. The prose reading, that the ball is half
  white and half black, needs the two colours as separate predicates, and so they are here.
* `attested` leaves out the existential 'say' of footnote 10, which the paper could not
  confirm and the entry predicts (`attested_ssubset_meaning`).

## TODO

* §4: the bouletic readings, split at LF into the doxastic *ivək* and an item in the embedded
  clause, the counterfactual mood (23) and the covert *des* (26), over the information-state
  index of [yalcin-2007].

## References

* [mocnik-abramovitz-2019]
* [nauze-2008]
* [rullmann-matthewson-davis-2008]
* [hintikka-1962]
* [yalcin-2007]
-/

@[expose] public section

namespace MocnikAbramovitz2019

open Modality ModalLogic
open scoped SetRel

variable {W E : Type*}

/-! ### Force: a universal over a selected subset -/

/-- The cover `C` of (11) resolves to the identity on the domain, the default, or all subset
selection functions, which pick a nonempty subset of it. -/
inductive Cover
  | identity
  | all
  deriving DecidableEq, Fintype

namespace Cover

/-- The selection functions a resolution admits over the domain `D`. -/
def funs : Cover → Set W → Set (Set W → Set W)
  | identity, D => {f | f D = D}
  | all, D => {f | f D ⊆ D ∧ (f D).Nonempty}

/-- The force of a resolution, by `holds_identity_iff` and `holds_all_iff`. -/
def force : Cover → ModalForce
  | identity => .necessity
  | all => .possibility

end Cover

/-- The quantification of (11) over a domain `D` holds when some admitted selection function maps
`D` into `p`. -/
def Holds (c : Cover) (D : Set W) (p : W → Prop) : Prop :=
  ∃ f ∈ c.funs D, ∀ v ∈ f D, p v

variable {D : Set W} {p q : W → Prop}

theorem holds_identity_iff : Holds .identity D p ↔ ∀ v ∈ D, p v :=
  ⟨fun ⟨f, (hf : f D = D), h⟩ v hv ↦ h v (by rwa [hf]), fun h ↦ ⟨id, rfl, h⟩⟩

theorem holds_all_iff : Holds .all D p ↔ ∃ v ∈ D, p v :=
  ⟨fun ⟨_, ⟨hsub, v, hv⟩, h⟩ ↦ ⟨v, hsub hv, h v hv⟩, fun ⟨v, hv, hp⟩ ↦
    ⟨fun _ ↦ {v}, ⟨Set.singleton_subset_iff.2 hv, v, rfl⟩, fun _ hu ↦ hu ▸ hp⟩⟩

/-! ### Flavor: the domain of quantification -/

/-- The flavors of *ivək*, the values its modal-base-like variable takes in (15): the holder's
belief worlds or the worlds compatible with what the holder says. -/
inductive Flavor
  | doxastic
  | assertive
  deriving DecidableEq, Fintype

/-- For a holder at a world, the worlds compatible with what the holder believes and with what
the holder says. -/
structure Frame (W E : Type*) where
  belief : E → SetRel W W
  sayings : E → SetRel W W

namespace Frame

/-- The accessibility relation a flavor selects. -/
def access (F : Frame W E) : Flavor → E → SetRel W W
  | .doxastic => F.belief
  | .assertive => F.sayings

/-- By the entry (15), *ivək* on a flavor and a cover holds when some admitted selection from the
holder's domain maps it into the complement. -/
def ivek (F : Frame W E) (φ : Flavor) (c : Cover) (p : W → Prop) (x : E) (w : W) : Prop :=
  Holds c {v | w ~[F.access φ x] v} p

variable {F : Frame W E} {φ : Flavor} {x : E} {w : W}

theorem ivek_identity_iff : F.ivek φ .identity p x w ↔ □[F.access φ x] p w :=
  holds_identity_iff

theorem ivek_all_iff : F.ivek φ .all p x w ↔ ◇[F.access φ x] p w :=
  holds_all_iff

theorem ivek_doxastic_identity_iff_holdsAt :
    F.ivek .doxastic .identity p x w ↔
      (⟨F.belief, .nonVeridical, none⟩ : Doxastic.DoxasticPredicate W E).HoldsAt x p w := by
  rw [Doxastic.DoxasticPredicate.holdsAt_iff, ivek_identity_iff]
  exact ⟨fun h ↦ ⟨nofun, trivial, h⟩, fun h ↦ h.2.2⟩

/-! ### Conjunction and negation, §2 -/

/-- On the identity cover, *ivək* of two complements incompatible over a nonempty domain is
contradictory (Option 1 of (12) for (6); necessity reading of (8a)). -/
theorem not_ivek_identity_and (h : ∃ v, w ~[F.access φ x] v)
    (hpq : ∀ v, w ~[F.access φ x] v → p v → ¬ q v) :
    ¬ (F.ivek φ .identity p x w ∧ F.ivek φ .identity q x w) := by
  rintro ⟨hp, hq⟩
  obtain ⟨v, hv⟩ := h
  exact hpq v hv (ivek_identity_iff.1 hp v hv) (ivek_identity_iff.1 hq v hv)

/-- On the full cover, *ivək* holds of both complements iff the domain leaves each open (Option 2 of
(12) for (6); possibility reading of (8a)). -/
theorem ivek_all_and_iff :
    F.ivek φ .all p x w ∧ F.ivek φ .all q x w ↔
      (∃ v, w ~[F.access φ x] v ∧ p v) ∧ ∃ v, w ~[F.access φ x] v ∧ q v :=
  and_congr ivek_all_iff ivek_all_iff

/-- On the identity cover, (8b) says the beliefs leave open that the ball is not white and that it
is not black (Option 1 of (13)). -/
theorem ex8b_identity_iff {white black : W → Prop} :
    ¬ F.ivek φ .identity white x w ∧ ¬ F.ivek φ .identity black x w ↔
      (∃ v, w ~[F.access φ x] v ∧ ¬ white v) ∧ ∃ v, w ~[F.access φ x] v ∧ ¬ black v := by
  simp only [ivek_identity_iff, not_box]
  rfl

/-- On the full cover, (8b) says the ball is neither white nor black. -/
theorem ex8b_all_iff {white black : W → Prop} :
    ¬ F.ivek φ .all white x w ∧ ¬ F.ivek φ .all black x w ↔
      □[F.access φ x] (fun v ↦ ¬ white v ∧ ¬ black v) w := by
  rw [box_and, ← not_diamond, ← not_diamond, ivek_all_iff, ivek_all_iff]

/-- If the ball is white or black in every admissible world, as in (8), the full-cover reading of
(8b) is false (Option 2 of (13)). -/
theorem ex8b_all_false {white black : W → Prop} (h : ∃ v, w ~[F.access φ x] v)
    (hctx : ∀ v, w ~[F.access φ x] v → white v ∨ black v) :
    ¬ (¬ F.ivek φ .all white x w ∧ ¬ F.ivek φ .all black x w) := by
  rw [ex8b_all_iff]
  obtain ⟨v, hv⟩ := h
  intro hbox
  exact (hctx v hv).elim (hbox v hv).1 (hbox v hv).2

/-! ### One flavor for each *ivək*, §3 -/

/-- Over a nonempty domain, a single *ivək* over contradictory clauses, as in (20), is false on
every reading. -/
theorem not_ivek_and_not (h : ∃ v, w ~[F.access φ x] v) (c : Cover) :
    ¬ F.ivek φ c (fun v ↦ p v ∧ ¬ p v) x w := by
  cases c
  · obtain ⟨v, hv⟩ := h
    exact fun hb ↦ (ivek_identity_iff.1 hb v hv).2 (ivek_identity_iff.1 hb v hv).1
  · exact fun hd ↦ let ⟨_, _, hp, hnp⟩ := ivek_all_iff.1 hd; hnp hp

end Frame

/-- The two *ivək*s of (14), with assertive and doxastic flavors, can report saying that the
students study well and thinking that they study badly. -/
theorem ex14_consistent : ∃ (F : Frame Bool Unit) (p : Bool → Prop),
    (∃ v, true ~[F.sayings ()] v) ∧ (∃ v, true ~[F.belief ()] v) ∧
      F.ivek .assertive .identity p () true ∧
      F.ivek .doxastic .identity (fun v ↦ ¬ p v) () true :=
  ⟨⟨fun _ ↦ {p | p.2 = false}, fun _ ↦ {p | p.2 = true}⟩, (· = true), ⟨true, rfl⟩, ⟨false, rfl⟩,
    Frame.ivek_identity_iff.2 fun _ hv ↦ hv,
    Frame.ivek_identity_iff.2 fun _ (hv : _ = false) hp ↦ Bool.false_ne_true (hv ▸ hp)⟩

/-! ### The force-flavor pairs -/

/-- The force-flavor pairs *ivək* expresses on the entry, one for each resolution of the cover
and each flavor. -/
def meaning : Finset (ModalForce × Flavor) :=
  (Finset.univ : Finset (Cover × Flavor)).image fun r ↦ (r.1.force, r.2)

theorem meaning_eq : meaning = {.necessity, .possibility} ×ˢ Finset.univ := by
  decide

/-- *ivək* varies in force and in flavor, against the universal (1) of [nauze-2008]. -/
theorem not_singleAxis_meaning : ¬ SingleAxis meaning := by
  decide

/-- The paper attests the pairs 'think' (2), 'allow for the possibility' (4), (6), (8a), and
'say' (2), (7). Footnote 10 could not confirm an existential 'say'. -/
def attested : Finset (ModalForce × Flavor) :=
  {(.necessity, .doxastic), (.possibility, .doxastic), (.necessity, .assertive)}

theorem attested_ssubset_meaning :
    attested ⊂ meaning ∧ (.possibility, .assertive) ∈ meaning \ attested := by
  decide

theorem not_singleAxis_attested : ¬ SingleAxis attested := by
  decide

end MocnikAbramovitz2019
