module

public import Linglib.Semantics.PolarityItem.Licenser
public import Linglib.Semantics.Negation.Polarity

/-!
# Polarity items in a clause of a given polarity

A clause of positive polarity leaves the proposition it contains as it is, and a clause of
negative polarity takes its complement. As a licenser of the polarity items inside it, the
positive clause is upward entailing and licenses nothing, while the negative clause is
anti-morphic: it licenses every negative polarity item and blocks every positive one. A polarity
`s` therefore admits an item when the item, if positive, finds `s` positive, and, if negative,
finds `s` negative. This is the diagnostic that classes a negative question by the items it
admits ([ladd-1981]).

## Main definitions

* `PolarityItem.Licenser.ofPolarity`: the licenser that the clause of a given polarity is.
* `Polarity.Admits`: a positive polarity item needs the positive polarity and a negative one the
  negative polarity.

## Main results

* `PolarityItem.Licenser.admits_ofPolarity_iff`: the licenser of a polarity admits an item that
  is not a free choice item exactly when the polarity admits it.

## References

* [ladd-1981]
* [zwarts-1998]
* [romero-han-2004]
-/

@[expose] public section

open PolarityItem

/-- The profile of a clause of polarity `s`: a positive clause carries and holds no strength of
negation, and a negative clause carries and holds every strength. -/
def Polarity.profile : Polarity → PolarityItem.Profile
  | .positive => ⟨⊥, ⊥, false⟩
  | .negative => ⟨PolarityItem.ofStrength .antimorphic, PolarityItem.ofStrength .antimorphic, false⟩

/-- The polarity `s` admits the class `k` when its profile does. A positive clause admits the
classes that require nothing, and a negative clause admits the classes that some strength of
negation licenses and none blocks. -/
def Polarity.Admits (s : Polarity) (k : PolarityItem.Class) : Prop := s.profile.Admits k

instance (s : Polarity) (k : PolarityItem.Class) : Decidable (s.Admits k) :=
  inferInstanceAs (Decidable (s.profile.Admits k))

namespace PolarityItem.Licenser

variable (W : Type) (s : Polarity)

/-- The licenser that a clause of polarity `s` over the worlds `W` is: the identity on
propositions when `s` is positive and the complement when it is negative. -/
def ofPolarity : Licenser := .ofOperator fun q : Set W ↦ s • q

variable {W s}

/-- The profile of the licenser of a polarity is the profile of the polarity. -/
theorem profile_ofPolarity [Nonempty W] : (ofPolarity W s).profile = s.profile := by
  have hne : (Set.univ : Set W) ≠ ∅ := Set.univ_nonempty.ne_empty
  cases s
  · have hH : ¬(ofPolarity W .positive).Holds .monotoneDecreasing := fun h ↦
      hne (Set.subset_empty_iff.1 (h ⟨⟩ (Set.empty_subset Set.univ)))
    exact profile_eq_mk
      (carried_eq_bot fun _ hr ↦ (carries_ofOperator_iff.1 hr).2 fun _ _ h ↦ h)
      (held_eq_bot fun _ ↦ not_holds_of_not_holds_monotoneDecreasing hH)
      (iff_of_false id Bool.false_ne_true)
  · have hH (r : Negation.Strength) : (ofPolarity W .negative).Holds r := fun _ ↦
      Negation.HasStrength.of_le (t := .antimorphic)
        ⟨fun _ _ ↦ Set.compl_union _ _, fun _ ↦ rfl⟩ le_top
    exact profile_eq_mk
      (carried_eq_coe fun r ↦ ⟨fun _ ↦ r.le_antimorphic, fun _ ↦ carries_ofOperator_iff.2
        ⟨hH r ⟨⟩, fun hm ↦ hne (Set.subset_empty_iff.1
          (by simpa using hm (Set.empty_subset Set.univ)))⟩⟩)
      (held_eq_coe fun r ↦ ⟨fun _ ↦ r.le_antimorphic, fun _ ↦ hH r⟩)
      (iff_of_false id Bool.false_ne_true)

/-- The licenser of a polarity admits a class exactly when the polarity admits it. -/
theorem admits_ofPolarity_iff [Nonempty W] {k : Class} :
    (ofPolarity W s).Admits k ↔ s.Admits k := by
  rw [← profile_admits_iff, profile_ofPolarity, Polarity.Admits]

end PolarityItem.Licenser
