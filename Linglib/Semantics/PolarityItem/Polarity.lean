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

open NaturalLogic PolarityItem

/-- The polarity `s` admits the item `e`: a positive polarity item needs `s` positive, and a
negative polarity item needs `s` negative. -/
def Polarity.Admits (s : Polarity) (e : PolarityItem) : Prop :=
  (e.IsPPI → s = .positive) ∧ (e.IsNPI → s = .negative)

instance (s : Polarity) (e : PolarityItem) : Decidable (s.Admits e) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace PolarityItem.Licenser

variable (W : Type) (s : Polarity)

/-- The licenser that a clause of polarity `s` over the worlds `W` is: the identity on
propositions when `s` is positive and the complement when it is negative. -/
def ofPolarity : Licenser := .ofOperator fun q : Set W ↦ s • q

variable {W s}

/-- The licenser of a polarity admits an item that is not a free choice item exactly when the
polarity admits it. -/
theorem admits_ofPolarity_iff [Nonempty W] {e : PolarityItem} (hf : ¬e.IsFCI) :
    (ofPolarity W s).Admits e ↔ s.Admits e := by
  have hne : (Set.univ : Set W) ≠ ∅ := Set.univ_nonempty.ne_empty
  cases s
  · have hH : ¬(ofPolarity W .positive).Holds .anti := fun h ↦
      hne (Set.subset_empty_iff.1
        (ProjectivitySignature.holdsFor_anti_iff.1 (h ⟨⟩) (Set.empty_subset Set.univ)))
    have hL : ¬(ofPolarity W .positive).Licenses e := by
      rintro (⟨r, -, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      exacts [(carries_ofOperator_iff.1 hr).2 fun _ _ h ↦ h, h, h]
    simp [Polarity.Admits, Admits, AntiLicenses, hL, hf, not_holds_toProjectivitySignature hH]
  · have hH : (ofPolarity W .negative).Holds .antiAddMult := fun _ ↦
      ProjectivitySignature.holdsFor_antiAddMult_compl
    have hL : e.IsNPI → (ofPolarity W .negative).Licenses e := fun h ↦ by
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
      exact .inl ⟨r, hr, carries_ofOperator_iff.2
        ⟨ProjectivitySignature.holdsFor_antiAddMult_compl.of_le
          (Negation.Strength.toProjectivitySignature_antitone le_top),
        fun hm ↦ hne (Set.subset_empty_iff.1 (by simpa using hm (Set.empty_subset Set.univ)))⟩⟩
    rw [Admits, antiLicenses_iff_isPPI hH]
    simpa [Polarity.Admits, hf] using fun _ ↦ hL

end PolarityItem.Licenser
