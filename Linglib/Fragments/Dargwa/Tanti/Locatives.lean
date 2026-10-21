module

public import Linglib.Syntax.Case.Spatial
public import Linglib.Fragments.Dargwa.Tanti.Case
public import Linglib.Fragments.Dargwa.Tanti.Agreement

/-!
# Tanti Dargwa locative forms

This file defines the locative forms of Tanti Dargwa as Sumbatova describes them. A locative
form is the oblique stem followed by three suffix slots: a localization, the domain in space
with respect to the reference point, of which Tanti has eight; an orientation, whether the
object is in that domain, moving towards it, from it or across it; and a direction of the
motion with respect to the speaker, which the essive lacks, the elative requires and the lative
admits. The translative combines only with the localizations *sub*, *ante* and *post*, and
*post* with the translative alone. The orientations are the path heads of Pantcheva's
decomposition and the localizations refine its regions, so the forms fill the region-by-path
grid except for the route outside the exterior. An elative without the direction marker the
spatial paradigm demands has a non-locative use, as the causee of a transitive causative and
the standard of comparison.

## Main definitions

* `Dargwa.Tanti.Localization`, `Dargwa.Tanti.Orientation`, `Dargwa.Tanti.Direction`: the three
  categories with their suffixes, and `Localization.region` and `Orientation.pathDir` their
  comparative labels
* `Dargwa.Tanti.Orientation.marker?`: the marker of an orientation, apart from the side it attaches
  on
* `Dargwa.Tanti.LocativeForm`: a form, with `LocativeForm.morphs` its suffixes and
  `LocativeForm.IsSpatial` the combinatorics of the spatial paradigm
* `Dargwa.Tanti.comparisonStandard`: the super-elative of the standard of comparison

## Main results

* `Dargwa.Tanti.LocativeForm.not_isSpatial_elative_none`: no directionless elative is spatial
* `Dargwa.Tanti.LocativeForm.isSpatial_post_iff`: *post* takes the translative alone
* `Dargwa.Tanti.LocativeForm.exists_isSpatial_iff`: the region-by-path grid is filled except for
  the route outside the exterior

## Implementation notes

* The essive is the localization followed by the gender marker, so `morphs` takes the marker.
* The direction suffixes are cited in their long forms; the short forms drop *-le*, and
  *-sale* and *-dale* vary with *-sele* and *-dele*. Whether the translative takes a direction
  marker is not stated, so `IsSpatial` leaves it open.
* The general-localization form of some nouns, *kis-na-b* 'in the pocket', is irregular and
  left out, as are the locative adverbs and postpositions, which inflect for orientation.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
* [M. Pantcheva, *Decomposing Path: The Nanosyntax of Directional Expressions*
  (2011)][pantcheva-2011]
-/

@[expose] public section

namespace Dargwa.Tanti

open Morphology

/-! ### Localization -/

/-- A localization is the domain in space a locative form specifies with respect to the
reference point. -/
inductive Localization where
  /-- *super* *-ja*, on the surface of the object. -/
  | super
  /-- *sub* *-gu*, under the object. -/
  | sub
  /-- *ante* *-sa*, in front of the object. -/
  | ante
  /-- *in* *-ʜe*, *-ʜaˁ* for some nouns, inside a container. -/
  | in_
  /-- *inter* *-cːe*, in a solid substance. -/
  | inter
  /-- *apud* *-hira*, near the object. -/
  | apud
  /-- *ad* *-šːu*, in the place functionally associated with the object. -/
  | ad
  /-- *post* *-hi*, behind the object. -/
  | post
  deriving DecidableEq, Repr, Fintype

/-- The localization suffix. -/
def Localization.suffix : Localization → Morph
  | .super => .suff "ja"
  | .sub => .suff "gu"
  | .ante => .suff "sa"
  | .in_ => .suff "ʜe"
  | .inter => .suff "cːe"
  | .apud => .suff "hira"
  | .ad => .suff "šːu"
  | .post => .suff "hi"

/-- The region of the comparative decomposition a localization falls in. *super* is the
surface, *in* and *inter* are the interior and the rest are the exterior. -/
def Localization.region : Localization → Spatial.Localization
  | .super => .surface
  | .in_ | .inter => .interior
  | .sub | .ante | .apud | .ad | .post => .exterior

/-- The localizations the translative combines with. -/
def Localization.TakesTranslative (l : Localization) : Prop := l = .sub ∨ l = .ante ∨ l = .post

instance : DecidablePred Localization.TakesTranslative := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

/-! ### Orientation -/

/-- An orientation is the motion, or its absence, with respect to the reference point. -/
inductive Orientation where
  /-- The lative, unmarked, motion towards the reference point. -/
  | lative
  /-- The elative *-r*, motion from the reference point. -/
  | elative
  /-- The essive, the gender marker after the localization, location in the reference
  point. -/
  | essive
  /-- The translative *-tːi*, motion across the reference point. -/
  | translative
  deriving DecidableEq, Repr, Fintype

/-- The marker of an orientation, the gender marker `g` for the essive and none for the lative. -/
def Orientation.marker? : Orientation → Gender.Marker → Option String
  | .lative, _ => none
  | .elative, _ => some "r"
  | .essive, g => some g.form
  | .translative, _ => some "tːi"

/-- The orientation suffixes, with the gender marker `g` the essive takes. -/
def Orientation.morphs (o : Orientation) (g : Gender.Marker) : List Morph :=
  ((o.marker? g).map Morph.suff).toList

/-- The path head of the comparative decomposition an orientation expresses. -/
def Orientation.pathDir : Orientation → Spatial.Path.Direction
  | .essive => .place
  | .lative => .goal
  | .elative => .source
  | .translative => .route

/-! ### Direction -/

/-- A direction orients the motion with respect to the speaker or another point of
reference. -/
inductive Direction where
  /-- *-ha(le)*, upward. -/
  | up
  /-- *-ka(le)*, downward. -/
  | down
  /-- *-se(le)* or *-sale*, towards the speaker. -/
  | hither
  /-- *-de(le)* or *-dale*, away from the speaker. -/
  | thither
  deriving DecidableEq, Repr, Fintype

/-- The direction suffix, in its long form. -/
def Direction.suffix : Direction → Morph
  | .up => .suff "hale"
  | .down => .suff "kale"
  | .hither => .suff "sele"
  | .thither => .suff "dele"

/-! ### Locative forms -/

/-- A locative form is a localization, an orientation and, where the form has one, a
direction. -/
structure LocativeForm where
  localization : Localization
  orientation : Orientation
  direction : Option Direction
  deriving DecidableEq, Repr, Fintype

namespace LocativeForm

variable (f : LocativeForm)

/-- The suffixes of a locative form after the oblique stem, with the gender marker `g` in the
essive. -/
def morphs (g : Gender.Marker) : List Morph :=
  f.localization.suffix :: (f.orientation.morphs g ++ (f.direction.map Direction.suffix).toList)

/-- A form is spatial when its slots combine as the paradigm allows. The essive takes no
direction marker, the elative requires one and the lative admits one; the translative combines
only with the localizations that take it, and *post* only with the translative. -/
def IsSpatial : Prop :=
  (f.orientation = .essive → f.direction = none) ∧
    (f.orientation = .elative → f.direction ≠ none) ∧
    (f.orientation = .translative → f.localization.TakesTranslative) ∧
    (f.localization = .post → f.orientation = .translative)

instance : DecidablePred IsSpatial := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- *kːumi-li-ja-r-sele* 'from the bridge hither' is the super-elative with the direction
*hither*, a spatial form whose suffixes the slots derive. -/
theorem super_elative_hither :
    IsSpatial ⟨.super, .elative, some .hither⟩ ∧
      (⟨.super, .elative, some .hither⟩ : LocativeForm).morphs .b =
        [.suff "ja", .suff "r", .suff "sele"] := by
  decide

variable {l : Localization}

/-- No elative without a direction marker is spatial. -/
theorem not_isSpatial_elative_none (l : Localization) : ¬ IsSpatial ⟨l, .elative, none⟩ :=
  fun h ↦ h.2.1 rfl rfl

/-- The essive of every localization but *post* is spatial. -/
theorem isSpatial_essive (h : l ≠ .post) : IsSpatial ⟨l, .essive, none⟩ :=
  ⟨fun _ ↦ rfl, nofun, nofun, fun hl ↦ absurd hl h⟩

/-- The lative of every localization but *post* is spatial, with or without a direction. -/
theorem isSpatial_lative (d : Option Direction) (h : l ≠ .post) : IsSpatial ⟨l, .lative, d⟩ :=
  ⟨nofun, nofun, nofun, fun hl ↦ absurd hl h⟩

/-- The elative with a direction of every localization but *post* is spatial. -/
theorem isSpatial_elative_some (d : Direction) (h : l ≠ .post) :
    IsSpatial ⟨l, .elative, some d⟩ :=
  ⟨nofun, fun _ ↦ nofun, nofun, fun hl ↦ absurd hl h⟩

/-- The translative is spatial exactly with the localizations that take it. -/
theorem isSpatial_translative_iff {d : Option Direction} :
    IsSpatial ⟨l, .translative, d⟩ ↔ l.TakesTranslative :=
  ⟨fun h ↦ h.2.2.1 rfl, fun h ↦ ⟨nofun, nofun, fun _ ↦ h, fun _ ↦ rfl⟩⟩

/-- *post* takes the translative alone. -/
theorem isSpatial_post_iff {o : Orientation} {d : Option Direction} :
    IsSpatial ⟨.post, o, d⟩ ↔ o = .translative :=
  ⟨fun h ↦ h.2.2.2 rfl, fun h ↦ h ▸ isSpatial_translative_iff.2 (.inr (.inr rfl))⟩

/-- The forms fill the grid of regions and path heads except for the route, which the
translative expresses, outside the exterior. -/
theorem exists_isSpatial_iff (r : Spatial.Localization) (d : Spatial.Path.Direction) :
    (∃ f : LocativeForm,
      f.IsSpatial ∧ f.localization.region = r ∧ f.orientation.pathDir = d) ↔
      d ≠ .route ∨ r = .exterior := by
  constructor
  · rintro ⟨⟨l, o, dir⟩, hs, rfl, rfl⟩
    cases o
    · exact .inl nofun
    · exact .inl nofun
    · exact .inl nofun
    · rcases hs.2.2.1 rfl with rfl | rfl | rfl <;> exact .inr rfl
  · intro h
    obtain ⟨l, hl, hp⟩ : ∃ l : Localization, l.region = r ∧ l ≠ .post := by
      cases r
      · exact ⟨.in_, rfl, nofun⟩
      · exact ⟨.super, rfl, nofun⟩
      · exact ⟨.sub, rfl, nofun⟩
    cases d
    · exact ⟨⟨l, .essive, none⟩, isSpatial_essive hp, hl, rfl⟩
    · exact ⟨⟨l, .lative, none⟩, isSpatial_lative none hp, hl, rfl⟩
    · exact ⟨⟨l, .elative, some .up⟩, isSpatial_elative_some .up hp, hl, rfl⟩
    · obtain rfl : r = .exterior := h.resolve_left (not_not.2 rfl)
      exact ⟨⟨.sub, .translative, none⟩, isSpatial_translative_iff.2 (.inl rfl), rfl, rfl⟩

end LocativeForm

/-- The super-elative without a direction marker of the standard of comparison. -/
def comparisonStandard : LocativeForm := ⟨.super, .elative, none⟩

/-- The standard of comparison is not a spatial form. -/
theorem not_isSpatial_comparisonStandard : ¬ comparisonStandard.IsSpatial :=
  LocativeForm.not_isSpatial_elative_none _

end Dargwa.Tanti
