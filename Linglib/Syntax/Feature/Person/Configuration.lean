/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Minimal
public import Linglib.Syntax.Feature.Person.Category

/-!
# Configurations of a referent

The *configuration* of a referent is the set of speech-act participants it contains together
with the number of its other members: the speaker with one other has the speaker and one. One
configuration lies below another when it has a subset of the participants and no more others,
as the configuration of a part lies below that of the whole. Cysouw's referential categories
are the configurations with several others counted alike: every configuration but the empty one
has exactly one category.

A referent with a participant has no others at the least, and one with none has one. This is
the logical minimum of Corbett's account of Rembarrnga, two members for the speaker with the
addressee and one otherwise.

A number label covers the configurations of a person's region by their size: the singular those
of one member, the minimal the smallest of the region and the augmented the rest. A person, a
clusivity and a number together thus cover some of the referential categories.

A finite set of individuals has a configuration once each role has a holder: the roles whose
holders it contains, with the number of its members that hold no role. A part of a set has a
configuration below that of the set, and where the two roles have different holders a set is
minimal among those whose configuration lies in a region exactly when its configuration is
minimal in the region. Statements about minimal configurations, such as the minimal and the unit
augmented number, then hold of the referents themselves.

## Main definitions

* `Configuration`: the participants of a referent and the number of its others.
* `Configuration.category x`: the referential category of `x`.
* `Category.ofPersonNumber p cl n`: the categories that the person `p`, the optional clusivity
  `cl` and the number `n` cover.
* `Configuration.ofFinset h u`: the configuration of the set `u` of individuals, `h` giving the
  holder of each role.

## Main results

* `Configuration.category_eq_some_iff`: every configuration but the empty one has exactly one
  category.
* `Category.ofPersonNumber_inclusive_singular`: the inclusive has no singular.
* `Configuration.minimal_ofFinset_iff`: a set is minimal among those whose configuration lies in
  a region exactly when its configuration is minimal in the region.

## Implementation notes

The order is the product order on the two fields. No join is given: the configuration of a sum
of two referents depends on the others they share, which a configuration does not record.

The holders of the roles are a function and not an embedding: one individual may hold both
roles, as a speaker addressing themself does, and the order lemmas hold of any such function. The
lemmas that count members or build a part take the injectivity of the holders as a hypothesis.

## References

* [cysouw-2003]
* [corbett-2000]
* [bickel-nichols-2005]
-/

@[expose] public section

namespace Person

open SpeechAct

/-- The configuration of a referent: the speech-act participants it contains and the number of
its other members. -/
@[ext]
structure Configuration where
  /-- The speech-act participants the referent contains. -/
  participants : Finset Role
  /-- The number of members that are not participants. -/
  others : ℕ

namespace Configuration

variable {x y : Configuration} {s : Finset Role}

/-- The pair of the participants and the number of others, the injection that induces the
order. -/
def toProd (x : Configuration) : Finset Role × ℕ := (x.participants, x.others)

theorem toProd_injective : Function.Injective toProd := fun _ _ h ↦
  Configuration.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : DecidableEq Configuration := toProd_injective.decidableEq

instance : LE Configuration := ⟨fun x y ↦ x.participants ⊆ y.participants ∧ x.others ≤ y.others⟩

theorem le_def : x ≤ y ↔ x.participants ⊆ y.participants ∧ x.others ≤ y.others := Iff.rfl

instance : DecidableLE Configuration := fun _ _ ↦ decidable_of_iff' _ le_def

instance : PartialOrder Configuration := { PartialOrder.lift toProd toProd_injective with
  le := (· ≤ ·) }

/-- `toProd` as an order embedding. -/
@[simps]
def toProdHom : Configuration ↪o Finset Role × ℕ where
  toFun := toProd
  inj' := toProd_injective
  map_rel_iff' := Iff.rfl

/-- The empty configuration, of no referent, lies below every other. -/
instance : OrderBot Configuration where
  bot := ⟨∅, 0⟩
  bot_le _ := ⟨Finset.empty_subset _, Nat.zero_le _⟩

@[simp] theorem participants_bot : (⊥ : Configuration).participants = ∅ := rfl

@[simp] theorem others_bot : (⊥ : Configuration).others = 0 := rfl

/-- The number of members of a referent with the configuration. -/
def card (x : Configuration) : ℕ := x.participants.card + x.others

theorem eq_bot_iff_card_eq_zero : x = ⊥ ↔ x.card = 0 := by
  simp [Configuration.ext_iff, card]

theorem card_le_card (h : x ≤ y) : x.card ≤ y.card :=
  Nat.add_le_add (Finset.card_le_card h.1) h.2

/-- The fewest others a referent with the participants `s` has: one where it has no participant,
none otherwise. -/
def minimum (s : Finset Role) : ℕ := if s = ∅ then 1 else 0

@[simp] theorem minimum_empty : minimum ∅ = 1 := rfl

theorem minimum_of_nonempty (h : s.Nonempty) : minimum s = 0 := by simp [minimum, h.ne_empty]

/-- A configuration is of some referent exactly when it has at least the minimum of others. -/
theorem ne_bot_iff_minimum_le : x ≠ ⊥ ↔ minimum x.participants ≤ x.others := by
  obtain ⟨s, n⟩ := x
  rcases s.eq_empty_or_nonempty with rfl | h
  · simp [Configuration.ext_iff, Nat.one_le_iff_ne_zero]
  · simp [Configuration.ext_iff, minimum_of_nonempty h, h.ne_empty]

/-- The referential category of a configuration, several others counting alike, and none for
the empty configuration. -/
def category (x : Configuration) : Option Category :=
  match decide (Role.speaker ∈ x.participants), decide (Role.addressee ∈ x.participants),
    x.others with
  | true, true, 0 => some .speakerAddressee
  | true, true, _ + 1 => some .speakerAddresseeOthers
  | true, false, 0 => some .speaker
  | true, false, _ + 1 => some .speakerOthers
  | false, true, 0 => some .addressee
  | false, true, _ + 1 => some .addresseeOthers
  | false, false, 0 => none
  | false, false, 1 => some .other
  | false, false, _ + 2 => some .others

@[simp] theorem category_bot : (⊥ : Configuration).category = none := rfl

/-- The others of a configuration as a category counts them: one or several beside no
participant, none or some beside one. -/
def otherCount (x : Configuration) : ℕ :=
  if x.participants = ∅ then min x.others 2 else min x.others 1

/-- A category is that of a configuration exactly when it has the configuration's participants
and counts its others. -/
theorem category_eq_some_iff {c : Category} :
    x.category = some c ↔
      x ≠ ⊥ ∧ c.participants = x.participants ∧ c.otherCount = x.otherCount := by
  have key : ∀ (m : Fin 3) (s : Finset Role) (c : Category),
      category ⟨s, m⟩ = some c ↔
        (⟨s, m⟩ : Configuration) ≠ ⊥ ∧ c.participants = s ∧
          (c.otherCount : ℕ) = otherCount ⟨s, m⟩ := by
    decide
  obtain ⟨s, n⟩ := x
  rcases n with _ | _ | n
  · exact key 0 s c
  · exact key 1 s c
  · have h1 : category ⟨s, n + 2⟩ = category ⟨s, 2⟩ := by
      simp only [category]; split <;> simp_all
    have h2 : otherCount ⟨s, n + 2⟩ = otherCount ⟨s, 2⟩ := by
      simp only [otherCount]; split_ifs <;> omega
    have h3 : (⟨s, n + 2⟩ : Configuration) ≠ ⊥ ↔ (⟨s, 2⟩ : Configuration) ≠ ⊥ := by
      simp [Configuration.ext_iff]
    rw [h1, h2, h3]
    exact key 2 s c

/-! ### The categories a number label covers -/

/-- The region of the referents whose participants are among `S`. -/
def InRegion (S : Finset (Finset Role)) (x : Configuration) : Prop := x.participants ∈ S ∧ x ≠ ⊥

instance (S : Finset (Finset Role)) : DecidablePred (InRegion S) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The configurations of the region of `S` with at most three others, enough to hold the
referents of each category and of each exact number. -/
def bounded (S : Finset (Finset Role)) : Finset Configuration :=
  ((S ×ˢ Finset.range 4).image fun p ↦ (⟨p.1, p.2⟩ : Configuration)).filter (· ≠ ⊥)

theorem mem_bounded_iff {S : Finset (Finset Role)} :
    x ∈ bounded S ↔ InRegion S x ∧ x.others < 4 := by
  obtain ⟨s, n⟩ := x
  simp only [bounded, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists, mk.injEq, InRegion]
  exact ⟨fun ⟨⟨_, _, ⟨hs, hn⟩, rfl, rfl⟩, hx⟩ ↦ ⟨⟨hs, hx⟩, hn⟩,
    fun ⟨⟨hs, hx⟩, hn⟩ ↦ ⟨⟨s, n, ⟨hs, hn⟩, rfl, rfl⟩, hx⟩⟩

/-- The minimal elements of a finite set of configurations. -/
def minimals (T : Finset Configuration) : Finset Configuration :=
  T.filter fun x ↦ ∀ y ∈ T, y ≤ x → x ≤ y

/-- The minimal configurations with at most three others are the minimal ones of the region,
which have the fewest others their participants allow. -/
theorem mem_minimals_bounded_iff {S : Finset (Finset Role)} :
    x ∈ minimals (bounded S) ↔ Minimal (InRegion S) x := by
  simp only [minimals, Finset.mem_filter, mem_bounded_iff]
  constructor
  · rintro ⟨⟨hx, hlt⟩, hmin⟩
    exact ⟨hx, fun y hy hyx ↦ hmin y ⟨hy, lt_of_le_of_lt hyx.2 hlt⟩ hyx⟩
  · rintro ⟨hx, hmin⟩
    have hle := hmin (y := ⟨x.participants, minimum x.participants⟩)
      ⟨hx.1, ne_bot_iff_minimum_le.2 le_rfl⟩ ⟨subset_rfl, ne_bot_iff_minimum_le.1 hx.2⟩
    have h1 : minimum x.participants ≤ 1 := by unfold minimum; split_ifs <;> omega
    exact ⟨⟨hx, lt_of_le_of_lt (hle.2.trans h1) (by omega)⟩, fun y hy hyx ↦ hmin hy.1 hyx⟩

/-- The configurations of the region of `S` that a number label covers at the least: the exact
numbers by the count of members, the minimal as the smallest referents of the region, the
augmented as the rest and the unit augmented as the smallest of the rest, and the plural and
the approximative numbers as the groups. A system narrows a label further by its other
labels, as the plural excludes two where there is a dual. -/
def covered (S : Finset (Finset Role)) : Number → Finset Configuration
  | .general => bounded S
  | .singular => (bounded S).filter (·.card = 1)
  | .dual => (bounded S).filter (·.card = 2)
  | .trial => (bounded S).filter (·.card = 3)
  | .minimal => minimals (bounded S)
  | .augmented => bounded S \ minimals (bounded S)
  | .unitAugmented => minimals (bounded S \ minimals (bounded S))
  | .plural | .paucal | .greaterPaucal | .greaterPlural | .globalPlural =>
    (bounded S).filter (2 ≤ ·.card)

end Configuration

namespace Category

/-- The categories of the referents in the region of `S` that a number label covers. -/
def ofNumber (S : Finset (Finset Role)) (n : Number) : Finset Category :=
  (Configuration.covered S n).biUnion fun x ↦ x.category.toFinset

/-- The categories a person, an optional clusivity and a number label cover: those of the
referents in the region of the person, narrowed by the clusivity, that the label covers. The
first person without a clusivity is every referent with the speaker, of which the speaker
alone is the smallest; with one, the inclusive has the speaker and the addressee as its
smallest and the exclusive the speaker alone. -/
def ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number) : Finset Category :=
  ofNumber (Clusivity.restrict cl p.participantSets) n

/-- Every category is recovered from its person and clusivity at some number label. -/
theorem ofPersonNumber_person (c : Category) :
    ∃ n, ofPersonNumber c.person c.clusivity n = {c} := by
  cases c
  · exact ⟨.singular, by decide⟩
  · exact ⟨.singular, by decide⟩
  · exact ⟨.singular, by decide⟩
  · exact ⟨.minimal, by decide⟩
  · exact ⟨.augmented, by decide⟩
  · exact ⟨.plural, by decide⟩
  · exact ⟨.plural, by decide⟩
  · exact ⟨.plural, by decide⟩

/-- No category of a region is both minimal and augmented in it. -/
theorem disjoint_ofNumber_minimal_augmented :
    ∀ S, Disjoint (ofNumber S .minimal) (ofNumber S .augmented) := by
  decide

/-- The inclusive has no singular, its smallest referent being the speaker with the addressee:
the gap of the systems [bickel-nichols-2005] call the Belhare type. -/
theorem ofPersonNumber_inclusive_singular :
    ofPersonNumber .first (some .inclusive) .singular = ∅ := by
  decide

/-- The singular of an exclusive is the speaker alone, the referent of a first person singular
without a clusivity: the systems that give the exclusive a singular and those that divide only
the first person non-singular differ in their categories and not in what is referred to. -/
theorem ofPersonNumber_exclusive_singular :
    ofPersonNumber .first (some .exclusive) .singular = ofPersonNumber .first none .singular := by
  decide

/-- The minimal inclusive is the speaker with the addressee, a referent of two, and the minimal
exclusive the speaker alone. -/
theorem ofPersonNumber_minimal :
    ofPersonNumber .first (some .inclusive) .minimal = {.speakerAddressee} ∧
      ofPersonNumber .first (some .exclusive) .minimal = {.speaker} := by
  decide

/-- The unit augmented is the trial of the inclusive and the dual of the other persons. -/
theorem covered_unitAugmented :
    Configuration.covered {{.speaker, .addressee}} .unitAugmented =
        Configuration.covered {{.speaker, .addressee}} .trial ∧
      ∀ S ∈ ({{{.speaker}}, {{.addressee}}, {∅}} : Finset (Finset (Finset SpeechAct.Role))),
        Configuration.covered S .unitAugmented = Configuration.covered S .dual := by
  decide

theorem sharedPerson_ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number)
    (h : (ofPersonNumber p cl n).Nonempty) : sharedPerson (ofPersonNumber p cl n) = some p := by
  revert h; revert p cl n; decide

theorem sharedNumber_ofPersonNumber_eq_general (p : Person) (cl : Option Clusivity) (n : Number)
    (h : sharedNumber (ofPersonNumber p cl n) = some .general) : n = .general := by
  revert h; revert p cl n; decide

end Category

end Person

/-! ### The configuration of a set of individuals -/

namespace Person.Configuration

open SpeechAct

variable {ι : Type*} [DecidableEq ι] (h : Role → ι) {u v : Finset ι} {r : Role}

/-- The configuration of a set of individuals, `h r` being the holder of the role `r`: the roles
whose holders it contains and the number of its members holding no role. -/
def ofFinset (u : Finset ι) : Configuration :=
  ⟨Finset.univ.filter (h · ∈ u), (u \ Finset.univ.image h).card⟩

@[simp] theorem mem_participants_ofFinset : r ∈ (ofFinset h u).participants ↔ h r ∈ u := by
  simp [ofFinset]

theorem participants_ofFinset_sdiff (u v : Finset ι) :
    (ofFinset h (u \ v)).participants =
      (ofFinset h u).participants \ (ofFinset h v).participants := by
  ext; simp

theorem ofFinset_mono : Monotone (ofFinset h) := fun _ _ hvu ↦
  ⟨fun _ hr ↦ (mem_participants_ofFinset h).2 (hvu ((mem_participants_ofFinset h).1 hr)),
    Finset.card_le_card (Finset.sdiff_subset_sdiff hvu subset_rfl)⟩

/-- `ofFinset` as an order homomorphism. -/
@[simps]
def ofFinsetHom : Finset ι →o Configuration := ⟨ofFinset h, ofFinset_mono h⟩

/-- A proper part of a set of individuals has a strictly smaller configuration. -/
theorem ofFinset_strictMono : StrictMono (ofFinset h) := fun v u hlt ↦ by
  refine lt_of_le_of_ne (ofFinset_mono h hlt.le) fun he ↦ hlt.ne (le_antisymm hlt.le fun z hz ↦ ?_)
  have ho : v \ Finset.univ.image h = u \ Finset.univ.image h :=
    Finset.eq_of_subset_of_card_le (Finset.sdiff_subset_sdiff hlt.le subset_rfl)
      (congrArg others he).ge
  by_cases hzr : z ∈ Finset.univ.image h
  · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hzr
    exact (mem_participants_ofFinset h).1
      (congrArg participants he ▸ (mem_participants_ofFinset h).2 hz)
  · exact (Finset.mem_sdiff.1 (ho ▸ Finset.mem_sdiff.2 ⟨hz, hzr⟩)).1

section Injective

variable {h} (hh : Function.Injective h)

include hh

/-- With different holders for the two roles, the configuration of a set has as many members as
the set. -/
theorem card_ofFinset (u : Finset ι) : (ofFinset h u).card = u.card := by
  rw [card, ofFinset, ← Finset.card_image_of_injective _ hh,
    ← Finset.card_inter_add_card_sdiff u (Finset.univ.image h)]
  congr 2
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  exact ⟨fun ⟨r, hr, e⟩ ↦ ⟨e ▸ hr, r, e⟩, fun ⟨hz, r, e⟩ ↦ ⟨r, e ▸ hz, e⟩⟩

theorem others_ofFinset (u : Finset ι) :
    (ofFinset h u).others = u.card - (ofFinset h u).participants.card :=
  Nat.eq_sub_of_add_eq' (card_ofFinset hh u)

/-- Every configuration below that of a set of individuals is the configuration of a part of
it, the two roles having different holders. -/
theorem exists_le_ofFinset_eq {y : Configuration} (hle : y ≤ ofFinset h u) :
    ∃ v ≤ u, ofFinset h v = y := by
  obtain ⟨t, m⟩ := y
  obtain ⟨ht, hm⟩ := hle
  obtain ⟨o, ho, rfl⟩ := Finset.exists_subset_card_eq hm
  have ho' : ∀ z ∈ o, z ∈ u ∧ z ∉ Finset.univ.image h := fun z hz ↦ Finset.mem_sdiff.1 (ho hz)
  refine ⟨t.image h ∪ o, fun z hz ↦ ?_, Configuration.ext ?_ ?_⟩
  · rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hz
      exact (mem_participants_ofFinset h).1 (ht hr)
    · exact (ho' z hz).1
  · ext r
    simp only [mem_participants_ofFinset, Finset.mem_union, Finset.mem_image]
    exact ⟨fun hr ↦ hr.elim (fun ⟨r', hr', e⟩ ↦ hh e ▸ hr')
      fun hr ↦ absurd (Finset.mem_image_of_mem h (Finset.mem_univ r)) (ho' _ hr).2,
      fun hr ↦ Or.inl ⟨r, hr, rfl⟩⟩
  · change ((t.image h ∪ o) \ Finset.univ.image h).card = o.card
    congr 1
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hz, hzr⟩ ↦ hz.resolve_left fun ⟨r, _, e⟩ ↦ hzr ⟨r, e⟩,
      fun hz ↦ ⟨Or.inr hz, by simpa using (ho' z hz).2⟩⟩

/-- A set of individuals is minimal among those whose configuration lies in a region exactly
when its configuration is minimal in the region. -/
theorem minimal_ofFinset_iff {P : Configuration → Prop} :
    Minimal (fun v ↦ P (ofFinset h v)) u ↔ Minimal P (ofFinset h u) :=
  minimal_comp_iff_of_strictMono (ofFinset_strictMono h) fun _ _ ↦ exists_le_ofFinset_eq hh

end Injective

end Person.Configuration
