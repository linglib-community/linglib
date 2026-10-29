module

public import Linglib.Data.Examples.AckemaNeeleman2018
public import Linglib.Fragments.Dutch.Pronouns
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Set.Subsingleton
public import Studies.Harbour2016

/-!
# Ackema and Neeleman (2018): Features of Person: From the Inventory of Persons to Their Morphological Realization

Ackema and Neeleman derive the inventory of persons from two privative features that act as
partial functions on a layered set, a set of atoms with a chain of predecessors. `PROX` discards
the outermost layer and `DIST` selects it, and neither applies to a set with no predecessor.
Their input is the person space: three nested sets, with the speaker an obligatory member of the
innermost and an addressee of the next. Third person is `[DIST]`, second `[PROX–DIST]`, first
`[PROX–PROX]` and the inclusive `[PROX]`.

Number applies to the output of person, and plural requires more than one member. The inclusive has
two obligatory members and so no singular, which leaves three singular pronouns and four plural
ones. Only `[DIST]` can deliver the empty set, so expletives are third person singular. Spell-out
rules mention features with multiplicity, and Maximal Encoding uses the applicable rule mentioning
the most: Dutch has no rule mentioning two `PROX`, so *wij* realizes both the inclusive and the
exclusive. No natural class holds the inclusive and the second person without the exclusive, but
impoverishing `DIST` under `PROX` in the plural [turns a paradigm Harbour's parameters generate into
Zwicky's tripartition](##impoverishDist_not_mem_image_graph), which they never generate: the
generalization is statistical here and absolute for Harbour.

## Implementation notes

* A layered set carries its predecessors, so the set a feature leaves unlayered has none. The
  paper defines the predecessor on the three sets of the person space.
* The features are defined over any type with a difference, so the same definitions compute the
  participants a structure delivers over finite sets of discourse roles (`preimage_atom_eval`).
* A pronoun without `PL` denotes a set with at most one member, the chapter's provisional
  singular. Its impersonal pronoun, the structure with no feature, is left to later chapters.
* Gender is not analysed, so the third person singular rule inserts *hij* where the paper lists
  *hij*, *zij* and *het*.

## TODO

* The honorific feature and the polite pronouns recruited by impoverishment.
* The context operators that fix the speaker and the addressee, and their shifting.

## References

* [P. Ackema and A. Neeleman, *Features of Person: From the Inventory of Persons to Their
  Morphological Realization* (2018)][ackema-neeleman-2018]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [D. Harbour, *Impossible Persons* (2016)][harbour-2016]
-/

@[expose] public section

namespace AckemaNeeleman2018

open Morphology.Exponence Discourse

variable {α β γ E : Type*}

/-! ### Layered sets and the person features -/

/-- A layered set is a set with the chain of its predecessors, the nearest first. A set with no
predecessor is unlayered. -/
structure Layered (β : Type*) where
  /-- The set itself. -/
  set : β
  /-- `Pred S`, `Pred (Pred S)` and so on. -/
  preds : List β

namespace Layered

/-- `Pred S`, with the predecessors that remain. -/
def pred : Layered β → Option (Layered β)
  | ⟨_, []⟩ => none
  | ⟨_, p :: ps⟩ => some ⟨p, ps⟩

/-- The image of a layered set under a map of sets. -/
def map (g : β → γ) (S : Layered β) : Layered γ := ⟨g S.set, S.preds.map g⟩

end Layered

/-- The two privative person features. -/
inductive Feature
  | prox
  | dist
  deriving DecidableEq

section SDiff

variable [SDiff β] [SDiff γ] {S T : Layered β} {fs : List Feature} {g : β → γ}

namespace Feature

/-- `PROX S = Pred S` discards the outermost layer of a layered set and `DIST S = S − Pred S`
selects it, leaving an unlayered set. Neither applies to an unlayered set. -/
def apply : Feature → Layered β → Option (Layered β)
  | .prox, S => S.pred
  | .dist, S => S.pred.map fun P ↦ ⟨S.set \ P.set, []⟩

theorem length_preds_lt {f : Feature} (h : f.apply S = some T) :
    T.preds.length < S.preds.length := by
  rcases S with ⟨s, _ | ⟨p, ps⟩⟩ <;> cases f <;> simp [apply, Layered.pred] at h <;> simp [← h]

theorem apply_map (hg : ∀ s t, g (s \ t) = g s \ g t) (f : Feature) (S : Layered β) :
    f.apply (S.map g) = (f.apply S).map (.map g) := by
  rcases S with ⟨s, _ | ⟨p, ps⟩⟩ <;> cases f <;> simp [apply, Layered.pred, Layered.map, hg]

end Feature

namespace Layered

/-- The output of a person feature structure on a layered set, its features applied in order. -/
def eval (S : Layered β) (fs : List Feature) : Option (Layered β) :=
  fs.foldlM (fun S f ↦ f.apply S) S

@[simp] theorem eval_nil (S : Layered β) : S.eval [] = some S := rfl

@[simp] theorem eval_cons (S : Layered β) (f : Feature) (fs : List Feature) :
    S.eval (f :: fs) = (f.apply S).bind (·.eval fs) := by
  simp [eval]

/-- A feature structure has an output on a layered set iff it has at most as many features as
the set has predecessors and only its last feature is `DIST`. -/
theorem isSome_eval_iff :
    (S.eval fs).isSome ↔ fs.length ≤ S.preds.length ∧ ∀ f ∈ fs.dropLast, f = .prox := by
  induction fs generalizing S with
  | nil => simp
  | cons f fs ih =>
    rw [eval_cons]
    rcases S with ⟨s, _ | ⟨p, ps⟩⟩
    · cases f <;> simp [Feature.apply, pred]
    · cases f <;> simp only [Feature.apply, pred, Option.map_some, Option.bind_some, ih] <;>
        cases fs <;> simp

theorem length_preds_add_length_le (h : S.eval fs = some T) :
    T.preds.length + fs.length ≤ S.preds.length := by
  induction fs generalizing S with
  | nil => simp [Option.some.inj h]
  | cons f fs ih =>
    obtain ⟨U, hU, hT⟩ := Option.bind_eq_some_iff.1 (eval_cons S f fs ▸ h)
    grind [f.length_preds_lt hU, ih hT]

theorem eval_eq_some_self_iff : S.eval fs = some S ↔ fs = [] :=
  ⟨fun h ↦ List.length_eq_zero_iff.1 (by have := length_preds_add_length_le h; omega),
    fun h ↦ h ▸ rfl⟩

theorem eval_map (hg : ∀ s t, g (s \ t) = g s \ g t) (S : Layered β) (fs : List Feature) :
    (S.map g).eval fs = (S.eval fs).map (map g) := by
  induction fs generalizing S with
  | nil => rfl
  | cons f fs ih => cases h : f.apply S <;> simp [Feature.apply_map hg, h, ih]

end Layered

end SDiff

/-! ### The person space -/

/-- The person space is a nest of three sets of atoms. The speaker is an obligatory member of
the innermost, `Sᵢ`, and an addressee of the next, `Sᵢ₊ᵤ`; their other members are associates of
the two, and the remaining members of the whole space `Sᵢ₊ᵤ₊ₒ` are the others. -/
structure PersonSpace (α : Type*) where
  /-- The speaker `i`. -/
  speaker : α
  /-- The addressee `u`. -/
  addressee : α
  /-- `Sᵢ`. -/
  Si : Set α
  /-- `Sᵢ₊ᵤ`. -/
  Siu : Set α
  /-- `Sᵢ₊ᵤ₊ₒ`. -/
  Siuo : Set α
  speaker_mem : speaker ∈ Si
  addressee_mem : addressee ∈ Siu
  addressee_notMem : addressee ∉ Si
  Si_subset : Si ⊆ Siu
  Siu_subset : Siu ⊆ Siuo

namespace PersonSpace

variable (S : PersonSpace α)

/-- The input to the person features is the whole space, with predecessor `Sᵢ₊ᵤ`, whose
predecessor is `Sᵢ`. -/
def layered : Layered (Set α) := ⟨S.Siuo, [S.Siu, S.Si]⟩

/-- The atom bearing a discourse role. -/
def atom : Role → α
  | .speaker => S.speaker
  | .addressee => S.addressee

theorem speaker_ne_addressee : S.speaker ≠ S.addressee := fun h ↦
  S.addressee_notMem (h ▸ S.speaker_mem)

theorem nontrivial_Siu : S.Siu.Nontrivial :=
  ⟨_, S.Si_subset S.speaker_mem, _, S.addressee_mem, S.speaker_ne_addressee⟩

theorem nontrivial_Siuo : S.Siuo.Nontrivial := S.nontrivial_Siu.mono S.Siu_subset

end PersonSpace

/-! ### The inventory of persons -/

/-- Third person `[DIST]`. -/
def third : List Feature := [.dist]

/-- Second person `[PROX–DIST]`. -/
def second : List Feature := [.prox, .dist]

/-- First person `[PROX–PROX]`. -/
def first : List Feature := [.prox, .prox]

/-- First person inclusive `[PROX]`. -/
def inclusive : List Feature := [.prox]

section Semantics

variable (S : PersonSpace α) {fs : List Feature} {L : Layered (Set α)}

theorem eval_third : S.layered.eval third = some ⟨S.Siuo \ S.Siu, []⟩ := rfl

theorem eval_second : S.layered.eval second = some ⟨S.Siu \ S.Si, []⟩ := rfl

theorem eval_first : S.layered.eval first = some ⟨S.Si, []⟩ := rfl

theorem eval_inclusive : S.layered.eval inclusive = some ⟨S.Siu, [S.Si]⟩ := rfl

/-- The person features have an output for exactly five structures, the four persons and the
structure with no feature. -/
theorem isSome_eval_layered_iff :
    (S.layered.eval fs).isSome ↔ fs ∈ [[], inclusive, first, second, third] := by
  rw [Layered.isSome_eval_iff]
  change fs.length ≤ 2 ∧ _ ↔ _
  rcases fs with _ | ⟨f, _ | ⟨g, _ | ⟨h, fs⟩⟩⟩
  · decide
  · cases f <;> decide
  · cases f <;> cases g <;> decide
  · simp [inclusive, first, second, third]

variable {S} in
theorem eq_nil_or_of_eval (h : S.layered.eval fs = some L) :
    fs = [] ∨ fs = inclusive ∨ fs = first ∨ fs = second ∨ fs = third := by
  simpa using (isSome_eval_layered_iff S).1 (Option.isSome_of_eq_some h)

variable {S} in
theorem nonempty_of_eval (h : S.layered.eval fs = some L) (hfs : fs ≠ third) : L.set.Nonempty := by
  rcases eq_nil_or_of_eval h with rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj h
  exacts [S.nontrivial_Siuo.nonempty, S.nontrivial_Siu.nonempty, ⟨_, S.speaker_mem⟩,
    ⟨_, S.addressee_mem, S.addressee_notMem⟩, absurd rfl hfs]

/-! ### Participants

The speaker and the addressee are placed alike in every person space, so the participants in
the set a feature structure delivers do not depend on the space. -/

/-- The discourse participants in the set a feature structure delivers, computed in the space of
the speaker and the addressee alone. -/
def participants (fs : List Feature) : Option (Finset Role) :=
  ((⟨.univ, [.univ, {.speaker}]⟩ : Layered (Finset Role)).eval fs).map (·.set)

theorem preimage_atom_eval (fs : List Feature) :
    (S.layered.eval fs).map (S.atom ⁻¹' ·.set) = (participants fs).map (↑) := by
  have h : S.layered.map (S.atom ⁻¹' ·) =
      (⟨.univ, [.univ, {.speaker}]⟩ : Layered (Finset Role)).map (↑) := by
    simp [PersonSpace.layered, Layered.map, Set.ext_iff, PersonSpace.atom, S.speaker_mem,
      S.addressee_mem, S.addressee_notMem, S.Si_subset S.speaker_mem,
      S.Siu_subset S.addressee_mem, S.Siu_subset (S.Si_subset S.speaker_mem)]
  have h₁ := Layered.eval_map (g := (S.atom ⁻¹' ·)) (fun _ _ ↦ Set.preimage_sdiff ..) S.layered fs
  rw [h, Layered.eval_map (g := ((↑) : Finset Role → Set Role)) Finset.coe_sdiff] at h₁
  simpa [participants, Function.comp_def, Layered.map] using congrArg (·.map (·.set)) h₁.symm

theorem ofParticipants_participants :
    (participants first).map Person.ofParticipants = some .firstExclusive ∧
      (participants inclusive).map Person.ofParticipants = some .firstInclusive ∧
      (participants second).map Person.ofParticipants = some .second ∧
      (participants third).map Person.ofParticipants = some .third := by
  decide

end Semantics

/-! ### Number

Number is interpreted on the output of the person features. Without `PL` the output has at
most one member, and `PL` requires more than one. -/

/-- `PL` is defined on a set with more than one member that the person features deliver, and
not on their input. -/
def PersonSpace.PluralDefined (S : PersonSpace α) (L : Layered (Set α)) : Prop :=
  L.set.Nontrivial ∧ L ≠ S.layered

theorem PersonSpace.pluralDefined_iff {S : PersonSpace α} {fs : List Feature}
    {L : Layered (Set α)} (h : S.layered.eval fs = some L) :
    S.PluralDefined L ↔ L.set.Nontrivial ∧ fs ≠ [] :=
  and_congr_right fun _ ↦ not_congr
    ⟨fun e ↦ Layered.eval_eq_some_self_iff.1 (e ▸ h), fun e ↦ by simpa [e] using h.symm⟩

/-- A pronoun is a person feature structure under a number node, with `PL` or without. -/
structure Pronoun where
  /-- The person feature structure. -/
  person : List Feature
  /-- Whether the number node bears `PL`. -/
  plural : Bool
  deriving DecidableEq

/-- A pronoun denotes a set in a person space that its person features deliver and its number
accepts. -/
def Pronoun.Denotes (p : Pronoun) (S : PersonSpace α) (L : Layered (Set α)) : Prop :=
  S.layered.eval p.person = some L ∧ if p.plural then S.PluralDefined L else L.set.Subsingleton

/-- The seven pronouns, three singular and four plural. -/
def inventory : List Pronoun :=
  [⟨first, false⟩, ⟨second, false⟩, ⟨third, false⟩, ⟨inclusive, true⟩, ⟨first, true⟩,
    ⟨second, true⟩, ⟨third, true⟩]

/-- The person space of a speaker and an addressee alone. -/
private def pair : PersonSpace ℕ :=
  ⟨0, 1, {0}, {0, 1}, {0, 1}, rfl, by simp, by simp, by simp, subset_rfl⟩

/-- A person space with two members in each layer. -/
private def crowd : PersonSpace ℕ :=
  ⟨0, 2, .Iio 2, .Iio 4, .Iio 6, by simp, by simp, by simp, Set.Iio_subset_Iio (by decide),
    Set.Iio_subset_Iio (by decide)⟩

/-- The inventory consists of the pronouns with a denotation in some person space. The inclusive
has no singular, its set having two obligatory members, and the structure with no feature
neither a singular nor a plural, `PL` not being defined on its set. -/
theorem mem_inventory_iff {p : Pronoun} :
    p ∈ inventory ↔ ∃ (S : PersonSpace ℕ) (L : Layered (Set ℕ)), p.Denotes S L := by
  refine ⟨fun h ↦ ?_, fun ⟨S, L, h, hn⟩ ↦ ?_⟩
  · simp only [inventory, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pair, _, eval_first _, Set.subsingleton_singleton⟩
    · exact ⟨pair, _, eval_second _, by simp [pair, Set.Subsingleton]⟩
    · exact ⟨pair, _, eval_third _, by simp [pair]⟩
    · exact ⟨crowd, _, eval_inclusive _,
        (PersonSpace.pluralDefined_iff (eval_inclusive _)).2 ⟨crowd.nontrivial_Siu, by decide⟩⟩
    · exact ⟨crowd, _, eval_first _, (PersonSpace.pluralDefined_iff (eval_first _)).2
        ⟨⟨0, by simp [crowd], 1, by simp [crowd], by decide⟩, by decide⟩⟩
    · exact ⟨crowd, _, eval_second _, (PersonSpace.pluralDefined_iff (eval_second _)).2
        ⟨⟨2, by simp [crowd], 3, by simp [crowd], by decide⟩, by decide⟩⟩
    · exact ⟨crowd, _, eval_third _, (PersonSpace.pluralDefined_iff (eval_third _)).2
        ⟨⟨4, by simp [crowd], 5, by simp [crowd], by decide⟩, by decide⟩⟩
  · obtain ⟨fs, _ | _⟩ := p <;> rcases eq_nil_or_of_eval h with rfl | rfl | rfl | rfl | rfl
    · exact absurd (Option.some.inj h ▸ hn :) S.nontrivial_Siuo.not_subsingleton
    · exact absurd (Option.some.inj h ▸ hn :) S.nontrivial_Siu.not_subsingleton
    all_goals first | decide | exact absurd rfl ((PersonSpace.pluralDefined_iff h).1 hn).2

/-- The referential categories a pronoun covers are those with the participants its person
features deliver that are groups exactly when it is plural. -/
def Pronoun.categories (p : Pronoun) : Finset Person.Category :=
  {c | participants p.person = some c.participants ∧ (c.IsGroup ↔ p.plural)}

theorem map_categories_inventory :
    inventory.map Pronoun.categories =
      [{.speaker}, {.addressee}, {.other}, {.speakerAddressee, .speakerAddresseeOthers},
        {.speakerOthers}, {.addresseeOthers}, {.others}] := by
  decide

/-! ### Expletives -/

/-- A pronoun can be an expletive when it denotes the empty set in some person space. -/
def Pronoun.CanBeExpletive (p : Pronoun) : Prop :=
  ∃ (S : PersonSpace ℕ) (L : Layered (Set ℕ)), p.Denotes S L ∧ L.set = ∅

/-- Only the third person singular can be an expletive, since `DIST` alone can deliver the empty
set and `PL` is not defined on it. -/
theorem canBeExpletive_iff {p : Pronoun} : p.CanBeExpletive ↔ p = ⟨third, false⟩ := by
  refine ⟨fun ⟨S, L, ⟨h, hn⟩, he⟩ ↦ ?_, ?_⟩
  · obtain ⟨fs, n⟩ := p
    obtain rfl : fs = third := by_contra fun hfs ↦ (nonempty_of_eval h hfs).ne_empty he
    cases n
    exacts [rfl, absurd he hn.1.nonempty.ne_empty]
  · rintro rfl
    exact ⟨pair, _, ⟨eval_third _, by simp [pair]⟩, by simp [pair]⟩

instance : DecidablePred Pronoun.CanBeExpletive := fun _ ↦
  decidable_of_iff _ canBeExpletive_iff.symm

/-- The subject pronoun of an example, by its `person` label. -/
def subject? (e : Datum) : Option Pronoun :=
  e.parse? "person" [("first", ⟨first, false⟩), ("second", ⟨second, false⟩),
    ("third", ⟨third, false⟩), ("featureless", ⟨[], false⟩)]

/-- The paper reports an expletive subject acceptable exactly when its pronoun can be an
expletive. -/
theorem acceptable_iff_canBeExpletive :
    ∀ e ∈ Examples.all, e.feature? "phenomenon" = some "expletive" →
      ∃ p ∈ subject? e, (e.judgment = .acceptable ↔ p.CanBeExpletive) := by
  decide

/-! ### Spell-out and Maximal Encoding -/

/-- A spell-out rule inserts a form for the person features it mentions, counted with
multiplicity, with `PL` or without. -/
structure SpellOut (E : Type*) where
  /-- The person features mentioned. -/
  features : Multiset Feature
  /-- Whether `PL` is mentioned. -/
  plural : Bool
  /-- The form inserted. -/
  exponent : E

/-- A rule applies to a pronoun that has every feature it mentions. -/
instance : Rule (SpellOut E) Pronoun E where
  exponent := SpellOut.exponent
  Applies r p := r.features ≤ p.person ∧ r.plural ≤ p.plural

instance : DecidableRel (Applies : SpellOut E → Pronoun → Prop) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The number of features a rule mentions. -/
def SpellOut.size (r : SpellOut E) : ℕ := r.features.card + r.plural.toNat

section NaturalClasses

variable {r : SpellOut E} {n : Bool}

theorem shared_features :
    (first : Multiset Feature) ∩ second = {.prox} ∧ (second : Multiset Feature) ∩ third = {.dist} ∧
      (first : Multiset Feature) ∩ third = 0 := by
  decide

theorem applies_of_inter_le {fs gs hs : List Feature} (hf : Applies r (⟨fs, n⟩ : Pronoun))
    (hg : Applies r (⟨gs, n⟩ : Pronoun)) (h : (fs : Multiset Feature) ∩ gs ≤ hs) :
    Applies r (⟨hs, n⟩ : Pronoun) :=
  ⟨(Multiset.le_inter hf.1 hg.1).trans h, hf.2⟩

theorem applies_second_of_first_of_third (h₁ : Applies r (⟨first, n⟩ : Pronoun))
    (h₃ : Applies r (⟨third, n⟩ : Pronoun)) : Applies r (⟨second, n⟩ : Pronoun) :=
  applies_of_inter_le h₁ h₃ (by decide)

theorem applies_first_of_inclusive_of_second (h₁ : Applies r (⟨inclusive, n⟩ : Pronoun))
    (h₂ : Applies r (⟨second, n⟩ : Pronoun)) : Applies r (⟨first, n⟩ : Pronoun) :=
  applies_of_inter_le h₁ h₂ (by decide)

theorem applies_exclusive_iff_first (h : r.plural = false) :
    Applies r (⟨first, true⟩ : Pronoun) ↔ Applies r ⟨first, false⟩ := by
  simp [Applies, h]

end NaturalClasses

open Dutch.Pronouns in
/-- The spell-out rules of the Dutch strong subject pronouns, none of which mentions two
`PROX`. -/
def dutch : RuleSet (SpellOut PersonalPronoun) :=
  [⟨{.prox}, false, ik⟩, ⟨{.prox, .dist}, false, jij⟩, ⟨{.dist}, false, hij⟩,
    ⟨{.prox}, true, wij⟩, ⟨{.prox, .dist}, true, jullie⟩, ⟨{.dist}, true, zij_pl⟩]

open Dutch.Pronouns in
/-- Under Maximal Encoding the rule mentioning the most features is used, so the Dutch rules
realize the inventory with one form for the inclusive and the exclusive. -/
theorem dutch_paradigm :
    inventory.map (dutch.realize SpellOut.size) =
      [some ik, some jij, some hij, some wij, some wij, some jullie, some zij_pl] := by
  decide

/-- Each Dutch pronoun denotes the referential categories that the pronouns it realizes cover. -/
theorem dutch_referential : ∀ r ∈ dutch, ∀ c,
    c ∈ r.exponent.referential ↔
      ∃ p ∈ inventory, dutch.realize SpellOut.size p = some r.exponent ∧ c ∈ p.categories := by
  decide

/-- A rule set with a rule mentioning two `PROX` and a rule mentioning one, both with `PL`. -/
def clusive (a b : E) : RuleSet (SpellOut E) := [⟨{.prox, .prox}, true, a⟩, ⟨{.prox}, true, b⟩]

theorem clusive_split (a b : E) :
    (clusive a b).realize SpellOut.size ⟨first, true⟩ = some a ∧
      (clusive a b).realize SpellOut.size ⟨inclusive, true⟩ = some b :=
  ⟨rfl, rfl⟩

/-! ### Zwicky's generalization

No natural class holds the inclusive and the second person without the exclusive, so no rule
marks them alike to the exclusion of the exclusive. Impoverishment can still bring them
together: deleting `DIST` under `PROX` in the plural gives the second person plural the
inclusive's structure. In a language that spells out one and two `PROX` apart, the exclusive is
then marked apart from the inclusive and the second person, which is why the chapter takes
Zwicky's generalization to be statistical. Harbour's parameters never generate that system. -/

/-- Impoverishment of `DIST` under `PROX` in the plural: the second person plural loses its
`DIST`. -/
def impoverishDist : Pronoun → Pronoun
  | ⟨[.prox, .dist], true⟩ => ⟨[.prox], true⟩
  | p => p

/-- The system a realization of the plural pronouns induces on participant sets: two are related
when pronouns with those participants are realized alike. -/
def pluralGraph [DecidableEq E] (f : Pronoun → Option E) : Finset (Finset Role × Finset Role) :=
  Finset.univ.filter fun P ↦ ∃ p ∈ inventory, ∃ q ∈ inventory, p.plural ∧ q.plural ∧
    participants p.person = some P.1 ∧ participants q.person = some P.2 ∧ f p = f q

/-- Plural rules for two `PROX`, one `PROX`, `PROX` with `DIST`, and `DIST`. -/
def pluralRules : RuleSet (SpellOut (Fin 4)) :=
  [⟨{.prox, .prox}, true, 0⟩, ⟨{.prox}, true, 1⟩, ⟨{.prox, .dist}, true, 2⟩, ⟨{.dist}, true, 3⟩]

-- without impoverishment the plural paradigm is the quadripartition
theorem pluralGraph_pluralRules :
    pluralGraph (pluralRules.realize SpellOut.size) = Harbour2016.graph {.author, .hearer} := by
  decide

-- with it, Zwicky's tripartition: the inclusive with the second person, the exclusive apart
theorem pluralGraph_pluralRules_impoverishDist :
    pluralGraph (pluralRules.realize SpellOut.size ∘ impoverishDist) =
      Harbour2016.graph {.hearer, .participant} := by
  decide

/-- Impoverishing `DIST` under `PROX` in the plural turns a plural paradigm that Harbour's
parameters generate into one they never generate, Zwicky's tripartition. -/
theorem impoverishDist_not_mem_image_graph :
    pluralGraph (pluralRules.realize SpellOut.size) ∈
        Finset.univ.image Harbour2016.Setting.graph ∧
      pluralGraph (pluralRules.realize SpellOut.size ∘ impoverishDist) ∉
        Finset.univ.image Harbour2016.Setting.graph := by
  rw [pluralGraph_pluralRules, pluralGraph_pluralRules_impoverishDist,
    Harbour2016.graph_mem_image_iff, Harbour2016.graph_mem_image_iff]
  decide

end AckemaNeeleman2018
