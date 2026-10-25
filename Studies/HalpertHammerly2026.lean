module

public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Person.Features
public import Linglib.Fragments.Xhosa.Nouns
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Data.Examples.HalpertHammerly2026
public import Studies.Carstens2026
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Halpert and Hammerly (2026): Reconciling Animacy and Noun Class in Bantu

This file formalizes the Core Noun Class Hypothesis: every Bantu noun is specified for
[±Animate, ±Human] on its nominalizing head, Kramer's gendered n, and so belongs to one of the
core classes HUMAN, ANIMATE and INANIMATE, canonically classes 1/2, 9/10 and 7/8 (19), whatever
class its prefix shows. The features are Hammerly's containment sets of ontological primitives
ranked by prominence (1), so every category a specification denotes is order-convex, and no
conflation in McGinnis's sense groups humans with natural forces to the exclusion of animals.

Class prefixes are secondary n's stacked over the core, as in Fuchs and van der Wal's
diminutives, so a nominal is Carstens's stacked nominal over the core classes. Agreement depends
on the probe (29): a flat probe finds the secondary n and agrees with the prefix class, as in
Zulu, while a probe relativized to [+Animate] searches past it to the core, the animacy override
of Chiyao and Swahili and the animate-only object marking of Nyaturu.

## Main results

* `category_ordConnected`: every category is order-convex.
* `agreement_flat`, `agreement_animateProbe`: a flat probe agrees with the prefix class and a
  relativized one with the core.
* `isikhohleli_agreement`: *isikhohleli* 'coughing person' agrees in class 7 or class 1 by the
  probe.

## Implementation notes

* A nominal has a secondary n only when its prefix class is a core class other than its core's;
  `ofEntry` is undefined for classes 3/4 and 5/6, whose features the paper leaves open.
* The fragment's semantic animacy stands in for the grammatical core, which the paper allows to
  be idiosyncratic.
* Agreement with conjoined subjects, (15) to (18), is recorded as data only.

## References

* [halpert-hammerly-2026]
* [hammerly-2023]
* [mcginnis-2005]
* [fuchs-van-der-wal-2022]
* [taraldsen-et-al-2018]
* [carstens-2026]
* [kramer-2015]
-/

@[expose] public section

namespace HalpertHammerly2026

open Bantu Minimalist

/-! ### Containment features, section 2 -/

/-- The ontological primitives of (1) and (3), most prominent first, which are the author I, the
addressee U, other humans O, animals A, natural forces F, concrete things R, and abstract
things S. -/
inductive Primitive where
  | author | addressee | human | animal | force | concrete | abstract
  deriving DecidableEq, Repr, Fintype

namespace Primitive

/-- Prominence rank, the author highest. -/
def rank : Primitive → ℕ
  | .author => 0 | .addressee => 1 | .human => 2 | .animal => 3
  | .force => 4 | .concrete => 5 | .abstract => 6

/-- The prominence order (1), `author < addressee < human < animal < force < concrete <
abstract`. -/
instance : LinearOrder Primitive :=
  LinearOrder.lift' rank (fun a b h ↦ by cases a <;> cases b <;> simp_all [rank])

end Primitive

/-- A feature of (3), the primitives at least as prominent as its cutoff. [Author] is
`feature .author`, [Participant] `feature .addressee`, [Human] `feature .human`, [Animate]
`feature .animal`, [Agent] `feature .force`, [Individuated] `feature .concrete`, and ɸ
`feature .abstract`, each contained in the next. -/
abbrev feature (p : Primitive) : Set Primitive := Set.Iic p

/-- A bivalent value of a feature, the feature itself or its complement. -/
def value (p : Primitive) : Bool → Set Primitive
  | true => feature p
  | false => (feature p)ᶜ

theorem value_ordConnected (p : Primitive) (b : Bool) : (value p b).OrdConnected := by
  cases b
  · rw [value, feature, Set.compl_Iic]; exact Set.ordConnected_Ioi
  · exact Set.ordConnected_Iic

/-- A specification, the value, if any, of each feature. -/
abbrev Spec := Primitive → Option Bool

/-- The category a specification defines, the intersection of the values it specifies ((4),
(5)); a feature left unspecified is conflated. -/
def category (s : Spec) : Set Primitive := ⋂ p, ⋂ b ∈ s p, value p b

theorem mem_category {s : Spec} {x : Primitive} :
    x ∈ category s ↔ ∀ p b, s p = some b → (x ≤ p ↔ b = true) := by
  simp only [category, Set.mem_iInter, Option.mem_def]
  refine forall₂_congr fun p b ↦ imp_congr_right fun _ ↦ ?_
  cases b <;> simp [value, feature]

/-- Feature-definable categories are order-convex. -/
theorem category_ordConnected (s : Spec) : (category s).OrdConnected :=
  Set.ordConnected_iInter fun p ↦ Set.ordConnected_biInter fun b _ ↦ value_ordConnected p b

theorem animal_mem_category {s : Spec} (h₁ : .human ∈ category s)
    (h₂ : .force ∈ category s) : .animal ∈ category s :=
  (category_ordConnected s).out h₁ h₂ ⟨by decide, by decide⟩

/-- The full specification singling out a primitive (4), positive on every feature at or above it
and negative on every feature below it. -/
def contrast (p : Primitive) : Spec := fun q ↦ some (decide (p ≤ q))

/-- At the limit each primitive defines its own category, the leaves of the contrastive
hierarchy (4). -/
theorem category_contrast (p : Primitive) : category (contrast p) = {p} := by
  ext x
  simp only [mem_category, contrast, Option.some.injEq, Set.mem_singleton_iff]
  revert x p
  decide

/-! ### Core noun classes, (19) and (22) -/

/-- The bivalent features [±Animate, ±Human] of a Bantu nominalizing head (19), [+Human]
entailing [+Animate]. -/
inductive AnimacyFeature where
  | animate
  | human
  deriving DecidableEq, Repr, Fintype

/-- Position on the dependency chain, animate below human. -/
def AnimacyFeature.rank : AnimacyFeature → Fin 2
  | .animate => 0
  | .human => 1

instance : LinearOrder AnimacyFeature := LinearOrder.lift' AnimacyFeature.rank (by decide)

/-- The features of a nominalizing head, its positive ones. -/
abbrev AnimacyFeatures := Finset AnimacyFeature

namespace AnimacyFeatures

/-- A specification is coherent when [+Human] entails [+Animate] (footnote 10). -/
abbrev WellFormed (af : AnimacyFeatures) : Prop := IsLowerSet (↑af : Set AnimacyFeature)

/-- The features as a specification of the [Animate] and [Human] features of (3). -/
def spec (af : AnimacyFeatures) : Spec := fun q ↦
  if q = .animal then some (decide (.animate ∈ af))
  else if q = .human then some (decide (.human ∈ af)) else none

theorem category_spec_eq_empty_iff (af : AnimacyFeatures) :
    category af.spec = ∅ ↔ ¬ af.WellFormed := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_category]
  revert af
  decide

end AnimacyFeatures

/-- A core noun class (19), a coherent specification of [±Animate, ±Human]. -/
abbrev Core := {af : AnimacyFeatures // af.WellFormed}

namespace Core

/-- HUMAN, [+Animate, +Human]. -/
def human : Core := ⟨{.animate, .human}, by decide⟩

/-- ANIMATE, [+Animate, −Human]. -/
def animal : Core := ⟨{.animate}, by decide⟩

/-- INANIMATE, [−Animate, −Human]. -/
def inanimate : Core := ⟨∅, by decide⟩

/-- HUMAN denotes every primitive down to the local persons, so its class contains the speech-act
participants ((8), (10)). -/
theorem category_spec_human : category human.1.spec = Set.Iic .human := by
  ext x
  simp only [mem_category, Set.mem_Iic]
  revert x
  decide

/-- INANIMATE is the conflation of natural forces, concrete things, and abstract things, the
GENERIC INANIMATE of (5). -/
theorem category_spec_inanimate : category inanimate.1.spec = Set.Ioi .animal := by
  ext x
  simp only [mem_category, Set.mem_Ioi]
  revert x
  decide

/-- The core class of a referent of a given animacy. -/
def ofAnimacy : Animacy → Core
  | .human => human
  | .animate => animal
  | .inanimate => inanimate

/-- In Xhosa (19), HUMAN is class 1/2, ANIMATE class 9/10, and INANIMATE class 7/8. -/
def gender (c : Core) : Xhosa.Gender :=
  if .human ∈ c.1 then .genderA else if .animate ∈ c.1 then .genderE else .genderD

/-- The core class of a gender, read off the semantic core the fragment records for it; none
for a purely formal gender. -/
def ofGender (g : Xhosa.Gender) : Option Core :=
  match g.status with
  | .interpretable .human => some human
  | .interpretable .animal => some animal
  | .interpretable .inanimate => some inanimate
  | _ => none

/-- The classes of (19) agree with the fragment's semantic cores, the gender a core class is spelled
out in bearing that core. -/
theorem ofGender_gender : ∀ c : Core, ofGender c.gender = some c := by decide

theorem gender_eq_of_ofGender {g : Xhosa.Gender} {c : Core} (h : ofGender g = some c) :
    c.gender = g := by
  revert h; revert c; revert g; decide

/-- The nominalizing final vowels (22). -/
inductive FinalVowel where
  | i | o
  deriving DecidableEq, Repr

/-- By (22) the core n is spelled out as -i when [+Human] and as -o otherwise. -/
def finalVowel (c : Core) : FinalVowel := if .human ∈ c.1 then .i else .o

theorem finalVowel_eq_i_iff (c : Core) : c.finalVowel = .i ↔ c.gender = .genderA := by
  revert c; decide

/-- An exponent conditioned on [±Animate] alone, like Swahili animacy override (13), treats humans
and animals alike (5). -/
theorem eq_of_factorsThrough_animate {β : Type*} {f : Core → β}
    (hf : Function.FactorsThrough f (decide <| .animate ∈ ·.1)) : f human = f animal :=
  hf (a := human) (b := animal) (by decide)

theorem not_factorsThrough_gender :
    ¬ Function.FactorsThrough gender (decide <| .animate ∈ ·.1) :=
  fun h ↦ absurd (h (a := human) (b := animal) (by decide)) (by decide)

/-- The plural subject marker of a core class's gender. -/
def pluralSubjPrefix (c : Core) : String := c.gender.plSubjPrefix

/-- The Xhosa plural subject marker is conditioned on [±Human] alone, so classes 8 and 10 share
*zi-* (footnote 7). -/
theorem pluralSubjPrefix_factorsThrough :
    Function.FactorsThrough pluralSubjPrefix (decide <| .human ∈ ·.1) := by
  intro a b; revert a b; decide

end Core

/-! ### Local persons -/

/-- The person features [±Participant, ±Author] as a specification of (3). -/
def personSpec (pf : Person.Features) : Spec := fun q ↦
  if q = .addressee then some (decide (.participant ∈ pf))
  else if q = .author then some (decide (.author ∈ pf)) else none

/-- A participant's category lies inside HUMAN, so a class 1/2 probe finds local persons ((8), (10),
section 3.2). -/
theorem category_personSpec_subset {pf : Person.Features} (h : .participant ∈ pf) :
    category (personSpec pf) ⊆ category Core.human.1.spec := by
  rw [Core.category_spec_human]
  intro x hx
  have hx' := mem_category.mp hx .addressee (decide (.participant ∈ pf)) (by simp [personSpec])
  rw [decide_eq_true h] at hx'
  exact le_trans (hx'.mpr rfl) (by decide)

/-! ### Stacked nominals, (26) to (29)

A nominal is [carstens-2026]'s stacked nominal over the core classes: the core n beneath an
optional secondary n with a class feature of its own ((27), (28)). An aligned noun's secondary n
bears none and is spelled out by the core. -/

open Carstens2026

/-- The class prefix, the allomorph of the outermost n (27). -/
def prefixGender (n : Nominal Core) : Xhosa.Gender := n.visible.gender

/-- The nominal of a Xhosa noun (28), with the core from the entity denoted and a secondary n
bearing the features of the noun's gender when that is a core class other than the core's. It
is undefined for the genders whose features the paper leaves open. -/
def ofEntry (e : Xhosa.Noun) : Option (Nominal Core) :=
  (Core.ofGender e.gender).map (.stack (Core.ofAnimacy e.animacy))

theorem prefixGender_eq_gender {e : Xhosa.Noun} {n : Nominal Core} (h : ofEntry e = some n) :
    prefixGender n = e.gender := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa [prefixGender] using Core.gender_eq_of_ofGender hs

/-- *Isikhohleli* 'coughing person' (28) is a human core under a class 7 secondary n. -/
theorem ofEntry_isikhohleli :
    ofEntry Xhosa.Nouns.isikhohleli = some ⟨Core.human, some Core.inanimate⟩ := by decide

/-- In (27a) and (27c) *umkhohleli* 'coughing person' and *isikhohlela* 'phlegm' are aligned, the
prefix class the core's own. -/
theorem ofEntry_aligned :
    ofEntry Xhosa.Nouns.umkhohleli = some ⟨Core.human, none⟩ ∧
      ofEntry Xhosa.Nouns.isikhohlela = some ⟨Core.inanimate, none⟩ := by decide

/-- The flat ɸ probe of (29a), to which any n is visible. -/
def flat : Probe Core := Probe.indiscriminate

/-- The ɸ probe of (29b), relativized to [+Animate]. -/
def animateProbe : Probe Core := Probe.relativized (decide <| .animate ∈ ·.1)

/-- The gender a probe agrees in, the allomorph of the n it finds searching from the top. -/
def agreement (p : Probe Core) (n : Nominal Core) : Option Xhosa.Gender :=
  (p.search n.genders.reverse).map Core.gender

/-- In Zulu a flat probe finds the outermost n, so agreement tracks the prefix class (29a). -/
theorem agreement_flat (n : Nominal Core) : agreement flat n = some (prefixGender n) := by
  rcases n with ⟨c, _ | s⟩ <;> rfl

/-- With an inanimate secondary n over an animate core (28), the Swahili animate probe searches past
the secondary n to the core (29b). -/
theorem animateProbe_search {n : Nominal Core} (hc : .animate ∈ n.core.1)
    (hs : ∀ s ∈ n.outer, .animate ∉ s.1) :
    animateProbe.search n.genders.reverse = some n.core := by
  rcases n with ⟨c, _ | s⟩ <;> simp only at hc hs
  · simp [animateProbe, Probe.search, Nominal.genders, Probe.relativized, hc]
  · simp [animateProbe, Probe.search, Nominal.genders, Probe.relativized, hc, hs s rfl]

/-- Under animacy override ((11), (13)) the relativized probe agrees with the core class. -/
theorem agreement_animateProbe {n : Nominal Core} (hc : .animate ∈ n.core.1)
    (hs : ∀ s ∈ n.outer, .animate ∉ s.1) :
    agreement animateProbe n = some n.core.gender := by
  rw [agreement, animateProbe_search hc hs, Option.map_some]

/-- In Nyaturu object doubling (14), the [+Animate] object probe is valued by an aligned noun iff
its core is animate. -/
theorem animateProbe_search_isSome (c : Core) :
    (animateProbe.search (Nominal.mk c none).genders.reverse).isSome ↔ .animate ∈ c.1 := by
  simp [Nominal.genders, animateProbe]

/-- By (28) and (29) *isikhohleli* agrees in class 7 with a flat probe and in class 1 with the
relativized one. -/
theorem isikhohleli_agreement :
    (ofEntry Xhosa.Nouns.isikhohleli).bind (agreement flat) = some .genderD ∧
      (ofEntry Xhosa.Nouns.isikhohleli).bind (agreement animateProbe) = some .genderA := by
  decide

end HalpertHammerly2026
