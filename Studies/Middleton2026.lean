module

public import Mathlib.Data.List.DropRight
public import Mathlib.Data.List.Permutation
public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Fragments.Taos.Agreement
public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Feature.Person.Features
public import Linglib.Phonology.RuleInteraction

/-!
# Middleton (2026): A Remark on the Ordering of Impoverishment Rules: Differences between Taos and Basque

The Taos agreement prefix has three arguments, the agent, the goal and the object (`Prefix`),
each a list of person and number features. A rule of impoverishment (`Rule`) changes the argument
of one slot where a condition on the prefix holds; it is paradigmatic when the condition factors
through that slot's own argument, and syntagmatic otherwise. Applying a list of rules in order is
`run`, and a list respects the block architecture of Arregi and Nevins (`ParadigmaticFirst`) when
no syntagmatic rule precedes a paradigmatic one. A rule only deletes features
(`Rule.get_apply_sublist`).

A rule changing one slot leaves the condition of a paradigmatic rule of another slot as it was
(`Rule.fires_apply_iff_of_paradigmatic`), so a rule that a rule of another slot bleeds is
syntagmatic (`Rule.syntagmatic_of_bleeds`). In four Taos interactions a paradigmatic rule bleeds
a syntagmatic rule that the attested prefix needs, and in a fifth the attested prefix needs the
bleeding; an order with the first and the fifth is in neither block order (`must_interleave`).
The rules the paper labels paradigmatic and syntagmatic are so (`paradigmatic_of_labelled`,
`syntagmatic_of_labelled`).

After impoverishment the prefix is linearized into a string of feature terminals, to which
metathesis, exponence, epenthesis and tone apply. `derive` composes these maps, and
`derive_eq_form` compares its value with the paradigm of `Fragments/Taos/Agreement.lean`.
Impoverishment feeds metathesis in Taos (`r24_feeds_m23`), and feeds and bleeds it in Basque
(`Basque.ondarru_feeds`, `Basque.zamudio_bleeds`).

## Implementation notes

* The prefix is a structure with a field for each argument, not a function `Slot → Arg`, so that
  a rule's condition reads `p.agent` and `p.goal`; `Prefix.get` and `Prefix.set` are its
  evaluation and update, and `Prefix.around` presents a slot as the focus of a neighborhood, on
  which `ImpoverishmentRule` is stated.
* Inverse number is the one feature `Feat.inverse`, which `Arg.Has` reads as containing the
  dual's values (`dual_le_inverse`); the category labels *s*, *d*, *p*, *i* are exact tests
  on the number features (`Arg.IsSingular` and kin).
* The paper labels its (35) and (43), the appendix's (40) and (26), paradigmatic, and each is
  printed with a bracket for another slot: `RuleName.rule` follows the labels, `RuleName.printed`
  the printed rules, and both sets derive the paradigm (`derive_eq_form_printed`).
* Five rules differ from the appendix's listing: (32) is ordered after (7) and (44) after (43),
  (44) applies before a plural object too, (7) applies only while the agent has number, and
  (38a) applies to an agent whose `[+minimal]` is already deleted (see the constructors of
  `RuleName`). Rules (2) and (3) read "3" as `[−author]`.
* Exponence is the appendix's rules as `ExponenceRule`s, each bracket read in the adjacent window
  of a tier (`onTiers`), the present arguments keeping an agent impoverishment has left only
  `[+author]`, as the appendix's trace reading has it; a third person object's number is null
  (`objectNumberNull`). The portmanteaux, epenthesis and tone carry the additions the appendix's
  prose uses but never states (see `exponence`).
* Forms are strings, as in the fragment, so epenthesis and tone are stated on characters.

## TODO

* The nine cells in `unaccounted`, with what the pipeline gives them in
  `derive_unaccounted`: ∅:2s:∅ and 1:2s:∅ (*o*; the appendix says it will return to them and
  does not, and the rules give *kǫ*), 3i:3p (printed toneless; footnote 5 calls that a typo
  for high, but (50c) gives a closed final syllable falling, *îw*), 3i:refl (printed *ímó*;
  the rules give footnote 6's corrected *ímo*), and the three 3d possessives with an object
  (Table 3 prints *ónôm* and *ónôw*, but the tone rule (51h) and the appendix's Tables 8, 14,
  17 and 38 have *ónóm* and *ónów*, which the rules give).
* The paper's (13) is an adjacent swap; the study follows Arregi and Nevins's fronting rule,
  which the Zamudio auxiliary of (19) needs, and its rejected-order outputs are Arregi and
  Nevins's stranded forms rather than the paper's starred (17b) and (19b).

## References

* [J. Middleton, *A remark on the ordering of impoverishment rules: differences between Taos
  and Basque*][middleton-2026]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [D. Harbour, *The Kiowa case for feature insertion*][harbour-2003]
* [D. Harbour, *Valence and atomic number*][harbour-2011]
* [D. Harbour, *Paucity, abundance, and the theory of number*][harbour-2014]
* [D. Harbour, *Impossible persons*][harbour-2016]
* [B. Moskal and P. W. Smith, *Towards a theory without adjacency: hyper-contextual
  VI-rules*][moskal-smith-2016]
-/

@[expose] public section

namespace Middleton2026

open Minimalist DistributedMorphology Phonology Number

/-! ### Inherent and natural number

The noun classes of the appendix's Table 21 follow Harbour: a D head receives values of
`[±atomic]` and `[±minimal]` from the noun's class and from its natural number, its bundle is the
union of the two, and inverse agreement is a bundle carrying both values of a feature, the
configuration that on Number⁰ is Harbour's feature recursion. Harbour's `[±singular]` and
`[±augmented]` ([harbour-2011] Table 2) are `[±atomic]` and the negation of `[±minimal]`. -/

/-- The bundle a natural number contributes in a system with a dual, [harbour-2011]'s
decomposition (Table 2). -/
def natural : Number → Bundle
  | .singular => {(.atomic, true), (.minimal, true)}
  | .dual => {(.atomic, false), (.minimal, true)}
  | .plural => {(.atomic, false), (.minimal, false)}
  | _ => ∅

/-- The agreement category a D head shows: inverse when its bundle carries both values of a
feature, otherwise the number the bundle spells, if any. -/
def category (b : Bundle) : Option Number.Inverse.Category :=
  if ∃ f, b.CarriesBoth f then some .inverse
  else if b = natural .singular then some .singular
  else if b = natural .dual then some .dual
  else if b = natural .plural then some .plural
  else none

theorem category_natural_singular : category (natural .singular) = some .singular := by decide

theorem category_natural_dual : category (natural .dual) = some .dual := by decide

theorem category_natural_plural : category (natural .plural) = some .plural := by decide

/-! ### Noun classes

The four classes by inherent number ([harbour-2003], [harbour-2011]; appendix Table 21):
'one or two', 'two or more', 'two', and 'any number'. -/

/-- Class I, inherently `[+minimal]`: 'one or two'. -/
def classI : Bundle := {(.minimal, true)}

/-- Class II, inherently `[−atomic]`: 'two or more'. -/
def classII : Bundle := {(.atomic, false)}

/-- Class III, inherently `[−atomic +minimal]`: 'two'. -/
def classIII : Bundle := {(.atomic, false), (.minimal, true)}

/-- Class IV, with no inherent number: 'any number'. -/
def classIV : Bundle := ∅

theorem classI_category :
    category (classI ∪ natural .singular) = some .singular ∧
      category (classI ∪ natural .dual) = some .dual ∧
      category (classI ∪ natural .plural) = some .inverse := by
  decide

theorem classII_category :
    category (classII ∪ natural .singular) = some .inverse ∧
      category (classII ∪ natural .dual) = some .dual ∧
      category (classII ∪ natural .plural) = some .plural := by
  decide

theorem classIII_category :
    category (classIII ∪ natural .singular) = some .inverse ∧
      category (classIII ∪ natural .dual) = some .dual ∧
      category (classIII ∪ natural .plural) = some .inverse := by
  decide

theorem classIV_category :
    category (classIV ∪ natural .singular) = some .singular ∧
      category (classIV ∪ natural .dual) = some .dual ∧
      category (classIV ∪ natural .plural) = some .plural := by
  decide

-- Table 21
theorem dual_le_inverse :
    ∀ c ∈ [classI, classII, classIII, classIV], ∀ n ∈ [Number.singular, .dual, .plural],
    (∃ f, Bundle.CarriesBoth (c ∪ natural n) f) → natural .dual ⊆ c ∪ natural n := by
  decide

/-! ### Features and arguments

The paper's (2) and (3): Taos distinguishes three persons and three numbers, and inverse
agreement is the paper's (8), one feature here. The dummy object *no* and the reflexive are
the two objects without person. -/

/-- A feature of a Taos argument. The inventory is study-local rather than
`Minimalist.FeatureVal`, which has no inverse, dummy or reflexive feature. -/
inductive Feat where
  | participant (b : Bool)
  | author (b : Bool)
  | atomic (b : Bool)
  | minimal (b : Bool)
  | inverse
  | dummy
  | refl
  deriving DecidableEq, Repr

namespace Feat

/-- The person features are `[±participant]` and `[±author]`. -/
def IsPerson : Feat → Prop
  | .participant _ | .author _ => True
  | _ => False

/-- The number features are `[±atomic]`, `[±minimal]` and inverse. -/
def IsNumber : Feat → Prop
  | .atomic _ | .minimal _ | .inverse => True
  | _ => False

instance : DecidablePred IsPerson := fun f ↦ by cases f <;> unfold IsPerson <;> infer_instance

instance : DecidablePred IsNumber := fun f ↦ by cases f <;> unfold IsNumber <;> infer_instance

/-- The position of a feature within its argument after Linearization, the paper's (4) and
(5): `[±participant] [±author] [±atomic] [±minimal]`. -/
def rank : Feat → ℕ
  | .participant _ => 0
  | .author _ => 1
  | .atomic _ => 2
  | .minimal _ => 3
  | .inverse => 4
  | .dummy | .refl => 5

end Feat

/-- An argument is given by its features. -/
abbrev Arg := List Feat

/-- A person bears Harbour's bivalent features (3), `[+F]` for each feature of its bundle and
`[−F]` for the others. -/
def personFeats (p : Person) : Arg :=
  [.participant (decide (.participant ∈ p.toFeatures Finset.univ)),
    .author (decide (.speaker ∈ p.toFeatures Finset.univ))]

/-- A bundle bears Harbour's number features (2), each with the values it carries. -/
def bundleFeats (b : Bundle) : Arg :=
  ([true, false].filter fun v ↦ (Feature.atomic, v) ∈ b).map .atomic ++
    ([true, false].filter fun v ↦ (Feature.minimal, v) ∈ b).map .minimal

/-- An agreement category bears the features of its natural number's bundle; the inverse bears
the one feature `Feat.inverse` (see the implementation notes). -/
def numberFeats : Number.Inverse.Category → Arg
  | .singular => bundleFeats (natural .singular)
  | .dual => bundleFeats (natural .dual)
  | .plural => bundleFeats (natural .plural)
  | .inverse => [.inverse]

def first : Arg := personFeats .first
def second : Arg := personFeats .second
def third : Arg := personFeats .third
def singular : Arg := numberFeats .singular
def dual : Arg := numberFeats .dual
def plural : Arg := numberFeats .plural
def inverse : Arg := numberFeats .inverse

namespace Arg

/-- `a` has `f`, an inverse bundle containing the dual's values (`dual_le_inverse`). -/
def Has (a : Arg) (f : Feat) : Prop := f ∈ a ∨ .inverse ∈ a ∧ f ∈ dual

instance (a : Arg) : DecidablePred a.Has := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- `a` has every feature of `fs`. -/
def Bears (a fs : Arg) : Prop := ∀ f ∈ fs, a.Has f

instance (a fs : Arg) : Decidable (a.Bears fs) := inferInstanceAs (Decidable (∀ f ∈ fs, _))

/-- The number features. -/
def number (a : Arg) : Arg := a.filter (·.IsNumber)

/-- First person. -/
def IsFirst (a : Arg) : Prop := a.Bears first

/-- Second person. -/
def IsSecond (a : Arg) : Prop := a.Bears second

/-- Third person. -/
def IsThird (a : Arg) : Prop := a.Bears third

/-- Exactly singular. -/
def IsSingular (a : Arg) : Prop := a.number = singular

/-- Exactly dual. -/
def IsDual (a : Arg) : Prop := a.number = dual

/-- Exactly plural. -/
def IsPlural (a : Arg) : Prop := a.number = plural

/-- Inverse. -/
def IsInverse (a : Arg) : Prop := .inverse ∈ a

/-- Singular, its `[+minimal]` possibly already deleted. -/
def IsAtomicSingular (a : Arg) : Prop := .atomic true ∈ a ∧ .inverse ∉ a

/-- Has a `[±participant]` feature. -/
def HasParticipant (a : Arg) : Prop := ∃ b, .participant b ∈ a

instance : DecidablePred IsFirst := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsSecond := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsThird := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsSingular := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsDual := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsPlural := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsInverse := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))
instance : DecidablePred IsAtomicSingular := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred HasParticipant := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

end Arg

/-! ### The agreement prefix

The prefix of the paper's (1) agrees with the agent, the goal and the object, linearized in
that order. -/

/-- The three daughters of AgrP in (1), in linear order. -/
inductive Slot where
  | agent
  | goal
  | object
  deriving DecidableEq, Repr

/-- The agreement prefix of (1) has the agent, goal and object, an absent argument having no
features. -/
structure Prefix where
  /-- The agent. -/
  agent : Arg
  /-- The goal. -/
  goal : Arg
  /-- The object. -/
  object : Arg
  deriving DecidableEq, Repr

namespace Prefix

/-- The argument in a slot. -/
def get (p : Prefix) : Slot → Arg
  | .agent => p.agent
  | .goal => p.goal
  | .object => p.object

/-- Replace the argument in a slot. -/
def set (p : Prefix) : Slot → Arg → Prefix
  | .agent, a => { p with agent := a }
  | .goal, a => { p with goal := a }
  | .object, a => { p with object := a }

/-- The neighborhood of a slot has its argument in focus and the other two as context, in the order
of (1). -/
def around (p : Prefix) : Slot → Neighborhood Arg
  | .agent => ⟨p.agent, [], [p.goal, p.object]⟩
  | .goal => ⟨p.goal, [p.agent], [p.object]⟩
  | .object => ⟨p.object, [p.goal, p.agent], []⟩

/-- The prefix a slot's neighborhood came from. -/
def ofAround : Slot → Neighborhood Arg → Prefix
  | .agent, n => ⟨n.focus, n.rightCtx.getD 0 [], n.rightCtx.getD 1 []⟩
  | .goal, n => ⟨n.leftCtx.getD 0 [], n.focus, n.rightCtx.getD 0 []⟩
  | .object, n => ⟨n.leftCtx.getD 1 [], n.leftCtx.getD 0 [], n.focus⟩

@[simp] theorem ofAround_around (p : Prefix) (s : Slot) : ofAround s (p.around s) = p := by
  cases s <;> rfl

/-- A prefix is determined by the neighborhood of any of its slots. -/
def aroundEmbedding (s : Slot) : Prefix ↪ Neighborhood Arg :=
  ⟨(·.around s), Function.LeftInverse.injective fun p ↦ ofAround_around p s⟩

@[simp] theorem aroundEmbedding_apply (s : Slot) (p : Prefix) :
    aroundEmbedding s p = p.around s := rfl

@[simp] theorem focus_around (p : Prefix) (s : Slot) : (p.around s).focus = p.get s := by
  cases s <;> rfl

@[simp] theorem get_set_self (p : Prefix) (s : Slot) (a : Arg) : (p.set s a).get s = a := by
  cases s <;> rfl

@[simp] theorem set_get (p : Prefix) (s : Slot) : p.set s (p.get s) = p := by
  cases s <;> rfl

theorem get_set_of_ne (p : Prefix) {s t : Slot} (a : Arg) (h : t ≠ s) :
    (p.set s a).get t = p.get t := by
  cases s <;> cases t <;> first | rfl | exact absurd rfl h

/-- The leftmost number bundle is the first slot with a number feature. -/
def leftmostNumber (p : Prefix) : Option Slot :=
  if p.agent.number = [] then
    if p.goal.number = [] then
      if p.object.number = [] then none else some .object
    else some .goal
  else some .agent

/-- The features of the leftmost number bundle. -/
def leftmostNumberArg (p : Prefix) : Arg := (p.leftmostNumber.map p.get).getD []

/-- The second argument is the goal, or the object of a prefix without a goal. -/
def secondArg (p : Prefix) : Slot := if p.goal ≠ [] then .goal else .object

/-- The present arguments. -/
def args (p : Prefix) : List Arg := [p.agent, p.goal, p.object].filter (· ≠ [])

end Prefix

/-! ### Spell-Out -/

/-- Spell-Out: the prefix of a cell of the paradigm. -/
def spellOut (c : Taos.Cell) : Prefix where
  agent := (c.agent.map fun a ↦ personFeats a.1 ++ numberFeats a.2).getD []
  goal := (c.goal.map fun a ↦ personFeats a.1 ++ numberFeats a.2).getD []
  object := match c.object with
    | none => []
    | some .dummy => [.dummy]
    | some .reflexive => [.refl]
    | some (.third n) => third ++ numberFeats n

/-! ### Rules of impoverishment

A rule is the appendix's `X → E / context`: the slot whose argument changes, and an
`ImpoverishmentRule` at that slot's neighborhood whose target is the structural change. Rules the
appendix writes with an agent bracket followed by an object bracket apply only without a goal;
the appendix's prose orders (33) before (32), (5) before (7), and (45) before (40). -/

/-- The structural change of a rule deletes the features that satisfy `Deletes`. -/
structure Change where
  /-- The features the rule deletes. -/
  Deletes : Feat → Prop
  [dec : DecidablePred Deletes]

namespace Change

instance (c : Change) : DecidablePred c.Deletes := c.dec

/-- The features of `fs` are deleted. -/
protected def delete (fs : Arg) : Change := ⟨(· ∈ fs)⟩

/-- The number features are deleted. -/
def deleteNumber : Change := ⟨Feat.IsNumber⟩

/-- The person features are deleted. -/
def deletePerson : Change := ⟨Feat.IsPerson⟩

/-- Every feature is deleted. -/
def obliterate : Change := ⟨fun _ ↦ True⟩

/-- Apply a change to an argument. -/
def apply (c : Change) (a : Arg) : Arg := a.filter (¬ c.Deletes ·)

theorem apply_sublist (c : Change) (a : Arg) : (c.apply a).Sublist a := List.filter_sublist

end Change

/-- A rule of impoverishment over the prefix is a rule at the neighborhood of the slot whose
argument it changes. -/
structure Rule extends ImpoverishmentRule Arg Change where
  /-- The slot whose argument the rule changes. -/
  slot : Slot

namespace Rule

/-- A rule conditioned by its own slot's argument. -/
def paradigmatic (s : Slot) (check : Arg → Prop) [DecidablePred check] (c : Change) : Rule :=
  ⟨.ofFocus check c, s⟩

/-- A rule conditioned by the prefix. -/
def syntagmatic (s : Slot) (cond : Prefix → Prop) [DecidablePred cond] (c : Change) : Rule :=
  ⟨⟨fun n ↦ cond (Prefix.ofAround s n), c⟩, s⟩

/-- Apply the rule to the prefix. -/
def apply (r : Rule) (p : Prefix) : Prefix :=
  p.set r.slot (ImpoverishmentRule.apply (fun a c ↦ c.apply a) r.toImpoverishmentRule
    (p.around r.slot))

/-- The rule fires at a prefix when its condition holds at its slot's neighborhood. -/
def Fires (r : Rule) (p : Prefix) : Prop := r.condition (p.around r.slot)

instance (r : Rule) : DecidablePred r.Fires :=
  fun _ ↦ inferInstanceAs (Decidable (r.condition _))

variable {a b : Rule} {p : Prefix}

theorem apply_of_not_fires (h : ¬ a.Fires p) : a.apply p = p := by
  rw [apply, ImpoverishmentRule.apply, ite_eq_right (show ¬ a.condition _ from h),
    Prefix.focus_around, Prefix.set_get]

theorem get_apply_of_ne (r : Rule) (p : Prefix) {s : Slot} (h : s ≠ r.slot) :
    (r.apply p).get s = p.get s :=
  p.get_set_of_ne _ h

theorem get_apply_sublist (r : Rule) (p : Prefix) (s : Slot) :
    ((r.apply p).get s).Sublist (p.get s) := by
  by_cases h : s = r.slot
  · subst h
    rw [apply, Prefix.get_set_self, ImpoverishmentRule.apply]
    split
    · exact (Change.apply_sublist _ _).trans (by rw [Prefix.focus_around])
    · rw [Prefix.focus_around]
  · rw [r.get_apply_of_ne p h]

theorem paradigmatic_isParadigmatic (s : Slot) (check : Arg → Prop) [DecidablePred check]
    (c : Change) : (paradigmatic s check c).Paradigmatic :=
  ImpoverishmentRule.paradigmatic_ofFocus check c

theorem fires_apply_iff_of_paradigmatic (hb : b.Paradigmatic) (h : b.slot ≠ a.slot)
    (p : Prefix) : b.Fires (a.apply p) ↔ b.Fires p :=
  hb.condition_iff <| by rw [Prefix.focus_around, Prefix.focus_around, a.get_apply_of_ne p h]

/-- A rule that a rule of another slot bleeds is syntagmatic. -/
theorem syntagmatic_of_bleeds (h : b.slot ≠ a.slot) (hab : Bleeds a.apply b.Fires p) :
    b.Syntagmatic :=
  fun hb ↦ (bleeds_iff.1 hab).2
    ((fires_apply_iff_of_paradigmatic hb h p).2 (bleeds_iff.1 hab).1)

theorem syntagmatic_of_feeds (h : b.slot ≠ a.slot) (hab : Feeds a.apply b.Fires p) :
    b.Syntagmatic :=
  fun hb ↦ (feeds_iff.1 hab).1
    ((fires_apply_iff_of_paradigmatic hb h p).1 (feeds_iff.1 hab).2)

end Rule

/-- Apply a sequence of rules in order. -/
def run (rs : List Rule) (p : Prefix) : Prefix := rs.foldl (fun p r ↦ r.apply p) p

@[simp] theorem run_nil (p : Prefix) : run [] p = p := rfl

@[simp] theorem run_cons (r : Rule) (rs : List Rule) (p : Prefix) :
    run (r :: rs) p = run rs (r.apply p) := rfl

theorem run_append (rs₁ rs₂ : List Rule) (p : Prefix) :
    run (rs₁ ++ rs₂) p = run rs₂ (run rs₁ p) :=
  List.foldl_append

-- In the bleeding order the bled rule applies vacuously.
theorem run_pair_of_bleeds {a b : Rule} {p : Prefix} (h : Bleeds a.apply b.Fires p) :
    run [a, b] p = a.apply p :=
  h.isFixedPt fun _ ↦ Rule.apply_of_not_fires

/-! ### The block architecture

Arregi and Nevins's (72), `Exponence Conversion > Paradigmatic > Syntagmatic`: the
paradigmatic rules form a block before the syntagmatic ones. -/

/-- A sequence of rules over the prefix is paradigmatic-first when it is as a sequence of rules
at neighborhoods. -/
abbrev ParadigmaticFirst (rs : List Rule) : Prop :=
  ImpoverishmentRule.ParadigmaticFirst (rs.map (·.toImpoverishmentRule))

/-- A sequence of rules over the prefix is syntagmatic-first when it is as a sequence of rules
at neighborhoods. -/
abbrev SyntagmaticFirst (rs : List Rule) : Prop :=
  ImpoverishmentRule.SyntagmaticFirst (rs.map (·.toImpoverishmentRule))

theorem ParadigmaticFirst.eq_of_perm {p s : Rule} (hp : p.Paradigmatic) (hs : s.Syntagmatic)
    {l : List Rule} (hl : ParadigmaticFirst l) (hperm : l.Perm [p, s]) : l = [p, s] := by
  rcases List.perm_pair.mp hperm with rfl | rfl
  · rfl
  · exact absurd hl
      (ImpoverishmentRule.not_paradigmaticFirst_of_sublist hs hp (List.Sublist.refl _))

theorem run_eq_of_paradigmaticFirst {p s : Rule} (hp : p.Paradigmatic) (hs : s.Syntagmatic)
    {l : List Rule} (hl : ParadigmaticFirst l) (hperm : l.Perm [p, s]) (q : Prefix) :
    run l q = run [p, s] q := by
  rw [hl.eq_of_perm hp hs hperm]

/-! ### The Taos rules

The appendix's rules of impoverishment, by its numbering; the paper's numbers are in the
docstrings. -/

/-- The appendix's rules of impoverishment, by its numbering. -/
inductive RuleName where
  /-- By rule (1), the goal loses its number after an inverse agent, with an object. -/
  | r1
  /-- By rule (4), a first person agent loses its number before a second person goal. -/
  | r4
  /-- By the optional rule (5), a second person agent loses its number before a first dual or
  inverse goal with no object; the prefix is then the portmanteau *ku*. -/
  | r5
  /-- By rule (9), a first singular possessive goal loses `[+participant]`. -/
  | r9
  /-- By rule (12), a first person agent loses `[+participant]` before a second dual or inverse
  goal. -/
  | r12
  /-- By rule (24), the paper's (27), a `[−author]` goal loses `[−participant]` after a dual
  agent. -/
  | r24
  /-- By rule (33), the paper's (41), a `[−author]` goal loses its singular features between a
  dual agent and a third singular object. -/
  | r33
  /-- By rule (34a), the paper's (32a), a singular object loses its person after an agent. -/
  | r34a
  /-- By rule (34b), the paper's (32b), an inverse `[−author]` object loses `[−participant]` after
  an agent. -/
  | r34b
  /-- By rule (14), a first dual or inverse agent loses its person before no object, or a
  singular, dummy or inverse one. -/
  | r14
  /-- By rule (35), a singular object loses its person after a first inverse possessive goal. -/
  | r35
  /-- By rule (46), the paper's (37), a first or second singular agent loses `[+minimal]` before a
  singular or dummy object. -/
  | r46
  /-- By rule (2), the agent loses its number before a third dual or inverse goal, with an object;
  "3" is read as `[−author]`, since (24) may already have removed the goal's `[−participant]`. -/
  | r2
  /-- By rule (7), on the agent, a second person agent with number and a first person goal both
  lose their number; the optional (5) bleeds it, leaving the goal's number for *ku*. -/
  | r7a
  /-- (7), on the goal, before the agent's half so that the agent's number is still there to
  condition it. -/
  | r7b
  /-- By rule (32), the paper's (40), a singular object loses its person after a singular goal. It
  runs after (7), not in the appendix's first set, or 2:1s:3s *môm* comes out *mǫ́*. -/
  | r32
  /-- By rule (15), a first person agent loses its person before a second singular goal. -/
  | r15
  /-- By the paradigmatic rule (26), the paper's (43), a first person `[+minimal]` goal loses
  `[+atomic]`. -/
  | r26
  /-- By rule (45a), the paper's (36b), the object loses its singular features after a `[+atomic]`
  agent. -/
  | r45a
  /-- By rule (45b), the paper's (36a), the dummy object is obliterated after a `[+atomic]` agent.
  -/
  | r45b
  /-- By the paradigmatic rule (40), the paper's (35), a third singular agent is obliterated. -/
  | r40
  /-- By rule (47), an inverse object loses `[−author]` after a singular agent. -/
  | r47
  /-- By rule (3), a first person agent loses `[+participant]` before a third person goal and an
  object when the leftmost number is dual or inverse; "3" is read as `[−author]`, as in (2). -/
  | r3
  /-- By the paradigmatic rule (11a), the paper's (39), a second singular agent loses
  `[+participant]`. -/
  | r11a
  /-- By rule (11b), a second singular possessive goal loses `[−author]`. -/
  | r11b
  /-- By rule (29), the paper's (44), at slot `s`, the leftmost number bundle, when singular,
  loses `[+minimal]` before a third inverse object. -/
  | r29 (s : Slot)
  /-- By rule (43), a first singular agent loses `[+participant]` before no object or a
  `[−atomic]` one. -/
  | r43
  /-- By rule (44), a first singular agent loses `[+minimal]` before no object or a plural one. It
  runs after (43), not in the first set, or 1s:∅ comes out *ti*, and the printed intransitive
  context `[[A +author +atomic __]]` is widened to a plural object, or 1s:3p comes out *pi*. -/
  | r44
  /-- By rule (38b), the reflexive object is obliterated after a singular agent. -/
  | r38b
  /-- By rule (42), a second singular intransitive agent loses `[−author]`. -/
  | r42
  /-- By rule (38a), a third plural object is obliterated after a singular agent. -/
  | r38a
  /-- By rule (48a), an inverse object loses its number after a first singular agent. -/
  | r48a
  /-- By rule (48b), a second singular agent loses its singular features before an inverse object.
  -/
  | r48b
  deriving DecidableEq, Repr

namespace RuleName

/-- The rule a name stands for. -/
def rule : RuleName → Rule
  | r1 =>
    .syntagmatic .goal (fun p ↦ p.agent.IsInverse ∧ p.goal.IsThird ∧ p.object ≠ []) .deleteNumber
  | r4 =>
    .syntagmatic .agent (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond) .deleteNumber
  | r5 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.IsSecond ∧ p.goal.IsFirst ∧ p.goal.Has (.atomic false) ∧
        p.goal.Has (.minimal true) ∧ p.object = [])
      .deleteNumber
  | r9 =>
    .syntagmatic .goal
      (fun p ↦ p.agent = [] ∧ p.goal.Has (.author true) ∧ p.goal.Has (.atomic true))
      (.delete [.participant true])
  | r12 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond ∧ p.goal.Has (.atomic false) ∧
        p.goal.Has (.minimal true))
      (.delete [.participant true])
  | r24 =>
    .syntagmatic .goal (fun p ↦ p.agent.IsDual ∧ p.goal.Has (.author false))
      (.delete [.participant false])
  | r33 =>
    .syntagmatic .goal
      (fun p ↦ p.agent.IsDual ∧ p.goal.Has (.author false) ∧ p.object.IsThird ∧ p.object.IsSingular)
      (.delete singular)
  | r34a =>
    .syntagmatic .object (fun p ↦ p.goal = [] ∧ p.agent ≠ [] ∧ p.object.IsSingular)
      .deletePerson
  | r34b =>
    .syntagmatic .object
      (fun p ↦ p.goal = [] ∧ p.agent ≠ [] ∧ p.object.Has (.author false) ∧
        p.object.IsInverse)
      (.delete [.participant false])
  | r14 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.agent.Has (.atomic false) ∧
        p.agent.Has (.minimal true) ∧ p.goal = [] ∧
        (p.object = [] ∨ p.object.IsSingular ∨ p.object = [.dummy] ∨ p.object.IsInverse))
      .deletePerson
  | r35 =>
    .syntagmatic .object
      (fun p ↦ p.agent = [] ∧ p.goal.IsFirst ∧ p.goal.IsInverse ∧ p.object.IsSingular)
      .deletePerson
  | r46 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.participant true) ∧ p.agent.Has (.atomic true) ∧
        p.goal = [] ∧ (p.object.IsSingular ∨ p.object = [.dummy]))
      (.delete [.minimal true])
  | r2 =>
    .syntagmatic .agent
      (fun p ↦ p.goal.Has (.author false) ∧ p.goal.Has (.atomic false) ∧
        p.goal.Has (.minimal true) ∧ p.object ≠ [])
      .deleteNumber
  | r7a =>
    .syntagmatic .agent (fun p ↦ p.agent.IsSecond ∧ p.agent.number ≠ [] ∧ p.goal.IsFirst)
      .deleteNumber
  | r7b =>
    .syntagmatic .goal (fun p ↦ p.agent.IsSecond ∧ p.agent.number ≠ [] ∧ p.goal.IsFirst)
      .deleteNumber
  | r32 =>
    .syntagmatic .object (fun p ↦ p.goal.IsSingular ∧ p.object.IsSingular) .deletePerson
  | r15 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond ∧ p.goal.Has (.atomic true))
      .deletePerson
  | r26 =>
    .paradigmatic .goal (fun a ↦ a.Has (.author true) ∧ a.Has (.minimal true))
      (.delete [.atomic true])
  | r45a =>
    .syntagmatic .object
      (fun p ↦ p.agent.Has (.atomic true) ∧ p.goal = [] ∧ p.object ≠ [])
      (.delete singular)
  | r45b =>
    .syntagmatic .object
      (fun p ↦ p.agent.Has (.atomic true) ∧ p.goal = [] ∧ p.object = [.dummy]) .obliterate
  | r40 =>
    .paradigmatic .agent (fun a ↦ a.IsThird ∧ a.IsSingular) .obliterate
  | r47 =>
    .syntagmatic .object (fun p ↦ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
      (.delete [.author false])
  | r3 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.goal.Has (.author false) ∧ p.object ≠ [] ∧
        p.leftmostNumberArg.Has (.atomic false) ∧ p.leftmostNumberArg.Has (.minimal true))
      (.delete [.participant true])
  | r11a =>
    .paradigmatic .agent (fun a ↦ a.Has (.author false) ∧ a.Has (.atomic true))
      (.delete [.participant true])
  | r11b =>
    .syntagmatic .goal
      (fun p ↦ p.agent = [] ∧ p.goal.Has (.participant true) ∧ p.goal.Has (.atomic true))
      (.delete [.author false])
  | r29 s =>
    .syntagmatic s
      (fun p ↦ p.leftmostNumber = some s ∧ (p.get s).IsSingular ∧ p.object.IsThird ∧
        p.object.IsInverse)
      (.delete [.minimal true])
  | r43 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.agent.IsSingular ∧ p.goal = [] ∧
        (p.object = [] ∨ p.object.Has (.atomic false)))
      (.delete [.participant true])
  | r44 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author true) ∧ p.agent.Has (.atomic true) ∧ p.goal = [] ∧
        (p.object = [] ∨ p.object.IsPlural))
      (.delete [.minimal true])
  | r38b =>
    .syntagmatic .object (fun p ↦ p.agent.IsSingular ∧ p.goal = [] ∧ p.object = [.refl]) .obliterate
  | r42 =>
    .syntagmatic .agent
      (fun p ↦ p.agent.IsSingular ∧ p.agent.Has (.author false) ∧ p.goal = [] ∧
        p.object = [])
      (.delete [.author false])
  | r38a =>
    .syntagmatic .object
      (fun p ↦ p.agent.IsAtomicSingular ∧ p.goal = [] ∧ p.object.IsThird ∧ p.object.IsPlural)
      .obliterate
  | r48a =>
    .syntagmatic .object
      (fun p ↦ p.agent.Has (.author true) ∧ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
      .deleteNumber
  | r48b =>
    .syntagmatic .agent
      (fun p ↦ p.agent.Has (.author false) ∧ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
      (.delete singular)

/-- The rules with (40) and (26) as the appendix prints them: (40), `[[A __](O)]`, applies with no
goal, and (26), `[[G 1 __ +minimal]`, with no agent. -/
def printed : RuleName → Rule
  | r40 =>
    .syntagmatic .agent (fun p ↦ p.agent.IsThird ∧ p.agent.IsSingular ∧ p.goal = []) .obliterate
  | r26 =>
    .syntagmatic .goal
      (fun p ↦ p.agent = [] ∧ p.goal.Has (.author true) ∧ p.goal.Has (.minimal true))
      (.delete [.atomic true])
  | n => n.rule

/-- The appendix's seven sets of rules of impoverishment, in order. -/
def order : List RuleName :=
  [r1, r4, r5, r9, r12, r24, r33, r34a, r34b, r14, r35, r46,
   r2, r7b, r7a, r32, r15, r26, r45a, r45b, r40, r47,
   r3, r11a, r11b, r29 .agent, r29 .goal, r43, r44,
   r38b, r42, r38a, r48a, r48b]

end RuleName

open RuleName

/-- The appendix's rules in order, with its optional (5) included or not. -/
def impoverishment (optional : Bool) : List Rule :=
  (if optional then order else order.erase r5).map rule

/-- The same sets with (40) and (26) as printed. -/
def impoverishmentPrinted (optional : Bool) : List Rule :=
  (if optional then order else order.erase r5).map printed

theorem r40_paradigmatic : r40.rule.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

theorem r11a_paradigmatic : r11a.rule.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

theorem r26_paradigmatic : r26.rule.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

/-- The 3S:3S transitive cell, whose prefix is ∅ (Table 15). -/
def cell3S3S : Taos.Cell := ⟨some (.third, .singular), none, some (.third .singular)⟩

/-- The 3S:3I transitive cell, whose prefix is *í* (Table 15). -/
def cell3S3I : Taos.Cell := ⟨some (.third, .singular), none, some (.third .inverse)⟩

/-- The 3S:no transitive cell, whose prefix is ∅ (Table 16). -/
def cell3Sno : Taos.Cell := ⟨some (.third, .singular), none, some .dummy⟩

/-- The 2S:3S transitive cell, whose prefix is *o* (Table 17). -/
def cell2S3S : Taos.Cell := ⟨some (.second, .singular), none, some (.third .singular)⟩

/-- The 2S intransitive cell, whose prefix is *ǫ* (Table 17). -/
def cell2S : Taos.Cell := ⟨some (.second, .singular), none, none⟩

/-- The 1S:3S possessive cell, whose prefix is *ôn* (Table 22). -/
def cell1S3S : Taos.Cell := ⟨none, some (.first, .singular), some (.third .singular)⟩

/-- The 1S:3I possessive cell, whose prefix is *ónôm* (Table 22). -/
def cell1S3I : Taos.Cell := ⟨none, some (.first, .singular), some (.third .inverse)⟩

/-- The 1D:3S:3S ditransitive cell, whose prefix is *opénôm* (Table 21). -/
def cell1D3S3S : Taos.Cell :=
  ⟨some (.first, .dual), some (.third, .singular), some (.third .singular)⟩

/-- The 1D:3S:no ditransitive cell, whose prefix is *opén*, the paper's (25). -/
def cell1D3Sno : Taos.Cell := ⟨some (.first, .dual), some (.third, .singular), some .dummy⟩

theorem r45a_syntagmatic : r45a.rule.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell3S3S).around .object)
    (n₂ := (⟨[], [], third ++ singular⟩ : Prefix).around .object) rfl (by decide) (by decide)

theorem r46_syntagmatic : r46.rule.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell2S3S).around .agent)
    (n₂ := (spellOut cell2S).around .agent) rfl (by decide) (by decide)

theorem r40_printed_syntagmatic : r40.printed.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell3S3S).around .agent)
    (n₂ := (⟨third ++ singular, third ++ singular, third ++ singular⟩ : Prefix).around .agent)
    rfl (by decide) (by decide)

theorem r26_printed_syntagmatic : r26.printed.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell1S3S).around .goal)
    (n₂ := (⟨third ++ singular, first ++ singular, third ++ singular⟩ : Prefix).around .goal)
    rfl (by decide) (by decide)

theorem r33_syntagmatic : r33.rule.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell1D3S3S).around .goal)
    (n₂ := (⟨[], third ++ singular, third ++ singular⟩ : Prefix).around .goal)
    rfl (by decide) (by decide)

theorem r29_goal_syntagmatic : (r29 .goal).rule.Syntagmatic :=
  ImpoverishmentRule.syntagmatic_of_focus_eq (n₁ := (spellOut cell1S3I).around .goal)
    (n₂ := (⟨[], first ++ singular, []⟩ : Prefix).around .goal) rfl (by decide) (by decide)

/-! ### Case 1 (§4.2.1): object impoverishment precedes agent impoverishment

The 3S:3S prefix is ∅ (Table 15), so no *m*, the exponent of a third person object (31), is
inserted: the object's third person must be gone at Vocabulary Insertion, which (34a) does only
while the agent is still there for its context. The theorems are about the feature bundles the
two orders leave; that the block order conflicts with Arregi and Nevins rests on the paper's
labelling of (40) as paradigmatic (see the implementation notes). -/

theorem form_3S3S :
    Taos.form cell3S3S = some "" := by
  decide

theorem case1_syn_para :
    run [r34a.rule, r40.rule] (spellOut cell3S3S) = ⟨[], [], singular⟩ := by
  decide

/-- (35) removes the agent that (32a) needs, so applying it first bleeds (32a). -/
theorem r40_bleeds_r34a : Bleeds r40.rule.apply r34a.rule.Fires (spellOut cell3S3S) := by decide

theorem r34a_syntagmatic : r34a.rule.Syntagmatic :=
  Rule.syntagmatic_of_bleeds (by decide) r40_bleeds_r34a

theorem case1_para_syn :
    run [r40.rule, r34a.rule] (spellOut cell3S3S) = ⟨[], [], third ++ singular⟩ := by
  rw [run_pair_of_bleeds r40_bleeds_r34a]; decide

-- (31)
theorem case1_block (l : List Rule) (hl : ParadigmaticFirst l)
    (hperm : l.Perm [r40.rule, r34a.rule]) :
    (run l (spellOut cell3S3S)).object = third ++ singular := by
  rw [run_eq_of_paradigmaticFirst r40_paradigmatic r34a_syntagmatic hl hperm, case1_para_syn]

-- (34b)
theorem case1_inverse :
    run [r34b.rule, r40.rule] (spellOut cell3S3I) = ⟨[], [], [.author false, .inverse]⟩ ∧
      run [r40.rule, r34b.rule] (spellOut cell3S3I) = ⟨[], [], third ++ inverse⟩ := by
  decide

/-! ### Case 2 (§4.2.2): dummy object impoverishment precedes agent impoverishment

The 3S:no and 3S:3S prefixes are ∅ and toneless (Table 16), so the paper has the object
obliterated and its singular features deleted by (45), which need the singular agent that (40)
removes. The 3S:3S half reaches the surface (the block order leaves a singular object, which
would be exponed); the dummy half is featural only, since a one-argument prefix with a
featureless dummy object is ∅ and toneless under either order. -/

theorem form_3Sno : Taos.form cell3Sno = some "" := by
  decide

theorem case2_dummy_syn_para :
    run [r45b.rule, r40.rule] (spellOut cell3Sno) = ⟨[], [], []⟩ := by
  decide

-- (35), (36a)
theorem r40_bleeds_r45b : Bleeds r40.rule.apply r45b.rule.Fires (spellOut cell3Sno) := by decide

theorem r45b_syntagmatic : r45b.rule.Syntagmatic :=
  Rule.syntagmatic_of_bleeds (by decide) r40_bleeds_r45b

theorem case2_dummy_para_syn :
    run [r40.rule, r45b.rule] (spellOut cell3Sno) = ⟨[], [], [.dummy]⟩ := by
  rw [run_pair_of_bleeds r40_bleeds_r45b]; decide

theorem case2_singular_syn_para :
    run [r34a.rule, r45a.rule, r40.rule] (spellOut cell3S3S) = ⟨[], [], []⟩ := by
  decide

theorem case2_singular_para_syn :
    run [r40.rule, r34a.rule, r45a.rule] (spellOut cell3S3S) = ⟨[], [], third ++ singular⟩ := by
  decide

theorem case2_block (l : List Rule) (hl : ParadigmaticFirst l)
    (hperm : l.Perm [r40.rule, r45b.rule]) :
    (run l (spellOut cell3Sno)).object = [.dummy] := by
  rw [run_eq_of_paradigmaticFirst r40_paradigmatic r45b_syntagmatic hl hperm, case2_dummy_para_syn]

/-! ### Case 3 (§4.2.3): `[+minimal]` impoverishment precedes `[+participant]` impoverishment

The 2S:3S transitive prefix *o* differs from the 2S intransitive *ǫ* (Table 17), so the two
agents differ at Vocabulary Insertion. (46) makes them differ by deleting `[+minimal]` from the
transitive agent, and needs the `[+participant]` that (11a) deletes. -/

theorem form_2S3S_ne_form_2S :
    Taos.form cell2S3S ≠
      Taos.form cell2S := by
  decide

theorem case3_syn_para :
    (run [r46.rule, r11a.rule] (spellOut cell2S3S)).agent = [.author false, .atomic true] := by
  decide

-- (39), (37)
theorem r11a_bleeds_r46 : Bleeds r11a.rule.apply r46.rule.Fires (spellOut cell2S3S) := by decide

theorem case3_para_syn :
    (run [r11a.rule, r46.rule] (spellOut cell2S3S)).agent =
      (run [r11a.rule] (spellOut cell2S)).agent := by
  rw [run_pair_of_bleeds r11a_bleeds_r46]; decide

theorem case3_block (l : List Rule) (hl : ParadigmaticFirst l)
    (hperm : l.Perm [r11a.rule, r46.rule]) :
    (run l (spellOut cell2S3S)).agent = (run [r11a.rule] (spellOut cell2S)).agent := by
  rw [run_eq_of_paradigmaticFirst r11a_paradigmatic r46_syntagmatic hl hperm, case3_para_syn]

/-! ### Case 4 (§4.2.4): third singular object impoverishment precedes possessive impoverishment

The 1S:3S possessive prefix is *ôn* (Table 22), with no *m*: the object's third person is
deleted by (32), which needs the singular goal that (26) makes non-singular. -/

theorem form_1S3S :
    Taos.form cell1S3S = some "ôn" ∧
      'm' ∉ "ôn".toList := by
  decide

-- (43), (40)
theorem r26_bleeds_r32 : Bleeds r26.rule.apply r32.rule.Fires (spellOut cell1S3S) := by decide

theorem r32_syntagmatic : r32.rule.Syntagmatic :=
  Rule.syntagmatic_of_bleeds (by decide) r26_bleeds_r32

theorem case4_syn_para :
    run [r32.rule, r26.rule] (spellOut cell1S3S) = ⟨[], first ++ [.minimal true], singular⟩ := by
  decide

theorem case4_para_syn :
    run [r26.rule, r32.rule] (spellOut cell1S3S) =
      ⟨[], first ++ [.minimal true], third ++ singular⟩ := by
  rw [run_pair_of_bleeds r26_bleeds_r32]; decide

-- (31)
theorem case4_block (l : List Rule) (hl : ParadigmaticFirst l)
    (hperm : l.Perm [r26.rule, r32.rule]) :
    (run l (spellOut cell1S3S)).object = third ++ singular := by
  rw [run_eq_of_paradigmaticFirst r26_paradigmatic r32_syntagmatic hl hperm, case4_para_syn]

-- (33), (32), Table 21
theorem r33_bleeds_r32 : Bleeds r33.rule.apply r32.rule.Fires (spellOut cell1D3S3S) := by decide

theorem case4_r33_r32 :
    (run [r33.rule, r32.rule] (spellOut cell1D3S3S)).object = third ++ singular ∧
      (run [r32.rule, r33.rule] (spellOut cell1D3S3S)).object = singular := by
  rw [run_pair_of_bleeds r33_bleeds_r32]; decide

theorem form_1D3S3S :
    Taos.form cell1D3S3S =
        some "opénôm" ∧
      'm' ∈ "opénôm".toList := by
  decide

/-! ### Case 5 (§4.2.5): a paradigmatic rule before a syntagmatic one

The 1S:3I possessive prefix *ónôm* keeps *n*, the exponent of `[+minimal]` (20): (26) deletes
the goal's `[+atomic]` first and bleeds (29), which would delete the `[+minimal]`. -/

theorem form_1S3I :
    Taos.form cell1S3I = some "ónôm" ∧
      'n' ∈ "ónôm".toList := by
  decide

-- (43), (44)
theorem r26_bleeds_r29 :
    Bleeds r26.rule.apply (r29 .goal).rule.Fires (spellOut cell1S3I) := by
  decide

theorem case5_para_syn :
    (run [r26.rule, (r29 .goal).rule] (spellOut cell1S3I)).goal = first ++ [.minimal true] := by
  rw [run_pair_of_bleeds r26_bleeds_r29]; decide

theorem case5_syn_para :
    (run [(r29 .goal).rule, r26.rule] (spellOut cell1S3I)).goal = first ++ [.atomic true] := by
  decide

/-! ### The two kinds interleave (§4.2, §5) -/

/-- An order with (32a) before (35) and (43) before (44) respects neither block architecture, so
paradigmatic and syntagmatic impoverishment interleave. -/
theorem must_interleave {l : List Rule} (h₁ : [r34a.rule, r40.rule].Sublist l)
    (h₅ : [r26.rule, (r29 .goal).rule].Sublist l) :
    ¬ ParadigmaticFirst l ∧ ¬ SyntagmaticFirst l :=
  ⟨ImpoverishmentRule.not_paradigmaticFirst_of_sublist r34a_syntagmatic r40_paradigmatic
      (h₁.map _),
    ImpoverishmentRule.not_syntagmaticFirst_of_sublist r26_paradigmatic r29_goal_syntagmatic
      (h₅.map _)⟩

/-- The rules the paper labels paradigmatic: its (35), (39) and (43). -/
def labelledParadigmatic : List RuleName := [r40, r11a, r26]

/-- The rules the paper labels syntagmatic: its (32), (36), (37), (40), (41) and (44). -/
def labelledSyntagmatic : List RuleName := [r34a, r34b, r45b, r45a, r46, r32, r33, r29 .goal]

theorem r34b_syntagmatic : r34b.rule.Syntagmatic :=
  Rule.syntagmatic_of_bleeds (a := r40.rule) (p := spellOut cell3S3I) (by decide) (by decide)

theorem paradigmatic_of_labelled : ∀ n ∈ labelledParadigmatic, n.rule.Paradigmatic := by
  simpa [labelledParadigmatic] using ⟨r40_paradigmatic, r11a_paradigmatic, r26_paradigmatic⟩

theorem syntagmatic_of_labelled : ∀ n ∈ labelledSyntagmatic, n.rule.Syntagmatic := by
  simpa [labelledSyntagmatic] using ⟨r34a_syntagmatic, r34b_syntagmatic, r45b_syntagmatic,
    r45a_syntagmatic, r46_syntagmatic, r32_syntagmatic, r33_syntagmatic, r29_goal_syntagmatic⟩

/-! ### Linearization, metathesis and exponence

After Linearization the prefix is a string of feature terminals, each tagged with its slot,
in the order of (4) and (5); the appendix's rules of metathesis swap adjacent terminals, by
Generalized Reduplication with one terminal on either side of the angled brackets, (18) and (22)
on the goal as their subscript says and (23) on
the second argument, goal or object. Exponence then reads each terminal in its prefix. -/

/-- A terminal of the linearized prefix is a slot with a feature. -/
abbrev Terminal := Slot × Feat

/-- The linearized prefix. -/
def linearize (p : Prefix) : List Terminal :=
  [Slot.agent, .goal, .object].flatMap fun s ↦
    ((List.range 6).flatMap fun k ↦ (p.get s).filter (Feat.rank · == k)).map ((s, ·))

/-- By rule (18), the goal's `[−author]` swaps with its following inverse feature, when an agent is
present. -/
def m18 (p : Prefix) (n : Neighborhood Terminal) : Option Reduplication :=
  if p.agent ≠ [] ∧ n.focus = (.goal, .author false) ∧
    n.rightCtx.head? = some (.goal, .inverse) then some (.metathesis 1 1) else none

/-- By rule (23), the paper's (26), a `[−atomic]` agent's `[+minimal]` swaps with the second
argument's following `[−author]`. -/
def m23 (p : Prefix) (n : Neighborhood Terminal) : Option Reduplication :=
  if p.agent.Has (.atomic false) ∧ n.focus = (.agent, .minimal true) ∧
    n.rightCtx.head? = some (p.secondArg, .author false) then some (.metathesis 1 1) else none

/-- By rule (22), the paper's (24), the goal's `[−author]` swaps with its following `[−atomic]`
before `[+minimal]`, when an agent is present. -/
def m22 (p : Prefix) (n : Neighborhood Terminal) : Option Reduplication :=
  if p.agent ≠ [] ∧ n.focus = (.goal, .author false) ∧
    n.rightCtx.take 2 = [(.goal, .atomic false), (.goal, .minimal true)]
  then some (.metathesis 1 1) else none

/-- The appendix's two sets of rules of metathesis in order. -/
def metathesis (p : Prefix) : List Terminal → List Terminal :=
  reduplicateFirst (m22 p) ∘ reduplicateFirst (m23 p) ∘ reduplicateFirst (m18 p)

/-- The phonological role of an exponent, for the epenthetic vowel. -/
inductive Role where
  | onset
  | coda
  | full
  deriving DecidableEq

/-- An exponent and its role. -/
abbrev Morph := String × Role

/-! ### Rules of exponence

A rule of exponence realizes one of its target features, the first its bundle bears, and discharges
the others, as `S ⇔ ǫ` leaves a singular's `[+minimal]` unexponed. Its brackets are conditions on
the arguments around the target's slot, each read in the adjacent window of one tier: the leftmost
brackets `[[π` and `[[ω` on the tiers of `[±participant]` and of number, the others on the tier of
the present arguments. A rule with brackets on several tiers refers to several nodes, as the
hyper-contextual rules of [moskal-smith-2016] do. -/

/-- The arguments of a prefix around slot `s`, each with its slot, absent ones empty, in the order
of (1). -/
def Prefix.slotsAround (p : Prefix) : Slot → Neighborhood (Slot × Arg)
  | .agent => ⟨(.agent, p.agent), [], [(.goal, p.goal), (.object, p.object)]⟩
  | .goal => ⟨(.goal, p.goal), [(.agent, p.agent)], [(.object, p.object)]⟩
  | .object => ⟨(.object, p.object), [(.goal, p.goal), (.agent, p.agent)], []⟩

/-- The tiers on which brackets are read. -/
inductive Tier where
  /-- The present arguments: those impoverishment has left a feature, an argument whose features
  are all deleted dropping out. -/
  | present
  /-- The arguments with a `[±participant]` feature, the person bundles that count as leftmost. -/
  | participant
  /-- The arguments with number features. -/
  | number
  deriving DecidableEq, Repr

/-- The arguments a tier keeps. -/
def Tier.Keeps : Tier → Slot × Arg → Prop
  | .present, x => x.2 ≠ []
  | .participant, x => x.2.HasParticipant
  | .number, x => x.2.number ≠ []

instance (t : Tier) : DecidablePred t.Keeps := fun x ↦ by
  cases t <;> unfold Tier.Keeps <;> infer_instance

/-- A bracket of a rule of exponence. -/
inductive Bracket where
  /-- The target's own argument and slot satisfy `P`. -/
  | own (P : Slot × Arg → Prop) [dec : DecidablePred P]
  /-- The target's argument is the leftmost of the tier, `[[π __` or `[[ω __`. -/
  | leftmost (t : Tier)
  /-- The tier's argument before the target's satisfies `P`, as in `[πA …][π __]`. -/
  | after (t : Tier) (P : Slot × Arg → Prop) [dec : DecidablePred P]
  /-- The tier's leftmost argument satisfies `P`, as in `[[ω I`: the one before the target's, else
  the target's, else the one after. -/
  | leftmostIs (t : Tier) (P : Slot × Arg → Prop) [dec : DecidablePred P]

namespace Bracket

/-- The tier a bracket is read on. -/
def tier : Bracket → Tier
  | own _ => .present
  | leftmost t | after t _ | leftmostIs t _ => t

/-- What a bracket says of a window. -/
def HoldsAt : Bracket → Neighborhood (Slot × Arg) → Prop
  | own P, n => P n.focus
  | leftmost t, n => t.Keeps n.focus ∧ n.leftCtx = []
  | after _ P, n => ∃ x ∈ n.leftCtx.head?, P x
  | leftmostIs t P, n => (∃ x ∈ n.leftCtx.head?, P x) ∨ n.leftCtx = [] ∧
    (t.Keeps n.focus ∧ P n.focus ∨ ¬ t.Keeps n.focus ∧ ∃ x ∈ n.rightCtx.head?, P x)

instance (c : Bracket) (n : Neighborhood (Slot × Arg)) : Decidable (c.HoldsAt n) := by
  cases c <;> unfold HoldsAt <;> infer_instance

end Bracket

/-- A reading of the brackets assigns each the window it is read in. -/
abbrev Reading := Bracket → Neighborhood (Slot × Arg) → Neighborhood (Slot × Arg)

/-- Each bracket is read in the adjacent window of the tier `f` assigns its own: with `f = id` on
its tier, with a tier sent to `.present` on the present arguments, null terminals pruned but that
tier not projected. -/
def onTiersVia (f : Tier → Tier) : Reading := fun c n ↦ (n.project (f c.tier).Keeps).window 1

/-- Each bracket is read in the adjacent window of its tier. -/
abbrev onTiers : Reading := onTiersVia id

/-- A rule of exponence. -/
structure ExponenceRule where
  /-- The features it realizes. -/
  targets : Arg
  /-- Its brackets. -/
  brackets : List Bracket
  /-- Its exponent, empty for a null exponent. -/
  exponent : List Morph

namespace ExponenceRule

/-- The bundle bears the features `fs`. -/
def bears (fs : Arg) : Bracket := .own fun x ↦ ∀ f ∈ fs, f ∈ x.2

/-- The target's slot is `s`. -/
def inSlot (s : Slot) : Bracket := .own (·.1 = s)

/-- The prefix is the dual agent and the target, `[[A D][ __ ]]`. -/
def afterDualAgent : Bracket := .after .present fun x ↦ x.1 = .agent ∧ x.2.IsDual

/-- The agent precedes the target's argument, `[πA …][π __]`: present, its features possibly
impoverished, the trace reading of the appendix's discussion after (10). -/
def afterAgent : Bracket := .after .present (·.1 = .agent)

/-- By rule (39b), `3P ⇔ ∅ / [[A D][ __ ]]`. -/
def e39b : ExponenceRule :=
  ⟨third ++ plural, [inSlot .object, .own fun x ↦ x.2.IsThird ∧ x.2.IsPlural, afterDualAgent], []⟩

/-- By rule (36), `3P ⇔ w`. -/
def e36 : ExponenceRule :=
  ⟨third ++ plural, [.own fun x ↦ x.2.IsThird ∧ x.2.IsPlural], [("w", .coda)]⟩

/-- By rule (39d), `refl ⇔ ∅ / [[A D][ __ ]]`. -/
def e39d : ExponenceRule := ⟨[.refl], [afterDualAgent], []⟩

/-- By rule (37), `refl ⇔ mo`. -/
def e37 : ExponenceRule := ⟨[.refl], [], [("mo", .full)]⟩

/-- By rule (31), `3 ⇔ m / [O __ ]`. -/
def e31 : ExponenceRule := ⟨third, [inSlot .object, bears third], [("m", .coda)]⟩

/-- A third person object's number has no exponent, this study's addition. The appendix lists
none, and without it an object that impoverishment leaves the leftmost number would be exponed by
(25), (16) or (30). -/
def objectNumberNull : ExponenceRule :=
  ⟨[.atomic true, .atomic false, .minimal true, .minimal false, .inverse],
    [inSlot .object, bears third], []⟩

/-- By rule (8), `1 ⇔ t / [[π __ +atomic]`. -/
def e8 : ExponenceRule := ⟨first, [.leftmost .participant, bears (first ++ [.atomic true])],
  [("t", .onset)]⟩

/-- By rule (10), `[+participant] ⇔ m / [[±participant __ −author]`. -/
def e10 : ExponenceRule :=
  ⟨[.participant true], [.leftmost .participant, bears [.author false]], [("m", .onset)]⟩

/-- By rule (13), `[+participant] ⇔ k / [[π __ ]`. -/
def e13 : ExponenceRule := ⟨[.participant true], [.leftmost .participant], [("k", .onset)]⟩

/-- By rule (17), `[−author] ⇔ pi / [πA …][π __]` with the leftmost number inverse. -/
def e17 : ExponenceRule :=
  ⟨[.author false], [afterAgent, .leftmostIs .number (·.2.IsInverse)], [("pi", .full)]⟩

/-- By rule (19), `[−author] ⇔ pé / [πA …][π __]` with the leftmost number dual. -/
def e19 : ExponenceRule :=
  ⟨[.author false], [afterAgent, .leftmostIs .number (·.2.IsDual)], [("pé", .full)]⟩

/-- By rule (16a), `I ⇔ o / [[ω __` with the leftmost person second. -/
def e16a : ExponenceRule :=
  ⟨[.inverse], [.leftmost .number, .leftmostIs .participant (·.2.IsSecond)], [("o", .full)]⟩

/-- By rule (16b), `I ⇔ i / [[ω __`. -/
def e16b : ExponenceRule := ⟨[.inverse], [.leftmost .number], [("i", .full)]⟩

/-- By rule (25), `S ⇔ ǫ / [[ω __`. -/
def e25 : ExponenceRule :=
  ⟨singular, [.leftmost .number, .own (·.2.IsSingular)], [("ǫ", .full)]⟩

/-- By rule (20), `[+minimal] ⇔ n / [[ω __`. -/
def e20 : ExponenceRule := ⟨[.minimal true], [.leftmost .number], [("n", .coda)]⟩

/-- By rule (30), `[±atomic] ⇔ o / [[ω __`. -/
def e30 : ExponenceRule := ⟨[.atomic true, .atomic false], [.leftmost .number], [("o", .full)]⟩

/-- The rule applies to a terminal of a prefix when it targets the terminal's feature and, read by
`read`, its brackets hold around the terminal's slot. -/
def Applies (read : Reading) (r : ExponenceRule) (p : Prefix) (t : Terminal) : Prop :=
  t.2 ∈ r.targets ∧ ∀ c ∈ r.brackets, c.HoldsAt (read c (p.slotsAround t.1))

instance (read : Reading) (r : ExponenceRule) (p : Prefix) (t : Terminal) :
    Decidable (r.Applies read p t) := inferInstanceAs (Decidable (_ ∧ ∀ _ ∈ _, _))

end ExponenceRule

open ExponenceRule in
/-- The Vocabulary of the appendix's rules of exponence, a bundle's category before its single
features and the contextual rules before the elsewhere ones. -/
def vocabulary : List ExponenceRule :=
  [e39b, e36, e39d, e37, e31, objectNumberNull, e8, e10, e13, e17, e19, e16a, e16b, e25, e20, e30]

/-- The exponents of a terminal in its prefix come from the first rule of the Vocabulary that
applies, realized at the first of its targets the bundle bears and null at the others. -/
def exponents (p : Prefix) (t : Terminal) (read : Reading := onTiers) : List Morph :=
  match vocabulary.find? (fun r ↦ decide (r.Applies read p t)) with
  | none => []
  | some r =>
    if ((r.targets.filter (· ∈ p.get t.1)).map Feat.rank).min? = some t.2.rank then r.exponent
    else []

/-- The exponents of a linearized prefix, the portmanteaux (6), (41) and (49) and *mây*
first; the flag marks a portmanteau form, which takes no tone rule. Three additions the appendix
uses without stating them: *mây* for the 2:1 prefixes without an object (its §3.4), (41) and (49)
matching an argument's remaining bundle exactly, and portmanteaux taking no tone, without which
(6) *ku* would come out *kú*. -/
def exponence (p : Prefix) (ts : List Terminal) (read : Reading := onTiers) :
    List Morph × Bool :=
  if p.agent = second ∧ p.object = [] then
    if p.goal = first ++ dual ∨ p.goal = first ++ inverse then ([("ku", .full)], true)
    else if p.goal = first then ([("mây", .full)], true)
    else (ts.flatMap (exponents p · read), false)
  else match p.args with
  | [a] =>
    if a = [.participant true, .author true, .atomic true] then ([("ti", .full)], true)
    else if a = [.author true, .atomic true, .minimal true] then ([("pi", .full)], true)
    else if a = [.author false, .atomic true, .minimal true] then ([("ki", .full)], true)
    else (ts.flatMap (exponents p · read), false)
  | _ => (ts.flatMap (exponents p · read), false)

/-! ### Epenthesis and tone -/

/-- The concatenation of a list of strings (`String.join` does not reduce under `decide`). -/
def concat (l : List String) : String := l.foldl (· ++ ·) ""

/-- A vowel of the exponents, before tone is assigned. -/
def isVowel (c : Char) : Bool := "aeiouǫé".toList.contains c

/-- By the epenthesis rule (27), an onset consonant with no vowel after it, or a coda consonant with
none before it, takes the vowel *o*. -/
def epenthesis : Option Char → List Morph → List String
  | _, [] => []
  | prev, (m, r) :: rest =>
    let before := if r == .coda && !(prev.any isVowel) then ["o"] else []
    let next := (rest.head?.map (·.1)).bind fun n ↦ n.toList.head?
    let after := if r == .onset && !(next.any isVowel) then ["o"] else []
    let out := before ++ [m] ++ after
    out ++ epenthesis (concat out).toList.getLast? rest

/-- A tone. -/
inductive Tone where
  | high
  | falling
  deriving DecidableEq

/-- A toned vowel, as the fragment prints it. -/
def mark : Tone → Char → String
  | .high, 'o' => "ó"
  | .high, 'ǫ' => "ǫ́"
  | .high, 'i' => "í"
  | .high, 'e' | .high, 'é' => "é"
  | .high, 'u' => "ú"
  | .high, 'a' => "á"
  | .falling, 'o' => "ô"
  | .falling, 'ǫ' => "ǫ̂"
  | .falling, 'i' => "î"
  | .falling, 'e' | .falling, 'é' => "ê"
  | .falling, 'u' => "û"
  | .falling, 'a' => "â"
  | _, c => c.toString

/-- The syllable nuclei of a string from index `i`, each with whether its syllable is
closed. -/
def syllables : List Char → ℕ → List (ℕ × Bool)
  | [], _ => []
  | c :: rest, i =>
    if !isVowel c then syllables rest (i + 1)
    else match rest with
      | d :: e :: rest' =>
        if !isVowel d && !isVowel e then (i, true) :: syllables (e :: rest') (i + 2)
        else (i, false) :: syllables (d :: e :: rest') (i + 1)
      | [d] => if !isVowel d then [(i, true)] else (i, false) :: syllables [d] (i + 1)
      | [] => [(i, false)]

/-- The appendix's context-specific tone rules (51b)–(51h), read off the cell: a tone for the
final syllable, `some none` for none, `none` where no rule applies. The appendix prints (51f) as
toneless, but its prose and Table 3 make the ∅:3s possessives high, as here; (51h) applies as
printed (see the TODO). -/
def exception (c : Taos.Cell) : Option (Option Tone) :=
  match c.agent, c.goal, c.object with
  | some (_, .dual), none, some .dummy | some (_, .dual), none, some (.third .singular) =>
    some (some .high)
  | some (.first, .dual), none, some (.third .plural)
  | some (.second, .dual), none, some (.third .plural)
  | some (.first, .dual), none, some .reflexive
  | some (.second, .dual), none, some .reflexive => some (some .falling)
  | none, some (.third, .singular), some (.third .singular) => some none
  | some (_, .singular), some (.third, .singular), some (.third .singular) => some none
  | none, some (.third, .singular), some _ => some (some .high)
  | some (_, .singular), some (.third, .singular), some _ => some (some .high)
  | none, some (.third, .dual), some _ => some (some .high)
  | _, _, _ => none

/-- By the tone rules (50) and (51), a one-argument prefix is toneless; otherwise the final
syllable, *mo* aside, is high if open and falling if closed, *pé* is high, and the syllable before
it is high unless it precedes *pi* or *pé*. -/
def tone (c : Taos.Cell) (nargs : ℕ) (morphs : List String) (fixed : Bool) : String :=
  let s := concat morphs
  if fixed then s else
  let hasMo := morphs.getLast? == some "mo" && morphs.length > 1
  let chars := if hasMo then s.toList.rdrop 2 else s.toList
  let syl := syllables chars 0
  match syl.getLast? with
  | none => s
  | some (vf, closed) =>
    let pOnset := chars[vf - 1]? == some 'p'
    let final : Option Tone := match exception c with
      | some t => t
      | none =>
        if nargs ≤ 1 then none
        else if pOnset && chars[vf]? == some 'é' then some .high
        else if closed then some .falling else some .high
    let vp := ((syl.getD (syl.length - 2) (0, false)).1)
    let penult := final.isSome && syl.length ≥ 2 && !pOnset
    let out := concat (chars.mapIdx fun i ch ↦
      if i == vf then (match final with | some t => mark t ch | none => ch.toString)
      else if penult && i == vp then mark .high ch else ch.toString)
    out ++ (if hasMo then "mo" else "")

/-! ### The derivation -/

/-- A prefix expones its present arguments, less an object silenced by the allomorphs (39b,d). -/
def Prefix.exponed (p : Prefix) : ℕ :=
  p.args.length -
    if p.agent.IsDual ∧ p.goal = [] ∧ (p.object = [.refl] ∨ p.object.IsThird ∧ p.object.IsPlural)
    then 1 else 0

/-- The surface form of a cell under a rule system results from Spell-Out, impoverishment,
Linearization, metathesis, exponence, epenthesis and tone. -/
def deriveWith (rules : List Rule) (c : Taos.Cell) (read : Reading := onTiers) : String :=
  let p := run rules (spellOut c)
  let (morphs, fixed) := exponence p (metathesis p (linearize p)) read
  let morphs := if morphs.map (·.1) == ["w"] then [("u", .full)] else morphs
  tone c p.exponed (epenthesis none morphs) fixed

/-- The surface form of a cell under the appendix's seven sets, with or without the optional
(5). -/
def derive (optional : Bool) : Taos.Cell → String := deriveWith (impoverishment optional)

/-- The cells of the paradigm the appendix leaves unaccounted for (see the TODO). -/
def unaccounted : List Taos.Cell :=
  [⟨none, some (.second, .singular), none⟩,
   ⟨some (.first, .singular), some (.second, .singular), none⟩,
   ⟨some (.first, .dual), some (.second, .singular), none⟩,
   ⟨some (.first, .inverse), some (.second, .singular), none⟩,
   ⟨some (.third, .inverse), none, some (.third .plural)⟩,
   ⟨some (.third, .inverse), none, some .reflexive⟩,
   ⟨none, some (.third, .dual), some (.third .singular)⟩,
   ⟨none, some (.third, .dual), some (.third .inverse)⟩,
   ⟨none, some (.third, .dual), some (.third .plural)⟩]

/-- Every other cell of the paradigm derives, with or without the optional (5). -/
theorem derive_eq_form :
    ∀ r ∈ Taos.prefixes, r.1 ∉ unaccounted →
      r.2 = derive false r.1 ∨ r.2 = derive true r.1 := by
  decide +kernel

theorem derive_unaccounted :
    unaccounted.map (derive false) =
      ["kǫ", "kǫ", "kǫ", "kǫ", "îw", "ímo", "ónóm", "ónóm", "ónów"] := by
  decide +kernel

-- (40), (26)
theorem derive_eq_form_printed :
    ∀ r ∈ Taos.prefixes, r.1 ∉ unaccounted →
      r.2 = deriveWith (impoverishmentPrinted false) r.1 ∨
        r.2 = deriveWith (impoverishmentPrinted true) r.1 := by
  decide +kernel

-- (19), (10)
theorem mopen_tiers :
    let c : Taos.Cell := ⟨some (.first, .singular), some (.second, .dual), none⟩
    let without (t : Tier) := onTiersVia fun u ↦ if u = t then .present else u
    derive false c = "mopén" ∧
      deriveWith (impoverishment false) c (without .participant) = "opén" ∧
      deriveWith (impoverishment false) c (without .number) = "mó" ∧
      deriveWith (impoverishment false) c (onTiersVia fun _ ↦ .present) = "" := by
  decide +kernel

/-! ### Impoverishment precedes metathesis in Taos (§3.2)

*opén*, the 1D:3:no prefix of the paper's (25), needs (24) to remove the goal's
`[−participant]` before (23) can swap the agent's `[+minimal]` with the goal's `[−author]`;
without (24) the two are not adjacent and the string stays in the order of *o-n-pé*. -/

/-- The 1D:3S:no prefix after impoverishment. -/
def prefix1D3no : Prefix :=
  run (impoverishment false)
    (spellOut cell1D3Sno)

theorem metathesis_prefix1D3no :
    (metathesis prefix1D3no (linearize prefix1D3no)).map (·.2) =
      [.author true, .atomic false, .author false, .minimal true, .atomic true, .minimal true,
        .dummy] := by
  decide +kernel

-- (24), (23)
theorem metathesis_without_r24 :
    let p := run (((order.erase r5).erase r24).map rule) (spellOut cell1D3Sno)
    metathesis p (linearize p) = linearize p := by
  decide +kernel

/-- Applied to the prefix as Spell-Out leaves it, (24) feeds (23): it removes the goal's
`[−participant]` that separates the agent's `[+minimal]` from the goal's `[−author]`. -/
theorem r24_feeds_m23 :
    Feeds r24.rule.apply (fun p ↦ Fires (m23 p) (linearize p))
      (spellOut cell1D3Sno) := by
  decide +kernel

theorem derive_prefix1D3no :
    derive false cell1D3Sno = "opén" := by
  decide +kernel

/-! ### Impoverishment precedes metathesis in Basque (§3.1)

The finite auxiliary of (10) is a string of terminals: the absolutive clitic, T, and the
ergative and dative clitics. Participant Dissimilation, the paper's (16) and (18) after Arregi
and Nevins's (25), obliterates a clitic in the Feature Markedness module; T-Noninitiality, the
paper's (12), is repaired in the Linear Operations module by Ergative Metathesis (13) or
L-Support, one module as in Arregi and Nevins's §6.2.4. T bears `[+tense]` for their `[+past]`,
and the dative-clitic conditions of their Ergative Metathesis and the `[+motion]` restriction of
Participant Dissimilation, which the two auxiliaries do not reach, are left out. -/

namespace Basque

/-- A Basque terminal is a list of Minimalist features. -/
abbrev Terminal := List FeatureVal

/-- A clitic bears its case and its person and number features. -/
def clitic (c : Case) (φ : Terminal) : Terminal := ⟨.case, c⟩ :: φ

/-- First person, in the Minimalist inventory. -/
def firstφ : Terminal := [⟨.participant, true⟩, ⟨.author, true⟩]

/-- Second person, in the Minimalist inventory. -/
def secondφ : Terminal := [⟨.participant, true⟩, ⟨.author, false⟩]

/-- T, past tense. -/
def pastT : Terminal := [⟨.tense, true⟩]

/-- The epenthetic L of L-Support, a terminal without features. -/
def lSupport : Terminal := []

/-- Under Participant Dissimilation a `[+participant +author]` clitic is obliterated when another
clitic of the word bears `trigger`; Arregi and Nevins's `[+motion]` restriction and their First
Singular Clitic Impoverishment, which keep first singular clitics out of it, are not modelled. -/
def participantDissimilation (trigger : Terminal) : ObliterationRule Terminal :=
  ⟨fun n ↦ firstφ ⊆ n.focus ∧ ∃ t ∈ n.leftCtx ++ n.rightCtx, trigger ⊆ t⟩

/-- In Ondarru, the paper's (16), the trigger is an ergative participant clitic. -/
def ondarru : ObliterationRule Terminal :=
  participantDissimilation [⟨.case, .erg⟩, ⟨.participant, true⟩]

/-- In Zamudio, the paper's (18), the trigger is any participant clitic. -/
def zamudio : ObliterationRule Terminal := participantDissimilation [⟨.participant, true⟩]

/-- Under Ergative Metathesis, the paper's (13) after Arregi and Nevins's (105), a word-initial
past T and what follows it up to the first ergative clitic change places with that clitic: the
double brackets open before T and close after the clitic, and the angled brackets stand before
the clitic. (105a)'s conditions on an intervening dative clitic are left out. -/
def ergativeMetathesis (n : Neighborhood Terminal) : Option Reduplication :=
  if n.leftCtx = [] ∧ ⟨.tense, true⟩ ∈ n.focus then
    (n.rightCtx.findIdx? (·.contains ⟨.case, .erg⟩)).map fun i ↦ .metathesis (i + 1) 1
  else none

theorem reduplicateFirst_ergativeMetathesis_perm (d : SpelloutDomain Terminal) :
    (reduplicateFirst ergativeMetathesis d).Perm d :=
  reduplicateFirst_perm (fun n b hb ↦ by
    unfold ergativeMetathesis at hb
    split_ifs at hb
    · obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hb; rfl
    · cases hb) d

/-- L-Support: an L before a word-initial T. -/
def lSupportRepair (d : SpelloutDomain Terminal) : SpelloutDomain Terminal :=
  if ∃ t ∈ d.head?, ⟨.tense, true⟩ ∈ t then lSupport :: d else d

/-- The Linear Operations module applies the two repairs of T-Noninitiality. -/
def linearOperations : SpelloutDomain Terminal → SpelloutDomain Terminal :=
  lSupportRepair ∘ reduplicateFirst ergativeMetathesis

/-- Feature Markedness before Linear Operations, the order of Figure 1. -/
def markednessThenLinear (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  linearOperations ∘ pd.apply

/-- Linear Operations before Feature Markedness, the order both papers reject. -/
def linearThenMarkedness (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  pd.apply ∘ linearOperations

/-- The Ondarru auxiliary of (17), *s-endu-n* 'you saw us': a first plural absolutive clitic,
past T, and a second singular ergative clitic. -/
def auxiliary17 : SpelloutDomain Terminal :=
  [clitic .abs (firstφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩]), pastT,
   clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩])]

/-- The Zamudio auxiliary of (19), *y-a-tzu-e-n* 'we accompanied you lot': past T, a second
plural dative clitic, and a first plural ergative clitic. -/
def auxiliary19 : SpelloutDomain Terminal :=
  [pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩]),
   clitic .erg (firstφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])]

theorem ondarru_markedness_then_linear :
    markednessThenLinear ondarru auxiliary17 =
      [clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩]), pastT] := by
  decide

-- (17b)
theorem ondarru_linear_then_markedness :
    linearThenMarkedness ondarru auxiliary17 =
      [pastT, clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩])] := by
  decide

-- §3.1.3
theorem ondarru_feeds :
    Feeds ondarru.apply (Fires ergativeMetathesis) auxiliary17 := by
  decide

theorem zamudio_markedness_then_linear :
    markednessThenLinear zamudio auxiliary19 =
      [lSupport, pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])] := by
  decide

-- §6.2.4
theorem zamudio_linear_then_markedness :
    linearThenMarkedness zamudio auxiliary19 =
      [pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])] := by
  decide

-- §3.1.4
theorem zamudio_bleeds :
    Bleeds zamudio.apply (Fires ergativeMetathesis) auxiliary19 := by
  decide

end Basque

end Middleton2026
