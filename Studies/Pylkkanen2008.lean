module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.Tree
public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Data.Examples.Pylkkanen2008

/-!
# Pylkkänen (2008): Introducing Arguments

Pylkkänen's inventory of argument-introducing heads underlies two typologies. Applicative heads
are high or low: a high applicative relates the applied argument to the event and combines with
the verb phrase by Event Identification, and a low applicative relates it to the verb's theme
by a transfer of possession and takes the verb as its argument. Causative heads share one
meaning, Cause, which relates a causing event to a caused one and introduces no individual;
they vary in whether Cause is bundled with Voice and in whether it selects a root, a verb or a
phase. The diagnostics that separate the heads, such as the restriction of low applicatives to
structures with a direct object, are facts about semantic types, derived here by the
type-driven composition engine.

## Main definitions

* `lowAppl`: the low applicative.
* `CauseHead.Embeds`: the layers a causative head's complement may contain.

## Implementation notes

Semantic types are those of `Montague.Ty`, whose eventuality sort `v` is the book's event type
`s`, so the book's `⟨s,t⟩` is `Ty.vt` and `⟨e,⟨s,t⟩⟩` is `Ty.evt`. A constituent fails to compose
with another exactly when `Ty.combine?` returns `none`.

The third applicative diagnostic, the availability of the applied argument for depictive
modification, is also a typing fact in the book: a depictive phrase is of type ⟨e,⟨s,t⟩⟩ and
combines by Predicate Modification with constituents of that type, which a high Appl' is and a
low Appl' is not. The engine's predicate modification is at `⟨e,t⟩` and `⟨v,t⟩` only, so that
diagnostic is recorded in the data rows only.

The Voice-bundling status of the Bemba, Luganda, and Venda causatives is unknown (Table 3.1,
note a), so only the English, Japanese, and Finnish heads are given as `CauseHead` values.

## TODO

The second applicative diagnostic (18), that low applicatives are nonsensical with completely
static verbs such as *hold*, is a fact about the plausibility of the transfer of possession
(15) asserts, not a typing fact: the low ApplP composes with a static transitive verb
(`lowApplP_composes_transitive`). Since the transfer relation of (15) is not relativized to the
event, the clash with a static event does not follow from the denotation; the study records the
book's correlation of the two tests across Table 2.1 (`table21_static_iff_unergative`).

## References

* [pylkkanen-2008]
* [kratzer-1996]
* [marantz-1993]
* [marantz-1997]
* [cuervo-2003]
-/

@[expose] public section

namespace Pylkkanen2008


open ArgumentStructure Minimalist Examples Montague PhraseStructure.Tree
open scoped SetRel

variable {Entity E : Type*}

/-! ### Applicatives: high relates to the event, low to the theme -/

/-- The low applicative (15) relates the direct object `x` to the indirect object `y` by the
transfer relation `poss`, to-the-possession for a recipient applicative and from-the-possession
for a source applicative, and asserts that `x` is the theme of the verb `f`. -/
def lowAppl (theme : Entity → E → Prop) (poss : Entity → Entity → Prop) (x y : Entity)
    (f : Entity → E → Prop) : E → Prop :=
  fun e ↦ f x e ∧ theme x e ∧ poss x y

/-- `lowApplTy` is the type of the low applicative head (15), `⟨e,⟨e,⟨⟨e,⟨s,t⟩⟩,⟨s,t⟩⟩⟩⟩`. -/
abbrev lowApplTy : Ty := .e ⇒ .e ⇒ Ty.evt ⇒ Ty.vt

/-- `sisterTy a` is the type of the applicative constituent that is the verb's sister, the high
applicative head (13) of type `⟨e,⟨s,t⟩⟩`, which the verb phrase combines with by Event
Identification, or the low ApplP of type `⟨⟨e,⟨s,t⟩⟩,⟨s,t⟩⟩`, which takes the verb as its
argument. The affected
applicative of [cuervo-2003] is outside the book's inventory and has no type here. -/
def sisterTy : ApplType → Option Ty
  | .high => some Ty.evt
  | .low _ => some (Ty.evt ⇒ Ty.vt)
  | .affected => none

/-- An applicative composes with an unergative verb phrase, of type `⟨s,t⟩`, exactly when it is
high, Diagnostic 1 (17). -/
theorem composes_unergative_iff (a : ApplType) :
    (∃ τ ∈ sisterTy a, (Ty.combine? τ Ty.vt).isSome) ↔ a = .high := by
  cases a <;> simp [sisterTy] <;> decide

-- (17)
theorem lowAppl_not_composes_unergative :
    ∀ τ ∈ [lowApplTy, .e ⇒ Ty.evt ⇒ Ty.vt, Ty.evt ⇒ Ty.vt],
      Ty.combine? τ Ty.vt = none ∧ Ty.combine? Ty.vt τ = none := by
  decide

-- (18)
theorem lowApplP_composes_transitive : Ty.combine? (Ty.evt ⇒ Ty.vt) Ty.evt = some Ty.vt := by
  decide

-- (16)
theorem voiceP_lowAppl (agent theme : Entity → E → Prop) (poss : Entity → Entity → Prop)
    (buying : E → Prop) (mary john book : Entity) (e : E) :
    eventIdentification agent
        (lowAppl theme poss book john (eventIdentification theme buying)) mary e ↔
      buying e ∧ agent mary e ∧ theme book e ∧ poss book john := by
  simp only [eventIdentification_apply, lowAppl]
  tauto

/-- Over an unergative, low ApplP holds of no event when no participant is both agent and theme
(103b). -/
theorem lowAppl_agent_eq_bot {agent theme : Entity → E → Prop} (h : Disjoint agent theme)
    (poss : Entity → Entity → Prop) (run : E → Prop) (x y : Entity) :
    lowAppl theme poss x y (eventIdentification agent run) = ⊥ := by
  ext e
  simp only [Pi.disjoint_iff, Prop.disjoint_iff] at h
  simpa [lowAppl] using fun ha _ ht _ ↦ h x e ⟨ha, ht⟩

/-- A `Construction` is one of the applicative constructions the book analyzes, with the head it
assigns
(Table 1.1, together with the Korean and Albanian applicatives of Chapter 2). -/
inductive Construction where
  | chagaBenefactive
  | lugandaBenefactive
  | vendaBenefactive
  | albanianBenefactive
  | japaneseGaplessAdversity
  | englishDOC
  | japaneseDOC
  | koreanDOC
  | hebrewPossessorDative
  | japaneseAdversityCausative
  | japaneseGappedAdversity
  deriving DecidableEq, Repr

/-- `c.head` is the head the book assigns to the construction `c`. -/
def Construction.head : Construction → ApplType
  | .chagaBenefactive | .lugandaBenefactive | .vendaBenefactive | .albanianBenefactive
  | .japaneseGaplessAdversity => .high
  | .englishDOC | .japaneseDOC | .koreanDOC => .low .recipient
  | .hebrewPossessorDative | .japaneseAdversityCausative | .japaneseGappedAdversity =>
    .low .source

/-- A construction composes with an unergative verb phrase when its head's applicative
constituent does. -/
def Construction.ComposesUnergative (c : Construction) : Prop :=
  ∃ τ ∈ sisterTy c.head, (Ty.combine? τ Ty.vt).isSome

instance : DecidablePred Construction.ComposesUnergative := fun c ↦
  inferInstanceAs (Decidable (∃ τ ∈ sisterTy c.head, _))

/-- Table 2.1 lists each of the six languages with the construction tested, its unergative test,
and its static-verb test. -/
def table21 : List (Construction × Datum × Datum) :=
  [(.englishDOC, ex20a, ex20b), (.japaneseDOC, ex21a, ex21b), (.koreanDOC, ex22a, ex22b),
   (.lugandaBenefactive, ex23a, ex23b), (.vendaBenefactive, ex24a, ex24b),
   (.albanianBenefactive, ex25a, ex25b)]

-- Table 2.1
theorem table21_unergative :
    ∀ t ∈ table21, t.2.1.judgment = .acceptable ↔ t.1.ComposesUnergative := by
  decide

-- Table 2.1, §2.1.2
theorem table21_static_iff_unergative :
    ∀ t ∈ table21, t.2.2.judgment = .acceptable ↔ t.2.1.judgment = .acceptable := by
  decide

-- Table 2.5
theorem adversity_passives :
    Construction.japaneseGaplessAdversity.ComposesUnergative ∧
      ¬ Construction.japaneseGappedAdversity.ComposesUnergative := by
  decide

-- (102), Table 2.2
theorem possessor_dative_transitivity :
    ¬ Construction.hebrewPossessorDative.ComposesUnergative := by
  decide

/-! ### Cause introduces a causing event, not a causer -/

-- (9), (14), (13b), (16), (15b)
theorem melted_readings (M : EventStructure.Interpretation Entity E E)
    (agent causer : Entity → E → Prop) (melt : E → Prop) (john : Entity) (e : E) :
    (eventIdentification agent (M.vCause melt) john e ↔
        agent john e ∧ ∃ e', e ~[M.cause] e' ∧ melt e') ∧
      (eventIdentification causer melt john e ↔ causer john e ∧ melt e) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- `causeTy` is the type of Cause (9), `⟨⟨s,t⟩,⟨s,t⟩⟩`. -/
abbrev causeTy : Ty := Ty.vt ⇒ Ty.vt

-- (18), (16a), §3.2
theorem unaccusative_causative :
    Ty.combine? causeTy Ty.vt = some Ty.vt ∧ Ty.combine? Ty.evt Ty.vt = some Ty.evt := by
  decide

/-- The heads of the Voice-bundling Cause (42) cannot combine with each other and apply to the verb
phrase Cause first (§3.3). -/
theorem cause_voice_order :
    Ty.combine? causeTy Ty.evt = none ∧ Ty.combine? Ty.evt causeTy = none ∧
      (Ty.combine? causeTy Ty.vt).bind (Ty.combine? Ty.evt) = some Ty.evt ∧
      (Ty.combine? Ty.evt Ty.vt).bind (Ty.combine? causeTy) = none := by
  decide

/-! ### Selection: Cause takes a root, a verb, or a phase -/

/-- The layers of the Kratzer/Marantz verbal architecture (12) are the category-neutral root, the
verb a category-defining head makes of it, and the phase closed by an external-argument
introducer, Voice or a high applicative. -/
inductive Layer where
  | root
  | verb
  | phase
  deriving DecidableEq, Repr, Fintype

/-- Layers are ordered by containment. -/
def Layer.rank : Layer → ℕ
  | .root => 0
  | .verb => 1
  | .phase => 2

instance : LinearOrder Layer := LinearOrder.lift' Layer.rank (by decide)

/-- A causative head is given by the largest layer its complement may contain (11) and whether
Cause is bundled with Voice (10). -/
structure CauseHead where
  selects : Layer
  bundled : Bool
  deriving DecidableEq, Repr

/-- `c.Embeds l` holds when a constituent of layer `l` can occur between the root and Cause. -/
def CauseHead.Embeds (c : CauseHead) (l : Layer) : Prop := l ≤ c.selects

instance (c : CauseHead) (l : Layer) : Decidable (c.Embeds l) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- Table 3.2
theorem embeds_verb_iff (c : CauseHead) : c.Embeds .verb ↔ c.selects ≠ .root := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

-- Table 3.2
theorem embeds_phase_iff (c : CauseHead) : c.Embeds .phase ↔ c.selects = .phase := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- A causee position (94) exists inside Cause's complement when that complement is at least a
verb, or between Cause and Voice when Cause is not bundled with Voice. -/
def CauseHead.HasCauseePosition (c : CauseHead) : Prop := c.Embeds .verb ∨ c.bundled = false

instance (c : CauseHead) : Decidable c.HasCauseePosition :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Causatives of unergatives and transitives are impossible exactly for a root-selecting,
Voice-bundling head (Table 3.1, second row). -/
theorem hasCauseePosition_iff (c : CauseHead) :
    c.HasCauseePosition ↔ ¬ (c.selects = .root ∧ c.bundled = true) := by
  obtain ⟨s, b⟩ := c; cases s <;> cases b <;> decide

/-- The English zero-causative is root-selecting and Voice-bundling. -/
def englishZero : CauseHead := ⟨.root, true⟩

/-- The Japanese lexical causative is root-selecting, with Cause independent of Voice. -/
def japaneseLexical : CauseHead := ⟨.root, false⟩

/-- The Finnish *-tta* causative is verb-selecting, with Cause independent of Voice. -/
def finnishTta : CauseHead := ⟨.verb, false⟩

-- (95), (96)
theorem root_causativized_unergative :
    (ex95.judgment = .acceptable ↔ englishZero.HasCauseePosition) ∧
      (ex96.judgment = .acceptable ↔ japaneseLexical.HasCauseePosition) := by
  decide

end Pylkkanen2008
