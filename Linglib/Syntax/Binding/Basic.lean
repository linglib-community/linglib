/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.Word.Basic

/-!
# Binding theory

A configuration says which positions command which and gives each position a binding domain; an
anaphoric dependency says which positions are antecedents of which. A position binds another
when it is an antecedent of it, distinct from it, that commands it. An anaphor is bound in its
domain (Condition A), a pronominal is not (Condition B), and an R-expression is not bound at all
(Condition C), the three conditions of Chomsky's binding theory.

Frameworks differ in what they supply. Chomsky binds coindexed noun phrases under c-command
within the governing category, Pollard and Sag under local o-command, and Charnavel within the
smallest spell-out domain. The dependency is a relation `L`, with `L a b` read as "`a` is an
antecedent of `b`"; coindexation is one encoding of it, and the logical binding that Reuland
reviews is another.

Condition A holds of the anaphors outside an exempt set. Chomsky exempts none and Pollard and Sag
exempt an anaphor that nothing in its domain commands (`Configuration.exempt`). Charnavel argues
that exemption is only apparent: the anaphor is bound in its domain by a silent pronoun, and
looks exempt when that position is left out of account.

## Main definitions

* `Binding.BindingClass`, `Binding.bindingClassOf`: anaphor, pronominal or R-expression, read
  off a word's morphology.
* `Binding.Configuration`: a command relation and a binding domain, ordered pointwise;
  `Configuration.comap` pulls one back along a map of positions, and
  `Configuration.monoclausal` is the configuration of a single binding domain.
* `Binding.pair`: the dependency relating two positions to each other alone.
* `Configuration.Binds`, `Bound`, `LocallyBound`, `LocallyCommanded`, `exempt`.
* `Configuration.Condition`, `Configuration.Satisfies`: Conditions A, B and C.
* `Configuration.covertlyBound`: the positions bound in their domain by a position that a
  restriction of the configuration leaves out.

## Main statements

* `Configuration.condition_iff_not_condition_pronoun`: outside the exempt set an anaphor and a
  pronominal with one domain are in complementary distribution.
* `Configuration.condition_exempt_iff`: with the structural exemption, an anaphor meets its
  condition when, if commanded in its domain, it is bound there.
* `Configuration.condition_mono`, `condition_pronoun_anti`, `condition_rExpression_anti`: more
  command binds more, so Condition A is monotone in the configuration and B and C antitone.
* `Configuration.condition_comap`: Condition A with nothing exempt among all positions is
  Condition A among some of them with those bound by a position left out exempt.

## Implementation notes

The conditions restrict binding. Coreference that is not binding falls outside Condition B, as
Reuland stresses, and outside this file.

## References

* [chomsky-1981]
* [pollard-sag-1992]
* [pollard-sag-1994]
* [reuland-2018]
* [charnavel-2019]
-/
@[expose] public section

namespace Binding

/-! ### Binding classes -/

/-- A nominal's binding class is an anaphor, reflexive or reciprocal, a pronominal, or an
R-expression, which fall under Conditions A, B and C. -/
inductive BindingClass where
  /-- Reflexive anaphor (*himself*, *herself*, *themselves*). -/
  | reflexive
  /-- Reciprocal anaphor (*each other*, *one another*). -/
  | reciprocal
  /-- Pronominal (*he*, *she*, *they*, …). -/
  | pronoun
  /-- Referring expression (proper name, full noun phrase). -/
  | rExpression
  deriving Repr, DecidableEq, Fintype

namespace BindingClass

/-- A class is an anaphor's, subject to Condition A, when it is reflexive or reciprocal. -/
def IsAnaphor (c : BindingClass) : Prop := c = .reflexive ∨ c = .reciprocal

/-- A class is a pronominal's, subject to Condition B. -/
def IsPronominal (c : BindingClass) : Prop := c = .pronoun

/-- A class is a referring expression's, subject to Condition C. -/
def IsRExpression (c : BindingClass) : Prop := c = .rExpression

instance (c : BindingClass) : Decidable c.IsAnaphor := inferInstanceAs (Decidable (_ ∨ _))
instance (c : BindingClass) : Decidable c.IsPronominal := inferInstanceAs (Decidable (_ = _))
instance (c : BindingClass) : Decidable c.IsRExpression := inferInstanceAs (Decidable (_ = _))

end BindingClass

/-- A part of speech is nominal when it is a proper noun, a common noun or a pronoun. -/
def IsNominal (cat : UD.UPOS) : Prop := cat = .PROPN ∨ cat = .NOUN ∨ cat = .PRON

instance : DecidablePred IsNominal := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- `bindingClassOf w` reads the binding class of `w` off its morphology and category.
Reflexive marking makes a reflexive, the reciprocal pronoun type a reciprocal, any other pronoun
a pronominal, and a noun an R-expression. -/
def bindingClassOf (w : Morphology.Word) : Option BindingClass :=
  if (w.features .reflex).isSome then some .reflexive
  else match w.features .pronType with
    | some .Rcp => some .reciprocal
    | _ =>
      if w.cat = .PRON then some .pronoun
      else if IsNominal w.cat then some .rExpression
      else none

/-! ### Configurations -/

/-- A binding configuration on the positions `ι` says which positions command which and gives
each position its binding domain. -/
structure Configuration (ι : Type*) where
  /-- `commands a b` holds when `a` commands `b`. -/
  commands : ι → ι → Prop
  /-- `domain b` is the binding domain of `b`. -/
  domain : ι → Set ι

/-- `pair a b` is the dependency that relates `a` and `b` to each other and nothing else. -/
def pair {ι : Type*} (a b : ι) (x y : ι) : Prop := x = a ∧ y = b ∨ x = b ∧ y = a

instance {ι : Type*} [DecidableEq ι] (a b : ι) : DecidableRel (pair a b) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem pair_comm {ι : Type*} (a b : ι) : pair a b = pair b a :=
  funext fun _ ↦ funext fun _ ↦ propext or_comm

namespace Configuration

variable {ι : Type*}

/-- Configurations are ordered pointwise, `s ≤ t` when `t` commands whatever `s` commands and
each domain of `s` lies in the corresponding domain of `t`. -/
instance : PartialOrder (Configuration ι) :=
  PartialOrder.lift (fun s ↦ (s.commands, s.domain)) fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

theorem le_def {s t : Configuration ι} :
    s ≤ t ↔ s.commands ≤ t.commands ∧ s.domain ≤ t.domain :=
  Iff.rfl

/-- `s.comap f` is the configuration that `s` induces along `f`, in which one position commands
another when their images do and a position's domain is the preimage of its image's. -/
def comap {κ : Type*} (f : κ → ι) (s : Configuration ι) : Configuration κ where
  commands a b := s.commands (f a) (f b)
  domain b := f ⁻¹' s.domain (f b)

theorem comap_mono {κ : Type*} (f : κ → ι) : Monotone (comap f) :=
  fun _ _ h ↦ ⟨fun _ _ hc ↦ h.1 _ _ hc, fun _ _ ha ↦ h.2 _ ha⟩

instance {κ : Type*} (f : κ → ι) (s : Configuration ι) [DecidableRel s.commands] :
    DecidableRel (s.comap f).commands :=
  fun _ _ ↦ inferInstanceAs (Decidable (s.commands _ _))

instance {κ : Type*} (f : κ → ι) (s : Configuration ι) [∀ b, DecidablePred (· ∈ s.domain b)]
    (b : κ) : DecidablePred (· ∈ (s.comap f).domain b) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ s.domain _))

/-- `monoclausal pos R` is the configuration of a single binding domain. The map `pos` reads a
position as an object, one position commands another when its object `R`-commands the other's,
and every position lies in every domain. -/
def monoclausal {α : Type*} (pos : ι → Option α) (R : α → α → Prop) : Configuration ι where
  commands a b := ∃ x ∈ pos a, ∃ y ∈ pos b, R x y
  domain _ := Set.univ

theorem monoclausal_mono {α : Type*} {pos : ι → Option α} {R R' : α → α → Prop} (h : R ≤ R') :
    monoclausal pos R ≤ monoclausal pos R' :=
  ⟨fun _ _ ⟨x, hx, y, hy, hr⟩ ↦ ⟨x, hx, y, hy, h x y hr⟩, le_rfl⟩

instance {α : Type*} (pos : ι → Option α) (R : α → α → Prop) [DecidableRel R] :
    DecidableRel (monoclausal pos R).commands :=
  fun _ _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _))

instance {α : Type*} (pos : ι → Option α) (R : α → α → Prop) (b : ι) :
    DecidablePred (· ∈ (monoclausal pos R).domain b) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ Set.univ))

variable (s : Configuration ι) (L : ι → ι → Prop)

/-- `a` binds `b` along the dependency `L` when `a` is an antecedent of `b` other than `b`
itself and commands `b`. -/
def Binds (a b : ι) : Prop := a ≠ b ∧ L a b ∧ s.commands a b

/-- `b` is bound when some position binds it. -/
def Bound (b : ι) : Prop := ∃ a, s.Binds L a b

/-- `b` is locally bound when some position in its domain binds it. -/
def LocallyBound (b : ι) : Prop := ∃ a ∈ s.domain b, s.Binds L a b

/-- `b` is locally commanded when some position other than `b` in its domain commands it. -/
def LocallyCommanded (b : ι) : Prop := ∃ a ∈ s.domain b, a ≠ b ∧ s.commands a b

/-- `exempt` is the set of positions that nothing in their domain commands. -/
def exempt : Set ι := {b | ¬ s.LocallyCommanded b}

/-- `Condition E b c` is the condition a nominal of class `c` at `b` must meet when the
positions in `E` are exempt from Condition A. An anaphor is bound in its domain unless exempt, a
pronominal is not bound in its domain, and an R-expression is not bound. -/
def Condition (E : Set ι) (b : ι) : BindingClass → Prop
  | .reflexive | .reciprocal => b ∈ E ∨ s.LocallyBound L b
  | .pronoun => ¬ s.LocallyBound L b
  | .rExpression => ¬ s.Bound L b

/-- The dependency `L` satisfies the binding theory, with the positions in `E` exempt from
Condition A, when every position the classifier `cls` classifies meets its class's condition. -/
def Satisfies (E : Set ι) (cls : ι → Option BindingClass) : Prop :=
  ∀ b c, cls b = some c → s.Condition L E b c

variable {s L} {t : Configuration ι} {L' : ι → ι → Prop} {E E' : Set ι}
  {cls : ι → Option BindingClass} {a b x : ι} {c : BindingClass}

theorem Binds.commands (h : s.Binds L a b) : s.commands a b := h.2.2

theorem Binds.mono (hL : L ≤ L') (h : s.Binds L a b) : s.Binds L' a b :=
  ⟨h.1, hL a b h.2.1, h.2.2⟩

theorem Bound.mono (hL : L ≤ L') (h : s.Bound L b) : s.Bound L' b :=
  let ⟨a, ha⟩ := h
  ⟨a, ha.mono hL⟩

theorem LocallyBound.mono (hL : L ≤ L') (h : s.LocallyBound L b) : s.LocallyBound L' b :=
  let ⟨a, hd, ha⟩ := h
  ⟨a, hd, ha.mono hL⟩

theorem Binds.of_le (hst : s ≤ t) (h : s.Binds L a b) : t.Binds L a b :=
  ⟨h.1, h.2.1, hst.1 a b h.2.2⟩

theorem Bound.of_le (hst : s ≤ t) (h : s.Bound L b) : t.Bound L b :=
  let ⟨a, ha⟩ := h
  ⟨a, ha.of_le hst⟩

theorem LocallyBound.of_le (hst : s ≤ t) (h : s.LocallyBound L b) : t.LocallyBound L b :=
  let ⟨a, hd, ha⟩ := h
  ⟨a, hst.2 b hd, ha.of_le hst⟩

theorem LocallyBound.bound (h : s.LocallyBound L b) : s.Bound L b :=
  let ⟨a, _, ha⟩ := h
  ⟨a, ha⟩

theorem LocallyBound.locallyCommanded (h : s.LocallyBound L b) : s.LocallyCommanded b :=
  let ⟨a, hd, ha⟩ := h
  ⟨a, hd, ha.1, ha.commands⟩

theorem not_locallyBound_of_mem_exempt (hb : b ∈ s.exempt) : ¬ s.LocallyBound L b :=
  fun h ↦ hb h.locallyCommanded

theorem bound_iff_binds (h : ∀ x, L x b → x = a ∨ x = b) : s.Bound L b ↔ s.Binds L a b :=
  ⟨fun ⟨x, hx⟩ ↦ (h x hx.2.1).elim (· ▸ hx) (absurd · hx.1), fun h ↦ ⟨a, h⟩⟩

theorem binds_pair_iff (hab : a ≠ b) : s.Binds (pair a b) x b ↔ x = a ∧ s.commands a b := by
  constructor
  · rintro ⟨hxb, ⟨rfl, -⟩ | ⟨rfl, -⟩, hc⟩
    · exact ⟨rfl, hc⟩
    · exact absurd rfl hxb
  · rintro ⟨rfl, hc⟩
    exact ⟨hab, .inl ⟨rfl, rfl⟩, hc⟩

theorem bound_pair_iff (hab : a ≠ b) : s.Bound (pair a b) b ↔ s.commands a b :=
  ⟨fun ⟨_, h⟩ ↦ ((binds_pair_iff hab).1 h).2, fun hc ↦ ⟨a, (binds_pair_iff hab).2 ⟨rfl, hc⟩⟩⟩

theorem locallyBound_pair_iff (hab : a ≠ b) :
    s.LocallyBound (pair a b) b ↔ a ∈ s.domain b ∧ s.commands a b := by
  constructor
  · rintro ⟨x, hd, h⟩
    obtain ⟨rfl, hc⟩ := (binds_pair_iff hab).1 h
    exact ⟨hd, hc⟩
  · rintro ⟨hd, hc⟩
    exact ⟨a, hd, (binds_pair_iff hab).2 ⟨rfl, hc⟩⟩

theorem condition_anaphor (hc : c.IsAnaphor) :
    s.Condition L E b c ↔ b ∈ E ∨ s.LocallyBound L b := by
  rcases hc with rfl | rfl <;> rfl

/-- Outside the exempt positions an anaphor meets its condition exactly where a pronominal fails
its own. -/
theorem condition_iff_not_condition_pronoun (hc : c.IsAnaphor) (hb : b ∉ E) :
    s.Condition L E b c ↔ ¬ s.Condition L E b .pronoun := by
  rw [condition_anaphor hc, Condition, not_not, or_iff_right hb]

theorem condition_of_mem (hc : c.IsAnaphor) (hb : b ∈ E) : s.Condition L E b c :=
  (condition_anaphor hc).2 (.inl hb)

/-- With the structural exemption, an anaphor meets its condition exactly when it is bound in
its domain if anything there commands it. -/
theorem condition_exempt_iff (hc : c.IsAnaphor) :
    s.Condition L s.exempt b c ↔ (s.LocallyCommanded b → s.LocallyBound L b) := by
  rw [condition_anaphor hc, imp_iff_not_or]
  rfl

theorem condition_empty_iff (hc : c.IsAnaphor) :
    s.Condition L ∅ b c ↔ s.Condition L s.exempt b c ∧ s.LocallyCommanded b := by
  rw [condition_anaphor hc, condition_exempt_iff hc]
  exact ⟨fun h ↦ ⟨fun _ ↦ h.resolve_left id, (h.resolve_left id).locallyCommanded⟩,
    fun h ↦ .inr (h.1 h.2)⟩

theorem condition_pronoun_of_rExpression (h : s.Condition L E b .rExpression) :
    s.Condition L E b .pronoun :=
  fun hb ↦ h hb.bound

theorem Satisfies.mono_exempt (hE : E ⊆ E') (h : s.Satisfies L E cls) : s.Satisfies L E' cls := by
  intro b c hbc
  have := h b c hbc
  cases c with
  | reflexive | reciprocal => exact this.imp_left (hE ·)
  | pronoun | rExpression => exact this

/-- An anaphor's condition is monotone in the configuration, since more command and larger
domains bind more. -/
theorem condition_mono (hc : c.IsAnaphor) :
    Monotone fun s : Configuration ι ↦ s.Condition L E b c := fun _ _ hst h ↦
  (condition_anaphor hc).2 (((condition_anaphor hc).1 h).imp_right (·.of_le hst))

/-- A pronominal's condition is antitone in the configuration. -/
theorem condition_pronoun_anti :
    Antitone fun s : Configuration ι ↦ s.Condition L E b .pronoun :=
  fun _ _ hst h hb ↦ h (hb.of_le hst)

/-- An R-expression's condition is antitone in the configuration. -/
theorem condition_rExpression_anti :
    Antitone fun s : Configuration ι ↦ s.Condition L E b .rExpression :=
  fun _ _ hst h hb ↦ h (hb.of_le hst)

/-! ### Positions left out of account

A configuration restricts along an injection `f` to the positions `f` reaches. A position bound
in its domain by one that `f` does not reach is bound in the whole configuration and may be free
in the restriction. -/

section Comap

open scoped Function

variable {κ : Type*} {f : κ → ι} {a b : κ}

variable (s L f) in
/-- `s.covertlyBound L f` is the set of positions whose images are bound in their domains by a
position outside the range of `f`. -/
def covertlyBound : Set κ := {b | ∃ x ∈ s.domain (f b), x ∉ Set.range f ∧ s.Binds L x (f b)}

theorem binds_comap (hf : f.Injective) :
    (s.comap f).Binds (L on f) a b ↔ s.Binds L (f a) (f b) := by
  simp only [Binds, comap, ne_eq, hf.eq_iff]

theorem locallyBound_comap_or (hf : f.Injective) :
    (s.comap f).LocallyBound (L on f) b ∨ b ∈ s.covertlyBound L f ↔ s.LocallyBound L (f b) := by
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨x, hx, -, h⟩)
    exacts [⟨f a, ha, (binds_comap hf).1 h⟩, ⟨x, hx, h⟩]
  · rintro ⟨x, hx, h⟩
    by_cases hr : x ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hr
      exact .inl ⟨a, hx, (binds_comap hf).2 h⟩
    · exact .inr ⟨x, hx, hr, h⟩

theorem bound_comap_or (hf : f.Injective) :
    (s.comap f).Bound (L on f) b ∨ (∃ x ∉ Set.range f, s.Binds L x (f b)) ↔ s.Bound L (f b) := by
  constructor
  · rintro (⟨a, h⟩ | ⟨x, -, h⟩)
    exacts [⟨f a, (binds_comap hf).1 h⟩, ⟨x, h⟩]
  · rintro ⟨x, h⟩
    by_cases hr : x ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hr
      exact .inl ⟨a, (binds_comap hf).2 h⟩
    · exact .inr ⟨x, hr, h⟩

/-- An anaphor meets Condition A among all positions exactly when it meets it among those `f`
reaches with the covertly bound positions exempt. -/
theorem condition_comap (hf : f.Injective) (hc : c.IsAnaphor) :
    (s.comap f).Condition (L on f) (f ⁻¹' E ∪ s.covertlyBound L f) b c ↔
      s.Condition L E (f b) c := by
  rw [condition_anaphor hc, condition_anaphor hc, ← locallyBound_comap_or hf, Set.mem_union,
    Set.mem_preimage, or_assoc, or_comm (a := b ∈ s.covertlyBound L f)]

theorem mem_covertlyBound_of_condition (hf : f.Injective) (hc : c.IsAnaphor)
    (h : s.Condition L ∅ (f b) c) (hb : ¬ (s.comap f).LocallyBound (L on f) b) :
    b ∈ s.covertlyBound L f :=
  ((locallyBound_comap_or hf).2 (((condition_anaphor hc).1 h).resolve_left id)).resolve_left hb

theorem condition_pronoun_comap (hf : f.Injective) {F : Set κ} :
    (s.comap f).Condition (L on f) F b .pronoun ∧ b ∉ s.covertlyBound L f ↔
      s.Condition L E (f b) .pronoun := by
  simp only [Condition, ← locallyBound_comap_or hf, not_or]

theorem condition_rExpression_comap (hf : f.Injective) {F : Set κ} :
    (s.comap f).Condition (L on f) F b .rExpression ∧ (¬ ∃ x ∉ Set.range f, s.Binds L x (f b)) ↔
      s.Condition L E (f b) .rExpression := by
  simp only [Condition, ← bound_comap_or hf, not_or]

end Comap

section Decidable

variable (s L) [Fintype ι] [DecidableEq ι] [DecidableRel L] [DecidableRel s.commands]
  [∀ b, DecidablePred (· ∈ s.domain b)]

instance (a b : ι) : Decidable (s.Binds L a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (b : ι) : Decidable (s.Bound L b) := inferInstanceAs (Decidable (∃ _, _))

instance (b : ι) : Decidable (s.LocallyBound L b) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance (b : ι) : Decidable (s.LocallyCommanded b) :=
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance {κ : Type*} [Fintype κ] (f : κ → ι) (b : κ) : Decidable (b ∈ s.covertlyBound L f) :=
  inferInstanceAs (Decidable (∃ x, x ∈ s.domain (f b) ∧ x ∉ Set.range f ∧ _))

instance : DecidablePred (· ∈ s.exempt) := fun _ ↦ inferInstanceAs (Decidable (¬ _))

instance (E : Set ι) [DecidablePred (· ∈ E)] (b : ι) : ∀ c, Decidable (s.Condition L E b c)
  | .reflexive | .reciprocal => inferInstanceAs (Decidable (_ ∨ _))
  | .pronoun | .rExpression => inferInstanceAs (Decidable (¬ _))

instance (E : Set ι) [DecidablePred (· ∈ E)] (cls : ι → Option BindingClass) :
    Decidable (s.Satisfies L E cls) :=
  inferInstanceAs (Decidable (∀ _ _, _ → _))

end Decidable

end Configuration

end Binding
