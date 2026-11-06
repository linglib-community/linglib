/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Four
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Trivalent propositions

A trivalent proposition is a function `W → Trivalent`, true, false or undefined at each world,
with the connectives taken pointwise. Its worlds split into a positive extension, a negative
extension and a gap. Sending a proposition to its two extensions is a bounded lattice embedding
into Fitting's product `Set W ⊙ Set W`, natural in the worlds, whose image is the disjoint pairs;
it carries Kleene's negation to the swap and transplication to Fitting's guard. A trivalent
proposition is also a conditional event in de Finetti's sense, the transplication of its truth on
its definedness, and Beaver and Krahmer's assertion operator applied pointwise collapses its gap
into the negative extension. The file ends with the three families of trivalent quantifiers.

## Main definitions

* `Trivalent.posExt`, `Trivalent.negExt`, `Trivalent.gapExt`: where a proposition is true, false
  and undefined.
* `Trivalent.extensions`: the two extensions, as a bounded lattice hom into `Set W ⊙ Set W`, and
  `Trivalent.orderIsoDisjoint`: an order isomorphism onto the disjoint pairs.
* `Trivalent.IsBivalent`: the proposition is never `undefined`.
* `Trivalent.forallWeak`, `Trivalent.existsWeak`: the Weak Kleene quantifiers, undefined as
  soon as any instance is.
* `Trivalent.forallStrong`, `Trivalent.existsStrong`: the Strong Kleene quantifiers, the
  indexed `⊓` and `⊔`.
* `Trivalent.forallHaug`, `Trivalent.existsHaug`: Haug's quantifiers, undefined only when
  every instance is, with `existsHaug_meetWeak_presuppose` as Quantifier Projection.

## Main results

* `Trivalent.extensions_compl`, `Trivalent.extensions_transplication`, `Trivalent.extensions_comp`:
  negation is the swap, transplication is Fitting's guard, and reindexing the worlds takes
  preimages.
* `Trivalent.transplication_definedness_truth`, `Trivalent.transplication_ofProp_eq_iff`: every
  trivalent proposition is the conditional event of its truth on its definedness, and two
  conditional events coincide exactly when they have the same condition and agree on it.

Each family is the quantifier of a theory of how a presupposition projects from the scope of a
quantifier. Over the domain's subtype, the Weak Kleene quantifiers project universally, as
Chemla's experiments support, Haug's existentially, as Mayr and Sauerland argue for a semantic
projection that pragmatics then strengthens, and the Strong Kleene existential of Kleene and Fox
is defined exactly where some instance is true or every instance is false; Spector and Sudo
delimit when each reading surfaces.

## Implementation notes

The Strong Kleene quantifiers are explicit definitions rather than `⨅` and `⨆`, because a
`CompleteLinearOrder` instance on `Trivalent` would carry a second `LinearOrder` parent that
instance search prefers, making every later `⊓` noncomputable.

## References

* [beaver-krahmer-2001]
* [kriz-2016]
* [haug-2014]
* [coppock-beaver-2015]
* [chemla-2009a]
* [mayr-sauerland-2015]
* [spector-sudo-2017]
* [fox-2013]
* [de-finetti-1936]
* [fitting-1994]
* [george-2014]
-/

@[expose] public section

namespace Trivalent

open Bilattice Product

variable {W : Type*}

/-! ### Extensions -/

/-- The positive extension collects the worlds where the proposition is true. -/
def posExt (p : W → Trivalent) : Set W := {w | p w = .true}

/-- The negative extension collects the worlds where the proposition is false. -/
def negExt (p : W → Trivalent) : Set W := {w | p w = .false}

/-- The extension gap collects the worlds where the proposition is neither true nor false. -/
def gapExt (p : W → Trivalent) : Set W := {w | p w = .undefined}

section Extensions

variable {p q : W → Trivalent} {w : W}

@[simp] theorem mem_posExt : w ∈ posExt p ↔ p w = .true := Iff.rfl
@[simp] theorem mem_negExt : w ∈ negExt p ↔ p w = .false := Iff.rfl
@[simp] theorem mem_gapExt : w ∈ gapExt p ↔ p w = .undefined := Iff.rfl

instance (p : W → Trivalent) : DecidablePred (· ∈ posExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .true))

instance (p : W → Trivalent) : DecidablePred (· ∈ negExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .false))

instance (p : W → Trivalent) : DecidablePred (· ∈ gapExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .undefined))

theorem posExt_union_negExt_union_gapExt (p : W → Trivalent) :
    posExt p ∪ negExt p ∪ gapExt p = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ, iff_true]
  cases p w <;> simp

/-- The positive and negative extensions of a trivalent proposition, in Fitting's product of
world-sets: Strong Kleene conjunction and disjunction are its truth meet and join. -/
def extensions : BoundedLatticeHom (W → Trivalent) (Set W ⊙ Set W) where
  toFun p := mk (posExt p) (negExt p)
  map_sup' p q := by ext w <;> simp [posExt, negExt]
  map_inf' p q := by ext w <;> simp [posExt, negExt]
  map_top' := by ext w <;> simp [posExt, negExt]
  map_bot' := by ext w <;> simp [posExt, negExt]

theorem extensions_apply (p : W → Trivalent) : extensions p = mk (posExt p) (negExt p) := rfl

@[simp] theorem pro_extensions (p : W → Trivalent) : (extensions p).pro = posExt p := rfl
@[simp] theorem con_extensions (p : W → Trivalent) : (extensions p).con = negExt p := rfl

/-- `extensions` is natural in the worlds: reindexing a proposition along `f` takes preimages of
its extensions. -/
theorem extensions_comp {W' : Type*} (f : W' → W) (p : W → Trivalent) :
    extensions (p ∘ f) = mk (f ⁻¹' posExt p) (f ⁻¹' negExt p) := rfl

theorem extensions_le_extensions : extensions p ≤ extensions q ↔ p ≤ q := by
  have key : ∀ a b : Trivalent, a ≤ b ↔ (a = .true → b = .true) ∧ (b = .false → a = .false) := by
    decide
  simp only [extensions_apply, mk_le_mk, Set.subset_def, mem_posExt, mem_negExt, Pi.le_def, key]
  exact ⟨fun h w ↦ ⟨h.1 w, h.2 w⟩, fun h ↦ ⟨fun w ↦ (h w).1, fun w ↦ (h w).2⟩⟩

theorem extensions_injective : Function.Injective (extensions (W := W)) := fun _ _ h ↦
  le_antisymm (extensions_le_extensions.1 h.le) (extensions_le_extensions.1 h.ge)

/-- The extensions of a proposition are disjoint, and every disjoint pair is the extensions of a
proposition: over a Boolean factor, Fitting's consistent pairs. -/
theorem range_extensions : Set.range (extensions (W := W)) = {x | Disjoint x.pro x.con} := by
  classical
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [Set.mem_ofPred_eq, Set.disjoint_left]
    intro w h₁ h₂
    simp only [pro_extensions, con_extensions, mem_posExt, mem_negExt] at h₁ h₂
    exact absurd (h₁.symm.trans h₂) (by decide)
  · intro hx
    refine ⟨fun w ↦ if w ∈ x.pro then .true else if w ∈ x.con then .false else .undefined, ?_⟩
    ext w <;> simp only [pro_extensions, con_extensions, mem_posExt, mem_negExt]
    · split_ifs <;> simp_all
    · split_ifs with h₁ h₂
      · exact iff_of_false (by decide) (Set.disjoint_left.1 hx h₁)
      · simp_all
      · simp_all

/-- Three-valued propositions are the disjoint pairs of world-sets. -/
noncomputable def orderIsoDisjoint : (W → Trivalent) ≃o {x : Set W ⊙ Set W | Disjoint x.pro x.con} :=
  (OrderEmbedding.ofMapLEIff extensions fun _ _ ↦ extensions_le_extensions).orderIso.trans
    (Set.orderIsoOfEq _ _ range_extensions)

/-- Kleene's negation of a proposition swaps its extensions. -/
@[simp] theorem extensions_compl (p : W → Trivalent) : extensions pᶜ = (extensions p)ᶜ := by
  ext w <;> simp [posExt, negExt]

/-- Transplication of propositions is Fitting's guard on their extensions. -/
theorem extensions_transplication (π φ : W → Trivalent) :
    extensions (fun w ↦ transplication (π w) (φ w)) = guard (extensions π) (extensions φ) := by
  ext w <;> simp [posExt, negExt, transplication_eq_true_iff, transplication_eq_false_iff]

end Extensions

/-- A proposition is bivalent if it takes no `undefined` value. -/
def IsBivalent (p : W → Trivalent) : Prop :=
  ∀ w, p w = .true ∨ p w = .false

theorem isBivalent_iff_gapExt_eq_empty (p : W → Trivalent) :
    IsBivalent p ↔ gapExt p = ∅ := by
  simp only [IsBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_undefined (p : W → Trivalent) :
    IsBivalent p ↔ ∀ w, p w ≠ .undefined :=
  forall_congr' fun w => by cases p w <;> simp

theorem IsBivalent.ne_undefined {p : W → Trivalent} (h : IsBivalent p) (w : W) :
    p w ≠ .undefined :=
  (isBivalent_iff_forall_ne_undefined p).1 h w

/-! ### Conditional events

A proposition defined where `A` holds and asserting `B` there is the transplication of `B` on `A`,
pointwise: the classical value of `B` on `A` and `undefined` elsewhere. A trivalent proposition is
fixed by where it is defined and where it is true, and every such pair arises, so trivalent
propositions are the conditional events `B | A` of [de-finetti-1936], conditional assertions of a
two-valued content on a two-valued condition; two of them coincide exactly when they have the
same condition and agree on it. -/

section ConditionalEvent

/-- Every trivalent proposition is the conditional event of its truth on its definedness. -/
theorem transplication_definedness_truth (p : W → Trivalent) :
    (fun w ↦ transplication (ofProp (p w ≠ .undefined)) (ofProp (p w = .true))) = p := by
  funext w; cases p w <;> rfl

/-- Two conditional events coincide exactly when they have the same condition and agree on it. -/
theorem transplication_ofProp_eq_iff {A A' B B' : W → Prop} [DecidablePred A]
    [DecidablePred A'] [DecidablePred B] [DecidablePred B'] :
    (fun w ↦ transplication (ofProp (A w)) (ofProp (B w))) =
        (fun w ↦ transplication (ofProp (A' w)) (ofProp (B' w))) ↔
      {w | A w} = {w | A' w} ∧ {w | A w} ∩ {w | B w} = {w | A' w} ∩ {w | B' w} := by
  constructor
  · intro h
    have hgap := congrArg gapExt h
    have hpos := congrArg posExt h
    simp only [Set.ext_iff, mem_gapExt, mem_posExt, transplication_eq_undefined_iff,
      transplication_eq_true_iff, ne_eq, ofProp_eq_true_iff, ofProp_ne_undefined, or_false]
      at hgap hpos
    exact ⟨Set.ext fun w ↦ not_iff_not.1 (hgap w), Set.ext fun w ↦ hpos w⟩
  · rintro ⟨hA, hAB⟩
    funext w
    have h₁ := Set.ext_iff.1 hA w
    have h₂ := Set.ext_iff.1 hAB w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff] at h₁ h₂
    by_cases ha : A w
    · have ha' := h₁.1 ha
      simp only [ofProp, ha, ha', ite_true, transplication_true_left]
      exact ofProp_congr ⟨fun hb ↦ (h₂.1 ⟨ha, hb⟩).2, fun hb ↦ (h₂.2 ⟨ha', hb⟩).2⟩
    · have ha' : ¬ A' w := fun h ↦ ha (h₁.2 h)
      simp only [ofProp, ha, ha', ite_false]; rfl

end ConditionalEvent

/-! ### Extensions under assertion

Asserting a proposition pointwise, `fun w ↦ ofProp (p w = .true)`, keeps its positive extension and
moves its gap into the negative extension. Conjoining it with a two-valued `R` keeps its gap only
where `R` holds. -/

@[simp] theorem posExt_ofProp_eq_true (p : W → Trivalent) :
    posExt (fun w ↦ ofProp (p w = .true)) = posExt p := by
  ext w; simp

@[simp] theorem negExt_ofProp_eq_true (p : W → Trivalent) :
    negExt (fun w ↦ ofProp (p w = .true)) = negExt p ∪ gapExt p := by
  ext w; cases h : p w <;> simp [h]

@[simp] theorem gapExt_ofProp_eq_true (p : W → Trivalent) :
    gapExt (fun w ↦ ofProp (p w = .true)) = ∅ := by
  ext w; simp

@[simp] theorem posExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    posExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ posExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem negExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    negExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w}ᶜ ∪ negExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem gapExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    gapExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ gapExt p := by
  ext w; simp [and_comm]

/-- Composing with a function undefined exactly at `0` preserves the gap. -/
theorem gapExt_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a = .undefined ↔ a = .undefined) (p : W → Trivalent) :
    gapExt (f ∘ p) = gapExt p := by
  ext w; simp [hf]

/-- Composing with a function that is never `0` leaves no gap. -/
theorem isBivalent_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a ≠ .undefined) (p : W → Trivalent) :
    IsBivalent (f ∘ p) :=
  (isBivalent_iff_forall_ne_undefined _).2 fun _ ↦ hf _

theorem isBivalent_ofProp_eq_true (p : W → Trivalent) : IsBivalent fun w ↦ ofProp (p w = .true) :=
  fun w ↦ by by_cases h : p w = .true <;> simp [h]

/-! ### Quantifiers

Like the binary connectives, the trivalent quantifiers come in rival families that share one
truth rule and differ only in where undefinedness projects, which `forallWith` and
`existsWith` make definitional: a family is fixed by its definedness condition. The Weak
Kleene quantifiers are undefined as soon as any instance is; the Strong Kleene quantifiers
are defined whenever the instances settle the value, the indexed `⊓` and `⊔`; and the
quantifiers of [haug-2014], adopted by [coppock-beaver-2015] and [cooper-2023], are undefined
only when every instance is, so that a quantified presupposition projects existentially.
Restricted to a pair of instances the families are the binary connectives — Weak Kleene
`meetWeak`, Strong Kleene `⊓`, and, for Haug's quantifier, Belnap's skip-undefined
`meetBelnap` (`forallHaug_pair`). Middle Kleene reads its operands left to right, so no
quantifier restricts to it on a pair of instances. Peters-Kleene deployment, which derives Middle
Kleene from the classical connectives, takes a quantifier's instances as a single argument, and
so gives the Strong Kleene quantifiers ([george-2014] §4.1). -/

open Classical in
/-- `forallWith D p` is the universal quantifier undefined unless `D` holds, and otherwise false
exactly when some instance is. All the families share this truth rule
(`forallWith_eq_forallWith_of_defined`). -/
noncomputable def forallWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  if D then if ∃ i, p i = .false then .false else .true else .undefined

/-- `existsWith D p` is the existential quantifier of the family whose definedness condition
is `D`, the dual of `forallWith`. -/
noncomputable def existsWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  (forallWith D fun i ↦ (p i)ᶜ)ᶜ

section WithFamilies

variable {ι : Sort*} {D D' : Prop} {p : ι → Trivalent}

theorem forallWith_eq_undefined_iff : forallWith D p = .undefined ↔ ¬D := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_false_iff : forallWith D p = .false ↔ D ∧ ∃ i, p i = .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_true_iff : forallWith D p = .true ↔ D ∧ ∀ i, p i ≠ .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem existsWith_eq_undefined_iff : existsWith D p = .undefined ↔ ¬D := by
  simp [existsWith, forallWith_eq_undefined_iff]

theorem existsWith_eq_true_iff : existsWith D p = .true ↔ D ∧ ∃ i, p i = .true := by
  simp [existsWith, forallWith_eq_false_iff]

theorem existsWith_eq_false_iff : existsWith D p = .false ↔ D ∧ ∀ i, p i ≠ .true := by
  simp [existsWith, forallWith_eq_true_iff]

theorem forallWith_eq_forallWith_of_defined (hD : D) (hD' : D') :
    forallWith D p = forallWith D' p := by
  unfold forallWith
  rw [ite_eq_left hD, ite_eq_left hD']

theorem forallWith_congr (h : D ↔ D') : forallWith D p = forallWith D' p :=
  eq_of_eq_undefined_iff_of_eq_true_iff
    (by rw [forallWith_eq_undefined_iff, forallWith_eq_undefined_iff, h])
    (by rw [forallWith_eq_true_iff, forallWith_eq_true_iff, h])

theorem existsWith_congr (h : D ↔ D') : existsWith D p = existsWith D' p :=
  congrArg compl (forallWith_congr h)

end WithFamilies

/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith (∀ i, p i ≠ .undefined) p

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith (∀ i, p i ≠ .undefined) p

section WeakQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallWeak_eq_undefined_iff : forallWeak p = .undefined ↔ ∃ i, p i = .undefined := by
  rw [forallWeak, forallWith_eq_undefined_iff, not_forall]
  simp

@[simp] theorem forallWeak_eq_true_iff : forallWeak p = .true ↔ ∀ i, p i = .true := by
  rw [forallWeak, forallWith_eq_true_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hf i)
    · exact absurd h (hd i)
    · rfl
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallWeak_eq_false_iff :
    forallWeak p = .false ↔ (∀ i, p i ≠ .undefined) ∧ ∃ i, p i = .false := by
  rw [forallWeak, forallWith_eq_false_iff]

@[simp] theorem existsWeak_eq_undefined_iff : existsWeak p = .undefined ↔ ∃ i, p i = .undefined := by
  rw [existsWeak, existsWith_eq_undefined_iff, not_forall]
  simp

@[simp] theorem existsWeak_eq_true_iff :
    existsWeak p = .true ↔ (∀ i, p i ≠ .undefined) ∧ ∃ i, p i = .true := by
  rw [existsWeak, existsWith_eq_true_iff]

@[simp] theorem existsWeak_eq_false_iff : existsWeak p = .false ↔ ∀ i, p i = .false := by
  rw [existsWeak, existsWith_eq_false_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · rfl
    · exact absurd h (hd i)
    · exact absurd h (hf i)
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

end WeakQuantifiers

/-- The Strong Kleene universal quantifier is the indexed `⊓`, false when any instance is, true
when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith ((∃ i, p i = .false) ∨ ∀ i, p i = .true) p

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed
`⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith ((∃ i, p i = .true) ∨ ∀ i, p i = .false) p

section StrongQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallStrong_eq_false_iff : forallStrong p = .false ↔ ∃ i, p i = .false := by
  rw [forallStrong, forallWith_eq_false_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem forallStrong_eq_true_iff : forallStrong p = .true ↔ ∀ i, p i = .true := by
  rw [forallStrong, forallWith_eq_true_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallStrong_eq_undefined_iff :
    forallStrong p = .undefined ↔ (∀ i, p i ≠ .false) ∧ ∃ i, p i = .undefined := by
  rw [forallStrong, forallWith_eq_undefined_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

theorem forallStrong_ne_undefined_iff : forallStrong p ≠ .undefined ↔ (∃ i, p i = .false) ∨ ∀ i, p i ≠ .undefined := by
  rw [ne_eq, forallStrong_eq_undefined_iff, not_and_or, not_forall_not, not_exists]

@[simp] theorem existsStrong_eq_true_iff : existsStrong p = .true ↔ ∃ i, p i = .true := by
  rw [existsStrong, existsWith_eq_true_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem existsStrong_eq_false_iff : existsStrong p = .false ↔ ∀ i, p i = .false := by
  rw [existsStrong, existsWith_eq_false_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem existsStrong_eq_undefined_iff :
    existsStrong p = .undefined ↔ (∀ i, p i ≠ .true) ∧ ∃ i, p i = .undefined := by
  rw [existsStrong, existsWith_eq_undefined_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

theorem existsStrong_ne_undefined_iff : existsStrong p ≠ .undefined ↔ (∃ i, p i = .true) ∨ ∀ i, p i ≠ .undefined := by
  rw [ne_eq, existsStrong_eq_undefined_iff, not_and_or, not_forall_not, not_exists]

/-- The Strong Kleene quantifiers are dual under Kleene's negation. -/
theorem compl_forallStrong : (forallStrong p)ᶜ = existsStrong fun i ↦ (p i)ᶜ :=
  eq_of_eq_true_iff_of_eq_false_iff (by simp) (by simp)

end StrongQuantifiers

/-- Haug's universal quantifier skips undefined instances — undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → Trivalent) : Trivalent :=
  forallWith (∃ w, p w ≠ .undefined) p

/-- The dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → Trivalent) : Trivalent :=
  existsWith (∃ w, p w ≠ .undefined) p

section HaugQuantifiers

variable {p : W → Trivalent}

@[simp] theorem forallHaug_eq_undefined_iff : forallHaug p = .undefined ↔ ∀ w, p w = .undefined := by
  rw [forallHaug, forallWith_eq_undefined_iff, not_exists]
  simp

@[simp] theorem forallHaug_eq_false_iff : forallHaug p = .false ↔ ∃ w, p w = .false := by
  rw [forallHaug, forallWith_eq_false_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem forallHaug_eq_true_iff :
    forallHaug p = .true ↔ (∃ w, p w ≠ .undefined) ∧ ∀ w, p w ≠ .false := by
  rw [forallHaug, forallWith_eq_true_iff]

@[simp] theorem existsHaug_eq_undefined_iff : existsHaug p = .undefined ↔ ∀ w, p w = .undefined := by
  rw [existsHaug, existsWith_eq_undefined_iff, not_exists]
  simp

@[simp] theorem existsHaug_eq_true_iff : existsHaug p = .true ↔ ∃ w, p w = .true := by
  rw [existsHaug, existsWith_eq_true_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem existsHaug_eq_false_iff :
    existsHaug p = .false ↔ (∃ w, p w ≠ .undefined) ∧ ∀ w, p w ≠ .true := by
  rw [existsHaug, existsWith_eq_false_iff]

end HaugQuantifiers

/-! ### Each family restricted to a pair is its binary connective

One lemma carries the correspondence: the gap-policy quantifier at a pair of instances is
the gap-policy connective at the matching policy (`forallWith_pair`), and each family's
pair lemma instantiates it. -/

section Pairs

variable (a b : Trivalent)

theorem forallWith_pair {D : Prop} [Decidable D] :
    forallWith D (fun i : Bool => bif i then a else b) = meetWith D a b := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · rw [forallWith_eq_undefined_iff, meetWith_eq_undefined_iff]
  · rw [forallWith_eq_true_iff, meetWith_eq_true_iff, Bool.forall_bool]
    exact and_congr_right fun _ => and_comm

theorem existsWith_pair {D : Prop} [Decidable D] :
    existsWith D (fun i : Bool => bif i then a else b) = joinWith D a b := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · rw [existsWith_eq_undefined_iff, joinWith_eq_undefined_iff]
  · rw [existsWith_eq_true_iff, joinWith_eq_true_iff, Bool.exists_bool]
    exact and_congr_right fun _ => or_comm

theorem forallWeak_pair : forallWeak (fun i : Bool => bif i then a else b) = meetWeak a b :=
  (forallWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((forallWith_pair a b).trans (meetWeak_eq_meetWith a b).symm)

theorem existsWeak_pair : existsWeak (fun i : Bool => bif i then a else b) = joinWeak a b :=
  (existsWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((existsWith_pair a b).trans (joinWeak_eq_joinWith a b).symm)

theorem forallStrong_pair :
    forallStrong (fun i : Bool => bif i then a else b) = a ⊓ b :=
  (forallWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((forallWith_pair a b).trans (inf_eq_meetWith a b).symm)

theorem existsStrong_pair :
    existsStrong (fun i : Bool => bif i then a else b) = a ⊔ b :=
  (existsWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((existsWith_pair a b).trans (sup_eq_joinWith a b).symm)

theorem forallHaug_pair :
    forallHaug (fun i : Bool => bif i then a else b) = meetBelnap a b :=
  (forallWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((forallWith_pair a b).trans (meetBelnap_eq_meetWith a b).symm)

theorem existsHaug_pair :
    existsHaug (fun i : Bool => bif i then a else b) = joinBelnap a b :=
  (existsWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((existsWith_pair a b).trans (joinBelnap_eq_joinWith a b).symm)

end Pairs

theorem existsHaug_presuppose_ne_false (p : W → Trivalent) :
    existsHaug (fun w => (p w ⊔ .undefined)) ≠ .false := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix) lets a presupposition under the
existential project as an existentially quantified presupposition, over bivalent `φ` and
`ψ`. -/
theorem existsHaug_meetWeak_presuppose {φ ψ : W → Trivalent} (hφ : IsBivalent φ)
    (hψ : IsBivalent ψ) :
    existsHaug (fun w => meetWeak (φ w ⊔ .undefined) (ψ w)) =
      meetWeak (existsHaug fun w => (φ w ⊔ .undefined))
        (existsHaug fun w => meetWeak (φ w) (ψ w)) := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · simp only [existsHaug_eq_undefined_iff, meetWeak_eq_undefined_iff, sup_undefined_eq_undefined_iff, hφ.ne_undefined,
      hψ.ne_undefined, or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h w => (h w).elim⟩
  · simp only [existsHaug_eq_true_iff, meetWeak_eq_true_iff, sup_undefined_eq_true_iff]
    exact ⟨fun ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, fun h => h.2⟩

end Trivalent
