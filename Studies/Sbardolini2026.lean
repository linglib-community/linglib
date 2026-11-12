module

public import Linglib.Data.Examples.Sbardolini2026
public import Linglib.Semantics.Attitudes.Preference.BestWorlds
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Reference.Iota

/-!
# Sbardolini (2026): Negative polarity, presuppositions, and the Harmony hypothesis

Sbardolini takes *any* to be disharmonious: `any x: F x` is true when everything is `F` and false
when nothing is. Truth preservation closed under contraposition then [relates any two instances of
a predicate](##Sbardolini2026.triviality), as Prior's *tonk* does, and English keeps its logic
non-trivial by never committing a speaker to *any*: an occurrence is grammatical only if its
environment is not [Strawson upward monotone](##Sbardolini2026.IsSUM). A [non-constant Strawson
downward-entailing environment never is](##Sbardolini2026.not_isSUM_of_isStrawsonDE); unlike the
condition of von Fintel and Gajewski, this one [admits the restrictor of
*most*](##Sbardolini2026.restrictor_most), and, against Ladusaw, it [excludes
tautologies](##Sbardolini2026.tautology).

## Implementation notes

* An environment is the function of the slot `F` in the paper's table of predictions, over sets of
  individuals or of worlds, which entail one another by inclusion. `IsSUM` takes at least one
  premise; with none, the restrictor of the singular definite would fail it.

## TODO

* Polar questions, imperatives, generics, plural definites, *both*, and the scope of *too*.

## References

* [sbardolini-2026]
* [prior-1960]
* [von-fintel-1999]
* [gajewski-2011]
* [bylinina-nouwen-2018]
* [ladusaw-1979]
-/

@[expose] public section

namespace Sbardolini2026

open Presupposition Trivalent Quantifier PolarityItem

/-! ### Disharmony -/

section Disharmony

variable {E W : Type*} (F : E → W → Prop)

open Classical in
/-- Disharmonious *any*: `any x: F x` is true where everything is `F`, false where nothing is,
and neither where some things are `F` and others are not. -/
noncomputable def any : W → Trivalent := fun w ↦
  if ∀ x, F x w then .true else if ∀ x, ¬ F x w then .false else .undefined

open Classical in
/-- The sentence that `x` is `F`. -/
noncomputable def atom (x : E) : W → Trivalent := fun w ↦ .ofProp (F x w)

-- (3a): *Mary drank anything* entails *Mary drank the Chianti*.
theorem posExt_any_subset (c : E) : posExt (any F) ⊆ posExt (atom F c) := fun w hw ↦ by
  simp only [mem_posExt, any, atom] at hw ⊢
  split_ifs at hw
  simp_all

-- (3b): *Mary didn't drink anything* entails *Mary didn't drink the Barolo*.
theorem posExt_compl_any_subset (b : E) : posExt (any F)ᶜ ⊆ posExt (atom F b)ᶜ := fun w hw ↦ by
  simp only [mem_posExt, Pi.compl_apply, compl_eq_true_iff, any, atom] at hw ⊢
  split_ifs at hw
  simp_all

-- (3c), the contrapositive of (3b), is not truth preserving: *Mary drank the Barolo* does not
-- entail *Mary drank anything* where she did not drink the Chianti.
theorem not_posExt_atom_subset {b c : E} {w : W} (hb : F b w) (hc : ¬ F c w) :
    ¬ posExt (atom F b) ⊆ posExt (any F) := fun h ↦ by
  have := h (show w ∈ posExt (atom F b) by simp [atom, hb])
  simp only [mem_posExt, any] at this
  split_ifs at this
  simp_all

/-- Any consequence relation that contains truth preservation, validates contraposition and is
transitive relates every instance of a predicate to every other, as Prior's *tonk* relates every
sentence to every other ([prior-1960]): *any* trivializes classical consequence. -/
theorem triviality (R : (W → Trivalent) → (W → Trivalent) → Prop)
    (hR : ∀ ⦃φ ψ⦄, posExt φ ⊆ posExt ψ → R φ ψ) (hcon : ∀ ⦃φ ψ⦄, R φ ψ → R ψᶜ φᶜ)
    (htrans : ∀ ⦃φ ψ χ⦄, R φ ψ → R ψ χ → R φ χ) (b c : E) : R (atom F b) (atom F c) := by
  have hcc (φ : W → Trivalent) : φᶜᶜ = φ := funext fun w ↦ Trivalent.compl_compl (φ w)
  have h := hcon (hR (posExt_compl_any_subset F b))
  rw [hcc, hcc] at h
  exact htrans h (hR (posExt_any_subset F c))

end Disharmony

/-! ### The licensing condition -/

section Licensing

variable {α W : Type*}

/-- An environment is Strawson upward monotone (SUM) when `X₁, …, Xₙ ⊨ Y` makes
`f X₁ ∧ … ∧ f Xₙ`, together with the presupposition of `f Y`, entail `f Y` ([sbardolini-2026],
§5). *Any* is grammatical only in an environment that is not SUM. -/
def IsSUM [SemilatticeInf α] (f : α → W → Trivalent) : Prop :=
  ∀ (s : Finset α) (hs : s.Nonempty) (y : α), s.inf' hs id ≤ y →
    ∀ w, (∀ x ∈ s, f x w = .true) → f y w ≠ .undefined → f y w = .true

theorem IsSUM.isStrawsonUE [Lattice α] {f : α → W → Trivalent} (h : IsSUM f) :
    IsStrawsonUE f := by
  classical
  exact fun p q hpq w hp hq ↦
    h {p} (Finset.singleton_nonempty p) q (by simpa using hpq) w (by simpa using hp) hq

open Classical in
-- Without presuppositions, an environment is SUM when it is monotone and closed under meets,
-- the upward monotonicity of [sbardolini-2026]'s §3 for any number of premises.
theorem isSUM_ofProp_iff [Lattice α] {g : α → W → Prop} :
    IsSUM (fun x w ↦ Trivalent.ofProp (g x w)) ↔
      Monotone g ∧ ∀ x y w, g x w → g y w → g (x ⊓ y) w := by
  refine ⟨fun h ↦ ⟨isStrawsonUE_ofProp_iff.1 h.isStrawsonUE, fun x y w hx hy ↦ ?_⟩,
    fun ⟨hm, hi⟩ s hs y hy w hs' _ ↦ ?_⟩
  · simpa using h {x, y} (by simp) (x ⊓ y) (by simp [Finset.inf'_insert]) w
      (by simp [hx, hy]) (by simp)
  · simp only [Trivalent.ofProp_eq_true_iff] at hs' ⊢
    exact hm hy w (Finset.inf'_induction hs id (p := (g · w)) (fun a ha b hb ↦ hi a b w ha hb) hs')

/-- A non-constant Strawson downward-entailing environment is not SUM ([sbardolini-2026]'s
footnote 7), so *any* is grammatical under negation and in the restrictor of *every*. -/
theorem not_isSUM_of_isStrawsonDE [Lattice α] {f : α → W → Trivalent} (hd : IsStrawsonDE f)
    {p q : α} (hpq : p ≤ q) {w : W} (hp : f p w ≠ .undefined) (hq : f q w ≠ .undefined)
    (hne : f p w ≠ f q w) : ¬ IsSUM f := fun h ↦
  hne (isStrawsonUE_and_isStrawsonDE_iff.1 ⟨h.isStrawsonUE, hd⟩ hpq w hp hq)

end Licensing

/-! ### Environments -/

section Environments

variable {E W : Type*}

open Classical in
/-- The scope of a determiner over the restrictor `A`. -/
noncomputable def scope (d : Det E) (A : Set E) : Set E → W → Trivalent :=
  fun F _ ↦ .ofProp (d A F)

open Classical in
/-- The restrictor of a determiner over the scope `B`. -/
noncomputable def restrictor (d : Det E) (B : Set E) : Set E → W → Trivalent :=
  fun F _ ↦ .ofProp (d F B)

open Classical in
/-- A modal as a determiner over the worlds accessible by `R`: `□` is `every` over them, `◇`
`some`. -/
noncomputable def modal (d : Det W) (R : SetRel W W) : Set W → W → Trivalent :=
  fun p w ↦ .ofProp (d {v | (w, v) ∈ R} p)

/-- The singular definite presupposes that its restrictor `F` has exactly one member and says
that it is in its scope `B`. -/
noncomputable def definite (F B : Set E) : W → Trivalent :=
  presupOfReferent (fun _ ↦ iota F) fun e _ ↦ e ∈ B

theorem isSUM_scope_of_filtrating {d : Det E} (hd : d.Filtrating) (A : Set E) :
    IsSUM (scope (W := W) d A) :=
  isSUM_ofProp_iff.2 ⟨fun _ _ h _ ↦ hd.1 A h, fun _ _ _ ↦ hd.2 A _ _⟩

theorem isSUM_modal_of_filtrating {d : Det W} (hd : d.Filtrating) (R : SetRel W W) :
    IsSUM (modal d R) :=
  isSUM_ofProp_iff.2 ⟨fun _ _ h _ ↦ hd.1 _ h, fun _ _ _ ↦ hd.2 _ _ _⟩

end Environments

/-! ### The table of predictions -/

section Table

variable {E W : Type*}

open Classical in
-- *\*Mary ate any pizza*: predication is SUM.
theorem isSUM_predication (x : E) : IsSUM fun F : Set E ↦ fun _ : W ↦ Trivalent.ofProp (x ∈ F) :=
  isSUM_ofProp_iff.2 ⟨fun _ _ h _ hx ↦ h hx, fun _ _ _ hF hG ↦ ⟨hF, hG⟩⟩

open Classical in
-- *Mary didn't eat any pizza*: negation is not SUM.
theorem not_isSUM_negation [Nonempty W] (x : E) :
    ¬ IsSUM fun F : Set E ↦ fun _ : W ↦ Trivalent.ofProp (x ∉ F) :=
  not_isSUM_of_isStrawsonDE (.of_antitone (a := fun F _ ↦ x ∉ F)
    (fun _ _ h _ hG hF ↦ hG (Set.mem_of_mem_of_subset hF h)) fun _ _ _ ↦ by simp)
    (Set.empty_subset {x}) (w := Classical.arbitrary W) (by simp) (by simp) (by simp)

-- *\*Everyone who left ate any pizza* and *\*Mary must drink anything*: the scope of *every*
-- and necessity are SUM.
theorem isSUM_every (A : Set E) (R : SetRel W W) :
    IsSUM (scope (W := W) Det.every A) ∧ IsSUM (modal Det.every R) :=
  ⟨isSUM_scope_of_filtrating Det.filtrating_every A,
    isSUM_modal_of_filtrating Det.filtrating_every R⟩

-- *Everyone who ate any pizza left*: the restrictor of *every* is not SUM.
theorem not_isSUM_restrictor_every [Nonempty W] {x : E} {B : Set E} (hx : x ∉ B) :
    ¬ IsSUM (restrictor (W := W) Det.every B) :=
  not_isSUM_of_isStrawsonDE (isStrawsonDE_ofProp_iff.2 fun _ _ h _ hG ↦ h.trans hG)
    (Set.empty_subset {x}) (w := Classical.arbitrary W) (by simp [restrictor])
    (by simp [restrictor]) (by simp [restrictor, Det.every, hx])

-- *\*Someone who left ate any pizza* has an environment SUM for one premise.
theorem isStrawsonUE_scope_some (A : Set E) : IsStrawsonUE (scope (W := W) Det.some A) :=
  isStrawsonUE_ofProp_iff.2 fun _ _ h _ ↦ Det.monotone_some A h

-- With two premises, the scope of *some* over a restrictor with two members is not SUM.
theorem not_isSUM_scope_some [Nonempty W] {A : Set E} {a b : E} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) : ¬ IsSUM (scope (W := W) Det.some A) := fun h ↦ by
  classical
  have := h {{a}, {b}} (by simp) ∅ (by simp [Finset.inf'_insert, hab]) (Classical.arbitrary W)
  simp [scope, Det.some, ha, hb] at this

-- With two premises, the restrictor of *some* over a scope with two members is not SUM.
theorem not_isSUM_restrictor_some [Nonempty W] {B : Set E} {a b : E} (ha : a ∈ B) (hb : b ∈ B)
    (hab : a ≠ b) : ¬ IsSUM (restrictor (W := W) Det.some B) := fun h ↦ by
  classical
  have := h {{a}, {b}} (by simp) ∅ (by simp [Finset.inf'_insert, hab]) (Classical.arbitrary W)
  simp [restrictor, Det.some, ha, hb] at this

-- With two premises, the scope of *most* over three professors is not SUM: *most* of them are
-- in `{0, 1}` and *most* in `{1, 2}`, but only one is in both.
theorem not_isSUM_scope_most [Nonempty W] :
    ¬ IsSUM (scope (W := W) Det.most (Set.univ : Set (Fin 3))) := fun h ↦ by
  classical
  have := h {{x | x ≠ 2}, {x | x ≠ 0}} (by simp) {x | x = 1}
    (by intro x; simp [Finset.inf'_insert]; omega) (Classical.arbitrary W)
    (by simp [scope]; decide) (by simp [scope])
  simp [scope] at this
  revert this; decide

-- *Most professors who ate any pizza left*: the restrictor of *most* is not SUM.
theorem not_isSUM_restrictor_most [Nonempty W] :
    ¬ ∀ B : Set (Fin 3), IsSUM (restrictor (W := W) Det.most B) := fun h ↦
  Det.not_restrictorMonotone_most fun B _ _ hFG hF ↦
    isStrawsonUE_ofProp_iff.1 (h B).isStrawsonUE hFG (Classical.arbitrary W) hF

-- *If Mary drank anything, she got sick*: the antecedent of a conditional is not SUM.
theorem not_isSUM_antecedent :
    ¬ IsSUM fun p : Set Bool ↦
      Conditional.horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Bool)) p {Bool.true} :=
  fun h ↦ Conditional.not_isStrawsonUE_horizonCounterfactual h.isStrawsonUE

-- *\*If Mary got sick, she drank anything*: the consequent of a conditional is SUM.
theorem isSUM_consequent {I : Type*} (horizon : I → Set W) (p : Set W) :
    IsSUM (Conditional.horizonCounterfactual horizon p) := by
  intro s hs y hy i hall _
  simp only [Conditional.horizonCounterfactual_eq_true_iff] at hall ⊢
  exact ⟨(hall _ hs.choose_spec).1, (Finset.inf'_induction hs id (p := (horizon i ∩ p ⊆ ·))
    (fun _ ha _ hb ↦ Set.subset_inter ha hb) fun x hx ↦ (hall x hx).2).trans hy⟩

-- *\*Zero or more students read anything* and *\*At most one and at least three students read
-- anything*: a tautology and a contradiction are SUM.
theorem isSUM_tautology_contradiction (A : Set E) :
    IsSUM (scope (W := W) (Det.atLeast 0) A) ∧
      IsSUM (scope (W := W) (Det.atMost 1 ⊓ Det.atLeast 3) A) :=
  ⟨isSUM_ofProp_iff.2 ⟨fun _ _ _ _ _ ↦ Nat.zero_le _, fun _ _ _ _ _ ↦ Nat.zero_le _⟩,
    isSUM_ofProp_iff.2 ⟨fun _ _ _ _ h ↦ absurd (h.2.trans h.1) (by norm_num),
      fun _ _ _ h ↦ absurd (h.2.trans h.1) (by norm_num)⟩⟩

-- *\*The student with any books sold them* has an environment SUM for one premise: *the novel
-- was long* and *there was exactly one book* entail *the book was long* (19).
theorem isStrawsonUE_definite_restrictor (B : Set E) :
    IsStrawsonUE fun F ↦ definite (W := W) F B := by
  intro F G hFG w hF hG
  obtain ⟨e, he, heB⟩ := presupOfReferent_eq_true_iff.1 hF
  obtain ⟨e', he'⟩ := Part.dom_iff_mem.1 (not_not.1 (presupOfReferent_eq_undefined_iff.not.1 hG))
  obtain rfl := (mem_iota.1 he').2 e (hFG (mem_iota.1 he).1)
  exact presupOfReferent_eq_true_iff.2 ⟨_, he', heB⟩

-- With two premises, the restrictor of the singular definite is not SUM: *the novel* and *the
-- cookbook* can be long while *the poem* is not, though nothing is both a novel and a cookbook.
theorem not_isSUM_definite_restrictor [Nonempty W] {B : Set E} {a b c : E} (ha : a ∈ B)
    (hb : b ∈ B) (hc : c ∉ B) (hab : a ≠ b) : ¬ IsSUM fun F ↦ definite (W := W) F B := fun h ↦ by
  classical
  have := h {{a}, {b}} (by simp) {c} (by simp [Finset.inf'_insert, hab]) (Classical.arbitrary W)
  simp [definite, ha, hb, hc] at this

-- *\*The student sold any books*: the scope of the singular definite is SUM.
theorem isSUM_definite_scope (A : Set E) : IsSUM (definite (W := W) A) := by
  intro s hs y hy w hall hdef
  obtain ⟨e, he⟩ :=
    Part.dom_iff_mem.1 (not_not.1 (presupOfReferent_eq_undefined_iff.not.1 hdef))
  refine presupOfReferent_eq_true_iff.2 ⟨e, he, hy (Finset.inf'_induction hs id (p := (e ∈ ·))
    (fun _ ha _ hb ↦ ⟨ha, hb⟩) fun x hx ↦ ?_)⟩
  obtain ⟨e', he', hx'⟩ := presupOfReferent_eq_true_iff.1 (hall x hx)
  exact Part.mem_unique he he' ▸ hx'

-- *\*It is Mary who sold any books*: the cleft, which presupposes that exactly one thing is `F`
-- and says that it is `x`, is SUM, being the singular definite with scope `{x}` (20a).
theorem isSUM_cleft (x : E) : IsSUM fun F ↦ definite (W := W) F {x} := by
  intro s hs y hy w hall hdef
  have hx : ∀ F ∈ s, x ∈ F := fun F hF ↦ by
    obtain ⟨e, he, rfl⟩ := presupOfReferent_eq_true_iff.1 (hall F hF)
    exact (mem_iota.1 he).1
  obtain ⟨e, he⟩ :=
    Part.dom_iff_mem.1 (not_not.1 (presupOfReferent_eq_undefined_iff.not.1 hdef))
  exact presupOfReferent_eq_true_iff.2 ⟨e, he, ((mem_iota.1 he).2 x
    (hy (Finset.inf'_induction hs id (p := (x ∈ ·)) (fun _ ha _ hb ↦ ⟨ha, hb⟩) hx))).symm⟩

-- *Only Mary sold any books*: *only x* is not SUM, since *only John saw a small bird* and *John
-- saw a bird* do not entail *only John saw a bird* (22a).
theorem not_isSUM_only [Nonempty W] {x y : E} (hxy : x ≠ y) :
    ¬ IsSUM fun F : Set E ↦ Focus.only (· = ·) Set.univ (fun j ↦ {_w : W | j ∈ F}) x := fun h ↦
  Presupposition.not_isStrawsonUE (p := {x}) (q := {x, y}) (w := Classical.arbitrary W)
    (by simp) (by simp [Focus.only]) (by simp [Focus.only, hxy]) h.isStrawsonUE

-- *John is sorry that Mary sold any books*: *sorry that* is not SUM, since *sorry that Robin
-- bought a Civic* does not Strawson-entail *sorry that Robin bought a car* (22c).
theorem not_isSUM_regret :
    ¬ IsSUM (Desire.BestWorlds.regret (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ)
      (fun _ ↦ {(· = 1)})) :=
  fun h ↦ Desire.BestWorlds.not_isStrawsonUE_regret h.isStrawsonUE

end Table

/-! ### Rival conditions -/

section Rivals

variable {E W : Type*}

/-- *Most professors who understand anything are very appreciative* (7c): the restrictor of
*most* is neither Strawson downward entailing, which von Fintel's condition and Gajewski's ask
([von-fintel-1999], [gajewski-2011]), nor SUM, so the Harmony hypothesis licenses *any* there and
they do not. -/
theorem restrictor_most [Nonempty W] :
    ¬ (∀ B : Set (Fin 3), IsStrawsonDE (restrictor (W := W) Det.most B)) ∧
      ¬ ∀ B : Set (Fin 3), IsSUM (restrictor (W := W) Det.most B) :=
  ⟨fun h ↦ Det.not_restrictorAntitone_most fun B _ _ hFG hG ↦
    isStrawsonDE_ofProp_iff.1 (h B) hFG (Classical.arbitrary W) hG, not_isSUM_restrictor_most⟩

/-- *\*Zero or more students read anything* (12a): a tautology is downward entailing, so
Ladusaw's condition licenses *any* in it ([ladusaw-1979]), but it carries no strength of negation
and is SUM, so neither von Fintel's condition nor the Harmony hypothesis does. -/
theorem tautology {E : Type} (A : Set E) :
    Antitone (Det.atLeast 0 A) ∧ ¬ (Licenser.ofOperator (Det.atLeast 0 A)).Carries .weak ∧
      IsSUM (scope (W := W) (Det.atLeast 0) A) :=
  ⟨fun _ _ _ _ ↦ Nat.zero_le _,
    fun h ↦ (Licenser.carries_ofOperator_iff.1 h).2 fun _ _ _ _ ↦ Nat.zero_le _,
    (isSUM_tautology_contradiction A).1⟩

-- *\*Mary must drink anything*: necessity carries no strength of negation, being upward
-- entailing, and is SUM, so von Fintel's condition and the Harmony hypothesis alike exclude *any*
-- under it.
theorem necessity {W : Type} (R : SetRel W W) :
    ¬ (Licenser.modal LicensingContext.necessityFamily).Carries .weak ∧
      IsSUM (modal Det.every R) :=
  ⟨fun h ↦ h.2 LicensingContext.isStrawsonUE_necessityFamily,
    isSUM_modal_of_filtrating Det.filtrating_every R⟩

end Rivals

/-! ### Possibility modals -/

section Possibility

variable {W : Type*}

-- *Mary might drink anything*: `◇` is `some` over the accessible worlds, upward entailing for
-- one premise as the scope of *some* is, so the n = 1 condition of footnotes 6 and 7 predicts it
-- ungrammatical.
theorem isStrawsonUE_modal_some (R : SetRel W W) : IsStrawsonUE (modal Det.some R) :=
  isStrawsonUE_ofProp_iff.2 fun _ _ h _ ↦ Det.monotone_some _ h

-- With two premises, `◇` over two accessible worlds is not SUM, as (11a) shows.
theorem not_isSUM_modal_some {R : SetRel W W} {w u v : W} (hu : (w, u) ∈ R) (hv : (w, v) ∈ R)
    (huv : u ≠ v) : ¬ IsSUM (modal Det.some R) := fun h ↦ by
  classical
  have := h {{u}, {v}} (by simp) ∅ (by simp [Finset.inf'_insert, huv]) w
  simp [modal, Det.some, hu, hv] at this

end Possibility

end Sbardolini2026
