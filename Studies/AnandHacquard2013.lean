module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Data.Examples.AnandHacquard2013
public import Mathlib.Data.Set.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Anand & Hacquard 2013: epistemics and attitudes

Epistemic modals are acceptable in the complements of attitudes of acceptance (*think*, *say*,
*realize*), unacceptable under desideratives and directives, and acceptable under emotive
doxastics (*hope*, *fear*) and dubitatives (*doubt*) with possibility but not necessity force, in
seven-point acceptability surveys of French, Italian, and Spanish. The account combines Yalcin's
information-state semantics, on which an epistemic quantifies over a state `S` anaphoric to the
embedding attitude and presupposes `S ≠ ∅`, with Bolinger's split of attitudes: representational
attitudes pass their doxastic state as `S`; non-representational ones set `S = ∅` and combine
with their complement by Villalta's comparison against the Heimian alternative `¬φ`, so an
embedded epistemic is never defined. Emotive doxastics and dubitatives are hybrids — a doxastic
possibility assertion, a comparison of the complement's verifiers with its falsifiers, and an
uncertainty presupposition demanding both — and the doxastic assertion of an embedded necessity
modal contradicts that presupposition, while an embedded possibility modal contributes nothing
new. Italian *pensare* selects the subjunctive yet licenses epistemics, so subjunctive is an
imperfect correlate.

## Main definitions

* `SProp`: a complement relative to an information state `S`, with `might`, `must`, `ofSet`.
* `Better`: Villalta's lift of an ordering to propositions; `verifiers` the sub-states settled
  on a complement.
* `Licensed`: whether some context makes an embedded epistemic defined and true.

## References

* [anand-hacquard-2013]
* [yalcin-2007] — the information-state parameter, and the *suppose* sentences that (23) adapts
* [veltman-1996], [hacquard-2006], [hacquard-2010] — anaphoric modal bases
* [bolinger-1968] — representational attitudes
* [villalta-2008] — comparative semantics for subjunctive-selecting attitudes
* [heim-1992] — the alternative set `{φ, ¬φ}`
* [geurts-2005] — the non-triviality presupposition of modals
* [scheffler-2008] — the doxastic component of *hope*
* [falaus-2010] — Romanian *vreun* under *want* and *hope*
-/

@[expose] public section

namespace AnandHacquard2013

variable {W : Type*}

/-! ### Complements relative to an information state -/

/-- A complement evaluated against an information state `S` — Yalcin's parameter — as a
trivalent proposition for each `S`. -/
abbrev SProp (W : Type*) := Set W → W → SignType

open Classical in
/-- An unmodalized complement ignores the information state. -/
noncomputable def ofSet (p : Set W) : SProp W := fun _ w ↦ SignType.ofProp (w ∈ p)

open Classical in
/-- Epistemic possibility (37a) presupposes `S ≠ ∅` and is true iff `S` contains a
`p`-world. -/
noncomputable def might (p : Set W) : SProp W :=
  fun S ↦ {_w | S.Nonempty}.indicator fun _ ↦ SignType.ofProp (S ∩ p).Nonempty

open Classical in
/-- Epistemic necessity (37b) presupposes `S ≠ ∅` and is true iff `S ⊆ p`. -/
noncomputable def must (p : Set W) : SProp W :=
  fun S ↦ {_w | S.Nonempty}.indicator fun _ ↦ SignType.ofProp (S ⊆ p)

/-- Negation of a complement, keeping its presupposition. -/
def neg (φ : SProp W) : SProp W := fun S ↦ -φ S

/-- Conjunction of complements, defined where both are (Weak Kleene). -/
def conj (φ ψ : SProp W) : SProp W := fun S w ↦ (φ S w).meetWeak (ψ S w)

section Values

variable {p S : Set W} {w : W}

@[simp] theorem ofSet_eq_one_iff : ofSet p S w = 1 ↔ w ∈ p := by simp [ofSet]

@[simp] theorem ofSet_eq_neg_one_iff : ofSet p S w = -1 ↔ w ∉ p := by simp [ofSet]

@[simp] theorem ofSet_ne_zero : ofSet p S w ≠ 0 := by simp [ofSet]

@[simp] theorem might_eq_one_iff : might p S w = 1 ↔ (S ∩ p).Nonempty := by
  simpa [might] using fun h : (S ∩ p).Nonempty ↦ h.mono Set.inter_subset_left

@[simp] theorem might_eq_neg_one_iff : might p S w = -1 ↔ S.Nonempty ∧ ¬ (S ∩ p).Nonempty := by
  simp [might]

@[simp] theorem might_eq_zero_iff : might p S w = 0 ↔ S = ∅ := by
  simp [might, Set.nonempty_iff_ne_empty]

@[simp] theorem must_eq_one_iff : must p S w = 1 ↔ S.Nonempty ∧ S ⊆ p := by simp [must]

@[simp] theorem must_eq_neg_one_iff : must p S w = -1 ↔ S.Nonempty ∧ ¬ S ⊆ p := by simp [must]

@[simp] theorem must_eq_zero_iff : must p S w = 0 ↔ S = ∅ := by
  simp [must, Set.nonempty_iff_ne_empty]

@[simp] theorem neg_apply (φ : SProp W) : neg φ S w = -φ S w := rfl

end Values

/-- An *according to X* phrase evaluates its complement at `X`'s own information state (39). -/
def accordingTo (T : Set W) (φ : SProp W) : SProp W := fun _ => φ T

/-- Epistemic modal force. -/
inductive Force
  | possibility
  | necessity
  deriving DecidableEq, Fintype

/-- The epistemic of a given force. -/
noncomputable def Force.modal : Force → Set W → SProp W
  | .possibility => might
  | .necessity => must

/-! ### Representational and non-representational attitudes -/

/-- Under a representational attitude (29) the complement holds at every world of the attitude's
domain, which also serves as its information state; it is the Weak Kleene universal over the
domain. -/
noncomputable def representational (dox : W → Set W) (φ : SProp W) : W → SignType :=
  fun w ↦ Trivalent.forallWeak fun v : dox w ↦ φ (dox w) v

/-- Vacuous quantification (35) — an embedded necessity epistemic claims that the domain is
included in its prejacent. -/
theorem representational_must_eq_one_iff (dox : W → Set W) (p : Set W) (w : W) :
    representational dox (must p) w = 1 ↔ dox w ⊆ p := by
  simp only [representational, Trivalent.forallWeak_eq_one_iff, must_eq_one_iff, Subtype.forall]
  exact ⟨fun h v hv ↦ (h v hv).2 hv, fun h v hv ↦ ⟨⟨v, hv⟩, h⟩⟩

/-- The paper's (23b), *imagine that it is raining but it might not be*, is contradictory whenever
the imagination state is nonempty, since the modal quantifies over that very state. -/
theorem imagine_epistemic_eq_neg_one (dox : W → Set W) (p : Set W) {w : W}
    (h : (dox w).Nonempty) :
    representational dox (conj (ofSet p) (might pᶜ)) w = -1 := by
  have hm (u : W) : might pᶜ (dox w) u ≠ 0 := by simpa [Set.nonempty_iff_ne_empty] using h
  rw [representational, Trivalent.forallWeak_eq_neg_one_iff]
  refine ⟨fun u ↦ by simp [conj, hm], ?_⟩
  by_cases hp : dox w ⊆ p
  · obtain ⟨v, hv⟩ := id h
    exact ⟨⟨v, hv⟩, by simp [conj, h, Set.inter_compl_nonempty_iff, hp, hp hv]⟩
  · obtain ⟨u, hu, hup⟩ := Set.not_subset.1 hp
    exact ⟨⟨u, hu⟩, by simp [conj, hm, hup]⟩

/-- Villalta's lift of a strict ordering to sets (32b) requires that every member of `q` is
bettered by some
member of `p`, and some member of `p` is bettered by no member of `q`. Applied to sets of sets
it is the ordering of (52). -/
def Better {α : Type*} (r : α → α → Prop) (p q : Set α) : Prop :=
  (∀ v ∈ q, ∃ u ∈ p, r u v) ∧ ∃ u ∈ p, ∀ v ∈ q, ¬ r v u

theorem Better.mono_left {α : Type*} {r : α → α → Prop} {p p' q : Set α} (h : Better r p q)
    (hp : p ⊆ p') : Better r p' q :=
  ⟨fun v hv => let ⟨u, hu, hr⟩ := h.1 v hv; ⟨u, hp hu, hr⟩,
    let ⟨u, hu, hr⟩ := h.2; ⟨u, hp hu, hr⟩⟩

theorem Better.anti_right {α : Type*} {r : α → α → Prop} {p q q' : Set α} (h : Better r p q)
    (hq : q' ⊆ q) : Better r p q' :=
  ⟨fun v hv => h.1 v (hq hv), let ⟨u, hu, hr⟩ := h.2; ⟨u, hu, fun v hv => hr v (hq hv)⟩⟩

open Classical in
/-- Under a non-representational attitude (36) the information state is reset to `∅`, and the
complement evaluated there is compared with its negation — Villalta's comparison over the
Heimian alternative set `{φ, ¬φ}`, with `des w` the desirability ordering at `w`, setting the
worlds where the complement is true against those where its negation is. -/
noncomputable def preferential (des : W → W → W → Prop) (φ : SProp W) : W → SignType :=
  (Function.support (φ ∅)).indicator fun w ↦
    SignType.ofProp (Better (des w) (Trivalent.posExt (φ ∅)) (Trivalent.posExt (neg φ ∅)))

/-- In (38) an epistemic embedded under a non-representational attitude inherits the empty
information state and fails its non-triviality presupposition. -/
theorem preferential_modal_eq_zero (des : W → W → W → Prop) (f : Force) (p : Set W)
    (w : W) : preferential des (f.modal p) w = 0 := by
  cases f <;> simp [preferential, Force.modal]

/-- The escape hatch (39) is an *according to X* phrase making the embedded epistemic defined
exactly when `X`'s information state is nonempty. -/
theorem preferential_accordingTo_ne_zero_iff (des : W → W → W → Prop) (T : Set W) (f : Force)
    (p : Set W) (w : W) :
    preferential des (accordingTo T (f.modal p)) w ≠ 0 ↔ T.Nonempty := by
  cases f <;> simp [preferential, accordingTo, Force.modal, Set.nonempty_iff_ne_empty]

/-! ### Verifiers and falsifiers -/

/-- The nonempty sub-states of `A`. -/
def subStates {α : Type*} (A : Set α) : Set (Set α) := {X | X ⊆ A ∧ X.Nonempty}

/-- The `φ`-verifiers in `S` (50) are the nonempty sub-states of `S` on all of whose sub-states
`φ` holds throughout. -/
def verifiers (φ : SProp W) (S : Set W) : Set (Set W) :=
  {X | X ⊆ S ∧ X.Nonempty ∧ ∀ Y ⊆ X, ∀ w ∈ Y, φ Y w = 1}

/-- The `φ`-falsifiers in `S` are the `¬φ`-verifiers. -/
def falsifiers (φ : SProp W) (S : Set W) : Set (Set W) := verifiers (neg φ) S

theorem verifiers_eq {φ : SProp W} {q : Set W}
    (h : ∀ X : Set W, (∀ Y ⊆ X, ∀ w ∈ Y, φ Y w = 1) ↔ X ⊆ q) (S : Set W) :
    verifiers φ S = subStates (S ∩ q) := by
  ext X; simp only [verifiers, subStates, Set.mem_ofPred_eq, h, Set.subset_inter_iff]; tauto

/-- By Figure 3 the verifiers of `p`, `might p`, and `must p` in `S` are all the nonempty
sub-states of `S ∩ p`. -/
theorem verifiers_ofSet (p S : Set W) : verifiers (ofSet p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := ofSet p) (q := p) (fun X => ⟨fun h _ hw => ofSet_eq_one_iff.1
    (h X Set.Subset.rfl _ hw), fun h _ hY _ hw => ofSet_eq_one_iff.2 (h (hY hw))⟩) S

theorem verifiers_might (p S : Set W) : verifiers (might p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := might p) (q := p) (fun X => ⟨fun h w hw => by
      obtain ⟨v, hv, hvp⟩ := might_eq_one_iff.1
        (h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w))
      exact Set.mem_singleton_iff.mp hv ▸ hvp,
    fun h _ hY w hw => might_eq_one_iff.2 ⟨w, hw, h (hY hw)⟩⟩) S

theorem verifiers_must (p S : Set W) : verifiers (must p) S = subStates (S ∩ p) :=
  verifiers_eq (φ := must p) (q := p) (fun X => ⟨fun h _ hw =>
    (must_eq_one_iff.1 (h X Set.Subset.rfl _ hw)).2 hw,
    fun h _ hY _ hw => must_eq_one_iff.2 ⟨⟨_, hw⟩, hY.trans h⟩⟩) S

/-- By Figure 3 the falsifiers of `p`, `might p`, and `must p` in `S` are all the nonempty
sub-states of `S ∩ pᶜ`. -/
theorem falsifiers_ofSet (p S : Set W) : falsifiers (ofSet p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (ofSet p)) (q := pᶜ) (fun X => ⟨fun h _ hw => by
    simpa using h X Set.Subset.rfl _ hw, fun h _ hY _ hw => by simpa using h (hY hw)⟩) S

theorem falsifiers_might (p S : Set W) : falsifiers (might p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (might p)) (q := pᶜ) (fun _ => ⟨fun h w hw hp => by
      simpa [hp] using h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w),
    fun h _ hY w hw => by
      rw [neg_apply, SignType.neg_eq_one_iff, might_eq_neg_one_iff]
      exact ⟨⟨w, hw⟩, fun ⟨_, hvY, hvp⟩ => h (hY hvY) hvp⟩⟩) S

theorem falsifiers_must (p S : Set W) : falsifiers (must p) S = subStates (S ∩ pᶜ) :=
  verifiers_eq (φ := neg (must p)) (q := pᶜ) (fun _ => ⟨fun h w hw hp => by
      simpa [hp] using h {w} (Set.singleton_subset_iff.mpr hw) w (Set.mem_singleton w),
    fun h _ hY w hw => by
      rw [neg_apply, SignType.neg_eq_one_iff, must_eq_neg_one_iff]
      exact ⟨⟨w, hw⟩, fun hYp => h (hY hw) (hYp hw)⟩⟩) S

/-- By footnote 19, comparing two families of nonempty sub-states under the lifted ordering is
comparing the states themselves, by upward monotonicity of `Better` in its first argument and
downward monotonicity in its second. -/
theorem better_subStates_iff {α : Type*} (r : α → α → Prop) (A B : Set α) :
    Better (Better r) (subStates A) (subStates B) ↔ Better r A B := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases B.eq_empty_or_nonempty with rfl | hB
    · obtain ⟨P, ⟨hPA, u, hu⟩, -⟩ := h2
      exact ⟨fun v hv => absurd hv (Set.notMem_empty v), u, hPA hu,
        fun v hv => absurd hv (Set.notMem_empty v)⟩
    · obtain ⟨p, ⟨hpA, -⟩, hp⟩ := h1 B ⟨Set.Subset.rfl, hB⟩
      exact hp.mono_left hpA
  · rintro ⟨h1, u, hu, hr⟩
    refine ⟨fun q hq => ⟨A, ⟨Set.Subset.rfl, u, hu⟩, Better.anti_right ⟨h1, u, hu, hr⟩ hq.1⟩,
      {u}, ⟨Set.singleton_subset_iff.mpr hu, Set.singleton_nonempty u⟩, fun q hq hqu => ?_⟩
    obtain ⟨v, hv, hvr⟩ := hqu.1 u (Set.mem_singleton u)
    exact hr v (hq.1 hv) hvr

/-- In (51) the preference component of an emotive doxastic compares `S ∩ p` with `S ∩ pᶜ`. -/
theorem prefers_iff {φ : SProp W} {p S : Set W} (r : W → W → Prop)
    (hv : verifiers φ S = subStates (S ∩ p)) (hf : falsifiers φ S = subStates (S ∩ pᶜ)) :
    Better (Better r) (verifiers φ S) (falsifiers φ S) ↔ Better r (S ∩ p) (S ∩ pᶜ) := by
  rw [hv, hf, better_subStates_iff]

/-- The preference component does not see the modal, so *hopes p*, *hopes might p*, and
*hopes must p* all prefer the `p`-verifying doxastic alternatives. -/
theorem prefers_modal_iff (r : W → W → Prop) (p S : Set W) (f : Force) :
    Better (Better r) (verifiers (f.modal p) S) (falsifiers (f.modal p) S) ↔
      Better (Better r) (verifiers (ofSet p) S) (falsifiers (ofSet p) S) := by
  cases f <;> simp only [Force.modal, verifiers_might, verifiers_must, falsifiers_might,
    falsifiers_must, verifiers_ofSet, falsifiers_ofSet]

/-! ### Emotive doxastics and dubitatives -/

/-- The uncertainty condition (54) demands that the complement has both verifiers and
falsifiers in the
doxastic state. -/
def Uncertain (φ : SProp W) (S : Set W) : Prop :=
  (verifiers φ S).Nonempty ∧ (falsifiers φ S).Nonempty

/-- The doxastic assertion (53) says the complement holds at some world of the doxastic
state. -/
def Possible (φ : SProp W) (S : Set W) : Prop := ∃ w ∈ S, φ S w = 1

open Classical in
/-- `a hopes that φ` (55) presupposes uncertainty and asserts doxastic possibility and that the
verifiers are more desirable than the falsifiers. *fear* has the shape of `doubt` over the
desirability ordering. -/
noncomputable def hope (des : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) :
    W → SignType :=
  {w | Uncertain φ (dox w)}.indicator fun w ↦ SignType.ofProp
    (Possible φ (dox w) ∧ Better (Better (des w)) (verifiers φ (dox w)) (falsifiers φ (dox w)))

open Classical in
/-- `a doubts that φ` (63) is as `hope`, with the falsifiers likelier than the verifiers. -/
noncomputable def doubt (prob : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) :
    W → SignType :=
  {w | Uncertain φ (dox w)}.indicator fun w ↦ SignType.ofProp
    (Possible φ (dox w) ∧ Better (Better (prob w)) (falsifiers φ (dox w)) (verifiers φ (dox w)))

section Values

variable {r : W → W → W → Prop} {dox : W → Set W} {φ : SProp W} {w : W}

theorem hope_eq_one_iff : hope r dox φ w = 1 ↔ Uncertain φ (dox w) ∧ Possible φ (dox w) ∧
    Better (Better (r w)) (verifiers φ (dox w)) (falsifiers φ (dox w)) := by
  simp [hope]

theorem doubt_eq_one_iff : doubt r dox φ w = 1 ↔ Uncertain φ (dox w) ∧ Possible φ (dox w) ∧
    Better (Better (r w)) (falsifiers φ (dox w)) (verifiers φ (dox w)) := by
  simp [doubt]

end Values

/-- In (58) with *must*, the doxastic assertion of an embedded necessity epistemic puts the whole
state inside `p`, leaving no falsifier — it contradicts the uncertainty presupposition. -/
theorem uncertain_must_not_possible {p S : Set W} (hu : Uncertain (must p) S) :
    ¬ Possible (must p) S := by
  intro hp
  obtain ⟨_, _, hS⟩ := hp
  obtain ⟨_, hf⟩ := hu
  rw [falsifiers_must] at hf
  obtain ⟨X, hX, v, hv⟩ := hf
  exact (hX hv).2 ((must_eq_one_iff.1 hS).2 (hX hv).1)

theorem hope_must_ne_one (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W) :
    hope des dox (must p) w ≠ 1 := fun h ↦
  let ⟨hu, hp, _⟩ := hope_eq_one_iff.1 h
  uncertain_must_not_possible hu hp

theorem doubt_must_ne_one (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : doubt prob dox (must p) w ≠ 1 := fun h ↦
  let ⟨hu, hp, _⟩ := doubt_eq_one_iff.1 h
  uncertain_must_not_possible hu hp

/-- In (74) a possibility epistemic scoping under negation is a universal claim and fails like
*must*. -/
theorem hope_neg_might_ne_one (des : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : hope des dox (neg (might p)) w ≠ 1 := by
  intro h
  obtain ⟨⟨-, X, hXS, ⟨v, hv⟩, hX⟩, ⟨_, _, hS⟩, -⟩ := hope_eq_one_iff.1 h
  have hX : (X ∩ p).Nonempty := by simpa using hX X Set.Subset.rfl v hv
  have hS : (dox w).Nonempty ∧ ¬ (dox w ∩ p).Nonempty := by simpa using hS
  exact hS.2 (hX.mono (Set.inter_subset_inter_left p hXS))

theorem possible_might_iff (p S : Set W) : Possible (might p) S ↔ Possible (ofSet p) S := by
  simp only [Possible, might_eq_one_iff, ofSet_eq_one_iff]
  exact ⟨fun ⟨_, _, v, hv⟩ => ⟨v, hv.1, hv.2⟩, fun ⟨w, hw, hp⟩ => ⟨w, hw, w, hw, hp⟩⟩

open Classical in
/-- Under an emotive doxastic, *might p* and bare *p* have the same uncertainty presupposition,
doxastic assertion, and preference, so (59) is (57) — modal concord. -/
theorem hope_might (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    hope des dox (might p) = hope des dox (ofSet p) := by
  simp only [hope, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

open Classical in
theorem doubt_might (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    doubt prob dox (might p) = doubt prob dox (ofSet p) := by
  simp only [doubt, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

/-! ### The distribution -/

/-- The attitude classes of Table 3. -/
inductive AttitudeClass
  | doxastic
  | argumentative
  | semifactive
  | desiderative
  | directive
  | emotiveDoxastic
  | dubitative
  deriving DecidableEq, Fintype

/-- The four lexical semantics the paper assigns. -/
inductive Kind
  | acceptance
  | preferenceOriented
  | emotiveDoxastic
  | dubitative
  deriving DecidableEq

/-- Attitudes of acceptance are representational (§3.3), desideratives and directives
preference-oriented (36), and the two hybrid classes get (55) and (63). -/
def AttitudeClass.kind : AttitudeClass → Kind
  | .doxastic | .argumentative | .semifactive => .acceptance
  | .desiderative | .directive => .preferenceOriented
  | .emotiveDoxastic => .emotiveDoxastic
  | .dubitative => .dubitative

/-- The lexical entry of each kind, over the attitude's scale, doxastic state, and
complement. -/
noncomputable def Kind.entry : Kind → (W → W → W → Prop) → (W → Set W) → SProp W → W → SignType
  | .acceptance => fun _ dox => representational dox
  | .preferenceOriented => fun r _ => preferential r
  | .emotiveDoxastic => hope
  | .dubitative => doubt

/-- An epistemic of force `f` is licensed under a kind of attitude when some scale, doxastic
state, prejacent, and world make the embedding defined and true. -/
def Licensed (W : Type*) (k : Kind) (f : Force) : Prop :=
  ∃ (r : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W),
    k.entry r dox (f.modal p) w = 1

theorem licensed_acceptance [Nontrivial W] (f : Force) :
    Licensed W .acceptance f := by
  obtain ⟨a, -, -⟩ := exists_pair_ne W
  refine ⟨fun _ _ _ => True, fun _ => Set.univ, Set.univ, a, ?_⟩
  cases f <;> simp [Kind.entry, Force.modal, representational]

theorem not_licensed_preferenceOriented (f : Force) : ¬ Licensed W .preferenceOriented f :=
  fun ⟨r, _, p, w, h⟩ => absurd ((preferential_modal_eq_zero r f p w).symm.trans h) (by decide)

theorem licensed_emotiveDoxastic_possibility [Nontrivial W] :
    Licensed W .emotiveDoxastic .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u = a ∧ v ≠ a, fun _ => Set.univ, {a}, a, hope_eq_one_iff.2 ⟨?_,
    ⟨a, trivial, might_eq_one_iff.2 ⟨a, trivial, rfl⟩⟩, ?_⟩⟩
  · show Uncertain (might {a}) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u = a ∧ v ≠ a) (verifiers (might {a}) Set.univ)
      (falsifiers (might {a}) Set.univ)
    rw [prefers_iff _ (verifiers_might _ _) (falsifiers_might _ _), Set.univ_inter,
      Set.univ_inter]
    exact ⟨fun v hv => ⟨a, rfl, rfl, hv⟩, a, rfl, fun v hv h => hv h.1⟩

theorem not_licensed_emotiveDoxastic_necessity : ¬ Licensed W .emotiveDoxastic .necessity :=
  fun ⟨r, dox, p, w, h⟩ => hope_must_ne_one r dox p w h

theorem licensed_dubitative_possibility [Nontrivial W] : Licensed W .dubitative .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u ≠ a ∧ v = a, fun _ => Set.univ, {a}, a, doubt_eq_one_iff.2 ⟨?_,
    ⟨a, trivial, might_eq_one_iff.2 ⟨a, trivial, rfl⟩⟩, ?_⟩⟩
  · show Uncertain (might {a}) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u ≠ a ∧ v = a) (falsifiers (might {a}) Set.univ)
      (verifiers (might {a}) Set.univ)
    rw [falsifiers_might, verifiers_might, better_subStates_iff, Set.univ_inter, Set.univ_inter]
    exact ⟨fun v hv => ⟨b, hab.symm, hab.symm, hv⟩, b, hab.symm, fun v hv h => h.1 hv⟩

theorem not_licensed_dubitative_necessity : ¬ Licensed W .dubitative .necessity :=
  fun ⟨r, dox, p, w, h⟩ => doubt_must_ne_one r dox p w h

/-- Table 3, derived — epistemics are licensed by representational attitudes, by no
preferential attitude, and by the hybrids only with possibility force. -/
theorem licensed_iff [Nontrivial W] (k : Kind) (f : Force) :
    Licensed W k f ↔ k ≠ .preferenceOriented ∧ (k = .acceptance ∨ f = .possibility) := by
  cases k <;> cases f <;>
    simp only [licensed_acceptance, not_licensed_preferenceOriented,
      licensed_emotiveDoxastic_possibility, not_licensed_emotiveDoxastic_necessity,
      licensed_dubitative_possibility, not_licensed_dubitative_necessity] <;> decide

/-! ### The paper's examples -/

/-- The `attitude_class` feature of an example row. -/
def AttitudeClass.ofString? : String → Option AttitudeClass
  | "doxastic" => some .doxastic
  | "argumentative" => some .argumentative
  | "semifactive" => some .semifactive
  | "desiderative" => some .desiderative
  | "directive" => some .directive
  | "emotive_doxastic" => some .emotiveDoxastic
  | "dubitative" => some .dubitative
  | _ => none

/-- The `modal_force` feature of an example row. -/
def Force.ofString? : String → Option Force
  | "possibility" => some .possibility
  | "necessity" => some .necessity
  | _ => none

theorem rows_track_licensing [Nontrivial W] :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" →
      r.feature? "modal_flavor" = some "epistemic" →
      ∀ c f, (r.feature? "attitude_class").bind AttitudeClass.ofString? = some c →
        (r.feature? "modal_force").bind Force.ofString? = some f →
        (r.judgment = .acceptable ↔ Licensed W c.kind f) := by
  simp only [licensed_iff]; decide +kernel

/-- Every unacceptable attitude-anchored epistemic in the Romance data sits in a subjunctive
complement (§5.1); the converse fails at (18), (20), and (65). -/
theorem unacceptable_rows_subjunctive :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" → r.judgment = .unacceptable →
      r.feature? "mood" = none ∨ r.feature? "mood" = some "subjunctive" := by
  decide +kernel

end AnandHacquard2013
