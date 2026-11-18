module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Modality.DomainSemantics
public import Linglib.Semantics.Modality.ComparativePossibility
public import Linglib.Data.Examples.AnandHacquard2013
public import Mathlib.Data.Set.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Readers

/-!
# Anand & Hacquard 2013: epistemics and attitudes

Epistemic modals are acceptable in the complements of attitudes of acceptance (*think*, *say*,
*realize*), unacceptable under desideratives and directives, and acceptable under emotive
doxastics (*hope*, *fear*) and dubitatives (*doubt*) with possibility but not necessity force, in
seven-point acceptability surveys of French, Italian, and Spanish.

The account adopts Yalcin's domain semantics, on which an epistemic quantifies over an information
state $S$ anaphoric to the embedding attitude, and adds Geurts's presupposition that $S$ is not
empty: an epistemic is undefined at the empty state and elsewhere [is Yalcin's
modal](##truth_might) on the truth of its complement. Following Bolinger, representational
attitudes pass their doxastic state as $S$ and [are true where that state accepts the
complement](##representational_eq_true_iff); non-representational ones set $S = \emptyset$ and
compare the complement with its negation by Villalta's ordering, so [an embedded epistemic is never
defined](##preferential_modal_eq_undefined). Emotive doxastics and dubitatives are hybrids: a
doxastic possibility assertion, a comparison of the complement's verifiers with its falsifiers, and
an uncertainty presupposition demanding both. The doxastic assertion of an embedded necessity modal
[contradicts that presupposition](##hope_must_ne_true), and so does a negated possibility modal,
[a universal assertion](##compl_might_ofSet), while [an embedded possibility modal contributes
nothing new](##hope_might). Together these [derive the distribution](##rows_track_licensing).
Italian *pensare* selects the subjunctive yet licenses epistemics, so the subjunctive is an
imperfect correlate.

## Implementation notes

* A complement is a trivalent proposition for each information state, `Set W → W → Trivalent`.
* The paper does not say how an attitude treats a partial complement. A representational attitude
  is the Weak Kleene universal over its domain. A non-representational one compares two sets of
  worlds, so it is defined only when its complement, at the empty state, is defined at every world:
  the reading on which an embedded epistemic is undefined whatever the world of evaluation.
* Villalta's alternative set is Heim's $\{\varphi, \neg\varphi\}$, as the paper assumes.

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

open DomainSemantics ComparativePossibility

variable {W : Type*}

/-! ### Complements relative to an information state -/

/-- A complement evaluated against an information state `S` — Yalcin's parameter — as a
trivalent proposition for each `S`. -/
abbrev SProp (W : Type*) := Set W → W → Trivalent

/-- Where a complement is true, a sentence of Yalcin's domain semantics. -/
def truth (φ : SProp W) : DomainSemantics.Sentence W := fun S w ↦ φ S w = .true

open Classical in
/-- An unmodalized complement ignores the information state. -/
noncomputable def ofSet (p : Set W) : SProp W := fun _ w ↦ Trivalent.ofProp (w ∈ p)

open Classical in
/-- Epistemic possibility (37a) presupposes `S ≠ ∅` and is otherwise Yalcin's *might* (26) on
the truth of its complement. -/
noncomputable def might (φ : SProp W) : SProp W := fun S w ↦
  Trivalent.transplication (Trivalent.ofProp S.Nonempty) (Trivalent.ofProp ((truth φ).might S w))

open Classical in
/-- Epistemic necessity (37b) presupposes `S ≠ ∅` and is otherwise Yalcin's *must* on the truth
of its complement. -/
noncomputable def must (φ : SProp W) : SProp W := fun S w ↦
  Trivalent.transplication (Trivalent.ofProp S.Nonempty) (Trivalent.ofProp ((truth φ).must S w))

/-- Conjunction of complements, defined where both are (Weak Kleene). -/
def conj (φ ψ : SProp W) : SProp W := fun S w ↦ (φ S w).meetWeak (ψ S w)

section Values

variable {φ : SProp W} {p S : Set W} {w : W}

@[simp] theorem truth_apply : truth φ S w ↔ φ S w = .true := .rfl

@[simp] theorem ofSet_eq_true_iff : ofSet p S w = .true ↔ w ∈ p := by simp [ofSet]

@[simp] theorem ofSet_eq_false_iff : ofSet p S w = .false ↔ w ∉ p := by simp [ofSet]

@[simp] theorem ofSet_ne_undefined : ofSet p S w ≠ .undefined := by simp [ofSet]

theorem truth_ofSet (p : Set W) : truth (ofSet p) = Sentence.ofProp p := by
  funext S w; simp [Sentence.ofProp]

theorem compl_ofSet (p : Set W) : (ofSet p)ᶜ = ofSet pᶜ := by
  funext S w; by_cases h : w ∈ p <;> simp [ofSet, h]

@[simp] theorem might_eq_true_iff : might φ S w = .true ↔ ∃ w' ∈ S, φ S w' = .true := by
  simpa [might, Sentence.might] using fun w' hw' _ ↦ ⟨w', hw'⟩

@[simp] theorem might_eq_false_iff :
    might φ S w = .false ↔ S.Nonempty ∧ ∀ w' ∈ S, φ S w' ≠ .true := by
  simp [might, Sentence.might]

@[simp] theorem might_eq_undefined_iff : might φ S w = .undefined ↔ S = ∅ := by
  simp [might, Set.nonempty_iff_ne_empty]

@[simp] theorem must_eq_true_iff : must φ S w = .true ↔ S.Nonempty ∧ ∀ w' ∈ S, φ S w' = .true := by
  simp [must, Sentence.must]

@[simp] theorem must_eq_false_iff :
    must φ S w = .false ↔ S.Nonempty ∧ ∃ w' ∈ S, φ S w' ≠ .true := by
  simp [must, Sentence.must]

@[simp] theorem must_eq_undefined_iff : must φ S w = .undefined ↔ S = ∅ := by
  simp [must, Set.nonempty_iff_ne_empty]

end Values

/-- Wherever epistemic possibility is defined it is [yalcin-2007]'s: its truth is the
domain-semantic *might* of the truth of its complement. -/
theorem truth_might (φ : SProp W) : truth (might φ) = (truth φ).might := by
  funext S w; simp [Sentence.might]

theorem acceptedIn_truth_must (φ : SProp W) {S : Set W} :
    (truth (must φ)).AcceptedIn S ↔ (truth φ).AcceptedIn S :=
  ⟨fun h w hw ↦ (must_eq_true_iff.1 (h w hw)).2 w hw, fun h _ hw ↦ must_eq_true_iff.2 ⟨⟨_, hw⟩, h⟩⟩

theorem compl_might_ofSet (p : Set W) : (might (ofSet p))ᶜ = must (ofSet pᶜ) := by
  funext S w
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_ <;> simp

theorem compl_must_ofSet (p : Set W) : (must (ofSet p))ᶜ = might (ofSet pᶜ) := by
  funext S w
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp) ?_
  simpa using fun x hx _ ↦ ⟨x, hx⟩

/-- An *according to X* phrase evaluates its complement at `X`'s own information state (39). -/
def accordingTo (T : Set W) (φ : SProp W) : SProp W := fun _ => φ T

/-- Epistemic modal force. -/
inductive Force
  | possibility
  | necessity
  deriving DecidableEq, Fintype

/-- The epistemic of a given force. -/
noncomputable def Force.modal : Force → SProp W → SProp W
  | .possibility => might
  | .necessity => must

@[simp] theorem Force.modal_eq_undefined_iff {f : Force} {φ : SProp W} {S : Set W} {w : W} :
    f.modal φ S w = .undefined ↔ S = ∅ := by
  cases f <;> simp [Force.modal]

/-! ### Representational and non-representational attitudes -/

/-- Under a representational attitude (29) the complement holds at every world of the attitude's
domain, which also serves as its information state; it is the Weak Kleene universal over the
domain. -/
noncomputable def representational (dox : W → Set W) (φ : SProp W) : W → Trivalent :=
  fun w ↦ Trivalent.forallWeak fun v : dox w ↦ φ (dox w) v

theorem representational_eq_true_iff (dox : W → Set W) (φ : SProp W) (w : W) :
    representational dox φ w = .true ↔ (truth φ).AcceptedIn (dox w) := by
  rw [representational, Trivalent.forallWeak_eq_true_iff, Subtype.forall]; rfl

-- (35)
theorem representational_must_eq_true_iff (dox : W → Set W) (φ : SProp W) (w : W) :
    representational dox (must φ) w = .true ↔ representational dox φ w = .true := by
  rw [representational_eq_true_iff, representational_eq_true_iff, acceptedIn_truth_must]

-- (23b)
theorem imagine_epistemic_eq_false (dox : W → Set W) (p : Set W) {w : W}
    (h : (dox w).Nonempty) :
    representational dox (conj (ofSet p) (might (ofSet pᶜ))) w = .false := by
  have hm (u : W) : might (ofSet pᶜ) (dox w) u ≠ .undefined := by
    simpa [Set.nonempty_iff_ne_empty] using h
  rw [representational, Trivalent.forallWeak_eq_false_iff]
  refine ⟨fun u ↦ by simp [conj, hm], ?_⟩
  by_cases hp : dox w ⊆ p
  · obtain ⟨v, hv⟩ := id h
    exact ⟨⟨v, hv⟩, by simpa [conj, h, hp hv] using fun _ hu ↦ hp hu⟩
  · obtain ⟨u, hu, hup⟩ := Set.not_subset.1 hp
    exact ⟨⟨u, hu⟩, by simp [conj, hm, hup]⟩

/-- Villalta's lift of a strict ordering to sets (32b) requires that every member of `q` is
bettered by some member of `p`, and some member of `p` is bettered by no member of `q`: `p` is
strictly more possible than `q` in Lewis's sense of comparative possibility. Applied to sets of
sets it is the ordering of (52). -/
def Better {α : Type*} (r : α → α → Prop) : Set α → Set α → Prop :=
  AsymmRel (Lewis r)

theorem Better.mono_left {α : Type*} {r : α → α → Prop} {p p' q : Set α} (h : Better r p q)
    (hp : p ⊆ p') : Better r p' q :=
  ⟨h.1.mono_left hp, fun h' ↦ h.2 (h'.anti_right hp)⟩

theorem Better.anti_right {α : Type*} {r : α → α → Prop} {p q q' : Set α} (h : Better r p q)
    (hq : q' ⊆ q) : Better r p q' :=
  ⟨h.1.anti_right hq, fun h' ↦ h.2 (h'.mono_left hq)⟩

open Classical in
/-- Under a non-representational attitude (36) the information state is reset to `∅`, and the
complement evaluated there is compared with its negation — Villalta's comparison over the
Heimian alternative set `{φ, ¬φ}`, with `des w` the desirability ordering at `w`, setting the
worlds where the complement is true against those where it is false. The comparison is between
sets of worlds, so it is defined only when the complement is defined at every world. -/
noncomputable def preferential (des : W → W → W → Prop) (φ : SProp W) : W → Trivalent :=
  Trivalent.condEvent (fun _ ↦ Trivalent.IsBivalent (φ ∅))
    (fun w ↦ Better (des w) (Trivalent.posExt (φ ∅)) (Trivalent.negExt (φ ∅)))

open Classical in
/-- An epistemic embedded under a desiderative or directive is undefined, whatever its
complement (38). -/
theorem preferential_modal_eq_undefined (des : W → W → W → Prop) (f : Force) (φ : SProp W)
    (w : W) : preferential des (f.modal φ) w = .undefined :=
  Trivalent.condEvent_eq_undefined_iff.2 fun h ↦ h.ne_undefined w (by simp)

-- (39)
theorem preferential_accordingTo_ne_undefined_iff (des : W → W → W → Prop) (T : Set W) (f : Force)
    (φ : SProp W) (w : W) :
    preferential des (accordingTo T (f.modal φ)) w ≠ .undefined ↔ T.Nonempty := by
  simp only [preferential, accordingTo, ne_eq, Trivalent.condEvent_eq_undefined_iff, not_not,
    Trivalent.isBivalent_iff_forall_ne_undefined, Force.modal_eq_undefined_iff,
    Set.nonempty_iff_ne_empty]
  exact ⟨fun h ↦ h w, fun h _ ↦ h⟩

/-! ### Verifiers and falsifiers -/

/-- The nonempty sub-states of `A`. -/
def subStates {α : Type*} (A : Set α) : Set (Set α) := {X | X ⊆ A ∧ X.Nonempty}

/-- The `φ`-verifiers in `S` (50) are the nonempty sub-states of `S` that accept `φ` and are
certain about it: each of their own sub-states accepts `φ` as well. -/
def verifiers (φ : SProp W) (S : Set W) : Set (Set W) :=
  {X | X ⊆ S ∧ X.Nonempty ∧ ∀ Y ⊆ X, (truth φ).AcceptedIn Y}

/-- The `φ`-falsifiers in `S` are the `¬φ`-verifiers. -/
def falsifiers (φ : SProp W) (S : Set W) : Set (Set W) := verifiers φᶜ S

theorem verifiers_eq {φ : SProp W} {q : Set W}
    (h : ∀ X : Set W, (∀ Y ⊆ X, (truth φ).AcceptedIn Y) ↔ X ⊆ q) (S : Set W) :
    verifiers φ S = subStates (S ∩ q) := by
  ext X; simp only [verifiers, subStates, Set.mem_ofPred_eq, h, Set.subset_inter_iff]; tauto

theorem verifiers_must (φ : SProp W) (S : Set W) : verifiers (must φ) S = verifiers φ S := by
  simp only [verifiers, acceptedIn_truth_must]

-- Figure 3
theorem verifiers_ofSet (p S : Set W) : verifiers (ofSet p) S = subStates (S ∩ p) :=
  verifiers_eq (fun X ↦ by
    simp only [truth_ofSet, Sentence.acceptedIn_ofProp_iff]
    exact ⟨fun h ↦ h X subset_rfl, fun h _ hY ↦ hY.trans h⟩) S

theorem verifiers_might (p S : Set W) : verifiers (might (ofSet p)) S = subStates (S ∩ p) :=
  verifiers_eq (fun X ↦ by
    simp only [truth_might, truth_ofSet, Sentence.acceptedIn_might_iff]
    refine ⟨fun h w hw ↦ ?_, fun h Y hY ↦
      Y.eq_empty_or_nonempty.imp_right fun ⟨w, hw⟩ ↦ ⟨w, hw, h (hY hw)⟩⟩
    obtain ⟨v, hv, hvp⟩ :=
      (h {w} (Set.singleton_subset_iff.2 hw)).resolve_left (Set.singleton_ne_empty w)
    exact Set.mem_singleton_iff.1 hv ▸ hvp) S

-- Figure 3
theorem falsifiers_ofSet (p S : Set W) : falsifiers (ofSet p) S = subStates (S ∩ pᶜ) := by
  rw [falsifiers, compl_ofSet, verifiers_ofSet]

theorem falsifiers_might (p S : Set W) : falsifiers (might (ofSet p)) S = subStates (S ∩ pᶜ) := by
  rw [falsifiers, compl_might_ofSet, verifiers_must, verifiers_ofSet]

theorem falsifiers_must (p S : Set W) : falsifiers (must (ofSet p)) S = subStates (S ∩ pᶜ) := by
  rw [falsifiers, compl_must_ofSet, verifiers_might]

-- footnote 19
theorem better_subStates_iff {α : Type*} (r : α → α → Prop) (A B : Set α) :
    Better (Better r) (subStates A) (subStates B) ↔ Better r A B := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases B.eq_empty_or_nonempty with rfl | hB
    · obtain ⟨P, ⟨hPA, u, hu⟩, -⟩ := not_lewis_iff.1 h2
      exact ⟨lewis_empty A, fun h ↦ by simpa [lewis_empty_left_iff.1 h] using hPA hu⟩
    · obtain ⟨p, ⟨hpA, -⟩, hp⟩ := h1 ⟨Set.Subset.rfl, hB⟩
      exact Better.mono_left hp hpA
  · intro hAB
    obtain ⟨u, hu, hr⟩ := not_lewis_iff.1 hAB.2
    refine ⟨fun q hq ↦ ⟨A, ⟨Set.Subset.rfl, u, hu⟩, Better.anti_right hAB hq.1⟩, not_lewis_iff.2
      ⟨{u}, ⟨Set.singleton_subset_iff.mpr hu, Set.singleton_nonempty u⟩, fun q hq hqu ↦ ?_⟩⟩
    obtain ⟨v, hv, hvr⟩ := hqu.1 (Set.mem_singleton u)
    exact hr v (hq.1 hv) hvr

-- (51)
theorem prefers_iff {φ : SProp W} {p S : Set W} (r : W → W → Prop)
    (hv : verifiers φ S = subStates (S ∩ p)) (hf : falsifiers φ S = subStates (S ∩ pᶜ)) :
    Better (Better r) (verifiers φ S) (falsifiers φ S) ↔ Better r (S ∩ p) (S ∩ pᶜ) := by
  rw [hv, hf, better_subStates_iff]

theorem prefers_modal_iff (r : W → W → Prop) (p S : Set W) (f : Force) :
    Better (Better r) (verifiers (f.modal (ofSet p)) S) (falsifiers (f.modal (ofSet p)) S) ↔
      Better (Better r) (verifiers (ofSet p) S) (falsifiers (ofSet p) S) := by
  cases f <;> simp only [Force.modal, verifiers_might, verifiers_must, falsifiers_might,
    falsifiers_must, verifiers_ofSet, falsifiers_ofSet]

/-! ### Emotive doxastics and dubitatives -/

/-- The uncertainty condition (54) demands that the complement has both verifiers and
falsifiers in the doxastic state. -/
def Uncertain (φ : SProp W) (S : Set W) : Prop :=
  (verifiers φ S).Nonempty ∧ (falsifiers φ S).Nonempty

/-- The doxastic assertion (53) says the complement holds at some world of the doxastic
state. -/
def Possible (φ : SProp W) (S : Set W) : Prop := ∃ w ∈ S, φ S w = .true

open Classical in
/-- `a hopes that φ` (55) presupposes uncertainty and asserts doxastic possibility and that the
verifiers are more desirable than the falsifiers. *fear* has the shape of `doubt` over the
desirability ordering. -/
noncomputable def hope (des : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) :
    W → Trivalent :=
  Trivalent.condEvent (fun w ↦ Uncertain φ (dox w))
    (fun w ↦ Possible φ (dox w) ∧
      Better (Better (des w)) (verifiers φ (dox w)) (falsifiers φ (dox w)))

open Classical in
/-- `a doubts that φ` (63) is as `hope`, with the falsifiers likelier than the verifiers. -/
noncomputable def doubt (prob : W → W → W → Prop) (dox : W → Set W) (φ : SProp W) :
    W → Trivalent :=
  Trivalent.condEvent (fun w ↦ Uncertain φ (dox w))
    (fun w ↦ Possible φ (dox w) ∧
      Better (Better (prob w)) (falsifiers φ (dox w)) (verifiers φ (dox w)))

section Values

variable {r : W → W → W → Prop} {dox : W → Set W} {φ : SProp W} {w : W}

theorem hope_eq_true_iff : hope r dox φ w = .true ↔ Uncertain φ (dox w) ∧ Possible φ (dox w) ∧
    Better (Better (r w)) (verifiers φ (dox w)) (falsifiers φ (dox w)) := by
  simp [hope]

theorem doubt_eq_true_iff : doubt r dox φ w = .true ↔ Uncertain φ (dox w) ∧ Possible φ (dox w) ∧
    Better (Better (r w)) (falsifiers φ (dox w)) (verifiers φ (dox w)) := by
  simp [doubt]

end Values

-- (58)
theorem uncertain_must_not_possible {p S : Set W} (hu : Uncertain (must (ofSet p)) S) :
    ¬ Possible (must (ofSet p)) S := fun ⟨_, _, hS⟩ ↦ by
  obtain ⟨X, hX, v, hv⟩ := falsifiers_must p S ▸ hu.2
  exact (hX hv).2 (ofSet_eq_true_iff.1 ((must_eq_true_iff.1 hS).2 v (hX hv).1))

/-- An emotive doxastic never makes an embedded necessity modal true: the doxastic assertion
contradicts the uncertainty condition (58). -/
theorem hope_must_ne_true (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W) :
    hope des dox (must (ofSet p)) w ≠ .true := fun h ↦
  let ⟨hu, hp, _⟩ := hope_eq_true_iff.1 h
  uncertain_must_not_possible hu hp

theorem doubt_must_ne_true (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : doubt prob dox (must (ofSet p)) w ≠ .true := fun h ↦
  let ⟨hu, hp, _⟩ := doubt_eq_true_iff.1 h
  uncertain_must_not_possible hu hp

-- (74)
theorem hope_compl_might_ne_true (des : W → W → W → Prop) (dox : W → Set W) (p : Set W)
    (w : W) : hope des dox (might (ofSet p))ᶜ w ≠ .true :=
  compl_might_ofSet p ▸ hope_must_ne_true des dox pᶜ w

theorem possible_might_iff (p S : Set W) :
    Possible (might (ofSet p)) S ↔ Possible (ofSet p) S := by
  simp only [Possible, might_eq_true_iff, ofSet_eq_true_iff]
  exact ⟨fun ⟨_, _, h⟩ ↦ h, fun ⟨w, hw, hp⟩ ↦ ⟨w, hw, w, hw, hp⟩⟩

open Classical in
/-- *Hope that might p* is *hope that p* (59): the verifiers, the falsifiers and the doxastic
assertion all coincide (57). -/
theorem hope_might (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    hope des dox (might (ofSet p)) = hope des dox (ofSet p) := by
  funext w
  simp only [hope, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

open Classical in
theorem doubt_might (prob : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    doubt prob dox (might (ofSet p)) = doubt prob dox (ofSet p) := by
  funext w
  simp only [doubt, Uncertain, verifiers_might, verifiers_ofSet, falsifiers_might,
    falsifiers_ofSet, possible_might_iff]

-- footnote 25: a necessity modal under negation is predicted licensed; (i) is judged marginal
theorem hope_compl_must (des : W → W → W → Prop) (dox : W → Set W) (p : Set W) :
    hope des dox (must (ofSet p))ᶜ = hope des dox (ofSet pᶜ) := by
  rw [compl_must_ofSet, hope_might]

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
noncomputable def Kind.entry : Kind → (W → W → W → Prop) → (W → Set W) → SProp W → W → Trivalent
  | .acceptance => fun _ dox => representational dox
  | .preferenceOriented => fun r _ => preferential r
  | .emotiveDoxastic => hope
  | .dubitative => doubt

/-- An epistemic of force `f` is licensed under a kind of attitude when some scale, doxastic
state, prejacent, and world make the embedding defined and true. -/
def Licensed (W : Type*) (k : Kind) (f : Force) : Prop :=
  ∃ (r : W → W → W → Prop) (dox : W → Set W) (p : Set W) (w : W),
    k.entry r dox (f.modal (ofSet p)) w = .true

theorem licensed_acceptance [Nontrivial W] (f : Force) :
    Licensed W .acceptance f := by
  obtain ⟨a, -, -⟩ := exists_pair_ne W
  refine ⟨fun _ _ _ => True, fun _ => Set.univ, Set.univ, a, ?_⟩
  cases f <;> simp [Kind.entry, Force.modal, representational]

theorem not_licensed_preferenceOriented (f : Force) : ¬ Licensed W .preferenceOriented f :=
  fun ⟨r, _, p, w, h⟩ => absurd ((preferential_modal_eq_undefined r f _ w).symm.trans h) (by decide)

theorem licensed_emotiveDoxastic_possibility [Nontrivial W] :
    Licensed W .emotiveDoxastic .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u = a ∧ v ≠ a, fun _ => Set.univ, {a}, a, ?_⟩
  show hope (fun _ u v => u = a ∧ v ≠ a) (fun _ => Set.univ) (might (ofSet {a})) a = .true
  refine hope_eq_true_iff.2 ⟨?_, ⟨a, trivial, might_eq_true_iff.2 ⟨a, trivial, by simp⟩⟩, ?_⟩
  · show Uncertain (might (ofSet {a})) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u = a ∧ v ≠ a) (verifiers (might (ofSet {a})) Set.univ)
      (falsifiers (might (ofSet {a})) Set.univ)
    rw [prefers_iff _ (verifiers_might _ _) (falsifiers_might _ _), Set.univ_inter,
      Set.univ_inter]
    exact ⟨fun v hv => ⟨a, rfl, rfl, hv⟩, not_lewis_iff.2 ⟨a, rfl, fun v hv h => hv h.1⟩⟩

theorem not_licensed_emotiveDoxastic_necessity : ¬ Licensed W .emotiveDoxastic .necessity :=
  fun ⟨r, dox, p, w, h⟩ => hope_must_ne_true r dox p w h

theorem licensed_dubitative_possibility [Nontrivial W] : Licensed W .dubitative .possibility := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne W
  refine ⟨fun _ u v => u ≠ a ∧ v = a, fun _ => Set.univ, {a}, a, ?_⟩
  show doubt (fun _ u v => u ≠ a ∧ v = a) (fun _ => Set.univ) (might (ofSet {a})) a = .true
  refine doubt_eq_true_iff.2 ⟨?_, ⟨a, trivial, might_eq_true_iff.2 ⟨a, trivial, by simp⟩⟩, ?_⟩
  · show Uncertain (might (ofSet {a})) Set.univ
    rw [Uncertain, verifiers_might, falsifiers_might, Set.univ_inter, Set.univ_inter]
    exact ⟨⟨{a}, Set.Subset.rfl, Set.singleton_nonempty a⟩,
      ⟨{b}, Set.singleton_subset_iff.mpr hab.symm, Set.singleton_nonempty b⟩⟩
  · show Better (Better fun u v => u ≠ a ∧ v = a) (falsifiers (might (ofSet {a})) Set.univ)
      (verifiers (might (ofSet {a})) Set.univ)
    rw [falsifiers_might, verifiers_might, better_subStates_iff, Set.univ_inter, Set.univ_inter]
    exact ⟨fun v hv => ⟨b, hab.symm, hab.symm, hv⟩,
      not_lewis_iff.2 ⟨b, hab.symm, fun v hv h => h.1 hv⟩⟩

theorem not_licensed_dubitative_necessity : ¬ Licensed W .dubitative .necessity :=
  fun ⟨r, dox, p, w, h⟩ => doubt_must_ne_true r dox p w h

-- Table 3
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

/-- An epistemic embedded under an attitude is judged acceptable exactly when the attitude's
class licenses its force. -/
theorem rows_track_licensing [Nontrivial W] :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" →
      r.feature? "modal_flavor" = some "epistemic" →
      ∀ c f, (r.feature? "attitude_class").bind AttitudeClass.ofString? = some c →
        (r.feature? "modal_force").bind Force.ofString? = some f →
        (r.judgment = .acceptable ↔ Licensed W c.kind f) := by
  simp only [licensed_iff]; decide +kernel

-- §5.1, (18), (20), (65)
theorem unacceptable_rows_subjunctive :
    ∀ r ∈ Examples.all, r.feature? "anchor" = some "attitude" → r.judgment = .unacceptable →
      r.feature? "mood" = none ∨ r.feature? "mood" = some "subjunctive" := by
  decide +kernel

end AnandHacquard2013
