module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Dynamic.Expectation
public import Linglib.Semantics.Modality.Background
public import Linglib.Semantics.Modality.DomainSemantics
public import Studies.Khoo2015

/-!
# Rudin (2025): Asserting epistemic modals

This file formalizes the Neo-Stalnakerian theory of assertion over Yalcin's domain semantics. An
assertor presents her state as one in which the sentence is known, a member of its
meta-intensionalization `MI`, and proposes the greatest refinement of the context in `MI`
(`IsAssertiveUpdate`), which exists exactly when `MI` is closed under unions. It is Stalnaker's
intersection for a sentence whose truth does not depend on the state and for *must*, and
Veltman's consistency test for *might*. A hearer may reject when no nonempty refinement of her
state lies in `MI` (`Compatible`), so *might p* is rejected exactly when `p` is while its truth
turns on the assertor's state, which fits Khoo's ratings. Under the ordering semantics asserting
*might p* adds `p` to the ordering source: Veltman's update with *normally p*.

## Main statements

* `isAssertiveUpdate_might`
* `exists_isAssertiveUpdate_iff`
* `compatible_might_iff_compatible_ofProp`
* `predicts_khoo_ratings`
* `toExpState_mightOrdUpdate`

## Implementation notes

The two versions share their definitions over a projection `b : S → Set W` to the modal base,
`id` or `OrdState.base`. The greatest refinement renders the paper's gloss of its update
condition, removing no world not needed to reach `MI`. Khoo's vignettes are two worlds, the
assertor's evidence leaving both open and the participant knowing the actual one. The ordering
*might* update assumes a finite frame, the limit assumption.

## Errata

* (27b), (28), (54b) and (69c) omit the absurd state, which every `MI` contains (`MI_might`);
  compatibility asks for a nonempty refinement, so no prediction changes.
* Conservativity (17) compares denotations world by world. A commensurate update for a contingent
  `p` guarantees *must p*, false at an unsettled context, so (15) assigns `p` no update
  (`not_conservative_of_commensurate`); informational consequence repairs this
  (`IsAssertiveUpdate.informationalConsequence`).
* Ordering propositions overlapping the prejacent can leave a non-prejacent world best, against
  the argument for (64), so its update is not commensurate (`not_commensurate_mustOrdUpdate`).

## References

* [rudin-2025a]
* [stalnaker-1978]
* [veltman-1996]
* [yalcin-2007]
* [khoo-2015]
* [kratzer-1981]
* [portner-2007]
-/

@[expose] public section

namespace Rudin2025a

open DynamicSemantics DomainSemantics Sentence Modality ModalLogic SetRel

variable {W : Type*}

/-! ### The machinery of assertion -/

section Machinery

variable {S : Type*} (b : S → Set W)

/-- The meta-intensionalization of a sentence consists of the states in which it is known: those
at every world of whose modal base it is true relative to the state itself. -/
def MI (s : S → W → Prop) : Set S := {i | ∀ w ∈ b i, s i w}

/-- A context is compatible with a sentence when some refinement of it, a state with a smaller
modal base, has a nonempty modal base and lies in the meta-intensionalization. Rejection is
licensed exactly when the rejector's state is not compatible. -/
def Compatible (s : S → W → Prop) (c : S) : Prop :=
  ∃ c', b c' ⊆ b c ∧ (b c').Nonempty ∧ c' ∈ MI b s

/-- An update is commensurate with a sentence when it takes every compatible context into the
meta-intensionalization. -/
def Commensurate (s : S → W → Prop) (f : S → S) : Prop :=
  ∀ c, Compatible b s c → f c ∈ MI b s

variable {b}

theorem mem_MI_of_eq_empty (s : S → W → Prop) {i : S} (h : b i = ∅) : i ∈ MI b s := by
  simp [MI, h]

theorem compatible_of_mem {s : S → W → Prop} {c : S} (hc : (b c).Nonempty) (h : c ∈ MI b s) :
    Compatible b s c :=
  ⟨c, subset_rfl, hc, h⟩

end Machinery

/-! ### The simple version -/

section Simple

variable {p c i : Set W} {s s' : Sentence W} {f : CCP W}

theorem MI_id (s : Sentence W) : MI id s = {i | s.AcceptedIn i} := rfl

theorem MI_ofProp (p : Set W) : MI id (ofProp p) = Set.Iic p := rfl

theorem MI_might (p : Set W) : MI id (ofProp p).might = insert ∅ {i | (i ∩ p).Nonempty} :=
  Set.ext fun _ ↦ acceptedIn_might_iff _

theorem MI_must (φ : Sentence W) : MI id φ.must = MI id φ :=
  Set.ext fun _ ↦ acceptedIn_must_iff φ

theorem compatible_ofProp : Compatible id (ofProp p) c ↔ (c ∩ p).Nonempty := by
  refine ⟨fun ⟨_, hc', ⟨w, hw⟩, h⟩ ↦ ⟨w, hc' hw, h w hw⟩, fun ⟨w, hwc, hwp⟩ ↦ ?_⟩
  exact ⟨{w}, Set.singleton_subset_iff.2 hwc, Set.singleton_nonempty w,
    fun _ hv ↦ Set.mem_singleton_iff.1 hv ▸ hwp⟩

theorem compatible_might : Compatible id (ofProp p).might c ↔ (c ∩ p).Nonempty := by
  refine ⟨fun ⟨_, hc', ⟨w, hw⟩, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, hv, hvp⟩ := h w hw
    exact ⟨v, hc' hv, hvp⟩
  · exact compatible_of_mem (b := id) (h.mono Set.inter_subset_left) fun _ _ ↦ h

/-- A *might* claim is rejected exactly when its prejacent is: when the rejector knows the
prejacent false. -/
theorem compatible_might_iff_compatible_ofProp :
    Compatible id (ofProp p).might c ↔ Compatible id (ofProp p) c :=
  compatible_might.trans compatible_ofProp.symm

theorem not_compatible_ofProp : ¬ Compatible id (ofProp p) i ↔ i ∈ MI id (ofProp pᶜ) := by
  rw [compatible_ofProp, Set.not_nonempty_iff_eq_empty, MI_ofProp, Set.mem_Iic,
    Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty]

theorem dissociation {a r : Set W} (ha : (a ∩ p).Nonempty) (hr : r ⊆ pᶜ) :
    a ∈ MI id (ofProp p).might ∧ ¬ Compatible id (ofProp p).might r :=
  ⟨fun _ _ ↦ ha, compatible_might_iff_compatible_ofProp.not.2 (not_compatible_ofProp.2 hr)⟩

/-! ### Assertive update -/

/-- An update is the assertive update of a sentence when it takes each context to its greatest
refinement in the sentence's meta-intensionalization. -/
def IsAssertiveUpdate (s : Sentence W) (f : CCP W) : Prop :=
  ∀ c, IsGreatest (Set.Iic c ∩ MI id s) (f c)

theorem isGreatest_of_mem (h : c ∈ MI id s) : IsGreatest (Set.Iic c ∩ MI id s) c :=
  ⟨⟨Set.self_mem_Iic, h⟩, fun _ h ↦ h.1⟩

theorem isGreatest_empty_of_not_compatible (h : ¬ Compatible id s c) :
    IsGreatest (Set.Iic c ∩ MI id s) ∅ :=
  ⟨⟨Set.empty_subset c, mem_MI_of_eq_empty (b := id) s rfl⟩, fun c' hc' ↦
    (Set.not_nonempty_iff_eq_empty.1 fun hn ↦ h ⟨c', hc'.1, hn, hc'.2⟩).le⟩

theorem IsAssertiveUpdate.unique {g : CCP W} (hf : IsAssertiveUpdate s f)
    (hg : IsAssertiveUpdate s g) : f = g :=
  funext fun c ↦ (hf c).unique (hg c)

theorem IsAssertiveUpdate.commensurate (hf : IsAssertiveUpdate s f) : Commensurate id s f :=
  fun c _ ↦ (hf c).1.2

theorem IsAssertiveUpdate.eq_empty_of_not_compatible (hf : IsAssertiveUpdate s f)
    (h : ¬ Compatible id s c) : f c = ∅ :=
  (hf c).unique (isGreatest_empty_of_not_compatible h)

theorem IsAssertiveUpdate.informationalConsequence (hf : IsAssertiveUpdate s f)
    (h : ∀ c, Compatible id s c → f c ∈ MI id s') : InformationalConsequence [s] s' := by
  refine informationalConsequence_singleton_iff.2 fun i (hi : i ∈ MI id s) ↦ ?_
  rcases i.eq_empty_or_nonempty with rfl | hne
  · exact mem_MI_of_eq_empty (b := id) s' rfl
  · exact (hf i).unique (isGreatest_of_mem hi) ▸ h i (compatible_of_mem hne hi)

/-- The assertive update exists exactly when the meta-intensionalization is closed under unions. -/
theorem exists_isAssertiveUpdate_iff :
    (∃ f, IsAssertiveUpdate s f) ↔ ∀ F ⊆ MI id s, ⋃₀ F ∈ MI id s := by
  refine ⟨fun ⟨f, hf⟩ F hF ↦ ?_, fun h ↦ ⟨fun c ↦ ⋃₀ (Set.Iic c ∩ MI id s), fun c ↦ ?_⟩⟩
  · have hle : ⋃₀ F ⊆ f (⋃₀ F) := Set.sUnion_subset fun A hA ↦
      (hf _).2 ⟨Set.subset_sUnion_of_mem hA, hF hA⟩
    exact hle.antisymm (hf _).1.1 ▸ (hf _).1.2
  · exact ⟨⟨Set.sUnion_subset fun _ h ↦ h.1, h _ Set.inter_subset_right⟩,
      fun _ h ↦ Set.subset_sUnion_of_mem h⟩

theorem not_exists_isAssertiveUpdate_must_sup (hp : p.Nonempty) (hp' : pᶜ.Nonempty) :
    ¬ ∃ f, IsAssertiveUpdate ((ofProp p).must ⊔ (ofProp pᶜ).must) f := by
  obtain ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ := And.intro hp hp'
  rw [exists_isAssertiveUpdate_iff]
  intro h
  have := h {{w}, {v}} (by simp [Set.insert_subset_iff, MI, must, ofProp, hw, em]) w (by simp)
  simp only [Set.sUnion_insert, Set.sUnion_singleton, Pi.sup_apply, sup_Prop_eq, must, ofProp,
    Set.mem_union, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff] at this
  tauto

theorem isAssertiveUpdate_up (p : Set W) : IsAssertiveUpdate (ofProp p) (CCP.up p) :=
  fun c ↦ Set.Iic_inter_Iic (a := c) (b := p) ▸ isGreatest_Iic

/-- Veltman's consistency test is the assertive update of *might p*. -/
theorem isAssertiveUpdate_might (p : Set W) :
    IsAssertiveUpdate (ofProp p).might (CCP.might (CCP.up p)) := fun c ↦ by
  by_cases h : (c ∩ p).Nonempty
  · rw [show CCP.might (CCP.up p) c = c from CCP.guard_pos h]
    exact isGreatest_of_mem fun _ _ ↦ h
  · rw [show CCP.might (CCP.up p) c = ∅ from CCP.guard_neg h]
    exact isGreatest_empty_of_not_compatible (compatible_might.not.2 h)

theorem isAssertiveUpdate_must (p : Set W) : IsAssertiveUpdate (ofProp p).must (CCP.up p) :=
  fun c ↦ MI_must (ofProp p) ▸ isAssertiveUpdate_up p c

/-- An update is conservative for a sentence when, whatever it guarantees on the compatible
contexts, the sentence entails world by world at each of them. -/
def Conservative (s : Sentence W) (f : CCP W) : Prop :=
  ∀ s' : Sentence W, (∀ c, Compatible id s c → f c ∈ MI id s') →
    ∀ c, Compatible id s c → s c ≤ s' c

theorem not_conservative_of_commensurate (hp : p.Nonempty) (hp' : pᶜ.Nonempty)
    (hf : Commensurate id (ofProp p) f) : ¬ Conservative (ofProp p) f := fun hcons ↦ by
  obtain ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ := And.intro hp hp'
  have hu : Compatible id (ofProp p) Set.univ := compatible_ofProp.2 ⟨w, trivial, hw⟩
  exact hv (hcons (ofProp p).must (fun c hc ↦ by rw [MI_must]; exact hf c hc) _ hu w hw v trivial)

/-! ### Khoo's experiment -/

/-- The sentence of each of Khoo's vignettes: the prejacent, or *might* of it. -/
def khooSentence : Khoo2015.Sentence → Sentence Bool
  | .control => ofProp {true}
  | .modal => (ofProp {true}).might

/-- The verdict on a cell of Khoo's design given a rejection condition: the claim is judged false
when it is false at the actual world relative to the assertor's state. -/
def KhooVerdict (reject : Sentence Bool → Prop) : Khoo2015.Sentence → Khoo2015.Response → Prop
  | s, .judgedFalse => ¬ khooSentence s .univ false
  | s, .rejection => reject (khooSentence s)

/-- The rejection condition of the theory fits every cell of Khoo's experiment, read against the
midpoint of the scale. -/
theorem predicts_khoo_ratings (s : Khoo2015.Sentence) (q : Khoo2015.Response) :
    (Khoo2015.midpoint : ℚ) < Khoo2015.mean s q ↔
      KhooVerdict (fun φ ↦ ¬ Compatible id φ {false}) s q := by
  cases s <;> cases q
  · exact iff_of_true (by decide +kernel) (by simp [KhooVerdict, khooSentence, ofProp])
  · exact iff_of_true (by decide +kernel) (by simp [KhooVerdict, khooSentence, compatible_ofProp])
  · exact iff_of_false (by decide +kernel) (by simp [KhooVerdict, khooSentence, might, ofProp])
  · exact iff_of_true (by decide +kernel) (by simp [KhooVerdict, khooSentence, compatible_might])

/-- Stalnakerian rejection, licensed when the rejector's state excludes every world at which the
claim is true, misses Khoo's rejection of the *might* claim. -/
theorem stalnakerian_mispredicts_khoo_ratings :
    ¬ ∀ s q, (Khoo2015.midpoint : ℚ) < Khoo2015.mean s q ↔
      KhooVerdict (fun φ ↦ Disjoint {false} {w | φ .univ w}) s q := by
  intro h
  have := (h .modal .rejection).1 (by decide +kernel)
  simp [KhooVerdict, khooSentence, might, ofProp] at this

end Simple

/-! ### The ordering version -/

/-- An epistemic state of the ordering version pairs a modal base with an ordering source. -/
structure OrdState (W : Type*) where
  /-- The worlds compatible with what the state-holder knows. -/
  base : Set W
  /-- The propositions that rank the worlds of the base. -/
  ordering : Set (W → Prop)

namespace OrdState

/-- The best worlds of a state are the worlds of its base that no world of the base betters
under its ordering source. -/
def best (i : OrdState W) : Set W := (premisePreorder i.ordering).minimals i.base

/-- A state as an expectation state, its ordering source inducing the pattern and its best worlds
the optimal worlds. -/
def toExpState (i : OrdState W) : ExpState W := ⟨i.base, premisePreorder i.ordering⟩

theorem best_singleton {d p : Set W} (h : (d ∩ p).Nonempty) : best ⟨d, {(· ∈ p)}⟩ = d ∩ p := by
  obtain ⟨w, hwd, hwp⟩ := h
  simpa [best, Set.sep_mem_eq] using
    Preorder.minimals_ofCriteria_eq (sat := fun w (q : W → Prop) ↦ q w) (criteria := {(· ∈ p)})
      (s := d) ⟨w, hwd, by simpa using hwp⟩

end OrdState

variable {p : Set W} {c : OrdState W}

/-- Under the ordering semantics *might p* is true when some best world is a `p`-world. -/
def mightOrd (p : Set W) : OrdState W → W → Prop := fun i _ ↦ (i.best ∩ p).Nonempty

/-- Under the ordering semantics *must p* is true when every best world is a `p`-world. -/
def mustOrd (p : Set W) : OrdState W → W → Prop := fun i _ ↦ i.best ⊆ p

theorem premisePreorder_insert (φ : W → Prop) (A : Set (W → Prop)) :
    premisePreorder (insert φ A) = ExpState.refine (premisePreorder A) φ :=
  Preorder.ext fun _ _ ↦ by simp only [Preorder.ofCriteria_le_iff, Set.forall_mem_insert,
    ExpState.refine_le, and_comm]

theorem compatible_mightOrd : Compatible OrdState.base (mightOrd p) c ↔ (c.base ∩ p).Nonempty := by
  refine ⟨fun ⟨_, hc', ⟨v, hv⟩, h⟩ ↦ ?_, fun h ↦
    ⟨⟨c.base, {(· ∈ p)}⟩, subset_rfl, h.mono Set.inter_subset_left, fun _ _ ↦ ?_⟩⟩
  · obtain ⟨m, hm, hmp⟩ := h v hv
    exact ⟨m, hc' (Preorder.minimals_subset _ _ hm), hmp⟩
  · rwa [mightOrd, OrdState.best_singleton h, Set.inter_assoc, Set.inter_self]

open scoped Classical in
/-- The update of *might p* adds `p` to the ordering source of a compatible context and
otherwise empties the modal base. -/
noncomputable def mightOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then ⟨c.base, insert (· ∈ p) c.ordering⟩ else ⟨∅, c.ordering⟩

/-- On a compatible context the update of *might p* is Veltman's update with *normally p*, the
promotion of Portner's To-Do List, on the epistemic ordering source. -/
theorem toExpState_mightOrdUpdate (h : (c.base ∩ p).Nonempty) :
    (mightOrdUpdate p c).toExpState = c.toExpState.promote (· ∈ p) := by
  rw [mightOrdUpdate, ite_eq_left h]
  exact congrArg (ExpState.mk _) (premisePreorder_insert _ _)

theorem commensurate_mightOrdUpdate [Finite W] (p : Set W) :
    Commensurate OrdState.base (mightOrd p) (mightOrdUpdate p) := by
  intro c hc _ _
  have h := compatible_mightOrd.1 hc
  obtain ⟨m, hm⟩ := Preorder.minimals_nonempty (premisePreorder (insert (· ∈ p) c.ordering))
    (s := c.base ∩ p) h
  rw [mightOrdUpdate, ite_eq_left h]
  refine ⟨m, ?_, (Preorder.minimals_subset _ _ hm).2⟩
  rw [Preorder.mem_minimals_iff] at hm
  exact (Preorder.mem_minimals_iff (p := premisePreorder _)).2
    ⟨hm.1.1, fun v hv hvm ↦ hm.2 ⟨hv, hvm (· ∈ p) (Set.mem_insert _ _) hm.1.2⟩ hvm⟩

/-! ### *must* under the ordering semantics -/

open scoped Classical in
/-- The update of *must p* adds `p` to the ordering source of a compatible context and
removes the propositions disjoint from `p`, and otherwise empties the modal base. -/
noncomputable def mustOrdUpdate (p : Set W) (c : OrdState W) : OrdState W :=
  if (c.base ∩ p).Nonempty then
    ⟨c.base, insert (· ∈ p) {q ∈ c.ordering | ∃ w ∈ p, q w}⟩
  else ⟨∅, c.ordering⟩

theorem mk_singleton_mem_MI_mustOrd {d : Set W} (h : (d ∩ p).Nonempty) :
    (⟨d, {(· ∈ p)}⟩ : OrdState W) ∈ MI OrdState.base (mustOrd p) :=
  fun _ _ ↦ (OrdState.best_singleton h).trans_subset Set.inter_subset_right

theorem compatible_mustOrd [Finite W] :
    Compatible OrdState.base (mustOrd p) c ↔ (c.base ∩ p).Nonempty := by
  refine ⟨fun ⟨c', hc', ⟨v, hv⟩, h⟩ ↦ ?_, fun h ↦ ⟨⟨c.base, {(· ∈ p)}⟩, subset_rfl,
    h.mono Set.inter_subset_left, mk_singleton_mem_MI_mustOrd h⟩⟩
  obtain ⟨m, hm⟩ := Preorder.minimals_nonempty (premisePreorder c'.ordering) (s := c'.base) ⟨v, hv⟩
  exact ⟨m, hc' (Preorder.minimals_subset _ _ hm), h v hv hm⟩

/-- Decide a claim about a three-world state by unfolding the operators. -/
local macro "decide_states" : tactic =>
  `(tactic| (simp only [MI, mustOrd, OrdState.best, Preorder.mem_minimals_iff,
      premisePreorder, Preorder.ofCriteria_le_iff,
      Set.mem_ofPred_eq, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.subset_def,
      Set.mem_inter_iff, Set.Nonempty, forall_eq_or_imp, forall_eq, Set.mem_empty_iff_false,
      false_implies, implies_true, true_and, and_true, forall_const]; decide))

theorem must_needs_prejacent :
    (⟨Set.univ, ∅⟩ : OrdState (Fin 3)) ∉ MI OrdState.base (mustOrd {0, 1}) ∧
      (⟨Set.univ, {(· ∈ ({0, 1} : Set (Fin 3)))}⟩ : OrdState (Fin 3)) ∈
        MI OrdState.base (mustOrd {0, 1}) := by
  decide_states

theorem must_needs_removal :
    (⟨Set.univ, {(· ∈ ({0, 1} : Set (Fin 3))), (· ∈ ({2} : Set (Fin 3)))}⟩ : OrdState (Fin 3)) ∉
      MI OrdState.base (mustOrd {0, 1}) := by
  decide_states

theorem mustOrdUpdate_removal :
    mustOrdUpdate ({0, 1} : Set (Fin 3)) ⟨Set.univ, {(· ∈ ({2} : Set (Fin 3)))}⟩ ∈
      MI OrdState.base (mustOrd {0, 1}) := by
  rw [mustOrdUpdate, ite_eq_left ⟨0, Set.mem_univ _, by simp⟩,
    Set.sep_eq_empty_iff_mem_false.2 (by simp), insert_empty_eq]
  exact must_needs_prejacent.2

theorem not_commensurate_mustOrdUpdate :
    ¬ Commensurate OrdState.base (mustOrd ({0, 1} : Set (Fin 3))) (mustOrdUpdate {0, 1}) := by
  intro h
  have hc := h ⟨Set.univ, {(· ∈ ({1, 2} : Set (Fin 3))), (· ∈ ({0, 2} : Set (Fin 3)))}⟩
    (compatible_mustOrd.2 ⟨0, Set.mem_univ _, by simp⟩)
  rw [mustOrdUpdate, ite_eq_left ⟨0, Set.mem_univ _, by simp⟩,
    Set.sep_eq_self_iff_mem_true.2 (by simp)] at hc
  revert hc
  decide_states

/-! ### The relational semantics -/

theorem MI_diamond_eq_MI_might {R : Set W → SetRel W W} (hR : ∀ i, ∀ w ∈ i, {v | w ~[R i] v} = i)
    (p : Set W) : MI id (fun i ↦ ◇[R i] (· ∈ p)) = MI id (ofProp p).might :=
  Set.ext fun i ↦ forall₂_congr fun w hw ↦
    exists_congr fun v ↦ and_congr_left' (Set.ext_iff.1 (hR i w hw) v)

theorem MI_relational_eq_MI_mightOrd {f : OrdState W → W → Set W}
    {g : OrdState W → W → Set (W → Prop)} (hf : ∀ i, ∀ w ∈ i.base, f i w = i.base)
    (hg : ∀ i, ∀ w ∈ i.base, g i w = i.ordering) (p : Set W) :
    MI OrdState.base (fun i w ↦ ((premisePreorder (g i w)).minimals (f i w) ∩ p).Nonempty) =
      MI OrdState.base (mightOrd p) :=
  Set.ext fun i ↦ forall₂_congr fun w hw ↦ by
    simp only [mightOrd, OrdState.best, hf i w hw, hg i w hw]

end Rudin2025a
