module

public import Mathlib.Data.PFun
public import Linglib.Semantics.Dynamic.Consequence
public import Linglib.Semantics.Presupposition.Context

/-!
# Partial updates

A partial update `PartialUpdate α := α →. α` is a partial function on states, and a state admits
the update when the update is defined there. Heim's context change potentials are the partial
updates of sets of worlds (`CCP.Partial`), whose domain condition is the presupposition, so that
Karttunen's satisfaction law for conjunction is the domain condition of composition and holds by
construction. A trivalent proposition gives the update defined on the contexts where it is
defined throughout, and under this update the filtering connectives, Peters' Middle Kleene
connectives, are the admittance conditions of the dynamic connectives. More strongly, the update
map is an isomorphism from trivalent propositions to the updates it reaches, carrying the constant
truth, Peters' conjunction and the Weak Kleene difference, disjunction and conjunction to the null
update, sequencing, difference, union and intersection ([george-2014] §2). Every update built
from these operations out of trivalentisable ones is therefore trivalentisable, and Heim's
connectives are Peters'.

## Main definitions

* `PartialUpdate.seq`: sequencing, the composition of partial functions.
* `PartialUpdate.IsEliminative`: Heim's Principle (A), that an update never adds information.
* `PartialUpdate.supports`: a state supports an update of which it is a fixed point.
* `PartialUpdate.Presupposes`: every state admitting the first update supports the second.
* `CCP.Partial.ofTrivalent`: the update of a trivalent proposition.
* `CCP.Partial.neg`, `CCP.Partial.cond`, `CCP.Partial.disj`: Heim's negation and conditional,
  and the disjunction that updates its second disjunct with the negation of the first.
* `CCP.Partial.diff`, `CCP.Partial.union`, `CCP.Partial.inter`: the difference, union and
  intersection of updates, defined where both updates are.
* `CCP.Partial.IsTrivalentisable`: an update given by a trivalent proposition.
* `CCP.Partial.ofTrivalentEquiv`: trivalent propositions are the trivalentisable updates.

## Main results

* `PartialUpdate.admits_seq`: the satisfaction law.
* `PartialUpdate.seq_eq_kleisliComp`: sequencing is Kleisli composition for `Part`.
* `PartialUpdate.entails_bind_iff_seq_eq`: entailment is absorption under sequencing.
* `PartialUpdate.Presupposes.seq_right`: a presupposition of the second conjunct projects
  conditionalised on the first.
* `CCP.Partial.admits_seq_ofTrivalent`, `CCP.Partial.admits_cond_ofTrivalent`,
  `CCP.Partial.admits_disj_ofTrivalent`: the filtering connectives, derived.
* `CCP.Partial.ofTrivalent_injective`, `CCP.Partial.ofTrivalent_one`,
  `CCP.Partial.ofTrivalent_meetMiddle`, `CCP.Partial.ofTrivalent_diff`,
  `CCP.Partial.ofTrivalent_joinWeak`, `CCP.Partial.ofTrivalent_meetWeak`: the update map is an
  isomorphism of the trivalent operations onto the operations on updates.
* `CCP.Partial.ofTrivalent_neg`, `CCP.Partial.ofTrivalent_cond`,
  `CCP.Partial.ofTrivalent_joinMiddle`, `CCP.Partial.ofTrivalent_joinMiddle_eq_neg_seq_neg`:
  Heim's connectives, and both Beaver's disjunction and its De Morgan form, are Peters'.

## Implementation notes

The partiality is of the update and not of the points. The partial assignments of
`Dynamic/State.lean` encode referential growth rather than presupposition, the sense of partial
dynamic semantics in Haug's work, and the two kinds compose in `Dynamic/FileChange.lean`. Heim
gives context change potentials for negation, conjunction and the conditional only, and the
disjunction follows Beaver. [george-2014]'s error context `#` is the undefinedness of a `Part`, so
every update sends `#` to `#`; updates that recover from `#`, such as his (6a), are not
representable, but every trivalentisable update is of this kind.

## References

* [heim-1982]
* [heim-1983]
* [heim-1992]
* [karttunen-1974-presupposition]
* [beaver-2001]
* [beaver-krahmer-2001]
* [coppock-beaver-2015]
* [veltman-1996]
* [groenendijk-stokhof-1990]
* [moggi-1991]
* [shan-2001]
* [haug-2014]
* [george-2014]
-/

@[expose] public section

namespace DynamicSemantics

open Presupposition

/-- A partial update of states of type `α`. The domain condition is the presupposition;
`Part.Dom` is [heim-1983]'s admittance. -/
abbrev PartialUpdate (α : Type*) := α →. α

namespace PartialUpdate

variable {α : Type*} {φ ψ χ : PartialUpdate α} {s : α}

/-- `u.Admits s` says the update is defined at `s` ([heim-1983]'s "s admits u",
    [karttunen-1974-presupposition]'s satisfaction). This is `Part.Dom`. -/
def Admits (u : PartialUpdate α) (s : α) : Prop := (u s).Dom

/-- Total updates are partial updates with trivial presupposition. -/
def ofTotal (φ : α → α) : PartialUpdate α := fun s ↦ Part.some (φ s)

@[simp] theorem admits_ofTotal (φ : α → α) (s : α) :
    (ofTotal φ).Admits s := trivial

/-- Sequencing, dynamic conjunction, is `s[φ ∧ ψ] = s[φ][ψ]`. This is
    `PFun.comp`; the projection behavior of conjunction is the
    composition law of partial functions. -/
def seq (φ ψ : PartialUpdate α) : PartialUpdate α := ψ.comp φ

/-- Sequencing is Kleisli composition for the `Part` monad, since a partial update is
    definitionally a Kleisli arrow `α → Part α`. This is the partiality column of the effect
    view of dynamic semantics, beside the powerset column in `Collapse.lean` ([moggi-1991],
    [shan-2001]). -/
theorem seq_eq_kleisliComp (φ ψ : α → Part α) :
    (seq φ ψ : α → Part α) = φ >=> ψ := rfl

/-! ### Eliminativity -/

/-- A partial update is *eliminative* if its defined outputs are at least as informative as the
input ([heim-1982]'s Principle (A); [groenendijk-stokhof-1990]'s `↓`-direction). -/
def IsEliminative [LE α] (φ : PartialUpdate α) : Prop := ∀ s, ∀ s' ∈ φ s, s' ≤ s

theorem isEliminative_id [Preorder α] : IsEliminative (PFun.id α) :=
  fun _ _ h ↦ le_of_eq (Part.mem_some_iff.mp h)

theorem IsEliminative.seq [Preorder α] (hφ : φ.IsEliminative) (hψ : ψ.IsEliminative) :
    (seq φ ψ).IsEliminative := fun s s' h ↦ by
  obtain ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp h
  exact (hψ t s' hs').trans (hφ s t ht)

/-! ### Support and entailment -/

/-- `s` supports `φ` when the update changes nothing ([heim-1992]'s `c + φ = c`,
[veltman-1996]'s acceptance). -/
def supports (s : α) (φ : PartialUpdate α) : Prop := s ∈ φ s

theorem supports_iff_mem : supports s φ ↔ s ∈ φ s := Iff.rfl

theorem supports_iff_eq_some : supports s φ ↔ φ s = Part.some s := Part.eq_some_iff.symm

theorem supports.seq_apply (h : supports s φ) (ψ : PartialUpdate α) : seq φ ψ s = ψ s := by
  rw [seq, PFun.comp_apply, supports_iff_eq_some.1 h, Part.bind_some]

theorem supports_iff_isFixedPt :
    supports s φ ↔ Function.IsFixedPt (· >>= φ) (pure s : Part α) :=
  supports_iff_eq_some.trans <| by rw [Function.IsFixedPt, pure_bind]; rfl

/-- Dynamic entailment between partial updates, every defined update with `φ` supporting `ψ`
([veltman-1996]'s acceptance consequence; [heim-1982]'s entailment between file change
potentials), is `Entails` of their extensions along `Part.bind`. It is absorption, sequencing
`ψ` after `φ` changing nothing. -/
theorem entails_bind_iff_seq_eq : Entails [(· >>= φ)] (· >>= ψ) ↔ seq φ ψ = φ := by
  rw [entails_singleton_iff, seq_eq_kleisliComp]
  refine ⟨fun h ↦ funext fun s ↦ ?_, fun h ↦ funext fun x ↦ ?_⟩
  · simpa [Bind.kleisliRight] using congrFun h (pure s)
  · simp only [Function.comp_apply, bind_assoc]
    exact congrArg (x >>= ·) h

theorem entails_bind_iff : Entails [(· >>= φ)] (· >>= ψ) ↔ ∀ s, ∀ s' ∈ φ s, supports s' ψ := by
  rw [entails_bind_iff_seq_eq]
  refine ⟨fun h s s' hs' ↦ ?_, fun h ↦ funext fun s ↦ Part.ext fun t ↦ ?_⟩
  · have hs'' : s' ∈ seq φ ψ s := by rw [h]; exact hs'
    obtain ⟨t, ht, hst⟩ := Part.mem_bind_iff.mp hs''
    exact Part.mem_unique ht hs' ▸ hst
  · rw [seq, PFun.comp_apply, Part.mem_bind_iff]
    refine ⟨fun ⟨s', hs', ht⟩ ↦ ?_, fun ht ↦ ⟨t, ht, h s t ht⟩⟩
    rw [supports_iff_eq_some.1 (h s s' hs'), Part.mem_some_iff] at ht
    exact ht ▸ hs'

/-! ### Presupposition -/

/-- `φ` presupposes `ψ` when every state admitting `φ` supports `ψ`. This is [heim-1983]'s
presupposition when `ψ` is the update of a plain proposition (`presupposes_ofProp_iff`), and
[beaver-2001]'s presupposition between sentences. -/
def Presupposes (φ ψ : PartialUpdate α) : Prop := ∀ s, φ.Admits s → supports s ψ

theorem supports.admits (h : supports s φ) : φ.Admits s := Part.dom_iff_mem.2 ⟨s, h⟩

/-- Presupposition composes. -/
theorem Presupposes.trans (h₁ : Presupposes φ ψ) (h₂ : Presupposes ψ χ) : Presupposes φ χ :=
  fun s hs ↦ h₂ s (h₁ s hs).admits

theorem Presupposes.seq_left (h : Presupposes φ ψ) : Presupposes (seq φ χ) ψ :=
  fun s ⟨hs, _⟩ ↦ h s hs

/-! ### The satisfaction law -/

/-- The Karttunen satisfaction law ([karttunen-1974-presupposition]), that `s` admits `φ ∧ ψ`
    iff `s` admits `φ` and `s[φ]` admits `ψ`, holds by construction as the domain condition of
    `Part.bind`. -/
theorem admits_seq (φ ψ : PartialUpdate α) (s : α) :
    (seq φ ψ).Admits s ↔ ∃ h : φ.Admits s, ψ.Admits ((φ s).get h) :=
  Iff.rfl

theorem admits_seq_iff (φ ψ : PartialUpdate α) (s : α)
    (h : φ.Admits s) :
    (seq φ ψ).Admits s ↔ ψ.Admits ((φ s).get h) :=
  ⟨fun ⟨_, hb⟩ ↦ hb, fun hb ↦ ⟨h, hb⟩⟩

theorem _root_.PFun.image_comp {α β γ : Type*} (f : α →. β) (g : β →. γ) (s : Set α) :
    (g.comp f).image s = g.image (f.image s) := by
  ext c
  simp only [PFun.mem_image, PFun.comp_apply, Part.mem_bind_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hc⟩
    exact ⟨b, ⟨a, ha, hb⟩, hc⟩
  · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩
    exact ⟨a, ha, b, hb, hc⟩

/-- The states reachable after two updates in sequence are the image of the image
([beaver-krahmer-2001]'s §5.3). -/
theorem image_seq (φ ψ : PartialUpdate α) (s : Set α) :
    (seq φ ψ).image s = ψ.image (φ.image s) :=
  PFun.image_comp φ ψ s

end PartialUpdate

/-! ### Heim's partial context change potentials -/

/-- A partial context change potential is a partial update of sets of possibilities, the
partial variant of the `CCP` API. -/
abbrev CCP.Partial (S : Type*) := PartialUpdate (Set S)

namespace CCP.Partial

open PartialUpdate

variable {P W : Type*} {φ ψ χ : CCP.Partial P} {s : Set P}

/-- The Heimian update of a trivalent proposition is defined iff the proposition is defined
throughout the context, and keeps the worlds where it is true. This is the `update` relation of
[beaver-krahmer-2001] §5.3 read as a partial function (`mem_ofTrivalent`), and the context update
of [coppock-beaver-2015].

The whole-state domain condition is what separates admittance from per-world filtering (the
static update `CCP.up`). A context containing a single presupposition-failing world admits
nothing, rather than silently discarding the world. -/
def ofTrivalent (p : W → Trivalent) : CCP.Partial W :=
  fun s ↦ ⟨s ⊆ (Trivalent.gapExt p)ᶜ, fun _ ↦ {w ∈ s | p w = .true}⟩

theorem admits_ofTrivalent (p : W → Trivalent) (s : Set W) :
    (ofTrivalent p).Admits s ↔ s ⊆ (Trivalent.gapExt p)ᶜ := Iff.rfl

theorem admits_ofTrivalent_iff_disjoint_gapExt (p : W → Trivalent) (s : Set W) :
    (ofTrivalent p).Admits s ↔ Disjoint s (Trivalent.gapExt p) := by
  rw [admits_ofTrivalent, Set.subset_compl_iff_disjoint_right]

@[simp] theorem ofTrivalent_get (p : W → Trivalent) (s : Set W) (h : (ofTrivalent p s).Dom) :
    (ofTrivalent p s).get h = {w ∈ s | p w = .true} := rfl

theorem mem_ofTrivalent (p : W → Trivalent) (s t : Set W) :
    t ∈ ofTrivalent p s ↔ s ⊆ (Trivalent.gapExt p)ᶜ ∧ t = {w ∈ s | p w = .true} :=
  ⟨fun ⟨h, e⟩ ↦ ⟨h, e.symm⟩, fun ⟨h, e⟩ ↦ ⟨h, e.symm⟩⟩

theorem mem_ofTrivalent_self (p : W → Trivalent) (s : Set W) :
    s ∈ ofTrivalent p s ↔ ∀ w ∈ s, p w = .true := by
  refine ⟨fun ⟨_, e⟩ ↦ Set.sep_eq_self_iff_mem_true.1 e, fun h ↦ ⟨fun w hw ↦ ?_, ?_⟩⟩
  · simp [Trivalent.mem_compl_gapExt, Trivalent.mem_gapExt, h w hw]
  · exact Set.sep_eq_self_iff_mem_true.2 h

theorem ofTrivalent_congr {p q : W → Trivalent} {s : Set W} (h : ∀ w ∈ s, p w = q w) :
    ofTrivalent p s = ofTrivalent q s :=
  Part.ext' (forall₂_congr fun w hw ↦ by simp [h w hw])
    fun _ _ ↦ Set.ext fun w ↦ and_congr_right fun hw ↦
      show p w = .true ↔ q w = .true by rw [h w hw]

/-! ### Connectives -/

/-- Heim negation is `s[¬φ] = s \ s[φ]`, defined iff `s[φ]` is. -/
def neg (φ : CCP.Partial P) : CCP.Partial P := fun s ↦ (φ s).map (s \ ·)

/-- The Heim conditional is `s[if φ, ψ] = s \ (s[φ] \ s[φ][ψ])`, defined iff
    `s[φ]` and `s[φ][ψ]` are. -/
def cond (φ ψ : CCP.Partial P) : CCP.Partial P :=
  fun s ↦ (φ s).bind fun sφ ↦ (ψ sφ).map fun sφψ ↦ s \ (sφ \ sφψ)

/-- Disjunction, after [beaver-2001], is `s[φ ∨ ψ] = s[φ] ∪ (s \ s[φ])[ψ]`, evaluating its
second disjunct in the ¬φ local context. -/
def disj (φ ψ : CCP.Partial P) : CCP.Partial P :=
  fun s ↦ (φ s).bind fun sφ ↦ (ψ (s \ sφ)).map fun sψ ↦ sφ ∪ sψ

/-- The difference of updates is `s[φ \ ψ] = s[φ] \ s[ψ]`, defined iff both updates are
([george-2014], Definition 7). -/
def diff (φ ψ : CCP.Partial P) : CCP.Partial P := fun s ↦ φ s \ ψ s

/-- The union of updates is `s[φ ∪ ψ] = s[φ] ∪ s[ψ]`, defined iff both updates are
([george-2014], Definition 7). -/
def union (φ ψ : CCP.Partial P) : CCP.Partial P := fun s ↦ φ s ∪ ψ s

/-- The intersection of updates is `s[φ ∩ ψ] = s[φ] ∩ s[ψ]`, defined iff both updates are
([george-2014], Definition 7). -/
def inter (φ ψ : CCP.Partial P) : CCP.Partial P := fun s ↦ φ s ∩ ψ s

theorem admits_diff (φ ψ : CCP.Partial P) (s : Set P) :
    (diff φ ψ).Admits s ↔ φ.Admits s ∧ ψ.Admits s := exists_prop

theorem admits_union (φ ψ : CCP.Partial P) (s : Set P) :
    (union φ ψ).Admits s ↔ φ.Admits s ∧ ψ.Admits s := exists_prop

theorem admits_inter (φ ψ : CCP.Partial P) (s : Set P) :
    (inter φ ψ).Admits s ↔ φ.Admits s ∧ ψ.Admits s := exists_prop

/-- Heim negation is the difference from the null update ([george-2014], Definition 8). -/
theorem neg_eq_diff (φ : CCP.Partial P) : neg φ = diff (PFun.id _) φ :=
  funext fun s ↦ (Part.bind_some s _).symm

/-- The Heim conditional is `ε \ (φ \ (φ; ψ))` ([george-2014], Definition 8). -/
theorem cond_eq_diff (φ ψ : CCP.Partial P) :
    cond φ ψ = diff (PFun.id _) (diff φ (PartialUpdate.seq φ ψ)) := by
  funext s
  refine Part.ext' ?_ fun _ _ ↦ rfl
  exact ⟨fun ⟨h, h'⟩ ↦ ⟨trivial, h, h, h'⟩, fun ⟨_, h, _, h'⟩ ↦ ⟨h, h'⟩⟩

theorem cond_eq_neg_seq_neg (φ ψ : CCP.Partial P) :
    cond φ ψ = neg (PartialUpdate.seq φ (neg ψ)) := by
  funext s
  simp only [cond, neg, PartialUpdate.seq, PFun.comp_apply, Part.map_bind, Part.map_map]
  rfl

/-! ### Eliminativity -/

theorem isEliminative_ofTrivalent (p : W → Trivalent) :
    (ofTrivalent p).IsEliminative := fun _ _ h ↦ (Part.mem_mk_iff.mp h).2 ▸ Set.sep_subset _ _

theorem isEliminative_neg (φ : CCP.Partial P) : (neg φ).IsEliminative := fun _ _ h ↦ by
  obtain ⟨t, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact Set.sdiff_subset

theorem isEliminative_cond (φ ψ : CCP.Partial P) : (cond φ ψ).IsEliminative := fun _ _ h ↦ by
  obtain ⟨_, -, h⟩ := Part.mem_bind_iff.mp h
  obtain ⟨_, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact Set.sdiff_subset

@[simp] theorem admits_neg (φ : CCP.Partial P) (s : Set P) :
    (neg φ).Admits s ↔ φ.Admits s :=
  Iff.rfl

theorem admits_cond (φ ψ : CCP.Partial P) (s : Set P) :
    (cond φ ψ).Admits s ↔ ∃ h : φ.Admits s, ψ.Admits ((φ s).get h) :=
  Iff.rfl

theorem admits_disj (φ ψ : CCP.Partial P) (s : Set P) :
    (disj φ ψ).Admits s ↔
      ∃ h : φ.Admits s, ψ.Admits (s \ (φ s).get h) :=
  Iff.rfl

/-! ### Local contexts

The connectives evaluate their second argument in [karttunen-1974-presupposition]'s local
context (`Presupposition.Connective.localContext`): conjunction and the conditional in the
context updated with the first argument, disjunction in the context updated with its negation. -/

open Presupposition (Connective)

theorem admits_seq_ofTrivalent_iff (p : W → Trivalent) (ψ : CCP.Partial W) (s : Set W) :
    (PartialUpdate.seq (ofTrivalent p) ψ).Admits s ↔
      s ⊆ (Trivalent.gapExt p)ᶜ ∧ ψ.Admits (Connective.conj.localContext s (Trivalent.posExt p)) :=
  ⟨fun ⟨h, hψ⟩ ↦ ⟨h, hψ⟩, fun ⟨h, hψ⟩ ↦ ⟨h, hψ⟩⟩

theorem admits_cond_ofTrivalent_iff (p : W → Trivalent) (ψ : CCP.Partial W) (s : Set W) :
    (cond (ofTrivalent p) ψ).Admits s ↔
      s ⊆ (Trivalent.gapExt p)ᶜ ∧ ψ.Admits (Connective.cond.localContext s (Trivalent.posExt p)) :=
  admits_seq_ofTrivalent_iff p ψ s

theorem admits_disj_ofTrivalent_iff (p : W → Trivalent) (ψ : CCP.Partial W) (s : Set W) :
    (disj (ofTrivalent p) ψ).Admits s ↔
      s ⊆ (Trivalent.gapExt p)ᶜ ∧ ψ.Admits (Connective.disj.localContext s (Trivalent.posExt p)) := by
  have e : s \ {w ∈ s | p w = .true} = Connective.disj.localContext s (Trivalent.posExt p) :=
    Set.ext fun _ ↦ ⟨fun ⟨hs, hn⟩ ↦ ⟨hs, fun ha ↦ hn ⟨hs, ha⟩⟩, fun ⟨hs, hn⟩ ↦ ⟨hs, fun h ↦ hn h.2⟩⟩
  refine ⟨fun ⟨h, hψ⟩ ↦ ⟨h, ?_⟩, fun ⟨h, hψ⟩ ↦ ⟨h, ?_⟩⟩
  · rw [← e]; exact hψ
  · change ψ.Admits (s \ {w ∈ s | p w = .true}); rw [e]; exact hψ

/-! ### Filtering connectives, derived

Under `ofTrivalent`, the admittance conditions of the dynamic connectives are exactly the
definedness conditions of the filtering connectives, Peters' Middle Kleene connectives: both are
satisfaction in the local contexts (`Presupposition.subset_support_meetMiddle_iff` and its
siblings), so Karttunen filtering is the composition law of partial updates, not a
stipulation. -/

/-- Dynamic conjunction admits `s` iff the Middle Kleene conjunction is defined throughout it. -/
theorem admits_seq_ofTrivalent (p q : W → Trivalent) (s : Set W) :
    (PartialUpdate.seq (ofTrivalent p) (ofTrivalent q)).Admits s ↔
      s ⊆ (Trivalent.gapExt fun w ↦ (p w).meetMiddle (q w))ᶜ :=
  (admits_seq_ofTrivalent_iff p _ s).trans Presupposition.subset_support_meetMiddle_iff.symm

/-- The dynamic conditional admits `s` iff the Middle Kleene conditional is defined throughout
it. -/
theorem admits_cond_ofTrivalent (p q : W → Trivalent) (s : Set W) :
    (cond (ofTrivalent p) (ofTrivalent q)).Admits s ↔
      s ⊆ (Trivalent.gapExt fun w ↦ (p w)ᶜ.joinMiddle (q w))ᶜ :=
  (admits_cond_ofTrivalent_iff p _ s).trans Presupposition.subset_support_neg_joinMiddle_iff.symm

/-- Dynamic disjunction admits `s` iff the Middle Kleene disjunction is defined throughout it,
the ¬φ local context being Karttunen's negative-antecedent filtering. -/
theorem admits_disj_ofTrivalent (p q : W → Trivalent) (s : Set W) :
    (disj (ofTrivalent p) (ofTrivalent q)).Admits s ↔
      s ⊆ (Trivalent.gapExt fun w ↦ (p w).joinMiddle (q w))ᶜ :=
  (admits_disj_ofTrivalent_iff p _ s).trans Presupposition.subset_support_joinMiddle_iff.symm

/-! ### The update isomorphism

[george-2014]'s Proposition 1: the update map is injective (Remark 1) and carries the constant
truth, Peters' conjunction and the Weak Kleene difference `meetWeak p (-q)`, disjunction and
conjunction to the null update, sequencing, difference, union and intersection. The
trivalentisable updates are therefore closed under these operations (Corollary 1), and reading
Heim's connectives off their isomorphic images shows that they are Peters' (footnote 15). -/

/-- An update is trivalentisable when it is the update of a trivalent proposition
([george-2014], Definition 11). -/
def IsTrivalentisable (φ : CCP.Partial W) : Prop := φ ∈ Set.range ofTrivalent

theorem isTrivalentisable_ofTrivalent (p : W → Trivalent) : IsTrivalentisable (ofTrivalent p) :=
  ⟨p, rfl⟩

/-- Distinct trivalent propositions give distinct updates, as the update of a singleton context
recovers the value at its world ([george-2014], Remark 1). -/
theorem ofTrivalent_injective :
    Function.Injective (ofTrivalent : (W → Trivalent) → CCP.Partial W) := by
  intro p q h
  funext w
  have h₀ : ∀ r : W → Trivalent, (ofTrivalent r {w}).Dom ↔ ¬ r w = .undefined := fun r ↦ by
    simp [ofTrivalent, Trivalent.mem_compl_gapExt]
  have h₁ : ∀ r : W → Trivalent, {w} ∈ ofTrivalent r {w} ↔ r w = .true := fun r ↦ by
    simp [mem_ofTrivalent_self]
  refine Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · rw [← not_iff_not, ← h₀, ← h₀, h]
  · rw [← h₁, ← h₁, h]

/-- The constant truth gives the null update. -/
@[simp] theorem ofTrivalent_one : ofTrivalent ((fun _ ↦ .true) : W → Trivalent) = PFun.id (Set W) := by
  funext s
  exact Part.ext' (iff_of_true (fun w _ ↦ by simp) trivial) fun _ _ ↦ by simp [ofTrivalent]

/-- Peters' conjunction gives sequencing. -/
theorem ofTrivalent_meetMiddle (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ (p w).meetMiddle (q w)) =
      PartialUpdate.seq (ofTrivalent p) (ofTrivalent q) := by
  funext s
  refine Part.ext' (admits_seq_ofTrivalent p q s).symm fun _ _ ↦ ?_
  show {w ∈ s | _} = {w ∈ {w ∈ s | p w = .true} | q w = .true}
  ext w
  simp [and_assoc]

/-- An update of a pointwise Weak Kleene operation is defined where both operands' updates are. -/
theorem admits_ofTrivalent_weak {f : Trivalent → Trivalent → Trivalent}
    (hf : ∀ a b, f a b ≠ .undefined ↔ a ≠ .undefined ∧ b ≠ .undefined) (p q : W → Trivalent) (s : Set W) :
    (ofTrivalent fun w ↦ f (p w) (q w)).Admits s ↔
      (ofTrivalent p).Admits s ∧ (ofTrivalent q).Admits s := by
  simp only [admits_ofTrivalent, Set.subset_def, Trivalent.mem_compl_gapExt, Trivalent.mem_gapExt, hf]
  exact ⟨fun h ↦ ⟨fun w hw ↦ (h w hw).1, fun w hw ↦ (h w hw).2⟩,
    fun h w hw ↦ ⟨h.1 w hw, h.2 w hw⟩⟩

/-- The Weak Kleene difference gives the difference of updates. -/
theorem ofTrivalent_diff (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ Trivalent.meetWeak (p w) ((q w)ᶜ)) =
      diff (ofTrivalent p) (ofTrivalent q) := by
  funext s
  refine Part.ext' ((admits_ofTrivalent_weak (f := fun a b ↦ Trivalent.meetWeak a (bᶜ))
    (by decide) p q s).trans (admits_diff _ _ s).symm) fun h _ ↦ ?_
  simp only [diff, Part.sdiff_get_eq, ofTrivalent_get]
  ext w
  by_cases hw : w ∈ s
  · have hd : Trivalent.meetWeak (p w) ((q w)ᶜ) ≠ .undefined := h hw
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, hw, true_and]
    revert hd; generalize p w = a; generalize q w = b
    cases a <;> cases b <;> decide
  · simp [hw]

/-- Weak Kleene disjunction gives the union of updates. -/
theorem ofTrivalent_joinWeak (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ Trivalent.joinWeak (p w) (q w)) =
      union (ofTrivalent p) (ofTrivalent q) := by
  funext s
  refine Part.ext' ((admits_ofTrivalent_weak (f := Trivalent.joinWeak) (by decide) p q s).trans
    (admits_union _ _ s).symm) fun h _ ↦ ?_
  simp only [union, Part.union_get_eq, ofTrivalent_get]
  ext w
  by_cases hw : w ∈ s
  · have hd : Trivalent.joinWeak (p w) (q w) ≠ .undefined := h hw
    simp only [Set.mem_ofPred_eq, Set.mem_union, hw, true_and]
    revert hd; generalize p w = a; generalize q w = b
    cases a <;> cases b <;> decide
  · simp [hw]

/-- Weak Kleene conjunction gives the intersection of updates. -/
theorem ofTrivalent_meetWeak (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ Trivalent.meetWeak (p w) (q w)) =
      inter (ofTrivalent p) (ofTrivalent q) := by
  funext s
  refine Part.ext' ((admits_ofTrivalent_weak (f := Trivalent.meetWeak) (by decide) p q s).trans
    (admits_inter _ _ s).symm) fun _ _ ↦ ?_
  simp only [inter, Part.inter_get_eq, ofTrivalent_get]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_sep_iff, Trivalent.meetWeak_eq_true_iff]
  tauto

/-- Heim negation is Kleene negation, read off the isomorphic images of `ε \ φ`
([george-2014], footnote 15). -/
theorem ofTrivalent_neg (p : W → Trivalent) :
    ofTrivalent (fun w ↦ (p w)ᶜ) = neg (ofTrivalent p) := by
  rw [neg_eq_diff, ← ofTrivalent_one, ← ofTrivalent_diff]
  simp only [Pi.one_apply, Trivalent.meetWeak_true_left]

/-- The Heim conditional is Peters' conditional, read off the isomorphic images of
`ε \ (φ \ (φ; ψ))` ([george-2014], footnote 15). -/
theorem ofTrivalent_cond (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ ((p w)ᶜ).joinMiddle (q w)) = cond (ofTrivalent p) (ofTrivalent q) := by
  rw [cond_eq_diff, ← ofTrivalent_meetMiddle, ← ofTrivalent_diff, ← ofTrivalent_one,
    ← ofTrivalent_diff]
  congr 1; funext w
  generalize p w = a; generalize q w = b
  cases a <;> cases b <;> rfl

/-- Beaver's disjunction is Peters' disjunction. It is not built from the toolbox, so this is
proved directly; `ofTrivalent_joinMiddle_eq_neg_seq_neg` reads off the De Morgan form. -/
theorem ofTrivalent_joinMiddle (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ (p w).joinMiddle (q w)) = disj (ofTrivalent p) (ofTrivalent q) := by
  funext s
  refine Part.ext' (admits_disj_ofTrivalent p q s).symm fun h _ ↦ ?_
  show {w ∈ s | _} = {w ∈ s | p w = .true} ∪ {w ∈ s \ {w ∈ s | p w = .true} | q w = .true}
  ext w
  by_cases hw : w ∈ s
  · have hd : (p w).joinMiddle (q w) ≠ .undefined := h hw
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, hw, true_and]
    revert hd; generalize p w = a; generalize q w = b
    cases a <;> cases b <;> decide
  · simp [hw]

/-- [george-2014]'s disjunction `¬(¬φ; ¬ψ)` (Definition 9) is Peters' disjunction, read off the
isomorphic images (footnote 15). -/
theorem ofTrivalent_joinMiddle_eq_neg_seq_neg (p q : W → Trivalent) :
    ofTrivalent (fun w ↦ (p w).joinMiddle (q w)) =
      neg (PartialUpdate.seq (neg (ofTrivalent p)) (neg (ofTrivalent q))) := by
  rw [← ofTrivalent_neg, ← ofTrivalent_neg, ← ofTrivalent_meetMiddle, ← ofTrivalent_neg]
  congr 1; funext w
  generalize p w = a; generalize q w = b
  cases a <;> cases b <;> rfl

/-- On trivalentisable updates Beaver's disjunction is the De Morgan disjunction of
[george-2014]'s Definition 9; on arbitrary updates the two differ. -/
theorem disj_ofTrivalent (p q : W → Trivalent) :
    disj (ofTrivalent p) (ofTrivalent q) =
      neg (PartialUpdate.seq (neg (ofTrivalent p)) (neg (ofTrivalent q))) := by
  rw [← ofTrivalent_joinMiddle, ofTrivalent_joinMiddle_eq_neg_seq_neg]

/-- Trivalent propositions are the trivalentisable updates. -/
noncomputable def ofTrivalentEquiv : (W → Trivalent) ≃ Set.range (ofTrivalent (W := W)) :=
  Equiv.ofInjective _ ofTrivalent_injective

section Closure

/-! The trivalentisable updates contain the null update and are closed under the operations of
the toolbox ([george-2014], Corollary 1) and Heim's connectives (Proposition 2). -/

variable {φ ψ : CCP.Partial W}

theorem isTrivalentisable_id : IsTrivalentisable (PFun.id (Set W)) := ⟨(fun _ ↦ .true), ofTrivalent_one⟩

theorem IsTrivalentisable.seq (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (PartialUpdate.seq φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_meetMiddle p q⟩

theorem IsTrivalentisable.diff (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (diff φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_diff p q⟩

theorem IsTrivalentisable.union (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (union φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_joinWeak p q⟩

theorem IsTrivalentisable.inter (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (inter φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_meetWeak p q⟩

theorem IsTrivalentisable.neg (hφ : IsTrivalentisable φ) : IsTrivalentisable (neg φ) := by
  obtain ⟨p, rfl⟩ := hφ
  exact ⟨_, ofTrivalent_neg p⟩

theorem IsTrivalentisable.cond (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (cond φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_cond p q⟩

theorem IsTrivalentisable.disj (hφ : IsTrivalentisable φ) (hψ : IsTrivalentisable ψ) :
    IsTrivalentisable (disj φ ψ) := by
  obtain ⟨p, rfl⟩ := hφ; obtain ⟨q, rfl⟩ := hψ
  exact ⟨_, ofTrivalent_joinMiddle p q⟩

end Closure

/-! ### Presupposition -/

theorem presupposes_ofProp_iff (φ : CCP.Partial W) (p : W → Prop) [DecidablePred p] :
    PartialUpdate.Presupposes φ (ofTrivalent fun w ↦ Trivalent.ofProp (p w)) ↔
      ∀ c, φ.Admits c → ∀ w ∈ c, p w := by
  simp only [PartialUpdate.Presupposes, supports, mem_ofTrivalent_self, Trivalent.ofProp_eq_true_iff]

theorem presupposes_ofTrivalent (p : W → Trivalent) :
    PartialUpdate.Presupposes (ofTrivalent p) (ofTrivalent fun w ↦ Trivalent.ofProp (p w ≠ .undefined)) :=
  (presupposes_ofProp_iff _ _).2 fun _ h _ hw ↦ (admits_ofTrivalent _ _).1 h hw

end CCP.Partial

/-! ### Projection

Negation and the first argument of the conjunction and the conditional pass a presupposition
on unchanged; the second argument passes it on conditionalised on the first. -/

namespace PartialUpdate.Presupposes

variable {P : Type*} {φ ψ χ : CCP.Partial P}

theorem neg (h : Presupposes φ ψ) : Presupposes (CCP.Partial.neg φ) ψ := h

theorem cond_left (h : Presupposes φ ψ) : Presupposes (CCP.Partial.cond φ χ) ψ :=
  fun s ⟨hs, _⟩ ↦ h s hs

/-- A presupposition of the second conjunct projects conditionalised on the first. -/
theorem seq_right (h : Presupposes φ ψ) : Presupposes (seq χ φ) (CCP.Partial.cond χ ψ) := by
  rintro s ⟨hχ, hφ⟩
  exact Part.mem_bind_iff.2 ⟨_, Part.get_mem hχ, (Part.mem_map_iff _).2 ⟨_, h _ hφ, by simp⟩⟩

theorem cond_right (h : Presupposes φ ψ) :
    Presupposes (CCP.Partial.cond χ φ) (CCP.Partial.cond χ ψ) :=
  fun s hs ↦ h.seq_right s hs

end PartialUpdate.Presupposes

end DynamicSemantics
