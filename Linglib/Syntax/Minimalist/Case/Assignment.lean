/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Category
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Case assignment by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain, innermost first,
each phase head's domain with its own high, low and elsewhere cases, and functional heads value
case under [Agree](##Minimalist.agree) on the closest caseless NP they reach, which is
[what a relativized probe finds](##Minimalist.agree_eq_search); a value once assigned is kept, so a
dative valued in the verb phrase survives the clause. A language's case assigners are the rules of
each phase head's domain and the case each head values under Agree, so configurational, Agree-based
and hybrid systems are points in one space. Assignment is [a fold](##Minimalist.assignBy) over
[domains](##Minimalist.CaseDomain); `CaseAssigners.assign` builds them from NPs placed by hand, and
`Case/SyntacticObject.lean` reads them off an object.

## Implementation notes

A value once assigned is never replaced. Baker and Vinokurova let a later domain re-mark an NP and
spell out its innermost case (their (15)), which agrees with this wherever the outer case is not
overt.

## References

* [baker-vinokurova-2010]
* [baker-2015]
* [chomsky-2000], [chomsky-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

open Case CaseRule DependentCase FeatureSlot

/-! ### Agree -/

section Agree

variable {ι κ : Type*} [DecidableEq ι] (lt : ι → ι → Prop) [DecidableRel lt]

/-- Agree into the domain `D`: the closest goal in `D`, the goals being its unvalued NPs, is valued
with `v`. Goals neither of which c-commands the other are all closest, and all are valued. -/
def agree (v : κ) (D : Finset ι) (s : ι → FeatureSlot κ) : ι → FeatureSlot κ :=
  (CaseRule.inOrder [v]).passUnvalued lt D s

variable {lt} {D : Finset ι} {s t : ι → FeatureSlot κ} {x : ι} {v : κ} {xs : List ι}

/-- Agree values the goals with no goal above them, and nothing else. -/
theorem agree_apply : agree lt v D s x =
    if x ∈ unvaluedIn D s ∧ ∀ z ∈ unvaluedIn D s, ¬ lt z x then .valued v else s x := by
  by_cases hx : x ∈ unvaluedIn D s
  · have hs := (FeatureSlot.mem_unvaluedIn.1 hx).2
    rw [agree, CaseRule.passUnvalued_of_mem hx]
    by_cases hz : ∀ z ∈ unvaluedIn D s, ¬ lt z x
    · rw [Finset.filter_eq_empty_iff.2 hz, ite_eq_left ⟨hx, hz⟩]
      rfl
    · have hne : ((unvaluedIn D s).filter (lt · x)).card ≠ 0 := by
        rw [Finset.card_ne_zero]
        push Not at hz
        obtain ⟨z, hz, hzx⟩ := hz
        exact ⟨z, Finset.mem_filter.2 ⟨hz, hzx⟩⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hk, ite_eq_right fun h ↦ hz h.2, hs]
      simp [CaseRule.inOrder]
  · rw [agree, CaseRule.passUnvalued_of_notMem hx, ite_eq_right fun h ↦ hx h.1]

theorem extends_agree : Extends {v} s (agree lt v D s) :=
  (CaseRule.extends_inOrder [v] D s).mono fun _ hw ↦ by simpa using hw

/-- Agree is monotone in the unvalued nominals: what stays unvalued from a more valued state stays
unvalued from a less valued one. -/
theorem agree_eq_unvalued_of_forall (h : ∀ x, t x = .unvalued → s x = .unvalued)
    (ht : agree lt v D t x = .unvalued) : agree lt v D s x = .unvalued := by
  rw [agree_apply] at ht ⊢
  split_ifs at ht with ht'
  · simp at ht
  by_cases hx : x ∈ D
  · have htx : t x = .unvalued := ht
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ unvaluedIn D t, lt z x := by
      by_contra hno
      push Not at hno
      exact ht' ⟨FeatureSlot.mem_unvaluedIn.2 ⟨hx, htx⟩, hno⟩
    have hzs : z ∈ unvaluedIn D s :=
      mem_unvaluedIn.2 ⟨(mem_unvaluedIn.1 hz).1, h z (mem_unvaluedIn.1 hz).2⟩
    rw [ite_eq_right fun hs ↦ hs.2 z hzs hzx]
    exact h x htx
  · rw [ite_eq_right fun hs ↦ hx (FeatureSlot.mem_unvaluedIn.1 hs.1).1]
    exact h x ht

/-- Agree commutes with renaming the values. -/
theorem map_agree {κ' : Type*} (g : κ → κ') (x : ι) :
    (agree lt v D s x).map g = agree lt (g v) D (fun x ↦ (s x).map g) x := by
  simp only [agree_apply, FeatureSlot.unvaluedIn_map]
  split_ifs <;> rfl

/-- `agree` is Agree: a probe relativized to unvalued NPs, the activity condition of [chomsky-2000],
searches the domain in c-command order, and the goal it finds is valued while every other NP is left
as it is; if it finds none, nothing changes, the failed Agree of [preminger-2014]. -/
theorem agree_eq_search [Std.Asymm lt] (hxs : xs.Pairwise lt) :
    agree lt v xs.toFinset s = ((Probe.relativized fun x ↦ s x = .unvalued).search xs).elim s
      (Function.update s · (.valued v)) := by
  have hnd : xs.Nodup := List.Pairwise.imp (fun {a b} (h : lt a b) ↦ by
    rintro rfl
    exact asymm h h) hxs
  set G := xs.filter (s · = .unvalued) with hG
  have hsearch : (Probe.relativized fun x ↦ s x = .unvalued).search xs = G.head? := by
    simp [Probe.search, hG, List.head?_filter]
  have hgoals : unvaluedIn xs.toFinset s = G.toFinset := by ext x; simp [hG]
  rw [hsearch]
  funext x
  by_cases hx : x ∈ G
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hsx : s G[i] = .unvalued := by simpa using (List.mem_filter.1 hx).2
    rw [agree, CaseRule.passUnvalued_getElem _ (hxs.filter _) hgoals i hi]
    cases i with
    | zero =>
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi]
      simp [CaseRule.inOrder]
    | succ k =>
      have hpos : 0 < G.length := by omega
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
      have hne : G[k + 1] ≠ G[0] := fun e ↦ by
        simpa using (hnd.filter _).getElem_inj_iff.1 e
      simp [CaseRule.inOrder, Function.update_of_ne hne, hsx]
  · have hnm : x ∉ unvaluedIn xs.toFinset s := fun h ↦ hx (by simpa [hG] using h)
    rw [agree, CaseRule.passUnvalued_of_notMem hnm]
    rcases hl : G.head? with _ | g
    · rfl
    · have hne : x ≠ g := by
        rintro rfl
        exact hx (List.mem_of_mem_head? hl)
      exact (Function.update_of_ne hne _ _).symm

end Agree

/-! ### Positions set by hand -/

/-- An NP placed by hand: the case slot it enters with, the phase whose domain merges it, and the
    phase it shifts into, if any. -/
structure PhasedNP where
  /-- The case slot the NP enters with: valued by a lexical head, absent for an NP that bears no
  case, such as PRO, which competes for dependent case without bearing it, and unvalued
  otherwise. -/
  case : FeatureSlot Case := .unvalued
  /-- The phase whose domain merges the NP. -/
  phase : Cat := .C
  /-- The phase whose domain the NP shifts into, if any. -/
  shiftsTo : Option Cat := none
  deriving DecidableEq, Repr

/-- The NP is seen by the domain of `c` when it merges or shifts there. -/
def PhasedNP.Visible (np : PhasedNP) (c : Cat) : Prop := np.phase = c ∨ np.shiftsTo = some c

instance (np : PhasedNP) (c : Cat) : Decidable (np.Visible c) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The phase whose elsewhere case the NP falls back on: where it shifts to, or where it merges. -/
def PhasedNP.spellOut (np : PhasedNP) : Cat := np.shiftsTo.getD np.phase

/-! ### Case assigners -/

/-- The case assigners of a language, in both modalities of [baker-vinokurova-2010]: the
    dependent-case rules of the domain of each phase head, and the case each head values under
    Agree. -/
structure CaseAssigners where
  /-- The dependent-case rules of the domain of each phase head. -/
  rules : Cat → Rules := fun _ ↦ {}
  /-- The case each head values under Agree, if any. -/
  agreeCase : Cat → Option Case := fun _ ↦ none

/-! ### Assignment over domains -/

/-- One domain of case assignment: c-command among its NPs, its dependent rule and the NPs that rule
reads and values, its probes with the value each gives and the NPs each reaches, and its elsewhere
rule and the NPs that rule values. -/
structure CaseDomain (ι κ : Type*) where
  /-- C-command among the NPs of the domain. -/
  above : ι → ι → Prop
  [decAbove : DecidableRel above]
  /-- The dependent rule. -/
  dependent : CaseRule κ
  /-- The NPs the dependent rule reads and values. -/
  sees : Finset ι
  /-- The probes, each with the value it gives and the NPs it reaches. -/
  probes : List (κ × Finset ι)
  /-- The elsewhere rule. -/
  elsewhere : CaseRule κ
  /-- The NPs the elsewhere rule values. -/
  spellOut : Finset ι

attribute [instance] CaseDomain.decAbove

section AssignBy

variable {ι κ : Type*} [DecidableEq ι]

/-- One domain: its dependent rule over the NPs it sees, then each of its probes valuing the closest
NP it reaches, then its elsewhere rule. An NP that bears no case is passed over by all three. -/
def CaseDomain.pass (d : CaseDomain ι κ) (s : ι → FeatureSlot κ) : ι → FeatureSlot κ :=
  d.elsewhere.pass d.above d.spellOut <|
    d.probes.foldl (fun st p ↦ agree d.above p.1 p.2 st) (d.dependent.pass d.above d.sees s)

/-- The values a domain can assign: those of its rules, and of its probes. -/
def CaseDomain.values (d : CaseDomain ι κ) : Set κ :=
  d.dependent.values ∪ {v | ∃ p ∈ d.probes, p.1 = v} ∪ d.elsewhere.values

theorem CaseDomain.extends_pass (d : CaseDomain ι κ) (s : ι → FeatureSlot κ) :
    Extends d.values s (d.pass s) := by
  have hprobes : ∀ st, Extends d.values st
      (d.probes.foldl (fun st p ↦ agree d.above p.1 p.2 st) st) :=
    Extends.foldl (F := fun (p : κ × Finset ι) st ↦ agree d.above p.1 p.2 st) _ fun p hp _ ↦
      extends_agree.mono fun _ hv ↦
        Or.inl (Or.inr ⟨p, hp, (Set.mem_singleton_iff.1 hv).symm⟩)
  exact ((CaseRule.extends_pass _ _ s).mono fun _ hv ↦ Or.inl (Or.inl hv)).trans <|
    (hprobes _).trans <| (CaseRule.extends_pass _ _ _).mono fun _ hv ↦ Or.inr hv

/-- Assignment over the domains `ds`, innermost first. -/
def assignBy (ds : List (CaseDomain ι κ)) (s : ι → FeatureSlot κ) : ι → FeatureSlot κ :=
  ds.foldl (fun st d ↦ d.pass st) s

/-- Assignment over domains extends the state by what the domains can assign. -/
theorem extends_assignBy (ds : List (CaseDomain ι κ)) (s : ι → FeatureSlot κ) :
    Extends {v | ∃ d ∈ ds, v ∈ d.values} s (assignBy ds s) :=
  Extends.foldl (F := fun (d : CaseDomain ι κ) st ↦ d.pass st) ds (fun d hd st ↦
    (d.extends_pass st).mono fun v hv ↦ (⟨d, hd, hv⟩ : ∃ d ∈ ds, v ∈ d.values)) s

end AssignBy

/-! ### Assignment over NPs placed by hand -/

section Assign

variable {ι : Type*} (g : CaseAssigners) (U : Finset ι) (np : ι → PhasedNP)

/-- The probes of the domain of `c` among `probes`, the heads with the domain each agrees into:
    those with an Agree case, reaching what the domain sees of `U`. -/
def CaseAssigners.probesIn (probes : List (Cat × Cat)) (c : Cat) :
    List ((Case × Mechanism) × Finset ι) :=
  (probes.filter (·.2 == c)).filterMap fun pr ↦
    (g.agreeCase pr.1).map fun k ↦ ((k, .functional), U.filter fun x ↦ (np x).Visible c)

variable [DecidableEq ι] (lt : ι → ι → Prop) [DecidableRel lt] (probes : List (Cat × Cat))

/-- The domain of `c`, for the NPs `U` placed by hand, `lt` their c-command. -/
def CaseAssigners.domain (c : Cat) : CaseDomain ι (Case × Mechanism) where
  above := lt
  dependent := (g.rules c).dependent
  sees := U.filter fun x ↦ (np x).Visible c
  probes := g.probesIn U np probes c
  elsewhere := (g.rules c).elsewhere
  spellOut := U.filter fun x ↦ (np x).spellOut = c

/-- Case for the NPs `U` placed by hand, `lt` their c-command, the domains spelling out in
    `order`. -/
def CaseAssigners.assign (order : List Cat) : ι → FeatureSlot (Case × Mechanism) :=
  assignBy (order.map (g.domain U np lt probes)) (Case.lexical fun x ↦ (np x).case)

/-- What values a case under assignment: a lexical head; a dependent or elsewhere rule of a domain;
or under Agree, a probing head with that case. -/
theorem CaseAssigners.of_assign_eq_valued {order : List Cat} {x : ι} {v : Case × Mechanism}
    (h : g.assign U np lt probes order x = .valued v) :
    (np x).case = .valued v.1 ∧ v.2 = .lexical ∨ ∃ c ∈ order,
      v.2 = .dependent ∧ ((g.rules c).high = some v.1 ∨ (g.rules c).low = some v.1) ∨
      v.2 = .unmarked ∧ (g.rules c).unmarked = some v.1 ∨
      v.2 = .functional ∧ ∃ pr ∈ probes, pr.2 = c ∧ g.agreeCase pr.1 = some v.1 := by
  rcases (extends_assignBy _ _).of_valued h with h | ⟨d, hd, hv⟩
  · obtain ⟨c, hc, rfl⟩ := FeatureSlot.map_eq_valued_iff.1 h
    exact .inl ⟨hc, rfl⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    refine .inr ⟨c, hc, ?_⟩
    rcases hv with (hv | ⟨p, hp, rfl⟩) | hv
    · exact .inl (Rules.of_mem_values_dependent hv)
    · obtain ⟨pr, hmem, hk⟩ := List.mem_filterMap.1 hp
      obtain ⟨k, hk', rfl⟩ := Option.map_eq_some_iff.1 hk
      obtain ⟨hmem, hc'⟩ := List.mem_filter.1 hmem
      exact .inr (.inr ⟨rfl, pr, hmem, by simpa using hc', hk'⟩)
    · exact .inr (.inl (Rules.of_mem_values_elsewhere hv))

end Assign

end Minimalist
