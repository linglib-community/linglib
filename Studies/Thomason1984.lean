module

public import Linglib.Logic.Temporal.Basic
public import Linglib.Semantics.Modality.HistoricalAlternatives

/-!
# Thomason (1984): Combinations of Tense and Modality

On a T × W frame the worlds share one time order, and worlds are historical alternatives through a
time when they differ only in what is future to it. Thomason makes atoms respect this: an assignment
treats alternatives alike up to and including the time, which holds of a valuation [exactly when
the frame refines the agreement of worlds on its atoms up to each
time](##isAssignment_iff_sim_le). Then [a formula without the future tense is historically
necessary when true](##sat_N_iff) and the past of
a necessity is a necessity of the past, while [the converse fails](##exists_not_N_past_imp_past_N).
Since every world has the same times,
[whether a last moment lies ahead](##sat_fut_G_contradiction_iff) and
[whether none does](##sat_G_fut_excluded_middle_iff) are historically necessary too.

## Implementation notes

* Thomason's `□` is historical necessity, `Formula.N`; `Formula.box` is not in his language.
* The chapter was read in the second edition of the Handbook (2002, vol. 7), whose pages the
  locators give, which reprints it with bracketed editorial updates. The first edition was not
  available, so the 1984 page numbers are unchecked.

## TODO

* Treelike frames and Ockhamist validity (Definitions 1 to 5), which validate (6) and (7) but not
  (15) and (16). Kamp frames and their axioms (Definition 9), neutral frames (Definition 10), and
  the deontic section.

## References

* [thomason-1984]
-/

@[expose] public section

namespace Thomason1984

open Temporal Temporal.TWFrame

variable {T World Atom : Type*} [LinearOrder T] {F : TWFrame World T}
  {V : Atom → T → World → Prop} {a : Formula Atom} {t : T} {w w' : World}

/-- Definition 7: an assignment treats historical alternatives through a time alike on each atom,
up to and including that time. -/
def IsAssignment (F : TWFrame World T) (V : Atom → T → World → Prop) : Prop :=
  ∀ p ⦃t₁ t w w'⦄, t₁ ≤ t → F.sim t w w' → (V p t₁ w ↔ V p t₁ w')

/-- A valuation is an assignment of a frame exactly when the frame's historical equivalence refines
agreement on the valuation's atoms up to each time, so `TWFrame.ofDatedFacts` is the coarsest frame
for which the valuation is an assignment. -/
theorem isAssignment_iff_sim_le :
    IsAssignment F V ↔
      ∀ t, F.sim t ≤ (TWFrame.ofDatedFacts (World := World) Prod.snd
        (fun w (f : Atom × T) ↦ V f.1 f.2 w)).sim t :=
  ⟨fun h _ _ _ hww f hf ↦ h f.1 hf hww, fun h p t₁ _ _ _ hle hww ↦ h _ hww (p, t₁) hle⟩

/-- A formula contains no occurrences of `F` when it has no `G`, the primitive of which `F` is the
dual in `Formula`. -/
def ContainsNoF : Formula Atom → Prop
  | .atom _ => True
  | .neg a => ContainsNoF a
  | .and a b => ContainsNoF a ∧ ContainsNoF b
  | .G _ => False
  | .H a => ContainsNoF a
  | .N a => ContainsNoF a
  | .box a => ContainsNoF a

theorem sat_iff_of_sim (hV : IsAssignment F V) :
    ∀ {a : Formula Atom}, ContainsNoF a → ∀ {t : T} {w w' : World}, F.sim t w w' →
      (F.sat V a t w ↔ F.sat V a t w')
  | .atom p, _, _, _, _, h => hV p le_rfl h
  | .neg a, ha, _, _, _, h => not_congr (sat_iff_of_sim hV (a := a) ha h)
  | .and a b, ha, _, _, _, h =>
    and_congr (sat_iff_of_sim hV (a := a) ha.1 h) (sat_iff_of_sim hV (a := b) ha.2 h)
  | .H a, ha, _, _, _, h => by
    simp only [sat_H]
    exact forall₂_congr fun _ ht ↦ sat_iff_of_sim hV (a := a) ha (F.antitone_sim ht.le h)
  | .N _, _, _, _, _, h => by
    simp only [sat_N]
    exact forall_congr' fun _ ↦
      imp_congr_left ⟨(F.sim _).iseqv.trans ((F.sim _).iseqv.symm h), (F.sim _).iseqv.trans h⟩
  | .box _, _, _, _, _, _ => by simp only [sat_box]

/-- (6): under an assignment, a formula without the future tense is historically necessary exactly
when it is true (p. 209). -/
theorem sat_N_iff (hV : IsAssignment F V) (ha : ContainsNoF a) :
    F.sat V (.N a) t w ↔ F.sat V a t w :=
  ⟨fun h ↦ h w ((F.sim t).iseqv.refl w), fun h _ hw ↦ (sat_iff_of_sim hV ha hw).1 h⟩

-- (6) in the terms of `HistoricalAlternatives.settled`: past and present issues are settled.
theorem settled_sat (hV : IsAssignment F V) (ha : ContainsNoF a) (cg : Set World) :
    HistoricalAlternatives.settled F.alternatives cg t (F.sat V a t) :=
  fun _ _ _ hv ↦ sat_iff_of_sim hV ha hv

-- (7), p. 209: this needs only that historical equivalence gets finer as time advances.
theorem sat_N_past_of_past_N (h : F.sat V (.Pst (.N a)) t w) : F.sat V (.N (.Pst a)) t w := by
  simp only [sat_N, sat_Pst] at h ⊢
  obtain ⟨t', ht', hN⟩ := h
  exact fun v hv ↦ ⟨t', ht', hN v (F.antitone_sim ht'.le hv)⟩

-- The atomic instance of (8) is valid, by (6) and the T axiom.
theorem sat_past_N_of_N_past (hV : IsAssignment F V) {p : Atom}
    (h : F.sat V (.N (.Pst (.atom p))) t w) : F.sat V (.Pst (.N (.atom p))) t w := by
  obtain ⟨t', ht', hp⟩ := (sat_Pst F V _ t w).1 (h w ((F.sim t).iseqv.refl w))
  exact (sat_Pst F V _ t w).2 ⟨t', ht', (sat_N_iff hV (a := .atom p) trivial).2 hp⟩

/-- (8) is invalid (p. 209): it can have been that something would happen, on every alternative,
while at no earlier time was it settled that it would. The countermodel is an assignment, on a
frame of dated facts. -/
theorem exists_not_N_past_imp_past_N :
    ∃ (F : TWFrame Bool ℕ) (V : Unit → ℕ → Bool → Prop), IsAssignment F V ∧
      F.sat V (.N (.Pst (.Fut (.atom ())))) 1 true ∧
        ¬ F.sat V (.Pst (.N (.Fut (.atom ())))) 1 true := by
  refine ⟨.ofDatedFacts (fun _ : Unit ↦ 1) (fun w _ ↦ w = true),
    fun _ t w ↦ t = 1 ∧ w = true, ?_, ?_, ?_⟩
  · rintro _ t₁ t w w' hle h
    by_cases hne : t₁ = 1
    · subst hne
      simpa using h () hle
    · simp [hne]
  · intro v hv
    obtain rfl : v = true := by simpa using (hv () le_rfl).1 rfl
    simp
  · simp only [sat_Pst, sat_N, sat_Fut, sat_atom]
    rintro ⟨t', ht', h⟩
    obtain rfl : t' = 0 := by omega
    obtain ⟨_, _, _, hf⟩ := h false fun _ hf ↦ absurd hf (by simp)
    exact Bool.false_ne_true hf

/-- Why (15) is valid: `FG[p ∧ ¬p]` says that a last moment lies ahead, whatever the world, so it
is historically necessary when true (p. 217). -/
theorem sat_fut_G_contradiction_iff :
    F.sat V (.Fut (.G (.and a (.neg a)))) t w ↔ ∃ t', t < t' ∧ IsMax t' := by
  simp only [sat_Fut, sat_G, sat_and, sat_neg, and_not_self, imp_false, isMax_iff_forall_not_lt]

/-- Why (16) is valid: `GF[p ∨ ¬p]` says that no last moment lies ahead, whatever the world, so it
is historically necessary when true (p. 217). -/
theorem sat_G_fut_excluded_middle_iff :
    F.sat V (.G (.Fut (.or a (.neg a)))) t w ↔ ∀ t', t < t' → ¬ IsMax t' := by
  simp only [sat_G, sat_Fut, sat_or, sat_neg, em, and_true, isMax_iff_forall_not_lt, not_forall,
    not_not]

-- (15), p. 217
theorem valid_fifteen : F.sat V ((Formula.Fut (.G (.and a (.neg a)))).imp
    (.N (.Fut (.G (.and a (.neg a)))))) t w := by
  simp only [sat_imp, sat_N, sat_fut_G_contradiction_iff]
  exact fun h _ _ ↦ h

-- (16), p. 217
theorem valid_sixteen : F.sat V ((Formula.G (.Fut (.or a (.neg a)))).imp
    (.N (.G (.Fut (.or a (.neg a)))))) t w := by
  simp only [sat_imp, sat_N, sat_G_fut_excluded_middle_iff]
  exact fun h _ _ ↦ h

end Thomason1984
