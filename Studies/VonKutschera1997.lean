module

public import Mathlib.Basic.Countable.Defs
public import Studies.Thomason1984

/-!
# Von Kutschera (1997): T × W Completeness

Von Kutschera axiomatizes T × W logic in a language with an operator for truth in all worlds, which
he credits to Di Maio and Zanardo. The
Hilbert calculus `TW` adds to linear tense logic S5 modalities for historical necessity and for
truth in all worlds, their interaction with the tenses, and Gabbay's irreflexivity rule, whose
soundness rests on [a formula's depending only on the atoms it mentions](##sat_iff_of_agree). The
calculus is [sound](##soundness) and [complete](##completeness) for models with an arbitrary
valuation. His frames are Thomason's, but his models drop Thomason's condition on assignments, so
[an atom's historical necessity is valid for Thomason and unprovable in `TW`](##not_provable_imp_N).

## TODO

* `completeness`: von Kutschera's proof builds, from the maximal consistent sets of `TW`, a
  separated model refuting an unprovable sentence, using Gabbay's irreflexivity lemma.
* The equivalence of T × W and separated models (Theorem 1.1, p. 243), and the alternative
  axiomatization with an *actually* operator sketched at the end of the paper.

## References

* [von-kutschera-1997]
* [thomason-1984]
* [dimaio-zanardo-1994]
-/

@[expose] public section

namespace VonKutschera1997

open Temporal

universe u v

variable {Atom : Type*}

/-- The sentential constants occurring in a formula. -/
def mentions : Formula Atom → Atom → Prop
  | .atom p,  q => p = q
  | .neg a,   q => mentions a q
  | .and a b, q => mentions a q ∨ mentions b q
  | .G a,     q => mentions a q
  | .H a,     q => mentions a q
  | .N a,     q => mentions a q
  | .box a,   q => mentions a q

/-! ### Coincidence lemma

A formula's truth at a point depends only on the valuation of the atoms it mentions. -/

theorem sat_iff_of_agree {T World : Type*} [LinearOrder T] (F : TWFrame World T)
    (V₁ V₂ : Atom → T → World → Prop) :
    ∀ (a : Formula Atom), (∀ p, mentions a p → ∀ t w, V₁ p t w ↔ V₂ p t w) →
      ∀ t w, (F.sat V₁ a t w ↔ F.sat V₂ a t w)
  | .atom p,  h, t, w => h p rfl t w
  | .neg a,   h, t, w => by
      simp only [TWFrame.sat_neg]; rw [sat_iff_of_agree F V₁ V₂ a h t w]
  | .and a b, h, t, w => by
      simp only [TWFrame.sat_and]
      rw [sat_iff_of_agree F V₁ V₂ a (fun p hp ↦ h p (Or.inl hp)) t w,
          sat_iff_of_agree F V₁ V₂ b (fun p hp ↦ h p (Or.inr hp)) t w]
  | .G a, h, t, w => by
      simp only [TWFrame.sat_G]
      exact forall_congr' fun t' ↦ imp_congr_right fun _ ↦ sat_iff_of_agree F V₁ V₂ a h t' w
  | .H a, h, t, w => by
      simp only [TWFrame.sat_H]
      exact forall_congr' fun t' ↦ imp_congr_right fun _ ↦ sat_iff_of_agree F V₁ V₂ a h t' w
  | .N a, h, t, w => by
      simp only [TWFrame.sat_N]
      exact forall_congr' fun w' ↦ imp_congr_right fun _ ↦ sat_iff_of_agree F V₁ V₂ a h t w'
  | .box a, h, t, w => by
      simp only [TWFrame.sat_box]
      exact forall_congr' fun w' ↦ sat_iff_of_agree F V₁ V₂ a h t w'

/-- A formula is **valid** when it is true at every point of every T × W model. -/
def Valid (a : Formula Atom) : Prop :=
  ∀ {T : Type u} {World : Type v} [LinearOrder T]
    (F : TWFrame World T) (V : Atom → T → World → Prop) (t : T) (w : World),
    F.sat V a t w

open Formula in
/-- The Hilbert calculus `TW` of [von-kutschera-1997] has propositional axioms, the tense axioms
`A1`–`A3`, the modal axioms `A4`–`A5`, the interaction axioms `A6`–`A8`, modus ponens,
necessitation for `H`, `N` and `□`, and Gabbay's irreflexivity rule. -/
inductive Provable : Formula Atom → Prop where
  /-- Propositional `K` combinator. -/
  | impK (a b : Formula Atom) : Provable (a.imp (b.imp a))
  /-- Propositional `S` combinator. -/
  | impS (a b c : Formula Atom) :
      Provable ((a.imp (b.imp c)).imp ((a.imp b).imp (a.imp c)))
  /-- Classical contraposition. -/
  | contra (a b : Formula Atom) : Provable (((a.neg).imp (b.neg)).imp (b.imp a))
  /-- Conjunction introduction. -/
  | andI (a b : Formula Atom) : Provable (a.imp (b.imp (a.and b)))
  /-- Conjunction elimination (left). -/
  | andL (a b : Formula Atom) : Provable ((a.and b).imp a)
  /-- Conjunction elimination (right). -/
  | andR (a b : Formula Atom) : Provable ((a.and b).imp b)
  /-- A1a — `K` axiom for `G`. -/
  | a1a (a b : Formula Atom) : Provable (((a.imp b).G.and a.G).imp b.G)
  /-- A1b — `K` axiom for `H`. -/
  | a1b (a b : Formula Atom) : Provable (((a.imp b).H.and a.H).imp b.H)
  /-- A1c — the mixing principle `A ⊃ HFA` of [prior-1967]. -/
  | a1c (a : Formula Atom) : Provable (a.imp a.Fut.H)
  /-- A1d — the mixing principle `A ⊃ GPA` of [prior-1967]. -/
  | a1d (a : Formula Atom) : Provable (a.imp a.Pst.G)
  /-- A2 — `4` axiom for `G` (transitivity). -/
  | a2 (a : Formula Atom) : Provable (a.G.imp a.G.G)
  /-- A3a — future linearity (`.3`). -/
  | a3a (a : Formula Atom) : Provable (a.Fut.imp (a.Fut.or (a.or a.Pst)).G)
  /-- A3b — past linearity (`.3`). -/
  | a3b (a : Formula Atom) : Provable (a.Pst.imp (a.Fut.or (a.or a.Pst)).H)
  /-- A4a — `T` axiom for `N`. -/
  | a4a (a : Formula Atom) : Provable (a.N.imp a)
  /-- A4b — `K` axiom for `N`. -/
  | a4b (a b : Formula Atom) : Provable (((a.imp b).N.and a.N).imp b.N)
  /-- A4c — `5` axiom for `N`. -/
  | a4c (a : Formula Atom) : Provable (a.M.imp a.M.N)
  /-- A5a — `K` axiom for `□`. -/
  | a5a (a b : Formula Atom) : Provable (((a.imp b).box.and a.box).imp b.box)
  /-- A5b — `5` axiom for `□`. -/
  | a5b (a : Formula Atom) : Provable (a.dia.imp a.dia.box)
  /-- A6 — past/necessity interaction `PNA ⊃ NPA`. -/
  | a6 (a : Formula Atom) : Provable (a.N.Pst.imp a.Pst.N)
  /-- A7 — `□` dominates `N` (`□A ⊃ NA`). -/
  | a7 (a : Formula Atom) : Provable (a.box.imp a.N)
  /-- A8a — past/`□` interaction `P□A ⊃ □PA`. -/
  | a8a (a : Formula Atom) : Provable (a.box.Pst.imp a.Pst.box)
  /-- A8b — future/`□` interaction `F□A ⊃ □FA`. -/
  | a8b (a : Formula Atom) : Provable (a.box.Fut.imp a.Fut.box)
  /-- Modus ponens. -/
  | mp {a b : Formula Atom} : Provable (a.imp b) → Provable a → Provable b
  /-- Necessitation for `H`. -/
  | necH {a : Formula Atom} : Provable a → Provable a.H
  /-- Necessitation for `N`. -/
  | necN {a : Formula Atom} : Provable a → Provable a.N
  /-- Necessitation for `□`. -/
  | necBox {a : Formula Atom} : Provable a → Provable a.box
  /-- Gabbay's irreflexivity rule infers `A` from `□(¬q ∧ Gq) ⊃ A` when `q` is not in `A`. -/
  | ir {a : Formula Atom} (q : Atom) :
      Provable ((Formula.and (.neg (.atom q)) (.G (.atom q))).box.imp a) →
      ¬ mentions a q → Provable a

/-! ### Soundness -/

open TWFrame
open ModalLogic (box_four box_T)

/-- Every `TW`-provable formula is T × W-valid, the soundness of `TW` ([von-kutschera-1997]). -/
theorem soundness {a : Formula Atom} (h : Provable a) : Valid.{u, v} a := by
  intro T World _ F V t w
  induction h generalizing V t w with
  | impK _ _ => simp only [sat_imp]; exact fun p _ ↦ p
  | impS _ _ _ => simp only [sat_imp]; exact fun f g p ↦ f p (g p)
  | contra _ _ => simp only [sat_imp, sat_neg]; exact fun f q ↦ not_not.1 fun np ↦ f np q
  | andI _ _ => simp only [sat_imp, sat_and]; exact fun p q ↦ ⟨p, q⟩
  | andL _ _ => simp only [sat_imp, sat_and]; exact fun h ↦ h.1
  | andR _ _ => simp only [sat_imp, sat_and]; exact fun h ↦ h.2
  | a1a _ _ | a1b _ _ =>
      simp only [sat_imp, sat_and, sat_G, sat_H]
      exact fun h t' ht' ↦ h.1 t' ht' (h.2 t' ht')
  | a4b _ _ =>
      simp only [sat_imp, sat_and, sat_N]; exact fun h w' hw' ↦ h.1 w' hw' (h.2 w' hw')
  | a5a _ _ =>
      simp only [sat_imp, sat_and, sat_box]; exact fun h w' ↦ h.1 w' (h.2 w')
  | a1c _ =>
      simp only [sat_imp, sat_H, sat_Fut]
      exact fun ha t' ht' ↦ ⟨t, ht', ha⟩
  | a1d _ =>
      simp only [sat_imp, sat_G, sat_Pst]
      exact fun ha t' ht' ↦ ⟨t, ht', ha⟩
  | a2 _ =>
      simp only [sat_imp]; exact fun h ↦ box_four h
  | a3a _ | a3b _ =>
      simp only [sat_imp, sat_G, sat_H, sat_or, sat_Fut, sat_Pst]
      rintro ⟨t₀, _, ha⟩ t' _
      rcases lt_trichotomy t₀ t' with hlt | heq | hgt
      exacts [.inr (.inr ⟨t₀, hlt, ha⟩), .inr (.inl (heq ▸ ha)), .inl ⟨t₀, hgt, ha⟩]
  | a4a _ => simp only [sat_imp]; exact fun h ↦ box_T h
  | a4c _ =>
      simp only [sat_imp, sat_N, sat_M]
      rintro ⟨w₀, hw₀, ha⟩ w' hw'
      exact ⟨w₀, (F.sim t).iseqv.trans ((F.sim t).iseqv.symm hw') hw₀, ha⟩
  | a5b _ => simp only [sat_imp, sat_box, sat_dia]; exact fun ⟨w₀, ha⟩ _ ↦ ⟨w₀, ha⟩
  | a7 _ => simp only [sat_imp, sat_box, sat_N]; exact fun h w' _ ↦ h w'
  | a6 _ =>
      simp only [sat_imp, sat_N, sat_Pst]
      rintro ⟨t', ht', hN⟩ w' hw'
      exact ⟨t', ht', hN w' (F.antitone_sim ht'.le hw')⟩
  | a8a _ | a8b _ =>
      simp only [sat_imp, sat_box, sat_Pst, sat_Fut]
      rintro ⟨t', ht', hbox⟩ w'; exact ⟨t', ht', hbox w'⟩
  | mp _ _ ihab iha => exact (TWFrame.sat_imp F V _ _ t w).1 (ihab V t w) (iha V t w)
  | necH _ ih => exact fun t' _ ↦ ih V t' w
  | necN _ ih => exact fun w' _ ↦ ih V t w'
  | necBox _ ih => exact fun w' _ ↦ ih V t w'
  | @ir a q _ hq ih =>
      classical
      let V' : Atom → T → World → Prop := fun p t'' w'' ↦ if p = q then t < t'' else V p t'' w''
      have hbox : F.sat V' (Formula.and (.neg (.atom q)) (.G (.atom q))).box t w := by
        intro w' _; refine ⟨?_, fun t' ht' ↦ ?_⟩ <;> simp only [sat_neg, sat_atom, V']
        exacts [lt_irrefl t, Tense.mem_toSetRel_future.1 ht']
      have hagree : ∀ p, mentions a p → ∀ tt ww, V p tt ww ↔ V' p tt ww := by
        intro p hp tt ww
        have hpq : p ≠ q := fun e ↦ hq (e ▸ hp)
        simp only [V', ite_eq_right hpq]
      exact (sat_iff_of_agree F V V' a hagree t w).mpr
        ((TWFrame.sat_imp F V' _ _ t w).1 (ih V' t w) hbox)

/-- `TW` is complete for its models, the main theorem. The language needs infinitely many atoms for
the irreflexivity rule to have a fresh one. -/
theorem completeness [Countable Atom] [Infinite Atom] {a : Formula Atom} (h : Valid.{0, 0} a) :
    Provable a := by
  -- TODO: the canonical separated model of the maximal consistent sets of `TW` (see `## TODO`).
  sorry

/-- An atom's implying its own historical necessity is valid over Thomason's assignments, by his
(6), and is not provable in `TW`, whose models allow any valuation. -/
theorem not_provable_imp_N (p : Atom) :
    (∀ {T World : Type} [LinearOrder T] (F : TWFrame World T) (V : Atom → T → World → Prop),
      Thomason1984.IsAssignment F V → ∀ t w,
        F.sat V ((Formula.atom p).imp (Formula.atom p).N) t w) ∧
    ¬ Provable ((Formula.atom p).imp (Formula.atom p).N) := by
  refine ⟨fun F V hV t w ↦ (sat_imp F V _ _ t w).2 fun h ↦
    (Thomason1984.sat_N_iff hV (a := .atom p) trivial).2 h, fun h ↦ ?_⟩
  have hv : Valid.{0, 0} ((Formula.atom p).imp (Formula.atom p).N) := soundness h
  have hs := hv (T := Unit) (World := Bool) ⟨fun _ ↦ ⊤, fun _ _ _ ↦ le_rfl⟩
    (fun _ _ w ↦ w = true) () true
  exact Bool.false_ne_true ((sat_imp _ _ _ _ _ _).1 hs rfl false trivial)

end VonKutschera1997
