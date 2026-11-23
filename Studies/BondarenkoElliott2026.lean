module

public import Linglib.Logic.Truthmaker.Basic
public import Linglib.Semantics.Mereology.Relation

/-!
# Bondarenko and Elliott (2026): Monotonicity via mereology in the semantics of attitude reports

On the equality semantics for clausal embedding, *`M` believes that `p`* says that one of the
believings of `M` has content `p`. Attitudinal eventualities and contentful individuals have
parts, and propositions are ordered by informational parthood: `p'` is a part of `p` when `p`
entails `p'`, so the contents are the order dual `(Set W)ᵒᵈ`. The content of an eventuality is a
relation `cont : SetRel (Set W)ᵒᵈ V` between contents and their bearers, and the two conditions
of the paper on how such a map treats parts are the mapping conditions of [krifka-1998] on a
thematic relation: the content relation maps to sub-eventualities, `Mereology.MSE cont`, and the
theme relation of *believe* maps to sub-objects, `Mereology.MSO theme`.

For a set `B` of believings with divisive reference, mapping to sub-eventualities closes
`Believes B cont` under entailment (`Believes.mono`), and the content relation maps to parts
exactly when every divisive set of eventualities has contents closed under entailment
(`me_iff_forall_believes_mono`). *`M` believes the rumor that `p`* says that one of the
believings has as its theme a rumor with content `p`. Where a believing has the contents of its
theme, this report is closed under weakening of `p` (`BelievesTheRumorThat.mono`), so its
negation is Strawson downward entailing in the clause, and `not_believesTheRumorThat_mono` gives
a model of all the conditions in which the negation is not Strawson upward entailing. Where the
content relation is summative and the believings cumulative, belief is closed under conjunction
(`Believes.inter`).

Between single alternatives, Fine's conjunctive parthood of alternative sets is entailment
(`isConjunctivePart_singleton_iff_subset`).

## Implementation notes

The paper's content, theme and holder maps are partial functions. A partial function is here the
relation between a value and the arguments sent to it, as in `Mereology`, and no statement below
needs the relation to be functional. The believings of a holder at a world are a set `B`, of which
the statements use divisive and cumulative reference only.

Theme-event content matching is stated for every believing with a theme, which has the contents
of its theme.

## References

* [bondarenko-elliott-2026]
* [krifka-1998]
* [cheng-1973]
* [sharvit-2024]
-/

@[expose] public section

namespace BondarenkoElliott2026

open Mereology OrderDual
open scoped SetRel

variable {V E W : Type*}

/-! ### Belief and closure under entailment -/

/-- (45a): *`M` believes `p`* holds when one of the believings `B` of `M` has content `p`. -/
def Believes (B : Set V) (cont : SetRel (Set W)ᵒᵈ V) (p : Set W) : Prop :=
  ∃ e ∈ B, toDual p ~[cont] e

section Closure

variable [PartialOrder V] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V} {p p' : Set W}

/-- (45): where the content relation maps to sub-eventualities and the believings have divisive
reference, belief is closed under entailment. -/
theorem Believes.mono (hMSI : MSE cont) (hB : DIV B) (h : Believes B cont p) (hp : p ⊆ p') :
    Believes B cont p' :=
  me_iff_forall_isLowerSet.1 hMSI.me B hB (a := toDual p) hp h

-- (46)
theorem not_believes_of_subset (hMSI : MSE cont) (hB : DIV B) (hp : p ⊆ p')
    (h : ¬ Believes B cont p') : ¬ Believes B cont p :=
  fun hb ↦ h (hb.mono hMSI hB hp)

/-- The content relation maps to parts exactly when every set of eventualities with divisive
reference has contents closed under entailment. -/
theorem me_iff_forall_believes_mono :
    ME cont ↔ ∀ B, DIV B → ∀ ⦃p p' : Set W⦄, p ⊆ p' → Believes B cont p → Believes B cont p' :=
  me_iff_forall_isLowerSet.trans
    ⟨fun h B hB _ _ hp hb ↦ h B hB hp hb, fun h B hB _ _ hp hb ↦ h B hB hp hb⟩

end Closure

/-! ### Believing a rumor -/

/-- (59): theme-event content matching, by which a believing has the contents of its theme. -/
def TECM (B : Set V) (cont : SetRel (Set W)ᵒᵈ V) (contE : SetRel (Set W)ᵒᵈ E)
    (theme : SetRel E V) : Prop :=
  ∀ ⦃e⦄, e ∈ B → ∀ ⦃r⦄, r ~[theme] e → ∀ p, p ~[cont] e ↔ p ~[contE] r

/-- *`M` believes the rumor that `p`* holds when one of the believings `B` of `M` has as its
theme a rumor with content `p`. -/
def BelievesTheRumorThat (B : Set V) (theme : SetRel E V) (rumor : Set E)
    (contE : SetRel (Set W)ᵒᵈ E) (p : Set W) : Prop :=
  ∃ e ∈ B, ∃ r ∈ rumor, r ~[theme] e ∧ toDual p ~[contE] r

section Rumor

variable [PartialOrder V] [PartialOrder E] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V}
  {contE : SetRel (Set W)ᵒᵈ E} {theme : SetRel E V} {rumor : Set E} {p p' : Set W}

/-- (69): believing the rumor that `p` is closed under weakening of `p`. The believing has the
content of the rumor, so it has a part with the weaker content, which is a believing whose theme
is a part of the rumor, and that part is a rumor with the weaker content. -/
theorem BelievesTheRumorThat.mono (hMSI : MSE cont) (hMSO : MSO theme)
    (hTECM : TECM B cont contE theme) (hB : DIV B) (hR : DIV rumor)
    (h : BelievesTheRumorThat B theme rumor contE p) (hp : p ⊆ p') :
    BelievesTheRumorThat B theme rumor contE p' := by
  obtain rfl | hlt := hp.eq_or_ssubset
  · exact h
  obtain ⟨e, he, r, hr, hth, hc⟩ := h
  obtain ⟨e', he', hc'⟩ := hMSI ((hTECM he hth _).2 hc) (y := toDual p') hlt
  obtain ⟨r', hr', hth'⟩ := hMSO (show e ~[theme.inv] r from hth) he'
  have hB' := hB he'.le he
  exact ⟨e', hB', r', hR hr'.le hr, hth', (hTECM hB' hth' _).1 hc'⟩

-- (72)
theorem not_believesTheRumorThat_of_subset (hMSI : MSE cont) (hMSO : MSO theme)
    (hTECM : TECM B cont contE theme) (hB : DIV B) (hR : DIV rumor) (hp : p ⊆ p')
    (h : ¬ BelievesTheRumorThat B theme rumor contE p') :
    ¬ BelievesTheRumorThat B theme rumor contE p :=
  fun hb ↦ h (hb.mono hMSI hMSO hTECM hB hR hp)

end Rumor

/-- Believing the rumor that `p` is not closed under strengthening of `p`, so its negation is
not Strawson upward entailing. One believing has the trivial content and as its theme a rumor
with the trivial content, and a second rumor has the content `{true}`. -/
theorem not_believesTheRumorThat_mono :
    ∃ (B : Set Unit) (cont : SetRel (Set Bool)ᵒᵈ Unit) (contE : SetRel (Set Bool)ᵒᵈ Bool)
      (theme : SetRel Bool Unit) (rumor : Set Bool) (p p' : Set Bool),
      MSE cont ∧ MSO theme ∧ TECM B cont contE theme ∧ DIV B ∧ DIV rumor ∧ p ⊆ p' ∧
        BelievesTheRumorThat B theme rumor contE p' ∧
        ¬ BelievesTheRumorThat B theme rumor contE p := by
  refine ⟨Set.univ, {q | q.1 = toDual Set.univ},
    {q | q.1 = toDual (if q.2 then {true} else Set.univ)}, {q | q.1 = false}, Set.univ, {true},
    Set.univ, ?_, ?_, ?_, isLowerSet_univ, isLowerSet_univ, Set.subset_univ _,
    ⟨(), trivial, false, trivial, rfl, rfl⟩, ?_⟩
  · rintro _ _ rfl y hy
    exact absurd hy not_lt_bot
  · rintro _ _ - e' he'
    exact absurd he' (lt_irrefl _)
  · rintro _ - r rfl p
    exact Iff.rfl
  · rintro ⟨-, -, r, -, rfl, hc⟩
    exact Bool.false_ne_true (ofDual.injective hc ▸ Set.mem_univ false : false ∈ ({true} : Set _))

/-! ### Closure under conjunction -/

/-- (79): where the content of a sum is the conjunction of the contents, (78), and the believings
are closed under sum, belief is closed under conjunction. -/
theorem Believes.inter [SemilatticeSup V] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V}
    {p q : Set W} (hSUM : SUM cont) (hB : CUM B) (hp : Believes B cont p)
    (hq : Believes B cont q) : Believes B cont (p ∩ q) :=
  let ⟨e, he, hc⟩ := hp
  let ⟨e', he', hc'⟩ := hq
  ⟨e ⊔ e', hB he he', hSUM.sup hc hc'⟩

theorem not_believes_inter :
    ∃ (B : Set Bool) (cont : SetRel (Set Bool)ᵒᵈ Bool) (p q : Set Bool),
      Believes B cont p ∧ Believes B cont q ∧ ¬ Believes B cont (p ∩ q) := by
  refine ⟨Set.univ, {q | q.1 = toDual {q.2}}, {true}, {false}, ⟨true, trivial, rfl⟩,
    ⟨false, trivial, rfl⟩, ?_⟩
  rintro ⟨e, -, hc⟩
  have h : e ∈ ({true} : Set Bool) ∩ {false} := ofDual.injective hc ▸ Set.mem_singleton e
  exact Bool.false_ne_true (h.2.symm.trans h.1)

/-! ### Conjunctive parthood -/

open Truthmaker

theorem isConjunctivePart_singleton_iff_subset (p q : Set W) :
    IsConjunctivePart ({toDual q} : Set (Set W)ᵒᵈ) {toDual p} ↔ p ⊆ q :=
  isConjunctivePart_singleton_singleton

theorem not_isConjunctivePart_disjunction (p₁ p₂ p₃ : Set W) (h : ¬ p₃ ⊆ p₂) :
    ¬ IsConjunctivePart ({toDual p₁, toDual p₂} : Set (Set W)ᵒᵈ) {toDual p₃} := fun hc ↦
  h ((isConjunctivePart_singleton_right_iff (Set.insert_nonempty _ _)).1 hc _
    (Set.mem_insert_of_mem _ rfl))

end BondarenkoElliott2026
