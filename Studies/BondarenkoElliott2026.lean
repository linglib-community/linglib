module

public import Linglib.Logic.Truthmaker.Basic
public import Linglib.Semantics.Mereology.Relation
public import Mathlib.Data.PFun

/-!
# Bondarenko and Elliott (2026): Monotonicity via mereology in the semantics of attitude reports

On the equality semantics for clausal embedding, *`M` believes that `p`* says that one of the
believings of `M` has content `p`. Attitudinal eventualities and contentful individuals have
parts, and propositions are ordered by informational parthood: `p'` is a part of `p` when `p`
entails `p'`, so the contents are the order dual `(Set W)ᵒᵈ`. The content of an eventuality is a
relation `cont : SetRel (Set W)ᵒᵈ V` between contents and their bearers, so that for a set `B` of
believings the contents believed are `cont.preimage B`. The two conditions of the paper on how
such a map treats parts are the mapping conditions of [krifka-1998] on a thematic relation: the
content relation maps to sub-eventualities, `Mereology.MSE cont`, and the theme relation of
*believe* maps to sub-objects, `Mereology.MSO theme`.

Where the believings have divisive reference, mapping to sub-eventualities makes the contents
believed a lower set, which in the informational order is closure under entailment
(`isLowerSet_preimage_cont`); by `Mereology.me_iff_forall_isLowerSet` a content relation maps to
parts exactly when this holds of every divisive set of eventualities. *`M` believes the rumor
that `p`* says that one of the believings has as its theme a rumor with content `p`. Where a
believing has the contents of its theme, this report is closed under weakening of `p`
(`BelievesTheRumorThat.mono`), so its negation is Strawson downward entailing in the clause, and
`not_believesTheRumorThat_mono` gives a model of all the conditions in which the negation is not
Strawson upward entailing. Where the content relation is summative and the believings
cumulative, the contents believed are closed under conjunction (`supClosed_preimage_cont`).

Between single alternatives, Fine's conjunctive parthood of alternative sets is entailment
(`isConjunctivePart_singleton_iff_subset`).

## Implementation notes

The paper's content, theme and holder maps are partial functions. A partial function is here the
relation between a value and the arguments sent to it, as in `Mereology`, which for a content
function `f : V →. Set W` is `(f.map toDual).graph'.inv`, and no statement below needs the
relation to be functional. The believings of a holder at a world are a set `B`, of which
the statements use divisive and cumulative reference only.

Theme-event content matching is stated for every believing with a theme, which has the contents
of its theme. The report with *the rumor that `p`* is existential over the rumors with content
`p`, where the paper has a definite description that presupposes there is exactly one.

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

/-! ### Belief and closure under entailment

By (45a), *`M` believes `p`* holds when one of the believings `B` of `M` has content `p`, which
is `toDual p ∈ cont.preimage B`. -/

/-- The content relation of a partial content function is the converse of its graph, with the
contents in the informational order. -/
example (f : V →. Set W) (e : V) (p : Set W) :
    toDual p ~[(f.map toDual).graph'.inv] e ↔ p ∈ f e := by
  simp [PFun.graph', PFun.map]

section Closure

variable [PartialOrder V] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V} {p p' : Set W}

/-- (45): where the content relation maps to sub-eventualities and the believings have divisive
reference, the contents believed are a lower set in the informational order. -/
theorem isLowerSet_preimage_cont (hMSI : MSE cont) (hB : DIV B) : IsLowerSet (cont.preimage B) :=
  hMSI.me.isLowerSet_preimage hB

/-- Belief is closed under entailment, (75). -/
example (hMSI : MSE cont) (hB : DIV B) (h : toDual p ∈ cont.preimage B) (hp : p ⊆ p') :
    toDual p' ∈ cont.preimage B :=
  isLowerSet_preimage_cont hMSI hB (show toDual p' ≤ toDual p from hp) h

/-- Where each eventuality is its own content, the content relation maps to sub-eventualities,
and the believings below `p` have as contents the propositions that `p` entails. -/
example (p p' : Set W) :
    MSE (SetRel.id : SetRel (Set W)ᵒᵈ (Set W)ᵒᵈ) ∧
      (toDual p' ∈ (SetRel.id : SetRel (Set W)ᵒᵈ _).preimage (Set.Iic (toDual p)) ↔ p ⊆ p') :=
  ⟨fun _ _ h _ hy ↦ ⟨_, SetRel.mem_id.1 h ▸ hy, SetRel.mem_id.2 rfl⟩,
    fun ⟨_, he, hc⟩ ↦ ((SetRel.mem_id.1 hc).trans_le he : toDual p' ≤ toDual p),
    fun h ↦ ⟨toDual p', h, SetRel.mem_id.2 rfl⟩⟩

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

-- (61)
theorem BelievesTheRumorThat.believes {B : Set V} {cont : SetRel (Set W)ᵒᵈ V}
    {contE : SetRel (Set W)ᵒᵈ E} {theme : SetRel E V} {rumor : Set E} {p : Set W}
    (hTECM : TECM B cont contE theme) (h : BelievesTheRumorThat B theme rumor contE p) :
    toDual p ∈ cont.preimage B :=
  let ⟨e, he, _, _, hth, hc⟩ := h
  ⟨e, he, (hTECM he hth _).2 hc⟩

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

/-- (70), (73): believing the rumor that `p` is not closed under strengthening of `p`, so its
negation is not Strawson upward entailing. One believing has the trivial content and as its
theme a rumor with the trivial content, and a second rumor has the content `{true}`. -/
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
are closed under sum, the contents believed are closed under conjunction, the join of the
informational order. -/
theorem supClosed_preimage_cont [SemilatticeSup V] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V}
    (hSUM : SUM cont) (hB : CUM B) : SupClosed (cont.preimage B) :=
  hSUM.relPreimage hB

example [SemilatticeSup V] {B : Set V} {cont : SetRel (Set W)ᵒᵈ V} {p q : Set W}
    (hSUM : SUM cont) (hB : CUM B) (hp : toDual p ∈ cont.preimage B)
    (hq : toDual q ∈ cont.preimage B) : toDual (p ∩ q) ∈ cont.preimage B :=
  supClosed_preimage_cont hSUM hB hp hq

theorem not_supClosed_preimage_cont :
    ∃ (B : Set Bool) (cont : SetRel (Set Bool)ᵒᵈ Bool), ¬ SupClosed (cont.preimage B) := by
  refine ⟨Set.univ, {q | q.1 = toDual {q.2}}, fun h ↦ ?_⟩
  obtain ⟨e, -, hc⟩ := h (a := toDual {true}) ⟨true, trivial, rfl⟩ (b := toDual {false})
    ⟨false, trivial, rfl⟩
  have he : e ∈ ({true} : Set Bool) ∩ {false} :=
    (show ({true} : Set Bool) ∩ {false} = {e} from hc) ▸ Set.mem_singleton e
  exact Bool.false_ne_true (he.2.symm.trans he.1)

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
