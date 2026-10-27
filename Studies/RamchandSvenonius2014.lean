module

public import Linglib.Syntax.Cartography
public import Linglib.Data.Examples.RamchandSvenonius2014

/-!
# Ramchand and Svenonius (2014): Deriving the functional hierarchy

Ramchand and Svenonius derive the coarse part of the functional hierarchy from three sorts of
description: events, situations, which add time and world parameters to an event, and
propositions, which anchor a situation to the utterance (§3). A head takes a description of one
sort and yields one of the same or a higher sort (Compositional Coherence, (29)): the heads of the
V-domain map events to events, Asp* events to situations, the heads of the T-domain situations to
situations, and Fin* situations to propositions. Along any spine the sorts therefore rise, so a head
that needs a higher sort sits above one that needs a lower: the perfect, a situation head, above
the progressive, an event head (3); an English modal, which includes Fin*, above the perfect (§2.2);
an epistemic modal above a root modal and above the perfect, (20), (23), (24); and situation above
event adverbs (51). Within a zone the sorts fix no order, so a root modal and the perfect compose
in either order, (21) and §6. Adverbs under passive *been*, as in (54), are event modifiers, and
with *already* a situation modifier (51) no assignment of the zones to Cinque's heads is monotone,
since Cinque puts the volitional head of *intentionally* above anterior tense.

## Main statements

* `pairwise_cod_le`: along a spine of composing heads no head takes a sort below what one under
  it yields.
* `not_composes_of_tPerf_vEvt`: the progressive is not above the perfect, (3).
* `analyses_judgment`: a row is acceptable exactly when its spine composes.
* `composes_54a_iff`: adverbs under passive *been* modify events.
* `not_monotone_of_modVolitional`: the zones do not coarsen Cinque's hierarchy.

## Implementation notes

* A head is the sorts of its denotation in §4. Selection beyond sort, the progressive's dynamic
  complement (41) and the passive's argument structure (40), is not modelled, so (3c) and (3d),
  which the paper does not derive from sorts, are not rows; nor is the ordering within the event
  zone, so (3a) omits V-INIT, as §4.1 says the passive requires.
* The paper locates tense twice: in the T-domain below Fin* in (1) and (36), and on Fin* itself in
  (48). (3a) follows (36); the other spines put finite tense on Fin*. Where the paper names no Asp*
  for a form, the simple past and the infinitive, a spine has an unnamed Asp*, and a lexical verb
  with no decomposition is an eventuality description (26).
* *Probably* modifies situations, as §5.4 has it for (60), so (60b) composes and its star is the
  pragmatic one §5.4 assigns it. An adverb here modifies one sort; *easily* (58), which §5.3 lets
  modify either of two, is not a row.

## Errata

* §5.1 puts epistemic adverbials above anything that modifies the situation, where §5.4 puts
  *probably* among the situation modifiers; with the former, the acceptable (61) would not compose
  (`composes_61_iff`).
* §4.1 says the passive head prevents the merge of V-INIT, yet the trees (1) and (36), the head
  movement of §1 and the strict order of §4.1 put V-INIT above V-PASS in passives.

## TODO

* Wiltschko's fourth zone, point of view, between the event and the situation, which §3 declines.

## References

* [ramchand-svenonius-2014]
* [cinque-1999]
* [wiltschko-2014]
-/

@[expose] public section

namespace RamchandSvenonius2014

/-! ### Sorts and heads, §3 and §4 -/

/-- The sorts of description, events below situations below propositions. -/
inductive Zone
  | event
  | situation
  | proposition
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Zone := LinearOrder.lift' Zone.ctorIdx (by decide)

/-- The heads of §4, a lexical verb, an unnamed Asp*, and an adverb modifying descriptions of one
sort (§5.1). -/
inductive Head
  /-- A lexical verb, an eventuality description (26). -/
  | verb
  /-- Result, (36). -/
  | vRes
  /-- Process (37). -/
  | vProc
  /-- The passive participle (40). -/
  | vPass
  /-- Initiation (38). -/
  | vInit
  /-- The progressive *-ing* (41). -/
  | vEvt
  /-- An Asp* whose form the paper does not give. -/
  | asp
  /-- The perfect participle as Asp* (43). -/
  | aspEn
  /-- The null imperfect Asp* (44). -/
  | aspImp
  /-- The perfect auxiliary (45). -/
  | tPerf
  /-- The participle in the T-domain (46). -/
  | tEn
  /-- Past tense in the T-domain, (36). -/
  | tPast
  /-- A modal in the T-domain, root modality (47). -/
  | tModal
  /-- The transition to propositions (48), (49). -/
  | finStar
  /-- A modal in the propositional zone, epistemic modality (§4.4). -/
  | epistemic
  /-- An adverb modifying descriptions of the sort. -/
  | adverb (z : Zone)
  deriving DecidableEq, Repr

namespace Head

/-- The sort of description a head combines with. -/
def dom : Head → Zone
  | verb | vRes | vProc | vPass | vInit | vEvt | asp | aspEn | aspImp => .event
  | tPerf | tEn | tPast | tModal | finStar => .situation
  | epistemic => .proposition
  | adverb z => z

/-- The sort of description a head yields. -/
def cod : Head → Zone
  | verb | vRes | vProc | vPass | vInit | vEvt => .event
  | asp | aspEn | aspImp | tPerf | tEn | tPast | tModal => .situation
  | finStar | epistemic => .proposition
  | adverb z => z

-- (29)
theorem dom_le_cod (h : Head) : h.dom ≤ h.cod := by
  cases h <;> first | decide | exact le_rfl

end Head

open Head

/-- A spine, bottom-up, composes when each head takes the sort the head below yields. -/
def Composes (l : List Head) : Prop := l.IsChain fun h h' ↦ h.cod = h'.dom

instance (l : List Head) : Decidable (Composes l) := inferInstanceAs (Decidable (List.IsChain _ l))

theorem pairwise_cod_le {l : List Head} (hl : Composes l) : l.Pairwise fun h h' ↦ h.cod ≤ h'.dom :=
  have : IsTrans Head fun h h' ↦ h.cod ≤ h'.dom :=
    ⟨fun _ b _ hab hbc ↦ hab.trans ((dom_le_cod b).trans hbc)⟩
  List.isChain_iff_pairwise.1 (hl.imp fun _ _ e ↦ e.le)

theorem not_composes_of_sublist {l : List Head} {a b : Head} (h : List.Sublist [a, b] l)
    (hab : b.dom < a.cod) : ¬ Composes l := fun hl ↦
  not_lt_of_ge (List.pairwise_pair (R := fun h h' : Head ↦ h.cod ≤ h'.dom) |>.1
    ((pairwise_cod_le hl).sublist h)) hab

/-- (3): the progressive is not above the perfect auxiliary (§4.3). -/
theorem not_composes_of_tPerf_vEvt {l : List Head} (h : List.Sublist [tPerf, vEvt] l) :
    ¬ Composes l :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_finStar_tPerf {l : List Head} (h : List.Sublist [finStar, tPerf] l) :
    ¬ Composes l :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_epistemic_tEn {l : List Head} (h : List.Sublist [epistemic, tEn] l) :
    ¬ Composes l :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_epistemic_tModal {l : List Head}
    (h : List.Sublist [epistemic, tModal] l) : ¬ Composes l :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_adverb {l : List Head} {z z' : Zone}
    (h : List.Sublist [adverb z, adverb z'] l) (hz : z' < z) : ¬ Composes l :=
  not_composes_of_sublist h hz

theorem composes_tModal_tPerf :
    Composes [vProc, asp, tModal, tEn, tPerf, finStar] ∧
      Composes [vProc, aspEn, tPerf, tModal] := by
  decide

/-! ### The rows -/

/-- The rows with their spines, bottom-up. -/
def analyses : List (Datum × List Head) :=
  [(Examples.ex_3a, [vProc, vPass, vEvt, aspEn, tPerf, tPast, finStar]),
    (Examples.ex_3b, [vProc, aspEn, tPerf, vEvt, asp, finStar]),
    (Examples.ex_20a, [vProc, aspEn, tPerf, finStar, epistemic]),
    (Examples.ex_20b, [vProc, aspEn, tPerf, finStar, epistemic]),
    (Examples.ex_21a, [vProc, asp, tModal, tEn, tPerf, finStar]),
    (Examples.ex_21b, [vProc, asp, tModal, tEn, tPerf, finStar]),
    (Examples.ex_24a, [vProc, asp, tModal, tModal, finStar]),
    (Examples.ex_24b, [vProc, asp, tModal, finStar, epistemic]),
    (Examples.ex_51a, [verb, asp, adverb .situation, finStar, adverb .proposition]),
    (Examples.ex_51b, [verb, asp, adverb .proposition, adverb .situation, finStar]),
    (Examples.ex_51c, [vProc, adverb .event, asp, adverb .situation, finStar]),
    (Examples.ex_51d, [vProc, asp, adverb .situation, adverb .event, finStar]),
    (Examples.ex_54a, [vProc, vPass, adverb .event, adverb .event, aspEn, tPerf, finStar]),
    (Examples.ex_60a, [verb, asp, adverb .situation, adverb .situation, finStar])]

theorem analyses_judgment : ∀ p ∈ analyses, p.1.judgment = .acceptable ↔ Composes p.2 := by
  decide

/-- (23): the readings of a Norwegian modal under the perfect, with their spines. -/
def readingAnalyses : List (Datum × List (String × List Head)) :=
  [(Examples.ex_23a, [("root", [vProc, asp, tModal, tEn, tPerf, finStar]),
      ("epistemic", [vProc, asp, finStar, epistemic, tEn, tPerf, finStar])]),
    (Examples.ex_23b, [("root", [vProc, asp, tModal, tEn, tPerf, finStar]),
      ("epistemic", [vProc, asp, finStar, epistemic, tEn, tPerf, finStar])])]

theorem readingAnalyses_judgment : ∀ p ∈ readingAnalyses, ∀ r ∈ p.2,
    p.1.readings.lookup r.1 = some .acceptable ↔ Composes r.2 := by
  decide +kernel

/-- (60b) and (61), whose spines compose alike though only (61) is acceptable. -/
def pragmatic : List (Datum × List Head) :=
  [(Examples.ex_60b, [verb, asp, adverb .situation, adverb .situation, finStar]),
    (Examples.ex_61, [vProc, asp, adverb .situation, adverb .situation, finStar])]

theorem pragmatic_composes : ∀ p ∈ pragmatic, Composes p.2 := by decide

theorem composes_61_iff (z : Zone) :
    Composes [vProc, asp, adverb z, adverb .situation, finStar] ↔ z = .situation := by
  cases z <;> decide

theorem composes_54a_iff (z z' : Zone) :
    Composes [vProc, vPass, adverb z, adverb z', aspEn, tPerf, finStar] ↔
      z = .event ∧ z' = .event := by
  cases z <;> cases z' <;> decide

/-! ### Cinque's hierarchy, §5 -/

/-- With *intentionally* an event modifier (54) and *already* a situation modifier (51), no
assignment of zones to Cinque's heads is monotone in his hierarchy, which puts the volitional head
above anterior tense. -/
theorem not_monotone_of_modVolitional {z : Cartography.Head → Zone}
    (hv : z .modVolitional = .event) (ha : z .tAnterior = .situation) : ¬ Monotone z :=
  fun hz ↦ absurd (hz (show Cartography.Head.tAnterior ≤ .modVolitional by decide))
    (by rw [hv, ha]; decide)

end RamchandSvenonius2014
