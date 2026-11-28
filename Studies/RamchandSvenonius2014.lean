module

public import Linglib.Syntax.Cartography.Clause
public import Linglib.Data.Examples.RamchandSvenonius2014

/-!
# Ramchand and Svenonius (2014): Deriving the functional hierarchy

A clause is built from descriptions of three sorts: events; situations, which add a time and a
world to an event; and propositions, which anchor a situation to the utterance. A head of the
clausal spine takes a description of one sort and yields one of the same sort or of the next: the
heads of the V-domain take events to events, Asp* takes events to situations, the heads of the
T-domain take situations to situations, and Fin* takes situations to propositions. A spine composes
when each head takes the sort that the head below it yields.

Along a composing spine the sorts rise, so a head that takes a higher sort is never below one that
yields a lower sort. The perfect auxiliary, a situation head, is above the progressive, an event
head; an epistemic modal, a head of the propositional zone, is above a root modal and above the
perfect; and an adverb is above every adverb of a lower sort. Heads of one sort are not ordered by
sort: a root modal and the perfect compose in either order. 
A verbal word spells out a stretch of the spine: the heads of its stem, then those of its
inflection. The dummy *be* has no head of its own, the participle in *-en* is an Asp* over an event
description and a head of the T-domain over a situation description, and an infinitive or finite
form of an event stem includes a null Asp*. A finite form includes Fin*, so no finite form is below
the perfect auxiliary; English modals, which have only finite forms, are therefore above the
perfect, while a Norwegian root modal has a participle and composes below it.

With *intentionally* a modifier of events and *already* a modifier of situations, an assignment of
sorts to the heads of Cinque's hierarchy is not monotone, since the hierarchy has the volitional
head above anterior tense.

## Implementation notes

* A head is identified with the sorts of its denotation. Selection beyond sort is not modelled: the
  progressive's dynamic complement, the passive's argument structure and the order of the heads of
  the event zone. The doubled progressive and the doubled perfect, which sorts do not exclude, are
  not rows, and the spine of the passive has no initiation head.
* Finite tense is on Fin*, as in its denotation. In the tree of the full auxiliary sequence *could*
  spells out Fin* and one head of the T-domain; that head is the modal's here. Where no Asp* is
  named for a form, the simple past and the infinitive, a spine has an unnamed Asp*, and a lexical
  verb with no decomposition is an eventuality description.
* The reading of a modal in a row without judged readings is that of its translation.
* The rows with adverbs are paired with spines and not with words, since word order does not fix
  where an adverb before a finite verb is adjoined.
* *Probably* modifies situations, so the starred order *once probably* composes; its star is
  pragmatic. An adverb here modifies one sort, so *easily*, which modifies either of two, is not a
  row.

## References

* [ramchand-svenonius-2014]
* [cinque-1999]
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

/-- The heads of §4, with a lexical verb, an unnamed Asp*, and an adverb modifying descriptions of
one sort (§5.1). -/
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
  /-- A modal in the T-domain, root modality (47); the head under *could* in (36). -/
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
  | tPerf | tEn | tModal | finStar => .situation
  | epistemic => .proposition
  | adverb z => z

/-- The sort of description a head yields. -/
def cod : Head → Zone
  | verb | vRes | vProc | vPass | vInit | vEvt => .event
  | asp | aspEn | aspImp | tPerf | tEn | tModal => .situation
  | finStar | epistemic => .proposition
  | adverb z => z

-- (29)
theorem dom_le_cod (h : Head) : h.dom ≤ h.cod := by
  cases h <;> first | decide | exact le_rfl

end Head

open Head

/-- A spine composes when each head takes the sort that the head below it yields. -/
def Composes (s : Spine Head) : Prop := s.heads.IsChain fun h h' ↦ h.cod = h'.dom

instance (s : Spine Head) : Decidable (Composes s) :=
  inferInstanceAs (Decidable (List.IsChain _ s.heads))

variable {s : Spine Head}

/-- Along a composing spine no head takes a sort below what a head under it yields. -/
theorem pairwise_cod_le (hs : Composes s) : s.heads.Pairwise fun h h' ↦ h.cod ≤ h'.dom :=
  have : IsTrans Head fun h h' ↦ h.cod ≤ h'.dom :=
    ⟨fun _ b _ hab hbc ↦ hab.trans ((dom_le_cod b).trans hbc)⟩
  List.isChain_iff_pairwise.1 (hs.imp fun _ _ e ↦ e.le)

theorem not_composes_of_sublist {a b : Head} (h : List.Sublist [a, b] s.heads)
    (hab : b.dom < a.cod) : ¬ Composes s := fun hs ↦
  not_lt_of_ge (List.pairwise_pair (R := fun h h' : Head ↦ h.cod ≤ h'.dom) |>.1
    ((pairwise_cod_le hs).sublist h)) hab

/-- The progressive is not above the perfect auxiliary on a composing spine. -/
theorem not_composes_of_tPerf_vEvt (h : List.Sublist [tPerf, vEvt] s.heads) : ¬ Composes s :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_finStar_tPerf (h : List.Sublist [finStar, tPerf] s.heads) :
    ¬ Composes s :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_epistemic_tEn (h : List.Sublist [epistemic, tEn] s.heads) :
    ¬ Composes s :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_epistemic_tModal (h : List.Sublist [epistemic, tModal] s.heads) :
    ¬ Composes s :=
  not_composes_of_sublist h (by decide)

theorem not_composes_of_adverb {z z' : Zone} (h : List.Sublist [adverb z, adverb z'] s.heads)
    (hz : z' < z) : ¬ Composes s :=
  not_composes_of_sublist h hz

/-! ### Words -/

/-- The heads of a modal on a reading: a head of the T-domain on the root reading, and Fin* with a
head of the propositional zone on the epistemic reading (§4.4). -/
def modal : Examples.Reading → List Head
  | .root => [tModal]
  | .epistemic => [finStar, epistemic]

/-- The stems of the verbal words. -/
inductive Stem
  /-- A dynamic lexical verb. -/
  | lexical
  /-- The dummy *be*, inserted to carry an inflection (§4). -/
  | be
  /-- The perfect auxiliary. -/
  | have
  /-- A modal on a reading. -/
  | modal (r : Examples.Reading)

namespace Stem

/-- The heads a stem spells out. -/
def heads : Stem → List Head
  | .lexical => [vProc]
  | .be => []
  | .have => [tPerf]
  | .modal r => RamchandSvenonius2014.modal r

/-- The sort of the description a stem yields, an event description if it has no head. -/
def sort (s : Stem) : Zone := s.heads.getLast?.elim .event cod

end Stem

/-- The inflections of the verbal words. -/
inductive Inflection
  /-- The passive participle. -/
  | passive
  /-- The progressive participle in *-ing*. -/
  | ing
  /-- The participle in *-en* of the perfect. -/
  | en
  | infinitive
  | finite
  deriving DecidableEq

/-- The null heads that take a description of a sort to a situation description: an Asp* over an
event description (§4.2). -/
def toSituation : Zone → List Head
  | .event => [asp]
  | _ => []

/-- The heads an inflection spells out over a stem of a sort. The participle in *-en* is Asp* over
an event description and a head of the T-domain otherwise, and a finite form adds Fin* below the
propositional zone. -/
def Inflection.heads : Inflection → Zone → List Head
  | .passive, _ => [vPass]
  | .ing, _ => [vEvt]
  | .en, .event => [aspEn]
  | .en, _ => [tEn]
  | .infinitive, z => toSituation z
  | .finite, .proposition => []
  | .finite, z => toSituation z ++ [finStar]

/-- A verbal word, a stem with an inflection. -/
structure Word where
  stem : Stem
  inflection : Inflection

/-- The heads a word spells out, those of its stem below those of its inflection. -/
def Word.heads (w : Word) : List Head := w.stem.heads ++ w.inflection.heads w.stem.sort

/-- The spine of a sequence of verbal words in their surface order, the first word highest. -/
def spine (ws : List Word) : Spine Head := ⟨ws.reverse.flatMap Word.heads⟩

theorem finStar_mem_heads {w : Word} (h : w.inflection = .finite) : finStar ∈ w.heads := by
  rcases w with ⟨_ | _ | _ | _ | _, _⟩ <;> cases h <;> decide

/-- No finite word is below the perfect auxiliary on a composing spine. -/
theorem not_composes_of_finite_of_have {l₁ l₂ : List Word} {i : Inflection} {w : Word}
    (hw : w ∈ l₂) (hf : w.inflection = .finite) :
    ¬ Composes (spine (l₁ ++ ⟨.have, i⟩ :: l₂)) := by
  have h₁ : [finStar].Sublist (l₂.reverse.flatMap Word.heads) :=
    List.singleton_sublist.2 (List.mem_flatMap.2 ⟨w, List.mem_reverse.2 hw, finStar_mem_heads hf⟩)
  have h₂ : [tPerf].Sublist (Word.heads ⟨.have, i⟩) :=
    List.singleton_sublist.2 (List.mem_append_left _ List.mem_cons_self)
  refine not_composes_of_finStar_tPerf ?_
  simpa [spine] using (h₁.append h₂).trans (List.sublist_append_left _ (l₁.reverse.flatMap _))

-- a root modal and the perfect auxiliary compose in either order
theorem composes_modal_have :
    Composes (spine [⟨.have, .finite⟩, ⟨.modal .root, .en⟩, ⟨.lexical, .infinitive⟩]) ∧
      Composes (spine [⟨.modal .root, .finite⟩, ⟨.have, .infinitive⟩, ⟨.lexical, .en⟩]) := by
  decide

/-! ### The rows -/

/-- The rows of the auxiliary sequences with their verbal words. -/
def analyses : List (Datum × List Word) :=
  [(Examples.ex_3a, [⟨.modal .root, .finite⟩, ⟨.have, .infinitive⟩, ⟨.be, .en⟩, ⟨.be, .ing⟩,
      ⟨.lexical, .passive⟩]),
    (Examples.ex_3b, [⟨.be, .finite⟩, ⟨.have, .ing⟩, ⟨.lexical, .en⟩]),
    (Examples.ex_20a, [⟨.modal .epistemic, .finite⟩, ⟨.have, .infinitive⟩, ⟨.lexical, .en⟩]),
    (Examples.ex_20b, [⟨.modal .epistemic, .finite⟩, ⟨.have, .infinitive⟩, ⟨.lexical, .en⟩]),
    (Examples.ex_21a, [⟨.have, .finite⟩, ⟨.modal .root, .en⟩, ⟨.lexical, .infinitive⟩]),
    (Examples.ex_21b, [⟨.have, .finite⟩, ⟨.modal .root, .en⟩, ⟨.lexical, .infinitive⟩]),
    (Examples.ex_24a, [⟨.modal .root, .finite⟩, ⟨.modal .root, .infinitive⟩,
      ⟨.lexical, .infinitive⟩]),
    (Examples.ex_24b, [⟨.modal .epistemic, .finite⟩, ⟨.modal .root, .infinitive⟩,
      ⟨.lexical, .infinitive⟩])]

/-- A row is acceptable exactly when the spine of its words composes. -/
theorem analyses_judgment :
    ∀ p ∈ analyses, p.1.judgment = .acceptable ↔ Composes (spine p.2) := by
  decide

theorem modal_judgment : ∀ e ∈ [Examples.ex_23a, Examples.ex_23b], ∀ r,
    Examples.reading e r = some .acceptable ↔
      Composes (spine [⟨.have, .finite⟩, ⟨.modal r, .en⟩, ⟨.lexical, .infinitive⟩]) := by
  decide

/-- The rows with adverbs, with their spines. -/
def adverbAnalyses : List (Datum × Spine Head) :=
  [(Examples.ex_51a, ⟨[verb, asp, adverb .situation, finStar, adverb .proposition]⟩),
    (Examples.ex_51b, ⟨[verb, asp, adverb .proposition, adverb .situation, finStar]⟩),
    (Examples.ex_51c, ⟨[vProc, adverb .event, asp, adverb .situation, finStar]⟩),
    (Examples.ex_51d, ⟨[vProc, asp, adverb .situation, adverb .event, finStar]⟩),
    (Examples.ex_54a, ⟨[vProc, vPass, adverb .event, adverb .event, aspEn, tPerf, finStar]⟩),
    (Examples.ex_60a, ⟨[verb, asp, adverb .situation, adverb .situation, finStar]⟩)]

theorem adverbAnalyses_judgment :
    ∀ p ∈ adverbAnalyses, p.1.judgment = .acceptable ↔ Composes p.2 := by
  decide

/-- The two orders of *once* and *probably*, (60b) and (61), whose spines compose alike. -/
def pragmatic : List (Datum × Spine Head) :=
  [(Examples.ex_60b, ⟨[verb, asp, adverb .situation, adverb .situation, finStar]⟩),
    (Examples.ex_61, ⟨[vProc, asp, adverb .situation, adverb .situation, finStar]⟩)]

theorem pragmatic_composes : ∀ p ∈ pragmatic, Composes p.2 := by decide

theorem composes_61_iff (z : Zone) :
    Composes ⟨[vProc, asp, adverb z, adverb .situation, finStar]⟩ ↔ z = .situation := by
  cases z <;> decide

-- adverbs under passive *been* modify events
theorem composes_54a_iff (z z' : Zone) :
    Composes ⟨[vProc, vPass, adverb z, adverb z', aspEn, tPerf, finStar]⟩ ↔
      z = .event ∧ z' = .event := by
  cases z <;> cases z' <;> decide

/-! ### Cinque's hierarchy, §5 -/

/-- With *intentionally* an event modifier and *already* a situation modifier, no assignment of
sorts to Cinque's heads is monotone in his hierarchy, which has the volitional head above anterior
tense. -/
theorem not_monotone_of_modVolitional {z : Cartography.Head → Zone}
    (hv : z .modVolitional = .event) (ha : z .tAnterior = .situation) : ¬ Monotone z :=
  fun hz ↦ absurd (hz (show Cartography.Head.tAnterior ≤ .modVolitional by decide))
    (by rw [hv, ha]; decide)

end RamchandSvenonius2014
