module

public import Linglib.Semantics.Modality.Universals
public import Linglib.Semantics.Evidential.Defs
public import Linglib.Data.Examples.Matthewson2016
public import Linglib.Fragments.Gitksan.Modals
public import Linglib.Fragments.Statimcets.Modals
public import Linglib.Fragments.NezPerce.Modals
public import Linglib.Fragments.Niuean.Modals
public import Linglib.Fragments.Nsyilxcen.Modals
public import Studies.Condoravdi2002
public import Studies.Deal2011
public import Studies.Kratzer2012
public import Studies.Matthewson2013
public import Linglib.Data.Examples.Readers

/-!
# Matthewson (2016): Modality

This file formalizes the typological claims of the handbook chapter [matthewson-2016]. On
flavour, [kratzer-2012] projects a conversational background in a factual mode, over the worlds
holding counterparts of some actual situation or body of evidence, or in a content mode, over
the worlds compatible with what some source of information says. A factual background is
therefore realistic, and realism is exactly the veridicality of necessity, so a factual modal
cannot be followed by the denial of its prejacent while a content modal can: the rumor of
(23)–(24), and St'át'imcets *k'a* against *lákw7a* in (25)–(28). Deniability diagnoses the
content mode rather than ruling out a modal analysis of an evidential. With the
circumstantial–evidential division, whether a background encodes an information source, the
modes give Table 18.3's three classes, which St'át'imcets lexicalizes in full, and Gitksan
keeps its epistemic and circumstantial modals apart.

On force, Gitksan *ima('a)* and *g̱at*, variable in force, and Nez Perce *o'qa*, a possibility
modal that no necessity modal competes with ([deal-2011]), are modals without duals, and
*o'qa*'s necessity uses vanish in downward-entailing contexts, as [deal-2011]'s account of
modals without scales predicts. Nsyilxcen *mat* is used in possibility and necessity contexts
and *cmay* in possibility contexts only ([menzies-2013]), which raises questions for the view
that possibility modals are weak through the scalar implicature a contrasting necessity modal
induces: no lexical forces let the scalar account alone predict both. On modal–temporal
interaction, epistemic modals take a past temporal perspective in Blackfoot, Ktunaxa,
St'át'imcets and Gitksan, and Gitksan marks future orientation with the prospective *dim* where
English marks past orientation with the perfect, a mirror image of [condoravdi-2002]'s scopings
and [matthewson-2013]'s paradigms. On typology, Gitksan and Niuean, the chapter's cases of
epistemic modals lacking duals, distinguish force among circumstantial modals and not among
epistemic ones: in each, a circumstantial possibility modal and a necessity modal are duals and
no epistemic modal has one. [vander-klok-2013b]'s refinement of [nauze-2008]'s universal, one
axis of variation per modal domain, is strictly stronger than the universal and holds of
Gitksan.

## Implementation notes

* A factual-mode base is realistic, the actual world holding the situation or evidence whose
  counterparts it projects, and a content-mode base is unconstrained. Deniability is stated for
  simple necessity, the force of *must* in (23)–(24), without the stereotypical ordering source
  whose wiggle room the chapter allows the factual (23).
* The rows are joined to the fragments through `parse?` tables, and every row naming a modal
  resolves (`rows_resolve`), so no row theorem holds by a failed lookup.
* Duals, force distinctions and [nauze-2008]'s axes compare necessity with possibility, weak
  necessity counting as necessity (`ModalItem.classical`): Table 18.1's *sgi* is a (weak)
  necessity modal varying only in flavour. The chapter's weak necessity and graded modality
  (§18.3.1) are not formalized.
* A dual is a modal of the other force sharing a flavour, the necessity–possibility pairs of
  §18.3.1 and the same-domain condition on [deal-2011]'s scales.
* Table 18.4's hypothetical root system has a teleological flavour, which the library folds
  into circumstantial; bouletic stands in for it, which keeps the system ambiguous along both
  axes.
* The English row of Table 18.3 (*can*, *might*, *must*) is not formalized, no fragment
  recording the source or mode of the English modals.
* §18.3.2 contrasts [peterson-2010]'s *ima('a)*, a possibility modal strengthened by an
  ordering source, with [deal-2011]'s *o'qa*; the two part only in downward-entailing contexts,
  where the chapter finds *ima('a)* untestable, so Peterson's analysis is not formalized.
* The chapter says only that Nsyilxcen raises questions for the scalar account;
  `nsyilxcen_not_scalar` sharpens this to the account without further tampering with the
  modal's domain, such as [rullmann-matthewson-davis-2008]'s restriction of a necessity modal.
* (63)'s three contexts are the rows (63a)–(63c), and (42)–(43)'s sentences are rows keyed by
  the force of their context.

## References

* [matthewson-2016]
* [kratzer-2012]
* [matthewson-2013]
* [rullmann-matthewson-davis-2008]
* [peterson-2010]
* [deal-2011]
* [menzies-2013]
* [nauze-2008]
* [vander-klok-2013b]
* [condoravdi-2002]
-/

@[expose] public section

namespace Matthewson2016

open Modality Evidential

/-! ### Modes of projection (Table 18.2) -/

/-- [kratzer-2012]'s modes of projecting a conversational background: factual, over the worlds
holding counterparts of some actual situation or body of evidence, and content, over the worlds
compatible with the propositional content of some source of information. -/
inductive ProjectionMode where
  | factual
  | content
  deriving DecidableEq, Repr, Fintype

variable {W : Type*} {f : Background W} {μ : ProjectionMode}

/-- The modal bases a mode projects. The actual world holds the situation or evidence whose
counterparts a factual base projects, so a factual base is realistic; the content of a source
may be false, so a content base need not be. -/
def ProjectionMode.Admits : ProjectionMode → Background W → Prop
  | .factual, f => f.IsRealistic
  | .content, _ => True

/-- A modal base allows *must p, but not p* when at some world `p` is necessary and false. -/
def Deniable (f : Background W) : Prop := ∃ p w, simpleNecessity f p w ∧ ¬ p w

theorem deniable_iff_not_isRealistic : Deniable f ↔ ¬ f.IsRealistic := by
  simp [Deniable, isRealistic_iff_simpleNecessity_le_id, Pi.le_def]

/-- A mode is veridical over a space of worlds when no base it projects there allows the denial
of a necessity claim. -/
def ProjectionMode.Veridical (μ : ProjectionMode) (W : Type*) : Prop :=
  ∀ f : Background W, μ.Admits f → ¬ Deniable f

theorem ProjectionMode.veridical_iff [Nonempty W] : μ.Veridical W ↔ μ = .factual := by
  cases μ
  · exact iff_of_true (fun _ hf h ↦ deniable_iff_not_isRealistic.1 h hf) rfl
  · refine iff_of_false (fun h ↦ h (fun _ ↦ {fun _ ↦ False}) trivial ?_) nofun
    exact deniable_iff_not_isRealistic.2 fun hr ↦
      Background.mem_accessibleWorlds.1 (hr ‹Nonempty W›.some) _ (Set.mem_singleton _)

instance [Nonempty W] : Decidable (μ.Veridical W) :=
  decidable_of_iff _ ProjectionMode.veridical_iff.symm

-- (23), (24)
theorem rumor :
    ProjectionMode.factual.Admits Kratzer2012.evidence ∧ ¬ Deniable Kratzer2012.evidence ∧
      Deniable Kratzer2012.content :=
  ⟨Kratzer2012.evidence_realistic,
    fun h ↦ deniable_iff_not_isRealistic.1 h Kratzer2012.evidence_realistic,
    deniable_iff_not_isRealistic.2 Kratzer2012.content_not_realistic⟩

/-! ### The three-way classification (Table 18.3) -/

/-- The chapter's three classes of conversational backgrounds: factual backgrounds without an
information source, the traditional circumstantial class, and factual and content backgrounds
encoding one, the two epistemic subtypes. -/
inductive BackgroundClass where
  | factualCircumstantial
  | factualEvidential
  | contentEvidential
  deriving DecidableEq, Repr, Fintype

/-- The mode in which a class projects. -/
def BackgroundClass.projectionMode : BackgroundClass → ProjectionMode
  | .factualCircumstantial => .factual
  | .factualEvidential => .factual
  | .contentEvidential => .content

/-- The traditional epistemic or circumstantial flavour a class refines. -/
def BackgroundClass.traditionalFlavor : BackgroundClass → ModalFlavor
  | .factualCircumstantial => .circumstantial
  | .factualEvidential => .epistemic
  | .contentEvidential => .epistemic

-- Table 18.2
theorem table18_2 :
    (∀ c : BackgroundClass, c.traditionalFlavor = .circumstantial → c.projectionMode = .factual) ∧
      ∀ μ, ∃ c : BackgroundClass, c.traditionalFlavor = .epistemic ∧ c.projectionMode = μ := by
  decide

theorem projectionMode_traditionalFlavor_injective :
    Function.Injective fun c : BackgroundClass ↦ (c.projectionMode, c.traditionalFlavor) := by
  decide

/-- The class of a modal from its mode and the information source it encodes, if any. -/
def BackgroundClass.ofMode (μ : ProjectionMode) : Option EvidenceType → BackgroundClass
  | none => .factualCircumstantial
  | some _ => if μ = .factual then .factualEvidential else .contentEvidential

variable {s : Option EvidenceType}

theorem BackgroundClass.traditionalFlavor_ofMode :
    (ofMode μ s).traditionalFlavor = .circumstantial ↔ s = none := by
  cases s <;> cases μ <;> simp [ofMode, traditionalFlavor]

theorem BackgroundClass.projectionMode_ofMode (h : s = none → μ = .factual) :
    (ofMode μ s).projectionMode = μ := by
  cases s <;> cases μ <;> simp_all [ofMode, projectionMode]

/-! ### Rows -/

/-- The modals the chapter's rows name, keyed by their forms. -/
def modalTable : List (String × ModalItem) :=
  [Statimcets.kaInfer, Statimcets.lakw7a, Gitksan.imaa, NezPerce.oqa, Nsyilxcen.mat,
    Nsyilxcen.cmay, Niuean.liga, Niuean.maeke, Niuean.lata].map fun m ↦ (m.form, m)

theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.feature? "modal").isSome → (e.parse? "modal" modalTable).isSome := by
  decide

section Statimcets
open Statimcets

/-- The mode in which a St'át'imcets modal projects: *lákw7a* from the content of its sensory
evidence, the other evidentials and the circumstantial modals factually (Table 18.3). -/
def statimcetsMode (m : ModalItem) : ProjectionMode := if m = lakw7a then .content else .factual

/-- The class of a St'át'imcets modal. -/
def statimcetsClass (m : ModalItem) : BackgroundClass := .ofMode (statimcetsMode m) (source m)

-- Table 18.3
theorem table18_3 :
    statimcetsClass ka = .factualCircumstantial ∧
      statimcetsClass kaCircumfix = .factualCircumstantial ∧
      statimcetsClass kaInfer = .factualEvidential ∧ statimcetsClass ku7 = .factualEvidential ∧
      statimcetsClass lakw7a = .contentEvidential := by
  decide

theorem statimcets_full_split : ∀ c : BackgroundClass, ∃ m ∈ modals, statimcetsClass m = c := by
  decide

-- (25), (28)
theorem deniability_rows (W : Type*) [Nonempty W] :
    ∀ e ∈ Examples.all, e.feature? "test" = some "deniability" →
      ∃ m ∈ e.parse? "modal" modalTable,
        (e.judgment = .acceptable ↔ ¬ (statimcetsMode m).Veridical W) := by
  simp only [ProjectionMode.veridical_iff]
  decide

end Statimcets

/-! ### Gitksan: epistemic and circumstantial apart (Table 18.1) -/

theorem gitksan_absolute_split : Matthewson2013.TypeSelective Gitksan.modals :=
  Matthewson2013.gitksan_mixed.1

/-! ### Modal force: modals without duals (§18.3.2)

A modal without a dual comes in no necessity–possibility pair and is used in contexts
supporting either claim: Gitksan *ima('a)* and *g̱at*, variable in force, and Nez Perce *o'qa*,
a possibility modal usable in necessity contexts because no necessity modal competes with it to
induce a scalar implicature ([deal-2011]). -/

/-- A modal has a dual in an inventory when it is fixed for one classical force and another item
of the inventory, sharing one of its flavours, is fixed for the dual force. -/
def HasDualIn (L : List ModalItem) (m : ModalItem) : Prop :=
  m.classical.forces.card = 1 ∧ ∃ m' ∈ L, m'.classical.forces =
    m.classical.forces.image ModalForce.dual ∧ ∃ fl ∈ m.flavors, fl ∈ m'.flavors

instance (L : List ModalItem) (m : ModalItem) : Decidable (HasDualIn L m) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _ = _ ∧ ∃ _ ∈ _, _))

theorem not_hasDualIn_of_variesForce {L : List ModalItem} {m : ModalItem}
    (h : m.classical.VariesForce) : ¬ HasDualIn L m :=
  fun h' ↦ Nat.not_succ_le_self 1 (h.trans_eq h'.1)

theorem no_duals :
    ¬ HasDualIn Gitksan.modals Gitksan.imaa ∧ ¬ HasDualIn Gitksan.modals Gitksan.gat ∧
      ¬ HasDualIn NezPerce.modals NezPerce.oqa :=
  ⟨not_hasDualIn_of_variesForce (by decide), not_hasDualIn_of_variesForce (by decide),
    not_hasDualIn_of_variesForce (by decide)⟩

/-- The force a reading names. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("necessity", .necessity)]

-- (37), (38)
theorem imaa_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some Gitksan.imaa →
      ∀ r ∈ e.readings, ∃ fo ∈ forceTable.lookup r.1,
        (r.2 = .acceptable ↔ fo ∈ Gitksan.imaa.forces) := by
  decide

/-- The polarity of a row's context. -/
def polarityTable : List (String × Polarity) := [("false", .positive), ("true", .negative)]

-- (39), (40) [deal-2011]
theorem oqa_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some NezPerce.oqa →
      ∀ π ∈ e.parse? "downwardEntailing" polarityTable, ∀ r ∈ e.readings,
        ∃ fo ∈ forceTable.lookup r.1, (r.2 = .acceptable ↔
          Deal2011.Usable π (Deal2011.lexicalForce NezPerce.oqa)
            (ModalItem.HasScalemate Deal2011.lexicalForce NezPerce.modals NezPerce.oqa) fo) := by
  decide

-- (42), (43)
theorem nsyilxcen_rows :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable, m ∈ Nsyilxcen.modals →
      ∀ fo ∈ e.parse? "force" forceTable, (e.judgment = .acceptable ↔ fo ∈ m.forces) := by
  decide

/-- No lexical forces for *mat* and *cmay* let the scalar account of [deal-2011] predict their uses
((42)–(43)). -/
theorem nsyilxcen_not_scalar :
    ¬ ∃ lex : ModalItem → ModalForce, ∀ m ∈ Nsyilxcen.modals, ∀ g,
      g.classical ∈ m.classical.forces ↔
        Deal2011.Usable .positive (lex m) (ModalItem.HasScalemate lex Nsyilxcen.modals m) g := by
  rintro ⟨lex, h⟩
  have hm := h Nsyilxcen.mat (by decide)
  have hc := h Nsyilxcen.cmay (by decide)
  simp only [ModalItem.HasScalemate, ModalItem.Scalemates, Nsyilxcen.modals, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at hm hc
  generalize lex Nsyilxcen.mat = a at hm hc
  generalize lex Nsyilxcen.cmay = b at hm hc
  cases a <;> cases b <;> revert hm hc <;> decide

/-! ### Modal–temporal interaction (§18.4.3) -/

-- (57), (62)
theorem past_perspective_epistemics :
    ∀ e ∈ Examples.all, e.feature? "perspective" = some "past" → e.judgment = .acceptable ∧
      (e.feature? "flavor" = some "epistemic" ∨
        ∃ m ∈ e.parse? "modal" modalTable, m.Epistemic) := by
  decide

-- (60), (63) [matthewson-2013]
theorem gitksan_orientation_rows :
    ∀ e ∈ Examples.all, e.parse? "modal" modalTable = some Gitksan.imaa →
      ∀ s ∈ e.feature? "orientation", ∃ o ∈ Matthewson2013.orientationOf s,
        (e.judgment = .acceptable ↔ (e.feature? "prospective" = some "true" ↔ o = .future)) := by
  decide

-- §18.4.3 [condoravdi-2002] [matthewson-2013]
theorem marking_mirror :
    (∀ s : Condoravdi2002.Scope, s.orientation = .past ↔ s = .modalPerf) ∧
      ∀ e ∈ Matthewson2013.Examples.all,
        ∀ o ∈ (e.feature? "orientation").bind Matthewson2013.orientationOf,
          (e.judgment = .acceptable ↔ (e.feature? "prospective" = some "true" ↔ o = .future)) :=
  ⟨by decide, Matthewson2013.dim_rows⟩

/-! ### Typology (§18.5) -/

/-- An inventory distinguishes force within a domain when two of its modals there express
different sets of classical forces. -/
def DistinguishesForce (L : List ModalItem) (D : ModalItem → Prop) : Prop :=
  ∃ m ∈ L, ∃ m' ∈ L, D m ∧ D m' ∧ m.classical.forces ≠ m'.classical.forces

instance (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] :
    Decidable (DistinguishesForce L D) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _ ∧ _ ∧ _ ≠ _))

theorem force_only_circumstantial :
    (¬ DistinguishesForce Gitksan.modals ModalItem.Epistemic ∧
        DistinguishesForce Gitksan.modals ModalItem.Circumstantial) ∧
      ¬ DistinguishesForce Niuean.modals ModalItem.Epistemic ∧
        DistinguishesForce Niuean.modals ModalItem.Circumstantial := by
  decide

theorem gitksan_duals :
    HasDualIn Gitksan.modals Gitksan.daakhlxw ∧ HasDualIn Gitksan.modals Gitksan.sgi ∧
      ¬ HasDualIn Gitksan.modals Gitksan.imaa ∧ ¬ HasDualIn Gitksan.modals Gitksan.gat :=
  ⟨by decide, by decide, no_duals.1, no_duals.2.1⟩

theorem niuean_duals :
    HasDualIn Niuean.modals Niuean.maeke ∧
      HasDualIn Niuean.modals Niuean.lata ∧
      ¬ HasDualIn Niuean.modals Niuean.liga := by
  decide

/-- The strength a Niuean row records. -/
def strengthTable : List (String × ModalForce) := [("weak", .possibility), ("strong", .necessity)]

/-- The flavour a Niuean row records, (68)'s obligation reading being deontic. -/
def flavorTable : List (String × ModalFlavor) :=
  [("epistemic", .epistemic), ("circumstantial", .circumstantial), ("deontic", .deontic)]

-- (64), (68)
theorem niuean_rows :
    (∀ e ∈ Examples.all, e.feature? "section" = some "18.5" → (e.feature? "force").isSome →
      ∃ m ∈ e.parse? "modal" modalTable, ∃ fo ∈ e.parse? "force" strengthTable,
        ∃ fl ∈ e.parse? "flavor" flavorTable, (fo, fl) ∈ m.meaning) ∧
      ∀ fo ∈ Niuean.liga.forces, ∃ e ∈ Examples.all,
        e.parse? "modal" modalTable = some Niuean.liga ∧
          e.parse? "force" strengthTable = some fo := by
  decide

/-- An inventory varies along one axis within a domain when its modals there do not vary in
force and in flavour both. -/
def OneAxisWithin (L : List ModalItem) (D : ModalItem → Prop) : Prop :=
  ¬ ((∃ m ∈ L, D m ∧ m.classical.VariesForce) ∧ ∃ m ∈ L, D m ∧ m.VariesFlavor)

instance (L : List ModalItem) (D : ModalItem → Prop) [DecidablePred D] :
    Decidable (OneAxisWithin L D) :=
  inferInstanceAs (Decidable (¬ (_ ∧ _)))

theorem OneAxisWithin.singleAxis {L : List ModalItem} {D : ModalItem → Prop}
    (h : OneAxisWithin L D) {m : ModalItem} (hm : m ∈ L) (hD : D m) :
    SingleAxis m.classical.meaning :=
  ModalItem.singleAxis_meaning_iff.2 fun hv ↦
    h ⟨⟨m, hm, hD, hv.1⟩, m, hm, hD, by simpa [ModalItem.VariesFlavor] using hv.2⟩

/-- [vander-klok-2013b]'s refinement of the universal: within each domain, epistemic and
non-epistemic, an inventory varies along one axis only. -/
def VanderKlok (L : List ModalItem) : Prop :=
  OneAxisWithin L ModalItem.Epistemic ∧ OneAxisWithin L (¬ ·.Epistemic)

instance (L : List ModalItem) : Decidable (VanderKlok L) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem VanderKlok.singleAxis {L : List ModalItem} (h : VanderKlok L) {m : ModalItem}
    (hm : m ∈ L) : SingleAxis m.classical.meaning := by
  by_cases he : m.Epistemic
  exacts [h.1.singleAxis hm he, h.2.singleAxis hm he]

theorem gitksan_vanderKlok : VanderKlok Gitksan.modals := by decide

theorem gitksan_nauze : ∀ m ∈ Gitksan.modals, SingleAxis m.classical.meaning :=
  fun _ hm ↦ gitksan_vanderKlok.singleAxis hm

/-- Table 18.4's hypothetical root system: a deontic modal `x` of either force, a necessity
modal `y` over two flavours, and possibility modals `w` and `z` for one flavour each. -/
def hypotheticalRootSystem : List ModalItem :=
  [⟨"x", {(.necessity, .deontic), (.possibility, .deontic)}, .neutral⟩,
   ⟨"y", {(.necessity, .circumstantial), (.necessity, .bouletic)}, .neutral⟩,
   ⟨"w", {(.possibility, .circumstantial)}, .neutral⟩,
   ⟨"z", {(.possibility, .bouletic)}, .neutral⟩]

theorem hypotheticalRootSystem_singleAxis_not_vanderKlok :
    (∀ m ∈ hypotheticalRootSystem, SingleAxis m.classical.meaning) ∧
      ¬ VanderKlok hypotheticalRootSystem := by
  decide

end Matthewson2016
