module

public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Fragments.NezPerce.Modals
public import Linglib.Data.Examples.Deal2011
public import Linglib.Data.Examples.Readers

/-!
# Deal (2011): Modals without scales

[deal-2011] argues that the Nez Perce modal *o'qa*, used where English uses a possibility modal
and, in upward-entailing contexts, where it uses a necessity modal, is a possibility modal
without a Horn scale. The use of a modal conveys its claim exhaustified against the claims of
its scalemates, so [a modal with none conveys its bare claim](##appropriate_empty). A modal
serves for a force when, over every consistent modal base, it is appropriate wherever an English
modal of that force is, which holds [for its own force and, if no scalemate makes a stronger
claim, for the forces whose claim is stronger than its own](##servesFor_iff). Negation reverses
which claim is the stronger, so a possibility modal without a scale [is
flexible](##flexible_iff) in upward-entailing contexts only, as *o'qa*, [which forms a scale
with no Nez Perce modal](##oqa_scaleFree), [is](##oqa_flexible).

## Implementation notes

* The claims are [kratzer-1981]'s simple possibility and necessity over a consistent modal base,
  with no ordering source, and weak necessity makes the necessity claim. Negation acts on a claim
  by complement, the negative `Polarity`.
* The scalar implicature is [chierchia-2006]'s exhaustification, the grammatical view of the two
  the paper leaves open. The alternatives to a modal's use are the claims of its scalemates in
  the same context, and the English modal it is compared with has every force for an alternative.
* Negation stands in for the downward-entailing contexts of §3, the restrictions of universals
  and conditional antecedents, whose rows the `environment` feature marks; the paper treats
  conditional antecedents as not upward-entailing, leaving their monotonicity open (fn. 12).
* The rows are *o'qa*'s judgments by the force of the English modal of the context or
  translation. (11) and (12), where speakers find *o'qa* too weak a translation of a necessity
  claim, bear on the preference for possibility translations, which the paper attributes to
  *o'qa*'s being a possibility modal; they are not rows.

## References

* [deal-2011]
* [kratzer-1981]
* [chierchia-2006]
-/

@[expose] public section

namespace Deal2011

open Modality Exhaustification

/-! ### Claims -/

section Claims

variable {W : Type*} (f : Background W) (p : Set W)

/-- The claim a modal of force `fo` makes about `p` over the base `f`: simple possibility, or
simple necessity for the universal forces. -/
def claim : ModalForce → Set W
  | .possibility => {w | simplePossibility f w p}
  | .weakNecessity | .necessity => {w | p ∈ simpleNecessity f w}

/-- In a context of polarity `π`, the claim of force `g` is stronger than that of `fo`:
necessity is the stronger claim in an upward-entailing context, possibility under negation. -/
def StrongerIn : Polarity → ModalForce → ModalForce → Prop
  | .positive, g, fo => fo.classical < g.classical
  | .negative, g, fo => g.classical < fo.classical

instance : ∀ π g fo, Decidable (StrongerIn π g fo)
  | .positive, _, _ => inferInstanceAs (Decidable (_ < _))
  | .negative, _, _ => inferInstanceAs (Decidable (_ < _))

variable {f p} {π : Polarity} {fo g h : ModalForce}

theorem claim_classical (fo : ModalForce) : claim f p fo.classical = claim f p fo := by
  cases fo <;> rfl

theorem StrongerIn.asymm (h : StrongerIn π g fo) : ¬ StrongerIn π fo g := by
  cases π <;> exact lt_asymm h

theorem strongerIn_of_not (h : ¬ StrongerIn π fo g) (hne : fo.classical ≠ g.classical) :
    StrongerIn π g fo := by
  cases π
  exacts [lt_of_le_of_ne (not_lt.1 h) hne, lt_of_le_of_ne (not_lt.1 h) hne.symm]

-- With two classical forces, a claim that another is stronger than is the weakest.
theorem StrongerIn.not_right :
    ∀ {π g fo}, StrongerIn π g fo → ∀ h, ¬ StrongerIn π fo h := by
  decide

-- With two classical forces, a claim stronger than another is the strongest.
theorem StrongerIn.not_left :
    ∀ {π g fo}, StrongerIn π g fo → ∀ h, ¬ StrongerIn π h g := by
  decide

-- Over a consistent modal base, a claim entails every claim not stronger than it in the context.
theorem smul_claim_subset (hf : f.IsConsistent) (h : ¬ StrongerIn π fo g) :
    π • claim f p g ⊆ π • claim f p fo := by
  have hnec : claim f p .necessity ⊆ claim f p .possibility := fun w hw ↦
    let ⟨v, hv⟩ := hf w
    simplePossibility_iff.2 ⟨v, hv, hw hv⟩
  cases π <;> cases g <;> cases fo <;>
    first
    | exact absurd (by decide) h
    | exact subset_rfl
    | exact hnec
    | exact Set.compl_subset_compl.2 hnec

variable (f p)

/-- Where a modal of force `fo` is appropriate in a context of polarity `π`, its scalemates
having the forces `S`: where its claim holds and every scalemate's claim it does not entail
fails, the scalar implicature. -/
def appropriate (π : Polarity) (S : Set ModalForce) (fo : ModalForce) : Set W :=
  exh ((π • claim f p ·) '' S) (π • claim f p fo)

/-- A modal without a scale is appropriate wherever its claim holds: a possibility modal
wherever the prejacent holds at some accessible world, even if it holds at all of them. -/
@[simp]
theorem appropriate_empty (π : Polarity) (fo : ModalForce) :
    appropriate f p π ∅ fo = π • claim f p fo := by
  rw [appropriate, Set.image_empty, exh_empty]

end Claims

/-! ### Flexibility (§1, §3, Table 1) -/

/-- A modal of force `fo`, its scalemates having the forces `S`, serves in a context of polarity
`π` for the force `g` when, over every consistent modal base, it is appropriate wherever a modal
of force `g` with a scalemate of every force, as in English, is. -/
def ServesFor (π : Polarity) (S : Set ModalForce) (fo g : ModalForce) : Prop :=
  ∀ (W : Type) (f : Background W), f.IsConsistent → ∀ p : Set W,
    appropriate f p π .univ g ⊆ appropriate f p π S fo

/-- The two-world model in which `false` sees both worlds and `true` itself only. -/
private def upward : Background Bool := fun w ↦ {Set.Ici w}

private theorem isConsistent_upward : upward.IsConsistent := fun w ↦ ⟨w, by simp [upward]⟩

/-- A prejacent on which the claims of the two classical forces come apart at `false`. -/
private def prejacent : Polarity → Set Bool
  | .positive => {true}
  | .negative => {false}

private theorem true_mem (π : Polarity) (fo : ModalForce) :
    true ∈ π • claim upward (prejacent π) fo := by
  cases π <;> cases fo <;> simp [claim, upward, prejacent]

private theorem false_mem_iff (π : Polarity) (fo : ModalForce) :
    false ∈ π • claim upward (prejacent π) fo ↔ ∀ g, ¬ StrongerIn π fo g := by
  cases π <;> cases fo <;> simp [claim, upward, prejacent, StrongerIn] <;> decide

variable {π : Polarity} {fo g : ModalForce} {S : Set ModalForce}

/-- A modal serves for its own force and, if no scalemate's claim is stronger than its own, for
the forces whose claim is stronger than its own. -/
theorem servesFor_iff : ServesFor π S fo g ↔
    fo.classical = g.classical ∨ StrongerIn π g fo ∧ ∀ h ∈ S, ¬ StrongerIn π h fo := by
  refine ⟨fun hs ↦ or_iff_not_imp_left.2 fun hne ↦ ?_, ?_⟩
  · have hs := hs Bool upward isConsistent_upward (prejacent π)
    have hgf : StrongerIn π g fo := by
      refine strongerIn_of_not (fun hfg ↦ ?_) hne
      have hg : false ∈ appropriate upward (prejacent π) π .univ g :=
        ⟨(false_mem_iff π g).2 (hfg.not_right), by
          rintro _ ⟨x, -, rfl⟩ hx
          exact smul_claim_subset isConsistent_upward ((false_mem_iff π x).1 hx g)⟩
      exact (false_mem_iff π fo).1 (hs hg).1 g hfg
    refine ⟨hgf, fun h hh hhf ↦ ?_⟩
    have hg : true ∈ appropriate upward (prejacent π) π .univ g :=
      ⟨true_mem π g, by
        rintro _ ⟨x, -, rfl⟩ -
        exact smul_claim_subset isConsistent_upward (hgf.not_left x)⟩
    exact (false_mem_iff π h).1
      ((hs hg).2 _ ⟨h, hh, rfl⟩ (true_mem π h) ((false_mem_iff π fo).2 hhf.not_right)) fo hhf
  · rintro (heq | ⟨hgf, hS⟩) W f hf p
    · have hc : claim f p g = claim f p fo := by
        rw [← claim_classical g, ← heq, claim_classical]
      rw [appropriate, hc]
      exact exh_antitone (Set.image_mono (Set.subset_univ S)) _
    · exact fun w hw ↦ ⟨smul_claim_subset hf hgf.asymm hw.1, by
        rintro _ ⟨h, hh, rfl⟩ -
        exact smul_claim_subset hf (hS h hh)⟩

instance (π : Polarity) (S : Set ModalForce) [DecidablePred (· ∈ S)] (fo g : ModalForce) :
    Decidable (ServesFor π S fo g) :=
  decidable_of_iff _ servesFor_iff.symm

/-- A modal is flexible in a context, serving for every force, iff its claim is the weakest there
and no scalemate's is stronger (Table 1). -/
theorem flexible_iff : (∀ g, ServesFor π S fo g) ↔
    (∀ g, ¬ StrongerIn π fo g) ∧ ∀ h ∈ S, ¬ StrongerIn π h fo := by
  simp only [servesFor_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hw, hS⟩ g ↦ ?_⟩
  · obtain ⟨hd, hS⟩ := (h fo.dual).resolve_left (by cases fo <;> decide)
    exact ⟨hd.not_right, hS⟩
  · exact or_iff_not_imp_left.2 fun hne ↦ ⟨strongerIn_of_not (hw g) hne, hS⟩

/-! ### Scales (§2) -/

/-- A modal of the inventory `L` serves in a context of polarity `π` for the force `g`, given the
lexical forces `lex` of the modals: its scalemates are those of `L`. -/
def ServesIn (lex : ModalItem → ModalForce) (L : List ModalItem) (π : Polarity) (m : ModalItem)
    (g : ModalForce) : Prop :=
  ServesFor π {h | ∃ m' ∈ L, m.Scalemates lex m' ∧ lex m' = h} (lex m) g

instance (lex : ModalItem → ModalForce) (L : List ModalItem) (π : Polarity) (m : ModalItem)
    (g : ModalForce) : Decidable (ServesIn lex L π m g) :=
  inferInstanceAs (Decidable (ServesFor ..))

/-- The Nez Perce modals are possibility modals (§2): *o'qa*, the participial construction,
which appears to express possibility, *'ax̂*, which speakers judge equivalent to *o'qa*, and the
epistemic particles 'maybe'. -/
def lexicalForce (_ : ModalItem) : ModalForce := .possibility

/-- No Nez Perce modal forms a scale with *o'qa* (§2.6). -/
theorem oqa_scaleFree :
    ¬ ModalItem.HasScalemate lexicalForce NezPerce.modals NezPerce.oqa := by
  decide

/-- *O'qa* serves for both forces in an upward-entailing context and not under negation
(§1, §3). -/
theorem oqa_flexible :
    (∀ g, ServesIn lexicalForce NezPerce.modals .positive NezPerce.oqa g) ∧
      ¬ ∀ g, ServesIn lexicalForce NezPerce.modals .negative NezPerce.oqa g := by
  decide

theorem oqa_forces :
    ∀ g, g.classical ∈ NezPerce.oqa.classical.forces ↔
      ServesIn lexicalForce NezPerce.modals .positive NezPerce.oqa g := by
  decide

/-! ### Rows -/

/-- The modals the rows name, keyed by their forms. -/
def modalTable : List (String × ModalItem) := NezPerce.modals.map fun m ↦ (m.form, m)

/-- The polarity of a row's environment: negation, the restriction of a universal and a
conditional antecedent are not upward-entailing. -/
def polarityTable : List (String × Polarity) :=
  [("unembedded", .positive), ("existential restriction", .positive),
    ("conditional consequent", .positive), ("negation", .negative),
    ("universal restriction", .negative), ("conditional antecedent", .negative)]

/-- The force of the English modal of a row's context or translation. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("necessity", .necessity)]

theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.parse? "modal" modalTable).isSome ∧
      (e.parse? "environment" polarityTable).isSome := by
  decide

-- §1, §3
theorem rows :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable,
      ∀ π ∈ e.parse? "environment" polarityTable,
        (∀ g ∈ e.parse? "force" forceTable, (e.judgment = .acceptable ↔
          ServesIn lexicalForce NezPerce.modals π m g)) ∧
        ∀ r ∈ e.readings, ∃ g ∈ forceTable.lookup r.1, (r.2 = .acceptable ↔
          ServesIn lexicalForce NezPerce.modals π m g) := by
  decide

end Deal2011
