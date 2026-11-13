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
modal of that force is. In an upward-entailing context [a modal serves for its own force, and
an existential modal with no universal scalemate for every force](##servesFor_positive_iff);
[under negation a modal serves as its dual does](##servesFor_negative_iff_dual), so a
possibility modal without a scale [is flexible](##flexible_positive_iff) in upward-entailing
contexts only, as [*o'qa* is](##oqa_flexible).

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

variable {f p} {fo g : ModalForce}

-- Over a consistent modal base a universal claim entails every claim.
theorem claim_subset_claim (hf : f.IsConsistent) (h : fo.IsUniversal → g.IsUniversal) :
    claim f p g ⊆ claim f p fo := by
  have hnec : claim f p .necessity ⊆ claim f p .possibility := fun w hw ↦
    let ⟨v, hv⟩ := hf w
    simplePossibility_iff.2 ⟨v, hv, hw hv⟩
  cases g <;> cases fo <;>
    first
    | exact subset_rfl
    | exact hnec
    | exact absurd rfl (h (by decide))

variable (f p)

-- The negation of a claim is the claim of the dual force about the negated prejacent.
theorem compl_claim (fo : ModalForce) : (claim f p fo)ᶜ = claim f pᶜ fo.dual := by
  ext w
  cases fo <;>
    simp [claim, ModalForce.dual, Set.subset_def]

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

theorem appropriate_positive (S : Set ModalForce) (fo : ModalForce) :
    appropriate f p .positive S fo = exh (claim f p '' S) (claim f p fo) :=
  rfl

-- In a negative context a modal is appropriate where its dual is about the negated prejacent.
theorem appropriate_negative (S : Set ModalForce) (fo : ModalForce) :
    appropriate f p .negative S fo = appropriate f pᶜ .positive (ModalForce.dual '' S) fo.dual := by
  simp only [appropriate, Polarity.negative_smul_set, Polarity.positive_smul, compl_claim,
    Set.image_image]

-- The duals of the forces make the claims the forces make.
theorem image_claim_image_dual_univ :
    claim f p '' (ModalForce.dual '' .univ) = claim f p '' .univ := by
  refine (Set.image_mono (Set.subset_univ _)).antisymm ?_
  rintro _ ⟨fo, -, rfl⟩
  exact ⟨fo.dual.dual, ⟨fo.dual, trivial, rfl⟩, by cases fo <;> rfl⟩

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

private theorem true_mem (fo : ModalForce) : true ∈ claim upward {true} fo := by
  cases fo <;> simp [claim, upward]

private theorem false_mem_iff (fo : ModalForce) :
    false ∈ claim upward {true} fo ↔ ¬ fo.IsUniversal := by
  cases fo <;> simp [claim, upward, ModalForce.IsUniversal]

-- In the model the claims entail one another only as they do over every consistent base.
private theorem claim_upward_subset_iff {fo g : ModalForce} :
    claim upward {true} g ⊆ claim upward {true} fo ↔ (fo.IsUniversal → g.IsUniversal) :=
  ⟨fun h hfo ↦ by_contra fun hg ↦ (false_mem_iff fo).1 (h ((false_mem_iff g).2 hg)) hfo,
    claim_subset_claim isConsistent_upward⟩

-- In the model a modal with a scalemate of every force is appropriate somewhere.
private theorem nonempty_appropriate_upward (g : ModalForce) :
    (appropriate upward {true} .positive .univ g).Nonempty := by
  by_cases hg : g.IsUniversal
  · exact ⟨true, true_mem g, Set.forall_mem_image.2 fun _ _ _ ↦
      claim_upward_subset_iff.2 fun _ ↦ hg⟩
  · exact ⟨false, (false_mem_iff g).2 hg, Set.forall_mem_image.2 fun x _ hx ↦
      claim_upward_subset_iff.2 fun hx' ↦ absurd hx' ((false_mem_iff x).1 hx)⟩

variable {fo g : ModalForce} {S : Set ModalForce}

/-- In an upward-entailing context a modal serves for the forces that quantify as it does, and
an existential modal none of whose scalemates is universal serves for every force. -/
theorem servesFor_positive_iff : ServesFor .positive S fo g ↔
    (fo.IsUniversal ↔ g.IsUniversal) ∨ ¬ fo.IsUniversal ∧ ∀ h ∈ S, ¬ h.IsUniversal := by
  have key : ServesFor .positive S fo g ↔ (fo.IsUniversal → g.IsUniversal) ∧
      ∀ h ∈ S, (h.IsUniversal → g.IsUniversal) → h.IsUniversal → fo.IsUniversal := by
    refine ⟨fun hs ↦ ?_, fun ⟨hfg, hS⟩ W f hf p ↦ exh_subset_exh
      (Set.image_mono (Set.subset_univ S)) (claim_subset_claim hf hfg)
      (Set.forall_mem_image.2 fun h hh hgh ↦ ?_)⟩
    · obtain ⟨hfg, hS⟩ := (exh_subset_exh_iff (Set.mem_image_of_mem _ (Set.mem_univ fo))
        (Set.image_mono (Set.subset_univ S)) (nonempty_appropriate_upward g)).1
        (hs Bool upward isConsistent_upward {true})
      exact ⟨claim_upward_subset_iff.1 hfg, fun h hh hhg ↦ claim_upward_subset_iff.1
        (hS _ ⟨h, hh, rfl⟩ (claim_upward_subset_iff.2 hhg))⟩
    · by_cases hhg : h.IsUniversal → g.IsUniversal
      · exact claim_subset_claim hf (hS h hh hhg)
      · exact (claim_subset_claim hf fun hg ↦ absurd (fun _ ↦ hg) hhg).trans hgh
  rw [key]
  by_cases hfo : fo.IsUniversal <;> by_cases hg : g.IsUniversal <;> simp [hfo, hg]

/-- Under negation a modal serves as its dual does in an upward-entailing context, with the
duals of its scalemates. -/
theorem servesFor_negative_iff_dual : ServesFor .negative S fo g ↔
    ServesFor .positive (ModalForce.dual '' S) fo.dual g.dual := by
  have key (W : Type) (f : Background W) (p : Set W) :
      appropriate f p .negative .univ g ⊆ appropriate f p .negative S fo ↔
        appropriate f pᶜ .positive .univ g.dual ⊆
          appropriate f pᶜ .positive (ModalForce.dual '' S) fo.dual := by
    rw [appropriate_negative, appropriate_negative, appropriate_positive,
      image_claim_image_dual_univ]
    rfl
  exact ⟨fun h W f hf p ↦ by simpa using (key W f pᶜ).1 (h W f hf pᶜ),
    fun h W f hf p ↦ (key W f p).2 (h W f hf pᶜ)⟩

-- Under negation the universal modals are the ones with the weaker claim.
theorem servesFor_negative_iff : ServesFor .negative S fo g ↔
    (fo.IsUniversal ↔ g.IsUniversal) ∨ fo.IsUniversal ∧ ∀ h ∈ S, h.IsUniversal := by
  simp only [servesFor_negative_iff_dual, servesFor_positive_iff, Set.forall_mem_image,
    ModalForce.isUniversal_dual, not_not, not_iff_not]

instance (π : Polarity) (S : Set ModalForce) [DecidablePred (· ∈ S)] (fo g : ModalForce) :
    Decidable (ServesFor π S fo g) :=
  match π with
  | .positive => decidable_of_iff _ servesFor_positive_iff.symm
  | .negative => decidable_of_iff _ servesFor_negative_iff.symm

/-- A modal is flexible in an upward-entailing context, serving for every force, iff it is
existential and none of its scalemates is universal (Table 1). -/
theorem flexible_positive_iff : (∀ g, ServesFor .positive S fo g) ↔
    ¬ fo.IsUniversal ∧ ∀ h ∈ S, ¬ h.IsUniversal := by
  simp only [servesFor_positive_iff]
  refine ⟨fun h ↦ (h fo.dual).resolve_left (by simp [ModalForce.isUniversal_dual]), fun h _ ↦
    .inr h⟩

-- Table 1
theorem flexible_negative_iff : (∀ g, ServesFor .negative S fo g) ↔
    fo.IsUniversal ∧ ∀ h ∈ S, h.IsUniversal := by
  simp only [servesFor_negative_iff]
  refine ⟨fun h ↦ (h fo.dual).resolve_left (by simp [ModalForce.isUniversal_dual]), fun h _ ↦
    .inr h⟩

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

-- §2.6
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
