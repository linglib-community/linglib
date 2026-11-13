module

public import Linglib.Semantics.Exhaustification.Basic
public import Mathlib.Order.Filter.Basic
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
serves for a force when, over all consistent necessities, it is appropriate wherever an English
modal of that force is: [for its own force and, if no scalemate's claim is stronger, for the
stronger one](##servesFor_iff). Negation exchanges the forces, [a modal serving under it as its
dual does](##servesFor_iff_positive), so a possibility modal without a scale [is
flexible](##flexible_iff) in upward-entailing contexts only, as [*o'qa* is](##oqa_flexible).

## Implementation notes

* The necessities at a world are a filter of propositions, as in
  `Semantics/Modality/Necessity.lean`, consistent when it is `NeBot`: [kratzer-1981]'s simple
  necessity over a consistent modal base and her human necessity over an ordering source are
  both instances. Negation acts on a claim by complement, the negative `Polarity`.
* The scalar implicature is [chierchia-2006]'s exhaustification, the grammatical view of the two
  the paper leaves open. The alternatives to a modal's use are the claims of its scalemates in
  the same context, and the English modal it is compared with has both forces for alternatives.
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

open Modality Exhaustification Filter

/-! ### Claims -/

section Claims

variable {W : Type*} (N : W → Filter W) (p : Set W)

/-- The claim a modal of quantificational force `q` makes about `p` over the necessities `N`:
that `p` is a necessity, or that its negation is not. -/
def claim : QuantificationalForce → Set W
  | .universal => {w | p ∈ N w}
  | .existential => {w | ∃ᶠ v in N w, v ∈ p}

variable {N p}

-- Over consistent necessities the universal claim entails the existential one.
theorem antitone_claim (hN : ∀ w, (N w).NeBot) : Antitone (claim N p) := by
  intro q r hqr w hw
  have := hN w
  cases q <;> cases r
  exacts [hw, Eventually.frequently hw, absurd hqr (by decide), hw]

variable (N p)

-- The negation of a claim is the dual claim about the negated prejacent.
theorem compl_claim (q : QuantificationalForce) : (claim N p q)ᶜ = claim N pᶜ q.dual := by
  ext w
  cases q
  exacts [not_frequently, not_eventually]

theorem smul_claim (π : Polarity) (q : QuantificationalForce) :
    π • claim N p q = claim N (π • p) (π • q) := by
  cases π
  exacts [rfl, compl_claim N p q]

/-- Where a modal of force `q` is appropriate in a context of polarity `π`, its scalemates
having the forces `S`: where its claim holds and every scalemate's claim it does not entail
fails, the scalar implicature. -/
def appropriate (π : Polarity) (S : Set QuantificationalForce) (q : QuantificationalForce) :
    Set W :=
  exh ((π • claim N p ·) '' S) (π • claim N p q)

/-- A modal without a scale is appropriate wherever its claim holds: a possibility modal
wherever the prejacent holds at some accessible world, even if it holds at all of them. -/
@[simp]
theorem appropriate_empty (π : Polarity) (q : QuantificationalForce) :
    appropriate N p π ∅ q = π • claim N p q := by
  rw [appropriate, Set.image_empty, exh_empty]

-- In a context a modal is appropriate where the force the polarity makes of it is, about the
-- prejacent the polarity makes of its own.
theorem appropriate_eq_positive (π : Polarity) (S : Set QuantificationalForce)
    (q : QuantificationalForce) :
    appropriate N p π S q = appropriate N (π • p) .positive ((π • ·) '' S) (π • q) := by
  simp only [appropriate, smul_claim, Set.image_image, Polarity.positive_smul]

end Claims

/-! ### Flexibility (§1, §3, Table 1) -/

/-- A modal of force `q`, its scalemates having the forces `S`, serves in a context of polarity
`π` for the force `r` when, over all consistent necessities, it is appropriate wherever a modal
of force `r` with a scalemate of either force, as in English, is. -/
def ServesFor (π : Polarity) (S : Set QuantificationalForce) (q r : QuantificationalForce) :
    Prop :=
  ∀ (W : Type) (N : W → Filter W), (∀ w, (N w).NeBot) → ∀ p : Set W,
    appropriate N p π .univ r ⊆ appropriate N p π S q

variable {π : Polarity} {q r : QuantificationalForce} {S : Set QuantificationalForce}

/-- In a context a modal serves as the force the polarity makes of it does in an
upward-entailing one: under negation, as its dual. -/
theorem servesFor_iff_positive :
    ServesFor π S q r ↔ ServesFor .positive ((π • ·) '' S) (π • q) (π • r) := by
  have key (W : Type) (N : W → Filter W) (p : Set W) :
      appropriate N p π .univ r ⊆ appropriate N p π S q ↔
        appropriate N (π • p) .positive .univ (π • r) ⊆
          appropriate N (π • p) .positive ((π • ·) '' S) (π • q) := by
    rw [appropriate_eq_positive, appropriate_eq_positive N p π S,
      Set.image_univ_of_surjective (MulAction.surjective π)]
  refine ⟨fun h W N hN p ↦ ?_, fun h W N hN p ↦ (key W N p).2 (h W N hN _)⟩
  have := (key W N (π • p)).1 (h W N hN _)
  rwa [smul_smul, Polarity.mul_self, Polarity.positive_smul] at this

/-- The two-world necessities under which `false` sees both worlds and `true` itself only. -/
private def upward (w : Bool) : Filter Bool := 𝓟 (Set.Ici w)

private theorem neBot_upward (w : Bool) : (upward w).NeBot :=
  principal_neBot_iff.2 ⟨w, Set.self_mem_Ici⟩

private theorem true_mem (q : QuantificationalForce) : true ∈ claim upward {true} q := by
  cases q <;> simp [claim, upward]

private theorem false_mem_iff (q : QuantificationalForce) :
    false ∈ claim upward {true} q ↔ q = .existential := by
  cases q <;> simp [claim, upward]

-- Under these necessities the claims entail one another only as they do everywhere.
private theorem claim_upward_subset_iff :
    claim upward {true} r ⊆ claim upward {true} q ↔ q ≤ r :=
  ⟨fun h ↦ by
    by_contra hqr
    obtain rfl : r = .existential := by revert hqr; cases q <;> cases r <;> decide
    exact hqr ((false_mem_iff q).1 (h ((false_mem_iff _).2 rfl))).le,
    fun h ↦ antitone_claim neBot_upward h⟩

-- Under these necessities a modal with a scalemate of either force is appropriate somewhere.
private theorem nonempty_appropriate_upward (r : QuantificationalForce) :
    (appropriate upward {true} .positive .univ r).Nonempty := by
  cases r
  · exact ⟨false, (false_mem_iff _).2 rfl, Set.forall_mem_image.2 fun s _ hs ↦
      claim_upward_subset_iff.2 ((false_mem_iff s).1 hs).le⟩
  · exact ⟨true, true_mem .universal, Set.forall_mem_image.2 fun _ _ _ ↦
      claim_upward_subset_iff.2 le_top⟩

-- In an upward-entailing context a modal serves for its own force and, if no scalemate is
-- stronger, for the stronger force.
theorem servesFor_positive_iff :
    ServesFor .positive S q r ↔ q = r ∨ q < r ∧ ∀ s ∈ S, s ≤ q := by
  have key : ServesFor .positive S q r ↔ q ≤ r ∧ ∀ s ∈ S, s ≤ r → s ≤ q := by
    refine ⟨fun h ↦ ?_, fun ⟨hqr, hS⟩ W N hN p ↦ exh_subset_exh
      (Set.image_mono (Set.subset_univ S)) (antitone_claim hN hqr)
      (Set.forall_mem_image.2 fun s hs hrs ↦ ?_)⟩
    · obtain ⟨hqr, hS⟩ := (exh_subset_exh_iff (Set.mem_image_of_mem _ (Set.mem_univ q))
        (Set.image_mono (Set.subset_univ S)) (nonempty_appropriate_upward r)).1
        (h Bool upward neBot_upward {true})
      exact ⟨claim_upward_subset_iff.1 hqr, fun s hs hsr ↦ claim_upward_subset_iff.1
        (hS _ ⟨s, hs, rfl⟩ (claim_upward_subset_iff.2 hsr))⟩
    · by_cases hsr : s ≤ r
      · exact antitone_claim hN (hS s hs hsr)
      · obtain rfl : q = r := by revert hqr hsr; cases q <;> cases r <;> cases s <;> decide
        exact hrs
  rw [key]
  refine ⟨fun ⟨hqr, hS⟩ ↦ hqr.eq_or_lt.imp_right fun hlt ↦ ⟨hlt, fun s hs ↦ hS s hs ?_⟩, ?_⟩
  · revert hlt; cases q <;> cases r <;> cases s <;> decide
  · rintro (rfl | ⟨hlt, hS⟩)
    exacts [⟨le_rfl, fun _ _ h ↦ h⟩, ⟨hlt.le, fun s hs _ ↦ hS s hs⟩]

/-- A modal serves for its own force and, if no scalemate's claim is stronger in the context,
for the force whose claim is the stronger there. -/
theorem servesFor_iff :
    ServesFor π S q r ↔ q = r ∨ π • q < π • r ∧ ∀ s ∈ S, π • s ≤ π • q := by
  rw [servesFor_iff_positive, servesFor_positive_iff, Set.forall_mem_image,
    (MulAction.injective π).eq_iff]

instance (π : Polarity) (S : Set QuantificationalForce) [DecidablePred (· ∈ S)]
    (q r : QuantificationalForce) : Decidable (ServesFor π S q r) :=
  decidable_of_iff _ servesFor_iff.symm

/-- A modal is flexible in a context, serving for both forces, iff its claim is the existential
one there and its scalemates all have its own force (Table 1). -/
theorem flexible_iff :
    (∀ r, ServesFor π S q r) ↔ π • q = .existential ∧ ∀ s ∈ S, s = q := by
  simp only [servesFor_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hq, hS⟩ r ↦ or_iff_not_imp_left.2 fun hqr ↦ ⟨?_, fun s hs ↦ ?_⟩⟩
  · obtain ⟨hlt, hS⟩ := (h q.dual).resolve_left q.dual_ne.symm
    have hq : π • q = .existential := by
      revert hlt; cases π <;> cases q <;> decide
    exact ⟨hq, fun s hs ↦ MulAction.injective π (le_antisymm (hS s hs) (hq.le.trans bot_le))⟩
  · exact hq.le.trans_lt (bot_le.lt_of_ne fun h ↦ hqr (MulAction.injective π (hq.trans h)))
  · rw [hS s hs]

-- English: a possibility modal with a necessity scalemate does not serve for necessity.
example : ¬ ServesFor .positive {.universal} .existential .universal := by decide

/-! ### Scales (§2) -/

/-- A modal of the inventory `L` serves in a context of polarity `π` for the force `r`, given the
lexical forces `lex` of the modals: its scalemates are those of `L`. -/
def ServesIn (lex : ModalItem → QuantificationalForce) (L : List ModalItem) (π : Polarity)
    (m : ModalItem) (r : QuantificationalForce) : Prop :=
  ServesFor π (m.scalemateForces lex L) (lex m) r

instance (lex : ModalItem → QuantificationalForce) (L : List ModalItem) (π : Polarity)
    (m : ModalItem) (r : QuantificationalForce) : Decidable (ServesIn lex L π m r) :=
  inferInstanceAs (Decidable (ServesFor ..))

/-- The Nez Perce modals are possibility modals (§2): *o'qa*, the participial construction,
which appears to express possibility, *'ax̂*, which speakers judge equivalent to *o'qa*, and the
epistemic particles 'maybe'. -/
def lexicalForce (_ : ModalItem) : QuantificationalForce := .existential

-- §2.6
theorem oqa_scaleFree : NezPerce.oqa.scalemateForces lexicalForce NezPerce.modals = ∅ :=
  Set.not_nonempty_iff_eq_empty.1 <| ModalItem.scalemateForces_nonempty.not.2 (by decide)

/-- *O'qa* serves for both forces in an upward-entailing context and not under negation
(§1, §3). -/
theorem oqa_flexible :
    (∀ r, ServesIn lexicalForce NezPerce.modals .positive NezPerce.oqa r) ∧
      ¬ ∀ r, ServesIn lexicalForce NezPerce.modals .negative NezPerce.oqa r := by
  decide

theorem oqa_forces :
    ∀ r, r ∈ NezPerce.oqa.quantificationalForces ↔
      ServesIn lexicalForce NezPerce.modals .positive NezPerce.oqa r := by
  decide

/-! ### Rows -/

/-- The modals the rows name, keyed by their forms. -/
def modalTable : List (String × ModalItem) := NezPerce.modals.map fun m ↦ (m.form, m)

/-- The polarity of an environment: negation, the restriction of a universal and a conditional
antecedent are not upward-entailing. -/
def polarity : Examples.Environment → Polarity
  | .unembedded | .existentialRestriction | .conditionalConsequent => .positive
  | .negation | .universalRestriction | .conditionalAntecedent => .negative

/-- The force of the English modal of a row's context or translation. -/
def forceTable : List (String × QuantificationalForce) :=
  [("possibility", .existential), ("necessity", .universal)]

theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.parse? "modal" modalTable).isSome ∧
      (Examples.environment e).isSome := by
  decide

-- §1, §3
theorem rows :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable,
      ∀ env ∈ Examples.environment e,
        (∀ r ∈ e.parse? "force" forceTable, (e.judgment = .acceptable ↔
          ServesIn lexicalForce NezPerce.modals (polarity env) m r)) ∧
        ∀ x ∈ e.readings, ∃ r ∈ forceTable.lookup x.1, (x.2 = .acceptable ↔
          ServesIn lexicalForce NezPerce.modals (polarity env) m r) := by
  decide

end Deal2011
