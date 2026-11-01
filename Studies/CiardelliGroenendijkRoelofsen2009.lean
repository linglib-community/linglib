module

public import Linglib.Logic.Team.Inquisitive
public import Linglib.Semantics.Questions.Unrestricted

/-!
# Ciardelli, Groenendijk and Roelofsen (2009): Attention! 'Might' in inquisitive semantics

Ciardelli, Groenendijk and Roelofsen let a sentence express a set of possibilities that may
include non-maximal ones, so that besides providing and requesting information it can draw
attention to possibilities. Their restricted semantics keeps only the maximal possibilities and
their unrestricted semantics keeps them all. [The maximal possibilities for a formula are its
restricted possibilities](##CiardelliGroenendijkRoelofsen2009.setOf_maximal_unrestricted) and
[both cover its truth set](##CiardelliGroenendijkRoelofsen2009.sUnion_unrestricted), so the two
semantics agree on inquisitive and informative content. *Might φ*, the formula `⊤ ∨ φ`, [is the
tautology in the restricted semantics](##CiardelliGroenendijkRoelofsen2009.restricted_might), and
in the unrestricted one [it is attentive just when `φ` has a possibility other than the trivial
one](##CiardelliGroenendijkRoelofsen2009.isAttentive_might_iff). The non-informative closure
[`?φ` is attentive just when `φ` is](##CiardelliGroenendijkRoelofsen2009.isAttentive_polarQ_iff),
so only the closures of non-attentive formulas are questions.

## Implementation notes

* The language is the modal-free fragment of `Inquisitive.Formula`, the language of inquisitive
  logic; the modalities receive the trivial proposition, and the theorems about them assume
  `Inquisitive.Formula.IsModalFree`.
* The alternative closure `ALT` (Definition 2) is the set of maximal elements, and the
  propositional closure `PRO` (Definition 13) is `Inquisitive.Unrestricted.pro`.
* The two semantics are compared through the proposition of inquisitive logic,
  `Inquisitive.proposition`, which the possibilities of either generate.
* Worlds form a finite type, as the indices over finitely many proposition letters do.

## References

* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Attention! 'Might' in inquisitive semantics*
  (2009)][ciardelli-groenendijk-roelofsen-2009]
-/

@[expose] public section

namespace CiardelliGroenendijkRoelofsen2009

open Set Inquisitive Inquisitive.Unrestricted

variable {W Atom : Type*}

/-- The proposition a formula expresses in the restricted semantics, a set of alternative
possibilities (Definition 3). -/
def restricted (v : Atom → W → Prop) : Formula Atom → Set (Set W)
  | .atom p => {{w | v p w}}
  | .bot => {∅}
  | .conj φ ψ => {p | Maximal (· ∈ image2 (· ∩ ·) (restricted v φ) (restricted v ψ)) p}
  | .impl φ ψ => {p | Maximal (· ∈ range fun f : restricted v φ → restricted v ψ ↦
      ⋂ a : restricted v φ, (a : Set W)ᶜ ∪ f a) p}
  | .inqDisj φ ψ => {p | Maximal (· ∈ restricted v φ ∪ restricted v ψ) p}
  | .nec _ => {univ}
  | .ent _ => {univ}

/-- The proposition a formula expresses in the unrestricted semantics (Definition 14). -/
noncomputable def unrestricted (v : Atom → W → Prop) : Formula Atom → Set (Set W)
  | .atom p => {{w | v p w}}
  | .bot => {∅}
  | .conj φ ψ => pro (image2 (· ∩ ·) (unrestricted v φ) (unrestricted v ψ))
  | .impl φ ψ => pro (range fun f : unrestricted v φ → unrestricted v ψ ↦
      ⋂ a : unrestricted v φ, (a : Set W)ᶜ ∪ f a)
  | .inqDisj φ ψ => pro (unrestricted v φ ∪ unrestricted v ψ)
  | .nec _ => {univ}
  | .ent _ => {univ}

/-- *Might φ* is `⊤ ∨ φ`, with `⊤` the formula `¬⊥` (§3.2). -/
abbrev might (φ : Formula Atom) : Formula Atom := .inqDisj (Formula.neg .bot) φ

variable (v : Atom → W → Prop)

theorem isProposition_unrestricted : ∀ φ : Formula Atom, IsProposition (unrestricted v φ)
  | .atom _ => isProposition_singleton _
  | .bot => isProposition_singleton _
  | .conj φ ψ => isProposition_pro
      ((isProposition_unrestricted φ).1.image2 (isProposition_unrestricted ψ).1)
  | .impl _ ψ => isProposition_pro ⟨_, fun _ ↦ ⟨_, (isProposition_unrestricted ψ).1.some_mem⟩, rfl⟩
  | .inqDisj φ _ => isProposition_pro ((isProposition_unrestricted φ).1.mono subset_union_left)
  | .nec _ => isProposition_singleton _
  | .ent _ => isProposition_singleton _

theorem isAntichain_restricted : ∀ φ : Formula Atom, IsAntichain (· ⊆ ·) (restricted v φ)
  | .atom _ => IsAntichain.singleton
  | .bot => IsAntichain.singleton
  | .conj _ _ => setOfPred_maximal_antichain _
  | .impl _ _ => setOfPred_maximal_antichain _
  | .inqDisj _ _ => setOfPred_maximal_antichain _
  | .nec _ => IsAntichain.singleton
  | .ent _ => IsAntichain.singleton

theorem restricted_nonempty [Finite W] : ∀ φ : Formula Atom, (restricted v φ).Nonempty
  | .atom _ => singleton_nonempty _
  | .bot => singleton_nonempty _
  | .conj φ ψ => (toFinite _).exists_maximal
      ((restricted_nonempty φ).image2 (restricted_nonempty ψ))
  | .impl _ ψ => (toFinite _).exists_maximal
      ⟨_, fun _ ↦ ⟨_, (restricted_nonempty ψ).some_mem⟩, rfl⟩
  | .inqDisj φ _ => (toFinite _).exists_maximal ((restricted_nonempty φ).mono subset_union_left)
  | .nec _ => singleton_nonempty _
  | .ent _ => singleton_nonempty _

/-! ### Restricted and unrestricted possibilities (§3.1) -/

section Coincidence

variable [Fintype W] [DecidableEq W] (M : Model W Atom) {φ : Formula Atom}

theorem iSup_ofSet_unrestricted (hφ : φ.IsModalFree) :
    ⨆ p ∈ unrestricted M.val φ, Question.ofSet p = proposition M φ := by
  induction φ with
  | atom p => rw [unrestricted, iSup_singleton, proposition_atom]
  | bot => rw [unrestricted, iSup_singleton, Question.ofSet_empty, proposition_bot]
  | conj φ ψ ihφ ihψ =>
    rw [unrestricted, iSup_ofSet_pro, ← Question.biSup_ofSet_inf_biSup_ofSet, ihφ hφ.1, ihψ hφ.2,
      proposition_conj]
  | impl φ ψ ihφ ihψ =>
    rw [unrestricted, iSup_ofSet_pro,
      ← Question.biSup_ofSet_himp_biSup_ofSet (isProposition_unrestricted _ ψ).1, ihφ hφ.1,
      ihψ hφ.2, proposition_impl]
  | inqDisj φ ψ ihφ ihψ =>
    rw [unrestricted, iSup_ofSet_pro, iSup_union, ihφ hφ.1, ihψ hφ.2, proposition_inqDisj]
  | nec => exact hφ.elim
  | ent => exact hφ.elim

theorem iSup_ofSet_restricted (hφ : φ.IsModalFree) :
    ⨆ p ∈ restricted M.val φ, Question.ofSet p = proposition M φ := by
  induction φ with
  | atom p => rw [restricted, iSup_singleton, proposition_atom]
  | bot => rw [restricted, iSup_singleton, Question.ofSet_empty, proposition_bot]
  | conj φ ψ ihφ ihψ =>
    rw [restricted, Question.biSup_ofSet_setOf_maximal (toFinite _),
      ← Question.biSup_ofSet_inf_biSup_ofSet, ihφ hφ.1, ihψ hφ.2, proposition_conj]
  | impl φ ψ ihφ ihψ =>
    rw [restricted, Question.biSup_ofSet_setOf_maximal (toFinite _),
      ← Question.biSup_ofSet_himp_biSup_ofSet (restricted_nonempty _ ψ), ihφ hφ.1, ihψ hφ.2,
      proposition_impl]
  | inqDisj φ ψ ihφ ihψ =>
    rw [restricted, Question.biSup_ofSet_setOf_maximal (toFinite _), iSup_union, ihφ hφ.1,
      ihψ hφ.2, proposition_inqDisj]
  | nec => exact hφ.elim
  | ent => exact hφ.elim

/-- A possibility is maximal among the possibilities for a formula just in case it is one of the
formula's restricted possibilities (p. 99). -/
theorem setOf_maximal_unrestricted (hφ : φ.IsModalFree) :
    {p | Maximal (· ∈ unrestricted M.val φ) p} = restricted M.val φ := by
  rw [← Question.alt_biSup_ofSet_eq (isProposition_unrestricted _ φ).1,
    iSup_ofSet_unrestricted M hφ, ← iSup_ofSet_restricted M hφ,
    Question.alt_biSup_ofSet (restricted_nonempty _ φ) (isAntichain_restricted _ φ)]

-- p. 99
theorem isInquisitive_unrestricted_iff (hφ : φ.IsModalFree) :
    IsInquisitive (unrestricted M.val φ) ↔ (restricted M.val φ).Nontrivial := by
  rw [IsInquisitive, setOf_maximal_unrestricted M hφ]

/-- The possibilities for a formula cover its truth set (Proposition 15). -/
theorem sUnion_unrestricted (hφ : φ.IsModalFree) : ⋃₀ unrestricted M.val φ = truthSet M φ := by
  rw [← Question.info_biSup_ofSet, iSup_ofSet_unrestricted M hφ, info_proposition]

theorem sUnion_restricted (hφ : φ.IsModalFree) : ⋃₀ restricted M.val φ = truthSet M φ := by
  rw [← Question.info_biSup_ofSet, iSup_ofSet_restricted M hφ, info_proposition]

end Coincidence

/-! ### Might (§3.2) -/

section Might

theorem unrestricted_neg (φ : Formula Atom) :
    unrestricted v φ.neg = {(⋃₀ unrestricted v φ)ᶜ} := by
  have h : (fun f : unrestricted v φ → unrestricted v .bot ↦
      ⋂ a : unrestricted v φ, (a : Set W)ᶜ ∪ f a) = fun _ ↦ (⋃₀ unrestricted v φ)ᶜ := by
    funext f
    ext w
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_sUnion, not_exists, not_and]
    refine ⟨fun h a ha hw ↦ (h ⟨a, ha⟩).elim (· hw) fun hf ↦ ?_, fun h a ↦ .inl (h a a.2)⟩
    rw [show (f ⟨a, ha⟩ : Set W) = ∅ from (f ⟨a, ha⟩).2] at hf
    exact hf
  have : Nonempty (unrestricted v (.bot : Formula Atom)) := ⟨⟨∅, by rw [unrestricted]; rfl⟩⟩
  show unrestricted v (.impl φ .bot) = _
  rw [unrestricted, h, range_const, (isProposition_singleton _).pro_eq]

theorem unrestricted_top : unrestricted v (Formula.neg .bot : Formula Atom) = {univ} := by
  rw [unrestricted_neg]
  simp [unrestricted]

variable {φ : Formula Atom}

-- §3.2
theorem mem_unrestricted_might {p : Set W} (hφp : p ∈ unrestricted v φ) (hp : p.Nonempty) :
    p ∈ unrestricted v (might φ) := by
  show p ∈ pro (unrestricted v (Formula.neg .bot) ∪ unrestricted v φ)
  exact (mem_pro hp).2 (.inr hφp)

theorem proposition_might [Fintype W] [DecidableEq W] (M : Model W Atom) :
    proposition M (might φ) = ⊤ := by
  rw [proposition_inqDisj, proposition_impl, proposition_bot, himp_self, top_sup_eq]

/-- In the restricted semantics *might φ* expresses the tautology `{univ}`, since its trivial
possibility includes every other (p. 100). -/
theorem restricted_might : restricted v (might φ) = {univ} := by
  have htop : univ ∈ restricted v (Formula.neg .bot : Formula Atom) ∪ restricted v φ :=
    .inl ⟨⟨id, iInter_eq_univ.2 fun _ ↦ compl_union_self _⟩, fun _ _ _ ↦ subset_univ _⟩
  ext p
  exact ⟨fun hp ↦ hp.eq_of_subset htop (subset_univ p),
    fun h ↦ h ▸ ⟨htop, fun _ _ _ ↦ subset_univ _⟩⟩

variable [Nonempty W]

theorem univ_mem_unrestricted_might : univ ∈ unrestricted v (might φ) := by
  show univ ∈ pro (unrestricted v (Formula.neg .bot) ∪ unrestricted v φ)
  rw [mem_pro univ_nonempty, unrestricted_top]
  exact .inl rfl

-- §3.2, Proposition 25
theorem might_not_informative_not_inquisitive [Finite W] :
    ¬ IsInformative (unrestricted v (might φ)) ∧ ¬ IsInquisitive (unrestricted v (might φ)) :=
  (univ_mem_iff (toFinite _) (isProposition_unrestricted v _).1).1
    (univ_mem_unrestricted_might v)

/-- *Might φ* is attentive just in case `φ` has a nonempty possibility other than the trivial
one (§3.2, Figure 2). -/
theorem isAttentive_might_iff :
    IsAttentive (unrestricted v (might φ)) ↔ ∃ p ∈ unrestricted v φ, p.Nonempty ∧ p ≠ univ := by
  constructor
  · rintro ⟨q, hq, hnm⟩
    have hq' : q ∈ pro (unrestricted v (Formula.neg .bot) ∪ unrestricted v φ) := hq
    have hne : q.Nonempty := nonempty_iff_ne_empty.2 fun h0 ↦ by
      rw [h0, empty_mem_pro_iff, unrestricted_top] at hq'
      have h : univ ∈ ({∅} : Set (Set W)) := hq' ▸ mem_union_left _ (mem_singleton univ)
      exact univ_nonempty.ne_empty h
    have hU : q ≠ univ := fun h ↦ hnm ⟨hq, fun r _ hqr ↦ h ▸ subset_univ r⟩
    rw [mem_pro hne, unrestricted_top] at hq'
    exact ⟨q, hq'.resolve_left hU, hne, hU⟩
  · rintro ⟨p, hp, hpne, hpU⟩
    exact isAttentive_of_ssubset (mem_unrestricted_might v hp hpne)
      (univ_mem_unrestricted_might v) (ssubset_univ_iff.2 hpU)

-- Figure 2
theorem isAttentive_might_atom {a : Atom} (h₁ : {w | v a w}.Nonempty) (h₂ : {w | v a w} ≠ univ) :
    IsAttentive (unrestricted v (might (.atom a))) :=
  (isAttentive_might_iff v).2 ⟨_, by simp [unrestricted], h₁, h₂⟩

end Might

/-! ### Questions and attentiveness (§3.3) -/

theorem unrestricted_polarQ (φ : Formula Atom) :
    unrestricted v φ.polarQ = pro (unrestricted v φ ∪ {(⋃₀ unrestricted v φ)ᶜ}) := by
  show pro (unrestricted v φ ∪ unrestricted v φ.neg) = _
  rw [unrestricted_neg]

theorem not_isInformative_polarQ (φ : Formula Atom) :
    ¬ IsInformative (unrestricted v φ.polarQ) := by
  rw [unrestricted_polarQ, IsInformative, sUnion_pro, sUnion_union, sUnion_singleton,
    union_compl_self, not_not]

/-- The non-informative closure `?φ` is attentive just in case `φ` is, so it is a question,
neither informative nor attentive, just in case `φ` is not attentive (Proposition 24). -/
theorem isAttentive_polarQ_iff (φ : Formula Atom) :
    IsAttentive (unrestricted v φ.polarQ) ↔ IsAttentive (unrestricted v φ) := by
  have hS := (isProposition_unrestricted v φ).2
  rw [unrestricted_polarQ, isAttentive_pro_iff]
  constructor
  · rintro ⟨q, ⟨hq, hq0⟩, hnm⟩
    obtain ⟨r, hqr, ⟨hr, -⟩⟩ := (not_maximal_iff_exists_gt ⟨hq, hq0⟩).1 hnm
    have hq0 : q ≠ ∅ := hq0
    rcases hq with hq | rfl
    · rcases hr with hr | rfl
      · exact ⟨q, hq, fun hmax ↦ hqr.ne (hmax.eq_of_subset hr hqr.le)⟩
      · exact (hq0 (subset_empty_iff.1 fun w hw ↦ hqr.le hw (subset_sUnion_of_mem hq hw))).elim
    · rcases hr with hr | rfl
      · exact (hq0 (subset_empty_iff.1 fun w hw ↦ hw (subset_sUnion_of_mem hr (hqr.le hw)))).elim
      · exact (hqr.ne rfl).elim
  · rintro ⟨p, hp, hnm⟩
    obtain ⟨q, hpq, hq⟩ := (not_maximal_iff_exists_gt hp).1 hnm
    have hp0 : p ≠ ∅ := by
      rintro rfl
      rw [hS.resolve_left (not_not.2 hp)] at hq
      exact hpq.ne hq.symm
    exact isAttentive_of_ssubset ⟨.inl hp, hp0⟩
      ⟨.inl hq, fun h ↦ hp0 (subset_empty_iff.1 (h ▸ hpq.le))⟩ hpq

theorem not_isAttentive_polarQ_atom (a : Atom) :
    ¬ IsAttentive (unrestricted v (Formula.polarQ (.atom a))) := by
  rw [isAttentive_polarQ_iff, unrestricted, not_isAttentive_iff]
  exact IsAntichain.singleton

end CiardelliGroenendijkRoelofsen2009
