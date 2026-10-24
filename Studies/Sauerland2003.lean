module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Pragmatics.Competition

/-!
# Sauerland (2003): a new semantics for number

Sauerland locates the interpreted number feature in a φ-head above DP and interprets agreement
features as presuppositions: `[Sg]` is the identity function presupposing an atom (his entry
admits an atom or a mass; `Number.dom` keeps the atomic case), `[Pl]` the identity with no
presupposition, and Heim's Maximize Presupposition has the speaker use the most specific feature
whose presupposition holds, (7). In competition with the singular the plural is therefore
unblocked only at non-atoms (`unblocked_plural`), which the coordination *Kai and Lina* shows
(`coordination_plural`), and at atoms too once the singular is blocked by an independent factor,
singular *they* (13) or polite address (14) (`unblocked_plural_of_singular_blocked`).
The two domains are nested (`sg_domain_ssubset_pl`), an instance of his Feature-Subset
Principle (46), and since the features are domain restrictions the competition is
presuppositional rather than scalar. The person features (44) compete the same way: the second
person is used outside the first person's domain and the third outside the participants', the
non-participant presupposition of (47) (`unblocked_second`, `unblocked_third`), except in a
context whose speaker is part of the addressee, where the first and second person domains
coincide and competition cannot separate them (`unblocked_second_of_degenerate`).

*Every* decomposes into a definite `DER`, taking the maximal element of a cumulative
restrictor (`der_unique`; his cover-based `*` is `Mereology.algClosure_iff_exists_sup'`),
and `JE`, a universal over the atomic parts of a group individual that projects its scope's
presupposition universally (`JE`), whose truth on a bivalent scope is Link's distributivity
operator (`je_eq_one_iff_D`, `je_eq_one_iff_forall`). The indefinite projects existentially
(`aSem`), so *every boy invited his sister* requires every boy to have a sister while *a boy
invited his sister* requires one (`projection_asymmetry`), and the weak plural makes *Lina
didn't harvest tomatoes* entail *Lina didn't harvest a tomato*
(`negated_pl_entails_negated_sg`). The same mechanism runs Czech gender agreement on
coordinations, masculine vacuous, feminine presupposing non-masculinity and neuter
presupposing genderlessness (`czech_gender`), and predicts that polite address recruits the
unmarked values, plural and third person (`politeness_unmarked`).

## References

* [sauerland-2003]
* [heim-1991], [link-1987]
-/

@[expose] public section

namespace Sauerland2003

open Mereology (Atom AlgClosure cum_maximal_unique algClosure_cum not_atom_sup_of_ne)
open Mereology (D)
open Competition Trivalent

variable {E : Type*}

/-! ### Number features and Maximize Presupposition -/

section Number

variable [SemilatticeSup E] {a b : E}

theorem coordination_plural (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    a ⊔ b ∉ Number.dom (E := E) (some .singular) :=
  (Number.mem_dom_singular _).not.2 (not_atom_sup_of_ne ha hb hne)

theorem sg_domain_ssubset_pl (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    Number.dom (E := E) (some .singular) ⊂ Number.dom (some .plural) := by
  rw [Number.dom_plural]
  exact ⟨Set.subset_univ _, fun h ↦ coordination_plural ha hb hne (h (Set.mem_univ _))⟩

theorem der_unique {R : E → Prop} {m₁ m₂ : E} (h₁ : Maximal (AlgClosure R) m₁)
    (h₂ : Maximal (AlgClosure R) m₂) : m₁ = m₂ :=
  cum_maximal_unique algClosure_cum h₁ h₂

/-- The two number features that can head a φP are each other's alternatives. -/
def numberAlts : Option Number → Set (Option Number) := fun _ ↦ {some .singular, some .plural}

theorem unblocked_singular :
    unblocked numberAlts Number.dom (some .singular) = {x : E | Atom x} := by
  rw [unblocked_eq_self]
  · ext x; exact Number.mem_dom_singular x
  · rintro ⟨ψ, hψ, hss⟩
    rcases hψ with rfl | rfl
    · exact hss.ne rfl
    · exact hss.not_subset fun x _ ↦ by rw [Number.dom_plural]; trivial

theorem unblocked_plural (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    unblocked numberAlts Number.dom (some .plural) = {x : E | ¬ Atom x} := by
  rw [unblocked_eq_sdiff (ψ := some .singular) (Set.mem_insert _ _)
    (sg_domain_ssubset_pl ha hb hne)]
  · ext x; simp [Number.mem_dom_singular]
  · rintro χ (rfl | rfl) hss
    · exact le_rfl
    · exact absurd rfl hss.ne

/-- With `[Sg]` blocked by an independent factor, `[Pl]` is used of atoms too, (13)–(14). -/
theorem unblocked_plural_of_singular_blocked :
    unblocked (fun _ ↦ {some .plural}) (Number.dom (E := E)) (some .plural) = Set.univ := by
  rw [unblocked_eq_self, Number.dom_plural]
  rintro ⟨ψ, hψ, hss⟩
  rw [Set.mem_singleton_iff.1 hψ] at hss
  exact hss.ne rfl

theorem atom_mem_unblocked_iff (ha : Atom a) (hb : Atom b) (hne : a ≠ b) :
    a ∉ unblocked numberAlts Number.dom (some .plural) ∧
      a ∈ unblocked (fun _ ↦ {some .plural}) Number.dom (some .plural) := by
  rw [unblocked_plural ha hb hne, unblocked_plural_of_singular_blocked]
  exact ⟨fun h ↦ h ha, Set.mem_univ _⟩

end Number

/-! ### Person -/

section Person

variable {W P T : Type*} [PartialOrder E] (c : Kaplan.Context W E P T)

/-- The three person features that can head a φP are each other's alternatives, (44). -/
def personAlts : Option Person → Set (Option Person) :=
  fun _ ↦ {some .first, some .second, some .third}

theorem dom_first_ssubset_dom_second (h : ¬ c.agent ≤ c.addressee) :
    Person.dom c (some .first) ⊂ Person.dom c (some .second) := by
  refine ⟨fun x hx ↦ (Person.mem_dom_second c x).2 (Or.inl ((Person.mem_dom_first c x).1 hx)),
    fun hsub ↦ h ?_⟩
  exact (Person.mem_dom_first c _).1 (hsub ((Person.mem_dom_second c c.addressee).2
    (Or.inr le_rfl)))

theorem unblocked_first :
    unblocked personAlts (Person.dom c) (some .first) = Person.dom c (some .first) := by
  refine unblocked_eq_self ?_
  rintro ⟨ψ, hψ, hss⟩
  simp only [personAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
  rcases hψ with rfl | rfl | rfl
  · exact hss.ne rfl
  · exact hss.not_subset fun x hx ↦
      (Person.mem_dom_second c x).2 (Or.inl ((Person.mem_dom_first c x).1 hx))
  · exact hss.not_subset (Person.dom_third c ▸ Set.subset_univ _)

theorem unblocked_second (h : ¬ c.agent ≤ c.addressee) :
    unblocked personAlts (Person.dom c) (some .second) =
      Person.dom c (some .second) \ Person.dom c (some .first) := by
  refine unblocked_eq_sdiff (by simp [personAlts]) (dom_first_ssubset_dom_second c h) ?_
  rintro χ hχ hss
  simp only [personAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hχ
  rcases hχ with rfl | rfl | rfl
  · exact le_rfl
  · exact absurd rfl hss.ne
  · exact absurd (Person.dom_third c ▸ Set.subset_univ _) hss.not_subset

theorem unblocked_second_of_degenerate (h : c.agent ≤ c.addressee) :
    unblocked personAlts (Person.dom c) (some .second) = Person.dom c (some .second) := by
  refine unblocked_eq_self ?_
  rintro ⟨ψ, hψ, hss⟩
  simp only [personAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
  rcases hψ with rfl | rfl | rfl
  · refine hss.not_subset fun x hx ↦ (Person.mem_dom_first c x).2 ?_
    rcases (Person.mem_dom_second c x).1 hx with hx | hx
    exacts [hx, h.trans hx]
  · exact hss.ne rfl
  · exact hss.not_subset (Person.dom_third c ▸ Set.subset_univ _)

/-- The third person is used outside the participants' domain, the non-participant
presupposition of (47), when some referent lies outside it. -/
theorem unblocked_third (h : ∃ x, x ∉ Person.dom c (some .second)) :
    unblocked personAlts (Person.dom c) (some .third) = (Person.dom c (some .second))ᶜ := by
  obtain ⟨x, hx⟩ := h
  have hss : Person.dom c (some .second) ⊂ Person.dom c (some .third) :=
    Person.dom_third c ▸ Set.ssubset_univ_iff.2 fun h ↦ hx (h ▸ Set.mem_univ x)
  rw [unblocked_eq_sdiff (by simp [personAlts]) hss, Person.dom_third, Set.compl_eq_univ_sdiff]
  rintro χ hχ hss'
  simp only [personAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hχ
  rcases hχ with rfl | rfl | rfl
  · exact fun y hy ↦ (Person.mem_dom_second c y).2 (Or.inl ((Person.mem_dom_first c y).1 hy))
  · exact le_rfl
  · exact absurd rfl hss'.ne

end Person

/-! ### *Every* as `JE ∘ DER`, and the indefinite -/

/-- The indefinite projects its scope's presupposition existentially, defined when the scope is
defined of some individual of the restrictor and true when it is true of one. -/
noncomputable def aSem (R : E → Prop) (S : E → SignType) : SignType :=
  existsHaug fun x : {x // R x} ↦ S x

section Every

variable [PartialOrder E]

/-- `JE`, the quantificational part of *every*, ranges over the atomic parts of a group
individual `X`, presupposing the scope predicate is defined at each and asserting it holds
at each. -/
noncomputable def JE (X : E) (P : E → SignType) : SignType :=
  forallWeak fun a : {a // Atom a ∧ a ≤ X} ↦ P a

theorem je_eq_one_iff_forall {R Q : E → Prop} [DecidablePred Q] {maxR : E}
    (hR : ∀ x, R x ↔ Atom x ∧ x ≤ maxR) :
    JE maxR (fun x ↦ SignType.ofProp (Q x)) = 1 ↔ ∀ x, R x → Q x := by
  simp [JE, hR]

theorem projection_asymmetry {boys a₁ a₂ : E} {R : E → Prop} {S : E → SignType}
    (ha₂ : Atom a₂) (h₂ : a₂ ≤ boys) (hR₁ : R a₁) (hdom₁ : S a₁ ≠ 0) (hdom₂ : S a₂ = 0) :
    aSem R S ≠ 0 ∧ JE boys S = 0 :=
  ⟨fun h ↦ hdom₁ (existsHaug_eq_zero_iff.1 h ⟨a₁, hR₁⟩),
    forallWeak_eq_zero_iff.2 ⟨⟨a₂, ha₂, h₂⟩, hdom₂⟩⟩

theorem negated_pl_entails_negated_sg {starR harvest : E → Prop} [DecidablePred harvest]
    (h : aSem starR (fun x ↦ SignType.ofProp (harvest x)) = -1)
    (hsg : aSem (fun x ↦ Atom x ∧ starR x) (fun x ↦ SignType.ofProp (harvest x)) ≠ 0) :
    aSem (fun x ↦ Atom x ∧ starR x) (fun x ↦ SignType.ofProp (harvest x)) = -1 := by
  simp_all [aSem]

end Every

theorem je_eq_one_iff_D [SemilatticeSup E] (X : E) (P : E → Prop) [DecidablePred P] :
    JE X (fun x ↦ SignType.ofProp (P x)) = 1 ↔ D P X := by
  simp only [JE, forallWeak_eq_one_iff, SignType.ofProp_eq_one_iff, Subtype.forall, and_imp, D]
  exact forall_congr' fun _ ↦ imp.swap

/-! ### Gender agreement in Czech coordinations -/

/-- A conjunct of one of Sauerland's Czech coordinations is a man, a woman or a child. -/
inductive Conjunct where
  | man
  | woman
  | child
  deriving DecidableEq, Repr

/-- A coordination is gendered masculine when a conjunct is a man, and feminine when a conjunct is
a woman and none is a man; a coordination of children is gendered neither way. -/
instance gendered : Gendered (Finset Conjunct) where
  masculine := {s | ∃ r ∈ s, r = .man}
  feminine := {s | (∃ r ∈ s, r = .woman) ∧ ∀ r ∈ s, r ≠ .man}
  disjoint := Set.disjoint_left.mpr fun _ ⟨r, hr, hm⟩ ⟨_, hno⟩ ↦ hno r hr hm

/-- *Jan a Věra*, *Matka a její dítě* and *Otec a jeho dítě*, as the sums of their conjuncts. -/
def janVera : Finset Conjunct := {.man, .woman}
def matkaDite : Finset Conjunct := {.woman, .child}
def otecDite : Finset Conjunct := {.man, .child}

theorem czech_gender :
    janVera ∉ Gender.dom (some .Fem) ∧
      matkaDite ∈ Gender.dom (some .Fem) ∧
      matkaDite ∉ Gender.dom (some .Neut) ∧
      otecDite ∉ Gender.dom (some .Fem) ∧
      otecDite ∈ Gender.dom (some .Masc) := by
  simp only [Gender.mem_dom_feminine, Gender.mem_dom_neuter, Gender.dom_masculine, Set.mem_univ,
    and_true, Gendered.masculine, Gendered.feminine, Set.mem_ofPred_eq]
  decide

/-! ### Politeness -/

theorem politeness_unmarked {W P T : Type*} [PartialOrder E] (c : Kaplan.Context W E P T) :
    Number.dom (E := E) (some .plural) = Set.univ ∧ Person.dom c (some .third) = Set.univ :=
  ⟨rfl, rfl⟩

end Sauerland2003
