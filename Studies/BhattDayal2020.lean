module

public import Linglib.Semantics.Questions.Polar
public import Linglib.Semantics.Questions.Constituent
public import Linglib.Fragments.HindiUrdu.Particles

/-!
# Bhatt and Dayal 2020: the polar question particle kya:

This file formalizes Bhatt and Dayal's analysis of Hindi-Urdu polar *kya:*. The particle is
not a clause-typing Q-morpheme of the Japanese *-ka* kind: it occurs in polar and
alternative questions but not in constituent questions, and it embeds under rogative
predicates and modified responsives but not under plain responsives — the quasi-subordinated
configuration, which the authors place in a projection above CP, ForceP, that only some
predicates select. Semantically *kya:* is the identity on its sister question, defined only
when that question's alternative set is a singleton; a polar question denotes the singleton
of its nucleus proposition, a constituent question a plural set. An alternative question is
the disjunction of two polar questions and so has two alternatives; *kya:* is licensed in it
by applying inside a disjunct, and fails when it scopes over the disjunction. That failure
rules out one parse of clause-final *kya:* with a disjunction (51); the paper leaves open why
the other parse, with *kya:* on the second disjunct (52), is unavailable.

## Main definitions

* `KyaDefined`: the domain of *kya:*, a sister with a single alternative (23).
* `altQ`: the alternative question *p or q* as the disjunction of two polar questions.
* `selectsForceP`: the embedding contexts whose selecting predicate takes a ForceP
  complement.

## Implementation notes

Questions are inquisitive contents, and the paper's Hamblin set is a content's set of
alternatives `alt`: the polar question `{p}` of (22b) is `ofSet p` and the constituent
question of (22a) is `which`. Inquisitive contents do not separate declaratives from
interrogatives, so the declarative *p* is `ofSet p` as well and meets the presupposition. The
paper keeps *kya:* off declaratives by a type distinction instead, and names Roelofsen and
Farkas's highlighting as the replacement in theories without one; Xu analyses *nandao* that
way. `kyaDefined_iff_not_isInquisitive` states the collapse. The
paper's alternative question is the union `{p, q}` of the two disjuncts; the inquisitive
disjunction `altQ p q` has both as alternatives only when neither entails the other, which
the theorems about it assume.

## References

* [bhatt-dayal-2020]
* [dayal-grimshaw-2009]: quasi-subordination.
* [roelofsen-farkas-2015]: highlighting, the alternative to the singleton requirement.
* [xu-2012], [xu-2017]: the Mandarin *nandao* analysis the account draws on.
-/

@[expose] public section

namespace BhattDayal2020

open Question HindiUrdu.Particles Clause

variable {W : Type*}

/-! ### The singleton presupposition -/

/-- *kya:* is defined (23) when its sister has a single alternative, the paper's
`∃p ∈ Q[∀q[q ∈ Q → q = p]]` read on the sister's alternatives. On that domain *kya:* is the
identity. -/
def KyaDefined (Q : Question W) : Prop := ∃ p, alt Q = {p}

theorem not_kyaDefined_of_mem_alt {Q : Question W} {p₁ p₂ : Set W} (h₁ : p₁ ∈ alt Q)
    (h₂ : p₂ ∈ alt Q) (hne : p₁ ≠ p₂) : ¬KyaDefined Q := fun ⟨_, hp⟩ ↦
  (Set.nontrivial_of_mem_mem_ne h₁ h₂ hne).ne_singleton hp

/-- A polar question denotes the singleton of its nucleus proposition (22b), so *kya:* is
defined on it and returns it (23). -/
theorem kya_polar (p : Set W) : KyaDefined (ofSet p) := ⟨p, alt_ofSet p⟩

/-- A constituent question with two distinct answer cells is not a singleton (22a), so
*kya:* is undefined on it (4). -/
theorem kya_not_wh {E : Type*} {D : Set E} {P : E → Set W}
    (hD : D.Nonempty) (hA : IsAntichain (· ⊆ ·) (P '' D))
    {e₁ e₂ : E} (h₁ : e₁ ∈ D) (h₂ : e₂ ∈ D) (hPne : P e₁ ≠ P e₂) :
    ¬KyaDefined (which D P) := by
  refine not_kyaDefined_of_mem_alt ?_ ?_ hPne <;> rw [alt_which_of_antichain hD hA]
  exacts [⟨e₁, h₁, rfl⟩, ⟨e₂, h₂, rfl⟩]

theorem kya_not_two_cell {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬KyaDefined (polar (W := W) p) := by
  have halt := alt_polar_of_nontrivial hne hnu
  refine not_kyaDefined_of_mem_alt (p₁ := p) (p₂ := pᶜ) (by simp [halt]) (by simp [halt])
    fun h ↦ hne (Set.eq_empty_of_forall_notMem fun w hw ↦ (h ▸ hw : w ∈ pᶜ) hw)

/-- The presupposition picks out exactly the non-inquisitive contents among the normal ones.
The declarative *p* meets it as well as the polar question, since both are `ofSet p`. -/
theorem kyaDefined_iff_not_isInquisitive {Q : Question W} (hQ : Q.IsNormal) :
    KyaDefined Q ↔ ¬Q.IsInquisitive :=
  hQ.exists_alt_eq_singleton_iff.trans (info_mem_iff_not_isInquisitive Q)

/-! ### Alternative questions -/

/-- The alternative question *p or q* is the disjunction of the two polar questions, (44) and
(52). -/
def altQ (p q : Set W) : Question W := ofSet p ⊔ ofSet q

theorem mem_alt_altQ_left {p q : Set W} (h : ¬ p ⊆ q) : p ∈ alt (altQ p q) :=
  mem_alt_sup_of_alt_left (by simp) fun _ hr hpr => absurd (hpr.trans hr) h

theorem mem_alt_altQ_right {p q : Set W} (h : ¬ q ⊆ p) : q ∈ alt (altQ p q) :=
  mem_alt_sup_of_alt_right (by simp) fun _ hr hqr => absurd (hqr.trans hr) h

/-- *kya:* over an alternative question fails its presupposition ((43), (51)), while each disjunct
meets it ((44), (47), (52)). -/
theorem altQ_not_kyaDefined {p q : Set W} (hpq : ¬p ⊆ q) (hqp : ¬q ⊆ p) :
    ¬KyaDefined (altQ p q) :=
  not_kyaDefined_of_mem_alt (mem_alt_altQ_left hpq) (mem_alt_altQ_right hqp)
    fun h ↦ hpq h.le

-- (45)
theorem kya_polar_disjunction (p q : Set W) : KyaDefined (ofSet (p ∪ q)) := kya_polar _

/-! ### Distribution -/

/-- The embedding contexts whose selecting predicate takes a ForceP complement, (21), are the
matrix clause and quasi-subordination, not ordinary subordination. -/
def selectsForceP (e : EmbeddingContext) : Prop :=
  e = .matrix ∨ e = .quasiSubordinated

instance (e : EmbeddingContext) : Decidable (selectsForceP e) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Over the contexts the paper records, *kya:* is licensed exactly where ForceP is selected
((8), (9), (21)). -/
theorem kya_licensed_iff_selectsForceP :
    ∀ e, e ≠ EmbeddingContext.quotation →
      (e ∈ kya.distribution.possible.cod ↔ selectsForceP e) := by
  decide

/-- *kya:* is licensed in polar and alternative questions and not in constituent questions,
(4) and (5). -/
theorem kya_clause_types :
    ∀ c, c ∈ kya.distribution.possible.dom ↔ c = Clause.SentenceType.polar ∨ c = .alternative := by
  decide

end BhattDayal2020
