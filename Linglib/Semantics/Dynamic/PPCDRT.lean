module

public import Linglib.Semantics.Dynamic.PCDRT

/-!
# Partial Plural CDRT

Haug and Dalrymple's Partial Plural Compositional DRT joins the plural information states of
Plural CDRT (Brasoveanu, Dotlačil) with the partial assignments of Partial CDRT (Haug), in which
an anaphoric condition is a presupposition rather than a resolution the grammar makes. A condition
of a PPDRS is a property of the output state `S` and of the set `Δ` of drefs the DRS distributes
over. The class of a row `s` under distribution, `eqClass S Δ s`, is the set of rows of `S` that
agree with `s` on `Δ`.

We define three anaphoric relations between an anaphor `u` and its antecedent `v`, after
Higginbotham and Williams:

* binding, `bindingCond`: `s u = s v` in every row `s`, which needs c-command;
* group identity, `groupIdentityCond`: `value u (eqClass S Δ s) = value v S` for every row `s`,
  so that the anaphor's values over each class are the antecedent's values over the whole state
  and the antecedent escapes the distribution;
* reciprocity, `reciprocityCond`: group identity with the two drefs distinct in every row, the
  contribution of *each other*. Without the distinctness it is `underspecifiedCond`, the meaning
  of German *sich* or the Cheyenne reflexive/reciprocal affix (Murray, Cable).

Without distribution, group identity is equality of the two drefs' values
(`groupIdentityCond_empty`), and reciprocity says that their dependency is irreflexive with equal
domain and codomain (`reciprocityCond_empty_iff`). Where the rows that agree on `Δ` agree on
its antecedent, as they do when the antecedent is in `Δ`, a bound anaphor has at most one value
in each class (`subsingleton_value_of_bindingCond`), while the antecedent of a reciprocal has two
values in the state (`nontrivial_value_of_reciprocityCond`), so a bound dref has no value for a
reciprocal inside the distribution to take as antecedent
(`value_eq_empty_of_bindingCond_of_reciprocityCond`).

Partial dref introduction `extend u` relates `i` to `o` when `o` values `u`, `i` does not, and
the two agree on every other dref. It is a covering step of the extension order
(`mem_extend_iff_covBy`), and its cumulative lift to plural states, `introPartial u`, refines
Plural CDRT's introduction (`introPartial_subset_intro`).

## References

* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [D. T. T. Haug, *Partial dynamic semantics for anaphora: Compositionality without syntactic
  coindexation* (2014)][haug-2014]
* [A. Brasoveanu, *Structured nominal and modal reference* (2007)][brasoveanu-2007]
* [J. Dotlačil, *Reciprocals distribute over information states* (2013)][dotlacil-2013]
* [J. Higginbotham, *On semantics* (1985)][higginbotham-1985]
* [E. Williams, *Reciprocal scope* (1991)][williams-1991]
* [S. E. Murray, *Reflexivity and reciprocity with(out) underspecification* (2008)][murray-2008]
* [S. Cable, *Reflexives, reciprocals and contrast* (2014)][cable-2014]
-/

@[expose] public section

namespace PPCDRT

open PCDRT

variable {E : Type*}

/-- A PPDRS condition ([haug-dalrymple-2020] (27)): a property of the output plural state and of
the set `Δ` of drefs the DRS distributes over ((25)). -/
abbrev PPDRSCond (E : Type*) := PluralAssign ℕ E → Set ℕ → Prop

variable (uAnaph uAnt : ℕ) (S : PluralAssign ℕ E) (Δ : Set ℕ)

/-! ### Distribution -/

/-- The class of `s` under distribution over `Δ` ([haug-dalrymple-2020] (26)): the states of `S`
agreeing with `s` on every dref in `Δ`. -/
def eqClass (s : ℕ → Part E) : PluralAssign ℕ E :=
  {t ∈ S | Set.EqOn t s Δ}

@[simp] theorem eqClass_empty (s : ℕ → Part E) : eqClass S ∅ s = S := by
  ext t; simp [eqClass]

theorem mem_eqClass {s t : ℕ → Part E} : t ∈ eqClass S Δ s ↔ t ∈ S ∧ Set.EqOn t s Δ := Iff.rfl

theorem self_mem_eqClass {s : ℕ → Part E} (hs : s ∈ S) : s ∈ eqClass S Δ s :=
  ⟨hs, Set.eqOn_refl s Δ⟩

theorem eqClass_subset (s : ℕ → Part E) : eqClass S Δ s ⊆ S := fun _ h ↦ h.1

variable {S Δ} in
theorem eqClass_anti {Δ' : Set ℕ} (h : Δ ⊆ Δ') (s : ℕ → Part E) :
    eqClass S Δ' s ⊆ eqClass S Δ s :=
  fun _ ht ↦ ⟨ht.1, ht.2.mono h⟩

variable {S Δ} in
theorem eqClass_mono {T : PluralAssign ℕ E} (h : S ⊆ T) (s : ℕ → Part E) :
    eqClass S Δ s ⊆ eqClass T Δ s :=
  fun _ ht ↦ ⟨h ht.1, ht.2⟩

/-! ### Anaphoric relations -/

/-- Binding (`u_anaph = u_ant`, [haug-dalrymple-2020] (30)): the two drefs hold the same value in
every state, both defined and equal or both undefined. This is stronger than the coreference
presupposition of (29), which constrains only the states where both are defined. -/
def bindingCond : PPDRSCond E := fun S _ ↦ ∀ s ∈ S, s uAnaph = s uAnt

/-- Group identity (`∪u_anaph → ∪u_ant`, [haug-dalrymple-2020] (29), (38)): in every state, the
anaphor's values over the state's class under distribution are the antecedent's values over the
whole state. -/
def groupIdentityCond : PPDRSCond E := fun S Δ ↦
  ∀ s ∈ S, value uAnaph (eqClass S Δ s) = value uAnt S

/-- Reciprocity (`∪u_anaph → ∪u_ant`, `∂(u_anaph ≠ u_ant)`, [haug-dalrymple-2020] (41)): group
identity, with the two drefs distinct in every state where both are defined. -/
def reciprocityCond : PPDRSCond E := fun S Δ ↦
  groupIdentityCond uAnaph uAnt S Δ ∧
    ∀ s ∈ S, ∀ a ∈ s uAnaph, ∀ b ∈ s uAnt, a ≠ b

/-- The underspecified reflexive/reciprocal ([haug-dalrymple-2020] (79b)): group identity
without distinctness, admitting reflexive, reciprocal and mixed construals ([murray-2008],
[cable-2014]). -/
def underspecifiedCond : PPDRSCond E := groupIdentityCond uAnaph uAnt

/-- Without distribution, group identity is equality of the two drefs' values, the cumulative
identity `∪u_anaph = ∪u_ant` of [haug-dalrymple-2020] (39). -/
theorem groupIdentityCond_empty :
    groupIdentityCond uAnaph uAnt S ∅ ↔ value uAnaph S = value uAnt S := by
  simp only [groupIdentityCond, eqClass_empty]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ h⟩
  obtain rfl | ⟨s, hs⟩ := S.eq_empty_or_nonempty
  · simp [value]
  · exact h s hs

/-- Binding implies group identity without distribution. Under distribution the two come apart
([haug-dalrymple-2020] (24) against (31)). -/
theorem binding_implies_groupIdentity (h : bindingCond uAnaph uAnt S ∅) :
    groupIdentityCond uAnaph uAnt S ∅ := by
  intro s hs
  rw [eqClass_empty]
  exact Set.ext fun _ ↦ exists_congr fun g ↦ and_congr_right fun hg ↦ by
    change g uAnaph = _ ↔ g uAnt = _
    rw [h g hg]

/-- Reciprocity excludes binding once some state defines the anaphor: distinctness there
contradicts pointwise equality. Without such a state both drefs may be undefined throughout, and
binding and reciprocity hold together vacuously. -/
theorem reciprocity_excludes_binding (hdef : ∃ s ∈ S, (s uAnaph).Dom)
    (h : reciprocityCond uAnaph uAnt S Δ) : ¬ bindingCond uAnaph uAnt S Δ := fun hb ↦ by
  obtain ⟨s, hs, hd⟩ := hdef
  obtain ⟨d, hd⟩ := Part.dom_iff_mem.1 hd
  exact h.2 s hs d hd d (hb s hs ▸ hd) rfl

theorem reciprocity_strengthens_underspecified (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

variable {uAnaph uAnt S Δ}

/-- Without distribution, reciprocity says the antecedent-anaphor dependency is irreflexive with
equal domain and codomain ([haug-dalrymple-2020]'s gloss of (39)). -/
theorem reciprocityCond_empty_iff (hdef : ∀ s ∈ S, (s uAnaph).Dom ↔ (s uAnt).Dom) :
    reciprocityCond uAnaph uAnt S ∅ ↔
      (dep uAnt uAnaph S).dom = (dep uAnt uAnaph S).cod ∧ (dep uAnt uAnaph S).IsIrrefl := by
  rw [reciprocityCond, groupIdentityCond_empty,
    ← dom_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).2,
    ← cod_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).1, eq_comm]
  refine and_congr_right' ⟨fun h ↦ ⟨fun a ⟨s, hs, ha, ha'⟩ ↦
    h s hs a (Part.eq_some_iff.1 ha') a (Part.eq_some_iff.1 ha) rfl⟩, ?_⟩
  rintro h s hs a ha b hb rfl
  exact h.irrefl _ ⟨s, hs, Part.eq_some_iff.2 hb, Part.eq_some_iff.2 ha⟩

/-- A reciprocal's antecedent denotes a plurality: at a state defining both drefs, the
anaphor's value lies among the antecedent's by group identity and differs from the antecedent's
value there. This holds under any distribution. -/
theorem nontrivial_value_of_reciprocityCond (h : reciprocityCond uAnaph uAnt S Δ)
    {s : ℕ → Part E} (hs : s ∈ S) {a b : E} (ha : a ∈ s uAnaph) (hb : b ∈ s uAnt) :
    (value uAnt S).Nontrivial :=
  ⟨a, h.1 s hs ▸ ⟨s, self_mem_eqClass S Δ hs, Part.eq_some_iff.2 ha⟩,
    b, ⟨s, hs, Part.eq_some_iff.2 hb⟩, h.2 s hs a ha b hb⟩

/-- A bound anaphor holds one value throughout each class, where rows that agree on `Δ` agree on
its antecedent. -/
theorem eq_of_mem_eqClass_of_bindingCond (h : bindingCond uAnaph uAnt S Δ)
    (hΔ : ∀ t ∈ S, ∀ t' ∈ S, Set.EqOn t t' Δ → t uAnt = t' uAnt)
    {s t t' : ℕ → Part E} (ht : t ∈ eqClass S Δ s) (ht' : t' ∈ eqClass S Δ s) :
    t uAnaph = t' uAnaph := by
  rw [h t ht.1, h t' ht'.1, hΔ t ht.1 t' ht'.1 (ht.2.trans ht'.2.symm)]

/-- A bound anaphor denotes an individual: where rows that agree on `Δ` agree on its antecedent,
it has at most one value in each class. -/
theorem subsingleton_value_of_bindingCond (h : bindingCond uAnaph uAnt S Δ)
    (hΔ : ∀ t ∈ S, ∀ t' ∈ S, Set.EqOn t t' Δ → t uAnt = t' uAnt) (s : ℕ → Part E) :
    (value uAnaph (eqClass S Δ s)).Subsingleton :=
  fun _ ⟨_, ht, ha⟩ _ ⟨_, ht', hb⟩ ↦ Part.some_injective <|
    ha.symm.trans ((eq_of_mem_eqClass_of_bindingCond h hΔ ht ht').trans hb)

/-- A reciprocal inside the distribution cannot take a bound dref as its antecedent, where rows
that agree on `Δ` agree on the binder: the reciprocal would find the antecedent's value within
the class, where the antecedent holds that value in every row and so is nowhere distinct from
it. -/
theorem value_eq_empty_of_bindingCond_of_reciprocityCond {uRecip : ℕ}
    (hb : bindingCond uAnaph uAnt S Δ)
    (hΔ : ∀ t ∈ S, ∀ t' ∈ S, Set.EqOn t t' Δ → t uAnt = t' uAnt)
    (hr : reciprocityCond uRecip uAnaph S Δ) : value uAnaph S = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun d hd ↦ ?_
  obtain ⟨s, hs, hsd⟩ := id hd
  rw [← hr.1 s hs] at hd
  obtain ⟨t, ht, htd⟩ := hd
  have ht' : t uAnaph = Part.some d :=
    (eq_of_mem_eqClass_of_bindingCond hb hΔ ht (self_mem_eqClass S Δ hs)).trans hsd
  exact hr.2 t ht.1 d (Part.eq_some_iff.1 htd) d (Part.eq_some_iff.1 ht') rfl

/-! ### Partial dref introduction -/

section Introduction

open DynamicSemantics SetRel

variable {Var D : Type*} {u : Var} {i o : Var → Part D}

/-- Partial dref introduction `i[u]o` ([haug-dalrymple-2020] (20)): `i` leaves `u` unvalued, `o`
values it, and the two agree on every other dref. -/
def extend (u : Var) : Update (Var → Part D) :=
  {(i, o) | ¬(i u).Dom ∧ (o u).Dom ∧ ∀ v ≠ u, i v = o v}

theorem mem_extend : i ~[extend u] o ↔ ¬(i u).Dom ∧ (o u).Dom ∧ ∀ v ≠ u, i v = o v :=
  Iff.rfl

/-- Introducing `u` is a covering step of the extension order, the one that values `u`. -/
theorem mem_extend_iff_covBy : i ~[extend u] o ↔ i ⋖ o ∧ i u ≠ o u := by
  refine ⟨fun ⟨hi, ho, h⟩ ↦ ⟨Pi.covBy_iff.2 ⟨u, Part.covBy_iff.2 ⟨hi, ho⟩, h⟩,
    (Part.covBy_iff.2 ⟨hi, ho⟩).ne⟩,
    fun ⟨hcov, hne⟩ ↦ ?_⟩
  obtain ⟨x, hx, h⟩ := Pi.covBy_iff.1 hcov
  obtain ⟨hi, ho⟩ := Part.covBy_iff.1 hx
  obtain rfl : x = u := by_contra fun hxu ↦ hne (h u (Ne.symm hxu))
  exact ⟨hi, ho, h⟩

theorem extend_subset_randomAssign [DecidableEq Var] :
    extend u ⊆ Update.randomAssign (S := Var → Part D) u := by
  rintro ⟨i, o⟩ ⟨-, -, h⟩
  refine (Update.mem_randomAssign (i := i) (j := o) (r := u)).2 ⟨o u, funext fun v ↦ ?_⟩
  rw [RegisterStructure.extend_eq_update]
  by_cases hv : v = u
  · subst hv
    simp
  · rw [Function.update_of_ne hv]
    exact (h v hv).symm

/-- Partial dref introduction on plural states ([haug-dalrymple-2020] (6), after
[dotlacil-2013]): every input row has an extension at `u` among the output rows, every output row
extends some input row, and the output state is nonempty. It refines Plural CDRT's `PCDRT.intro`
(`introPartial_subset_intro`) in two ways: every output row values `u`, where a random assignment
may leave it ★, and the output is nonempty. -/
def introPartial (u : Var) : Update (PluralAssign Var D) :=
  {(I, O) | O.Nonempty ∧ I ~[Update.cumul (extend u)] O}

theorem introPartial_subset_intro [DecidableEq Var] :
    introPartial u ⊆ PCDRT.intro (S := Var → Part D) (V := Part D) u :=
  fun (_, _) hp ↦ Update.cumul_mono extend_subset_randomAssign hp.2

end Introduction

end PPCDRT
