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

Within each class, the dependency between a reciprocal and a group-identical antecedent is
irreflexive, and its domain and codomain are the values of the antecedent's own antecedent
(`dep_eqClass_of_groupIdentityCond_of_reciprocityCond`).

A DRS with universe `us` and conditions `C` is `box us C`: given `Δ`, it relates `I` to `O` when
`O` introduces `us` over `I` and every condition holds of `O` under `Δ`.

Partial dref introduction `extend u` relates `i` to `o` when `o` values `u`, `i` does not, and
the two agree on every other dref. It is a covering step of the extension order
(`mem_extend_iff_covBy`), and its cumulative lift to plural states, `introPartial u`, refines
Plural CDRT's introduction (`introPartial_subset_intro`).

## Implementation notes

A condition takes the distributed drefs `Δ` as an argument, and a DRS passes its `Δ` to its
conditions, as Haug and Dalrymple define them. The alternative is a distribution operator on
DRSs, Dotlačil's `δ_u`, which is `PCDRT.dist`: it evaluates the DRS on each cell of `u`
separately, so a condition inside it cannot read the whole state, and group identity needs the
whole state for its antecedent. The two agree on conditions that only read the class
(`dist_test_iff_of_local`), and the class under distribution over one dref is that dref's cell
(`eqClass_singleton`).

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

open PCDRT DynamicSemantics SetRel

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

variable {S} in
/-- The class of a row under distribution over one dref is that dref's cell. -/
theorem eqClass_singleton {u : ℕ} (s : ℕ → Part E) : eqClass S {u} s = cell u (s u) S := by
  ext t; simp [eqClass, Set.EqOn]

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

/-- Within each class, the dependency between a reciprocal and a group-identical antecedent is
irreflexive, with the matrix antecedent's values as its domain and its codomain. -/
theorem dep_eqClass_of_groupIdentityCond_of_reciprocityCond {u₁ u₂ u₃ : ℕ}
    (hg : groupIdentityCond u₂ u₁ S Δ) (hr : reciprocityCond u₃ u₂ S Δ)
    (hdef : ∀ s ∈ S, (s u₂).Dom ∧ (s u₃).Dom) {s : ℕ → Part E} (hs : s ∈ S) :
    (dep u₂ u₃ (eqClass S Δ s)).dom = value u₁ S ∧
      (dep u₂ u₃ (eqClass S Δ s)).cod = value u₁ S ∧
      (dep u₂ u₃ (eqClass S Δ s)).IsIrrefl := by
  have hsub := eqClass_subset S Δ s
  have h₂ : value u₂ S = value u₁ S :=
    Set.Subset.antisymm (fun x ⟨t, ht, hx⟩ ↦ hg t ht ▸ ⟨t, self_mem_eqClass S Δ ht, hx⟩)
      (hg s hs ▸ value_mono hsub)
  refine ⟨?_, ?_, ⟨fun a ⟨t, ht, ha, ha'⟩ ↦ ?_⟩⟩
  · rw [dom_dep fun t ht _ ↦ (hdef t (hsub ht)).2, hg s hs]
  · rw [cod_dep fun t ht _ ↦ (hdef t (hsub ht)).1, hr.1 s hs, h₂]
  · exact hr.2 t (hsub ht) a (Part.eq_some_iff.1 ha') a (Part.eq_some_iff.1 ha) rfl

/-- [dotlacil-2013]'s distribution operator, `PCDRT.dist`, reads a condition within each cell of
`u`; a condition that only reads the class holds there exactly when it holds under `Δ = {u}`. An
anaphoric condition reads the whole state as well, and so differs: its antecedent escapes the
distribution. -/
theorem dist_test_iff_of_local {c : PPDRSCond E} {u : ℕ}
    (hc : ∀ S Δ, c S Δ ↔ ∀ s ∈ S, c (eqClass S Δ s) ∅) (hu : ∀ s ∈ S, (s u).Dom) :
    S ~[dist u (Update.test {T | c T ∅})] S ↔ c S {u} := by
  rw [hc S {u}]
  constructor
  · rintro ⟨-, h⟩ s hs
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 (hu s hs)
    have hx' : s u = Part.some x := Part.eq_some_iff.2 hx
    rw [eqClass_singleton, hx']
    exact (Update.mem_test.1 (h x ⟨s, hs, hx'⟩)).2
  · intro h
    refine ⟨rfl, fun x ⟨s, hs, hx⟩ ↦ Update.mem_test.2 ⟨rfl, ?_⟩⟩
    have := h s hs
    rwa [eqClass_singleton, show s u = Part.some x from hx] at this

/-! ### Partial dref introduction -/

section Introduction

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

/-! ### Discourse representation structures -/

section Box

variable {I O : PluralAssign ℕ E} {Δ : Set ℕ} {u v : ℕ}

/-- `I[u₁ … uₙ]O`: the drefs introduced one after another. -/
def introList : List ℕ → Update (PluralAssign ℕ E)
  | [] => SetRel.id
  | u :: us => introPartial u ○ introList us

@[simp] theorem introList_nil : (introList [] : Update (PluralAssign ℕ E)) = SetRel.id := rfl

@[simp] theorem introList_cons (u : ℕ) (us : List ℕ) :
    (introList (u :: us) : Update (PluralAssign ℕ E)) = introPartial u ○ introList us := rfl

/-- Introduction leaves the other drefs' values in place. -/
theorem value_eq_of_mem_introPartial (hv : v ≠ u) (h : I ~[introPartial u] O) :
    value v O = value v I := by
  ext x
  constructor
  · rintro ⟨o, ho, hx⟩
    obtain ⟨i, hi, -, -, hio⟩ := h.2.2 o ho
    exact ⟨i, hi, (hio v hv).trans hx⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨o, ho, -, -, hio⟩ := h.2.1 i hi
    exact ⟨o, ho, (hio v hv).symm.trans hx⟩

theorem value_eq_of_mem_introList {us : List ℕ} (hv : v ∉ us) (h : I ~[introList us] O) :
    value v O = value v I := by
  induction us generalizing I with
  | nil => obtain rfl := h; rfl
  | cons u us ih =>
    obtain ⟨K, hIK, hKO⟩ := h
    rw [ih (fun h ↦ hv (List.mem_cons_of_mem _ h)) hKO,
      value_eq_of_mem_introPartial (fun h ↦ hv (by simp [h])) hIK]

/-- Every output row of an introduction comes from an input row that agrees with it on the
other drefs. -/
theorem exists_eq_of_mem_introList {us : List ℕ} (h : I ~[introList us] O) {o : ℕ → Part E}
    (ho : o ∈ O) : ∃ i ∈ I, ∀ v ∉ us, i v = o v := by
  induction us generalizing I with
  | nil => obtain rfl := h; exact ⟨o, ho, fun _ _ ↦ rfl⟩
  | cons u us ih =>
    obtain ⟨K, hIK, hKO⟩ := h
    obtain ⟨k, hk, hko⟩ := ih hKO
    obtain ⟨i, hi, -, -, hik⟩ := hIK.2.2 k hk
    exact ⟨i, hi, fun v hv ↦ (hik v fun h ↦ hv (by simp [h])).trans
      (hko v fun h ↦ hv (List.mem_cons_of_mem _ h))⟩

/-- Every output row values an introduced dref. -/
theorem dom_of_mem_introList {us : List ℕ} (hu : u ∈ us) (hnd : us.Nodup)
    (h : I ~[introList us] O) {o : ℕ → Part E} (ho : o ∈ O) : (o u).Dom := by
  induction us generalizing I with
  | nil => simp at hu
  | cons u' us ih =>
    obtain ⟨K, hIK, hKO⟩ := h
    rcases List.mem_cons.1 hu with rfl | hu'
    · obtain ⟨k, hk, hko⟩ := exists_eq_of_mem_introList hKO ho
      obtain ⟨i, hi, -, hd, -⟩ := hIK.2.2 k hk
      exact hko u (List.nodup_cons.1 hnd).1 ▸ hd
    · exact ih hu' (List.nodup_cons.1 hnd).2 hKO

/-- A DRS with universe `us` and conditions `C` ([haug-dalrymple-2020] (25)): under distribution
over `Δ`, it introduces `us` and imposes each condition on the output state. -/
def box (us : List ℕ) (C : List (PPDRSCond E)) : Set ℕ → Update (PluralAssign ℕ E) :=
  fun Δ ↦ {(I, O) | I ~[introList us] O ∧ ∀ c ∈ C, c O Δ}

theorem mem_box {us : List ℕ} {C : List (PPDRSCond E)} :
    I ~[box us C Δ] O ↔ I ~[introList us] O ∧ ∀ c ∈ C, c O Δ :=
  Iff.rfl

end Box

end PPCDRT
