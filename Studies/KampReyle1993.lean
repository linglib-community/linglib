module

public import Linglib.Semantics.Dynamic.DRT.Relational
public import Linglib.Semantics.Dynamic.DRT.Accessibility
public import Linglib.Core.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Kamp and Reyle (1993): From Discourse to Logic

A discourse is interpreted by constructing a discourse representation structure (DRS), and a DRS
is verified by a partial embedding of its referents into a model. A sub-DRS is verified by
extensions of the embedding that keep the values it has already assigned (Defs. 1.4.4, 2.1.4),
the semantics `DRS.Verifies`, and a DRS is true when some embedding of its universe verifies it
from the empty input (Def. 1.4.5, `DRS.IsTrue`).

* `DRT.DRS.isProper_iff_forall_occurrence` (in `DRT/Accessibility.lean`): a DRS is proper iff
  every referent of an atomic condition is accessible where the condition occurs, the
  motivation for Def. 1.4.3 (p. 111).

## Implementation notes

The truth conditions are claims over arbitrary models, proved by unfolding the verifying
embeddings; the witnesses are built from `⊥` by `Function.update`. Names enter a DRS as the
unary conditions the construction algorithm writes for them.

## References

* [kamp-reyle-1993]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

namespace KampReyle1993

/-- The relation symbols of the worked examples; names (`jones`, `ulysses`, `porsche`)
enter as the unary conditions the construction algorithm writes for them (`Jones(x)`). -/
inductive KRRel : ℕ → Type
  | jones : KRRel 1 | ulysses : KRRel 1 | porsche : KRRel 1
  | farmer : KRRel 1 | donkey : KRRel 1
  | owns : KRRel 2 | fascinates : KRRel 2 | beats : KRRel 2

/-- The first-order language of the examples (no functions). -/
def krLang : Language := ⟨fun _ ↦ Empty, KRRel⟩

open DRT

variable {M : Type*} [krLang.Structure M]

/-- `RelMap` with the language pinned (a relation symbol alone does not determine
`L`). Lets truth-conditions read as `rm .farmer ![e]`. -/
abbrev rm {n} (R : krLang.Relations n) (x : Fin n → M) : Prop := Structure.RelMap R x

omit [krLang.Structure M] in
private theorem le_update {g : ℕ → Part M} {x : ℕ} (h : ¬(g x).Dom) (m : M) :
    g ≤ Function.update g x (.some m) :=
  le_update_iff.mpr ⟨fun _ ha => absurd ha.fst h, fun _ _ => le_rfl⟩

private theorem holds_atom1 {R : krLang.Relations 1} {a : ℕ} {g : ℕ → Part M} :
    (Condition.atom ⟨R, ![a]⟩ : Condition krLang ℕ).Holds g ↔
      ∃ m ∈ g a, rm R ![m] := by
  rw [Condition.holds_atom]
  constructor
  · rintro ⟨v, hv, hrel⟩
    have he : v = ![v 0] := funext fun i => by fin_cases i; rfl
    exact ⟨v 0, hv 0, he ▸ hrel⟩
  · rintro ⟨m, hm, hrel⟩
    refine ⟨![m], fun i => ?_, hrel⟩
    fin_cases i
    exact hm

private theorem holds_atom2 {R : krLang.Relations 2} {a b : ℕ} {g : ℕ → Part M} :
    (Condition.atom ⟨R, ![a, b]⟩ : Condition krLang ℕ).Holds g ↔
      ∃ m ∈ g a, ∃ n ∈ g b, rm R ![m, n] := by
  rw [Condition.holds_atom]
  constructor
  · rintro ⟨v, hv, hrel⟩
    have he : v = ![v 0, v 1] := funext fun i => by fin_cases i <;> rfl
    exact ⟨v 0, hv 0, v 1, hv 1, he ▸ hrel⟩
  · rintro ⟨m, hm, n, hn, hrel⟩
    refine ⟨![m, n], fun i => ?_, hrel⟩
    fin_cases i
    · exact hm
    · exact hn

/-! ### Names and pronouns: "Jones owns Ulysses. It fascinates him." (1.1) -/

/-- The completed §1.1 DRS of (1.1),
`[u₁ u₂ u₃ u₄ | Jones u₁, Ulysses u₂, u₁ owns u₂, u₃ = u₂, u₄ = u₁, u₃ fascinates u₄]`. Each name
and pronoun introduces a referent, and the (1.17)-style equations resolve *it* and *him* to the
first sentence's referents. -/
def ulyssesDiscourse : DRS krLang ℕ :=
  .mk {1, 2, 3, 4} [.atom ⟨.jones, ![1]⟩, .atom ⟨.ulysses, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩,
    .eq 3 2, .eq 4 1, .atom ⟨.fascinates, ![3, 4]⟩]

/-- The (1.1) discourse is true iff a single pair verifies both sentences (Def. 1.4.5). -/
theorem ulysses_tc :
    ulyssesDiscourse.IsTrue M ↔
      ∃ x y : M, rm .jones ![x] ∧ rm .ulysses ![y] ∧ rm .owns ![x, y] ∧
        rm .fascinates ![y, x] := by
  constructor
  · rintro ⟨g, -, -, h1, h2, h3, h4, h5, h6, -⟩
    obtain ⟨x, hx, hjones⟩ := holds_atom1.mp h1
    obtain ⟨y, hy, hulysses⟩ := holds_atom1.mp h2
    obtain ⟨x', hx', y', hy', howns⟩ := holds_atom2.mp h3
    obtain ⟨m, hm3, hm2⟩ := h4
    obtain ⟨n, hn4, hn1⟩ := h5
    obtain ⟨p, hp, q, hq, hfasc⟩ := holds_atom2.mp h6
    rw [Part.mem_unique hx' hx, Part.mem_unique hy' hy] at howns
    rw [Part.mem_unique hp hm3, Part.mem_unique hm2 hy, Part.mem_unique hq hn4,
      Part.mem_unique hn1 hx] at hfasc
    exact ⟨x, y, hjones, hulysses, howns, hfasc⟩
  · rintro ⟨x, y, hj, hu, ho, hf⟩
    refine ⟨Function.update (Function.update (Function.update
      (Function.update (⊥ : ℕ → Part M) 1 (Part.some x)) 2 (Part.some y)) 3 (Part.some y))
      4 (Part.some x), ?_⟩
    rw [ulyssesDiscourse, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    refine ⟨bot_le, ?_, holds_atom1.mpr ⟨x, by simp, hj⟩,
      holds_atom1.mpr ⟨y, by simp, hu⟩,
      holds_atom2.mpr ⟨x, by simp, y, by simp, ho⟩,
      (Condition.holds_eq 3 2).mpr
        ⟨y, by simp, by simp⟩,
      (Condition.holds_eq 4 1).mpr
        ⟨x, by simp, by simp⟩,
      holds_atom2.mpr ⟨y, by simp, x, by simp, hf⟩⟩
    ext n
    simp only [PFun.dom_update_some, PFun.dom_bot, Set.mem_insert_iff,
      Set.mem_union, Set.mem_empty_iff_false, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_singleton_iff]
    tauto

-- (1.1), Def. 1.4.2–1.4.3
theorem ulysses_proper : ulyssesDiscourse.IsProper := by decide

/-! ### Negation blocks anaphora: "Jones does not own a Porsche." (1.56) -/

/-- The box under `¬` in (1.57) is `[u₂ | Porsche u₂, u₁ owns u₂]`. -/
def porscheNeg : DRS krLang ℕ := .mk {2} [.atom ⟨.porsche, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩]

/-- The DRS (1.57) of (1.56), `[u₁ | Jones u₁, ¬[u₂ | Porsche u₂, u₁ owns u₂]]`, introduces
the indefinite's referent *inside* the negation. -/
def porscheDiscourse : DRS krLang ℕ := .mk {1} [.atom ⟨.jones, ![1]⟩, .neg porscheNeg]

/-- (1.57) is true when there is no Porsche that Jones owns, the negated box being verified by
the non-existence of a verifying extension. -/
theorem porsche_tc :
    porscheDiscourse.IsTrue M ↔
      ∃ x : M, rm .jones ![x] ∧ ¬ ∃ y : M, rm .porsche ![y] ∧ rm .owns ![x, y] := by
  constructor
  · rintro ⟨g, -, hdom, h1, hneg, -⟩
    obtain ⟨x, hx, hjones⟩ := holds_atom1.mp h1
    refine ⟨x, hjones, ?_⟩
    rintro ⟨y, hp, ho⟩
    refine hneg ⟨Function.update g 2 (Part.some y), ?_⟩
    rw [porscheNeg, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    have h2bot : ¬(g 2).Dom := by
      show (2 : ℕ) ∉ PFun.Dom g
      rw [hdom]
      simp
    refine ⟨le_update h2bot y, ?_, holds_atom1.mpr ⟨y, by simp, hp⟩,
      holds_atom2.mpr ⟨x, by simp [hx], y, by simp, ho⟩⟩
    rw [PFun.dom_update_some, Set.insert_eq, Finset.coe_singleton]
    exact Set.union_comm _ _
  · rintro ⟨x, hj, hn⟩
    refine ⟨Function.update ⊥ 1 (.some x), ?_⟩
    rw [porscheDiscourse, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    refine ⟨bot_le, by simp, holds_atom1.mpr ⟨x, by simp, hj⟩, ?_⟩
    rintro ⟨g', hle', hdom', hp, ho, -⟩
    obtain ⟨y, hy, hporsche⟩ := holds_atom1.mp hp
    obtain ⟨x', hx', y', hy', howns⟩ := holds_atom2.mp ho
    have h1 : x ∈ g' 1 := by
      have h := PFun.le_iff_eqOn_dom.mp hle' (x := 1) (by simp)
      rw [Function.update_self] at h
      exact h ▸ Part.mem_some x
    rw [Part.mem_unique hx' h1, Part.mem_unique hy' hy] at howns
    exact hn ⟨y, hporsche, howns⟩

/-- From the top-level position, the referent trapped under `¬` is not accessible
(Def. 2.1.3) — the reason a continuation "*It fascinates him." cannot resolve *it*. -/
theorem porsche_referent_inaccessible : ¬ DRS.Accessible porscheDiscourse 1 2 := by
  decide

-- Def. 2.1.3
theorem outer_referent_accessible : DRS.Accessible porscheDiscourse 2 1 := by
  decide

-- Def. 1.4.2–1.4.3
theorem continuation_improper :
    ¬ (porscheDiscourse.merge (.mk ∅ [.atom ⟨.fascinates, ![2, 1]⟩])).IsProper := by
  decide

/-! ### Donkey anaphora: "If a farmer owns a donkey he beats it." (2.47) -/

/-- The antecedent box `[u₁ u₂ | farmer u₁, donkey u₂, owns u₁ u₂]`. -/
def donkeyAnte : DRS krLang ℕ :=
  .mk {1, 2} [.atom ⟨.farmer, ![1]⟩, .atom ⟨.donkey, ![2]⟩, .atom ⟨.owns, ![1, 2]⟩]
/-- The consequent box `[ | beats u₁ u₂]` (pronouns resolved directly, (2.44)-style). -/
def donkeyCons : DRS krLang ℕ := .mk ∅ [.atom ⟨.beats, ![1, 2]⟩]
/-- (2.47) as `[ | donkeyAnte ⇒ donkeyCons]`. -/
def donkey : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyCons]

/-- By the verification clause for `⇒` ((2.31), Def. 2.1.4), the donkey sentence is true iff every
owning farmer–donkey pair satisfies `beats`. -/
theorem donkey_universal_reading :
    donkey.IsTrue M ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  constructor
  · rintro ⟨g, -, hdom, himp, -⟩ e₁ e₂ ⟨hf, hd, ho⟩
    have hg : g = ⊥ := (PFun.eq_of_le_of_dom_subset bot_le (by rw [hdom]; simp)).symm
    subst hg
    have hante : donkeyAnte.Verifies (⊥ : ℕ → Part M)
        (Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
          2 (Part.some e₂)) := by
      rw [donkeyAnte, DRS.verifies_mk]
      simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
      refine ⟨bot_le, ?_, holds_atom1.mpr ⟨e₁, by simp, hf⟩,
        holds_atom1.mpr ⟨e₂, by simp, hd⟩,
        holds_atom2.mpr ⟨e₁, by simp, e₂, by simp, ho⟩⟩
      ext n
      simp only [PFun.dom_update_some, PFun.dom_bot, Set.mem_insert_iff,
        Set.mem_union, Set.mem_empty_iff_false, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_singleton_iff]
      tauto
    obtain ⟨g₂, hle₂, hdom₂, hb, -⟩ := himp _ hante
    have hg₂ : g₂ = Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
        2 (Part.some e₂) :=
      (PFun.eq_of_le_of_dom_subset hle₂ (by rw [hdom₂]; simp)).symm
    obtain ⟨m, hm, n, hn, hbeats⟩ := holds_atom2.mp hb
    rw [hg₂] at hm hn
    have he₁ : e₁ ∈ Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
        2 (Part.some e₂) 1 := by simp
    have he₂ : e₂ ∈ Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
        2 (Part.some e₂) 2 := by simp
    rw [Part.mem_unique hm he₁, Part.mem_unique hn he₂] at hbeats
    exact hbeats
  · intro hall
    refine ⟨⊥, ?_⟩
    rw [donkey, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    refine ⟨le_rfl, by simp, ?_⟩
    rintro g₁ ⟨-, hdom₁, hf, hd, ho, -⟩
    obtain ⟨e₁, h1, hfarmer⟩ := holds_atom1.mp hf
    obtain ⟨e₂, h2, hdonkey⟩ := holds_atom1.mp hd
    obtain ⟨m, hm, n, hn, howns⟩ := holds_atom2.mp ho
    rw [Part.mem_unique hm h1, Part.mem_unique hn h2] at howns
    refine ⟨g₁, ?_⟩
    rw [donkeyCons, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    exact ⟨le_rfl, by simp,
      holds_atom2.mpr ⟨e₁, h1, e₂, h2, hall e₁ e₂ ⟨hfarmer, hdonkey, howns⟩⟩⟩

theorem donkey_proper : donkey.IsProper := by decide

/-- The (2.45)-style consequent `[u₃ | u₃ = u₂, beats u₁ u₃]`, in which the pronoun *it*
introduces its own referent, resolved to the donkey by an equation. -/
def donkeyPronounCons : DRS krLang ℕ := .mk {3} [.eq 3 2, .atom ⟨.beats, ![1, 3]⟩]
/-- (2.47) with the pronoun completed by referent-plus-equation. -/
def donkeyPronoun : DRS krLang ℕ := .mk ∅ [.imp donkeyAnte donkeyPronounCons]

theorem donkeyPronoun_tc :
    donkeyPronoun.IsTrue M ↔
    ∀ e₁ e₂ : M, (rm .farmer ![e₁] ∧ rm .donkey ![e₂] ∧ rm .owns ![e₁, e₂]) →
      rm .beats ![e₁, e₂] := by
  constructor
  · rintro ⟨g, -, hdom, himp, -⟩ e₁ e₂ ⟨hf, hd, ho⟩
    have hg : g = ⊥ := (PFun.eq_of_le_of_dom_subset bot_le (by rw [hdom]; simp)).symm
    subst hg
    have hante : donkeyAnte.Verifies (⊥ : ℕ → Part M)
        (Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
          2 (Part.some e₂)) := by
      rw [donkeyAnte, DRS.verifies_mk]
      simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
      refine ⟨bot_le, ?_, holds_atom1.mpr ⟨e₁, by simp, hf⟩,
        holds_atom1.mpr ⟨e₂, by simp, hd⟩,
        holds_atom2.mpr ⟨e₁, by simp, e₂, by simp, ho⟩⟩
      ext n
      simp only [PFun.dom_update_some, PFun.dom_bot, Set.mem_insert_iff,
        Set.mem_union, Set.mem_empty_iff_false, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_singleton_iff]
      tauto
    obtain ⟨g₂, hle₂, hdom₂, h32, hb, -⟩ := himp _ hante
    obtain ⟨m', hm3, hm2⟩ := h32
    obtain ⟨m, hm, n, hn, hbeats⟩ := holds_atom2.mp hb
    have h1 : e₁ ∈ g₂ 1 := by
      have h := PFun.le_iff_eqOn_dom.mp hle₂ (x := 1) (by simp)
      have hup : Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
          2 (Part.some e₂) 1 = Part.some e₁ := by simp
      rw [hup] at h
      exact h ▸ Part.mem_some e₁
    have h2 : e₂ ∈ g₂ 2 := by
      have h := PFun.le_iff_eqOn_dom.mp hle₂ (x := 2) (by simp)
      have hup : Function.update (Function.update (⊥ : ℕ → Part M) 1 (Part.some e₁))
          2 (Part.some e₂) 2 = Part.some e₂ := by simp
      rw [hup] at h
      exact h ▸ Part.mem_some e₂
    rw [Part.mem_unique hm h1, Part.mem_unique hn hm3, Part.mem_unique hm2 h2] at hbeats
    exact hbeats
  · intro hall
    refine ⟨⊥, ?_⟩
    rw [donkeyPronoun, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    refine ⟨le_rfl, by simp, ?_⟩
    rintro g₁ ⟨-, hdom₁, hf, hd, ho, -⟩
    obtain ⟨e₁, h1, hfarmer⟩ := holds_atom1.mp hf
    obtain ⟨e₂, h2, hdonkey⟩ := holds_atom1.mp hd
    obtain ⟨m, hm, n, hn, howns⟩ := holds_atom2.mp ho
    rw [Part.mem_unique hm h1, Part.mem_unique hn h2] at howns
    have h3bot : ¬(g₁ 3).Dom := by
      show (3 : ℕ) ∉ PFun.Dom g₁
      rw [hdom₁]
      simp
    refine ⟨Function.update g₁ 3 (Part.some e₂), ?_⟩
    rw [donkeyPronounCons, DRS.verifies_mk]
    simp only [Condition.holdsAll_cons, Condition.holdsAll_nil, and_true]
    refine ⟨le_update h3bot e₂, ?_,
      (Condition.holds_eq 3 2).mpr ⟨e₂, by simp, by simp [h2]⟩,
      holds_atom2.mpr ⟨e₁, by simp [h1], e₂, by simp,
        hall e₁ e₂ ⟨hfarmer, hdonkey, howns⟩⟩⟩
    rw [PFun.dom_update_some, Set.insert_eq, Finset.coe_singleton]
    exact Set.union_comm _ _

/-- Completing the pronoun directly or by a referent and an equation gives the same truth
conditions, (2.44) and (2.45). -/
theorem donkeyPronoun_agree : donkeyPronoun.IsTrue M ↔ donkey.IsTrue M :=
  donkeyPronoun_tc.trans donkey_universal_reading.symm

/-! ### Subordination and accessibility geometry -/

-- Def. 2.1.2
theorem donkey_antecedent_subordinate : DirectlySubordinate donkeyAnte donkey :=
  ⟨.imp donkeyAnte donkeyCons, by simp [donkey], [], by simp⟩

theorem donkey_consequent_subordinate : DirectlySubordinate donkeyCons donkey :=
  ⟨.imp donkeyAnte donkeyCons, by simp [donkey], [donkeyAnte], by simp⟩

-- Def. 2.1.3
theorem donkey_antecedent_accessible : AccessibleTo donkey donkeyAnte donkeyCons :=
  .antecedent .refl (by simp [donkey]) .refl

theorem donkey_not_consequent_accessible : ¬ AccessibleTo donkey donkeyCons donkeyAnte := by
  rw [accessibleTo_iff_exists_occurrence]
  rintro ⟨bs, h, hmem⟩
  have key : donkey.occurrences [] =
      [ [donkey], [donkeyAnte, donkey], [donkeyCons, donkeyAnte, donkey] ] := rfl
  rw [Occurrence, ← DRS.mem_occurrences_iff, key] at h
  simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at h hmem
  rcases h with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
  · exact absurd (congrArg DRS.referents h) (by decide)
  · rcases hmem with h | h
    · exact absurd (congrArg DRS.referents h) (by decide)
    · simpa [donkeyCons, donkey] using congrArg DRS.conditions (List.mem_singleton.1 h)
  · exact absurd (congrArg DRS.referents h) (by decide)

/-! ### Model evaluation: the donkey conditional in concrete models

Positive: a two-element domain where farmer `0` owns and beats donkey `1`. Negative: a
domain where the owning pair goes unbeaten falsifies the conditional. -/

instance : krLang.Structure (Fin 2) where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args ↦ args 0 = 0
    | 1, .donkey => fun args ↦ args 0 = 1
    | 2, .owns => fun args ↦ args 0 = 0 ∧ args 1 = 1
    | 2, .beats => fun args ↦ args 0 = 0 ∧ args 1 = 1
    | _, _ => fun _ ↦ False

-- (0, 1)
theorem donkey_true_in_model : donkey.IsTrue (Fin 2) := by
  rw [donkey_universal_reading]
  rintro e₁ e₂ ⟨hf, hd, -⟩
  exact ⟨hf, hd⟩

instance : krLang.Structure Bool where
  funMap {_} f _ := f.elim
  RelMap {n} R := match n, R with
    | 1, .farmer => fun args ↦ args 0 = false
    | 1, .donkey => fun args ↦ args 0 = true
    | 2, .owns => fun args ↦ args 0 = false ∧ args 1 = true
    | _, _ => fun _ ↦ False

theorem donkey_false_in_model : ¬ donkey.IsTrue Bool := by
  rw [donkey_universal_reading]
  exact fun h ↦ h false true ⟨rfl, rfl, rfl, rfl⟩

end KampReyle1993
