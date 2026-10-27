module

public import Linglib.Data.Examples.Brasoveanu2010
public import Linglib.Semantics.Dynamic.PCDRT
public import Linglib.Semantics.Quantification.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.FinCases

/-!
# Brasoveanu (2010): Decomposing Modal Quantification

[brasoveanu-2010] interprets discourse relative to plural information states, sets of variable
assignments that store both the values of discourse referents and the dependencies between them.
A generalized determiner is decomposed into maximization, which stores its restrictor and nuclear
scope sets in drefs, distributivity, which updates each value of a dref separately, and a static
determiner relating the two sets, while a singular pronoun requires the dref it retrieves to have
one value. The modal half of the paper analyses modal verbs as the modal counterparts of
determiners.

This file formalizes the system for individuals of §2: the wolf discourse (27), the matrix (64)
of structured inclusion, and the quantificational subordination discourses (5) and (6) of §2.6,
derived compositionally from the lexical entries (80)–(83) and (90)–(93). Under the narrow-scope
indefinite (86) the singular *she* of (5) forces the truth conditions of the wide-scope one (85),
and of the four scopings of (6) only (86) with (96), the combination (97), lets the woman vary
with the convention.

## Implementation notes

* A row is an assignment `Dref → Flat E`, and ★ is `⊥`; lexical relations are predicates of `E`,
  so they are false of ★ (fn. 5).
* The lexical entries keep the distributivity operators that (85), (86), (95) and (96) omit as
  redundant, and `every` is (83), with the operators (74) that the paper substitutes for those of
  (75) on a non-empty restrictor (`determiner_every_iff`). The truth conditions hold without the
  constraint of fn. 12 that a new dref takes ★ only when necessary.
* *The banquet* of (6b) is folded into the relation `Model.come`, as on p. 473.

## TODO

* Negation (52), the definite articles (53), (54), (78), (79), and the donkey sentences and
  anaphora to quantifier domains of §2.3.
* Intensional PCDRT (§3) and the entailment particles of §4.

## References

* [brasoveanu-2010]
* [karttunen-1976]
* [muskens-1996]
* [van-den-berg-1996]
-/

@[expose] public section

namespace Brasoveanu2010

open DynamicSemantics DynamicSemantics.Update PCDRT SetRel Quantifier RegisterStructure

/-- The drefs of the examples. -/
inductive Dref where
  | u
  | u'
  | u₁
  | u₂
  | u₃
  | u₄
  | u₅
  deriving DecidableEq

variable {E : Type*}

/-- A row of a plural info state: an individual or ★ for each dref. -/
abbrev Row (E : Type*) := Dref → Flat E

/-- A property, type `et`: a dref to an update. -/
abbrev Pred (E : Type*) := Dref → Update (Set (Row E))

/-- A quantifier, type `(et)t`: a property to an update. -/
abbrev Quant (E : Type*) := Pred E → Update (Set (Row E))

/-- The row with the given values of `u₁, …, u₅` and ★ for `u` and `u'`. -/
def row (a b c d e : Flat E) : Row E
  | .u₁ => a
  | .u₂ => b
  | .u₃ => c
  | .u₄ => d
  | .u₅ => e
  | _ => ⊥

section Row

variable {a b c d e x : Flat E}

@[simp] theorem row_u₁ : row a b c d e Dref.u₁ = a := rfl
@[simp] theorem row_u₂ : row a b c d e Dref.u₂ = b := rfl
@[simp] theorem row_u₃ : row a b c d e Dref.u₃ = c := rfl
@[simp] theorem row_u₄ : row a b c d e Dref.u₄ = d := rfl
@[simp] theorem row_u₅ : row a b c d e Dref.u₅ = e := rfl

@[simp] theorem update_row_u₁ : Function.update (row a b c d e) Dref.u₁ x = row x b c d e := by
  funext v; cases v <;> rfl
@[simp] theorem update_row_u₂ : Function.update (row a b c d e) Dref.u₂ x = row a x c d e := by
  funext v; cases v <;> rfl
@[simp] theorem update_row_u₃ : Function.update (row a b c d e) Dref.u₃ x = row a b x d e := by
  funext v; cases v <;> rfl
@[simp] theorem update_row_u₄ : Function.update (row a b c d e) Dref.u₄ x = row a b c x e := by
  funext v; cases v <;> rfl
@[simp] theorem update_row_u₅ : Function.update (row a b c d e) Dref.u₅ x = row a b c d x := by
  funext v; cases v <;> rfl

end Row

/-- The dummy assignment `i★`, which assigns ★ to every dref; `{i★}` is the dummy info state
(28), which holds no anaphoric information. -/
def iStar : Row E := ⊥

theorem iStar_eq_row : (iStar : Row E) = row ⊥ ⊥ ⊥ ⊥ ⊥ := by
  funext v; cases v <;> rfl

/-! ### Indefinites, pronouns and proper names (§2.2) -/

/-- (26), (30): a noun or intransitive verb is a test that its argument satisfies it. -/
def noun (P : E → Prop) : Pred E := fun v ↦ test (atom (fun x ↦ P (x 0)) ![v])

/-- (36): the singular indefinite introduces `d`, makes it singular, and predicates its
restrictor and its scope of it. -/
def indef (d : Dref) (P : Pred E) : Quant E := fun P' ↦ intro d ○ test (sing d) ○ P d ○ P' d

/-- (37): the singular pronoun requires its dref to be singular and passes it to the predicate. -/
def pron (d : Dref) : Quant E := fun P ↦ test (sing d) ○ P d

/-- (42), (43): a proper name introduces a dref whose only value is its bearer. -/
def name (x : E) (d : Dref) : Quant E := fun P ↦ intro d ○ test {I | value d I = {x}} ○ P d

/-- (45a): a transitive verb applies its object's quantifier to the relation. -/
def transVerb (R : E → E → Prop) (Q : Quant E) : Pred E :=
  fun v ↦ Q fun v' ↦ test (atom (fun x ↦ R (x 0) (x 1)) ![v, v'])

/-- The wolf discourse (27), (46): *A^u wolf came in. It_u ate Harvey^{u'}.* -/
def wolfDiscourse (wolf comeIn : E → Prop) (eat : E → E → Prop) (harvey : E) :
    Update (Set (Row E)) :=
  indef .u (noun wolf) (noun comeIn) ○ pron .u (transVerb eat (name harvey .u'))

-- (27), (35)
theorem wolfDiscourse_true_iff (wolf comeIn : E → Prop) (eat : E → E → Prop) (harvey : E) :
    {iStar} ∈ (wolfDiscourse wolf comeIn eat harvey).dom ↔
      ∃ x, wolf x ∧ comeIn x ∧ eat x harvey := by
  constructor
  · rintro ⟨J, K, hA, hB⟩
    simp only [indef, noun, mem_comp_test] at hA
    obtain ⟨⟨⟨hint, x, hx⟩, hwolf⟩, hcome⟩ := hA
    simp only [pron, transVerb, name, mem_test_comp, mem_comp_test] at hB
    obtain ⟨-, ⟨hint', hharvey⟩, heat⟩ := hB
    rw [mem_atom_vec1, hx] at hwolf hcome
    have hu : value Dref.u J = {x} := (value_intro_of_ne (by decide) hint').trans hx
    have hh : value Dref.u' J = {harvey} := hharvey
    obtain ⟨⟨p, hp⟩, heat⟩ := mem_atom_vec2.1 heat
    have h1 : p.1 = x := by simpa [hu] using fst_mem_value_of_mem_dep hp
    have h2 : p.2 = harvey := by simpa [hh] using snd_mem_value_of_mem_dep hp
    exact ⟨x, by simpa using hwolf.2 x rfl, by simpa using hcome.2 x rfl,
      by simpa [h1, h2] using heat p hp⟩
  · rintro ⟨x, hw, hc, he⟩
    set i₁ : Row E := Function.update iStar .u ↑x
    set i₂ : Row E := Function.update i₁ .u' ↑harvey
    have hv₁ : value Dref.u {i₁} = {x} := value_singleton_of_eq (by simp [i₁])
    have hv₂ : value Dref.u' {i₂} = {harvey} := value_singleton_of_eq (by simp [i₂])
    have hd : dep Dref.u Dref.u' {i₂} = {(x, harvey)} :=
      dep_singleton_of_eq (by simp [i₂, i₁]) (by simp [i₂])
    refine ⟨{i₂}, {i₁}, ?_, ?_⟩
    · simp only [indef, noun, mem_comp_test, mem_atom_vec1, hv₁]
      exact ⟨⟨⟨singleton_mem_intro _ _ _, x, hv₁⟩, by simp [hw]⟩, by simp [hc]⟩
    · simp only [pron, transVerb, name, mem_test_comp, mem_comp_test, mem_atom_vec2, hd]
      exact ⟨⟨x, hv₁⟩, ⟨singleton_mem_intro _ _ _, hv₂⟩, by simp [he]⟩

-- §2.2
theorem pron_not_true_at_iStar (d : Dref) (P : Pred E) : {iStar} ∉ (pron d P).dom := by
  rintro ⟨J, K, ⟨rfl, x, hx⟩, -⟩
  have : value d ({iStar} : Set (Row E)) = ∅ := by
    ext y
    simp [value, iStar]
  simp [this] at hx

/-! ### Structured inclusion (63)–(66)

The matrix (64): the conventions `α₁ … α₄` in `u₁`, the women `β₁ … β₄` courted at them in `u₂`,
and two ways of storing a subset of the conventions in `u₃`. -/

/-- The individuals of (64). -/
inductive Ind where
  | α₁ | α₂ | α₃ | α₄
  | β₁ | β₂ | β₃ | β₄
  deriving DecidableEq

open Ind

/-- (64) with the value-inclusion column: `u₃` holds `α₁, α₃, α₁, α₂`. -/
def valueCol : Set (Row Ind) :=
  {row α₁ β₁ α₁ ⊥ ⊥, row α₂ β₂ α₃ ⊥ ⊥, row α₃ β₃ α₁ ⊥ ⊥, row α₄ β₄ α₂ ⊥ ⊥}

/-- (64) with the structured column: `u₃` holds `α₁, α₂, ★, α₄`. -/
def structCol : Set (Row Ind) :=
  {row α₁ β₁ α₁ ⊥ ⊥, row α₂ β₂ α₂ ⊥ ⊥, row α₃ β₃ ⊥ ⊥ ⊥, row α₄ β₄ α₄ ⊥ ⊥}

-- (65)
theorem value_subset_valueCol : value Dref.u₃ valueCol ⊆ value Dref.u₁ valueCol := by
  intro x
  simp only [valueCol, mem_value, embed_flat, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, val_apply, row_u₁, row_u₃, Flat.coe_inj]
  rintro (rfl | rfl | rfl | rfl) <;> simp

theorem value_subset_structCol : value Dref.u₃ structCol ⊆ value Dref.u₁ structCol := by
  intro x
  simp only [structCol, mem_value, embed_flat, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, val_apply, row_u₁, row_u₃, Flat.coe_inj, Flat.bot_ne_coe,
    false_or]
  rintro (rfl | rfl | rfl) <;> simp

-- (63a)
theorem valueCol_scrambles_dep :
    ¬dep Dref.u₃ Dref.u₂ valueCol ⊆ dep Dref.u₁ Dref.u₂ valueCol := fun h ↦ by
  simpa [dep, valueCol] using h (show (α₁, β₃) ∈ dep Dref.u₃ Dref.u₂ valueCol by
    simp [dep, valueCol])

-- (66)
theorem valueCol_not_structSub : valueCol ∉ structSub Dref.u₃ Dref.u₁ := fun h ↦ by
  simpa using h (row α₂ β₂ α₃ ⊥ ⊥) (by simp [valueCol])

-- (68)
theorem structCol_structSubAll : structCol ∈ structSubAll Dref.u₃ Dref.u₁ := by
  refine ⟨fun i hi ↦ ?_, fun i hi x hx hix ↦ ?_⟩ <;>
    simp only [structCol, Set.mem_insert_iff, Set.mem_singleton_iff] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> simp_all [structCol]
  subst hix
  simp at hx

theorem structCol_keeps_dep : dep Dref.u₃ Dref.u₂ structCol ⊆ dep Dref.u₁ Dref.u₂ structCol :=
  dep_subset_of_structSub structCol_structSubAll.1

/-! ### Quantificational subordination (§2.5, §2.6) -/

/-- (83): `every^{u, u'⊑u}`, with the distributivity operators (74) that the paper substitutes
for those of (75) on a non-empty restrictor. -/
def every (d d' : Dref) (P : Pred E) : Quant E := fun P' ↦
  max d (distrib d (P d)) ○ maxSub d' d (distrib d' (P' d')) ○ test (det GQ.every d d')

/-- On a non-empty restrictor, (83) is the generalized determiner (77) at `EVERY` (p. 470). -/
theorem determiner_every_iff {d d' : Dref} (hd : d ≠ d') {P P' : Pred E} {I J : Set (Row E)}
    (hI : ∃ K, I ~[intro d ○ distrib d (P d)] K) :
    I ~[determiner GQ.every d d' P P'] J ↔ I ~[every d d' P P'] J :=
  mem_determiner_iff (fun _ ⟨x, hx⟩ h ↦ h x hx) hd hI

/-- (80): `court-at¹` gives its first object scope over its second. -/
def courtAt₁ (R : E → E → E → Prop) (Q' Q'' : Quant E) : Pred E :=
  fun v ↦ Q' fun v' ↦ Q'' fun v'' ↦ test (atom (fun x ↦ R (x 0) (x 1) (x 2)) ![v, v', v''])

/-- (81): `court-at²` gives its second object scope over its first. -/
def courtAt₂ (R : E → E → E → Prop) (Q' Q'' : Quant E) : Pred E :=
  fun v ↦ Q'' fun v'' ↦ Q' fun v' ↦ test (atom (fun x ↦ R (x 0) (x 1) (x 2)) ![v, v', v''])

/-- (90): `always^{u⊑u'}` quantifies universally over a structured subset of the dref it
retrieves. -/
def always (d d' : Dref) : Quant E := fun P ↦
  maxSub d d' (distrib d (P d)) ○ test (det GQ.every d' d)

/-- (92): `come-to-banquet-of¹` gives its subject scope over the adverb. -/
def come₁ (R : E → E → Prop) (Q Q' : Quant E) : Update (Set (Row E)) :=
  Q' fun v' ↦ Q fun v ↦ test (atom (fun x ↦ R (x 0) (x 1)) ![v', v])

/-- (93): `come-to-banquet-of²` gives the adverb scope over its subject. -/
def come₂ (R : E → E → Prop) (Q Q' : Quant E) : Update (Set (Row E)) :=
  Q fun v ↦ Q' fun v' ↦ test (atom (fun x ↦ R (x 0) (x 1)) ![v', v])

/-- A model of discourses (5) and (6): Harvey, the women and the conventions, who courts whom at
which convention, who is very pretty, and which woman comes to the banquet with Harvey at which
convention. -/
structure Model (E : Type*) where
  /-- Harvey. -/
  harvey : E
  /-- The women. -/
  woman : E → Prop
  /-- The conventions. -/
  convention : E → Prop
  /-- `courtAt x y z`: `x` courts `y` at `z`. -/
  courtAt : E → E → E → Prop
  /-- The very pretty individuals. -/
  veryPretty : E → Prop
  /-- `come y z`: `y` comes to the banquet with Harvey at `z`. -/
  come : E → E → Prop

variable (M : Model E) {J : Set (Row E)}

/-- (82): *Harvey^{u₁} courts a^{u₄} woman at every^{u₂, u₃⊑u₂} convention*, (85) under
`courtAt₁` and (86) under `courtAt₂`. -/
def courtSentence (court : (E → E → E → Prop) → Quant E → Quant E → Pred E) :
    Update (Set (Row E)) :=
  name M.harvey .u₁ (court M.courtAt (indef .u₄ (noun M.woman)) (every .u₂ .u₃ (noun M.convention)))

/-- (89): *She_{u₄} is very pretty.* -/
def prettySentence : Update (Set (Row E)) := pron .u₄ (noun M.veryPretty)

/-- (94): *She_{u₄} always^{u₅⊑u₃} comes to the banquet with him*, (95) under `come₁` and (96)
under `come₂`. -/
def comeSentence (come : (E → E → Prop) → Quant E → Quant E → Update (Set (Row E))) :
    Update (Set (Row E)) :=
  come M.come (always .u₅ .u₃) (pron .u₄)

/-! #### The first sentence -/

private theorem exists_courtAt_of_mem_atom {h c : E} (hJ₁ : value Dref.u₁ J = {h})
    (hc : cell Dref.u₃ c J ∈
      atom (fun x ↦ M.courtAt (x 0) (x 1) (x 2)) ![Dref.u₁, Dref.u₄, Dref.u₃]) :
    ∃ w ∈ value Dref.u₄ (cell Dref.u₃ c J), M.courtAt h w c := by
  obtain ⟨⟨y, k, ⟨hk, hk₃⟩, hy⟩, hall⟩ := hc
  have h0 : y 0 = h := by
    have : y 0 ∈ value Dref.u₁ J := ⟨k, hk, hy 0⟩
    rwa [hJ₁] at this
  have h2 : y 2 = c := Flat.coe_inj.1 ((hy 2).symm.trans hk₃)
  refine ⟨y 1, ⟨k, ⟨hk, hk₃⟩, hy 1⟩, ?_⟩
  simpa [h0, h2] using hall y ⟨k, ⟨hk, hk₃⟩, hy⟩

private theorem convention_mem_value {J₂ J₃ : Set (Row E)} (hJ₂ : J₂.Nonempty)
    (h : J₂ ~[max Dref.u₂ (test (atom (fun x ↦ M.convention (x 0)) ![Dref.u₂]))] J₃) :
    value Dref.u₂ J₃ = {c | M.convention c} := by
  have hP : ∃ c, M.convention (![c] 0) := by
    obtain ⟨K, -, -, hK⟩ := max_subset _ _ h
    obtain ⟨⟨c, hc⟩, hall⟩ := mem_atom_vec1.1 hK
    exact ⟨c, hall c hc⟩
  obtain ⟨-, hW⟩ := (mem_max_test_atom_self_iff hJ₂ hP).1 h
  obtain ⟨i, hi⟩ := hJ₂
  rw [← value_nonDummy, hW]
  ext c
  simp only [mem_value, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨j, -, x, hx, rfl⟩, hc⟩
    rw [val_extend_self, embed_flat, Flat.coe_inj] at hc
    simpa [hc] using hx
  · exact fun hc ↦ ⟨_, ⟨i, hi, c, by simpa using hc, rfl⟩, val_extend_self ..⟩

-- (85)
theorem courtAt₁_output (hJ : {iStar} ~[courtSentence M courtAt₁] J) :
    ∃ w, M.woman w ∧ (∀ c, M.convention c → M.courtAt M.harvey w c) ∧
      value Dref.u₃ J = {c | M.convention c} ∧ value Dref.u₄ J = {w} ∧
      ∀ c, M.convention c → value Dref.u₄ (cell Dref.u₃ c J) = {w} := by
  simp only [courtSentence, name, courtAt₁, indef, every, noun, distrib_test_atom_self] at hJ
  simp only [distrib_test] at hJ
  obtain ⟨J₁, hJ₁, J₂, hJ₂, hJ₃⟩ := hJ
  obtain ⟨-, hN⟩ := mem_comp_test.1 hJ₁
  simp only [mem_comp_test] at hJ₂
  obtain ⟨⟨hi₄, w, hw⟩, hwoman⟩ := hJ₂
  obtain ⟨⟨J₃, hmax, hsub⟩, hev⟩ := mem_comp_test.1 hJ₃
  obtain ⟨K, -, hK⟩ := max_subset _ _ hsub
  obtain ⟨hss, rfl, hCt⟩ := mem_test_comp.1 hK
  simp only [mem_det, GQ.every] at hev
  have hwJ : w ∈ value Dref.u₄ J₂ := hw ▸ Set.mem_singleton w
  have hwoman' : M.woman w := by
    simpa using (mem_atom_vec1.1 hwoman).2 w hwJ
  have hv₂ : value Dref.u₂ K = {c | M.convention c} := by
    rw [((preserves_test ![Dref.u₂] _).maxSub (by decide)).value_eq hsub]
    obtain ⟨k, hk, -⟩ := hwJ
    exact convention_mem_value M ⟨k, hk⟩ hmax
  have hv₄ : value Dref.u₄ K = {w} := by
    rw [(((preserves_test ![Dref.u₄] _).max (by decide)).comp
      ((preserves_test ![Dref.u₄] _).maxSub (by decide))).value_eq ⟨J₃, hmax, hsub⟩, hw]
  have hv₁ : value Dref.u₁ K = {M.harvey} := by
    rw [(((preserves_test ![Dref.u₁] _).max (by decide)).comp
      ((preserves_test ![Dref.u₁] _).maxSub (by decide))).value_eq ⟨J₃, hmax, hsub⟩,
      value_intro_of_ne (by decide) hi₄]
    exact hN
  have hconv (c : E) (hc : M.convention c) : c ∈ value Dref.u₃ K ∧ M.courtAt M.harvey w c ∧
      value Dref.u₄ (cell Dref.u₃ c K) = {w} := by
    have hc₃ : c ∈ value Dref.u₃ K := hev c (by rw [hv₂]; exact hc)
    obtain ⟨w', hw', hcourt⟩ := exists_courtAt_of_mem_atom M hv₁ (hCt.2 c hc₃)
    have hsub' : value Dref.u₄ (cell Dref.u₃ c K) ⊆ {w} :=
      hv₄ ▸ value_mono fun _ hk ↦ hk.1
    obtain rfl : w' = w := hsub' hw'
    exact ⟨hc₃, hcourt, Set.eq_singleton_iff_unique_mem.2 ⟨hw', fun _ hx ↦ hsub' hx⟩⟩
  refine ⟨w, hwoman', fun c hc ↦ (hconv c hc).2.1, Set.ext fun c ↦ ⟨fun ⟨k, hk, hk₃⟩ ↦ ?_,
    fun hc ↦ (hconv c hc).1⟩, hv₄, fun c hc ↦ (hconv c hc).2.2⟩
  have : c ∈ value Dref.u₂ K := by
    rcases hss.1 k hk with h | h
    · exact ⟨k, hk, h.symm.trans hk₃⟩
    · simp [h] at hk₃
  rwa [hv₂] at this

-- (86)
theorem courtAt₂_output (hJ : {iStar} ~[courtSentence M courtAt₂] J) :
    value Dref.u₃ J = {c | M.convention c} ∧ ∀ c, M.convention c →
      ∃ w, M.woman w ∧ M.courtAt M.harvey w c ∧ value Dref.u₄ (cell Dref.u₃ c J) = {w} := by
  simp only [courtSentence, name, courtAt₂, indef, every, noun, distrib_test_atom_self] at hJ
  obtain ⟨J₁, hJ₁, hJ₃⟩ := hJ
  obtain ⟨-, hN⟩ := mem_comp_test.1 hJ₁
  obtain ⟨⟨J₃, hmax, hsub⟩, hev⟩ := mem_comp_test.1 hJ₃
  obtain ⟨K₀, hi₃, hK⟩ := max_subset _ _ hsub
  obtain ⟨hss, hdist⟩ := mem_test_comp.1 hK
  simp only [mem_det, GQ.every] at hev
  have hhJ₁ : M.harvey ∈ value Dref.u₁ J₁ := hN ▸ Set.mem_singleton _
  have hv₂ : value Dref.u₂ K₀ = {c | M.convention c} := by
    rw [value_intro_of_ne (by decide) hi₃]
    obtain ⟨k, hk, -⟩ := hhJ₁
    exact convention_mem_value M ⟨k, hk⟩ hmax
  have hv₁ : value Dref.u₁ J = {M.harvey} := by
    rw [(((preserves_test ![Dref.u₁] _).max (by decide)).comp
      ((((((preserves_intro (by decide)).comp (preserves_test _ _)).comp
        (preserves_test _ _)).comp (preserves_test _ _)).distrib).maxSub
          (by decide))).value_eq ⟨J₃, hmax, hsub⟩]
    exact hN
  obtain ⟨-, -, hv₃, hcells⟩ := mem_distrib.1 hdist
  have hv₂₃ : value Dref.u₃ K₀ ⊆ value Dref.u₂ K₀ := fun c ⟨k, hk, hk₃⟩ ↦ by
    rcases hss.1 k hk with h | h
    · exact ⟨k, hk, h.symm.trans hk₃⟩
    · simp [h] at hk₃
  have hv₂J : value Dref.u₂ J = value Dref.u₂ K₀ :=
    (((((preserves_intro (by decide)).comp (preserves_test _ _)).comp
      (preserves_test _ _)).comp (preserves_test _ _)).distrib).value_eq hdist
  have hc₃ (c : E) (hc : M.convention c) : c ∈ value Dref.u₃ K₀ :=
    hv₃ ▸ hev c (by rw [hv₂J, hv₂]; exact hc)
  refine ⟨Set.ext fun c ↦ ⟨fun hc ↦ ?_, fun hc ↦ hv₃ ▸ hc₃ c hc⟩, fun c hc ↦ ?_⟩
  · have := hv₂₃ (hv₃ ▸ hc)
    rwa [hv₂] at this
  · have hD := hcells c (hc₃ c hc)
    simp only [mem_comp_test] at hD
    obtain ⟨⟨⟨-, w, hw⟩, hwoman⟩, hcourt⟩ := hD
    obtain ⟨w', hw', hcw⟩ := exists_courtAt_of_mem_atom M hv₁ hcourt
    rw [hw] at hw'
    obtain rfl : w' = w := hw'
    exact ⟨w', by simpa using (mem_atom_vec1.1 hwoman).2 w' (by simp [hw]), hcw, hw⟩

-- (87), (85)
theorem exists_courtAt₁_output (hc : ∃ c, M.convention c) {w : E} (hw : M.woman w)
    (h : ∀ c, M.convention c → M.courtAt M.harvey w c) :
    ∃ J, {iStar} ~[courtSentence M courtAt₁] J ∧ value Dref.u₄ J = {w} := by
  obtain ⟨c₀, hc₀⟩ := hc
  set r₁ : Row E := row ↑M.harvey ⊥ ⊥ ⊥ ⊥
  set r₂ : Row E := row ↑M.harvey ⊥ ⊥ ↑w ⊥
  set J₃ : Set (Row E) := (fun c : E ↦ row ↑M.harvey ↑c ⊥ ↑w ⊥) '' {c | M.convention c}
  have hcopy : copy Dref.u₃ Dref.u₂ J₃ =
      (fun c : E ↦ row ↑M.harvey ↑c ↑c ↑w ⊥) '' {c | M.convention c} := by
    ext j
    simp [copy, J₃]
  have hc : ∃ c, M.convention c := ⟨c₀, hc₀⟩
  have hv₄ : value Dref.u₄ J₃ = {w} := by
    ext x
    simp [J₃, hc, eq_comm]
  have hv₄₂ : value Dref.u₄ {r₂} = {w} := value_singleton_of_eq (by simp [r₂])
  refine ⟨copy Dref.u₃ Dref.u₂ J₃, ?_, by rw [value_copy_of_ne (by decide), hv₄]⟩
  simp only [courtSentence, name, courtAt₁, indef, every, noun, distrib_test_atom_self]
  simp only [distrib_test]
  refine ⟨{r₁}, mem_comp_test.2 ⟨?_, ?_⟩, {r₂}, ?_, mem_comp_test.2 ⟨⟨J₃, ?_, ?_⟩, ?_⟩⟩
  · simpa [iStar_eq_row, r₁] using singleton_mem_intro (iStar : Row E) Dref.u₁ ↑M.harvey
  · exact value_singleton_of_eq (by simp [r₁])
  · simp only [mem_comp_test]
    exact ⟨⟨by simpa [r₁, r₂] using singleton_mem_intro r₁ Dref.u₄ ↑w, w, hv₄₂⟩,
      mem_atom_vec1.2 ⟨by simp [hv₄₂], by simp [hv₄₂, hw]⟩⟩
  · have hint : ({r₂} : Set (Row E)) ~[intro Dref.u₂] J₃ := by
      refine ⟨fun i hi ↦ ⟨_, ⟨c₀, hc₀, rfl⟩, ↑c₀, ?_⟩, fun j ⟨c, hc, hj⟩ ↦ ⟨r₂, rfl, ↑c, ?_⟩⟩
      · rw [Set.mem_singleton_iff.1 hi]
        simp [r₂]
      · simp [← hj, r₂]
    refine (mem_max_test_atom_self_iff (P := fun x ↦ M.convention (x 0))
      (Set.singleton_nonempty r₂)
      ⟨c₀, by simpa using hc₀⟩).2 ⟨hint, ?_⟩
    rw [Set.image2_singleton_left]
    ext j
    simp only [J₃, r₂, mem_nonDummy, Set.mem_image, Set.mem_ofPred_eq, Matrix.cons_val_zero,
      extend_eq_update, update_row_u₂, val_apply]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, -⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc, rfl⟩, by simp⟩
  · have hv₂ : value Dref.u₂ J₃ = {c | M.convention c} := by
      ext x
      simp [J₃]
    refine mem_maxSub_test_copy (by decide) ⟨by rw [value_copy_self, hv₂]; exact hc, ?_⟩
    rw [value_copy_self, hcopy, hv₂]
    intro c hc
    have hcell : cell Dref.u₃ ↑c ((fun c : E ↦ row ↑M.harvey ↑c ↑c ↑w ⊥) '' {c | M.convention c}) =
        ({row ↑M.harvey ↑c ↑c ↑w ⊥} : Set (Row E)) := by
      ext j
      simp only [mem_cell, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff, val_apply]
      constructor
      · rintro ⟨⟨c', -, rfl⟩, h⟩
        rw [row_u₃, Flat.coe_inj] at h
        rw [h]
      · rintro rfl
        exact ⟨⟨c, hc, rfl⟩, rfl⟩
    rw [hcell, singleton_mem_atom_iff (y := ![M.harvey, w, c]) fun k ↦ by fin_cases k <;> rfl]
    exact h c hc
  · simp only [mem_det, GQ.every]
    rw [value_copy_of_ne (by decide), value_copy_self]
    exact fun _ h ↦ h

-- (88), (86)
theorem exists_courtAt₂_output (hc : ∃ c, M.convention c) {f : E → E}
    (hf : ∀ c, M.convention c → M.woman (f c) ∧ M.courtAt M.harvey (f c) c) :
    ∃ J, {iStar} ~[courtSentence M courtAt₂] J ∧ value Dref.u₄ J = f '' {c | M.convention c} ∧
      ∀ c, M.convention c → f c ∈ value Dref.u₄ (cell Dref.u₃ c J) := by
  obtain ⟨c₀, hc₀⟩ := hc
  have hc : ∃ c, M.convention c := ⟨c₀, hc₀⟩
  set r₁ : Row E := row ↑M.harvey ⊥ ⊥ ⊥ ⊥
  set J₃ : Set (Row E) := (fun c : E ↦ row ↑M.harvey ↑c ⊥ ⊥ ⊥) '' {c | M.convention c}
  set J : Set (Row E) := {j | ∃ c, M.convention c ∧
    (j = row ↑M.harvey ↑c ↑c ⊥ ⊥ ∨ j = row ↑M.harvey ↑c ↑c ↑(f c) ⊥)}
  have hcopy : copy Dref.u₃ Dref.u₂ J₃ =
      (fun c : E ↦ row ↑M.harvey ↑c ↑c ⊥ ⊥) '' {c | M.convention c} := by
    ext j
    simp [copy, J₃]
  have hv₂ : value Dref.u₂ J₃ = {c | M.convention c} := by
    ext x
    simp [J₃]
  have hcellJ (c : E) (hc : M.convention c) : cell Dref.u₃ ↑c J =
      ({row ↑M.harvey ↑c ↑c ⊥ ⊥, row ↑M.harvey ↑c ↑c ↑(f c) ⊥} : Set (Row E)) := by
    ext j
    simp only [J, mem_cell, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      val_apply]
    constructor
    · rintro ⟨⟨c', -, rfl | rfl⟩, h⟩ <;> rw [row_u₃, Flat.coe_inj] at h <;> subst h <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨c, hc, .inl rfl⟩, rfl⟩
      · exact ⟨⟨c, hc, .inr rfl⟩, rfl⟩
  have hcellK (c : E) (hc : M.convention c) :
      cell Dref.u₃ ↑c ((fun c : E ↦ row ↑M.harvey ↑c ↑c ⊥ ⊥) '' {c | M.convention c}) =
        ({row ↑M.harvey ↑c ↑c ⊥ ⊥} : Set (Row E)) := by
    ext j
    simp only [mem_cell, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff, val_apply]
    constructor
    · rintro ⟨⟨c', -, rfl⟩, h⟩
      rw [row_u₃, Flat.coe_inj] at h
      rw [h]
    · rintro rfl
      exact ⟨⟨c, hc, rfl⟩, rfl⟩
  have hD (c : E) (hc : M.convention c) :
      ({row ↑M.harvey ↑c ↑c ⊥ ⊥} : Set (Row E)) ~[((intro Dref.u₄ ○ test (sing Dref.u₄)) ○
        test (atom (fun x ↦ M.woman (x 0)) ![Dref.u₄])) ○
        test (atom (fun x ↦ M.courtAt (x 0) (x 1) (x 2)) ![Dref.u₁, Dref.u₄, Dref.u₃])]
        ({row ↑M.harvey ↑c ↑c ⊥ ⊥, row ↑M.harvey ↑c ↑c ↑(f c) ⊥} : Set (Row E)) := by
    have hv : value Dref.u₄
        ({row ↑M.harvey ↑c ↑c ⊥ ⊥, row ↑M.harvey ↑c ↑c ↑(f c) ⊥} : Set (Row E)) = {f c} := by
      ext
      simp [eq_comm]
    simp only [mem_comp_test]
    refine ⟨⟨⟨⟨fun i hi ↦ ⟨_, .inl rfl, ⊥, ?_⟩, fun j hj ↦ ⟨_, rfl, ?_⟩⟩, f c, hv⟩,
      mem_atom_vec1.2 ⟨by simp [hv], by simp [hv, (hf c hc).1]⟩⟩, ?_⟩
    · rw [Set.mem_singleton_iff.1 hi]
      simp
    · rcases hj with rfl | rfl
      · exact ⟨⊥, by simp⟩
      · exact ⟨↑(f c), by simp⟩
    · rw [mem_atom, Set.insert_eq, tuples_union, tuples_singleton_of_eq_bot (k := 1) rfl,
        tuples_singleton_of_eq (y := ![M.harvey, f c, c]) fun k ↦ by fin_cases k <;> rfl]
      simpa using (hf c hc).2
  refine ⟨J, ?_, ?_, fun c hc ↦ ?_⟩
  · simp only [courtSentence, name, courtAt₂, indef, every, noun, distrib_test_atom_self]
    refine ⟨{r₁}, mem_comp_test.2 ⟨?_, ?_⟩, mem_comp_test.2 ⟨⟨J₃, ?_, ?_⟩, ?_⟩⟩
    · simpa [iStar_eq_row, r₁] using singleton_mem_intro (iStar : Row E) Dref.u₁ ↑M.harvey
    · exact value_singleton_of_eq (by simp [r₁])
    · have hint : ({r₁} : Set (Row E)) ~[intro Dref.u₂] J₃ := by
        refine ⟨fun i hi ↦ ⟨_, ⟨c₀, hc₀, rfl⟩, ↑c₀, ?_⟩, fun j ⟨c, hc, hj⟩ ↦ ⟨r₁, rfl, ↑c, ?_⟩⟩
        · rw [Set.mem_singleton_iff.1 hi]
          simp [r₁]
        · simp [← hj, r₁]
      refine (mem_max_test_atom_self_iff (P := fun x ↦ M.convention (x 0))
        (Set.singleton_nonempty r₁) ⟨c₀, by simpa using hc₀⟩).2 ⟨hint, ?_⟩
      rw [Set.image2_singleton_left]
      ext j
      simp only [J₃, r₁, mem_nonDummy, Set.mem_image, Set.mem_ofPred_eq, Matrix.cons_val_zero,
        extend_eq_update, update_row_u₂, val_apply]
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, -⟩
        exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc, rfl⟩, by simp⟩
    · rw [maxSub, mem_max]
      refine ⟨⟨_, mem_intro_copy J₃,
        mem_test_comp.2 ⟨copy_mem_structSubAll (by decide) J₃, ?_⟩⟩, ?_⟩
      · rw [hcopy, mem_distrib]
        refine ⟨?_, ⟨c₀, _, ⟨c₀, hc₀, rfl⟩, rfl⟩, ?_, ?_⟩
        · ext j
          simp only [J, mem_cell, Set.mem_image, Set.mem_ofPred_eq, val_apply]
          constructor
          · rintro ⟨⟨c, -, rfl⟩, h⟩
            simp at h
          · rintro ⟨⟨c, -, rfl | rfl⟩, h⟩ <;> simp at h
        · ext x
          simp only [J, mem_value, Set.mem_image, Set.mem_ofPred_eq, val_apply]
          constructor
          · rintro ⟨_, ⟨c, hc, rfl⟩, hx⟩
            exact ⟨_, ⟨c, hc, .inl rfl⟩, hx⟩
          · rintro ⟨_, ⟨c, hc, rfl | rfl⟩, hx⟩ <;> exact ⟨_, ⟨c, hc, rfl⟩, hx⟩
        · rintro c ⟨_, ⟨c', hc', rfl⟩, h⟩
          simp only [val_apply, row_u₃, embed_flat, Flat.coe_inj] at h
          subst h
          rw [hcellK c' hc', hcellJ c' hc']
          exact hD c' hc'
      · rintro K ⟨K₀, hi₃, hK⟩ hJK k ⟨hk, hk₃⟩
        obtain ⟨hss, hdist'⟩ := mem_test_comp.1 hK
        obtain ⟨-, -, hv, hcells⟩ := mem_distrib.1 hdist'
        obtain ⟨c, hc⟩ := Flat.ne_bot_iff_exists.1 hk₃
        have hcK₀ : c ∈ value Dref.u₃ K₀ := hv ▸ ⟨k, hk, hc⟩
        have hDc := hcells c hcK₀
        simp only [mem_comp_test] at hDc
        obtain ⟨⟨⟨hi₄, w', hw'⟩, -⟩, -⟩ := hDc
        obtain ⟨k₀, ⟨hk₀, hk₀₃⟩, e, rfl⟩ := hi₄.2 k ⟨hk, hc⟩
        obtain ⟨_, ⟨x, hx, rfl⟩, e', rfl⟩ := hi₃.2 k₀ hk₀
        have hss₀ := hss.1 _ hk₀
        simp only [extend_eq_update, update_row_u₃, update_row_u₄, val_apply, row_u₃,
          row_u₂] at hk₀ hk₀₃ hk hss₀ ⊢
        subst hk₀₃
        obtain rfl : x = c := by
          rcases hss₀ with h | h
          · exact (Flat.coe_inj.1 h).symm
          · simp at h
        refine ⟨⟨x, hx, ?_⟩, by simp⟩
        induction e using Flat.recBotCoe with
        | bot => exact .inl rfl
        | coe b =>
          refine .inr ?_
          have hb : b ∈ value Dref.u₄ (cell Dref.u₃ ↑x K) := ⟨_, ⟨hk, rfl⟩, rfl⟩
          have hfx : f x ∈ value Dref.u₄ (cell Dref.u₃ ↑x K) :=
            ⟨_, ⟨(hJK ⟨⟨x, hx, .inr rfl⟩, by simp⟩).1, rfl⟩, rfl⟩
          rw [hw'] at hb hfx
          rw [Set.mem_singleton_iff.1 hb, Set.mem_singleton_iff.1 hfx]
    · simp only [mem_det, GQ.every]
      rintro x ⟨j, ⟨c, hc, rfl | rfl⟩, hx⟩ <;> exact ⟨_, ⟨c, hc, .inl rfl⟩, hx⟩
  · ext x
    simp only [J, mem_value, Set.mem_ofPred_eq, Set.mem_image, val_apply]
    constructor
    · rintro ⟨j, ⟨c, hc, rfl | rfl⟩, hx⟩
      · simp at hx
      · exact ⟨c, hc, Flat.coe_inj.1 hx⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨_, ⟨c, hc, .inr rfl⟩, rfl⟩
  · rw [hcellJ c hc]
    exact ⟨_, .inr rfl, rfl⟩

/-! #### The second sentence -/

theorem mem_dom_prettySentence :
    J ∈ (prettySentence M).dom ↔ ∃ w, value Dref.u₄ J = {w} ∧ M.veryPretty w := by
  simp only [prettySentence, pron, noun, test_comp_test, dom_test, Set.mem_inter_iff, sing,
    Set.mem_ofPred_eq, mem_atom_vec1]
  constructor
  · rintro ⟨⟨w, hw⟩, -, h⟩
    exact ⟨w, hw, by simpa using h w (by simp [hw])⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨⟨w, hw⟩, by simp [hw], by simp [hw, hp]⟩

/-- The universal adverb over a test entailing `COME{u₄, u₅}`. -/
private abbrev alwaysCome (C : Condition (Set (Row E))) : Update (Set (Row E)) :=
  maxSub Dref.u₅ Dref.u₃ (distrib Dref.u₅ (test C)) ○ test (det GQ.every Dref.u₃ Dref.u₅)

private theorem always_come {C : Condition (Set (Row E))}
    (hC : C ⊆ atom (fun x ↦ M.come (x 0) (x 1)) ![Dref.u₄, Dref.u₅])
    (h : J ∈ (alwaysCome C).dom) :
    ∀ c ∈ value Dref.u₃ J, ∃ w ∈ value Dref.u₄ (cell Dref.u₃ c J), M.come w c := by
  obtain ⟨J', hJJ'⟩ := h
  obtain ⟨hmax, hev⟩ := mem_comp_test.1 hJJ'
  rw [distrib_test] at hmax
  obtain ⟨K, -, hK⟩ := max_subset _ _ hmax
  obtain ⟨hss, rfl, hC5⟩ := mem_test_comp.1 hK
  have hP := (preserves_test ![Dref.u₃, Dref.u₄] _).maxSub (by decide) hmax
  have hv₃ := ((preserves_test ![Dref.u₃] _).maxSub (by decide)).value_eq hmax
  intro c hc
  have hc₅ : c ∈ value Dref.u₅ K := hev c (hv₃.symm ▸ hc)
  obtain ⟨⟨p, k, ⟨hk, hk₅⟩, hp₁, hp₂⟩, hcome⟩ := mem_atom_vec2.1 (hC (hC5.2 c hc₅))
  have hpc : p.2 = c := Flat.coe_inj.1 (hp₂.symm.trans hk₅)
  have hk₃ : val Dref.u₃ k = ↑c := by
    rcases hss.1 k hk with h | h
    · exact h.symm.trans hk₅
    · simp [h] at hk₅
  obtain ⟨j, hj, hjk⟩ := hP.2 k hk
  refine ⟨p.1, ⟨j, ⟨hj, (hjk 0).trans hk₃⟩, (hjk 1).trans hp₁⟩, ?_⟩
  simpa [hpc] using hcome ⟨p.1, p.2⟩ ⟨k, ⟨hk, hk₅⟩, hp₁, hp₂⟩

private theorem always_come_of {C : Condition (Set (Row E))} (hne : (value Dref.u₃ J).Nonempty)
    (hC : ∀ c ∈ value Dref.u₃ J, cell Dref.u₅ c (copy Dref.u₅ Dref.u₃ J) ∈ C) :
    J ∈ (alwaysCome C).dom := by
  refine ⟨copy Dref.u₅ Dref.u₃ J, mem_comp_test.2 ⟨?_, ?_⟩⟩
  · rw [distrib_test]
    refine mem_maxSub_test_copy (by decide) ⟨?_, fun c hc ↦ hC c ?_⟩
    · rwa [value_copy_self]
    · rwa [value_copy_self] at hc
  · simp only [mem_det, GQ.every]
    rw [value_copy_self, value_copy_of_ne (by decide)]
    exact fun _ h ↦ h

private theorem cell_copy_mem {c w : E} (hw : value Dref.u₄ (cell Dref.u₃ c J) = {w})
    (hcome : M.come w c) :
    cell Dref.u₅ c (copy Dref.u₅ Dref.u₃ J) ∈
      sing Dref.u₄ ∩ atom (fun x ↦ M.come (x 0) (x 1)) ![Dref.u₄, Dref.u₅] := by
  rw [cell_copy_self]
  refine ⟨⟨w, by rw [value_copy_of_ne (by decide), hw]⟩, mem_atom_vec2.2 ⟨?_, ?_⟩⟩
  · obtain ⟨x, ⟨hx, hx₃⟩, hx₄⟩ := (hw ▸ rfl : w ∈ value Dref.u₄ (cell Dref.u₃ c J))
    exact ⟨(w, c), _, ⟨x, ⟨hx, hx₃⟩, rfl⟩, by simpa using hx₄, by simpa using hx₃⟩
  · rintro ⟨y, z⟩ ⟨_, ⟨x, ⟨hx, hx₃⟩, rfl⟩, hy, hz⟩
    have hy' : y ∈ value Dref.u₄ (cell Dref.u₃ c J) := ⟨x, ⟨hx, hx₃⟩, by simpa using hy⟩
    rw [hw] at hy'
    obtain rfl := hy'
    obtain rfl : z = c := Flat.coe_inj.1 (by simpa [hx₃] using hz.symm)
    simpa using hcome

theorem comeSentence₁_imp (h : J ∈ (comeSentence M come₁).dom) : J ∈ sing Dref.u₄ ∧
    ∀ c ∈ value Dref.u₃ J, ∃ w ∈ value Dref.u₄ (cell Dref.u₃ c J), M.come w c := by
  simp only [comeSentence, come₁, always, pron] at h
  obtain ⟨J', hJJ'⟩ := h
  obtain ⟨hs, hJJ'⟩ := mem_test_comp.1 (by simpa only [comp_assoc] using hJJ')
  exact ⟨hs, always_come M subset_rfl ⟨J', hJJ'⟩⟩

theorem comeSentence₂_imp (h : J ∈ (comeSentence M come₂).dom) :
    ∀ c ∈ value Dref.u₃ J, ∃ w ∈ value Dref.u₄ (cell Dref.u₃ c J), M.come w c := by
  simp only [comeSentence, come₂, always, pron, test_comp_test] at h
  exact always_come M Set.inter_subset_right h

theorem mem_dom_comeSentence₁_of (hne : (value Dref.u₃ J).Nonempty) (hs : J ∈ sing Dref.u₄)
    (h : ∀ c ∈ value Dref.u₃ J, ∃ w, value Dref.u₄ (cell Dref.u₃ c J) = {w} ∧ M.come w c) :
    J ∈ (comeSentence M come₁).dom := by
  simp only [comeSentence, come₁, always, pron]
  obtain ⟨J', hJJ'⟩ := always_come_of (C := atom (fun x ↦ M.come (x 0) (x 1)) ![Dref.u₄, Dref.u₅])
    hne fun c hc ↦ let ⟨w, hw, hcome⟩ := h c hc; (cell_copy_mem M hw hcome).2
  exact ⟨J', by simpa only [comp_assoc] using mem_test_comp.2 ⟨hs, hJJ'⟩⟩

theorem mem_dom_comeSentence₂_of (hne : (value Dref.u₃ J).Nonempty)
    (h : ∀ c ∈ value Dref.u₃ J, ∃ w, value Dref.u₄ (cell Dref.u₃ c J) = {w} ∧ M.come w c) :
    J ∈ (comeSentence M come₂).dom := by
  simp only [comeSentence, come₂, always, pron, test_comp_test]
  exact always_come_of hne fun c hc ↦ let ⟨w, hw, hcome⟩ := h c hc; cell_copy_mem M hw hcome

/-! #### Discourses (5) and (6) -/

private theorem mem_dom_comp_iff {D D' : Update (Set (Row E))} :
    {iStar} ∈ (D ○ D').dom ↔ ∃ J, {iStar} ~[D] J ∧ J ∈ D'.dom :=
  ⟨fun ⟨_, J, hJ, hK⟩ ↦ ⟨J, hJ, _, hK⟩, fun ⟨J, hJ, K, hK⟩ ↦ ⟨K, J, hJ, hK⟩⟩

-- (6)
private theorem comeSentence_iff {w : E} (hc : ∃ c, M.convention c)
    (hv₃ : value Dref.u₃ J = {c | M.convention c}) (hv₄ : value Dref.u₄ J = {w})
    (hcell : ∀ c, M.convention c → value Dref.u₄ (cell Dref.u₃ c J) = {w}) :
    (J ∈ (comeSentence M come₁).dom ↔ ∀ c, M.convention c → M.come w c) ∧
      (J ∈ (comeSentence M come₂).dom ↔ ∀ c, M.convention c → M.come w c) := by
  have hne : (value Dref.u₃ J).Nonempty := hv₃ ▸ hc
  have hconv {c : E} (h : c ∈ value Dref.u₃ J) : M.convention c := by rwa [hv₃] at h
  have key (h : ∀ c ∈ value Dref.u₃ J, ∃ w' ∈ value Dref.u₄ (cell Dref.u₃ c J), M.come w' c)
      (c : E) (hc : M.convention c) : M.come w c := by
    obtain ⟨w', hw', hcome⟩ := h c (by rw [hv₃]; exact hc)
    rw [hcell c hc] at hw'
    rwa [← Set.mem_singleton_iff.1 hw']
  have hof (h : ∀ c, M.convention c → M.come w c) (c : E) (hc : c ∈ value Dref.u₃ J) :
      ∃ w', value Dref.u₄ (cell Dref.u₃ c J) = {w'} ∧ M.come w' c :=
    ⟨w, hcell c (hconv hc), h c (hconv hc)⟩
  exact ⟨⟨fun h ↦ key (comeSentence₁_imp M h).2,
      fun h ↦ mem_dom_comeSentence₁_of M hne ⟨w, hv₄⟩ (hof h)⟩,
    ⟨fun h ↦ key (comeSentence₂_imp M h), fun h ↦ mem_dom_comeSentence₂_of M hne (hof h)⟩⟩

private theorem courtAt₂_output' (hJ : {iStar} ~[courtSentence M courtAt₂] J) {w : E}
    (hv₄ : value Dref.u₄ J = {w}) :
    (∀ c, M.convention c → M.woman w ∧ M.courtAt M.harvey w c) ∧
      value Dref.u₃ J = {c | M.convention c} ∧
      ∀ c, M.convention c → value Dref.u₄ (cell Dref.u₃ c J) = {w} := by
  obtain ⟨hv₃, h⟩ := courtAt₂_output M hJ
  have hw (c : E) (hc : M.convention c) :
      M.woman w ∧ M.courtAt M.harvey w c ∧ value Dref.u₄ (cell Dref.u₃ c J) = {w} := by
    obtain ⟨w', hw', hcourt, hcell⟩ := h c hc
    have : w' ∈ value Dref.u₄ J := value_mono (fun _ hk ↦ hk.1) (hcell ▸ Set.mem_singleton w')
    rw [hv₄, Set.mem_singleton_iff] at this
    subst this
    exact ⟨hw', hcourt, hcell⟩
  exact ⟨fun c hc ↦ ⟨(hw c hc).1, (hw c hc).2.1⟩, hv₃, fun c hc ↦ (hw c hc).2.2⟩

/-- (85) is true at `I★` iff some woman is courted by Harvey at every convention (p. 471). -/
theorem courtAt₁_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₁).dom ↔
      ∃ w, M.woman w ∧ ∀ c, M.convention c → M.courtAt M.harvey w c := by
  refine ⟨fun ⟨J, hJ⟩ ↦ ?_, fun ⟨w, hw, h⟩ ↦ ?_⟩
  · obtain ⟨w, hw, h, -⟩ := courtAt₁_output M hJ
    exact ⟨w, hw, h⟩
  · obtain ⟨J, hJ, -⟩ := exists_courtAt₁_output M hc hw h
    exact ⟨J, hJ⟩

/-- (86) is true at `I★` iff Harvey courts some woman or other at every convention (p. 472). -/
theorem courtAt₂_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₂).dom ↔
      ∀ c, M.convention c → ∃ w, M.woman w ∧ M.courtAt M.harvey w c := by
  classical
  refine ⟨fun ⟨J, hJ⟩ c hc ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw, hcourt, -⟩ := (courtAt₂_output M hJ).2 c hc
    exact ⟨w, hw, hcourt⟩
  · obtain ⟨J, hJ, -⟩ := exists_courtAt₂_output M hc (f := fun c ↦
      if hc : M.convention c then (h c hc).choose else c) fun c hc ↦ by
        simpa [hc] using (h c hc).choose_spec
    exact ⟨J, hJ⟩

-- (5), (85), (89)
theorem courtAt₁_pretty_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₁ ○ prettySentence M).dom ↔
      ∃ w, M.woman w ∧ (∀ c, M.convention c → M.courtAt M.harvey w c) ∧ M.veryPretty w := by
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hp⟩
    obtain ⟨w, hw, h, -, hv₄, -⟩ := courtAt₁_output M hJ
    obtain ⟨w', hv₄', hpretty⟩ := (mem_dom_prettySentence M).1 hp
    obtain rfl : w = w' := Set.singleton_injective (hv₄.symm.trans hv₄')
    exact ⟨w, hw, h, hpretty⟩
  · rintro ⟨w, hw, h, hpretty⟩
    obtain ⟨J, hJ, hv₄⟩ := exists_courtAt₁_output M hc hw h
    exact ⟨J, hJ, (mem_dom_prettySentence M).2 ⟨w, hv₄, hpretty⟩⟩

/-- Discourse (5) under the narrow-scope indefinite (86) + (89): the singular pronoun makes the
truth conditions those of the wide-scope indefinite (pp. 472–473). -/
theorem courtAt₂_pretty_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₂ ○ prettySentence M).dom ↔
      ∃ w, M.woman w ∧ (∀ c, M.convention c → M.courtAt M.harvey w c) ∧ M.veryPretty w := by
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hp⟩
    obtain ⟨w, hv₄, hpretty⟩ := (mem_dom_prettySentence M).1 hp
    obtain ⟨h, -⟩ := courtAt₂_output' M hJ hv₄
    obtain ⟨c₀, hc₀⟩ := hc
    exact ⟨w, (h c₀ hc₀).1, fun c hc ↦ (h c hc).2, hpretty⟩
  · rintro ⟨w, hw, h, hpretty⟩
    obtain ⟨J, hJ, hv₄, -⟩ := exists_courtAt₂_output M hc (f := fun _ ↦ w)
      fun c hc ↦ ⟨hw, h c hc⟩
    rw [Set.Nonempty.image_const (s := {c | M.convention c}) hc] at hv₄
    exact ⟨J, hJ, (mem_dom_prettySentence M).2 ⟨w, hv₄, hpretty⟩⟩

/-- Discourse (6) under (86) + (96), the combination (97): the women may differ from
convention to convention (p. 474). -/
theorem courtAt₂_come₂_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₂ ○ comeSentence M come₂).dom ↔
      ∀ c, M.convention c → ∃ w, M.woman w ∧ M.courtAt M.harvey w c ∧ M.come w c := by
  classical
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hcome⟩ c hc
    obtain ⟨hv₃, h⟩ := courtAt₂_output M hJ
    obtain ⟨w, hw, hcourt, hcell⟩ := h c hc
    obtain ⟨w', hw', hcw⟩ := comeSentence₂_imp M hcome c (hv₃ ▸ hc)
    rw [hcell, Set.mem_singleton_iff] at hw'
    exact ⟨w, hw, hcourt, hw' ▸ hcw⟩
  · intro h
    set f : E → E := fun c ↦ if hc : M.convention c then (h c hc).choose else c
    have hf (c : E) (hc : M.convention c) :
        M.woman (f c) ∧ M.courtAt M.harvey (f c) c ∧ M.come (f c) c := by
      simpa [f, hc] using (h c hc).choose_spec
    obtain ⟨J, hJ, -, hfJ⟩ := exists_courtAt₂_output M hc fun c hc ↦ ⟨(hf c hc).1, (hf c hc).2.1⟩
    obtain ⟨hv₃, h₂⟩ := courtAt₂_output M hJ
    refine ⟨J, hJ, mem_dom_comeSentence₂_of M (hv₃ ▸ hc) fun c hc₃ ↦ ?_⟩
    rw [hv₃] at hc₃
    obtain ⟨w, -, -, hcell⟩ := h₂ c hc₃
    have := hfJ c hc₃
    rw [hcell, Set.mem_singleton_iff] at this
    exact ⟨w, hcell, this ▸ (hf c hc₃).2.2⟩

-- (6), (85), (95), p. 474
theorem courtAt₁_come₁_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₁ ○ comeSentence M come₁).dom ↔
      ∃ w, M.woman w ∧ ∀ c, M.convention c → M.courtAt M.harvey w c ∧ M.come w c := by
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hcome⟩
    obtain ⟨w, hw, h, hv₃, hv₄, hcell⟩ := courtAt₁_output M hJ
    have := (comeSentence_iff M hc hv₃ hv₄ hcell).1.1 hcome
    exact ⟨w, hw, fun c hc ↦ ⟨h c hc, this c hc⟩⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨J, hJ, hv₄⟩ := exists_courtAt₁_output M hc hw fun c hc ↦ (h c hc).1
    obtain ⟨w', -, -, hv₃, hv₄', hcell⟩ := courtAt₁_output M hJ
    obtain rfl : w' = w := Set.singleton_injective (hv₄'.symm.trans hv₄)
    exact ⟨J, hJ, (comeSentence_iff M hc hv₃ hv₄ hcell).1.2 fun c hc ↦ (h c hc).2⟩

-- (6), (85), (96), p. 474
theorem courtAt₁_come₂_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₁ ○ comeSentence M come₂).dom ↔
      ∃ w, M.woman w ∧ ∀ c, M.convention c → M.courtAt M.harvey w c ∧ M.come w c := by
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hcome⟩
    obtain ⟨w, hw, h, hv₃, hv₄, hcell⟩ := courtAt₁_output M hJ
    have := (comeSentence_iff M hc hv₃ hv₄ hcell).2.1 hcome
    exact ⟨w, hw, fun c hc ↦ ⟨h c hc, this c hc⟩⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨J, hJ, hv₄⟩ := exists_courtAt₁_output M hc hw fun c hc ↦ (h c hc).1
    obtain ⟨w', -, -, hv₃, hv₄', hcell⟩ := courtAt₁_output M hJ
    obtain rfl : w' = w := Set.singleton_injective (hv₄'.symm.trans hv₄)
    exact ⟨J, hJ, (comeSentence_iff M hc hv₃ hv₄ hcell).2.2 fun c hc ↦ (h c hc).2⟩

-- (6), (86), (95), p. 474
theorem courtAt₂_come₁_true_iff (hc : ∃ c, M.convention c) :
    {iStar} ∈ (courtSentence M courtAt₂ ○ comeSentence M come₁).dom ↔
      ∃ w, M.woman w ∧ ∀ c, M.convention c → M.courtAt M.harvey w c ∧ M.come w c := by
  rw [mem_dom_comp_iff]
  constructor
  · rintro ⟨J, hJ, hcome⟩
    obtain ⟨w, hv₄⟩ := (comeSentence₁_imp M hcome).1
    obtain ⟨h, hv₃, hcell⟩ := courtAt₂_output' M hJ hv₄
    have := (comeSentence_iff M hc hv₃ hv₄ hcell).1.1 hcome
    obtain ⟨c₀, hc₀⟩ := hc
    exact ⟨w, (h c₀ hc₀).1, fun c hc ↦ ⟨(h c hc).2, this c hc⟩⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨J, hJ, hv₄, -⟩ := exists_courtAt₂_output M hc (f := fun _ ↦ w)
      fun c hc ↦ ⟨hw, (h c hc).1⟩
    rw [Set.Nonempty.image_const (s := {c | M.convention c}) hc] at hv₄
    obtain ⟨-, hv₃, hcell⟩ := courtAt₂_output' M hJ hv₄
    exact ⟨J, hJ, (comeSentence_iff M hc hv₃ hv₄ hcell).1.2 fun c hc ↦ (h c hc).2⟩

/-! #### The readings of (5) and (6) -/

/-- The individuals of a scenario with Harvey, two conventions and two women. -/
inductive Indiv where
  | harvey
  | c₁
  | c₂
  | w₁
  | w₂
  deriving DecidableEq

/-- Harvey courts `w₁` at `c₁` and `w` at `c₂`, and each woman comes to the banquet with him
where he courts her; both women are very pretty. At `w = w₁` he courts the same woman at both
conventions, at `w = w₂` a different one at each. -/
def scenario (w : Indiv) : Model Indiv where
  harvey := .harvey
  woman x := x = .w₁ ∨ x = .w₂
  convention x := x = .c₁ ∨ x = .c₂
  courtAt x y z := x = .harvey ∧ (y = .w₁ ∧ z = .c₁ ∨ y = w ∧ z = .c₂)
  veryPretty x := x = .w₁ ∨ x = .w₂
  come y z := y = .w₁ ∧ z = .c₁ ∨ y = w ∧ z = .c₂

private theorem scenario_hc (w : Indiv) : ∃ c, (scenario w).convention c := ⟨.c₁, .inl rfl⟩

/-- The analysis gives (5) and (6) the readings of p. 444: both are true where Harvey courts the
same woman at both conventions, but where he courts a different woman at each, only (6) is
true under some scoping, namely (97). -/
theorem readings :
    ((∃ court ∈ [courtAt₁, courtAt₂], {iStar} ∈
        (courtSentence (scenario .w₁) court ○ prettySentence (scenario .w₁)).dom) ↔
      Examples.ex_5.readings.lookup "same woman" = some .acceptable) ∧
    ((∃ court ∈ [courtAt₁, courtAt₂], {iStar} ∈
        (courtSentence (scenario .w₂) court ○ prettySentence (scenario .w₂)).dom) ↔
      Examples.ex_5.readings.lookup "possibly different women" = some .acceptable) ∧
    ((∃ court ∈ [courtAt₁, courtAt₂], ∃ come ∈ [come₁, come₂], {iStar} ∈
        (courtSentence (scenario .w₁) court ○ comeSentence (scenario .w₁) come).dom) ↔
      Examples.ex_6.readings.lookup "same woman" = some .acceptable) ∧
    ((∃ court ∈ [courtAt₁, courtAt₂], ∃ come ∈ [come₁, come₂], {iStar} ∈
        (courtSentence (scenario .w₂) court ○ comeSentence (scenario .w₂) come).dom) ↔
      Examples.ex_6.readings.lookup "possibly different women" = some .acceptable) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    courtAt₁_pretty_true_iff _ (scenario_hc _), courtAt₂_pretty_true_iff _ (scenario_hc _),
    courtAt₁_come₁_true_iff _ (scenario_hc _), courtAt₁_come₂_true_iff _ (scenario_hc _),
    courtAt₂_come₁_true_iff _ (scenario_hc _), courtAt₂_come₂_true_iff _ (scenario_hc _)]
  refine ⟨iff_of_true ?_ (by decide), iff_of_false ?_ (by decide), iff_of_true ?_ (by decide),
    iff_of_true ?_ (by decide)⟩
  · exact .inl ⟨.w₁, .inl rfl, by rintro c (rfl | rfl) <;> simp [scenario], .inl rfl⟩
  · rintro (⟨w, -, h, -⟩ | ⟨w, -, h, -⟩) <;>
      obtain ⟨-, ⟨rfl, -⟩ | ⟨-, ⟨⟩⟩⟩ := h .c₁ (.inl rfl) <;>
      obtain ⟨-, ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, -⟩⟩ := h .c₂ (.inr rfl)
  · exact .inl (.inl ⟨.w₁, .inl rfl, by rintro c (rfl | rfl) <;> simp [scenario]⟩)
  · refine .inr (.inr fun c hc ↦ ?_)
    rcases hc with rfl | rfl
    · exact ⟨.w₁, .inl rfl, by simp [scenario]⟩
    · exact ⟨.w₂, .inr rfl, by simp [scenario]⟩

end Brasoveanu2010
