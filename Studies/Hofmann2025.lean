module

public import Linglib.Data.Examples.Hofmann2025
public import Linglib.Semantics.Dynamic.ICDRT

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

Hofmann accounts for anaphora to negated indefinites in the intensional compositional DRT of
`Semantics/Dynamic/ICDRT.lean`. An indefinite introduces its discourse referent globally,
relative to the propositional referent of its local context, and a pronoun is acceptable when
its referent exists throughout its own local context under a consistent assignment of speaker
commitments. This file runs the fragment of the paper's Appendix C on its four-world model of
the bathroom discourses.

## Implementation notes

* The operators of the fragment are CDRT's: a DRS `[δ | C]` is `box {δ} C` and
  `max_φ` is `maxAt` at a propositional dref.
* The maximization operators of App. C (18) and (19), and of the displayed updates (41), (43) and
  (44), apply to updates that leave the maximized dref unchanged, so under the definition
  (40) they are vacuous (`maxAt_eq_of_fixes`): the fragment as printed does not exclude
  the nonmaximal rows of Table 3 (`negated_row4`). Maximizing the prejacent's context over
  the whole assertion selects the paper's row (`negated_max`), and the commitment set of
  Figure 6 is the pragmatically maximal one of (35) (`veridical_maximal`).
* Commitment sets are introduced at the initial state and never changed by an update, as in
  (33) and Table 1, so a derivation starts from the initial state whose commitment set its
  output shows; Figure 6's is narrower than Figure 5's.
* The modal-subordination discourse of §4.4 needs the eight-world model with a doxastic state
  for Sue and is not run.

## TODO

* The eight-world model of §4.4 and the attitude update (52).

## References

* [hofmann-2025]
* [muskens-1996]
* [stone-1999]
* [brasoveanu-2006]
* [krahmer-muskens-1995]
* [roberts-1989]
* [karttunen-1976]
-/

@[expose] public section

namespace Hofmann2025

open DynamicSemantics DynamicSemantics.Update ICDRT SetRel

variable {W E : Type*}

/-! ### Commitment and veridicality ((16), (36), (37)) -/

/-- An individual dref is veridical if it is entailed in the commitment set (36a), and
hypothetical when it is not veridical (16b). -/
abbrev VeridicalIndiv (φ_DC : PVar) (v : IVar) (i : State W E) : Prop :=
  i ∈ localEntailment φ_DC v

/-- An individual dref is counterfactual if it has no referent throughout the commitment set
(37a). -/
def CounterfactualIndiv (φ_DC : PVar) (v : IVar) (i : State W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w = none

/-- A propositional dref is counterfactual if it is disjoint from the commitment set (37b). -/
def CounterfactualProp (φ_DC δ : PVar) (i : State W E) : Prop :=
  i.prop φ_DC ∩ i.prop δ = ∅

-- (16)
theorem CounterfactualIndiv.not_veridicalIndiv {φ_DC : PVar} {v : IVar} {i : State W E}
    (hc : CounterfactualIndiv φ_DC v i) (hDC : (i.prop φ_DC).Nonempty) :
    ¬VeridicalIndiv φ_DC v i := fun hv ↦
  let ⟨w, hw⟩ := hDC; hv w hw (hc w hw)

-- (20a)
theorem counterfactualProp_of_mem_eqCompl {φ_DC φ φ' : PVar} {i : State W E}
    (hc : i ∈ eqCompl φ φ') (hdec : i ∈ incl φ_DC φ) : CounterfactualProp φ_DC φ' i :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hw, hw'⟩ ↦ (hc ▸ hdec hw) hw'

/-! ### Accessibility (38) and the subset requirement (39) -/

/-- A dref `υ` is accessible (38) if it is entailed in the anaphor's local context `φ` and the
commitment set is consistent. The paper's consistency (31) covers every interlocutor; this is
one interlocutor's. -/
def Accessible (φ : PVar) (v : IVar) (φ_DC : PVar) (i : State W E) : Prop :=
  i ∈ localEntailment φ v ∧ (i.prop φ_DC).Nonempty

/-- In a veridical anaphor context, one the speaker's commitments entail, only a veridical
dref is accessible. -/
theorem veridicalIndiv_of_accessible {φ φ_DC : PVar} {v : IVar} {j : State W E}
    (hdec : j ∈ incl φ_DC φ) (h : Accessible φ v φ_DC j) : VeridicalIndiv φ_DC v j :=
  fun w hw ↦ h.1 w (hdec hw)

/-- A counterfactual antecedent admits no veridical anaphor, since the subset requirement (39)
empties the commitment set (§3.4.2, (26)). -/
theorem counterfactual_blocks_veridical (i j : State W E) (φ_DC φ_anaphor φ_neg : PVar)
    (h_extends_DC : j.prop φ_DC = i.prop φ_DC) (h_extends_neg : j.prop φ_neg = i.prop φ_neg)
    (h_disjoint : CounterfactualProp φ_DC φ_neg i) (h_dec : j ∈ incl φ_DC φ_anaphor)
    (h_subset : j ∈ incl φ_anaphor φ_neg) : ¬(j.prop φ_DC).Nonempty := by
  rintro ⟨w, hw⟩
  have hmem : w ∈ i.prop φ_DC ∩ i.prop φ_neg :=
    ⟨h_extends_DC ▸ hw, h_extends_neg ▸ h_subset (h_dec hw)⟩
  rw [h_disjoint] at hmem
  exact hmem

/-! ### The fragment of Appendix C

Each operator is a DRS `[δ | C] = box {δ} C` (App. B (12)) followed by maximization
`max_φ` (App. B (10b)), CDRT's `maxAt` at a propositional dref. -/

/-- A predicate, of type `e(wt)`, takes an individual dref and a local context to an update. -/
abbrev SemE (W E : Type*) := IVar → PVar → Update (State W E)

/-- A clause, of type `wt`, takes a local context to an update. -/
abbrev SemW (W E : Type*) := PVar → Update (State W E)

/-- The vacuous scope of an existential is the identity update. -/
def vacuousScope : SemE W E := fun _ _ ↦ SetRel.id

/-- A common noun is a test that its argument satisfies it in the local context (App. C (15)).
-/
def commonNoun (R : E → W → Prop) : SemE W E :=
  fun v φ ↦ test (pred R φ v)

/-- An intransitive verb phrase, of the same shape as a common noun. -/
abbrev intransVP (R : E → W → Prop) : SemE W E := commonNoun R

/-- The indefinite introduces its dref relative to the local context, then runs its restrictor
and its scope (App. C (16)). -/
def indefinite (v : IVar) (P P' : SemE W E) (φ : PVar) : Update (State W E) :=
  relUpdate φ v ○ P v φ ○ P' v φ

/-- A pronoun passes its index to the predicate (App. C (17)). -/
def pronoun (v : IVar) (P : SemE W E) (φ : PVar) : Update (State W E) := P v φ

/-- A proper name introduces a dref equal to its constant (App. C (14)). -/
def properName (name : E) (v : IVar) (P : SemE W E) (φ : PVar) : Update (State W E) :=
  box {v} {j | ∀ w : W, j.indiv v w = some name} ○ P v φ

/-- Negation introduces the complement of its context as the prejacent's context and maximizes it
over the prejacent (App. C (18a)). -/
def semNOT (φ' : PVar) (Sc : SemW W E) (φ : PVar) : Update (State W E) :=
  box {φ'} (eqCompl φ φ') ○ maxAt φ' (Sc φ')

/-- Disjunction introduces a context for each disjunct, whose union is its own (App. C (18b)). -/
def semOR (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (State W E) :=
  box {φ', φ''} {j | j.prop φ = j.prop φ' ∪ j.prop φ''} ○
    maxAt φ' (Sc' φ') ○ maxAt φ'' (Sc'' φ'')

/-- The conditional's context is the union of the antecedent's complement and the consequent's
context (App. C (18c)). -/
def semIF (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (State W E) :=
  box {φ', φ''} {j | j.prop φ = (j.prop φ')ᶜ ∪ j.prop φ''} ○
    maxAt φ' (Sc' φ') ○ maxAt φ'' (Sc'' φ'')

/-- Conjunction narrows the context through each conjunct in turn (App. C (18d)). -/
def semAND (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) : Update (State W E) :=
  box {φ'} (incl φ' φ) ○ maxAt φ' (Sc' φ') ○ box {φ''} (incl φ'' φ') ○ maxAt φ'' (Sc'' φ'')

/-- An attitude verb introduces a context the subject's doxastic state `dox` entails
(App. C (18e)). -/
def semBelieved (φ' : PVar) (dox : State W E → Set W) (Sc : SemW W E) (_φ : PVar) :
    Update (State W E) :=
  box {φ'} {j | dox j ⊆ j.prop φ'} ○ maxAt φ' (Sc φ')

/-- The declarative introduces the assertion's context, which the speaker's commitments entail
(20a), and maximizes it over the clause (App. C (19)). -/
def semDEC (φ_DC : PVar) (φ : PVar) (Sc : SemW W E) : Update (State W E) :=
  box {φ} (incl φ_DC φ) ○ maxAt φ (Sc φ)

/-! ### Maximization of a dref an update leaves fixed -/

theorem commonNoun_fixes (φ : PVar) (R : E → W → Prop) (v : IVar) (φ' : PVar) :
    Fixes φ (commonNoun R v φ') :=
  fixes_test _ _

theorem vacuousScope_fixes (φ : PVar) (v : IVar) (φ' : PVar) :
    Fixes φ (vacuousScope (W := W) (E := E) v φ') :=
  fixes_id _

theorem indefinite_fixes (φ : PVar) {v : IVar} {P P' : SemE W E} {φ' : PVar}
    (hP : Fixes φ (P v φ')) (hP' : Fixes φ (P' v φ')) : Fixes φ (indefinite v P P' φ') :=
  ((fixes_relUpdate φ φ' v).comp hP).comp hP'

theorem pronoun_fixes (φ : PVar) {v : IVar} {P : SemE W E} {φ' : PVar} (h : Fixes φ (P v φ')) :
    Fixes φ (pronoun v P φ') := h

theorem semNOT_fixes (φ : PVar) {φ' : PVar} {Sc : SemW W E} {φ₀ : PVar} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semNOT φ' Sc φ₀) :=
  (fixes_box (by simpa using h.symm) _).comp hSc.maxBy

theorem semOR_fixes (φ : PVar) {φ' φ'' : PVar} {Sc' Sc'' : SemW W E} {φ₀ : PVar}
    (h₁ : φ ≠ φ') (h₂ : φ ≠ φ'') (h' : Fixes φ (Sc' φ')) (h'' : Fixes φ (Sc'' φ'')) :
    Fixes φ (semOR φ' φ'' Sc' Sc'' φ₀) :=
  (((fixes_box (by simp [h₁, h₂]) _).comp h'.maxBy).comp h''.maxBy)

theorem semDEC_fixes (φ : PVar) {φ_DC φ' : PVar} {Sc : SemW W E} (h : φ' ≠ φ)
    (hSc : Fixes φ (Sc φ')) : Fixes φ (semDEC φ_DC φ' Sc) :=
  (fixes_box (by simpa using h.symm) _).comp hSc.maxBy

/-! ### The model M₁ (§3.3.2) -/

/-- The four worlds have a bathroom that is upstairs, a bathroom that is not, no bathroom and
something upstairs, and neither. -/
inductive World where
  | w_bu
  | w_b
  | w_u
  | w_0
  deriving DecidableEq

/-- The one entity of the model, the bathroom. -/
inductive Ent where
  | b
  deriving DecidableEq

open World Ent

/-- `b` is a bathroom in the two bathroom worlds. -/
def bathroom : Ent → World → Prop
  | .b, .w_bu => True
  | .b, .w_b => True
  | .b, _ => False

/-- `b` is upstairs in the two upstairs worlds. -/
def upstairs : Ent → World → Prop
  | .b, .w_bu => True
  | .b, .w_u => True
  | .b, _ => False

/-- The individual dref of the bathroom, defined exactly in the bathroom worlds. -/
def bathroomRef : World → Option Ent
  | .w_bu => some .b
  | .w_b => some .b
  | _ => none

/-- The propositional drefs of the derivations are the assertion's context and the contexts of
embedded clauses. -/
def φ₁ : PVar := ⟨1⟩
def φ₂ : PVar := ⟨2⟩
def φ₃ : PVar := ⟨3⟩
def φ₄ : PVar := ⟨4⟩
/-- The commitment set of the speaker `S`. -/
def φDC : PVar := ⟨10⟩
/-- The commitment sets of the interlocutors `A` and `B` of §4.3. -/
def φDCA : PVar := ⟨11⟩
def φDCB : PVar := ⟨12⟩
/-- The individual dref of the indefinite. -/
def υ : IVar := ⟨0⟩

/-- The null assignment (32) has no referents and no information. -/
def null : State World Ent := ⟨fun _ _ ↦ none, fun _ ↦ Set.univ⟩

/-- An initial state (33) of a single speaker whose commitment set is `dc`. -/
def init (dc : Set World) : State World Ent := null.updateProp φDC dc

/-- An initial state of the two interlocutors of §4.3. -/
def init₂ (dcA dcB : Set World) : State World Ent :=
  (null.updateProp φDCA dcA).updateProp φDCB dcB

/-- *There is a bathroom* (24) is the indefinite with the noun as restrictor and a vacuous scope.
-/
def thereIsABathroom : SemW World Ent := indefinite υ (commonNoun bathroom) vacuousScope

/-- *It is upstairs* (30) is the pronoun with the verb phrase. -/
def itIsUpstairs : SemW World Ent := pronoun υ (intransVP upstairs)

theorem thereIsABathroom_fixes (φ φ' : PVar) : Fixes φ (thereIsABathroom φ') :=
  indefinite_fixes φ (commonNoun_fixes φ _ _ _) (vacuousScope_fixes φ _ _)

theorem itIsUpstairs_fixes (φ φ' : PVar) : Fixes φ (itIsUpstairs φ') :=
  pronoun_fixes φ (commonNoun_fixes φ _ _ _)

theorem thereIsABathroom_output {φ : PVar} {k j : State World Ent}
    (h : k ~[thereIsABathroom φ] j) :
    (∀ w, w ∈ j.prop φ ↔ j.indiv υ w ≠ none) ∧ j.prop φ ⊆ {w_bu, w_b} := by
  obtain ⟨m, ⟨l, hrel, rfl, hpred⟩, rfl⟩ := h
  refine ⟨(mem_relUpdate.mp hrel).2, fun w hw ↦ ?_⟩
  have := hpred w hw
  revert this
  cases hv : l.indiv υ w with
  | none => exact False.elim
  | some e => cases e; cases w <;> simp [bathroom]

theorem itIsUpstairs_output {φ : PVar} {k j : State World Ent} (h : k ~[itIsUpstairs φ] j) :
    k = j ∧ ∀ w ∈ j.prop φ, j.indiv υ w ≠ none ∧ w ∈ ({w_bu, w_u} : Set World) := by
  obtain ⟨rfl, hpred⟩ := h
  refine ⟨rfl, fun w hw ↦ ?_⟩
  have := hpred w hw
  revert this
  cases hv : k.indiv υ w with
  | none => exact False.elim
  | some e => cases e; cases w <;> simp [upstairs]

/-! ### The veridical discourse (19a) and (30), Figures 5 and 6 -/

/-- *There is a bathroom. It is upstairs.* -/
def veridical : Update (State World Ent) :=
  semDEC φDC φ₁ thereIsABathroom ○ semDEC φDC φ₃ itIsUpstairs

/-- The output of Figure 6. -/
def j₆ : State World Ent :=
  ((((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef).updateProp φ₃ {w_bu})

/-- Figure 6 is an output of the veridical discourse from the initial state whose commitment
set it shows. -/
theorem veridical_run : init {w_bu} ~[veridical] j₆ := by
  refine ⟨((init {w_bu}).updateProp φ₁ {w_bu, w_b}).updateIndiv υ bathroomRef, ?_, ?_⟩
  · refine ⟨(init {w_bu}).updateProp φ₁ {w_bu, w_b}, updateProp_mem_box _ _ ?_, ?_⟩
    · intro w hw
      simp only [init, State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
      simp_all
    · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
      refine ⟨_, ⟨_, updateIndiv_mem_relUpdate _ fun w ↦ ?_, rfl, fun w hw ↦ ?_⟩, rfl⟩
      · cases w <;> simp [bathroomRef, init, State.updateProp_prop_self]
      · simp only [State.updateIndiv_prop, State.updateProp_prop_self] at hw
        cases w <;> simp_all [bathroomRef, bathroom]
  · refine ⟨j₆, updateProp_mem_box _ _ ?_, ?_⟩
    · intro w hw
      simp only [init, State.updateProp_prop_self, State.updateIndiv_prop,
        State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
        State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
      exact hw
    · rw [maxAt_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₆, State.updateProp_prop_self] at hw
      cases w <;> simp_all [j₆, bathroomRef, upstairs]

theorem veridical_veridicalIndiv : VeridicalIndiv φDC υ j₆ := by
  intro w hw
  simp only [j₆, init, State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    State.updateIndiv_prop, State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    State.updateProp_prop_self] at hw
  cases w <;> simp_all [j₆, bathroomRef]

-- Figure 6
theorem veridical_accessible : Accessible φ₃ υ φDC j₆ :=
  ⟨fun w hw ↦ by
    simp only [j₆, State.updateProp_prop_self] at hw
    cases w <;> simp_all [j₆, bathroomRef],
   ⟨w_bu, by simp [j₆, init, State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

-- (35), Figure 6
theorem veridical_maximal (dc : Set World) (h : State World Ent)
    (hrun : init dc ~[veridical] h) : ¬ (j₆.prop φDC ⊂ h.prop φDC) := by
  obtain ⟨h₁, ⟨k₁, hk₁, hmax₁⟩, ⟨k₂, hk₂, hmax₂⟩⟩ := hrun
  obtain ⟨hup₁, -⟩ := mem_box_singleton.mp hk₁
  obtain ⟨hup₂, hdec₂⟩ := mem_box_singleton.mp hk₂
  replace hup₁ := mem_randomAssign_prop.mp hup₁
  replace hup₂ := mem_randomAssign_prop.mp hup₂
  rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax₁
  rw [maxAt_eq_of_fixes (itIsUpstairs_fixes _ _)] at hmax₂
  obtain ⟨hbi, _⟩ := thereIsABathroom_output hmax₁
  obtain ⟨rfl, hup⟩ := itIsUpstairs_output hmax₂
  have hDC : k₂.prop φDC = dc := by
    rw [hup₂.1 φDC (by decide), (thereIsABathroom_fixes φDC φ₁).prop_eq hmax₁,
      hup₁.1 φDC (by decide)]
    simp [init]
  have hυ : k₂.indiv υ = h₁.indiv υ := hup₂.2 υ
  have hsub : dc ⊆ {w_bu} := fun w hw ↦ by
    have hw' := hdec₂ (hDC ▸ hw)
    obtain ⟨hne, hu⟩ := hup w hw'
    rw [hυ] at hne
    have hb : w ∈ h₁.prop φ₁ := (hbi w).2 hne
    have hb' := (thereIsABathroom_output hmax₁).2 hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb' hu ⊢
    rcases hb' with rfl | rfl <;> rcases hu with h | h <;> simp_all
  intro hlt
  rw [hDC] at hlt
  exact hlt.2 (fun w hw ↦ by
    have := hsub hw
    simp only [j₆, init, State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
      State.updateIndiv_prop, State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
      State.updateProp_prop_self]
    exact this)

/-! ### The negated antecedent (41), Figure 7 -/

/-- *There isn't a bathroom.* -/
def negated : Update (State World Ent) := semDEC φDC φ₁ (semNOT φ₂ thereIsABathroom)

/-- The output of Figure 7, the first row of Table 3. -/
def j₇ : State World Ent :=
  (((init {w_u, w_0}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef

/-- A negated antecedent (Figure 7) makes its referent counterfactual, and no consistent extension
admits a veridical continuation. -/
theorem negated_run : init {w_u, w_0} ~[negated] j₇ := by
  refine ⟨(init {w_u, w_0}).updateProp φ₁ {w_u, w_0}, updateProp_mem_box _ _ ?_, ?_⟩
  · intro w hw
    simp only [init, State.updateProp_prop_self,
      State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
    refine ⟨((init {w_u, w_0}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b},
      updateProp_mem_box _ _ ?_, ?_⟩
    · show _ = _ᶜ
      ext w
      cases w <;> simp [State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
    · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
      refine ⟨_, ⟨_, updateIndiv_mem_relUpdate _ fun w ↦ ?_, rfl, fun w hw ↦ ?_⟩, rfl⟩
      · cases w <;> simp [bathroomRef, State.updateProp_prop_self]
      · simp only [State.updateIndiv_prop, State.updateProp_prop_self] at hw
        cases w <;> simp_all [bathroomRef, bathroom]

theorem negated_counterfactualIndiv : CounterfactualIndiv φDC υ j₇ := by
  intro w hw
  simp only [j₇, init, State.updateIndiv_prop,
    State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    State.updateProp_prop_self] at hw
  cases w <;> simp_all [j₇, bathroomRef]

theorem negated_isComplement : j₇ ∈ eqCompl φ₁ φ₂ := by
  show _ = _ᶜ
  ext w
  cases w <;> simp [j₇, State.updateProp_prop_self,
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

-- (41)
theorem negated_counterfactualProp {i j : State World Ent} (h : i ~[negated] j) :
    CounterfactualProp φDC φ₂ j := by
  obtain ⟨k, hk, hmax⟩ := h
  rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))] at hmax
  obtain ⟨m, hm, hmax⟩ := hmax
  rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax
  obtain ⟨hup, hc⟩ := mem_box_singleton.mp hm
  have hdec' : m ∈ incl φDC φ₁ := by
    have hdec := (mem_box_singleton.mp hk).2
    rw [incl, Set.mem_ofPred_eq, (fixes_randomAssign_of_ne (by decide)).prop_eq hup,
      (fixes_randomAssign_of_ne (by decide)).prop_eq hup]
    exact hdec
  rw [CounterfactualProp, (thereIsABathroom_fixes φDC φ₂).prop_eq hmax,
    (thereIsABathroom_fixes φ₂ φ₂).prop_eq hmax]
  exact counterfactualProp_of_mem_eqCompl hc hdec'

/-- No consistent extension of Figure 7 admits the veridical anaphor (30) (§3.4.2). -/
theorem counterfactual_veridical_impossible (j : State World Ent)
    (hDC : j.prop φDC = j₇.prop φDC) (hφ₂ : j.prop φ₂ = j₇.prop φ₂)
    (hdec : j ∈ incl φDC φ₃) (hsub : j ∈ incl φ₃ φ₂) : ¬ (j.prop φDC).Nonempty :=
  counterfactual_blocks_veridical j₇ j φDC φ₃ φ₂ hDC hφ₂ (negated_counterfactualProp negated_run)
    hdec hsub

/-- The last row of Table 3, with the prejacent's context empty and the dref nowhere defined,
is also an output of (41), since the printed maximization does not exclude it. -/
def jRow4 : State World Ent :=
  ((init Set.univ).updateProp φ₁ Set.univ).updateProp φ₂ ∅

theorem negated_row4 : init Set.univ ~[negated] jRow4 := by
  refine ⟨(init Set.univ).updateProp φ₁ Set.univ,
    updateProp_mem_box _ _ fun _ _ ↦ trivial, ?_⟩
  rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
  refine ⟨jRow4, updateProp_mem_box _ _ ?_, ?_⟩
  · show _ = _ᶜ
    simp [State.updateProp_prop_self,
      State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
  · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
    refine ⟨jRow4, ⟨jRow4, mem_relUpdate.mpr ⟨mem_randomAssign_indiv.mpr ⟨fun _ ↦ rfl,
      fun _ _ ↦ rfl⟩, fun w ↦ ?_⟩, rfl, fun w hw ↦ ?_⟩, rfl⟩
    · simp [jRow4, init, null, State.updateProp_prop_self]
    · simp [jRow4, State.updateProp_prop_self] at hw

-- Figure 7
theorem negated_max : init {w_u, w_0} ~[maxAt φ₂ negated] j₇ := by
  refine mem_maxAt_prop.mpr ⟨negated_run, fun k hk hlt ↦ ?_⟩
  obtain ⟨k₁, ⟨_, _⟩, hmax⟩ := hk
  rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))] at hmax
  obtain ⟨k₂, ⟨_, _⟩, hmax₂⟩ := hmax
  rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)] at hmax₂
  have hsub := (thereIsABathroom_output hmax₂).2
  refine hlt.2 (fun w hw ↦ ?_)
  have := hsub hw
  simp only [j₇, State.updateIndiv_prop, State.updateProp_prop_self]
  exact this

/-! ### Double negation (43), Figure 8 -/

/-- *It's not the case that there isn't a bathroom.* -/
def doubleNeg : Update (State World Ent) :=
  semDEC φDC φ₁ (semNOT φ₂ (semNOT φ₃ thereIsABathroom))

/-- The output of Figure 8. -/
def j₈ : State World Ent :=
  ((((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0}).updateProp φ₃
    {w_bu, w_b}).updateIndiv υ bathroomRef

theorem doubleNeg_run : init {w_bu, w_b} ~[doubleNeg] j₈ := by
  refine ⟨(init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}, updateProp_mem_box _ _ ?_, ?_⟩
  · intro w hw
    simp only [init, State.updateProp_prop_self,
      State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide)
      (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _)))]
    refine ⟨((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0},
      updateProp_mem_box _ _ ?_, ?_⟩
    · show _ = _ᶜ
      ext w
      cases w <;> simp [State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
    · rw [maxAt_eq_of_fixes (semNOT_fixes φ₂ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨(((init {w_bu, w_b}).updateProp φ₁ {w_bu, w_b}).updateProp φ₂ {w_u, w_0}).updateProp
        φ₃ {w_bu, w_b}, updateProp_mem_box _ _ ?_, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [State.updateProp_prop_self,
          State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
      · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, updateIndiv_mem_relUpdate _ fun w ↦ ?_, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, State.updateProp_prop_self]
        · simp only [State.updateIndiv_prop, State.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]

theorem doubleNeg_prop_eq : j₈.prop φ₁ = j₈.prop φ₃ := by
  simp [j₈, State.updateIndiv_prop, State.updateProp_prop_self,
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]

theorem doubleNeg_veridicalIndiv : VeridicalIndiv φDC υ j₈ := by
  intro w hw
  simp only [j₈, init, State.updateIndiv_prop,
    State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
    State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁),
    State.updateProp_prop_self] at hw
  cases w <;> simp_all [j₈, bathroomRef]

-- §4.1
theorem doubleNeg_accessible : Accessible φ₃ υ φDC j₈ :=
  ⟨fun w hw ↦ by
    simp only [j₈, State.updateIndiv_prop, State.updateProp_prop_self] at hw
    cases w <;> simp_all [j₈, bathroomRef],
   ⟨w_bu, by simp [j₈, init, State.updateIndiv_prop,
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-! ### The bathroom disjunction (44), Figure 9 -/

/-- *Either there isn't a bathroom, or it's upstairs.* -/
def bathDisj : Update (State World Ent) :=
  semDEC φDC φ₁ (semOR φ₂ φ₃ (semNOT φ₄ thereIsABathroom) itIsUpstairs)

/-- The output of Figure 9. -/
def j₉ : State World Ent :=
  (((((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂ {w_u, w_0}).updateProp
    φ₃ {w_bu}).updateProp φ₄ {w_bu, w_b}).updateIndiv υ bathroomRef

theorem bathDisj_run : init {w_bu, w_u, w_0} ~[bathDisj] j₉ := by
  refine ⟨(init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0},
    updateProp_mem_box _ _ ?_, ?_⟩
  · intro w hw
    simp only [init, State.updateProp_prop_self,
      State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)] at hw ⊢
    exact hw
  · rw [maxAt_eq_of_fixes (semOR_fixes φ₁ (by decide) (by decide)
      (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _)) (itIsUpstairs_fixes _ _))]
    refine ⟨j₉, ⟨(((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂
      {w_u, w_0}).updateProp φ₃ {w_bu}, mem_box_insert_of_mem (updateProp_mem_randomAssign _ _ _)
      (updateProp_mem_box _ _ ?_), ?_⟩, ?_⟩
    · show _ = _ ∪ _
      ext w
      cases w <;> simp [State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
        State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂),
        State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
    · rw [maxAt_eq_of_fixes (semNOT_fixes φ₂ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨((((init {w_bu, w_u, w_0}).updateProp φ₁ {w_bu, w_u, w_0}).updateProp φ₂
        {w_u, w_0}).updateProp φ₃ {w_bu}).updateProp φ₄ {w_bu, w_b},
        updateProp_mem_box _ _ ?_, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [State.updateProp_prop_self,
          State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₄),
          State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃)]
      · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, updateIndiv_mem_relUpdate _ fun w ↦ ?_, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, State.updateProp_prop_self]
        · simp only [State.updateIndiv_prop, State.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]
    · rw [maxAt_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₉, State.updateIndiv_prop, State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)] at hw
      cases w <;> simp_all [j₉, bathroomRef, upstairs]

theorem bathDisj_union : j₉.prop φ₁ = j₉.prop φ₂ ∪ j₉.prop φ₃ := by
  ext w
  cases w <;> simp [j₉, State.updateIndiv_prop, State.updateProp_prop_self,
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₄),
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂),
    State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₄),
    State.updateProp_prop_of_ne _ (by decide : φ₂ ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)]

-- §4.2
theorem bathDisj_accessible : Accessible φ₃ υ φDC j₉ :=
  ⟨fun w hw ↦ by
    simp only [j₉, State.updateIndiv_prop, State.updateProp_prop_self,
      State.updateProp_prop_of_ne _ (by decide : φ₃ ≠ φ₄)] at hw
    cases w <;> simp_all [j₉, bathroomRef],
   ⟨w_bu, by simp [j₉, init, State.updateIndiv_prop,
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₄),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₃),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₂),
     State.updateProp_prop_of_ne _ (by decide : φDC ≠ φ₁)]⟩⟩

/-! ### Disagreement (47) and (48), Figure 10 -/

/-- Speaker `A` says *There isn't a bathroom* and speaker `B` says *It is upstairs*. -/
def disagree : Update (State World Ent) :=
  semDEC φDCA φ₁ (semNOT φ₂ thereIsABathroom) ○ semDEC φDCB φ₃ itIsUpstairs

/-- The output of Figure 10. -/
def j₁₀ : State World Ent :=
  ((((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b}).updateIndiv υ
    bathroomRef).updateProp φ₃ {w_bu}

theorem disagree_run : init₂ {w_u, w_0} {w_bu} ~[disagree] j₁₀ := by
  refine ⟨(((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂
    {w_bu, w_b}).updateIndiv υ bathroomRef, ?_, ?_⟩
  · refine ⟨(init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}, updateProp_mem_box _ _ ?_,
      ?_⟩
    · intro w hw
      simp only [init₂, State.updateProp_prop_self,
        State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
        State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB)] at hw ⊢
      exact hw
    · rw [maxAt_eq_of_fixes (semNOT_fixes φ₁ (by decide) (thereIsABathroom_fixes _ _))]
      refine ⟨((init₂ {w_u, w_0} {w_bu}).updateProp φ₁ {w_u, w_0}).updateProp φ₂ {w_bu, w_b},
        updateProp_mem_box _ _ ?_, ?_⟩
      · show _ = _ᶜ
        ext w
        cases w <;> simp [State.updateProp_prop_self,
          State.updateProp_prop_of_ne _ (by decide : φ₁ ≠ φ₂)]
      · rw [maxAt_eq_of_fixes (thereIsABathroom_fixes _ _)]
        refine ⟨_, ⟨_, updateIndiv_mem_relUpdate _ fun w ↦ ?_, rfl, fun w hw ↦ ?_⟩, rfl⟩
        · cases w <;> simp [bathroomRef, State.updateProp_prop_self]
        · simp only [State.updateIndiv_prop, State.updateProp_prop_self] at hw
          cases w <;> simp_all [bathroomRef, bathroom]
  · refine ⟨j₁₀, updateProp_mem_box _ _ ?_, ?_⟩
    · intro w hw
      simp only [init₂, State.updateProp_prop_self, State.updateIndiv_prop,
        State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
        State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
        State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁)] at hw ⊢
      exact hw
    · rw [maxAt_eq_of_fixes (itIsUpstairs_fixes _ _)]
      refine ⟨rfl, fun w hw ↦ ?_⟩
      simp only [j₁₀, State.updateProp_prop_self] at hw
      cases w <;> simp_all [j₁₀, bathroomRef, upstairs]

theorem disagree_counterfactual_A : CounterfactualIndiv φDCA υ j₁₀ := by
  intro w hw
  simp only [j₁₀, init₂, State.updateIndiv_prop,
    State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
    State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
    State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB),
    State.updateProp_prop_self] at hw
  cases w <;> simp_all [j₁₀, bathroomRef]

theorem disagree_veridical_B : VeridicalIndiv φDCB υ j₁₀ := by
  intro w hw
  simp only [j₁₀, init₂, State.updateIndiv_prop,
    State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
    State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
    State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁),
    State.updateProp_prop_self] at hw
  cases w <;> simp_all [j₁₀, bathroomRef]

-- §4.3
theorem disagree_accessible :
    (j₁₀.prop φDCA).Nonempty ∧ Accessible φ₃ υ φDCB j₁₀ :=
  ⟨⟨w_u, by simp [j₁₀, init₂, State.updateIndiv_prop,
     State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₃),
     State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₂),
     State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φ₁),
     State.updateProp_prop_of_ne _ (by decide : φDCA ≠ φDCB)]⟩,
   fun w hw ↦ by
     simp only [j₁₀, State.updateProp_prop_self] at hw
     cases w <;> simp_all [j₁₀, bathroomRef],
   ⟨w_bu, by simp [j₁₀, init₂, State.updateIndiv_prop,
     State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₃),
     State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₂),
     State.updateProp_prop_of_ne _ (by decide : φDCB ≠ φ₁)]⟩⟩

end Hofmann2025
