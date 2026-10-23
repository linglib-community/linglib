module

public import Linglib.Semantics.Dynamic.FileChange
public import Studies.Karttunen1973
public import Linglib.Data.Examples.Heim1983

/-!
# Heim (1983): On the Projection Problem for Presuppositions

This file formalizes Heim's paper. A context admits a sentence when the sentence's context
change potential is defined on it, a sentence presupposes what every admitting context
entails (12), and the heritage properties that Karttunen and Peters stipulate for *if*
and *not* are read off the potentials (14) and (15): a context admits "If A, B" iff it admits
A and its update by A admits B, and negation is a hole. The King example (1)–(3) is worked as
the paper does (`king_admits_iff`), and the two ways of accommodating a presupposition under
negation are (16)'s global and local readings (`globalNeg_entails`, `localNeg_entails`); a
preference for the global one recaptures Gazdar's cancellation under the threat of
inconsistency (`cancellation_only_under_inconsistency`). Contexts as sets of sequence–world
pairs (§3) carry the potentials for open sentences and for *every* (21): under the novelty
stipulation (22), "Every nation cherishes its king" presupposes that every nation has a king
(`every_nation_presupposes`), a presupposition in the restrictor projects universally (23),
and an indefinite's presupposition projects universally unless it is accommodated in the
course of the update (§3.3).

## Implementation notes

The propositional part (§2) uses the substrate's partial context change potentials over a
type of worlds: `ofTrivalent` for a sentence with a trivalent meaning, `cond` for (14), `neg`
for (15), and `Admits` for definedness, so that the heritage properties are the substrate's
`admits_cond` and `admits_neg`. Presupposing a proposition `p` (12) is the substrate's
`Presupposes` of the update `ofTrivalent fun w ↦ ofProp (p w)` (`presupposes_ofProp_iff`). The
file part (§3) uses the same potentials over pairs of a sequence `ℕ → M` and a world, with
`atom`, `atomP`, and `every` stated here as (19)–(21) and entailment by a context read as
inclusion. The paper gives no potential for *no* (24), so that sentence is a row only.

A file whose membership depends only on the cards in `X` is, restricted to those cards, a
state of the substrate uniform at `X` (`File.toState`), and on such files the paper's
clauses are the file change potentials of Heim's dissertation read on that stratum: the atom is
the merge with the atom's proposition state (`toState_atom`), negation by set difference is
non-subsistence (`neg_toState`), and (21) is rule (III) of the dissertation
(`toState_everyClause`). The novelty stipulation (22) is the file's independence of the
card (`novelIn_iff_determinedBy`).

## References

* [heim-1983]
* [heim-1982]
* [karttunen-1973]
* [karttunen-1974-presupposition]
* [karttunen-peters-1979]
* [gazdar-1979]
* [lewis-1979]
-/

@[expose] public section

namespace Heim1983

open DynamicSemantics PartialUpdate CCP.Partial Presupposition

/-! ### Admittance and presupposition (§2.1–§2.2) -/

section Propositional

variable {W : Type*}

/-- `S` is true in `w` with respect to `c` (13) iff `c` admits `S` and the context `c` updated
    by `S` is true in `w`. -/
def TrueWrt (φ : CCP.Partial W) (c : Set W) (w : W) : Prop := ∃ h : φ.Admits c, w ∈ (φ c).get h

theorem trueWrt_ofTrivalent {p : W → SignType} {c : Set W} {w : W} (hw : w ∈ c)
    (h : (ofTrivalent p).Admits c) : TrueWrt (ofTrivalent p) c w ↔ p w = 1 :=
  ⟨fun ⟨_, hm⟩ => hm.2, fun hq => ⟨h, hw, hq⟩⟩

variable (king son bald : W → Prop)

open Classical in
/-- *The king has a son* (1) presupposes a king and asserts that he has a son. -/
noncomputable def kingHasSon : W → SignType :=
  {w | king w}.indicator fun w ↦ SignType.ofProp (son w)

open Classical in
/-- *The king's son is bald* (2) presupposes a king with a son. -/
noncomputable def kingsSonBald : W → SignType :=
  {w | king w ∧ son w}.indicator fun w ↦ SignType.ofProp (bald w)

/-- (3) "If the king has a son, the king's son is bald", by (14). -/
noncomputable def ifKingHasSon : CCP.Partial W :=
  cond (ofTrivalent (kingHasSon king son)) (ofTrivalent (kingsSonBald king son bald))

variable {king son bald}

/-- A context admits (3) iff it entails there is a king, since it must admit (1) and its update by
(1) admits (2) (§2.1). -/
theorem king_admits_iff (c : Set W) :
    (ifKingHasSon king son bald).Admits c ↔ ∀ w ∈ c, king w := by
  simp [ifKingHasSon, admits_cond_ofTrivalent_iff, admits_ofTrivalent, Set.subset_def,
    kingHasSon, kingsSonBald, Connective.localContext]

open Classical in
/-- (3) presupposes that there is a king, which (1) presupposes in its antecedent. -/
theorem king_presupposes :
    Presupposes (ifKingHasSon king son bald) (ofTrivalent fun w ↦ SignType.ofProp (king w)) :=
  (presupposes_ofProp_iff _ _).2 fun c h ↦ (king_admits_iff c).1 h

open Classical in
/-- (3) does not presuppose that the king has a son, as soon as some world has a sonless
    king. -/
theorem not_presupposes_son (h : ∃ w, king w ∧ ¬ son w) :
    ¬ Presupposes (ifKingHasSon king son bald) (ofTrivalent fun w ↦ SignType.ofProp (son w)) := by
  rw [presupposes_ofProp_iff]
  obtain ⟨w, hk, hs⟩ := h
  intro hp
  exact hs (hp {w} ((king_admits_iff _).2 fun _ hv => hv ▸ hk) w rfl)

/-! ### Accommodation (§2.3) -/

variable (φ : CCP.Partial W) (p : Set W)

/-- The global option (A) evaluates *Not S* in a context that does not admit `S` by amending
    the context to `c ∩ p` and computing `(c ∩ p) + Not S`. -/
def globalNeg : CCP.Partial W := fun c => neg φ (c ∩ p)

/-- The local option (B) amends the context to `c ∩ p` only to compute `(c ∩ p) + S`, and
    subtracts that from `c` itself. -/
def localNeg : CCP.Partial W := fun c => (φ (c ∩ p)).map (c \ ·)

variable {φ p}

theorem globalNeg_admits {c : Set W} (h : φ.Admits (c ∩ p)) : (globalNeg φ p).Admits c := h

theorem localNeg_admits {c : Set W} (h : φ.Admits (c ∩ p)) : (localNeg φ p).Admits c := h

/-- The global option's result entails the accommodated presupposition, so (16) read in
    isolation has France with a king. -/
theorem globalNeg_entails {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ⊆ p :=
  fun _ hw ↦ (isEliminative_neg φ _ _ h hw).2

/-- Under the local option, (16) entails only that France has no king or he did not come. -/
theorem localNeg_entails {came : W → Prop} [DecidablePred came] {c c' : Set W}
    (h : c' ∈ localNeg (ofTrivalent (p.indicator fun w ↦ SignType.ofProp (came w))) p c) :
    c' = {w ∈ c | w ∉ p ∨ ¬ came w} := by
  obtain ⟨t, ht, rfl⟩ := (Part.mem_map_iff _).1 h
  obtain ⟨-, rfl⟩ := (mem_ofTrivalent _ _ _).1 ht
  ext w
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Trivalent.indicator_apply_eq_one_iff, SignType.ofProp_eq_one_iff]
  tauto

theorem globalNeg_disjoint {c c' : Set W} (h : c' ∈ globalNeg φ p c) : c' ∩ pᶜ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hw, hn⟩ => hn (globalNeg_entails h hw)

open scoped Classical in
/-- The paper's ceteris paribus preference for global over local accommodation takes the
    global result `g` continued by `k`, unless `k` is inconsistent with it, and otherwise the
    local result `l` continued by `k`. -/
noncomputable def preferGlobal (k g l : Set W) : Set W :=
  if (g ∩ k).Nonempty then g ∩ k else l ∩ k

/-- In (16) in isolation nothing contradicts the global result, so the preferred reading
    entails that France has a king. -/
theorem preferGlobal_univ_subset {c g : Set W} (l : Set W) (hg : g ∈ globalNeg φ p c)
    (hne : g.Nonempty) : preferGlobal Set.univ g l ⊆ p := by
  rw [preferGlobal, Set.inter_univ, ite_eq_left hne]
  exact globalNeg_entails hg

/-- When (16) is continued with *because France doesn't have a king*, the continuation is
    inconsistent with the global result, so the preferred reading is the local one. -/
theorem preferGlobal_compl {c g : Set W} (l : Set W) (hg : g ∈ globalNeg φ p c) :
    preferGlobal pᶜ g l = l ∩ pᶜ := by
  rw [preferGlobal, globalNeg_disjoint hg, ite_eq_right Set.not_nonempty_empty]

/-- The preference recaptures [gazdar-1979]'s assumption that presupposition cancellation
    occurs only under the threat of inconsistency. A preferred reading that does not entail
    the presupposition comes from a global result inconsistent with the continuation. -/
theorem cancellation_only_under_inconsistency {c g l k : Set W} (hg : g ∈ globalNeg φ p c)
    (h : ¬ preferGlobal k g l ⊆ p) : g ∩ k = ∅ := by
  rw [preferGlobal] at h
  split_ifs at h with hk
  · exact absurd (Set.inter_subset_left.trans (globalNeg_entails hg)) h
  · exact Set.not_nonempty_iff_eq_empty.1 hk

end Propositional

/-! ### Files: contexts as sets of sequence–world pairs (§3) -/

section Files

variable {M W : Type*}

/-- A file is a set of pairs of a sequence of individuals and a world (§3.1). -/
abbrev File (M W : Type*) := Set ((ℕ → M) × W)

/-- The proposition a file determines (17). -/
def File.prop (c : File M W) : Set W := {w | ∃ g, (g, w) ∈ c}

/-- A file is true in a world when some sequence fits it there (18). -/
def File.TrueIn (c : File M W) (w : W) : Prop := ∃ g, (g, w) ∈ c

/-- The update by an open sentence `P xᵢ` without presupposition (19). -/
def atom (P : M → W → Prop) (i : ℕ) : CCP.Partial ((ℕ → M) × W) :=
  ofTotal fun c => {gw ∈ c | P (gw.1 i) gw.2}

/-- An open sentence `P xᵢ` presupposing `pre xᵢ` is admitted by a file iff every pair in it
    satisfies the presupposition at the `i`-th member (20). -/
def atomP (pre P : M → W → Prop) (i : ℕ) : CCP.Partial ((ℕ → M) × W) :=
  fun c => ⟨∀ gw ∈ c, pre (gw.1 i) gw.2, fun _ => {gw ∈ c | P (gw.1 i) gw.2}⟩

/-- The clause of (21) keeps the pairs of `c` each of whose `i`-variants in `cA` survives in
    `cAB`. -/
def File.everyClause (i : ℕ) (c cA cAB : File M W) : File M W :=
  {gw ∈ c | ∀ a, (Function.update gw.1 i a, gw.2) ∈ cA → (Function.update gw.1 i a, gw.2) ∈ cAB}

/-- `c + Every xᵢ, A, B` (21) keeps the pairs of `c` each of whose `i`-variants in `c + A`
    survives in `c + A + B`, and is defined iff `c + A` and `c + A + B` are. -/
def every (i : ℕ) (A B : CCP.Partial ((ℕ → M) × W)) : CCP.Partial ((ℕ → M) × W) :=
  fun c ↦ (A c).bind fun cA ↦ (B cA).map fun cAB ↦ File.everyClause i c cA cAB

/-- The file does not yet distinguish the `i`-th member of a sequence (22), the lexical
    novelty requirement of *every* and of an indefinite indexed `i`. -/
def File.NovelIn (c : File M W) (i : ℕ) : Prop :=
  ∀ g w a, (g, w) ∈ c ↔ (Function.update g i a, w) ∈ c

theorem atom_admits (P : M → W → Prop) (i : ℕ) (c : File M W) : (atom P i).Admits c := trivial

theorem atomP_admits_iff (pre P : M → W → Prop) (i : ℕ) (c : File M W) :
    (atomP pre P i).Admits c ↔ ∀ gw ∈ c, pre (gw.1 i) gw.2 := Iff.rfl

theorem every_admits_iff (i : ℕ) (A B : CCP.Partial ((ℕ → M) × W)) (c : File M W) :
    (every i A B).Admits c ↔ ∃ h : A.Admits c, B.Admits ((A c).get h) :=
  Iff.rfl

/-- With restrictor `A xᵢ` and scope presupposing `pre xᵢ`, every pair of the file satisfying `A`
must satisfy `pre` ((ii) of §3.2). -/
theorem every_atom_admits_iff (i : ℕ) (A pre B : M → W → Prop) (c : File M W) :
    (every i (atom A i) (atomP pre B i)).Admits c ↔
      ∀ gw ∈ c, A (gw.1 i) gw.2 → pre (gw.1 i) gw.2 :=
  ⟨fun ⟨_, h⟩ gw hgw hA => h gw ⟨hgw, hA⟩, fun h => ⟨trivial, fun gw hgw => h gw hgw.1 hgw.2⟩⟩

/-- For a novel index, (7) presupposes under (22) that every nation has a king. -/
theorem every_nation_presupposes (i : ℕ) (nation hasKing cherishes : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (every i (atom nation i) (atomP hasKing cherishes i)).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, nation a w → hasKing a w := by
  rw [every_atom_admits_iff]
  constructor
  · rintro h w ⟨g, hg⟩ a hn
    have := h (Function.update g i a, w) ((hc g w a).1 hg)
    simp only [Function.update_self] at this
    exact this hn
  · rintro h ⟨g, w⟩ hgw hn
    exact h w ⟨g, hgw⟩ _ hn

/-- A presupposition in the restrictor projects universally (23), contrary to the prediction of
[karttunen-peters-1979]. -/
theorem every_restrictor_presupposes (i : ℕ) (hasKing serves rewarded : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (every i (atomP hasKing serves i) (atom rewarded i)).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, hasKing a w := by
  constructor
  · rintro ⟨h, -⟩ w ⟨g, hg⟩ a
    simpa using h (Function.update g i a, w) ((hc g w a).1 hg)
  · rintro h
    exact ⟨fun gw hgw => h gw.2 ⟨gw.1, hgw⟩ _, trivial⟩

/-! ### Files as uniform states

A file whose membership depends only on the cards in `X` is, restricted to `X`, an
information state uniform at `X`, and on such files the clauses (19), (15) and (21) are the
file change potentials of [heim-1982] on that stratum. -/

/-- The point of a sequence–world pair at the cards `X` restricts the sequence to `X`. -/
noncomputable def File.pointAt (X : Set ℕ) (gw : (ℕ → M) × W) : Possibility W ℕ (Flat M) :=
  ((Possibility.domainEquiv X).symm (gw.2, fun i ↦ gw.1 i.1)).1

variable {X Y : Set ℕ} {g g' : ℕ → M} {w w' : W} {i : ℕ} {c c' cA cAB : File M W}

@[simp] theorem File.pointAt_world (gw : (ℕ → M) × W) : (File.pointAt X gw).world = gw.2 := rfl

@[simp] theorem File.domain_pointAt (gw : (ℕ → M) × W) : (File.pointAt X gw).domain = X :=
  ((Possibility.domainEquiv X).symm _).2

open Classical in
theorem File.pointAt_assignment (gw : (ℕ → M) × W) (j : ℕ) :
    (File.pointAt X gw).assignment j = if j ∈ X then ↑(gw.1 j) else ⊥ := by
  by_cases hj : j ∈ X <;> simp [File.pointAt, Possibility.domainEquiv, hj]

theorem File.pointAt_assignment_eq_coe_iff {m : M} :
    (File.pointAt X (g, w)).assignment i = ↑m ↔ i ∈ X ∧ g i = m := by
  classical
  rw [File.pointAt_assignment]
  split_ifs with hi <;> simp [hi, Flat.coe_inj]

theorem File.pointAt_eq_coe (hj : i ∈ X) :
    (File.pointAt X (g, w)).assignment i = ↑(g i) :=
  File.pointAt_assignment_eq_coe_iff.mpr ⟨hj, rfl⟩

theorem File.pointAt_le_pointAt :
    File.pointAt X (g, w) ≤ File.pointAt Y (g', w') ↔ X ⊆ Y ∧ w = w' ∧ Set.EqOn g g' X := by
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨fun j hj ↦ ?_, hw, fun j hj ↦ ?_⟩ <;>
    · have hx : (File.pointAt X (g, w)).assignment j = ↑(g j) :=
        File.pointAt_assignment_eq_coe_iff.mpr ⟨hj, rfl⟩
      have := File.pointAt_assignment_eq_coe_iff.mp (Flat.coe_le_iff.1 (hx ▸ h j))
      first | exact this.1 | exact this.2.symm
  · rintro ⟨hXY, rfl, heq⟩
    refine ⟨rfl, fun j ↦ ?_⟩
    classical
    by_cases hj : j ∈ X
    · rw [File.pointAt_eq_coe hj]
      exact Flat.coe_le_iff.2 (File.pointAt_assignment_eq_coe_iff.mpr ⟨hXY hj, (heq hj).symm⟩)
    · rw [File.pointAt_assignment, ite_eq_right hj]
      exact bot_le

theorem File.pointAt_eq_pointAt :
    File.pointAt X (g, w) = File.pointAt X (g', w') ↔ w = w' ∧ Set.EqOn g g' X :=
  ⟨fun h ↦ ((File.pointAt_le_pointAt.mp h.le).2),
   fun ⟨hw, heq⟩ ↦ le_antisymm (File.pointAt_le_pointAt.mpr ⟨le_rfl, hw, heq⟩)
    (File.pointAt_le_pointAt.mpr ⟨le_rfl, hw.symm, heq.symm⟩)⟩

/-- The state of a file at the cards `X`. -/
def File.toState (X : Set ℕ) (c : File M W) : State W ℕ M := File.pointAt X '' c

theorem File.mem_toState {p : Possibility W ℕ (Flat M)} :
    p ∈ c.toState X ↔ ∃ gw ∈ c, File.pointAt X gw = p := Iff.rfl

theorem File.uniformAt_toState : State.UniformAt X (c.toState X) := by
  rintro _ ⟨gw, -, rfl⟩
  exact File.domain_pointAt gw

/-- A file is determined by the cards `X` when its membership depends only on them. -/
def File.DeterminedBy (X : Set ℕ) (c : File M W) : Prop :=
  ∀ ⦃g g' : ℕ → M⦄ ⦃w : W⦄, Set.EqOn g g' X → (g, w) ∈ c → (g', w) ∈ c

theorem File.DeterminedBy.mono (h : X ⊆ Y) (hc : c.DeterminedBy X) : c.DeterminedBy Y :=
  fun _ _ _ heq ↦ hc (heq.mono h)

/-- (22) is independence of the card, the file not distinguishing `i` iff it is determined
    by the other cards. -/
theorem File.novelIn_iff_determinedBy : c.NovelIn i ↔ c.DeterminedBy {i}ᶜ := by
  constructor
  · intro h g g' w heq hg
    have : g' = Function.update g i (g' i) := funext fun j ↦ by
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact (heq hj).symm
    exact this ▸ (h g w (g' i)).mp hg
  · intro h g w a
    have heq : Set.EqOn g (Function.update g i a) {i}ᶜ := fun j hj ↦
      (Function.update_of_ne hj a g).symm
    exact ⟨h heq, h heq.symm⟩

theorem File.pointAt_mem_toState (hc : c.DeterminedBy X) (gw : (ℕ → M) × W) :
    File.pointAt X gw ∈ c.toState X ↔ gw ∈ c := by
  obtain ⟨g, w⟩ := gw
  refine ⟨fun ⟨⟨g', w'⟩, h, heq⟩ ↦ ?_, fun h ↦ ⟨_, h, rfl⟩⟩
  obtain ⟨rfl, heq'⟩ := File.pointAt_eq_pointAt.mp heq
  exact hc heq' h

theorem File.toState_mul_stratum (hc : c.DeterminedBy X) :
    c.toState X * State.stratum Y = c.toState (X ∪ Y) := by
  ext r
  rw [State.mem_mul_stratum]
  constructor
  · rintro ⟨_, ⟨⟨g, w⟩, hg, rfl⟩, hpr, hdom⟩
    rw [File.domain_pointAt] at hdom
    classical
    let g' : ℕ → M := fun j ↦ if h : r.assignment j ≠ ⊥ then (r.assignment j).get h else g j
    have hval : ∀ j ∈ X, r.assignment j = ↑(g j) := fun j hj ↦
      Flat.coe_le_iff.1 (File.pointAt_eq_coe (w := w) hj ▸ hpr.2 j)
    refine ⟨(g', w), hc (fun j hj ↦ ?_) hg, ?_⟩
    · simp [g', hval j hj]
    · refine Possibility.ext hpr.1 (funext fun j ↦ ?_)
      by_cases hj : j ∈ X ∪ Y
      · have hd : r.assignment j ≠ ⊥ := show j ∈ r.domain by rw [hdom]; exact hj
        rw [File.pointAt_eq_coe hj]
        simp [g', hd]
      · have hd : r.assignment j = ⊥ := by
          by_contra hne
          exact hj (hdom ▸ hne)
        rw [File.pointAt_assignment, ite_eq_right hj, hd]
  · rintro ⟨⟨g, w⟩, hg, rfl⟩
    exact ⟨File.pointAt X (g, w), ⟨_, hg, rfl⟩,
      File.pointAt_le_pointAt.mpr ⟨Set.subset_union_left, rfl, fun _ _ ↦ rfl⟩,
      by rw [File.domain_pointAt, File.domain_pointAt]⟩

theorem File.toState_sep (hi : i ∈ X) (P : M → W → Prop) :
    File.toState X {gw ∈ c | P (gw.1 i) gw.2} =
      {r ∈ c.toState X | ∃ m : M, r.assignment i = ↑m ∧ P m r.world} := by
  ext r
  constructor
  · rintro ⟨⟨g, w⟩, ⟨hg, hP⟩, rfl⟩
    exact ⟨⟨_, hg, rfl⟩, g i, File.pointAt_eq_coe hi, hP⟩
  · rintro ⟨⟨⟨g, w⟩, hg, rfl⟩, m, hm, hP⟩
    obtain ⟨-, rfl⟩ := File.pointAt_assignment_eq_coe_iff.mp hm
    exact ⟨(g, w), ⟨hg, hP⟩, rfl⟩

/-- Under (19), the atomic rule of [heim-1982], updating a file merges its state with the atom's
proposition state. -/
theorem File.toState_atom (hc : c.DeterminedBy X) (P : M → W → Prop) :
    File.toState (insert i X) {gw ∈ c | P (gw.1 i) gw.2} =
      c.toState X * State.atomAt i fun w m ↦ P m w := by
  rw [State.mul_atomAt, File.toState_mul_stratum hc, Set.union_singleton,
    File.toState_sep (Set.mem_insert i X)]

theorem File.toState_sdiff (hc' : c'.DeterminedBy X) :
    (c \ c').toState X = c.toState X \ c'.toState X := by
  ext r
  constructor
  · rintro ⟨gw, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨⟨gw, h₁, rfl⟩, fun h ↦ h₂ ((File.pointAt_mem_toState hc' gw).mp h)⟩
  · rintro ⟨⟨gw, h₁, rfl⟩, h₂⟩
    exact ⟨gw, ⟨h₁, fun h ↦ h₂ ((File.pointAt_mem_toState hc' gw).mpr h)⟩, rfl⟩

/-- The non-subsistence negation (15) of [heim-1982] takes a determined file's state to the set
difference of the files. -/
theorem File.neg_toState {φ : FCP W ℕ M} (hφ : φ (c.toState X) = Part.some (c'.toState X))
    (hc' : c'.DeterminedBy X) :
    FCP.neg φ (c.toState X) = Part.some ((c \ c').toState X) := by
  rw [FCP.neg, hφ, Part.map_some, File.toState_sdiff hc']
  refine congrArg Part.some (Set.ext fun p ↦ and_congr_right fun hp ↦ ?_)
  exact not_congr (File.uniformAt_toState (c := c').mem_lowerClosure (File.uniformAt_toState p hp))

/-- On determined files, (21), rule (III) of [heim-1982], keeps the points each of whose extensions
in `F + A` extends into `(F + A) + B`. -/
theorem File.toState_everyClause (hi : i ∉ X) (hA : cA.DeterminedBy (insert i X))
    (hB : cAB.DeterminedBy (insert i X)) :
    (File.everyClause i c cA cAB).toState X =
      {p ∈ c.toState X | ∀ q ∈ cA.toState (insert i X), p ≤ q →
        ∃ r ∈ cAB.toState (insert i X), q ≤ r} := by
  ext p
  constructor
  · rintro ⟨⟨g, w⟩, ⟨hg, hall⟩, rfl⟩
    refine ⟨⟨_, hg, rfl⟩, ?_⟩
    rintro q ⟨⟨g', w'⟩, hq, rfl⟩ hle
    obtain ⟨-, rfl, heq⟩ := File.pointAt_le_pointAt.mp hle
    have heq' : Set.EqOn (Function.update g i (g' i)) g' (insert i X) := fun j hj ↦ by
      rcases hj with rfl | hj
      · simp
      · rw [Function.update_of_ne fun h : j = i ↦ hi (h ▸ hj)]; exact heq hj
    exact ⟨_, ⟨_, hB heq' (hall _ (hA heq'.symm hq)), rfl⟩, le_rfl⟩
  · rintro ⟨⟨⟨g, w⟩, hg, rfl⟩, hall⟩
    refine ⟨(g, w), ⟨hg, fun a ha ↦ ?_⟩, rfl⟩
    obtain ⟨_, ⟨⟨g'', w''⟩, hr, rfl⟩, hqr⟩ := hall _ ⟨_, ha, rfl⟩
      (File.pointAt_le_pointAt.mpr ⟨Set.subset_insert i X, rfl, fun j hj ↦
        (Function.update_of_ne (fun h : j = i ↦ hi (h ▸ hj)) a g).symm⟩)
    obtain ⟨-, rfl, heq⟩ := File.pointAt_le_pointAt.mp hqr
    exact hB heq.symm hr

/-! ### Indefinites (§3.3) -/

/-- *A fat man was pushing his bicycle* (26)–(27) is the sequence of two open sentences, the
    second presupposing that `xᵢ` has a bicycle. -/
def fatManBicycle (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial ((ℕ → M) × W) :=
  seq (atom fatMan i) (atomP hasBicycle pushing i)

/-- Without accommodation, (25) carries the universal presupposition that every fat man had
    a bicycle by (22), which is prima facie too strong. -/
theorem fatManBicycle_admits_iff (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    {c : File M W} (hc : c.NovelIn i) :
    (fatManBicycle i fatMan hasBicycle pushing).Admits c ↔
      ∀ w ∈ c.prop, ∀ a, fatMan a w → hasBicycle a w := by
  constructor
  · rintro ⟨_, h⟩ w ⟨g, hg⟩ a hf
    have := h (Function.update g i a, w) ⟨(hc g w a).1 hg, by simpa using hf⟩
    simpa using this
  · rintro h
    exact ⟨trivial, fun gw hgw => h gw.2 ⟨gw.1, hgw.1⟩ _ hgw.2⟩

/-- Accommodation in the course of the update amends `c + "xᵢ is a fat man"` with
    *xᵢ has a bicycle* before the second sentence is evaluated. -/
def fatManBicycleAcc (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop) :
    CCP.Partial ((ℕ → M) × W) :=
  fun c => atomP hasBicycle pushing i {gw ∈ c | fatMan (gw.1 i) gw.2 ∧ hasBicycle (gw.1 i) gw.2}

theorem fatManBicycleAcc_admits (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    (c : File M W) : (fatManBicycleAcc i fatMan hasBicycle pushing).Admits c :=
  fun _ hgw => hgw.2.2

theorem fatManBicycleAcc_entails (i : ℕ) (fatMan hasBicycle pushing : M → W → Prop)
    {c c' : File M W} (h : c' ∈ fatManBicycleAcc i fatMan hasBicycle pushing c) :
    ∀ gw ∈ c', fatMan (gw.1 i) gw.2 ∧ hasBicycle (gw.1 i) gw.2 ∧ pushing (gw.1 i) gw.2 := by
  rw [fatManBicycleAcc, atomP, Part.mem_mk_iff] at h
  obtain ⟨-, rfl⟩ := h
  exact fun gw hgw => ⟨hgw.1.2.1, hgw.1.2.2, hgw.2⟩

theorem fatManBicycleAcc_not_universal :
    ∃ (c' : File Bool Unit), c' ∈ fatManBicycleAcc 0 (fun _ _ => True) (fun a _ => a = true)
        (fun _ _ => True) Set.univ ∧ c'.TrueIn () ∧
      ¬ ∀ w ∈ c'.prop, ∀ a : Bool, a = true := by
  refine ⟨_, Part.get_mem (fatManBicycleAcc_admits _ _ _ _ _), ⟨fun _ => true, ?_⟩, ?_⟩
  · exact ⟨⟨Set.mem_univ _, trivial, rfl⟩, trivial⟩
  · intro h
    exact Bool.false_ne_true (h () ⟨fun _ => true, ⟨Set.mem_univ _, trivial, rfl⟩, trivial⟩ false)

end Files

/-! ### The conjunction filter of Karttunen (1973) -/

/-- Admittance of the sequenced update is [karttunen-1974-presupposition]'s satisfaction condition
for conjunction, equivalent to [karttunen-1973]'s filter relativized to the context ((8)–(14)). -/
theorem admits_seq_iff_conj {W : Type*} (c : Set W) (p q : W → SignType) :
    (seq (ofTrivalent p) (ofTrivalent q)).Admits c ↔
      ∀ C ∈ (Karttunen1973.conj (fun P C ↦ c ∩ P ⊆ C) (.ofTrivalent p)
        (.ofTrivalent q)).log, c ⊆ C := by
  rw [admits_seq_ofTrivalent_iff, admits_ofTrivalent]
  simp only [Karttunen1973.mem_log_conj, Karttunen1973.Presupposing.ofTrivalent, Writer.log_mk,
    List.mem_singleton]
  constructor
  · rintro ⟨hp, hq⟩ C (rfl | ⟨rfl, hf⟩)
    · exact hp
    · exact absurd (fun w ⟨hw, ha, _⟩ ↦ hq ⟨hw, ha⟩) hf
  · intro h
    have hp : c ⊆ Function.support p := h _ (.inl rfl)
    refine ⟨hp, fun w ⟨hw, ha⟩ ↦ ?_⟩
    by_cases hf : c ∩ (Karttunen1973.Presupposing.ofTrivalent p).truth ⊆ Function.support q
    · exact hf ⟨hw, ha, fun t ht ↦ List.mem_singleton.1 ht ▸ hp hw⟩
    · exact h _ (.inr ⟨rfl, hf⟩) hw

end Heim1983
