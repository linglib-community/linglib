module

public import Linglib.Logic.Team.BSML.NaturalDeduction
public import Linglib.Logic.Team.BSML.Characteristic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Completeness of natural deduction for BSML

The natural deduction system `Derives` of `NaturalDeduction.lean` is complete: a consequence that
holds on every model is derivable from finitely many premises. The proof follows the normal-form
strategy of Aloni, Anttila and Yang. The world types of `Characteristic.lean` are the worlds of one
universal model, and each type's Hintikka formula holds exactly at it there. A set of
types `T` has the strong Hintikka formula `θ_T`, the disjunction of the formulas `χ_τ ∧ NE`, which
derives every formula the team `T` supports. Conversely, the `⊥NE`-translation rules split every
formula into the cases `θ_T` for the teams supporting it.

## Main definitions

* `univModel e`: the model whose worlds are the world types.
* `Splits A S`: `A` splits into the cases `S`.

## Main results

* `derives_of_support`: a strong Hintikka formula derives what its team supports.
* `derives_bigDisj_hintikka`: every world has a type of each depth.
* `derives_bigDisj_realize`: a classical formula derives the disjunction of its types.
* `splits_fill`: every formula splits into the strong Hintikka formulas of its teams.
* `completeness`, `derives_iff`: completeness for finite premise sets.

## Implementation notes

Successor sets are finite, so completeness holds for finite premise sets only. No team supports
`{◇pₙ | n ∈ ℕ} ∪ {□¬(pᵢ ∧ pⱼ) | i ≠ j} ∪ {NE}`, yet each of its finite subsets is satisfiable.
The first sections derive general rules of the system.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
-/

@[expose] public section

namespace BSML

open ModalLogic (KripkeModel)

variable {Atom : Type*} [Inhabited Atom] {Γ : Set (Formula Atom)} {φ ψ χ α : Formula Atom}
  {L L' : List (Formula Atom)}

/-! ### Derived propositional rules -/

theorem Derives.disjE' (h : Γ ⊢ .disj φ ψ) (h₁ : {φ} ⊢ χ) (h₂ : {ψ} ⊢ χ) : Γ ⊢ χ := by
  simpa using h.disjE (Δ₁ := ∅) (Δ₂ := ∅) (by simp) (by simp) (by simpa using h₁)
    (by simpa using h₂)

theorem Derives.disjMonLeft (h : Γ ⊢ .disj φ ψ) (h' : {φ} ⊢ χ) : Γ ⊢ .disj χ ψ :=
  (h.disjCom.disjMon' h').disjCom

theorem Derives.of_disj_self (h : Γ ⊢ .disj φ φ) : Γ ⊢ φ := h.disjE' (.single _) (.single _)

theorem Derives.disj_assoc (h : Γ ⊢ .disj (.disj φ ψ) χ) : Γ ⊢ .disj φ (.disj ψ χ) :=
  ((h.disjCom.disjMon' (Derives.single _).disjCom).disjAss.disjCom).disjMon'
    (Derives.single _).disjCom

theorem Derives.disj_left_comm (h : Γ ⊢ .disj φ (.disj ψ χ)) : Γ ⊢ .disj ψ (.disj φ χ) :=
  (h.disjAss.disjMonLeft (Derives.single _).disjCom).disj_assoc

theorem Derives.disj_falsum (h : Γ ⊢ .disj φ .falsum) : Γ ⊢ φ := h.disjCom.falsumE

theorem Derives.of_falsum (h : Γ ⊢ .falsum) (hα : α.NEFree) : Γ ⊢ α := by
  have h₀ := Derives.single (Formula.falsum (Atom := Atom))
  have h₁ := Derives.negE (α := .atom default) (β := α) trivial hα h₀.conjE₁ h₀.conjE₂
  exact h.trans (by simpa using h₁)

theorem derives_em (hα : α.NEFree) : Γ ⊢ .disj α (.neg α) := by
  have h₀ := Derives.single (Formula.neg (.disj α (.neg α)))
  have h₁ := Derives.negE (α := .neg α) (β := .falsum) hα Formula.neFree_falsum
    h₀.dmDisjE.conjE₁ h₀.dmDisjE.conjE₂
  have h₂ : (∅ : Set (Formula Atom)) ⊢ .neg (.neg (.disj α (.neg α))) :=
    .negI (α := .neg (.disj α (.neg α))) ⟨hα, hα⟩ (by simp) (by simpa using h₁)
  exact h₂.dneE.mono (Set.empty_subset _)

theorem derives_verum : Γ ⊢ (verum : Formula Atom) := derives_em trivial

theorem Derives.bigConj_of_forall (h : ∀ x ∈ L, Γ ⊢ x) : Γ ⊢ bigConj L := by
  induction L with
  | nil => exact derives_verum
  | cons x r ih => exact (h x (by simp)).conj (ih fun y hy ↦ h y (by simp [hy]))

theorem Derives.of_bigConj (h : Γ ⊢ bigConj L) {x : Formula Atom} (hx : x ∈ L) : Γ ⊢ x := by
  induction L with
  | nil => simp at hx
  | cons y r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    exacts [h.conjE₁, ih h.conjE₂ hx]

theorem Derives.bigDisj_elim (h : Γ ⊢ bigDisj L) (hL : ∀ x ∈ L, {x} ⊢ χ)
    (h₀ : {.falsum} ⊢ χ) : Γ ⊢ χ := by
  induction L generalizing Γ with
  | nil => exact h.trans h₀
  | cons x r ih =>
    exact h.disjE' (hL x (by simp)) (ih (.single _) fun y hy ↦ hL y (by simp [hy]))

theorem Derives.bigDisj_of_mem (hL : ∀ y ∈ L, y.NEFree) {x : Formula Atom} (hx : x ∈ L)
    (h : Γ ⊢ x) : Γ ⊢ bigDisj L := by
  induction L with
  | nil => simp at hx
  | cons y r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.disjI (neFree_bigDisj r fun z hz ↦ hL z (by simp [hz]))
    · exact (ih (fun z hz ↦ hL z (by simp [hz])) hx).disjI (hL y (by simp)) |>.disjCom

theorem Derives.bigDisj_mono (hL' : ∀ y ∈ L', y.NEFree) (h : Γ ⊢ bigDisj L)
    (hsub : ∀ x ∈ L, {x} ⊢ bigDisj L') : Γ ⊢ bigDisj L' :=
  h.bigDisj_elim hsub ((Derives.single _).of_falsum (neFree_bigDisj L' hL'))

theorem Derives.bigDisj_expand {x : Formula Atom} (hx : x ∈ L) (h : Γ ⊢ bigDisj L) :
    Γ ⊢ .disj x (bigDisj L) := by
  induction L generalizing Γ with
  | nil => simp at hx
  | cons y r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (h.disjMonLeft (Derives.single _).disjW).disj_assoc
    · exact (h.disjMon' (ih hx (.single _))).disj_left_comm

theorem Derives.bigDisj_absorb {x : Formula Atom} (hx : x ∈ L) (h : Γ ⊢ .disj x (bigDisj L)) :
    Γ ⊢ bigDisj L := by
  induction L generalizing Γ with
  | nil => simp at hx
  | cons y r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.disjAss.disjMonLeft (Derives.single _).of_disj_self
    · exact h.disj_left_comm.disjMon' (ih hx (.single _))

theorem Derives.bigDisj_merge (hsub : ∀ x ∈ L, x ∈ L') (h : Γ ⊢ .disj (bigDisj L) (bigDisj L')) :
    Γ ⊢ bigDisj L' := by
  induction L generalizing Γ with
  | nil => exact h.falsumE
  | cons x r ih =>
    exact (h.disj_assoc.disjMon' (ih (fun y hy ↦ hsub y (by simp [hy])) (.single _))).bigDisj_absorb
      (hsub x (by simp))

theorem Derives.bigDisj_spread (hsub : ∀ x ∈ L', x ∈ L) (h : Γ ⊢ bigDisj L) :
    Γ ⊢ .disj (bigDisj L') (bigDisj L) := by
  induction L' generalizing Γ with
  | nil => exact (h.disjI Formula.neFree_falsum).disjCom
  | cons x r ih =>
    exact ((ih (fun y hy ↦ hsub y (by simp [hy])) h).disjMon'
      ((Derives.single _).bigDisj_expand (hsub x (by simp)))).disj_left_comm.disjAss

theorem Derives.bigDisj_perm (hperm : ∀ x, x ∈ L ↔ x ∈ L') (h : Γ ⊢ bigDisj L) :
    Γ ⊢ bigDisj L' :=
  (h.bigDisj_spread fun x hx ↦ (hperm x).mpr hx).disjCom.bigDisj_merge fun x hx ↦ (hperm x).mp hx

theorem Derives.bigDisj_append (h : Γ ⊢ bigDisj (L ++ L')) :
    Γ ⊢ .disj (bigDisj L) (bigDisj L') := by
  induction L generalizing Γ with
  | nil => exact (h.disjI Formula.neFree_falsum).disjCom
  | cons x r ih => exact (h.disjMon' (ih (.single _))).disjAss

theorem Derives.bigDisj_of_append (h : Γ ⊢ .disj (bigDisj L) (bigDisj L')) :
    Γ ⊢ bigDisj (L ++ L') := by
  induction L generalizing Γ with
  | nil => exact h.falsumE
  | cons x r ih => exact h.disj_assoc.disjMon' (ih (.single _))

/-! ### Modal combinations -/

theorem Derives.possJoin' (h₁ : Γ ⊢ .poss φ) (h₂ : Γ ⊢ .poss ψ) : Γ ⊢ .poss (.disj φ ψ) :=
  Set.union_self Γ ▸ h₁.possJoin h₂

theorem Derives.necMap (h : Γ ⊢ Formula.nec φ) (h' : {φ} ⊢ ψ) : Γ ⊢ Formula.nec ψ :=
  .necMon [φ] (by simpa using h') (by simpa using h)

theorem poss_falsum_derives : {.poss .falsum} ⊢ (.falsum : Formula Atom) := by
  have hneg : {.poss .falsum} ⊢ .neg (.poss (.falsum : Formula Atom)) :=
    .interI (.necMon [] (by simpa using derives_neg_falsum) (by simp))
  have h := Derives.negE (α := .poss .falsum) (β := .falsum) Formula.neFree_falsum
    Formula.neFree_falsum (.single _) hneg
  simpa using h

theorem Derives.poss_of_falsum (h : Γ ⊢ .falsum) : Γ ⊢ .poss φ := by
  have h₁ : Γ ⊢ .poss .falsum := h.of_falsum Formula.neFree_falsum
  have h₂ := Derives.possNeTrs (ψ := .falsum) .hole trivial h₁
  have hl : {.poss (.conj .falsum .ne)} ⊢ .poss φ := .possMon (strongFalsum_derives φ) (.single _)
  have hr : {.poss (.conj .falsum .falsum)} ⊢ (.falsum : Formula Atom) :=
    ((Derives.single _).possMon' (Derives.single _).conjE₁).trans poss_falsum_derives
  exact ((h₂.disjMonLeft hl).disjMon' hr).disj_falsum

theorem Derives.nec_of_falsum (h : Γ ⊢ .falsum) : Γ ⊢ Formula.nec φ := by
  have h₁ : Γ ⊢ Formula.nec .falsum := h.of_falsum Formula.neFree_falsum
  have h₂ := Set.union_self Γ ▸ h₁.necPossJoin (h.poss_of_falsum (φ := φ))
  exact h₂.necMap (Derives.single _).falsumE

/-- With `◇φ`, a necessary disjunction `□(φ ∨ ψ)` conjoins `NE` to `φ`
    ([aloni-anttila-yang-2024] Lemma 4.22 (ii), right to left). -/
theorem Derives.nec_disj_conj_ne (h : Γ ⊢ Formula.nec (.disj φ ψ)) (h' : Γ ⊢ .poss φ) :
    Γ ⊢ Formula.nec (.disj (.conj φ .ne) ψ) := by
  have h₁ := Set.union_self Γ ▸ h.necPossJoin (h'.trans poss_derives_poss_conj_ne)
  refine h₁.necMap ?_
  have hY : {.disj φ (.conj φ .ne)} ⊢ .conj φ .ne :=
    ((Derives.single _).disjMon' (Derives.single _).conjE₁).of_disj_self.conj
      disj_conj_ne_derives_conj_ne.conjE₂
  exact ((Derives.single _).disj_assoc.disjMon' (Derives.single _).disjCom).disjAss.disjMonLeft hY

theorem Derives.poss_bigDisj (hL : L ≠ []) (h : ∀ x ∈ L, Γ ⊢ .poss x) : Γ ⊢ .poss (bigDisj L) := by
  induction L with
  | nil => exact absurd rfl hL
  | cons x r ih =>
    rcases r with _ | ⟨y, r⟩
    · exact (h x (by simp)).possMon' ((Derives.single _).disjI Formula.neFree_falsum)
    · exact (h x (by simp)).possJoin' (ih (by simp) fun z hz ↦ h z (by simp [hz]))

private theorem Derives.nec_tag {A : List (Formula Atom)} :
    ∀ {B : List (Formula Atom)}, (∀ x ∈ B, Γ ⊢ .poss x) →
      Γ ⊢ Formula.nec (.disj (bigDisj A) (bigDisj B)) →
      Γ ⊢ Formula.nec (.disj (bigDisj A) (bigDisjNE B))
  | [], _, h => h
  | x :: r, hB, h => by
    have h₁ := (h.necMap (Derives.single _).disj_left_comm).nec_disj_conj_ne (hB x (by simp))
    have h₂ := h₁.necMap (((Derives.single _).disjAss.disjMonLeft
      (((Derives.single _).disjCom.disjMon' ((Derives.single _).disjI
        Formula.neFree_falsum)).bigDisj_of_append (L := A) (L' := [.conj x .ne]))))
    have h₃ := Derives.nec_tag (A := A ++ [.conj x .ne]) (fun y hy ↦ hB y (by simp [hy])) h₂
    have h₄ : {bigDisj (A ++ [.conj x .ne])} ⊢ .disj (bigDisj A) (.conj x .ne) :=
      (Derives.single _).bigDisj_append.disjMon'
        (show {bigDisj [Formula.conj x .ne]} ⊢ .conj x .ne from (Derives.single _).disj_falsum)
    exact h₃.necMap ((Derives.single _).disjMonLeft h₄).disj_assoc

/-- With the possibility of each disjunct, a necessary disjunction conjoins `NE` to every
    disjunct ([aloni-anttila-yang-2024] Lemma 4.23 (ii), right to left). -/
theorem Derives.nec_bigDisjNE (h : Γ ⊢ Formula.nec (bigDisj L)) (hL : ∀ x ∈ L, Γ ⊢ .poss x) :
    Γ ⊢ Formula.nec (bigDisjNE L) :=
  ((Derives.nec_tag (A := []) hL (h.necMap ((Derives.single _).disjI
    Formula.neFree_falsum).disjCom)).necMap (Derives.single _).falsumE)

theorem Derives.of_bigDisjNE (hL : ∀ x ∈ L, x.NEFree) (h : Γ ⊢ bigDisjNE L) : Γ ⊢ bigDisj L :=
  h.bigDisj_mono hL fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (Derives.single _).conjE₁.bigDisj_of_mem hL hx

theorem Derives.ne_of_bigDisjNE (hL : L ≠ []) (h : Γ ⊢ bigDisjNE L) : Γ ⊢ .ne := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil L hL
  exact ((h.bigDisj_expand (List.mem_map_of_mem hx)).disjCom.trans
    disj_conj_ne_derives_conj_ne).conjE₂

theorem Derives.poss_of_poss_bigDisjNE (h : Γ ⊢ .poss (bigDisjNE L)) {x : Formula Atom}
    (hx : x ∈ L) : Γ ⊢ .poss x :=
  (h.possMon' ((Derives.single _).bigDisj_expand
    (List.mem_map_of_mem (f := fun x ↦ Formula.conj x .ne) hx)).disjCom).possSep

theorem Derives.poss_of_nec_bigDisjNE (hL : L ≠ []) (h : Γ ⊢ Formula.nec (bigDisjNE L))
    {x : Formula Atom} (hx : x ∈ L) : Γ ⊢ .poss x :=
  (h.necMap ((Derives.single _).conj ((Derives.single _).ne_of_bigDisjNE hL))).necInst
    |>.poss_of_poss_bigDisjNE hx

/-! ### The universal model -/

variable {n : ℕ} (e : Fin n → Atom)

/-- In the universal model each type is a world, whose successors are its successor types. -/
noncomputable def univModel : KripkeModel (Σ k, WorldType n k) Atom where
  access
    | ⟨0, _⟩ => ∅
    | ⟨k + 1, τ⟩ => τ.2.image fun σ ↦ ⟨k, σ⟩
  val p w := ∃ i, e i = p ∧ w.2.val i = true

noncomputable instance : DecidableRel (univModel e).val := fun _ _ ↦ Classical.dec _

/-- `world k τ` is the type `τ` as a world of the universal model. -/
def WorldType.world (k : ℕ) (τ : WorldType n k) : Σ k, WorldType n k := ⟨k, τ⟩

theorem WorldType.world_injective (k : ℕ) : Function.Injective (world (n := n) k) := fun _ _ h ↦ by
  simpa [world] using h

open WorldType

variable {e}

omit [Inhabited Atom] in
theorem univModel_val (he : Function.Injective e) (i : Fin n) (w : Σ k, WorldType n k) :
    (univModel e).val (e i) w ↔ w.2.val i = true := by
  simp [univModel, he.eq_iff]

omit [Inhabited Atom] in
theorem univModel_access_succ {k : ℕ} (τ : WorldType n (k + 1)) :
    (univModel e).access (world (k + 1) τ) = τ.2.image (world k) := rfl

omit [Inhabited Atom] in
theorem worldType_univModel (he : Function.Injective e) :
    ∀ (k : ℕ) (τ : WorldType n k), worldType e (univModel e) k (world k τ) = τ
  | 0, a => funext fun i ↦ by simp [worldType, univModel_val he, world, WorldType.val]
  | k + 1, τ => by
    rw [worldType, univModel_access_succ, Finset.image_image]
    refine Prod.ext (funext fun i ↦ by simp [univModel_val he, world, WorldType.val]) ?_
    simp only [Function.comp_def, worldType_univModel he k, Finset.image_id']

theorem realize_hintikka (he : Function.Injective e) (k : ℕ) (τ τ' : WorldType n k) :
    Realize (univModel e) (hintikka e k τ) (world k τ') ↔ τ' = τ := by
  rw [realize_hintikka_iff, worldType_univModel he]

/-! ### Teams of types -/

/-- The atoms occurring in a formula all lie in `S`. -/
def Formula.AtomsIn (S : Set Atom) : Formula Atom → Prop
  | .atom p => p ∈ S
  | .ne => True
  | .neg φ | .poss φ => φ.AtomsIn S
  | .conj φ ψ | .disj φ ψ => φ.AtomsIn S ∧ ψ.AtomsIn S

omit [Inhabited Atom] in
theorem support_image_iff {k : ℕ} {φ : Formula Atom} (hφ : φ.NEFree) (T : Finset (WorldType n k)) :
    support (univModel e) φ (T.image (world k)) ↔ ∀ τ ∈ T, Realize (univModel e) φ (world k τ) := by
  simp [support_iff_forall_realize hφ]

theorem support_strongHintikka (he : Function.Injective e) {k : ℕ} (T T' : Finset (WorldType n k)) :
    support (univModel e) (strongHintikka e T) (T'.image (world k)) ↔ T' = T := by
  rw [support_strongHintikka_iff, Finset.image_image, Function.comp_def]
  simp only [worldType_univModel he, Finset.image_id']

/-! ### Derivations from Hintikka formulas -/

theorem hintikka_derives_literals {k : ℕ} (τ : WorldType n k) :
    {hintikka e k τ} ⊢ literals e τ.val := by
  cases k with
  | zero => exact .single _
  | succ k => exact (Derives.single _).conjE₁

theorem literals_derives_literal (a : Fin n → Bool) (i : Fin n) :
    {literals e a} ⊢ literal e i (a i) :=
  (Derives.single _).of_bigConj (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

theorem hintikka_derives_poss {k : ℕ} (τ : WorldType n (k + 1)) {σ : WorldType n k} (hσ : σ ∈ τ.2) :
    {hintikka e (k + 1) τ} ⊢ .poss (hintikka e k σ) :=
  (Derives.single _).conjE₂.conjE₁.of_bigConj
    (List.mem_map.mpr ⟨σ, Finset.mem_toList.mpr hσ, rfl⟩)

theorem hintikka_derives_nec {k : ℕ} (τ : WorldType n (k + 1)) :
    {hintikka e (k + 1) τ} ⊢ Formula.nec (strongHintikka e τ.2) :=
  (Derives.single _).conjE₂.conjE₂.nec_bigDisjNE fun x hx ↦ by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
    exact hintikka_derives_poss τ (Finset.mem_toList.mp hσ)

theorem Derives.strongHintikka_elim {k : ℕ} {T : Finset (WorldType n k)} {Γ : Set (Formula Atom)}
    {χ : Formula Atom} (h : Γ ⊢ strongHintikka e T)
    (hT : ∀ τ ∈ T, {.conj (hintikka e k τ) .ne} ⊢ χ) (h₀ : {.falsum} ⊢ χ) : Γ ⊢ χ :=
  h.bigDisj_elim (fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hy
    exact hT τ (Finset.mem_toList.mp hτ)) h₀

private theorem mem_tag_union {k : ℕ} (T₁ T₂ : Finset (WorldType n k)) (x : Formula Atom) :
    x ∈ (((T₁ ∪ T₂).toList.map (hintikka e k)).map fun y ↦ Formula.conj y .ne) ↔
      x ∈ ((T₁.toList.map (hintikka e k)).map fun y ↦ Formula.conj y .ne) ++
        ((T₂.toList.map (hintikka e k)).map fun y ↦ Formula.conj y .ne) := by
  simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_union, List.mem_append,
    or_and_right, exists_or]

theorem strongHintikka_union_derives {k : ℕ} (T₁ T₂ : Finset (WorldType n k)) :
    {strongHintikka e (T₁ ∪ T₂)} ⊢ .disj (strongHintikka e T₁) (strongHintikka e T₂) :=
  ((Derives.single (strongHintikka e (T₁ ∪ T₂))).bigDisj_perm
    (mem_tag_union T₁ T₂)).bigDisj_append

theorem disj_strongHintikka_derives {k : ℕ} (T₁ T₂ : Finset (WorldType n k)) :
    {.disj (strongHintikka e T₁) (strongHintikka e T₂)} ⊢ strongHintikka e (T₁ ∪ T₂) :=
  (Derives.single (Formula.disj (strongHintikka e T₁) (strongHintikka e T₂))).bigDisj_of_append
    |>.bigDisj_perm fun x ↦ (mem_tag_union T₁ T₂ x).symm

theorem Derives.poss_strongHintikka {k : ℕ} {U : Finset (WorldType n k)} {Γ : Set (Formula Atom)}
    (hU : U.Nonempty) (h : ∀ σ ∈ U, Γ ⊢ .poss (hintikka e k σ)) : Γ ⊢ .poss (strongHintikka e U) :=
  Derives.poss_bigDisj (by simpa [Finset.nonempty_iff_ne_empty] using hU) fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hy
    exact (h σ (Finset.mem_toList.mp hσ)).trans poss_derives_poss_conj_ne

/-! ### Strong Hintikka formulas derive what their teams support -/

/-- A strong Hintikka formula derives every formula its team supports, and the negation of every
    formula its team anti-supports. -/
theorem derives_of_support (he : Function.Injective e) :
    ∀ (φ : Formula Atom) {k : ℕ}, φ.modalDepth ≤ k → φ.AtomsIn (Set.range e) →
      ∀ T : Finset (WorldType n k),
        (support (univModel e) φ (T.image (world k)) → {strongHintikka e T} ⊢ φ) ∧
        (antiSupport (univModel e) φ (T.image (world k)) → {strongHintikka e T} ⊢ .neg φ)
  | .atom _, k, _, ⟨i, rfl⟩, T => by
    have hlit : ∀ τ : WorldType n k, {.conj (hintikka e k τ) .ne} ⊢ literal e i (τ.val i) := fun τ ↦
      (Derives.single _).conjE₁.trans
        ((hintikka_derives_literals τ).trans (literals_derives_literal _ i))
    refine ⟨fun h ↦ (Derives.single _).strongHintikka_elim (fun τ hτ ↦ ?_)
      ((Derives.single _).of_falsum trivial), fun h ↦ (Derives.single _).strongHintikka_elim
      (fun τ hτ ↦ ?_) ((Derives.single _).of_falsum trivial)⟩
    · have hv : τ.val i = true := by
        simpa [univModel_val he, world] using h (world k τ) (Finset.mem_image_of_mem _ hτ)
      simpa [literal, hv] using hlit τ
    · have hv : τ.val i = false := by
        simpa [univModel_val he, world] using h (world k τ) (Finset.mem_image_of_mem _ hτ)
      simpa [literal, hv] using hlit τ
  | .ne, k, _, _, T => by
    refine ⟨fun h ↦ (Derives.single _).ne_of_bigDisjNE ?_, fun h ↦ ?_⟩
    · obtain ⟨_, hw⟩ := h
      obtain ⟨τ, hτ, -⟩ := Finset.mem_image.mp hw
      simpa [Finset.toList_eq_nil] using Finset.ne_empty_of_mem hτ
    · obtain rfl : T = ∅ := Finset.image_eq_empty.mp h
      rw [strongHintikka_empty]
      exact (Derives.single _).negNeI
  | .neg ψ, k, hk, hA, T =>
    have ih := derives_of_support he ψ hk hA T
    ⟨ih.2, fun h ↦ (ih.1 h).dneI⟩
  | .conj ψ₁ ψ₂, k, hk, hA, T => by
    have ih₁ := derives_of_support he ψ₁ (max_le_iff.mp hk).1 hA.1
    have ih₂ := derives_of_support he ψ₂ (max_le_iff.mp hk).2 hA.2
    refine ⟨fun ⟨h₁, h₂⟩ ↦ ((ih₁ T).1 h₁).conj ((ih₂ T).1 h₂), ?_⟩
    rintro ⟨t₁, h₁, t₂, h₂, ht⟩
    obtain ⟨T₁, -, rfl⟩ := Finset.subset_image_iff.mp (ht ▸ Finset.subset_union_left)
    obtain ⟨T₂, -, rfl⟩ := Finset.subset_image_iff.mp (ht ▸ Finset.subset_union_right)
    rw [← Finset.image_union, (Finset.image_injective (WorldType.world_injective k)).eq_iff] at ht
    subst ht
    exact (((strongHintikka_union_derives T₁ T₂).disjMonLeft ((ih₁ T₁).2 h₁)).disjMon'
      ((ih₂ T₂).2 h₂)).dmConjI
  | .disj ψ₁ ψ₂, k, hk, hA, T => by
    have ih₁ := derives_of_support he ψ₁ (max_le_iff.mp hk).1 hA.1
    have ih₂ := derives_of_support he ψ₂ (max_le_iff.mp hk).2 hA.2
    refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ (((ih₁ T).2 h₁).conj ((ih₂ T).2 h₂)).dmDisjI⟩
    rintro ⟨t₁, h₁, t₂, h₂, ht⟩
    obtain ⟨T₁, -, rfl⟩ := Finset.subset_image_iff.mp (ht ▸ Finset.subset_union_left)
    obtain ⟨T₂, -, rfl⟩ := Finset.subset_image_iff.mp (ht ▸ Finset.subset_union_right)
    rw [← Finset.image_union, (Finset.image_injective (WorldType.world_injective k)).eq_iff] at ht
    subst ht
    exact ((strongHintikka_union_derives T₁ T₂).disjMonLeft ((ih₁ T₁).1 h₁)).disjMon'
      ((ih₂ T₂).1 h₂)
  | .poss ψ, 0, hk, _, _ => absurd hk (by simp [Formula.modalDepth])
  | .poss ψ, k + 1, hk, hA, T => by
    have ih := derives_of_support he ψ (k := k) (by simpa [Formula.modalDepth] using hk) hA
    refine ⟨fun h ↦ (Derives.single _).strongHintikka_elim (fun τ hτ ↦ ?_)
      (Derives.single _).poss_of_falsum, fun h ↦ (Derives.single _).strongHintikka_elim
      (fun τ hτ ↦ ?_) (Derives.single _).nec_of_falsum.interI⟩
    · obtain ⟨s, hs, hne, hψ⟩ := h (world (k + 1) τ) (Finset.mem_image_of_mem _ hτ)
      rw [univModel_access_succ] at hs
      obtain ⟨U, hU, rfl⟩ := Finset.subset_image_iff.mp hs
      refine ((Derives.single _).conjE₁.trans ?_).possMon' ((ih U).1 hψ)
      exact Derives.poss_strongHintikka (Finset.image_nonempty.mp hne) fun σ hσ ↦
        hintikka_derives_poss τ (hU hσ)
    · have hψ : antiSupport (univModel e) ψ (τ.2.image (world k)) :=
        h (world (k + 1) τ) (Finset.mem_image_of_mem _ hτ)
      exact (((Derives.single _).conjE₁.trans (hintikka_derives_nec τ)).necMap
        ((ih τ.2).2 hψ)).interI

/-! ### Exhaustiveness of the types -/

theorem Derives.conj_bigDisj {A : Formula Atom} (hA : A.NEFree) :
    ∀ {L : List (Formula Atom)} {Γ : Set (Formula Atom)}, Γ ⊢ .conj A (bigDisj L) →
      Γ ⊢ bigDisj (L.map (.conj A))
  | [], _, h => h.conjE₂
  | _ :: _, _, h =>
    (h.trans (conj_disj_derives_disj_conj hA)).disjMon' (Derives.conj_bigDisj hA (.single _))

theorem Derives.conj_comm (h : Γ ⊢ .conj φ ψ) : Γ ⊢ .conj ψ φ := h.conjE₂.conj h.conjE₁

private theorem derives_bigDisj_literals_aux (e : Fin n → Atom) (Γ : Set (Formula Atom)) :
    ∀ is : List (Fin n), Γ ⊢ bigDisj ((Finset.univ : Finset (Fin n → Bool)).toList.map
      fun a ↦ bigConj (is.map fun j ↦ literal e j (a j)))
  | [] => derives_verum.bigDisj_of_mem (fun x hx ↦ by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; exact neFree_verum)
      (List.mem_map.mpr ⟨fun _ ↦ true, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
  | i :: r => by
    have hcl : ∀ (a : Fin n → Bool) (is : List (Fin n)),
        (bigConj (is.map fun j ↦ literal e j (a j))).NEFree := fun a is ↦
      neFree_bigConj _ fun x hx ↦ by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact neFree_literal e j _
    refine (derives_bigDisj_literals_aux e Γ r).bigDisj_mono (fun x hx ↦ by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact hcl a _) fun x hx ↦ ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    have key : ∀ b : Bool, {.conj (bigConj (r.map fun j ↦ literal e j (a j))) (literal e i b)} ⊢
        bigDisj ((Finset.univ : Finset (Fin n → Bool)).toList.map
          fun a ↦ bigConj ((i :: r).map fun j ↦ literal e j (a j))) := fun b ↦ by
      have h₀ := Derives.single (Formula.conj (bigConj (r.map fun j ↦ literal e j (a j)))
        (literal e i b))
      refine (Derives.conj (by simpa using h₀.conjE₂) (Derives.bigConj_of_forall fun x hx ↦ ?_) :
          _ ⊢ bigConj ((i :: r).map fun j ↦ literal e j (Function.update a i b j))).bigDisj_of_mem
        (fun x hx ↦ by obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; exact hcl _ _)
        (List.mem_map.mpr ⟨Function.update a i b, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      by_cases hji : j = i
      · subst hji; simpa using h₀.conjE₂
      · simpa [Function.update_of_ne hji] using h₀.conjE₁.of_bigConj (List.mem_map_of_mem hj)
    refine (((Derives.single _).conj (derives_em (α := .atom (e i)) trivial)).trans
      (conj_disj_derives_disj_conj (hcl a r))).disjE' ?_ ?_
    · simpa [literal] using key true
    · simpa [literal] using key false

theorem derives_bigDisj_literals (e : Fin n → Atom) (Γ : Set (Formula Atom)) :
    Γ ⊢ bigDisj ((Finset.univ : Finset (Fin n → Bool)).toList.map (literals e)) :=
  derives_bigDisj_literals_aux e Γ (List.finRange n)

/-- `succLit e S σ` says whether `σ` is a successor type in `S`. -/
noncomputable def succLit (e : Fin n → Atom) {k : ℕ} (S : Finset (WorldType n k))
    (σ : WorldType n k) :
    Formula Atom :=
  if σ ∈ S then .poss (hintikka e k σ) else .neg (.poss (hintikka e k σ))

theorem neFree_succLit (e : Fin n → Atom) {k : ℕ} (S : Finset (WorldType n k)) (σ : WorldType n k) :
    (succLit e S σ).NEFree := by
  unfold succLit; split <;> exact neFree_hintikka e k σ

private theorem derives_bigDisj_succLit_aux (e : Fin n → Atom) {k : ℕ} (Γ : Set (Formula Atom)) :
    ∀ ss : List (WorldType n k),
      Γ ⊢ bigDisj ((Finset.univ : Finset (Finset (WorldType n k))).toList.map
      fun S ↦ bigConj (ss.map (succLit e S)))
  | [] => derives_verum.bigDisj_of_mem (fun x hx ↦ by
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; exact neFree_verum)
      (List.mem_map.mpr ⟨∅, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
  | σ :: r => by
    have hcl : ∀ S (ss : List (WorldType n k)), (bigConj (ss.map (succLit e S))).NEFree :=
      fun S ss ↦ neFree_bigConj _ fun x hx ↦ by
        obtain ⟨σ', -, rfl⟩ := List.mem_map.mp hx; exact neFree_succLit e S σ'
    refine (derives_bigDisj_succLit_aux e Γ r).bigDisj_mono (fun x hx ↦ by
      obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx; exact hcl S _) fun x hx ↦ ?_
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx
    have hsplit := ((Derives.single _).conj
      (derives_em (α := .poss (hintikka e k σ)) (neFree_hintikka e k σ))).trans
      (conj_disj_derives_disj_conj (hcl S r))
    have key : ∀ S' : Finset (WorldType n k), (∀ σ' ∈ r, σ' ≠ σ → (σ' ∈ S' ↔ σ' ∈ S)) →
        {.conj (bigConj (r.map (succLit e S))) (succLit e S' σ)} ⊢
          bigDisj ((Finset.univ : Finset (Finset (WorldType n k))).toList.map
            fun S ↦ bigConj ((σ :: r).map (succLit e S))) := fun S' hS' ↦ by
      refine (Derives.conj (Derives.single _).conjE₂ (Derives.bigConj_of_forall fun x hx ↦ ?_)
        : _ ⊢ bigConj ((σ :: r).map (succLit e S'))).bigDisj_of_mem (fun x hx ↦ by
          obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; exact hcl _ _)
        (List.mem_map.mpr ⟨S', Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
      obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp hx
      by_cases h : σ' = σ
      · subst h; exact (Derives.single _).conjE₂
      · have := (Derives.single (Formula.conj (bigConj (r.map (succLit e S)))
          (succLit e S' σ))).conjE₁.of_bigConj (List.mem_map_of_mem (f := succLit e S) hσ')
        simpa [succLit, hS' σ' hσ' h] using this
    refine hsplit.disjE' ?_ ?_
    · simpa [succLit] using key (insert σ S) fun σ' _ h ↦ by simp [h]
    · by_cases hσ : σ ∈ S
      · simpa [succLit, hσ] using key (S.erase σ) fun σ' _ h ↦ by simp [h]
      · simpa [succLit, hσ] using key S fun _ _ _ ↦ Iff.rfl

/-- `succPart e S` is the modal part of the Hintikka formula of a type with successor
    types `S`. -/
noncomputable def succPart (e : Fin n → Atom) {k : ℕ} (S : Finset (WorldType n k)) : Formula Atom :=
  .conj (bigConj (S.toList.map fun σ ↦ .poss (hintikka e k σ)))
    (Formula.nec (bigDisj (S.toList.map (hintikka e k))))

theorem neFree_succPart (e : Fin n → Atom) {k : ℕ} (S : Finset (WorldType n k)) :
    (succPart e S).NEFree :=
  ⟨neFree_bigConj _ fun x hx ↦ by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ,
   neFree_bigDisj _ fun x hx ↦ by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ⟩

theorem neFree_bigDisj_hintikka (e : Fin n → Atom) {k : ℕ} (L : List (WorldType n k)) :
    (bigDisj (L.map (hintikka e k))).NEFree :=
  neFree_bigDisj _ fun x hx ↦ by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ

/-- **Exhaustiveness.** Every world has some type of each depth. -/
theorem derives_bigDisj_hintikka (e : Fin n → Atom) :
    ∀ (k : ℕ) (Γ : Set (Formula Atom)),
      Γ ⊢ bigDisj ((Finset.univ : Finset (WorldType n k)).toList.map (hintikka e k))
  | 0, Γ => derives_bigDisj_literals e Γ
  | k + 1, Γ => by
    set all : List (WorldType n k) := (Finset.univ : Finset (WorldType n k)).toList
    have hM : ∀ S : Finset (WorldType n k), {bigConj (all.map (succLit e S))} ⊢ succPart e S := by
      intro S
      have hD : ∀ σ, {bigConj (all.map (succLit e S))} ⊢ succLit e S σ := fun σ ↦
        (Derives.single _).of_bigConj
          (List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ σ)))
      refine (Derives.bigConj_of_forall fun x hx ↦ ?_).conj ?_
      · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
        simpa [succLit, Finset.mem_toList.mp hσ] using hD σ
      · set N : Formula Atom := bigConj ((Finset.univ.filter (· ∉ S)).toList.map
          fun σ ↦ .neg (hintikka e k σ))
        have hN : N.NEFree := neFree_bigConj _ fun x hx ↦ by
          obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ
        refine .necMon [N, bigDisj (all.map (hintikka e k))] ?_ ?_
        · have h₁ : {δ | δ ∈ [N, bigDisj (all.map (hintikka e k))]} ⊢
              .conj N (bigDisj (all.map (hintikka e k))) :=
            (Derives.hyp (by simp)).conj (.hyp (by simp))
          refine (h₁.conj_bigDisj hN).bigDisj_mono (fun x hx ↦ by
            obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ) fun x hx ↦ ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hy
          by_cases hσ : σ ∈ S
          · exact (Derives.single _).conjE₂.bigDisj_of_mem (fun x hx ↦ by
              obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ)
              (List.mem_map_of_mem (Finset.mem_toList.mpr hσ))
          · have h₀ := Derives.single (Formula.conj N (hintikka e k σ))
            have := Derives.negE (α := hintikka e k σ) (β := bigDisj (S.toList.map (hintikka e k)))
              (neFree_hintikka e k σ) (neFree_bigDisj_hintikka e _) h₀.conjE₂
              (h₀.conjE₁.of_bigConj (List.mem_map_of_mem (Finset.mem_toList.mpr (by simpa))))
            simpa using this
        · intro δ hδ
          rcases List.mem_cons.mp hδ with rfl | hδ
          · refine Derives.necMon ((Finset.univ.filter (· ∉ S)).toList.map
              fun σ ↦ .neg (hintikka e k σ)) (Derives.bigConj_of_forall fun x hx ↦ .hyp hx)
              fun δ hδ ↦ ?_
            obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hδ
            have hσ : σ ∉ S := (Finset.mem_filter.mp (Finset.mem_toList.mp hσ)).2
            have h := hD σ
            simp only [succLit, hσ, ite_false] at h
            exact h.interE
          · rw [List.mem_singleton.mp hδ]
            exact .necMon [] (by simpa using derives_bigDisj_hintikka e k ∅) (by simp)
    have hSucc : Γ ⊢ bigDisj ((Finset.univ : Finset (Finset (WorldType n k))).toList.map
        (succPart e)) :=
      (derives_bigDisj_succLit_aux e Γ all).bigDisj_mono (fun x hx ↦ by
        obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx; exact neFree_succPart e S) fun x hx ↦ by
        obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx
        exact (hM S).bigDisj_of_mem (fun x hx ↦ by
          obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx; exact neFree_succPart e S)
          (List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ S)))
    have hcl : ∀ x ∈ (Finset.univ : Finset (WorldType n (k + 1))).toList.map (hintikka e (k + 1)),
        x.NEFree := fun x hx ↦ by
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e (k + 1) τ
    have h₁ := (hSucc.conj (derives_bigDisj_literals e Γ)).conj_bigDisj
      (neFree_bigDisj _ fun x hx ↦ by
        obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx; exact neFree_succPart e S)
    refine h₁.bigDisj_mono hcl fun x hx ↦ ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
    refine ((Derives.single _).conj_comm.conj_bigDisj (neFree_literals e a)).bigDisj_mono hcl
      fun x hx ↦ ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hy
    exact (Derives.single _).bigDisj_of_mem hcl
      (List.mem_map_of_mem (f := hintikka e (k + 1)) (Finset.mem_toList.mpr
        (Finset.mem_univ ((a, S) : WorldType n (k + 1)))))

/-! ### Classical normal forms -/

theorem Derives.of_conj_ne {β : Formula Atom} (hβ : β.NEFree) (h : {.conj φ .ne} ⊢ β) :
    {φ} ⊢ β := by
  simpa using Derives.neTrs (Δ₁ := ∅) (Δ₂ := ∅) (ψ := φ) (χ := β) .hole trivial (.single φ)
    (by simpa [Formula.Context.fill] using h)
    (by simpa [Formula.Context.fill] using
      (Derives.single (Formula.conj φ .falsum)).conjE₂.of_falsum hβ)

theorem strongHintikka_singleton {k : ℕ} (τ : WorldType n k) :
    {.conj (hintikka e k τ) .ne} ⊢ strongHintikka e {τ} := by
  simpa [strongHintikka, bigDisjNE, bigDisj] using
    (Derives.single (Formula.conj (hintikka e k τ) .ne)).disjI Formula.neFree_falsum

theorem hintikka_derives (he : Function.Injective e) {β : Formula Atom} (hβ : β.NEFree) {k : ℕ}
    (hk : β.modalDepth ≤ k) (hA : β.AtomsIn (Set.range e)) (τ : WorldType n k) :
    (Realize (univModel e) β (world k τ) → {hintikka e k τ} ⊢ β) ∧
      (¬ Realize (univModel e) β (world k τ) → {hintikka e k τ} ⊢ .neg β) := by
  have h := derives_of_support he β hk hA {τ}
  simp only [Finset.image_singleton] at h
  exact ⟨fun hr ↦ Derives.of_conj_ne hβ ((strongHintikka_singleton τ).trans
      (h.1 ((support_singleton_iff_realize hβ).mpr hr))),
    fun hr ↦ Derives.of_conj_ne hβ ((strongHintikka_singleton τ).trans
      (h.2 ((antiSupport_singleton_iff_not_realize hβ).mpr hr)))⟩

/-- **Classical normal form.** A classical formula derives the disjunction of the Hintikka
    formulas of the types at which it is true. -/
theorem derives_bigDisj_realize (he : Function.Injective e) {β : Formula Atom} (hβ : β.NEFree)
    {k : ℕ} (hk : β.modalDepth ≤ k) (hA : β.AtomsIn (Set.range e)) :
    {β} ⊢ bigDisj ((Finset.univ.filter fun τ ↦ Realize (univModel e) β (world k τ)).toList.map
      (hintikka e k)) := by
  refine (((Derives.single β).conj (derives_bigDisj_hintikka e k _)).conj_bigDisj hβ).bigDisj_mono
    (fun x hx ↦ by obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ)
    fun x hx ↦ ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hy
  by_cases hr : Realize (univModel e) β (world k τ)
  · exact (Derives.single _).conjE₂.bigDisj_of_mem (fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ)
      (List.mem_map_of_mem (Finset.mem_toList.mpr (by simpa using hr)))
  · have h₀ := Derives.single (Formula.conj β (hintikka e k τ))
    simpa using Derives.negE (β := bigDisj ((Finset.univ.filter fun τ ↦
      Realize (univModel e) β (world k τ)).toList.map (hintikka e k))) hβ
      (neFree_bigDisj_hintikka e _) h₀.conjE₁
      (h₀.conjE₂.trans ((hintikka_derives he hβ hk hA τ).2 hr))

/-! ### Splitting into cases -/

/-- `A` splits into the cases `S` when whatever follows from each case follows from `A`. -/
def Splits (A : Formula Atom) (S : Set (Formula Atom)) : Prop :=
  ∀ χ, (∀ σ ∈ S, {σ} ⊢ χ) → {A} ⊢ χ

theorem Splits.of_derives {A B : Formula Atom} (h : {A} ⊢ B) : Splits A {B} :=
  fun _ hχ ↦ h.trans (hχ B rfl)

theorem Splits.mono {A : Formula Atom} {S S' : Set (Formula Atom)} (h : Splits A S)
    (hS : S ⊆ S') : Splits A S' := fun χ hχ ↦ h χ fun σ hσ ↦ hχ σ (hS hσ)

theorem Splits.trans {A : Formula Atom} {S S' : Set (Formula Atom)} (h : Splits A S)
    (h' : ∀ σ ∈ S, Splits σ S') : Splits A S' := fun χ hχ ↦ h χ fun σ hσ ↦ h' σ hσ χ hχ

theorem Splits.of_derives_mem {A B : Formula Atom} {S : Set (Formula Atom)} (h : {A} ⊢ B)
    (hB : B ∈ S) : Splits A S := (Splits.of_derives h).mono (Set.singleton_subset_iff.mpr hB)

/-! ### Splittable contexts -/

namespace Formula.Context

/-- `C.comp D` places `D` in the hole of `C`. -/
def comp : Context Atom → Context Atom → Context Atom
  | hole, D => D
  | conjLeft C ψ, D => conjLeft (C.comp D) ψ
  | conjRight φ C, D => conjRight φ (C.comp D)
  | disjLeft C ψ, D => disjLeft (C.comp D) ψ
  | disjRight φ C, D => disjRight φ (C.comp D)
  | poss C, D => poss (C.comp D)
  | nec C, D => nec (C.comp D)

omit [Inhabited Atom] in
@[simp] theorem fill_comp (C D : Context Atom) (φ : Formula Atom) :
    (C.comp D).fill φ = C.fill (D.fill φ) := by
  induction C <;> simp_all [comp, fill]

omit [Inhabited Atom] in
theorem Distributive.comp {C D : Context Atom} (hC : C.Distributive) (hD : D.Distributive) :
    (C.comp D).Distributive := by
  induction C <;> simp_all [Context.comp, Distributive]

/-- A context is splittable when it is distributive below at most one modality at its top. -/
def Splittable : Context Atom → Prop
  | poss C | nec C => C.Distributive
  | C => C.Distributive

omit [Inhabited Atom] in
theorem Distributive.splittable {C : Context Atom} (hC : C.Distributive) : C.Splittable := by
  cases C <;> first | exact hC | exact hC.elim

omit [Inhabited Atom] in
theorem Splittable.comp {C D : Context Atom} (hC : C.Splittable) (hD : D.Distributive) :
    (C.comp D).Splittable := by
  cases C with
  | poss C => exact Distributive.comp (C := C) hC hD
  | nec C => exact Distributive.comp (C := C) hC hD
  | hole => exact hD.splittable
  | _ => exact (Distributive.comp hC hD).splittable

/-- A context with a modality on top adds the case of the empty team. -/
def extra : Context Atom → Set (Formula Atom)
  | poss _ | nec _ => {.falsum}
  | _ => ∅

theorem extra_comp {C D : Context Atom} (hD : D.Distributive) : (C.comp D).extra = C.extra := by
  cases C <;> try rfl
  cases D <;> first | rfl | exact hD.elim

end Formula.Context

open Formula.Context

theorem Splits.fill_split {C : Formula.Context Atom} (hC : C.Splittable) (ψ : Formula Atom) :
    Splits (C.fill ψ) {C.fill (.conj ψ .ne), C.fill (.conj ψ .falsum)} := fun χ hχ ↦ by
  have h₁ := hχ _ (Set.mem_insert _ _)
  have h₂ := hχ _ (Set.mem_insert_of_mem _ rfl)
  cases C with
  | poss C => exact (Derives.possNeTrs C hC (.single _)).disjE' h₁ h₂
  | nec C => exact (Derives.necNeTrs C hC (.single _)).disjE' h₁ h₂
  | _ => simpa using Derives.neTrs (Δ₁ := ∅) (Δ₂ := ∅) _ hC (.single _) (by simpa using h₁)
          (by simpa using h₂)

private theorem Derives.fill_strongFalsum {D : Formula.Context Atom} (hD : D.Distributive) :
    {D.fill .strongFalsum} ⊢ (.strongFalsum : Formula Atom) := by
  induction D with
  | hole => exact .single _
  | conjLeft D ψ ih => exact (Derives.single _).conjE₁.trans (ih hD)
  | conjRight φ D ih => exact (Derives.single _).conjE₂.trans (ih hD)
  | disjLeft D ψ ih => exact .strongFalsumCtr _ ((Derives.single _).disjMonLeft (ih hD))
  | disjRight φ D ih => exact .strongFalsumCtr _ ((Derives.single _).disjCom.disjMonLeft (ih hD))
  | poss | nec => exact hD.elim

theorem Splits.fill_strongFalsum {C : Formula.Context Atom} (hC : C.Splittable) :
    Splits (C.fill .strongFalsum) C.extra := by
  have hpf : {.poss (.strongFalsum : Formula Atom)} ⊢ .falsum :=
    ((Derives.single _).possMon' (Derives.single _).conjE₁).trans poss_falsum_derives
  cases C with
  | poss C =>
    exact Splits.of_derives (((Derives.single _).possMon' (Derives.fill_strongFalsum hC)).trans hpf)
  | nec C =>
    exact Splits.of_derives ((((Derives.single _).necMap
      (Derives.fill_strongFalsum hC)).necInst).trans poss_falsum_derives)
  | _ => exact fun χ _ ↦ (Derives.fill_strongFalsum hC).trans (strongFalsum_derives χ)

theorem conj_ne_disj_strongHintikka_derives {k : ℕ} (τ : WorldType n k)
    (T : Finset (WorldType n k)) :
    {.disj (.conj (hintikka e k τ) .ne) (strongHintikka e T)} ⊢ strongHintikka e (insert τ T) :=
  (Derives.single (bigDisj (.conj (hintikka e k τ) .ne ::
    (T.toList.map (hintikka e k)).map fun y ↦ .conj y .ne))).bigDisj_perm fun x ↦ by
    simp only [List.mem_cons, List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_insert,
      or_and_right, exists_or, exists_eq_left, Function.comp]
    exact or_congr_left eq_comm

theorem splits_bigDisj_hintikka {k : ℕ} :
    ∀ (L : List (WorldType n k)) {C : Formula.Context Atom}, C.Splittable →
      Splits (C.fill (bigDisj (L.map (hintikka e k))))
        ((fun T ↦ C.fill (strongHintikka e T)) '' {T | T ⊆ L.toFinset})
  | [], C, _ => Splits.of_derives_mem (B := C.fill .falsum) (.single _)
      ⟨∅, by simp, by simp only [strongHintikka_empty]⟩
  | τ :: r, C, hC => by
    have hsplit := Splits.fill_split
      (hC.comp (D := .disjLeft .hole (bigDisj (r.map (hintikka e k)))) trivial) (hintikka e k τ)
    simp only [fill_comp, fill] at hsplit
    refine hsplit.trans ?_
    rintro σ (rfl | rfl)
    · have h := splits_bigDisj_hintikka r
        (C := C.comp (.disjRight (.conj (hintikka e k τ) .ne) .hole))
        (hC.comp trivial)
      simp only [fill_comp, fill] at h
      refine h.trans ?_
      rintro _ ⟨T, hT, rfl⟩
      exact Splits.of_derives_mem ((conj_ne_disj_strongHintikka_derives τ T).fill C)
        ⟨insert τ T, Finset.insert_subset (by simp) (hT.trans (by simp)), rfl⟩
    · refine (Splits.of_derives (((Derives.single _).disjMonLeft
        (Derives.single _).conjE₂).falsumE.fill C)).trans ?_
      rintro _ rfl
      exact (splits_bigDisj_hintikka r hC).mono (Set.image_mono fun T (hT : T ⊆ r.toFinset) ↦
        hT.trans (by rw [List.toFinset_cons]; exact Finset.subset_insert _ _))

/-! ### Depth and atoms of the Hintikka formulas -/

omit [Inhabited Atom] in
theorem Formula.AtomsIn.mono {S S' : Set Atom} (hS : S ⊆ S') {φ : Formula Atom}
    (h : φ.AtomsIn S) : φ.AtomsIn S' := by
  induction φ with
  | atom => exact hS h
  | ne => trivial
  | neg _ ih | poss _ ih => exact ih h
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem atomsIn_bigConj {S : Set Atom} (hd : default ∈ S) {L : List (Formula Atom)}
    (hL : ∀ x ∈ L, x.AtomsIn S) : (bigConj L).AtomsIn S := by
  induction L with
  | nil => exact ⟨hd, hd⟩
  | cons x r ih => exact ⟨hL x (by simp), ih fun y hy ↦ hL y (by simp [hy])⟩

theorem atomsIn_bigDisj {S : Set Atom} (hd : default ∈ S) {L : List (Formula Atom)}
    (hL : ∀ x ∈ L, x.AtomsIn S) : (bigDisj L).AtomsIn S := by
  induction L with
  | nil => exact ⟨hd, hd⟩
  | cons x r ih => exact ⟨hL x (by simp), ih fun y hy ↦ hL y (by simp [hy])⟩

theorem atomsIn_literals (hd : default ∈ Set.range e) (a : Fin n → Bool) :
    (literals e a).AtomsIn (Set.range e) :=
  atomsIn_bigConj hd fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    unfold literal; split <;> exact ⟨i, rfl⟩

theorem atomsIn_hintikka (hd : default ∈ Set.range e) :
    ∀ (k : ℕ) (τ : WorldType n k), (hintikka e k τ).AtomsIn (Set.range e)
  | 0, a => atomsIn_literals hd a
  | k + 1, τ => ⟨atomsIn_literals hd _, atomsIn_bigConj hd fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact atomsIn_hintikka hd k σ,
    atomsIn_bigDisj hd fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact atomsIn_hintikka hd k σ⟩

/-! ### Distinct strong Hintikka formulas contradict -/

/-- A disjunction with a disjunct `α ∧ NE` contradicts `¬α`
    ([aloni-anttila-yang-2024] Lemma 4.13). -/
theorem conj_ne_disj_derives_strongFalsum {α : Formula Atom} (hα : α.NEFree) :
    {.conj (.neg α) (.disj (.conj α .ne) φ)} ⊢ .strongFalsum := by
  have h₀ := Derives.single (Formula.conj (.neg α) (.conj α .ne))
  have hf : {Formula.conj (.neg α) (.conj α .ne)} ⊢ .falsum := by
    simpa using Derives.negE (β := .falsum) hα Formula.neFree_falsum h₀.conjE₂.conjE₁ h₀.conjE₁
  have h₁ : {Formula.conj (.neg α) (.conj α .ne)} ⊢ .strongFalsum := hf.conj h₀.conjE₂.conjE₂
  exact .strongFalsumCtr _ (((Derives.single _).trans
    (conj_disj_derives_disj_conj (φ := .neg α) hα)).disjMonLeft h₁)

/-- Distinct strong Hintikka formulas contradict each other
    ([aloni-anttila-yang-2024] Lemma 4.11). -/
theorem strongHintikka_conj_derives (he : Function.Injective e) (hd : default ∈ Set.range e)
    {k : ℕ} {T₁ T₂ : Finset (WorldType n k)} (hT : T₁ ≠ T₂) :
    {.conj (strongHintikka e T₁) (strongHintikka e T₂)} ⊢ .strongFalsum := by
  have key : ∀ {T T' : Finset (WorldType n k)} {τ}, τ ∈ T → τ ∉ T' →
      {.conj (strongHintikka e T') (strongHintikka e T)} ⊢ .strongFalsum := by
    intro T T' τ hτ hτ'
    have hneg : {strongHintikka e T'} ⊢ .neg (hintikka e k τ) :=
      ((Derives.single _).of_bigDisjNE fun x hx ↦ by
        obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ).bigDisj_elim
        (fun x hx ↦ by
          obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
          refine (hintikka_derives he (neFree_hintikka e k τ) (modalDepth_hintikka e k τ)
            (atomsIn_hintikka hd k τ) σ).2 ?_
          rw [realize_hintikka he]; rintro rfl; exact hτ' (Finset.mem_toList.mp hσ))
        ((Derives.single _).of_falsum (neFree_hintikka e k τ))
    have hexp := (Derives.single (strongHintikka e T)).bigDisj_expand
      (List.mem_map_of_mem (f := fun y ↦ Formula.conj y .ne)
        (List.mem_map_of_mem (f := hintikka e k) (Finset.mem_toList.mpr hτ)))
    exact ((Derives.single _).conjE₁.trans hneg |>.conj
      ((Derives.single _).conjE₂.trans hexp)).trans
      (conj_ne_disj_derives_strongFalsum (neFree_hintikka e k τ))
  obtain ⟨τ, hτ⟩ : ∃ τ, (τ ∈ T₁ ∧ τ ∉ T₂) ∨ (τ ∈ T₂ ∧ τ ∉ T₁) := by
    by_contra h
    exact hT (Finset.ext fun τ ↦ by by_cases h₁ : τ ∈ T₁ <;> by_cases h₂ : τ ∈ T₂ <;> simp_all)
  rcases hτ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact (Derives.single _).conj_comm.trans (key h₁ h₂)
  · exact key h₁ h₂

/-! ### Splitting every formula into strong Hintikka cases -/

theorem realize_bigConj_poss_hintikka (he : Function.Injective e) {k : ℕ}
    (U : Finset (WorldType n k)) (τ : WorldType n (k + 1)) :
    Realize (univModel e) (bigConj (U.toList.map fun σ ↦ .poss (hintikka e k σ)))
      (world (k + 1) τ) ↔
      U ⊆ τ.2 := by
  simp only [realize_bigConj, List.mem_map, Finset.mem_toList, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, realize_poss, univModel_access_succ, Finset.mem_image,
    exists_exists_and_eq_and, realize_hintikka he, exists_eq_right]
  rfl

theorem realize_nec_bigDisj_hintikka (he : Function.Injective e) {k : ℕ}
    (U : Finset (WorldType n k)) (τ : WorldType n (k + 1)) :
    Realize (univModel e) (Formula.nec (bigDisj (U.toList.map (hintikka e k)))) (world (k + 1) τ) ↔
      τ.2 ⊆ U := by
  simp only [Formula.nec, realize_neg, realize_poss, univModel_access_succ, Finset.mem_image,
    exists_exists_and_eq_and, realize_bigDisj, List.mem_map, Finset.mem_toList,
    exists_exists_and_eq_and, realize_hintikka he, not_exists, not_and]
  exact ⟨fun h x hx ↦ by by_contra hc; exact h x hx fun y hy hxy ↦ hc (hxy ▸ hy),
    fun h x hx hn ↦ hn x (h hx) rfl⟩

theorem splits_of_derives_bigDisj {A : Formula Atom} {k : ℕ} {L : List (WorldType n k)}
    {P : Set (Finset (WorldType n k))} (h : {A} ⊢ bigDisj (L.map (hintikka e k)))
    (hP : ∀ T, T ⊆ L.toFinset → T ∈ P) {C : Formula.Context Atom} (hC : C.Splittable) :
    Splits (C.fill A) ((fun T ↦ C.fill (strongHintikka e T)) '' P ∪ C.extra) :=
  ((Splits.of_derives (h.fill C)).trans fun _ hσ ↦ hσ ▸ splits_bigDisj_hintikka L hC).mono
    (Set.subset_union_of_subset_left (Set.image_mono fun T hT ↦ hP T hT) _)

theorem splits_fill_of_neFree (he : Function.Injective e) {β : Formula Atom} (hβ : β.NEFree)
    {k : ℕ} (hk : β.modalDepth ≤ k) (hA : β.AtomsIn (Set.range e)) {C : Formula.Context Atom}
    (hC : C.Splittable) :
    Splits (C.fill β) ((fun T ↦ C.fill (strongHintikka e T)) ''
      {T | support (univModel e) β (T.image (world k))} ∪ C.extra) :=
  splits_of_derives_bigDisj (derives_bigDisj_realize he hβ hk hA) (fun T hT ↦
    (support_image_iff hβ T).mpr fun τ hτ ↦ by simpa using hT hτ) hC

/-- In a splittable context, a formula splits into the strong Hintikka formulas of the teams
    supporting it, and its negation into those of the teams anti-supporting it, together with
    the context's extra case. -/
theorem splits_fill (he : Function.Injective e) (hd : default ∈ Set.range e) :
    ∀ (φ : Formula Atom) {k : ℕ}, φ.modalDepth ≤ k → φ.AtomsIn (Set.range e) →
      ∀ {C : Formula.Context Atom}, C.Splittable →
        Splits (C.fill φ) ((fun T ↦ C.fill (strongHintikka e T)) ''
            {T | support (univModel e) φ (T.image (world k))} ∪ C.extra) ∧
        Splits (C.fill (.neg φ)) ((fun T ↦ C.fill (strongHintikka e T)) ''
            {T | antiSupport (univModel e) φ (T.image (world k))} ∪ C.extra)
  | .atom p, k, hk, hA, C, hC =>
    ⟨splits_fill_of_neFree (β := .atom p) he trivial hk hA hC,
      splits_fill_of_neFree (β := .neg (.atom p)) he trivial hk hA hC⟩
  | .ne, k, _, _, C, hC => by
    refine ⟨?_, Splits.of_derives_mem ((Derives.single _).negNeE.fill C)
      (Or.inl ⟨∅, Finset.image_empty _, by simp only [strongHintikka_empty]⟩)⟩
    have hs := splits_bigDisj_hintikka (e := e) (Finset.univ : Finset (WorldType n k)).toList
      (C := C.comp (.conjRight .ne .hole)) (hC.comp trivial)
    simp only [fill_comp, fill] at hs
    refine ((Splits.of_derives (((Derives.single _).conj
      (derives_bigDisj_hintikka e k _)).fill C)).trans fun _ hσ ↦ hσ ▸ hs).trans ?_
    rintro _ ⟨T, -, rfl⟩
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp only [strongHintikka_empty]
      refine (Splits.of_derives
        ((Derives.single (Formula.conj .ne .falsum)).conj_comm.fill C)).trans
        fun _ hσ ↦ hσ ▸ (Splits.fill_strongFalsum hC).mono Set.subset_union_right
    · exact Splits.of_derives_mem ((Derives.single _).conjE₂.fill C) (Or.inl ⟨T, hT.image _, rfl⟩)
  | .neg ψ, k, hk, hA, C, hC =>
    have ih := splits_fill he hd ψ hk hA hC
    ⟨ih.2, (Splits.of_derives ((Derives.single _).dneE.fill C)).trans fun _ hσ ↦ hσ ▸ ih.1⟩
  | .conj ψ₁ ψ₂, k, hk, hA, C, hC => by
    have ih₁ := fun {C : Formula.Context Atom} (hC : C.Splittable) ↦
      splits_fill he hd ψ₁ (max_le_iff.mp hk).1 hA.1 hC
    have ih₂ := fun {C : Formula.Context Atom} (hC : C.Splittable) ↦
      splits_fill he hd ψ₂ (max_le_iff.mp hk).2 hA.2 hC
    constructor
    · have h₁ := (ih₁ (C := C.comp (.conjLeft .hole ψ₂)) (hC.comp trivial)).1
      simp only [fill_comp, fill, extra_comp (D := .conjLeft .hole ψ₂) trivial] at h₁
      refine h₁.trans ?_
      rintro _ (⟨T₁, hT₁, rfl⟩ | hσ)
      · have h₂ := (ih₂ (C := C.comp (.conjRight (strongHintikka e T₁) .hole)) (hC.comp trivial)).1
        simp only [fill_comp, fill, extra_comp (D := .conjRight (strongHintikka e T₁) .hole)
          trivial] at h₂
        refine h₂.trans ?_
        rintro _ (⟨T₂, hT₂, rfl⟩ | hσ)
        · by_cases h : T₁ = T₂
          · subst h
            exact Splits.of_derives_mem ((Derives.single _).conjE₁.fill C)
              (Or.inl ⟨T₁, ⟨hT₁, hT₂⟩, rfl⟩)
          · exact (Splits.of_derives ((strongHintikka_conj_derives he hd h).fill C)).trans
              fun _ hσ ↦ hσ ▸ (Splits.fill_strongFalsum hC).mono Set.subset_union_right
        · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
      · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
    · refine (Splits.of_derives ((Derives.single _).dmConjE.fill C)).trans ?_
      rintro _ rfl
      have h₁ := (ih₁ (C := C.comp (.disjLeft .hole (.neg ψ₂))) (hC.comp trivial)).2
      simp only [fill_comp, fill, extra_comp (D := .disjLeft .hole (.neg ψ₂)) trivial] at h₁
      refine h₁.trans ?_
      rintro _ (⟨T₁, hT₁, rfl⟩ | hσ)
      · have h₂ := (ih₂ (C := C.comp (.disjRight (strongHintikka e T₁) .hole)) (hC.comp trivial)).2
        simp only [fill_comp, fill, extra_comp (D := .disjRight (strongHintikka e T₁) .hole)
          trivial] at h₂
        refine h₂.trans ?_
        rintro _ (⟨T₂, hT₂, rfl⟩ | hσ)
        · exact Splits.of_derives_mem ((disj_strongHintikka_derives T₁ T₂).fill C)
            (Or.inl ⟨T₁ ∪ T₂, ⟨_, hT₁, _, hT₂, (Finset.image_union _ _).symm⟩, rfl⟩)
        · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
      · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
  | .disj ψ₁ ψ₂, k, hk, hA, C, hC => by
    have ih₁ := fun {C : Formula.Context Atom} (hC : C.Splittable) ↦
      splits_fill he hd ψ₁ (max_le_iff.mp hk).1 hA.1 hC
    have ih₂ := fun {C : Formula.Context Atom} (hC : C.Splittable) ↦
      splits_fill he hd ψ₂ (max_le_iff.mp hk).2 hA.2 hC
    constructor
    · have h₁ := (ih₁ (C := C.comp (.disjLeft .hole ψ₂)) (hC.comp trivial)).1
      simp only [fill_comp, fill, extra_comp (D := .disjLeft .hole ψ₂) trivial] at h₁
      refine h₁.trans ?_
      rintro _ (⟨T₁, hT₁, rfl⟩ | hσ)
      · have h₂ := (ih₂ (C := C.comp (.disjRight (strongHintikka e T₁) .hole)) (hC.comp trivial)).1
        simp only [fill_comp, fill, extra_comp (D := .disjRight (strongHintikka e T₁) .hole)
          trivial] at h₂
        refine h₂.trans ?_
        rintro _ (⟨T₂, hT₂, rfl⟩ | hσ)
        · exact Splits.of_derives_mem ((disj_strongHintikka_derives T₁ T₂).fill C)
            (Or.inl ⟨T₁ ∪ T₂, ⟨_, hT₁, _, hT₂, (Finset.image_union _ _).symm⟩, rfl⟩)
        · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
      · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
    · refine (Splits.of_derives ((Derives.single _).dmDisjE.fill C)).trans ?_
      rintro _ rfl
      have h₁ := (ih₁ (C := C.comp (.conjLeft .hole (.neg ψ₂))) (hC.comp trivial)).2
      simp only [fill_comp, fill, extra_comp (D := .conjLeft .hole (.neg ψ₂)) trivial] at h₁
      refine h₁.trans ?_
      rintro _ (⟨T₁, hT₁, rfl⟩ | hσ)
      · have h₂ := (ih₂ (C := C.comp (.conjRight (strongHintikka e T₁) .hole)) (hC.comp trivial)).2
        simp only [fill_comp, fill, extra_comp (D := .conjRight (strongHintikka e T₁) .hole)
          trivial] at h₂
        refine h₂.trans ?_
        rintro _ (⟨T₂, hT₂, rfl⟩ | hσ)
        · by_cases h : T₁ = T₂
          · subst h
            exact Splits.of_derives_mem ((Derives.single _).conjE₁.fill C)
              (Or.inl ⟨T₁, ⟨hT₁, hT₂⟩, rfl⟩)
          · exact (Splits.of_derives ((strongHintikka_conj_derives he hd h).fill C)).trans
              fun _ hσ ↦ hσ ▸ (Splits.fill_strongFalsum hC).mono Set.subset_union_right
        · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
      · exact Splits.of_derives_mem (.single _) (Or.inr hσ)
  | .poss ψ, 0, hk, _, _, _ => absurd hk (by simp [Formula.modalDepth])
  | .poss ψ, k + 1, hk, hA, C, hC => by
    have ih := fun {C : Formula.Context Atom} (hC : C.Splittable) ↦
      splits_fill he hd ψ (k := k) (by simpa [Formula.modalDepth] using hk) hA hC
    have hcl : ∀ L : List (WorldType n (k + 1)), ∀ x ∈ L.map (hintikka e (k + 1)), x.NEFree :=
      fun L x hx ↦ by obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e _ τ
    have hconj : ∀ U : Finset (WorldType n k), (bigConj (U.toList.map fun σ ↦
        .poss (hintikka e k σ))).NEFree := fun U ↦ neFree_bigConj _ fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ
    have hconjk : ∀ U : Finset (WorldType n k), (bigConj (U.toList.map fun σ ↦
        .poss (hintikka e k σ))).modalDepth ≤ k + 1 := fun U ↦ modalDepth_bigConj fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.succ_le_succ (modalDepth_hintikka e k σ)
    have hconjA : ∀ U : Finset (WorldType n k), (bigConj (U.toList.map fun σ ↦
        .poss (hintikka e k σ))).AtomsIn (Set.range e) := fun U ↦ atomsIn_bigConj hd fun x hx ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact atomsIn_hintikka hd k σ
    have hpossU : ∀ U : Finset (WorldType n k), {.poss (strongHintikka e U)} ⊢
        bigConj (U.toList.map fun σ ↦ .poss (hintikka e k σ)) := fun U ↦
      Derives.bigConj_of_forall fun x hx ↦ by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
        exact (Derives.single _).poss_of_poss_bigDisjNE (List.mem_map_of_mem hσ)
    constructor
    · classical
      set A := Finset.univ.filter fun τ : WorldType n (k + 1) ↦
        support (univModel e) (.poss ψ) {world (k + 1) τ}
      have hNF : {.poss ψ} ⊢ bigDisj (A.toList.map (hintikka e (k + 1))) := by
        refine (ih (C := .poss .hole) trivial).1 _ ?_
        rintro _ (⟨U, hU, rfl⟩ | hσ)
        · rcases U.eq_empty_or_nonempty with rfl | hUne
          · simpa [fill, strongHintikka_empty] using
              poss_falsum_derives.of_falsum (neFree_bigDisj _ (hcl _))
          · refine (hpossU U).trans ((derives_bigDisj_realize he (hconj U) (hconjk U)
              (hconjA U)).bigDisj_mono (hcl _) fun x hx ↦ ?_)
            obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hx
            have hUτ := (realize_bigConj_poss_hintikka he U τ).mp
              (Finset.mem_filter.mp (Finset.mem_toList.mp hτ)).2
            refine (Derives.single _).bigDisj_of_mem (hcl _) (List.mem_map_of_mem
              (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)))
            intro w hw
            rw [Finset.mem_singleton.mp hw]
            refine ⟨U.image (world k), ?_, hUne.image _, hU⟩
            rw [univModel_access_succ]; exact Finset.image_subset_image hUτ
        · rw [hσ]; exact (Derives.single _).of_falsum (neFree_bigDisj _ (hcl _))
      refine splits_of_derives_bigDisj (P := {T | support (univModel e) (.poss ψ)
        (T.image (world (k + 1)))}) hNF (fun T hT w hw ↦ ?_) hC
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hw
      have hτA : τ ∈ A := by simpa using hT hτ
      exact (Finset.mem_filter.mp hτA).2 _ (Finset.mem_singleton_self _)
    · classical
      set A := Finset.univ.filter fun τ : WorldType n (k + 1) ↦
        antiSupport (univModel e) (.poss ψ) {world (k + 1) τ}
      have hNF : {.neg (.poss ψ)} ⊢ bigDisj (A.toList.map (hintikka e (k + 1))) := by
        refine (Derives.single _).interE.trans ((ih (C := .nec .hole) trivial).2 _ ?_)
        rintro _ (⟨U, hU, rfl⟩ | hσ)
        · set d := Formula.conj (Formula.nec (bigDisj (U.toList.map (hintikka e k))))
            (bigConj (U.toList.map fun σ ↦ .poss (hintikka e k σ)))
          have hd₁ : {Formula.nec (strongHintikka e U)} ⊢ d :=
            ((Derives.single _).necMap ((Derives.single _).of_bigDisjNE fun x hx ↦ by
              obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ)).conj
            (Derives.bigConj_of_forall fun x hx ↦ by
              obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
              exact (Derives.single _).poss_of_nec_bigDisjNE (by simpa using List.ne_nil_of_mem hσ)
                (List.mem_map_of_mem hσ))
          have hdβ : d.NEFree := ⟨neFree_bigDisj_hintikka e _, hconj U⟩
          have hdk : d.modalDepth ≤ k + 1 := max_le (Nat.succ_le_succ (modalDepth_bigDisj
            fun x hx ↦ by
              obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact modalDepth_hintikka e k σ))
            (hconjk U)
          have hdA : d.AtomsIn (Set.range e) := ⟨atomsIn_bigDisj hd fun x hx ↦ by
            obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact atomsIn_hintikka hd k σ, hconjA U⟩
          refine hd₁.trans ((derives_bigDisj_realize he hdβ hdk hdA).bigDisj_mono (hcl _)
            fun x hx ↦ ?_)
          obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hx
          have hr := (Finset.mem_filter.mp (Finset.mem_toList.mp hτ)).2
          have hτU : τ.2 = U := subset_antisymm ((realize_nec_bigDisj_hintikka he U τ).mp hr.1)
            ((realize_bigConj_poss_hintikka he U τ).mp hr.2)
          refine (Derives.single _).bigDisj_of_mem (hcl _) (List.mem_map_of_mem
            (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)))
          intro w hw
          rw [Finset.mem_singleton.mp hw]
          change antiSupport (univModel e) ψ ((univModel e).access (world (k + 1) τ))
          rw [univModel_access_succ, hτU]; exact hU
        · rw [hσ]; exact (Derives.single _).of_falsum (neFree_bigDisj _ (hcl _))
      refine splits_of_derives_bigDisj (P := {T | antiSupport (univModel e) (.poss ψ)
        (T.image (world (k + 1)))}) hNF (fun T hT w hw ↦ ?_) hC
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hw
      have hτA : τ ∈ A := by simpa using hT hτ
      exact (Finset.mem_filter.mp hτA).2 _ (Finset.mem_singleton_self _)

/-! ### Completeness -/

/-- `φ.atomList` lists the atoms occurring in `φ`. -/
def Formula.atomList : Formula Atom → List Atom
  | .atom p => [p]
  | .ne => []
  | .neg φ | .poss φ => φ.atomList
  | .conj φ ψ | .disj φ ψ => φ.atomList ++ ψ.atomList

omit [Inhabited Atom] in
theorem Formula.atomsIn_atomList (φ : Formula Atom) : φ.AtomsIn {p | p ∈ φ.atomList} := by
  induction φ with
  | atom p => simp [atomList, AtomsIn]
  | ne => trivial
  | neg _ ih | poss _ ih => exact ih
  | conj _ _ ih₁ ih₂ | disj _ _ ih₁ ih₂ =>
    exact ⟨ih₁.mono fun p hp ↦ by simp_all [atomList], ih₂.mono fun p hp ↦ by simp_all [atomList]⟩

/-- **Completeness** ([aloni-anttila-yang-2024] Theorem 4.43) for finite premise sets. A
    consequence that holds on every model is derivable. -/
theorem completeness {Γ : Finset (Formula Atom)} {φ : Formula Atom}
    (h : ∀ (W : Type) [DecidableEq W] (M : KripkeModel W Atom) (s : Finset W),
      (∀ γ ∈ Γ, support M γ s) → support M φ s) : (Γ : Set (Formula Atom)) ⊢ φ := by
  have := Classical.decEq Atom
  set γ : Formula Atom := bigConj Γ.toList
  set X : Finset Atom := (γ.atomList ++ φ.atomList ++ [default]).toFinset
  set e : Fin X.card → Atom := fun i ↦ (X.equivFin.symm i : Atom)
  have he : Function.Injective e := fun i j hij ↦ X.equivFin.symm.injective (Subtype.ext hij)
  have hX : ∀ p ∈ X, p ∈ Set.range e := fun p hp ↦ ⟨X.equivFin ⟨p, hp⟩, by simp [e]⟩
  have hd : default ∈ Set.range e := hX _ (by simp [X])
  have hγA : γ.AtomsIn (Set.range e) := γ.atomsIn_atomList.mono fun p hp ↦ hX p (by simp_all [X])
  have hφA : φ.AtomsIn (Set.range e) := φ.atomsIn_atomList.mono fun p hp ↦ hX p (by simp_all [X])
  have hγφ : {γ} ⊢ φ := by
    refine (splits_fill he hd γ (le_max_left γ.modalDepth φ.modalDepth) hγA
      (C := .hole) trivial).1 φ ?_
    rintro _ (⟨T, hT, rfl⟩ | hσ)
    · refine (derives_of_support he φ (le_max_right _ _) hφA T).1 (h _ (univModel e) _ ?_)
      exact fun γ' hγ' ↦ (support_bigConj_iff (univModel e) Γ.toList _).mp hT γ'
        (Finset.mem_toList.mpr hγ')
    · exact hσ.elim
  exact (Derives.bigConj_of_forall fun x hx ↦ .hyp (Finset.mem_toList.mp hx)).trans hγφ

/-- For finite premise sets, derivability is consequence on every model. -/
theorem derives_iff {Γ : Finset (Formula Atom)} {φ : Formula Atom} :
    (Γ : Set (Formula Atom)) ⊢ φ ↔ ∀ (W : Type) [DecidableEq W] (M : KripkeModel W Atom)
      (s : Finset W), (∀ γ ∈ Γ, support M γ s) → support M φ s :=
  ⟨fun h _ _ M s hs ↦ soundness h M s fun γ hγ ↦ hs γ hγ, completeness⟩

end BSML
