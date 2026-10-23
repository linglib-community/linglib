module

public import Linglib.Logic.Team.BSML.Classical
public import Linglib.Logic.Team.Bisimulation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Characteristic formulas for BSML

The world type of depth `k` of a world, over `n` atoms enumerated by `e`, records the truth values
of these atoms and, for positive `k`, the set of depth `k - 1` types of the world's successors.
Each type has a characteristic (Hintikka) formula, an `NE`-free formula that holds at a world
exactly when the world has that type. Two worlds have the same type exactly when they are
`k`-bisimilar, once `e` enumerates every atom. The strong Hintikka formula of a set of types `T` is
supported by a team exactly when the types of its worlds are those in `T`.

## Main definitions

* `verum`, `bigConj`, `bigDisj`, `bigDisjNE`: `⊤` as `p ∨ ¬p`, finite conjunction and
  disjunction, and finite disjunction with each disjunct conjoined with `NE`.
* `WorldType n k`, `worldType e M k w`: the world types, and the type of a world.
* `hintikka e k τ`, `strongHintikka e T`: the Hintikka formulas of a type and of a set of types.

## Main results

* `realize_hintikka_iff`: the Hintikka formula of `τ` holds at `w` iff `w` has type `τ`.
* `worldType_eq_iff_worldBisim`: two worlds have the same type iff they are `k`-bisimilar.
* `realize_hintikka_worldType_iff`: the Hintikka formula of `w`'s type holds at `w'` iff `w'` is
  `k`-bisimilar to `w`.
* `support_strongHintikka_iff`: a team supports the strong Hintikka formula of `T` iff the types
  of its worlds are those in `T`.

## Implementation notes

[aloni-anttila-yang-2024] Definition 3.2 conjoins the depth `k` Hintikka formula of the world at
depth `k + 1`; here only its literals are conjoined, which is equivalent and needs no truncation of
types.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
-/

@[expose] public section

namespace BSML

open ModalLogic

variable {W W' : Type*} {Atom : Type*}

/-! ### `⊤` and finite conjunction -/

/-- The tautology `p ∨ ¬p` for the default atom is `NE`-free, true at every world and
    supported by every team. BSML has no tautology without atoms. -/
def verum [Inhabited Atom] : Formula Atom :=
  .disj (.atom default) (.neg (.atom default))

@[simp] theorem realize_verum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    Realize M verum w :=
  em (M.val default w)

@[simp] theorem neFree_verum [Inhabited Atom] : (verum : Formula Atom).NEFree :=
  ⟨trivial, trivial⟩

/-- Finite conjunction of a list of formulas; the empty conjunction is `⊤`. -/
def bigConj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => verum
  | φ :: rest => .conj φ (bigConj rest)

theorem realize_bigConj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    Realize M (bigConj l) w ↔ ∀ φ ∈ l, Realize M φ w := by
  induction l with
  | nil => simp [bigConj]
  | cons φ rest ih => simp only [bigConj, Realize, List.forall_mem_cons, ih]

theorem neFree_bigConj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigConj l).NEFree := by
  induction l with
  | nil => exact neFree_verum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

/-! ### Finite disjunction -/

@[simp] theorem not_realize_falsum [Inhabited Atom] (M : KripkeModel W Atom) (w : W) :
    ¬ Realize M .falsum w := by
  simp [Formula.falsum, Realize]

/-- Finite disjunction of a list of formulas; the empty disjunction is `⊥`. -/
def bigDisj [Inhabited Atom] : List (Formula Atom) → Formula Atom
  | [] => .falsum
  | φ :: rest => .disj φ (bigDisj rest)

theorem realize_bigDisj [Inhabited Atom] (M : KripkeModel W Atom) (w : W)
    (l : List (Formula Atom)) :
    Realize M (bigDisj l) w ↔ ∃ φ ∈ l, Realize M φ w := by
  induction l with
  | nil => simp [bigDisj]
  | cons φ rest ih => simp [bigDisj, ih]

theorem neFree_bigDisj [Inhabited Atom] (l : List (Formula Atom))
    (h : ∀ φ ∈ l, φ.NEFree) : (bigDisj l).NEFree := by
  induction l with
  | nil => exact Formula.neFree_falsum
  | cons φ rest ih =>
    exact ⟨h φ (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun ψ hψ => h ψ (List.mem_cons.mpr (Or.inr hψ)))⟩

variable [Inhabited Atom]

theorem modalDepth_bigConj {L : List (Formula Atom)} {k : ℕ} (hL : ∀ x ∈ L, x.modalDepth ≤ k) :
    (bigConj L).modalDepth ≤ k := by
  induction L with
  | nil => simp [bigConj, verum, Formula.modalDepth]
  | cons x r ih =>
    simp only [bigConj, Formula.modalDepth, max_le_iff]
    exact ⟨hL x (by simp), ih fun y hy ↦ hL y (by simp [hy])⟩

theorem modalDepth_bigDisj {L : List (Formula Atom)} {k : ℕ} (hL : ∀ x ∈ L, x.modalDepth ≤ k) :
    (bigDisj L).modalDepth ≤ k := by
  induction L with
  | nil => simp [bigDisj, Formula.falsum, Formula.modalDepth]
  | cons x r ih =>
    simp only [bigDisj, Formula.modalDepth, max_le_iff]
    exact ⟨hL x (by simp), ih fun y hy ↦ hL y (by simp [hy])⟩

/-- `bigDisjNE L` is the disjunction of the formulas of `L`, each conjoined with `NE`. -/
def bigDisjNE (L : List (Formula Atom)) : Formula Atom := bigDisj (L.map fun x ↦ .conj x .ne)

/-! ### World types -/

/-- A world type of depth `k` over `n` atoms gives the truth values of the atoms and, at positive
    depth, the set of the depth `k - 1` types of the successors. -/
def WorldType (n : ℕ) : ℕ → Type
  | 0 => Fin n → Bool
  | k + 1 => (Fin n → Bool) × Finset (WorldType n k)

namespace WorldType

variable {n : ℕ}

noncomputable instance instDecidableEq (k : ℕ) : DecidableEq (WorldType n k) := Classical.decEq _

noncomputable instance instFintype : (k : ℕ) → Fintype (WorldType n k)
  | 0 => inferInstanceAs (Fintype (Fin n → Bool))
  | k + 1 => @instFintypeProd _ _ _ (@Finset.fintype _ (instFintype k))

/-- `τ.val` gives the truth values of the atoms at the type `τ`. -/
def val : {k : ℕ} → WorldType n k → Fin n → Bool
  | 0, a => a
  | _ + 1, τ => τ.1

end WorldType

variable {n : ℕ} (e : Fin n → Atom)

open scoped Classical in
/-- `worldType e M k w` is the type of depth `k` of the world `w`, over the atoms enumerated
    by `e`. -/
noncomputable def worldType (M : KripkeModel W Atom) : (k : ℕ) → W → WorldType n k
  | 0, w => fun i ↦ decide (M.val (e i) w)
  | k + 1, w => (fun i ↦ decide (M.val (e i) w), (M.access w).image (worldType M k))

open scoped Classical in
omit [Inhabited Atom] in
theorem val_worldType (M : KripkeModel W Atom) :
    ∀ (k : ℕ) (w : W), (worldType e M k w).val = fun i ↦ decide (M.val (e i) w)
  | 0, _ | _ + 1, _ => rfl

/-! ### Hintikka formulas -/

/-- `literal e i b` is the `i`-th atom if `b` holds and its negation otherwise. -/
def literal (i : Fin n) (b : Bool) : Formula Atom :=
  if b then .atom (e i) else .neg (.atom (e i))

/-- `literals e a` conjoins the literals of the assignment `a`. -/
def literals (a : Fin n → Bool) : Formula Atom :=
  bigConj ((List.finRange n).map fun i ↦ literal e i (a i))

/-- The Hintikka formula of a type conjoins its literals and, at positive depth, the possibility
    of each successor type and the necessity of their disjunction. -/
noncomputable def hintikka : (k : ℕ) → WorldType n k → Formula Atom
  | 0, a => literals e a
  | k + 1, τ => .conj (literals e τ.1)
      (.conj (bigConj (τ.2.toList.map fun σ ↦ .poss (hintikka k σ)))
      (Formula.nec (bigDisj (τ.2.toList.map (hintikka k)))))

/-- The strong Hintikka formula of a set of types `T` is the disjunction of the formulas
    `χ_τ ∧ NE` for `τ ∈ T`. -/
noncomputable def strongHintikka {k : ℕ} (T : Finset (WorldType n k)) : Formula Atom :=
  bigDisjNE (T.toList.map (hintikka e k))

omit [Inhabited Atom] in
theorem neFree_literal (i : Fin n) (b : Bool) : (literal e i b).NEFree := by
  unfold literal; split <;> trivial

theorem neFree_literals (a : Fin n → Bool) : (literals e a).NEFree :=
  neFree_bigConj _ fun φ hφ ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ; exact neFree_literal e i _

theorem neFree_hintikka : ∀ (k : ℕ) (τ : WorldType n k), (hintikka e k τ).NEFree
  | 0, a => neFree_literals e a
  | k + 1, τ => ⟨neFree_literals e _, neFree_bigConj _ (fun φ hφ ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hφ; exact neFree_hintikka k σ),
    neFree_bigDisj _ (fun φ hφ ↦ by
      obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hφ; exact neFree_hintikka k σ)⟩

theorem modalDepth_literals (a : Fin n → Bool) : (literals e a).modalDepth ≤ 0 :=
  modalDepth_bigConj fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; unfold literal; split <;> rfl

theorem modalDepth_hintikka : ∀ (k : ℕ) (τ : WorldType n k), (hintikka e k τ).modalDepth ≤ k
  | 0, a => modalDepth_literals e a
  | k + 1, τ => by
    simp only [hintikka, Formula.modalDepth, Formula.nec, max_le_iff]
    refine ⟨(modalDepth_literals e _).trans (Nat.zero_le _), modalDepth_bigConj fun x hx ↦ ?_,
      Nat.succ_le_succ (modalDepth_bigDisj fun x hx ↦ ?_)⟩ <;>
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx
    · exact Nat.succ_le_succ (modalDepth_hintikka k σ)
    · exact modalDepth_hintikka k σ

theorem strongHintikka_empty {k : ℕ} :
    strongHintikka e (∅ : Finset (WorldType n k)) = .falsum := by
  simp [strongHintikka, bigDisjNE, bigDisj]

/-! ### Hintikka formulas characterize types -/

variable {e}

open scoped Classical in
omit [Inhabited Atom] in
theorem realize_literal (M : KripkeModel W Atom) (i : Fin n) (b : Bool) (w : W) :
    Realize M (literal e i b) w ↔ decide (M.val (e i) w) = b := by
  unfold literal; cases b <;> simp

open scoped Classical in
theorem realize_literals (M : KripkeModel W Atom) (a : Fin n → Bool) (w : W) :
    Realize M (literals e a) w ↔ (fun i ↦ decide (M.val (e i) w)) = a := by
  rw [literals, realize_bigConj, funext_iff]
  simp [realize_literal]

/-- The Hintikka formula of `τ` holds at a world exactly when the world has type `τ`. -/
theorem realize_hintikka_iff (M : KripkeModel W Atom) :
    ∀ (k : ℕ) (τ : WorldType n k) (w : W), Realize M (hintikka e k τ) w ↔ worldType e M k w = τ
  | 0, a, w => realize_literals M a w
  | k + 1, τ, w => by
    simp only [hintikka, realize_conj, realize_literals, realize_bigConj, realize_bigDisj,
      List.mem_map, Finset.mem_toList, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      realize_poss, realize_hintikka_iff M k, Formula.nec, realize_neg, not_exists, not_and,
      exists_exists_and_eq_and, not_forall, not_not, exists_prop]
    rw [worldType, Prod.ext_iff, Finset.ext_iff]
    simp only [Finset.mem_image]
    refine and_congr Iff.rfl ⟨fun ⟨h₁, h₂⟩ σ ↦ ⟨fun ⟨v, hv, hσ⟩ ↦ ?_, fun hσ ↦ h₁ σ hσ⟩,
      fun h ↦ ⟨fun σ hσ ↦ (h σ).mpr hσ, fun v hv ↦ ⟨_, (h _).mp ⟨v, hv, rfl⟩, rfl⟩⟩⟩
    obtain ⟨x, hx, rfl⟩ := h₂ v hv
    exact hσ ▸ hx

omit [Inhabited Atom] in
/-- Two worlds have the same type exactly when they are `k`-bisimilar, once `e` enumerates every
    atom. -/
theorem worldType_eq_iff_worldBisim (he : Function.Surjective e) {M : KripkeModel W Atom}
    {M' : KripkeModel W' Atom} :
    ∀ (k : ℕ) (w : W) (w' : W'), worldType e M k w = worldType e M' k w' ↔ WorldBisim k M w M' w'
  | 0, w, w' => by
    rw [worldType, worldType, funext_iff, WorldBisim]
    simp only [decide_eq_decide]
    exact (he.forall (p := fun p ↦ (M.val p w ↔ M'.val p w'))).symm
  | k + 1, w, w' => by
    rw [worldType, worldType, Prod.ext_iff, funext_iff, WorldBisim, Finset.ext_iff]
    simp only [decide_eq_decide]
    refine and_congr (he.forall (p := fun p ↦ (M.val p w ↔ M'.val p w'))).symm ?_
    simp only [Finset.mem_image]
    constructor
    · intro h
      refine ⟨fun v hv ↦ ?_, fun v' hv' ↦ ?_⟩
      · obtain ⟨v', hv', hvv'⟩ := (h _).mp ⟨v, hv, rfl⟩
        exact ⟨v', hv', (worldType_eq_iff_worldBisim he k v v').mp hvv'.symm⟩
      · obtain ⟨v, hv, hvv'⟩ := (h _).mpr ⟨v', hv', rfl⟩
        exact ⟨v, hv, (worldType_eq_iff_worldBisim he k v v').mp hvv'⟩
    · rintro ⟨h₁, h₂⟩ σ
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨v', hv', hb⟩ := h₁ v hv
        exact ⟨v', hv', ((worldType_eq_iff_worldBisim he k v v').mpr hb).symm⟩
      · rintro ⟨v', hv', rfl⟩
        obtain ⟨v, hv, hb⟩ := h₂ v' hv'
        exact ⟨v, hv, (worldType_eq_iff_worldBisim he k v v').mpr hb⟩

/-- The Hintikka formula of the type of `w` holds at `w'` exactly when `w'` is `k`-bisimilar to `w`
    ([aloni-anttila-yang-2024] Theorem 3.3). -/
theorem realize_hintikka_worldType_iff (he : Function.Surjective e) {M : KripkeModel W Atom}
    {M' : KripkeModel W' Atom} (k : ℕ) (w : W) (w' : W') :
    Realize M' (hintikka e k (worldType e M k w)) w' ↔ WorldBisim k M w M' w' := by
  rw [realize_hintikka_iff, eq_comm, worldType_eq_iff_worldBisim he]

/-! ### Team support -/

variable [DecidableEq W]

omit [Inhabited Atom] in
theorem support_verum [Inhabited Atom] (M : KripkeModel W Atom) (t : Finset W) :
    support M (verum (Atom := Atom)) t :=
  (support_iff_forall_realize neFree_verum).mpr fun w _ => realize_verum M w

theorem support_bigConj_iff (M : KripkeModel W Atom) (l : List (Formula Atom)) (t : Finset W) :
    support M (bigConj l) t ↔ ∀ φ ∈ l, support M φ t := by
  induction l with
  | nil => simpa [bigConj] using support_verum M t
  | cons φ rest ih =>
    simp only [bigConj, support_conj, ih, List.forall_mem_cons]

theorem support_bigDisj_hintikka_iff (M : KripkeModel W Atom) {k : ℕ} (L : List (WorldType n k))
    (t : Finset W) :
    support M (bigDisj (L.map (hintikka e k))) t ↔ ∀ w ∈ t, worldType e M k w ∈ L := by
  rw [support_iff_forall_realize (neFree_bigDisj _ fun x hx ↦ by
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hx; exact neFree_hintikka e k σ)]
  simp [realize_bigDisj, realize_hintikka_iff]

private theorem support_bigDisjNE_hintikka (M : KripkeModel W Atom) {k : ℕ} :
    ∀ (l : List (WorldType n k)) (t : Finset W),
      support M (bigDisjNE (l.map (hintikka e k))) t ↔ t.image (worldType e M k) = l.toFinset
  | [], t => by simp [bigDisjNE, bigDisj]
  | τ :: r, t => by
    change t ∈ Team.tensor _ _ ↔ _
    rw [List.toFinset_cons]
    constructor
    · rintro ⟨t₁, ⟨h₁, hne⟩, t₂, h₂, rfl⟩
      replace h₁ := (support_iff_forall_realize (neFree_hintikka e k τ)).mp h₁
      rw [Finset.image_union, (support_bigDisjNE_hintikka M r t₂).mp h₂, Finset.insert_eq]
      congr 1
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun σ hσ ↦ ?_⟩
      · obtain ⟨w, hw⟩ := hne
        exact Finset.mem_image.mpr ⟨w, hw, (realize_hintikka_iff M k τ w).mp (h₁ w hw)⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hσ
        exact (realize_hintikka_iff M k τ w).mp (h₁ w hw)
    · intro h
      have hmem : ∀ w ∈ t, worldType e M k w = τ ∨ worldType e M k w ∈ r.toFinset := fun w hw ↦
        Finset.mem_insert.mp (h ▸ Finset.mem_image_of_mem _ hw)
      refine ⟨t.filter (worldType e M k · = τ), ⟨(support_iff_forall_realize
        (neFree_hintikka e k τ)).mpr fun w hw ↦ (realize_hintikka_iff M k τ w).mpr
          (Finset.mem_filter.mp hw).2, ?_⟩, t.filter (worldType e M k · ∈ r.toFinset),
        (support_bigDisjNE_hintikka M r _).mpr ?_, ?_⟩
      · obtain ⟨w, hw, hwτ⟩ := Finset.mem_image.mp (h ▸ Finset.mem_insert_self τ _)
        exact ⟨w, Finset.mem_filter.mpr ⟨hw, hwτ⟩⟩
      · ext σ
        simp only [Finset.mem_image, Finset.mem_filter]
        refine ⟨fun ⟨w, ⟨_, hw⟩, hσ⟩ ↦ hσ ▸ hw, fun hσ ↦ ?_⟩
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (h ▸ Finset.mem_insert_of_mem hσ)
        exact ⟨w, ⟨hw, hσ⟩, rfl⟩
      · ext w
        simp only [Finset.mem_union, Finset.mem_filter]
        exact ⟨fun h ↦ h.elim And.left And.left, fun hw ↦ (hmem w hw).imp (⟨hw, ·⟩) (⟨hw, ·⟩)⟩

/-- A team supports the strong Hintikka formula of `T` exactly when the types of its worlds are
    those in `T` ([aloni-anttila-yang-2024] Definition 3.10). -/
theorem support_strongHintikka_iff (M : KripkeModel W Atom) {k : ℕ} (T : Finset (WorldType n k))
    (t : Finset W) : support M (strongHintikka e T) t ↔ t.image (worldType e M k) = T := by
  rw [strongHintikka, support_bigDisjNE_hintikka, Finset.toList_toFinset]

end BSML
