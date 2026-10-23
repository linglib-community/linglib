module

public import Linglib.Semantics.Dynamic.DRS.Defs

/-!
# Structural operations on DRSs

This file develops the structural theory of the DRSs of `DRS/Defs.lean`, namely the renaming of
discourse referents, the merge algebra, the transport of the extension relation along renaming,
and occurring and free referents. Renaming along a bijection gives Kamp and Reyle's alphabetic
variants (the prose preceding Def. 1.4.8).

## Main declarations

* `DRS.map`: renaming along `f : V → W`, functorial.
* `DRS.varFinset`, `DRS.freeVarFinset`: occurring and free referents.
* `DRS.IsProper`: no free referent (Def. 1.4.2–1.4.3); decidable.
* `DRS.ReuseFreeAt`: no referent declared twice along a nesting path.

## Main statements

* `DRS.isProper_merge`: merging a proper DRS with an increment whose free referents
  it declares is proper.

## Implementation notes

Renaming, occurring and free referents, and reuse-freeness are each three mutually recursive
functions, on DRSs, conditions and condition lists, by structural recursion through the
nesting, so the kernel evaluates them and `decide` settles them on concrete DRSs.

## References

* [kamp-reyle-1993]
-/

@[expose] public section

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x} {M X : Type*}

/-! ### Renaming -/

section Map

variable [DecidableEq W]

mutual
/-- `K.map f` renames the discourse referents of `K` along `f`. -/
def DRS.map (f : V → W) : DRS L V → DRS L W
  | ⟨U, cs⟩ => ⟨U.image f, Condition.mapList f cs⟩
/-- `c.map f` renames the discourse referents of `c` along `f`. -/
def Condition.map (f : V → W) : Condition L V → Condition L W
  | .atom a => .atom (a.map f)
  | .eq a b => .eq (f a) (f b)
  | .neg K => .neg (DRS.map f K)
  | .imp a c => .imp (DRS.map f a) (DRS.map f c)
  | .dis l r => .dis (DRS.map f l) (DRS.map f r)
/-- `Condition.mapList f cs` renames each condition of `cs` along `f`. -/
def Condition.mapList (f : V → W) : List (Condition L V) → List (Condition L W)
  | [] => []
  | c :: cs => Condition.map f c :: Condition.mapList f cs
end

variable (f : V → W)

@[simp] theorem Condition.mapList_eq_map (cs : List (Condition L V)) :
    Condition.mapList f cs = cs.map (Condition.map f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Condition.mapList, ih]

@[simp] theorem DRS.referents_map (K : DRS L V) : (K.map f).referents = K.referents.image f := by
  cases K; rfl

@[simp] theorem DRS.conditions_map (K : DRS L V) :
    (K.map f).conditions = K.conditions.map (Condition.map f) := by
  cases K; simp [DRS.map]

end Map

private theorem DRS.map_id_of_forall [DecidableEq V] {K : DRS L V}
    (h : ∀ c ∈ K.conditions, Condition.map id c = c) : DRS.map id K = K := by
  obtain ⟨U, cs⟩ := K
  simp only [DRS.map, Condition.mapList_eq_map, Finset.image_id]
  rw [List.map_congr_left (g := id) h, List.map_id]

private theorem DRS.map_map_of_forall [DecidableEq W] [DecidableEq X] {g : W → X} {f : V → W}
    {K : DRS L V}
    (h : ∀ c ∈ K.conditions, Condition.map g (Condition.map f c) = Condition.map (g ∘ f) c) :
    DRS.map g (DRS.map f K) = DRS.map (g ∘ f) K := by
  obtain ⟨U, cs⟩ := K
  simp only [DRS.map, Condition.mapList_eq_map, Finset.image_image, List.map_map]
  exact congrArg _ (List.map_congr_left h)

namespace Condition

@[simp] theorem map_id [DecidableEq V] (c : Condition L V) : map id c = c := by
  induction c with
  | atom a => rfl
  | eq u v => rfl
  | neg K ih => exact congrArg neg (DRS.map_id_of_forall ih)
  | imp a c iha ihc =>
    exact congrArg₂ imp (DRS.map_id_of_forall iha) (DRS.map_id_of_forall ihc)
  | dis l r ihl ihr =>
    exact congrArg₂ dis (DRS.map_id_of_forall ihl) (DRS.map_id_of_forall ihr)

theorem map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W)
    (c : Condition L V) : map g (map f c) = map (g ∘ f) c := by
  induction c with
  | atom a => rfl
  | eq u v => rfl
  | neg K ih => exact congrArg neg (DRS.map_map_of_forall ih)
  | imp a c iha ihc =>
    exact congrArg₂ imp (DRS.map_map_of_forall iha) (DRS.map_map_of_forall ihc)
  | dis l r ihl ihr =>
    exact congrArg₂ dis (DRS.map_map_of_forall ihl) (DRS.map_map_of_forall ihr)

end Condition

/-! ### Renaming and extension -/

namespace DRS

theorem extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f g : W → M) :
    (K.map e).Extends f g ↔ K.Extends (f ∘ e) (g ∘ e) := by
  simp only [Box.Extends, referents_map, Function.comp_apply]
  refine ⟨fun h x hx => h (e x) (by simpa using hx), fun h y hy => ?_⟩
  have hx : e.symm y ∉ K.referents := fun hm =>
    hy (by simpa using Finset.mem_image_of_mem e hm)
  simpa using h (e.symm y) hx

theorem exists_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : W → M)
    (P : (V → M) → Prop) :
    (∃ g, (K.map e).Extends f g ∧ P (g ∘ e)) ↔ ∃ g, K.Extends (f ∘ e) g ∧ P g := by
  simp only [extends_map]
  refine ⟨fun ⟨g, hg, hp⟩ => ⟨g ∘ e, hg, hp⟩, fun ⟨g, hg, hp⟩ => ⟨g ∘ e.symm, ?_⟩⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key.symm ▸ ⟨hg, hp⟩

theorem forall_extends_map [DecidableEq W] (e : V ≃ W) (K : DRS L V) (f : W → M)
    (P : (V → M) → Prop) :
    (∀ g, (K.map e).Extends f g → P (g ∘ e)) ↔ ∀ g, K.Extends (f ∘ e) g → P g := by
  simp only [extends_map]
  refine ⟨fun H g hg => ?_, fun H g hg => H (g ∘ e) hg⟩
  have key : (g ∘ e.symm) ∘ e = g := by funext x; simp
  exact key ▸ H (g ∘ e.symm) (key.symm ▸ hg)

@[simp] theorem map_id [DecidableEq V] (K : DRS L V) : map id K = K :=
  map_id_of_forall fun c _ => Condition.map_id c

theorem map_map [DecidableEq W] [DecidableEq X] (g : W → X) (f : V → W) (K : DRS L V) :
    map g (map f K) = map (g ∘ f) K :=
  map_map_of_forall fun c _ => Condition.map_map g f c

end DRS

/-! ### Occurring and free referents -/

variable [DecidableEq V]

mutual
/-- The occurring referents of a DRS are its universe and those of its conditions. -/
def DRS.varFinset : DRS L V → Finset V
  | ⟨U, cs⟩ => U ∪ Condition.varFinsetL cs
/-- Occurring referents (free or bound) in a condition, as a `Finset` — the DRS
analogue of mathlib's `Term.varFinset`. -/
def Condition.varFinset : Condition L V → Finset V
  | .atom a => Finset.image a.args Finset.univ
  | .eq u v => {u, v}
  | .neg K => DRS.varFinset K
  | .imp a c => DRS.varFinset a ∪ DRS.varFinset c
  | .dis l r => DRS.varFinset l ∪ DRS.varFinset r
/-- Occurring referents in a list of conditions. -/
def Condition.varFinsetL : List (Condition L V) → Finset V
  | [] => ∅
  | c :: cs => Condition.varFinset c ∪ Condition.varFinsetL cs
end

mutual
/-- The free discourse referents of a DRS occur in its conditions and are bound neither by its
universe nor by an ancestor reachable "left and up" (the antecedent of a `⇒` threads its
referents into the consequent). `K.freeVarFinset ⊆ b` says every referent of `K` is bound in
context `b`. -/
def DRS.freeVarFinset : DRS L V → Finset V
  | ⟨U, cs⟩ => Condition.freeVarFinsetL cs \ U
/-- The free discourse referents of a condition (Def. 1.4.2); the consequent of a `⇒` also has
the antecedent's universe bound. -/
def Condition.freeVarFinset : Condition L V → Finset V
  | .atom a => Finset.image a.args Finset.univ
  | .eq u v => {u, v}
  | .neg K => DRS.freeVarFinset K
  | .imp a c => DRS.freeVarFinset a ∪ (DRS.freeVarFinset c \ a.referents)
  | .dis l r => DRS.freeVarFinset l ∪ DRS.freeVarFinset r
/-- Free referents of a list of conditions. -/
def Condition.freeVarFinsetL : List (Condition L V) → Finset V
  | [] => ∅
  | c :: cs => Condition.freeVarFinset c ∪ Condition.freeVarFinsetL cs
end

namespace Condition

@[simp] theorem varFinsetL_nil : varFinsetL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem varFinsetL_cons (c : Condition L V) (cs : List (Condition L V)) :
    varFinsetL (c :: cs) = c.varFinset ∪ varFinsetL cs := rfl
@[simp] theorem varFinset_atom (a : L.Atom V) :
    (atom a).varFinset = Finset.image a.args Finset.univ := rfl
@[simp] theorem varFinset_eq (u v : V) : (eq u v : Condition L V).varFinset = {u, v} := rfl
@[simp] theorem varFinset_neg (K : DRS L V) : (neg K).varFinset = K.varFinset := rfl
@[simp] theorem varFinset_imp (a c : DRS L V) :
    (imp a c).varFinset = a.varFinset ∪ c.varFinset := rfl
@[simp] theorem varFinset_dis (l r : DRS L V) :
    (dis l r).varFinset = l.varFinset ∪ r.varFinset := rfl

@[simp] theorem varFinsetL_append (cs ds : List (Condition L V)) :
    varFinsetL (cs ++ ds) = varFinsetL cs ∪ varFinsetL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

theorem varFinset_subset_varFinsetL {c : Condition L V} {cs : List (Condition L V)}
    (hc : c ∈ cs) : c.varFinset ⊆ varFinsetL cs := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with h | h
    · exact h ▸ Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

@[simp] theorem freeVarFinsetL_nil : freeVarFinsetL ([] : List (Condition L V)) = ∅ := rfl
@[simp] theorem freeVarFinsetL_cons (c : Condition L V) (cs : List (Condition L V)) :
    freeVarFinsetL (c :: cs) = c.freeVarFinset ∪ freeVarFinsetL cs := rfl
@[simp] theorem freeVarFinset_atom (a : L.Atom V) :
    (atom a).freeVarFinset = Finset.image a.args Finset.univ := rfl
@[simp] theorem freeVarFinset_eq (u v : V) :
    (eq u v : Condition L V).freeVarFinset = {u, v} := rfl
@[simp] theorem freeVarFinset_neg (K : DRS L V) : (neg K).freeVarFinset = K.freeVarFinset := rfl
@[simp] theorem freeVarFinset_imp (a c : DRS L V) :
    (imp a c).freeVarFinset = a.freeVarFinset ∪ (c.freeVarFinset \ a.referents) := rfl
@[simp] theorem freeVarFinset_dis (l r : DRS L V) :
    (dis l r).freeVarFinset = l.freeVarFinset ∪ r.freeVarFinset := rfl

@[simp] theorem freeVarFinsetL_append (cs ds : List (Condition L V)) :
    freeVarFinsetL (cs ++ ds) = freeVarFinsetL cs ∪ freeVarFinsetL ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Finset.union_assoc]

theorem freeVarFinset_subset_freeVarFinsetL {c : Condition L V} {cs : List (Condition L V)}
    (hc : c ∈ cs) : c.freeVarFinset ⊆ freeVarFinsetL cs := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with h | h
    · exact h ▸ Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

end Condition

namespace DRS

@[simp] theorem varFinset_mk (U : Finset V) (conds : List (Condition L V)) :
    varFinset ⟨U, conds⟩ = U ∪ Condition.varFinsetL conds := rfl

theorem varFinset_eq (K : DRS L V) :
    K.varFinset = K.referents ∪ Condition.varFinsetL K.conditions := by
  cases K; rfl

theorem varFinsetL_subset_varFinset (K : DRS L V) :
    Condition.varFinsetL K.conditions ⊆ K.varFinset := by
  rw [varFinset_eq]; exact Finset.subset_union_right

@[simp] theorem freeVarFinset_mk (U : Finset V) (conds : List (Condition L V)) :
    freeVarFinset ⟨U, conds⟩ = Condition.freeVarFinsetL conds \ U := rfl

theorem freeVarFinset_eq (K : DRS L V) :
    K.freeVarFinset = Condition.freeVarFinsetL K.conditions \ K.referents := by
  cases K; rfl

theorem coe_freeVarFinset (K : DRS L V) :
    (↑K.freeVarFinset : Set V) = ↑(Condition.freeVarFinsetL K.conditions) \ ↑K.referents := by
  rw [freeVarFinset_eq, Finset.coe_sdiff]

theorem freeVarFinset_subset_iff {U X : Finset V} {conds : List (Condition L V)} :
    freeVarFinset ⟨U, conds⟩ ⊆ X ↔ Condition.freeVarFinsetL conds ⊆ X ∪ U := by
  rw [freeVarFinset_mk, sdiff_le_iff, sup_comm, Finset.sup_eq_union]

end DRS

theorem Condition.freeVarFinset_subset_varFinset (c : Condition L V) :
    c.freeVarFinset ⊆ c.varFinset := by
  have box {K : DRS L V} (h : ∀ c ∈ K.conditions, c.freeVarFinset ⊆ c.varFinset) :
      K.freeVarFinset ⊆ K.varFinset := by
    obtain ⟨U, cs⟩ := K
    refine Finset.sdiff_subset.trans (Finset.subset_union_right.trans' ?_)
    induction cs with
    | nil => simp
    | cons d ds ih =>
      exact Finset.union_subset_union (h d (by simp)) (ih fun e he => h e (by simp [he]))
  induction c with
  | atom a => simp
  | eq u v => simp
  | neg K ih => exact box ih
  | imp a c iha ihc =>
    exact Finset.union_subset_union (box iha) (Finset.sdiff_subset.trans (box ihc))
  | dis l r ihl ihr => exact Finset.union_subset_union (box ihl) (box ihr)

theorem DRS.freeVarFinset_subset_varFinset (K : DRS L V) : K.freeVarFinset ⊆ K.varFinset :=
  Condition.freeVarFinset_subset_varFinset (.neg K)

theorem Condition.freeVarFinsetL_subset_varFinsetL (cs : List (Condition L V)) :
    Condition.freeVarFinsetL cs ⊆ Condition.varFinsetL cs := by
  induction cs with
  | nil => simp
  | cons c cs ih => exact Finset.union_subset_union (c.freeVarFinset_subset_varFinset) ih

/-! ### Merge algebra -/

namespace DRS

@[simp] theorem empty_merge (K : DRS L V) : (empty : DRS L V).merge K = K := by
  cases K with
  | mk r c => simp [merge, empty]

@[simp] theorem merge_empty (K : DRS L V) : K.merge (empty : DRS L V) = K := by
  cases K with
  | mk r c => simp [merge, empty]

theorem merge_assoc (K₁ K₂ K₃ : DRS L V) :
    (K₁.merge K₂).merge K₃ = K₁.merge (K₂.merge K₃) := by
  cases K₁; cases K₂; cases K₃
  simp only [merge, referents_mk, conditions_mk]
  rw [Finset.union_assoc, List.append_assoc]

theorem freeVarFinset_merge_subset {X : Finset V} {K₁ K₂ : DRS L V}
    (h₁ : K₁.freeVarFinset ⊆ X) (h₂ : K₂.freeVarFinset ⊆ X ∪ K₁.referents) :
    (K₁.merge K₂).freeVarFinset ⊆ X := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  rw [referents_mk] at h₂
  rw [freeVarFinset_subset_iff] at h₁ h₂
  rw [merge, referents_mk, conditions_mk, freeVarFinset_subset_iff,
    Condition.freeVarFinsetL_append, ← Finset.union_assoc]
  exact Finset.union_subset (h₁.trans Finset.subset_union_left) h₂

/-- A DRS is *proper* iff it has no free discourse referent
(Def. 1.4.2–1.4.3). -/
def IsProper (K : DRS L V) : Prop := K.freeVarFinset = ∅

instance (K : DRS L V) : Decidable K.IsProper :=
  decidable_of_iff (K.freeVarFinset = ∅) Iff.rfl

/-- Merging preserves properness when the increment's free referents are
supplied by the context DRS's universe. -/
theorem isProper_merge {K₁ K₂ : DRS L V} (h₁ : K₁.IsProper)
    (h₂ : K₂.freeVarFinset ⊆ K₁.referents) : (K₁.merge K₂).IsProper :=
  Finset.subset_empty.mp (freeVarFinset_merge_subset (Finset.subset_empty.mpr h₁)
    (h₂.trans Finset.subset_union_right))

end DRS

/-! ### Reuse-freeness

No discourse referent is declared twice along a nesting path: each universe is
fresh for the ambient declarations, threaded through sub-boxes the way
verification threads the base (the antecedent of a `⇒` feeds its referents
into the consequent). This is the hypothesis under which the total
agree-off-universe semantics and the persistence semantics coincide
(`DRS.trueRel_iff_toRelAt` in `DRS/Indexed.lean`). -/

mutual
/-- A DRS is *reuse-free* at ambient declarations `X` when its universe avoids `X` and its
conditions are reuse-free at the grown set. -/
def DRS.ReuseFreeAt (X : Finset V) : DRS L V → Prop
  | ⟨U, cs⟩ => Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) cs
/-- A condition is reuse-free at ambient declarations `X` when each sub-box is, the
consequent of a `⇒` at the declarations grown by the antecedent's universe. -/
def Condition.ReuseFreeAt (X : Finset V) : Condition L V → Prop
  | .atom _ => True
  | .eq _ _ => True
  | .neg K => DRS.ReuseFreeAt X K
  | .imp a c => DRS.ReuseFreeAt X a ∧ DRS.ReuseFreeAt (X ∪ a.referents) c
  | .dis l r => DRS.ReuseFreeAt X l ∧ DRS.ReuseFreeAt X r
/-- Every condition of the list is reuse-free at `X`. -/
def Condition.ReuseFreeAllAt (X : Finset V) : List (Condition L V) → Prop
  | [] => True
  | c :: cs => Condition.ReuseFreeAt X c ∧ Condition.ReuseFreeAllAt X cs
end

namespace Condition

@[simp] theorem reuseFreeAt_atom (X : Finset V) (a : L.Atom V) : ReuseFreeAt X (.atom a) :=
  trivial

@[simp] theorem reuseFreeAt_eq (X : Finset V) (u v : V) :
    ReuseFreeAt X (.eq u v : Condition L V) := trivial

@[simp] theorem reuseFreeAt_neg (X : Finset V) (K : DRS L V) :
    ReuseFreeAt X (.neg K) ↔ K.ReuseFreeAt X := Iff.rfl

@[simp] theorem reuseFreeAt_imp (X : Finset V) (a c : DRS L V) :
    ReuseFreeAt X (.imp a c) ↔ a.ReuseFreeAt X ∧ c.ReuseFreeAt (X ∪ a.referents) := Iff.rfl

@[simp] theorem reuseFreeAt_dis (X : Finset V) (l r : DRS L V) :
    ReuseFreeAt X (.dis l r) ↔ l.ReuseFreeAt X ∧ r.ReuseFreeAt X := Iff.rfl

@[simp] theorem reuseFreeAllAt_nil (X : Finset V) :
    ReuseFreeAllAt X ([] : List (Condition L V)) := trivial

@[simp] theorem reuseFreeAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) :
    ReuseFreeAllAt X (c :: cs) ↔ ReuseFreeAt X c ∧ ReuseFreeAllAt X cs := Iff.rfl

end Condition

@[simp] theorem DRS.reuseFreeAt_mk (X U : Finset V) (conds : List (Condition L V)) :
    DRS.ReuseFreeAt X (.mk U conds) ↔ Disjoint X U ∧ Condition.ReuseFreeAllAt (X ∪ U) conds :=
  Iff.rfl

mutual
/-- Reuse-freeness of a DRS is decidable. -/
@[instance_reducible]
def DRS.decidableReuseFreeAt (X : Finset V) : (K : DRS L V) → Decidable (K.ReuseFreeAt X)
  | ⟨U, cs⟩ => @instDecidableAnd _ _ inferInstance (Condition.decidableReuseFreeAllAt (X ∪ U) cs)
/-- Reuse-freeness of a condition is decidable. -/
@[instance_reducible]
def Condition.decidableReuseFreeAt (X : Finset V) :
    (c : Condition L V) → Decidable (c.ReuseFreeAt X)
  | .atom _ => instDecidableTrue
  | .eq _ _ => instDecidableTrue
  | .neg K => DRS.decidableReuseFreeAt X K
  | .imp a c =>
      @instDecidableAnd _ _ (DRS.decidableReuseFreeAt X a)
        (DRS.decidableReuseFreeAt (X ∪ a.referents) c)
  | .dis l r =>
      @instDecidableAnd _ _ (DRS.decidableReuseFreeAt X l) (DRS.decidableReuseFreeAt X r)
/-- Reuse-freeness of a list of conditions is decidable. -/
@[instance_reducible]
def Condition.decidableReuseFreeAllAt (X : Finset V) :
    (cs : List (Condition L V)) → Decidable (Condition.ReuseFreeAllAt X cs)
  | [] => instDecidableTrue
  | c :: cs =>
      @instDecidableAnd _ _ (Condition.decidableReuseFreeAt X c)
        (Condition.decidableReuseFreeAllAt X cs)
end

attribute [instance] DRS.decidableReuseFreeAt Condition.decidableReuseFreeAt
  Condition.decidableReuseFreeAllAt


end DRT
