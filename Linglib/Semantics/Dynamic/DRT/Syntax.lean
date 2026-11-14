module

public import Linglib.Core.ModelTheory.Atom
public import Mathlib.Data.Finset.Image

/-!
# Discourse representation structures

A *discourse representation structure* (DRS) pairs a finite set of discourse referents, its
universe, with a list of conditions on them. A condition is atomic, an atom of a
`FirstOrder.Language` or an equation between referents, or complex, a negation, conditional or
disjunction of sub-DRSs, so DRSs and conditions are defined by simultaneous recursion. This file
defines both, together with their syntactic theory: merge, renaming, occurring and free referents,
and properness.

## Main definitions

* `DRT.DRS`, `DRT.Condition`: DRSs and conditions over a language `L` and referent type `V`.
* `DRT.DRS.merge`, `DRT.DRS.map`: the merge of two DRSs, and renaming along `f : V → W`.
* `DRT.DRS.varFinset`, `DRT.DRS.freeVarFinset`: occurring and free referents.
* `DRT.DRS.IsProper`: no free referent.

## Implementation notes

* `DRS` is a `structure` in a mutual block with `Condition`, since Kamp and Reyle define the two
  by simultaneous recursion. Being recursive, it has no definitional eta, so a proof about a
  variable DRS that must unfold a recursive definition starts from `cases K`.
* `referents` is the textbook universe `U`: `universe` is a Lean keyword and `univ` collides with
  `Finset.univ`. `conditions` is a `List`, since an inductive cannot nest through `Finset` or
  `Multiset`; set semantics is recovered by the interpretation (`verifiesTotal_perm`).
* Renaming and occurring and free referents are each three mutually recursive functions, on DRSs,
  conditions and condition lists, by structural recursion through the nesting, so the kernel
  evaluates them and `decide` settles them on concrete DRSs.
* `DRT` is the owning namespace, on the `FirstOrder.Language` pattern.

## References

* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x} {X : Type*}

mutual

/-- A discourse representation structure pairs a universe of discourse referents, the objects
under discussion, with the conditions that record what has been said of them. These are the
finite DRSs of Def. 1.5.1. Def. 1.4.1 lets both components be infinite, which Kamp and Reyle set
aside for the rest of the volume (p. 128). -/
@[ext] structure DRS (L : Language.{u, v}) (V : Type w) where
  /-- The universe `U`: the discourse referents the DRS introduces. -/
  referents : Finset V
  /-- The conditions of the DRS. -/
  conditions : List (Condition L V)

/-- A DRS-condition is atomic, an atom or an equation, or complex, a negation (Def. 1.4.1) or a
conditional or disjunction (Chapter 2). Sub-DRSs occur only inside complex conditions. -/
inductive Condition (L : Language.{u, v}) (V : Type w) where
  /-- The atomic condition of an atom over the referents. -/
  | atom (a : L.Atom V)
  /-- Atomic equality condition `u = v`. -/
  | eq (u v : V)
  /-- Complex condition `¬K`. -/
  | neg (K : DRS L V)
  /-- Complex condition `K₁ ⇒ K₂` (antecedent ⇒ consequent). -/
  | imp (ante cons : DRS L V)
  /-- Complex condition `K₁ ∨ K₂`. -/
  | dis (left right : DRS L V)

end

namespace DRS

/-- The empty DRS `⟨∅, []⟩`. -/
def empty : DRS L V := .mk ∅ []

instance : Inhabited (DRS L V) := ⟨empty⟩

/-- The merge `K₁ ⊕ K₂` unions the referents and appends the conditions —
[muskens-1996]'s compositional operation (Kamp & Reyle combine DRSs
incrementally via the construction algorithm instead). An operation, not a
syntactic constructor. -/
def merge [DecidableEq V] (K₁ K₂ : DRS L V) : DRS L V :=
  .mk (K₁.referents ∪ K₂.referents) (K₁.conditions ++ K₂.conditions)

@[simp] theorem referents_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).referents = K₁.referents ∪ K₂.referents := rfl

@[simp] theorem conditions_merge [DecidableEq V] (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).conditions = K₁.conditions ++ K₂.conditions := rfl

end DRS

@[induction_eliminator] theorem Condition.induction {motive : Condition L V → Prop}
    (atom : ∀ a, motive (.atom a))
    (eq : ∀ u v, motive (.eq u v))
    (neg : ∀ K, (∀ c ∈ K.conditions, motive c) → motive (.neg K))
    (imp : ∀ a c, (∀ d ∈ a.conditions, motive d) → (∀ d ∈ c.conditions, motive d) →
      motive (.imp a c))
    (dis : ∀ l r, (∀ d ∈ l.conditions, motive d) → (∀ d ∈ r.conditions, motive d) →
      motive (.dis l r)) (c : Condition L V) : motive c :=
  Condition.rec (motive_1 := fun K => ∀ c ∈ K.conditions, motive c)
    (motive_3 := fun cs => ∀ c ∈ cs, motive c) (fun _ _ h => h) atom eq neg imp dis
    (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ hd hds _ he => (List.mem_cons.1 he).elim (· ▸ hd) (hds _)) c

/-- A condition is atomic when it is an atom or an equation (Def. 1.4.1). -/
inductive Condition.IsAtomic : Condition L V → Prop
  | atom (a : L.Atom V) : Condition.IsAtomic (.atom a)
  | eq (u v : V) : Condition.IsAtomic (.eq u v)

instance : DecidablePred (Condition.IsAtomic : Condition L V → Prop)
  | .atom a => isTrue (.atom a)
  | .eq u v => isTrue (.eq u v)
  | .neg _ | .imp _ _ | .dis _ _ => isFalse nofun

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

namespace DRS

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

theorem freeVarFinsetL_subset_iff {cs : List (Condition L V)} {S : Finset V} :
    freeVarFinsetL cs ⊆ S ↔ ∀ c ∈ cs, c.freeVarFinset ⊆ S := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [Finset.union_subset_iff, ih]

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

theorem referents_subset_varFinset (K : DRS L V) : K.referents ⊆ K.varFinset := by
  rw [varFinset_eq]; exact Finset.subset_union_left

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

theorem freeVarFinset_subset_iff {K : DRS L V} {X : Finset V} :
    K.freeVarFinset ⊆ X ↔ Condition.freeVarFinsetL K.conditions ⊆ X ∪ K.referents := by
  rw [freeVarFinset_eq, sdiff_le_iff, sup_comm, Finset.sup_eq_union]

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

@[simp] theorem empty_merge (K : DRS L V) : (empty : DRS L V).merge K = K :=
  DRS.ext (Finset.empty_union _) (List.nil_append _)

@[simp] theorem merge_empty (K : DRS L V) : K.merge (empty : DRS L V) = K :=
  DRS.ext (Finset.union_empty _) (List.append_nil _)

theorem merge_assoc (K₁ K₂ K₃ : DRS L V) :
    (K₁.merge K₂).merge K₃ = K₁.merge (K₂.merge K₃) :=
  DRS.ext (Finset.union_assoc _ _ _) (List.append_assoc _ _ _)

theorem freeVarFinset_merge_subset {X : Finset V} {K₁ K₂ : DRS L V}
    (h₁ : K₁.freeVarFinset ⊆ X) (h₂ : K₂.freeVarFinset ⊆ X ∪ K₁.referents) :
    (K₁.merge K₂).freeVarFinset ⊆ X := by
  rw [freeVarFinset_subset_iff] at h₁ h₂ ⊢
  rw [conditions_merge, referents_merge, Condition.freeVarFinsetL_append, ← Finset.union_assoc]
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

end DRT
