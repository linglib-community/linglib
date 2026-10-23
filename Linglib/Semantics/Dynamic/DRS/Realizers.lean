module

public import Linglib.Semantics.Dynamic.DRS.Gluing
public import Linglib.Semantics.Dynamic.DRS.Verification

/-!
# Realizers of basic DRSs

A basic DRS over a context is true under an assignment of the context's referents when each of
its literals holds, and the assignments that make it true are its realizers. Restriction along a
context morphism precomposes assignments, so realizers restrict with the theories they realize,
and the realizers of a theory are the verifying embeddings of its DRS. Gluing becomes a limit: an
assignment realizes the least gluing of a family along a cover exactly when its restrictions
realize the local theories, so the realizers of the gluing are the compatible families of local
realizers.

## Main definitions

* `DRT.Literal.Holds`, `DRT.Theory.realizers`: truth of a literal under an assignment, and the
  realizers of a theory.
* `DRT.Cover.Compatible`: local assignments that agree wherever the cover identifies referents.

## Main statements

* `DRT.Theory.verifies_toDRS_iff`: the realizers of a theory are the verifying embeddings of its
  DRS.
* `DRT.Cover.mem_realizers_iff`: an assignment realizes the least gluing iff its restrictions
  realize the local theories.
* `DRT.Cover.realizersEquiv`: the realizers of the least gluing are the compatible families of
  local realizers.

## Implementation notes

Abramsky and Sadrzadeh leave a sheaf-theoretic semantics of DRSs to future work; this file only
shows that truth is compatible with their gluing.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

@[expose] public section

open CategoryTheory FirstOrder Language Structure

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} {c c' : Context L V}

namespace Literal

variable [L.Structure M]

/-- `l.Holds g` says that the assignment `g` makes `l` true, its atom holding when `l` is
positive and failing when it is negative. -/
def Holds (l : Literal c) (g : c.vars → M) : Prop := RelMap l.rel.1.2 (g ∘ l.args) ↔ l.pos

@[simp] theorem holds_map (f : c ⟶ c') (l : Literal c) (g : c'.vars → M) :
    (l.map f).Holds g ↔ l.Holds (g ∘ f.map) :=
  .rfl

theorem holds_comp_val_iff (l : Literal c) (g : V → M) :
    l.Holds (g ∘ Subtype.val) ↔ (l.atom.Realize g ↔ l.pos) :=
  .rfl

end Literal

namespace Theory

variable [L.Structure M]

variable (M) in
/-- The realizers of a theory are the assignments of the context's referents that make each of its
literals true. -/
def realizers (s : Theory c) : Set (c.vars → M) := {g | ∀ l ∈ s.lits, l.Holds g}

variable {s : Theory c}

theorem mem_realizers {g : c.vars → M} : g ∈ s.realizers M ↔ ∀ l ∈ s.lits, l.Holds g :=
  .rfl

/-- An embedding verifies the DRS of a theory exactly when its restriction to the context's
referents realizes the theory. -/
theorem verifies_toDRS_iff {g : V → M} : Verifies g s.toDRS ↔ g ∘ Subtype.val ∈ s.realizers M := by
  rw [verifies_iff, mem_realizers]
  simp only [toDRS, DRS.conditions_mk, List.mem_map, Finset.mem_toList, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun l _ ↦ ?_
  rw [Literal.holds_comp_val_iff]
  unfold Literal.toCondition
  cases l.pos <;> simp [Box.Extends, ← funext_iff]

theorem comp_val_mem_realizers_iff (hpos : ∀ l ∈ s.lits, l.pos) {g : V → M} :
    g ∘ Subtype.val ∈ s.realizers M ↔
      g ∈ Atom.realizers M (Literal.atom '' (s.lits : Set (Literal c))) := by
  simp only [mem_realizers, Literal.holds_comp_val_iff, Atom.mem_realizers, Set.forall_mem_image,
    Finset.mem_coe]
  exact forall₂_congr fun l hl ↦ by simp [hpos l hl]

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

theorem comp_mem_realizers_restrict {f : c ⟶ c'} {s : Theory c'} {g : c'.vars → M}
    (h : g ∈ s.realizers M) : g ∘ f.map ∈ (s.restrict f).realizers M :=
  fun _ hl ↦ h _ (mem_restrict.1 hl)

end Theory

namespace Cover

variable {ι : Type*} {C : Cover c ι}

variable (C) in
/-- Local assignments are compatible when they agree wherever the cover identifies referents. -/
def Compatible (g : ∀ i, (C.part i).vars → M) : Prop :=
  ∀ i j a b, (C.map i).map a = (C.map j).map b → g i a = g j b

/-- `glueAssignment g` assigns each referent the value a local assignment gives one of its
preimages. -/
noncomputable def glueAssignment (g : ∀ i, (C.part i).vars → M) (t : c.vars) : M :=
  g (C.exists_map_eq t).choose (C.exists_map_eq t).choose_spec.choose

theorem glueAssignment_comp {g : ∀ i, (C.part i).vars → M} (hg : C.Compatible g) (i : ι) :
    glueAssignment g ∘ (C.map i).map = g i :=
  funext fun _ ↦ hg _ _ _ _ (C.exists_map_eq _).choose_spec.choose_spec

variable [L.Structure M] [Fintype ι] [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]
  {x : ∀ i, Theory (C.part i)} {s : Theory c}

/-- An assignment realizes the least gluing of a family exactly when its restriction along every
cover morphism realizes the local theory. -/
theorem mem_realizers_iff (hs : s.lits = C.pushforward x) {g : c.vars → M} :
    g ∈ s.realizers M ↔ ∀ i, g ∘ (C.map i).map ∈ (x i).realizers M := by
  simp only [Theory.mem_realizers, hs, mem_pushforward, forall_exists_index, and_imp]
  exact ⟨fun h i m hm ↦ h _ i m hm rfl, by rintro h _ i m hm rfl; exact h i m hm⟩

/-- The realizers of the least gluing of a family are the compatible families of local
realizers. -/
noncomputable def realizersEquiv (hs : s.lits = C.pushforward x) :
    s.realizers M ≃ {g : ∀ i, (x i).realizers M // C.Compatible fun i ↦ (g i).1} where
  toFun g := ⟨fun i ↦ ⟨g.1 ∘ (C.map i).map, (mem_realizers_iff hs).1 g.2 i⟩,
    fun _ _ _ _ h ↦ congrArg g.1 h⟩
  invFun g := ⟨glueAssignment fun i ↦ (g.1 i).1, (mem_realizers_iff hs).2 fun i ↦ by
    rw [glueAssignment_comp g.2]
    exact (g.1 i).2⟩
  left_inv g := Subtype.ext <| funext fun t ↦
    congrArg g.1 (C.exists_map_eq t).choose_spec.choose_spec
  right_inv g := Subtype.ext <| funext fun i ↦ Subtype.ext (glueAssignment_comp g.2 i)

end Cover

end DRT
