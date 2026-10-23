module

public import Linglib.Semantics.Dynamic.DRS.Basic
public import Linglib.Semantics.Dynamic.DRS.Dynamics
public import Linglib.Semantics.Dynamic.Transition

/-!
# Indexed relational semantics of DRSs

This file defines the base-threaded verification semantics: `toRelAt X K f g`
holds when the output `g` agrees with the input `f` on the context base `X`
and verifies `K`'s conditions, sub-boxes entered at the grown base. This is
the total-assignment rendering of the partial-embedding semantics of Kamp, van Genabith and
Reyle (Defs. 19, 22, 24): values at established referents persist, as in Kamp and Reyle's
original embeddings, in contrast to the flat `DRS.toRel` (`DRS/Dynamics.lean`), which freely
reassigns re-declared referents (Muskens's fn. 4).

Persistence types the semantics: `toRelAt X K` is read only at `X` and, given
the referential presupposition `K.freeVarFinset ⊆ X`, written only at `X ∪ U`,
so a well-formed DRS denotes a spine transition `Transition X (X ∪ U)` and a
proper DRS expresses an information state by acting on the initial state `⊤` (Def. 22). The
Merging Lemma here needs less than the flat freshness hypothesis — only
capture by sub-box universes is fatal, re-declaration is harmless — and lifts
to the spine, where the action equation is an instance of functoriality
(`Transition.apply_comp`).

## Main declarations

* `DRS.toRelAt`, `Condition.holdsAt`: the base-threaded semantics.
* `DRS.toRelAt_congr_left`, `DRS.toRelAt_congr_right`: read/write support.
* `DRS.transition`: a DRS as a spine transition `X ⟶ X ∪ U`.
* `DRS.state`: the information state a proper DRS expresses.
* `DRS.transition_merge`, `DRS.state_merge`: the Merging Lemma on the spine
  and the action equation.
* `DRS.trueRel_iff_toRelAt`: on reuse-free DRSs the flat and indexed
  semantics have the same truth conditions.

## References

* [kamp-vangenabith-reyle-2011]
* [kamp-reyle-1993]
* [muskens-1996]
-/

@[expose] public section

open FirstOrder FirstOrder.Language
open DynamicSemantics

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {M : Type x} [L.Structure M]
variable [DecidableEq V]

/-! ### The base-threaded semantics -/

mutual
/-- In the base-threaded relational semantics (Def. 19 in total-assignment form) the output
agrees with the input on the base, so that established referents persist, and verifies the
conditions, with sub-boxes entered at the grown base. -/
def DRS.toRelAt (X : Finset V) : DRS L V → (V → M) → (V → M) → Prop
  | .mk U conds => fun f g => Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g
/-- A condition holds at a base under an assignment; sub-DRSs are entered as
context extensions of the current base. -/
def Condition.holdsAt (X : Finset V) : Condition L V → (V → M) → Prop
  | .atom a => a.Realize
  | .eq u v => fun g => g u = g v
  | .neg K => fun g => ¬ ∃ g', DRS.toRelAt X K g g'
  | .imp a c => fun g => ∀ g', DRS.toRelAt X a g g' →
      ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g''
  | .dis l r => fun g => ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g'
/-- Every condition in the list holds at the base. A `List` helper — the
higher-order form fails the nested-inductive structural-recursion checker. -/
def Condition.holdsAllAt (X : Finset V) : List (Condition L V) → (V → M) → Prop
  | [] => fun _ => True
  | c :: cs => fun g => Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g
end

/-! ### Structural simp API -/

@[simp] theorem DRS.toRelAt_mk (X U : Finset V) (conds : List (Condition L V))
    (f g : V → M) :
    DRS.toRelAt X (.mk U conds) f g ↔
      Set.EqOn g f ↑X ∧ Condition.holdsAllAt (X ∪ U) conds g := Iff.rfl

@[simp] theorem Condition.holdsAt_atom (X : Finset V) (a : L.Atom V) (g : V → M) :
    (Condition.atom a).holdsAt X g ↔ a.Realize g :=
  .rfl

@[simp] theorem Condition.holdsAt_eq (X : Finset V) (u v : V) (g : V → M) :
    (Condition.eq u v : Condition L V).holdsAt X g ↔ g u = g v := Iff.rfl

@[simp] theorem Condition.holdsAt_neg (X : Finset V) (K : DRS L V) (g : V → M) :
    (Condition.neg K).holdsAt X g ↔ ¬ ∃ g', DRS.toRelAt X K g g' := Iff.rfl

@[simp] theorem Condition.holdsAt_imp (X : Finset V) (a c : DRS L V) (g : V → M) :
    (Condition.imp a c).holdsAt X g ↔
      ∀ g', DRS.toRelAt X a g g' →
        ∃ g'', DRS.toRelAt (X ∪ a.referents) c g' g'' := Iff.rfl

@[simp] theorem Condition.holdsAt_dis (X : Finset V) (l r : DRS L V) (g : V → M) :
    (Condition.dis l r).holdsAt X g ↔
      ∃ g', DRS.toRelAt X l g g' ∨ DRS.toRelAt X r g g' := Iff.rfl

@[simp] theorem Condition.holdsAllAt_nil (X : Finset V) (g : V → M) :
    Condition.holdsAllAt X ([] : List (Condition L V)) g := trivial

@[simp] theorem Condition.holdsAllAt_cons (X : Finset V) (c : Condition L V)
    (cs : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (c :: cs) g ↔
      Condition.holdsAt X c g ∧ Condition.holdsAllAt X cs g := Iff.rfl

/-! ### Read and write support

The indexed clauses only mention the input through the agreement conjunct, so
read-support is one line — the flat semantics' piecewise witness surgery
disappears. Write-support needs the referential presupposition `freeVarFinset ⊆ X`
only at the atomic clauses. -/

/-- `toRelAt X K` reads its input only at `X`. -/
theorem DRS.toRelAt_congr_left (X : Finset V) (K : DRS L V) {f f' g : V → M}
    (h : Set.EqOn f f' ↑X) : DRS.toRelAt X K f g ↔ DRS.toRelAt X K f' g := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.toRelAt_mk]
  exact and_congr_left fun _ => ⟨fun he => he.trans h, fun he => he.trans h.symm⟩

theorem Condition.holdsAt_congr {X : Finset V} (c : Condition L V)
    (hfv : c.freeVarFinset ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAt X c g ↔ Condition.holdsAt X c g' := by
  match c with
  | .atom a =>
    simp only [Condition.holdsAt_atom, Atom.Realize]
    rw [show g ∘ a.args = g' ∘ a.args from
      funext fun i => hgg' (Finset.mem_coe.mpr (hfv (by simp)))]
  | .eq u v =>
    simp only [Condition.holdsAt_eq]
    rw [hgg' (Finset.mem_coe.mpr (hfv (by simp [Condition.freeVarFinset_eq]))),
      hgg' (Finset.mem_coe.mpr (hfv (by simp [Condition.freeVarFinset_eq])))]
  | .neg K =>
    simp only [Condition.holdsAt_neg]
    exact not_congr (exists_congr fun k => DRS.toRelAt_congr_left X K hgg')
  | .imp a c =>
    simp only [Condition.holdsAt_imp]
    exact forall_congr' fun g₁ =>
      imp_congr (DRS.toRelAt_congr_left X a hgg') Iff.rfl
  | .dis l r =>
    simp only [Condition.holdsAt_dis]
    exact exists_congr fun k =>
      or_congr (DRS.toRelAt_congr_left X l hgg') (DRS.toRelAt_congr_left X r hgg')

theorem Condition.holdsAllAt_congr {X : Finset V} (cs : List (Condition L V))
    (hfv : Condition.freeVarFinsetL cs ⊆ X) {g g' : V → M} (hgg' : Set.EqOn g g' ↑X) :
    Condition.holdsAllAt X cs g ↔ Condition.holdsAllAt X cs g' := by
  induction cs with
  | nil => exact Iff.rfl
  | cons c cs ih =>
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    simp only [Condition.holdsAllAt_cons]
    exact and_congr (Condition.holdsAt_congr c hfv.1 hgg') (ih hfv.2)

/-- `toRelAt X K` writes its output only at `X ∪ U`, given the referential
presupposition `K.freeVarFinset ⊆ X`. -/
theorem DRS.toRelAt_congr_right {X : Finset V} (K : DRS L V) (hfv : K.freeVarFinset ⊆ X)
    {f g g' : V → M} (hgg' : Set.EqOn g g' ↑(X ∪ K.referents)) :
    DRS.toRelAt X K f g ↔ DRS.toRelAt X K f g' := by
  obtain ⟨U, conds⟩ := K
  rw [DRS.referents_mk] at hgg'
  have hX : Set.EqOn g g' ↑X := hgg'.mono (by simp)
  simp only [DRS.toRelAt_mk]
  exact and_congr
    ⟨fun he => hX.symm.trans he, fun he => hX.trans he⟩
    (Condition.holdsAllAt_congr conds (DRS.freeVarFinset_subset_iff.mp hfv) hgg')

/-! ### A DRS as a spine transition -/

/-- A well-formed DRS denotes a transition from its context base to the base grown by its universe,
given the referential presupposition (Def. 27(i)). -/
theorem DRS.readsAt_toRelAt {W : Type*} (X : Finset V) (K : DRS L V) :
    Transition.ReadsAt (W := W) ↑X fun _ => DRS.toRelAt (M := M) X K :=
  fun _ _ _ _ h => DRS.toRelAt_congr_left X K h

theorem DRS.writesAt_toRelAt {W : Type*} {X : Finset V} (K : DRS L V)
    (hK : K.freeVarFinset ⊆ X) :
    Transition.WritesAt (W := W) ↑(X ∪ K.referents)
      fun _ => DRS.toRelAt (M := M) X K :=
  fun _ _ _ _ h => DRS.toRelAt_congr_right K hK h

/-- A well-formed DRS is a transition, read at `X` and written at `X ∪ U`, through the
total–typed bridge. The referential presupposition documents Def. 24's domain condition, and
the congruence lemmas above are the bridge's support hypotheses. -/
def DRS.transition (W : Type*) (K : DRS L V) (X : Finset V)
    (_hK : K.freeVarFinset ⊆ X) :
    Transition W M (↑X : Set V) (↑(X ∪ K.referents) : Set V) :=
  Transition.ofTotal (Finset.coe_subset.mpr Finset.subset_union_left)
    fun _ => DRS.toRelAt X K

theorem DRS.transition_empty [Nonempty M] (W : Type*) (X : Finset V)
    (h : (DRS.empty : DRS L V).freeVarFinset ⊆ X)
    (he : X ∪ (DRS.empty : DRS L V).referents = X) :
    (DRS.empty.transition (M := M) W X h).copy rfl (Finset.coe_inj.mpr he) =
      Transition.id (↑X : Set V) := by
  unfold DRS.transition
  rw [Transition.ofTotal_copy]
  apply Transition.ext
  funext w e e'
  apply propext
  constructor
  · rintro ⟨f, g, rfl, rfl, hfg, -⟩
    exact funext fun v => (hfg v.2).symm
  · rintro rfl
    refine ⟨fun v => if hv : v ∈ (↑X : Set V) then e ⟨v, hv⟩
      else Classical.arbitrary M, fun v => if hv : v ∈ (↑X : Set V) then e ⟨v, hv⟩
      else Classical.arbitrary M, funext fun v => dite_eq_left v.2,
      funext fun v => dite_eq_left v.2, fun v _ => rfl, trivial⟩

theorem DRS.transition_isExtension (W : Type*) (K : DRS L V) (X : Finset V)
    (hK : K.freeVarFinset ⊆ X) : (K.transition (M := M) W X hK).IsExtension := by
  rintro w e e' ⟨f, g, rfl, rfl, hrel⟩
  obtain ⟨U, conds⟩ := K
  funext v
  exact (hrel.1 v.2).symm

theorem DRS.transition_copy (W : Type*) {X X' : Finset V} (K : DRS L V)
    (hX : X = X') (hK : K.freeVarFinset ⊆ X) (hK' : K.freeVarFinset ⊆ X') :
    (K.transition (M := M) W X hK).copy (Finset.coe_inj.mpr hX) (by rw [hX]) =
      K.transition W X' hK' := by
  subst hX; rfl

/-- A proper DRS expresses the information state it produces from the initial state (Def. 22).
-/
def DRS.state (W : Type*) (K : DRS L V) (hK : K.IsProper) : State W V M :=
  (K.transition W ∅ (Finset.subset_empty.mpr hK)).applyState ⊤

theorem DRS.uniformAt_state (W : Type*) (K : DRS L V) (hK : K.IsProper) :
    State.UniformAt ↑K.referents (K.state (M := M) W hK) := by
  have h := Transition.uniformAt_applyState
    (K.transition (M := M) W ∅ (Finset.subset_empty.mpr hK)) ⊤
  simpa [DRS.state] using h

theorem DRS.mem_state {W : Type*} {K : DRS L V} {hK : K.IsProper}
    {q : Possibility W V (Flat M)} :
    q ∈ K.state W hK ↔ q.domain = (↑(∅ ∪ K.referents) : Set V) ∧
      ∃ f g : V → M, DRS.toRelAt ∅ K f g ∧
        ∀ v : (↑(∅ ∪ K.referents) : Set V), q.assignment v.1 = ↑(g v.1) := by
  constructor
  · rintro ⟨hq, p, hpI, hp, hw, e, e', he, he', f, g, hf, hg, hrel⟩
    refine ⟨hq, f, g, hrel, fun v => ?_⟩
    have hv := he' v
    rw [← hg] at hv
    exact hv
  · rintro ⟨hq, f, g, hrel, hvals⟩
    refine ⟨hq, ⟨q.world, fun _ => ⊥⟩, ⟨q.world, rfl⟩, ?_, rfl,
      (↑(∅ : Finset V) : Set V).domRestrict f,
      (↑(∅ ∪ K.referents) : Set V).domRestrict g,
      fun v => absurd v.2 (by simp), fun v => hvals v, f, g, rfl, rfl, hrel⟩
    ext v
    exact iff_of_false (fun h => h rfl) (by simp)

/-! ### Base invariance

A fresh extension of the base is invisible to a well-formed condition. The
only fatal interference is *capture* — a fresh referent colliding with a
sub-box universe would freeze a previously local existential — so the
hypothesis is disjointness from the occurring referents. Re-declaration of
base referents needs no exclusion: persistence makes it inert. -/

@[simp] theorem Condition.holdsAllAt_append (X : Finset V)
    (cs ds : List (Condition L V)) (g : V → M) :
    Condition.holdsAllAt X (cs ++ ds) g ↔
      Condition.holdsAllAt X cs g ∧ Condition.holdsAllAt X ds g := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, and_assoc]

private theorem DRS.toRelAt_adjust {X Δ U : Finset V} {conds : List (Condition L V)}
    (hΔU : Disjoint Δ U) (hfvc : Condition.freeVarFinsetL conds ⊆ X ∪ U)
    (hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g k : V → M} (hk : DRS.toRelAt X (.mk U conds) g k) :
    DRS.toRelAt (X ∪ Δ) (.mk U conds) g (fun x => if x ∈ Δ then g x else k x) ∧
      Set.EqOn (fun x => if x ∈ Δ then g x else k x) k ↑(X ∪ U) := by
  obtain ⟨hag, hh⟩ := hk
  have hkk' : Set.EqOn (fun x => if x ∈ Δ then g x else k x) k ↑(X ∪ U) := by
    intro x hx
    by_cases hxΔ : x ∈ Δ
    · have hxU : x ∉ U := Finset.disjoint_left.mp hΔU hxΔ
      have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxU
      simp only [ite_eq_left hxΔ]
      exact (hag (Finset.mem_coe.mpr hxX)).symm
    · simp only [ite_eq_right hxΔ]
  refine ⟨⟨?_, ?_⟩, hkk'⟩
  · intro x hx
    by_cases hxΔ : x ∈ Δ
    · simp only [ite_eq_left hxΔ]
    · have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxΔ
      simp only [ite_eq_right hxΔ]
      exact hag (Finset.mem_coe.mpr hxX)
  · rw [Finset.union_right_comm]
    exact (hIH _).mpr ((Condition.holdsAllAt_congr conds hfvc hkk'.symm).mp hh)

private theorem DRS.toRelAt_down {X Δ U : Finset V} {conds : List (Condition L V)}
    (hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g k : V → M} (hk : DRS.toRelAt (X ∪ Δ) (.mk U conds) g k) :
    DRS.toRelAt X (.mk U conds) g k := by
  obtain ⟨hag, hh⟩ := hk
  refine ⟨hag.mono (Finset.coe_subset.mpr Finset.subset_union_left), ?_⟩
  rw [Finset.union_right_comm] at hh
  exact (hIH k).mp hh

mutual
theorem Condition.holdsAt_union_fresh {X Δ : Finset V} (c : Condition L V)
    (hocc : Disjoint Δ c.varFinset) (hfv : c.freeVarFinset ⊆ X) (g : V → M) :
    Condition.holdsAt (X ∪ Δ) c g ↔ Condition.holdsAt X c g := by
  match c with
  | .atom a => exact Iff.rfl
  | .eq u v => exact Iff.rfl
  | .neg K =>
    obtain ⟨U, conds⟩ := K
    simp only [Condition.varFinset_neg, DRS.varFinset_mk] at hocc
    rw [Condition.freeVarFinset_neg] at hfv
    obtain ⟨hΔU, hΔc⟩ := Finset.disjoint_union_right.mp hocc
    have hfvc : Condition.freeVarFinsetL conds ⊆ X ∪ U := DRS.freeVarFinset_subset_iff.mp hfv
    have hIH : ∀ k : V → M, Condition.holdsAllAt ((X ∪ U) ∪ Δ) conds k ↔
        Condition.holdsAllAt (X ∪ U) conds k :=
      fun k => Condition.holdsAllAt_union_fresh conds hΔc hfvc k
    simp only [Condition.holdsAt_neg]
    exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_down hIH hk⟩,
      fun ⟨k, hk⟩ => ⟨_, (DRS.toRelAt_adjust hΔU hfvc hIH hk).1⟩⟩
  | .imp a c' =>
    obtain ⟨Ua, ca⟩ := a
    obtain ⟨Uc, cc⟩ := c'
    simp only [Condition.varFinset_imp, DRS.varFinset_mk] at hocc
    obtain ⟨ha, hc⟩ := Finset.disjoint_union_right.mp hocc
    obtain ⟨hΔUa, hΔca⟩ := Finset.disjoint_union_right.mp ha
    obtain ⟨hΔUc, hΔcc⟩ := Finset.disjoint_union_right.mp hc
    rw [Condition.freeVarFinset_imp, Finset.union_subset_iff] at hfv
    obtain ⟨hfva, hfvc'⟩ := hfv
    have hfvca : Condition.freeVarFinsetL ca ⊆ X ∪ Ua := DRS.freeVarFinset_subset_iff.mp hfva
    have hfvcc : Condition.freeVarFinsetL cc ⊆ (X ∪ Ua) ∪ Uc := by
      intro x hx
      by_cases hxUc : x ∈ Uc
      · exact Finset.mem_union_right _ hxUc
      · by_cases hxUa : x ∈ Ua
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxUa)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (hfvc' ?_))
          rw [DRS.freeVarFinset_mk, DRS.referents_mk, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨⟨hx, hxUc⟩, hxUa⟩
    have hIHa : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ua) ∪ Δ) ca k ↔
        Condition.holdsAllAt (X ∪ Ua) ca k :=
      fun k => Condition.holdsAllAt_union_fresh ca hΔca hfvca k
    have hIHc : ∀ k : V → M, Condition.holdsAllAt (((X ∪ Ua) ∪ Uc) ∪ Δ) cc k ↔
        Condition.holdsAllAt ((X ∪ Ua) ∪ Uc) cc k :=
      fun k => Condition.holdsAllAt_union_fresh cc hΔcc hfvcc k
    simp only [Condition.holdsAt_imp]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨hadj, heq⟩ := DRS.toRelAt_adjust hΔUa hfvca hIHa hg₁
      obtain ⟨g₂, hg₂⟩ := hL _ hadj
      rw [Finset.union_right_comm] at hg₂
      refine ⟨g₂, (DRS.toRelAt_congr_left (X ∪ Ua) _ heq).mp ?_⟩
      exact DRS.toRelAt_down hIHc hg₂
    · intro hR g₁ hg₁
      obtain ⟨g₂, hg₂⟩ := hR g₁ (DRS.toRelAt_down hIHa hg₁)
      have hadj := (DRS.toRelAt_adjust hΔUc hfvcc hIHc hg₂).1
      rw [Finset.union_right_comm] at hadj
      exact ⟨_, hadj⟩
  | .dis l r =>
    obtain ⟨Ul, cl⟩ := l
    obtain ⟨Ur, cr⟩ := r
    simp only [Condition.varFinset_dis, DRS.varFinset_mk] at hocc
    obtain ⟨hl, hr⟩ := Finset.disjoint_union_right.mp hocc
    obtain ⟨hΔUl, hΔcl⟩ := Finset.disjoint_union_right.mp hl
    obtain ⟨hΔUr, hΔcr⟩ := Finset.disjoint_union_right.mp hr
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    obtain ⟨hfvl, hfvr⟩ := hfv
    have hfvcl : Condition.freeVarFinsetL cl ⊆ X ∪ Ul := DRS.freeVarFinset_subset_iff.mp hfvl
    have hfvcr : Condition.freeVarFinsetL cr ⊆ X ∪ Ur := DRS.freeVarFinset_subset_iff.mp hfvr
    have hIHl : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ul) ∪ Δ) cl k ↔
        Condition.holdsAllAt (X ∪ Ul) cl k :=
      fun k => Condition.holdsAllAt_union_fresh cl hΔcl hfvcl k
    have hIHr : ∀ k : V → M, Condition.holdsAllAt ((X ∪ Ur) ∪ Δ) cr k ↔
        Condition.holdsAllAt (X ∪ Ur) cr k :=
      fun k => Condition.holdsAllAt_union_fresh cr hΔcr hfvcr k
    simp only [Condition.holdsAt_dis]
    constructor
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl (DRS.toRelAt_down hIHl hk)⟩
      · exact ⟨k, Or.inr (DRS.toRelAt_down hIHr hk)⟩
    · rintro ⟨k, hk | hk⟩
      · exact ⟨_, Or.inl (DRS.toRelAt_adjust hΔUl hfvcl hIHl hk).1⟩
      · exact ⟨_, Or.inr (DRS.toRelAt_adjust hΔUr hfvcr hIHr hk).1⟩
theorem Condition.holdsAllAt_union_fresh {X Δ : Finset V}
    (cs : List (Condition L V)) (hocc : Disjoint Δ (Condition.varFinsetL cs))
    (hfv : Condition.freeVarFinsetL cs ⊆ X) (g : V → M) :
    Condition.holdsAllAt (X ∪ Δ) cs g ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => exact Iff.rfl
  | c :: cs =>
    simp only [Condition.varFinsetL] at hocc
    obtain ⟨hc, hcs⟩ := Finset.disjoint_union_right.mp hocc
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    simp only [Condition.holdsAllAt_cons]
    exact and_congr (Condition.holdsAt_union_fresh c hc hfv.1 g)
      (Condition.holdsAllAt_union_fresh cs hcs hfv.2 g)
end

/-! ### The Merging Lemma and the action equation -/

theorem DRS.toRelAt_merge {X : Finset V} (K₁ K₂ : DRS L V) (h₁ : K₁.freeVarFinset ⊆ X)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions)) :
    (DRS.toRelAt X (K₁.merge K₂) : (V → M) → (V → M) → Prop) =
      Relation.Comp (DRS.toRelAt X K₁) (DRS.toRelAt (X ∪ K₁.referents) K₂) := by
  obtain ⟨U₁, c₁⟩ := K₁
  obtain ⟨U₂, c₂⟩ := K₂
  have hfvc₁ := DRS.freeVarFinset_subset_iff.mp h₁
  funext f g
  apply propext
  simp only [DRS.merge, DRS.toRelAt_mk,
    Condition.holdsAllAt_append, Relation.Comp]
  rw [← Finset.union_assoc]
  constructor
  · rintro ⟨hag, hh₁, hh₂⟩
    exact ⟨g, ⟨hag, (Condition.holdsAllAt_union_fresh c₁ hfresh hfvc₁ g).mp hh₁⟩,
      Set.eqOn_refl g _, hh₂⟩
  · rintro ⟨h, ⟨hhf, hh₁⟩, hgh, hh₂⟩
    exact ⟨(hgh.mono (Finset.coe_subset.mpr Finset.subset_union_left)).trans hhf,
      (Condition.holdsAllAt_union_fresh c₁ hfresh hfvc₁ g).mpr
        ((Condition.holdsAllAt_congr c₁ hfvc₁ hgh).mpr hh₁), hh₂⟩

/-- Sequencing the transitions of two DRSs gives the merge's transition, repackaged along the
associativity of the grown bases. -/
theorem DRS.transition_merge (W : Type*) {X : Finset V} (K₁ K₂ : DRS L V)
    (h₁ : K₁.freeVarFinset ⊆ X) (h₂ : K₂.freeVarFinset ⊆ X ∪ K₁.referents)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions)) :
    (K₁.transition (M := M) W X h₁).comp (K₂.transition W (X ∪ K₁.referents) h₂) =
      ((K₁.merge K₂).transition W X (DRS.freeVarFinset_merge_subset h₁ h₂)).copy rfl
        (by rw [DRS.referents_merge, ← Finset.union_assoc]) := by
  unfold DRS.transition
  rw [Transition.ofTotal_comp (DRS.readsAt_toRelAt (X ∪ K₁.referents) K₂),
    Transition.ofTotal_copy]
  exact Transition.ofTotal_congr _ _
    (funext fun _ => (DRS.toRelAt_merge K₁ K₂ h₁ hfresh).symm)

/-- Applying a DRS's transition to the state of a proper context DRS yields the state of their merge
(the action equation, p. 159). -/
theorem DRS.state_merge (W : Type*) (K₁ K₂ : DRS L V) (h₁ : K₁.IsProper)
    (h₂ : K₂.freeVarFinset ⊆ K₁.referents)
    (hfresh : Disjoint K₂.referents (Condition.varFinsetL K₁.conditions)) :
    (K₂.transition (M := M) W K₁.referents h₂).applyState (K₁.state W h₁) =
      (K₁.merge K₂).state W (DRS.isProper_merge h₁ h₂) := by
  simp only [DRS.state]
  rw [← DRS.transition_copy (M := M) W K₂ (Finset.empty_union _)
      (h₂.trans Finset.subset_union_right) h₂,
    Transition.applyState_copy, ← Transition.applyState_comp,
    DRS.transition_merge (M := M) W K₁ K₂ (Finset.subset_empty.mpr h₁)
      (h₂.trans Finset.subset_union_right) hfresh,
    Transition.applyState_copy]

/-! ### Reconciliation with the flat semantics

On reuse-free DRSs (`DRS.ReuseFreeAt`, `DRS/Basic.lean`) the flat
agree-off-universe semantics (`DRS.toRel`, `DRS/Dynamics.lean`) and the indexed
persistence semantics coincide at truth level: every flat output is a indexed
output, and a indexed output repairs, off the grown base, into a flat one.
Reuse-freeness is needed — on a DRS that re-declares a referent the two
diverge (Muskens's fn. 4; witness in `Studies/Muskens1996.lean`). -/

private theorem DRS.toRelAt_of_toRel' {X U : Finset V} {conds : List (Condition L V)}
    (hXU : Disjoint X U)
    (hIH : ∀ k : V → M, (∀ c ∈ conds, VerifiesCondition k c) ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g g' : V → M}
    (h : Box.Extends (⟨U, conds⟩ : DRS L V) g g' ∧ Verifies g' (⟨U, conds⟩ : DRS L V)) :
    DRS.toRelAt X (.mk U conds) g g' := by
  obtain ⟨hag, hh⟩ := h
  exact ⟨fun x hx => hag x (Finset.disjoint_left.mp hXU (Finset.mem_coe.mp hx)),
    (hIH g').mp (verifies_mk U conds |>.mp hh)⟩

private theorem DRS.toRel_of_toRelAt' {X U : Finset V} {conds : List (Condition L V)}
    (hfvc : Condition.freeVarFinsetL conds ⊆ X ∪ U)
    (hIH : ∀ k : V → M, (∀ c ∈ conds, VerifiesCondition k c) ↔
      Condition.holdsAllAt (X ∪ U) conds k)
    {g g' : V → M} (h : DRS.toRelAt X (.mk U conds) g g') :
    (Box.Extends (⟨U, conds⟩ : DRS L V) g (fun x => if x ∈ U then g' x else g x) ∧
      Verifies (fun x => if x ∈ U then g' x else g x) (⟨U, conds⟩ : DRS L V)) ∧
      Set.EqOn (fun x => if x ∈ U then g' x else g x) g' ↑(X ∪ U) := by
  obtain ⟨hag, hh⟩ := h
  have heq : Set.EqOn (fun x => if x ∈ U then g' x else g x) g' ↑(X ∪ U) := by
    intro x hx
    by_cases hxU : x ∈ U
    · simp only [ite_eq_left hxU]
    · have hxX : x ∈ X := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
        · exact h
        · exact absurd h hxU
      simp only [ite_eq_right hxU]
      exact (hag (Finset.mem_coe.mpr hxX)).symm
  exact ⟨⟨fun x hxU => ite_eq_right hxU, (verifies_mk U conds).mpr
    ((hIH _).mpr ((Condition.holdsAllAt_congr conds hfvc heq).mpr hh))⟩, heq⟩

mutual
theorem Condition.verifies_iff_holdsAt {X : Finset V} (c : Condition L V)
    (hrf : Condition.ReuseFreeAt X c) (hfv : c.freeVarFinset ⊆ X) (g : V → M) :
    VerifiesCondition g c ↔ Condition.holdsAt X c g := by
  match c with
  | .atom a => simp only [verifies_atom, Condition.holdsAt_atom]
  | .eq u v => simp only [verifies_eq, Condition.holdsAt_eq]
  | .neg K =>
    obtain ⟨U, conds⟩ := K
    simp only [Condition.reuseFreeAt_neg, DRS.reuseFreeAt_mk] at hrf
    rw [Condition.freeVarFinset_neg] at hfv
    have hfvc := DRS.freeVarFinset_subset_iff.mp hfv
    have hIH : ∀ k : V → M, (∀ c ∈ conds, VerifiesCondition k c) ↔
        Condition.holdsAllAt (X ∪ U) conds k :=
      fun k => Condition.verifiesAll_iff_holdsAllAt conds hrf.2 hfvc k
    simp only [verifies_neg, Condition.holdsAt_neg]
    exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, DRS.toRelAt_of_toRel' hrf.1 hIH hk⟩,
      fun ⟨k, hk⟩ => ⟨_, (DRS.toRel_of_toRelAt' hfvc hIH hk).1⟩⟩
  | .imp a c' =>
    obtain ⟨Ua, ca⟩ := a
    obtain ⟨Uc, cc⟩ := c'
    simp only [Condition.reuseFreeAt_imp, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUa, hrfa⟩, hXUc, hrfc⟩ := hrf
    rw [Condition.freeVarFinset_imp, Finset.union_subset_iff] at hfv
    obtain ⟨hfva, hfvc'⟩ := hfv
    have hfvca : Condition.freeVarFinsetL ca ⊆ X ∪ Ua := DRS.freeVarFinset_subset_iff.mp hfva
    have hfvcc : Condition.freeVarFinsetL cc ⊆ (X ∪ Ua) ∪ Uc := by
      intro x hx
      by_cases hxUc : x ∈ Uc
      · exact Finset.mem_union_right _ hxUc
      · by_cases hxUa : x ∈ Ua
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxUa)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (hfvc' ?_))
          rw [DRS.freeVarFinset_mk, DRS.referents_mk, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨⟨hx, hxUc⟩, hxUa⟩
    have hIHa : ∀ k : V → M, (∀ c ∈ ca, VerifiesCondition k c) ↔
        Condition.holdsAllAt (X ∪ Ua) ca k :=
      fun k => Condition.verifiesAll_iff_holdsAllAt ca hrfa hfvca k
    have hIHc : ∀ k : V → M, (∀ c ∈ cc, VerifiesCondition k c) ↔
        Condition.holdsAllAt ((X ∪ Ua) ∪ Uc) cc k :=
      fun k => Condition.verifiesAll_iff_holdsAllAt cc hrfc hfvcc k
    simp only [verifies_imp, Condition.holdsAt_imp]
    constructor
    · intro hL g₁ hg₁
      obtain ⟨hflat, heq⟩ := DRS.toRel_of_toRelAt' hfvca hIHa hg₁
      obtain ⟨g₂, hg₂⟩ := hL _ hflat.1 hflat.2
      exact ⟨g₂, (DRS.toRelAt_congr_left (X ∪ Ua) _ heq).mp
        (DRS.toRelAt_of_toRel' hXUc hIHc hg₂)⟩
    · intro hR g₁ hg₁ hv₁
      obtain ⟨g₂, hg₂⟩ := hR g₁ (DRS.toRelAt_of_toRel' hXUa hIHa ⟨hg₁, hv₁⟩)
      exact ⟨_, (DRS.toRel_of_toRelAt' hfvcc hIHc hg₂).1⟩
  | .dis l r =>
    obtain ⟨Ul, cl⟩ := l
    obtain ⟨Ur, cr⟩ := r
    simp only [Condition.reuseFreeAt_dis, DRS.reuseFreeAt_mk] at hrf
    obtain ⟨⟨hXUl, hrfl⟩, hXUr, hrfr⟩ := hrf
    rw [Condition.freeVarFinset_dis, Finset.union_subset_iff] at hfv
    have hfvcl : Condition.freeVarFinsetL cl ⊆ X ∪ Ul := DRS.freeVarFinset_subset_iff.mp hfv.1
    have hfvcr : Condition.freeVarFinsetL cr ⊆ X ∪ Ur := DRS.freeVarFinset_subset_iff.mp hfv.2
    have hIHl : ∀ k : V → M, (∀ c ∈ cl, VerifiesCondition k c) ↔
        Condition.holdsAllAt (X ∪ Ul) cl k :=
      fun k => Condition.verifiesAll_iff_holdsAllAt cl hrfl hfvcl k
    have hIHr : ∀ k : V → M, (∀ c ∈ cr, VerifiesCondition k c) ↔
        Condition.holdsAllAt (X ∪ Ur) cr k :=
      fun k => Condition.verifiesAll_iff_holdsAllAt cr hrfr hfvcr k
    simp only [verifies_dis, Condition.holdsAt_dis]
    constructor
    · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
      · exact ⟨k, Or.inl (DRS.toRelAt_of_toRel' hXUl hIHl hk)⟩
      · exact ⟨k, Or.inr (DRS.toRelAt_of_toRel' hXUr hIHr hk)⟩
    · rintro ⟨k, hk | hk⟩
      · exact Or.inl ⟨_, (DRS.toRel_of_toRelAt' hfvcl hIHl hk).1⟩
      · exact Or.inr ⟨_, (DRS.toRel_of_toRelAt' hfvcr hIHr hk).1⟩
theorem Condition.verifiesAll_iff_holdsAllAt {X : Finset V} (cs : List (Condition L V))
    (hrf : Condition.ReuseFreeAllAt X cs) (hfv : Condition.freeVarFinsetL cs ⊆ X) (g : V → M) :
    (∀ c ∈ cs, VerifiesCondition g c) ↔ Condition.holdsAllAt X cs g := by
  match cs with
  | [] => simp
  | c :: cs =>
    simp only [Condition.reuseFreeAllAt_cons] at hrf
    rw [Condition.freeVarFinsetL_cons, Finset.union_subset_iff] at hfv
    simp only [List.forall_mem_cons, Condition.holdsAllAt_cons]
    exact and_congr (Condition.verifies_iff_holdsAt c hrf.1 hfv.1 g)
      (Condition.verifiesAll_iff_holdsAllAt cs hrf.2 hfv.2 g)
end

theorem DRS.toRelAt_of_toRel {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) {g g' : V → M} (h : (g, g') ∈ DRS.toRel K) :
    DRS.toRelAt X K g g' := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.reuseFreeAt_mk] at hrf
  exact DRS.toRelAt_of_toRel' hrf.1 (fun k => Condition.verifiesAll_iff_holdsAllAt conds hrf.2
    (DRS.freeVarFinset_subset_iff.mp hfv) k) ((DRS.toRel_iff _ _ _).1 h)

theorem DRS.toRel_of_toRelAt {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) {g g' : V → M} (h : DRS.toRelAt X K g g') :
    ∃ g'', (g, g'') ∈ DRS.toRel K ∧ Set.EqOn g'' g' ↑(X ∪ K.referents) := by
  obtain ⟨U, conds⟩ := K
  simp only [DRS.reuseFreeAt_mk] at hrf
  obtain ⟨hflat, heq⟩ := DRS.toRel_of_toRelAt' (DRS.freeVarFinset_subset_iff.mp hfv)
    (fun k => Condition.verifiesAll_iff_holdsAllAt conds hrf.2
      (DRS.freeVarFinset_subset_iff.mp hfv) k) h
  exact ⟨_, (DRS.toRel_iff _ _ _).2 hflat, heq⟩

/-- On a reuse-free DRS, the flat total-assignment and indexed persistence semantics have the same
truth conditions (Muskens's fn. 4). -/
theorem DRS.trueRel_iff_toRelAt {X : Finset V} {K : DRS L V} (hrf : DRS.ReuseFreeAt X K)
    (hfv : K.freeVarFinset ⊆ X) (g : V → M) :
    DRS.trueRel K g ↔ ∃ g', DRS.toRelAt X K g g' := by
  rw [DRS.trueRel_iff]
  exact ⟨fun ⟨g', h⟩ => ⟨g', DRS.toRelAt_of_toRel hrf hfv h⟩,
    fun ⟨g', h⟩ => (DRS.toRel_of_toRelAt hrf hfv h).imp fun _ hg => hg.1⟩

end DRT
