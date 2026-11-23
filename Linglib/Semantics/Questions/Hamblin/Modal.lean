module

public import Linglib.Semantics.Questions.Hamblin.Exhaustive
public import Linglib.Logic.Modal.Basic

/-!
# Knowing the answer and questions under necessity

Let `H` be a Hamblin set, and let `Dox : SetRel W W` relate each world to the worlds that an agent
considers possible there.

The agent knows the answer to `H` at `w` when the weak answer at `w` holds in every world the agent
considers possible. We write `KnowsAnswer H w Dox`. The agent knows some answer when at least one
true member of `H` holds in all those worlds, written `KnowsSomeAnswer H w Dox`. Knowing the answer
implies knowing some answer, provided that some member is true.

We also define the question under necessity, `box H R`. Its members say, for each member `p` of `H`,
that `p` holds in every `R`-accessible world.

## References

* [karttunen-1977]
* [belnap-1982]
* [groenendijk-stokhof-1984]
* [dayal-2025]
-/

@[expose] public section

namespace Question

open SetRel

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### Knowing the answer -/

section Knowing

variable {c A p : Set W} {Dox : SetRel W W}

/-- The center knows the answer to `H` at `w` when the weak answer holds throughout its doxastic
alternatives `Dox`, [karttunen-1977]'s meaning postulate for *know*. -/
def KnowsAnswer (Dox : SetRel W W) : Prop := w ∈ Dox.core (weakAnswer H w)

/-- The center knows some answer to `H` at `w` when some true member holds throughout its
alternatives `Dox`, the mention-some *know* of [belnap-1982] and [groenendijk-stokhof-1984]. -/
def KnowsSomeAnswer (Dox : SetRel W W) : Prop := ∃ p ∈ trueAnswers H w, w ∈ Dox.core p

/-- The perspectival center is possibly ignorant in the context `c` when it may not know the
answer there, [dayal-2025]'s requirement on the center of a question. -/
def PossiblyIgnorant (c : Set W) (Dox : SetRel W W) : Prop := ∃ w ∈ c, ¬ KnowsAnswer H w Dox

variable {H} {w}

theorem not_possiblyIgnorant_inter_of_subset (hA : A ⊆ {w | KnowsAnswer H w Dox}) :
    ¬ PossiblyIgnorant H (c ∩ A) Dox :=
  fun ⟨_, ⟨_, hw⟩, hk⟩ => hk (hA hw)

theorem possiblyIgnorant_inter_compl_iff :
    PossiblyIgnorant H (c ∩ {w | KnowsAnswer H w Dox}ᶜ) Dox ↔ PossiblyIgnorant H c Dox :=
  ⟨fun ⟨w, ⟨hc, _⟩, hk⟩ => ⟨w, hc, hk⟩, fun ⟨w, hc, hk⟩ => ⟨w, ⟨hc, hk⟩, hk⟩⟩

theorem possiblyIgnorant_inter_union_compl_iff :
    PossiblyIgnorant H (c ∩ (A ∪ Aᶜ)) Dox ↔ PossiblyIgnorant H c Dox := by
  rw [Set.union_compl_self, Set.inter_univ]

theorem knowsAnswer_id : KnowsAnswer H w .id := by
  rw [KnowsAnswer, SetRel.core_id]
  exact self_mem_weakAnswer H w

theorem knowsAnswer_univ_iff :
    KnowsAnswer H w Set.univ ↔ weakAnswer H w = Set.univ :=
  ⟨fun h => Set.eq_univ_of_forall fun _ => h trivial, fun h _ _ => h ▸ Set.mem_univ _⟩

theorem knowsSomeAnswer_of_mem [Dox.IsRefl] (hp : p ∈ H) (hw : w ∈ Dox.core p) :
    KnowsSomeAnswer H w Dox :=
  ⟨p, ⟨hp, hw Dox.rfl⟩, hw⟩

theorem knowsAnswer_of_mem_core_strongAnswer (h : w ∈ Dox.core (strongAnswer H w)) :
    KnowsAnswer H w Dox :=
  SetRel.core_subset_core (strongAnswer_subset_weakAnswer H w) h

theorem KnowsAnswer.knowsSomeAnswer (h : KnowsAnswer H w Dox) (hne : (trueAnswers H w).Nonempty) :
    KnowsSomeAnswer H w Dox :=
  let ⟨p, hp⟩ := hne
  ⟨p, hp, SetRel.core_subset_core (weakAnswer_subset H w hp.1 hp.2) h⟩

theorem knowsSomeAnswer_iff_knowsAnswer (h : trueAnswers H w = {p}) :
    KnowsSomeAnswer H w Dox ↔ KnowsAnswer H w Dox := by
  simp [KnowsSomeAnswer, KnowsAnswer, weakAnswer, h]

end Knowing

/-! ### Questions under necessity -/

/-- The question `□Q` over the accessibility `R` necessitates every member: it is the image of
`H` under `SetRel.core R`. -/
def box {W' : Type*} (R : SetRel W' W) : Set (Set W') := R.core '' H

theorem mem_box {W' : Type*} {R : SetRel W' W} {q : Set W'} :
    q ∈ box H R ↔ ∃ p ∈ H, R.core p = q := Iff.rfl

theorem isExhaustivelyResolvable_box_iff {W' : Type*} {R : SetRel W' W}
    (hR : ∀ v, ∃ x, ∀ u, x ~[R] u ↔ u = v) {x : W'} {s : Set W} (hs : ∀ v, x ~[R] v ↔ v ∈ s) :
    IsExhaustivelyResolvable (box H R) x ↔ IsExhaustivelyResolvableOn H s := by
  have mem : ∀ p, x ∈ R.core p ↔ s ⊆ p := fun p =>
    ⟨fun h v hv => h ((hs v).2 hv), fun h v hv => h ((hs v).1 hv)⟩
  have mono : ∀ p q : Set W, p ⊆ q → R.core p ⊆ R.core q := fun _ _ ↦ core_subset_core
  have refl : ∀ p q : Set W, R.core p ⊆ R.core q → p ⊆ q := by
    intro p q h v hv
    obtain ⟨y, hy⟩ := hR v
    exact h (fun u hu => ((hy u).1 hu) ▸ hv) ((hy v).2 rfl)
  constructor
  · rintro ⟨q, ⟨⟨p, hp, rfl⟩, hx⟩, hmin⟩
    refine ⟨p, ⟨hp, (mem p).1 hx⟩, fun r ⟨hr, hsr⟩ => refl p r (hmin ⟨⟨r, hr, rfl⟩, (mem r).2 hsr⟩)⟩
  · rintro ⟨p, ⟨hp, hsp⟩, hmin⟩
    refine ⟨_, ⟨⟨p, hp, rfl⟩, (mem p).2 hsp⟩, ?_⟩
    rintro q ⟨⟨r, hr, rfl⟩, hx⟩
    exact mono p r (hmin ⟨hr, (mem r).1 hx⟩)

end Question
