module

public import Linglib.Semantics.Presupposition.LocalContext
public import Linglib.Semantics.Quantification.NumberTree

/-!
# Local contexts in quantified sentences

A quantifier on van Benthem's tree of numbers holds of a restrictor and a scope according to how
many individuals of the restrictor are outside and inside the scope. A predicate in its scope or
restrictor denotes a set of world–individual pairs, so the local context of that position is a set
of such pairs (`scopeTruth`, `restrictorTruth`), and by `isLocalContext_of_dependsOn` it is the set
of pairs on which the sentence's truth value depends. At a world, a quantifier depends on whether an
individual is in its scope iff the individual is in the restrictor and the quantifier is not
constant on the row of the restrictor's size
(`Quantifier.NumberTree.dependsOn_toGQ_compl_singleton_iff`). So the local context of the nuclear
scope is the restrictor's individuals at the worlds of the context where that row is not constant
(`isLocalContext_scopeTruth`): a presupposition triggered in the scope projects universally over the
restrictor, except at worlds where the sentence's truth value does not depend on its scope at all
(`transparent_scopeTruth_iff`). A trigger in the scope is transparent at its own assertion iff the
quantifier gives one value to every scope that resolves the trigger, at each world of the context
(`transparentAt_scopeTruth_iff`). With every scope as a continuation, as the incremental theory has
it, the local context of the restrictor is every individual unless the quantifier is constant on the
whole triangle below the size of the universe, and a presupposition triggered in the restrictor
projects universally over the domain (`transparent_restrictorTruth_iff`).

These are Schlenker's derivations of universal projection, in Anti-Dynamics and in Local Contexts,
stated world by world. The conditions under which those papers prove them, that the restrictor and
the domain have constant sizes across the context and that the quantifier is not constant on the
relevant points of the tree there, become the condition at each world under which the
presupposition is required.

## Main results

* `isLocalContext_scopeTruth`, `transparent_scopeTruth_iff`: universal projection from the
  nuclear scope.
* `transparentAt_scopeTruth_iff`: definedness by supervaluation of a trigger in the nuclear scope.
* `isLocalContext_restrictorTruth`, `transparent_restrictorTruth_iff`: universal projection from
  the restrictor, with every scope as a continuation.

## Implementation notes

The domain is a finite type, the same at every world, and the quantifier is the same at every
world. A predicate's denotation is a set of world–individual pairs, the two-place intension of the
appendix of Local Contexts.

## References

* [van-benthem-1984]
* [schlenker-2007]
* [schlenker-2009]
-/

@[expose] public section

namespace Presupposition

open Quantifier

variable {W E : Type*}

/-- The truth set of `(Q A. _)`, as a function of the denotation of its scope, is the set of worlds
at which `q` holds of the restrictor and of the scope's individuals there. -/
def scopeTruth (q : NumberTree) (A : W → E → Prop) (d : Set (W × E)) : Set W :=
  {w | q.toGQ (A w) fun e ↦ (w, e) ∈ d}

/-- The truth set of `(Q _. B)` as a function of the denotation of its restrictor. -/
def restrictorTruth (q : NumberTree) (B : W → E → Prop) (d : Set (W × E)) : Set W :=
  {w | q.toGQ (fun e ↦ (w, e) ∈ d) (B w)}

/-- A truth value at `w` that is a function of the individuals at `w` depends on the pair
`(v, e)` iff `v` is `w` and the function depends on `e`. -/
theorem dependsOn_slice_iff {w v : W} {e : E} {g : (E → Prop) → Prop} :
    DependsOn (fun d : Set (W × E) ↦ g fun x ↦ (w, x) ∈ d) {(v, e)}ᶜ ↔
      (v = w → DependsOn g {e}ᶜ) := by
  refine ⟨fun h hv D D' hD ↦ ?_, fun h d d' hd ↦ ?_⟩
  · subst hv
    have := h (x := {p | p.1 = v ∧ D p.2}) (y := {p | p.1 = v ∧ D' p.2}) fun ⟨u, x⟩ hux ↦ by
      by_cases hu : u = v
      · subst hu
        exact congrArg (u = u ∧ ·) (hD x fun hx ↦ hux (by rw [hx]; rfl))
      · exact propext ⟨fun h ↦ (hu h.1).elim, fun h ↦ (hu h.1).elim⟩
    simpa using this
  · by_cases hv : v = w
    · subst hv
      exact h rfl fun x hx ↦ hd (v, x) fun h' ↦ hx (Prod.ext_iff.1 h').2
    · exact congrArg g (funext fun x ↦ hd (w, x) fun h' ↦ hv (Prod.ext_iff.1 h').1.symm)

/-- A truth value at `w` that is a function of the individuals at `w` depends on finitely many
pairs. -/
theorem dependsOn_slice [Finite E] (w : W) (g : (E → Prop) → Prop) :
    ∃ s : Set (W × E), s.Finite ∧ DependsOn (fun d : Set (W × E) ↦ g fun x ↦ (w, x) ∈ d) s :=
  ⟨{w} ×ˢ Set.univ, (Set.finite_singleton w).prod Set.finite_univ,
    fun _ _ hd ↦ congrArg g (funext fun x ↦ hd (w, x) ⟨rfl, trivial⟩)⟩

/-- A trigger in the nuclear scope that presupposes `P` and asserts `a` is transparent at `a` iff at
each world of the context the quantifier gives one value to every scope that agrees with `a` on
the individuals that satisfy `P` there. -/
theorem transparentAt_scopeTruth_iff {q : NumberTree} {A : W → E → Prop} {C : Set W}
    {P a : Set (W × E)} :
    TransparentAt C {scopeTruth q A} P a ↔ ∀ w ∈ C, ∀ D D' : E → Prop,
      (∀ e, (w, e) ∈ P → (D e ↔ (w, e) ∈ a)) → (∀ e, (w, e) ∈ P → (D' e ↔ (w, e) ∈ a)) →
        (q.toGQ (A w) D ↔ q.toGQ (A w) D') := by
  classical
  simp only [transparentAt_iff, Set.mem_singleton_iff, forall_eq]
  refine ⟨fun h w hw D D' hD hD' ↦ ?_, fun h d d' hd hd' w hw ↦ ?_⟩
  · let ext (D : E → Prop) : Set (W × E) := {p | if p.1 = w then D p.2 else p ∈ a}
    have hext {D : E → Prop} (hD : ∀ e, (w, e) ∈ P → (D e ↔ (w, e) ∈ a)) :
        P ⊓ ext D = P ⊓ a := Set.ext fun ⟨u, e⟩ ↦ and_congr_right fun hp ↦ by
      by_cases hu : u = w
      · subst hu; simpa [ext] using hD e hp
      · simp [ext, hu]
    simpa [scopeTruth, ext] using h _ _ (hext hD) (hext hD') w hw
  · have agree {d : Set (W × E)} (hd : P ⊓ d = P ⊓ a) (e : E) (hp : (w, e) ∈ P) :
        (w, e) ∈ d ↔ (w, e) ∈ a := by
      simpa [hp] using congrArg ((w, e) ∈ ·) hd
    exact h w hw (fun e ↦ (w, e) ∈ d) (fun e ↦ (w, e) ∈ d') (agree hd) (agree hd')

section Finite

variable [Finite E] (q : NumberTree) {C : Set W}

/-! ### The nuclear scope -/

/-- The local context of the nuclear scope of `(Q A. _)` is the individuals of the restrictor, at
the worlds of the context where `q` is not constant on the row of the restrictor's size. -/
theorem isLocalContext_scopeTruth (A : W → E → Prop) (C : Set W) :
    IsLocalContext C {scopeTruth q A}
      {p | p.1 ∈ C ∧ A p.1 p.2 ∧ ¬ q.ConstantOnRow {x | A p.1 x}.ncard} := by
  convert isLocalContext_of_dependsOn (C := C) (env := {scopeTruth q A}) fun f hf w _ ↦
    (Set.mem_singleton_iff.1 hf) ▸ dependsOn_slice w (q.toGQ (A w)) using 1
  ext ⟨v, e⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  change _ ↔ ∃ w ∈ C, ¬ DependsOn (fun d : Set (W × E) ↦ q.toGQ (A w) fun x ↦ (w, x) ∈ d) _
  simp only [dependsOn_slice_iff, NumberTree.dependsOn_toGQ_compl_singleton_iff, not_imp]
  exact ⟨fun ⟨hv, ha, hc⟩ ↦ ⟨v, hv, rfl, ha, hc⟩, fun ⟨_, hw, rfl, ha, hc⟩ ↦ ⟨hw, ha, hc⟩⟩

/-- A presupposition triggered in the nuclear scope projects universally over the restrictor. It
is transparent iff at each world of the context where `q` is not constant on the row of the
restrictor's size, every individual of the restrictor satisfies it. -/
theorem transparent_scopeTruth_iff {A : W → E → Prop} {P : Set (W × E)} :
    Transparent C {scopeTruth q A} P ↔
      ∀ w ∈ C, ¬ q.ConstantOnRow {x | A w x}.ncard → ∀ e, A w e → (w, e) ∈ P := by
  rw [← (isLocalContext_scopeTruth q A C).satisfied_iff_transparent,
    satisfied_iff (isLocalContext_scopeTruth q A C)]
  exact ⟨fun h w hw hc e he ↦ h ⟨hw, he, hc⟩, fun h ⟨w, e⟩ ⟨hw, he, hc⟩ ↦ h w hw hc e he⟩

/-! ### The restrictor -/

/-- With every scope as a continuation, the local context of the restrictor is every individual at
every world of the context, unless `q` is constant below the size of the universe. -/
theorem isLocalContext_restrictorTruth (C : Set W) :
    IsLocalContext C (Set.range (restrictorTruth q))
      {p : W × E | p.1 ∈ C ∧ ¬ q.ConstantBelow (Nat.card E)} := by
  convert isLocalContext_of_dependsOn (C := C) (env := Set.range (restrictorTruth q))
    (fun f hf w _ ↦ by
      obtain ⟨B, rfl⟩ := hf
      exact dependsOn_slice (E := E) w (q.toGQ · (B w))) using 1
  ext ⟨v, e⟩
  simp only [Set.mem_ofPred_eq, Set.exists_range_iff]
  refine ⟨fun ⟨hv, hc⟩ ↦ ?_, fun ⟨B, w, hw, hB⟩ ↦ ?_⟩
  · obtain ⟨B, hB⟩ := (NumberTree.exists_not_dependsOn_toGQ_restrictor_iff e).2 hc
    exact ⟨fun _ ↦ B, v, hv, fun h ↦ hB ((dependsOn_slice_iff (g := (q.toGQ · B))).1 h rfl)⟩
  · obtain rfl : v = w := by_contra fun hv ↦
      hB ((dependsOn_slice_iff (g := (q.toGQ · (B w)))).2 fun h ↦ (hv h).elim)
    exact ⟨hw, (NumberTree.exists_not_dependsOn_toGQ_restrictor_iff e).1
      ⟨B v, fun h ↦ hB ((dependsOn_slice_iff (g := (q.toGQ · (B v)))).2 fun _ ↦ h)⟩⟩

/-- A presupposition triggered in the restrictor, with every scope as a continuation, projects
universally over the domain. It is transparent iff every individual satisfies it at each world of
the context, unless `q` is constant below the size of the universe. -/
theorem transparent_restrictorTruth_iff {P : Set (W × E)} :
    Transparent C (Set.range (restrictorTruth q)) P ↔
      (¬ q.ConstantBelow (Nat.card E) → ∀ w ∈ C, ∀ e, (w, e) ∈ P) := by
  rw [← (isLocalContext_restrictorTruth q C).satisfied_iff_transparent,
    satisfied_iff (isLocalContext_restrictorTruth q C)]
  exact ⟨fun h hc w hw e ↦ h ⟨hw, hc⟩, fun h ⟨w, e⟩ ⟨hw, hc⟩ ↦ h hc w hw e⟩

end Finite

end Presupposition
