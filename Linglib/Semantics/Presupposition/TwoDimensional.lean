module

public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Semantics.Presupposition.Basic

/-!
# Two-dimensional presupposition

A two-dimensional account of presupposition computes what a sentence asserts and what it
presupposes separately, as a `TwoDim W (W → Prop)` whose not-at-issue content is the
presupposition. Such a proposition is [trivalent](##ConventionalImplicature.TwoDim.toTrivalent),
undefined where its presupposition fails, and the applicative connectives become the Weak Kleene
ones. Karttunen's filtering conditional is [a bind](##ConventionalImplicature.TwoDim.impFilter),
since its antecedent's at-issue content decides whether its consequent's presupposition projects;
it evaluates to [the Middle Kleene
conditional](##ConventionalImplicature.TwoDim.toTrivalent_impFilter), and [no applicative
combination](##ConventionalImplicature.TwoDim.exists_seq_notAtIssue_ne_impFilter) presupposes
what it does. The [filtering disjunction](##ConventionalImplicature.TwoDim.orFilter) is symmetric
and reads at-issue content where the presupposition fails, and so is [no trivalent
operation](##ConventionalImplicature.TwoDim.orFilter_not_trivalent).

## TODO

* Yagi presents the filtering disjunction as a departure from an asymmetric rule of Karttunen
  and Peters, and Sharvit presents it as their rule. The 1979 chapter has not been checked.

## References

* [karttunen-1973]
* [peters-1979]
* [karttunen-peters-1979]
* [yagi-2025]
* [sharvit-2025]
* [kalomoiros-schwarz-2021]
* [heim-1992]
* [van-der-sandt-1992]
* [delpinal-bassi-sauerland-2024]
-/

@[expose] public section

namespace ConventionalImplicature.TwoDim

universe u

variable {W : Type u}

section Trivalent

open Classical

variable (p q : TwoDim W (W → Prop)) {w : W}

/-- A two-dimensional proposition evaluates to the trivalent proposition undefined where its
not-at-issue content fails and the classical value of its at-issue content elsewhere. -/
noncomputable def toTrivalent : W → Trivalent :=
  Trivalent.condEvent p.notAtIssue p.atIssue

@[simp] theorem toTrivalent_eq_true_iff :
    p.toTrivalent w = .true ↔ p.notAtIssue w ∧ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_false_iff :
    p.toTrivalent w = .false ↔ p.notAtIssue w ∧ ¬ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_undefined_iff : p.toTrivalent w = .undefined ↔ ¬ p.notAtIssue w := by
  simp [toTrivalent]

theorem toTrivalent_neg : p.neg.toTrivalent = p.toTrivalentᶜ :=
  funext fun _ ↦ Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp)

theorem toTrivalent_and : (p.and q).toTrivalent w = (p.toTrivalent w).meetWeak (q.toTrivalent w) :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp [imp_iff_not_or])
    (by simp [and_and_and_comm])

theorem toTrivalent_or : (p.or q).toTrivalent w = (p.toTrivalent w).joinWeak (q.toTrivalent w) :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff
    (by simp [Trivalent.joinWeak_eq_undefined_iff, imp_iff_not_or])
    (by simp [Trivalent.joinWeak_eq_true_iff]; tauto)

theorem toTrivalent_imp :
    (p.imp q).toTrivalent w = ((p.toTrivalent w)ᶜ).joinWeak (q.toTrivalent w) :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff
    (by simp [Trivalent.joinWeak_eq_undefined_iff, imp_iff_not_or])
    (by simp [Trivalent.joinWeak_eq_true_iff, himp_eq]; tauto)

/-- The filtering conditional presupposes what its antecedent does, and what its consequent does
only where the antecedent's at-issue content holds. This is the conditional presupposition by
which [peters-1979] renders the filter of [karttunen-1973], and the one [sharvit-2025] gives for
the connectives of [karttunen-peters-1979]. -/
def impFilter : TwoDim W (W → Prop) := p >>= fun a ↦ ⟨a ⇨ q.atIssue, a ⇨ q.notAtIssue⟩

@[simp] theorem impFilter_atIssue : (p.impFilter q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem impFilter_notAtIssue :
    (p.impFilter q).notAtIssue = p.notAtIssue ⊓ (p.atIssue ⇨ q.notAtIssue) := rfl

theorem imp_notAtIssue_le_impFilter_notAtIssue :
    (p.imp q).notAtIssue ≤ (p.impFilter q).notAtIssue :=
  inf_le_inf_left _ le_himp

/-- The filtering conditional evaluates to the Middle Kleene conditional of [peters-1979]. -/
theorem toTrivalent_impFilter :
    (p.impFilter q).toTrivalent w = ((p.toTrivalent w)ᶜ).joinMiddle (q.toTrivalent w) :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp [himp_eq]; tauto)
    (by simp [himp_eq]; tauto)

/-- Filtering needs the bind: an at-issue operator applied to two meanings presupposes the same
whatever their at-issue content, so none presupposes what the filtering conditional does. -/
theorem exists_seq_notAtIssue_ne_impFilter [Nonempty W] :
    ∃ p q : TwoDim W (W → Prop), ∀ f : (W → Prop) → (W → Prop) → W → Prop,
      (f <$> p <*> q).notAtIssue ≠ (p.impFilter q).notAtIssue := by
  refine ⟨⟨⊥, ⊤⟩, ⟨⊥, ⊥⟩, fun f h ↦ ?_⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  simpa using congrFun h w

/-- The filtering disjunction presupposes `(A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))` and
asserts `A(φ) ∨ A(ψ)`: each disjunct's presupposition projects unless the other disjunct's
at-issue content holds. It is [yagi-2025]'s Definition 2 and the disjunction [sharvit-2025]
gives for the connectives of [karttunen-peters-1979]; [kalomoiros-schwarz-2021] give experimental
support for the symmetry. -/
@[simps]
def orFilter : TwoDim W (W → Prop) :=
  ⟨p.atIssue ⊔ q.atIssue, fun w ↦ (q.atIssue w ∨ p.notAtIssue w) ∧ (p.atIssue w ∨ q.notAtIssue w)⟩

theorem orFilter_comm : orFilter p q = orFilter q p :=
  TwoDim.ext (sup_comm ..) (funext fun _ ↦ propext and_comm)

/-- When the disjuncts' presuppositions conflict, a defined filtering disjunction is true, so it is
never both defined and false there ([yagi-2025] §2.2). -/
theorem orFilter_atIssue_of_conflict (h : ¬ (p.notAtIssue w ∧ q.notAtIssue w))
    (hp : (orFilter p q).notAtIssue w) : (orFilter p q).atIssue w := by
  obtain ⟨h₁, h₂⟩ := hp
  by_cases hp : p.notAtIssue w
  · exact Or.inl (h₂.resolve_right fun hq ↦ h ⟨hp, hq⟩)
  · exact Or.inr (h₁.resolve_right hp)

theorem orFilter_not_trivalent (w : W) :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent,
      ∀ p q : TwoDim W (W → Prop),
        (orFilter p q).toTrivalent w = f (p.toTrivalent w) (q.toTrivalent w) := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨fun _ ↦ True, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  have h₂ := hf ⟨fun _ ↦ False, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  simp [orFilter, toTrivalent, Trivalent.condEvent_apply] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-- Embedding under a negative factive, *x is unaware that p*, presupposes that the complement
holds, its presupposition included, and asserts that `x` does not believe its at-issue content.
The complement's presupposition so projects to the evaluation world, the transparent rule of
[van-der-sandt-1992], and not into `x`'s beliefs, the opaque rule of [heim-1992];
[delpinal-bassi-sauerland-2024] derive free choice under *unaware* with either. -/
@[simps]
def negFactive (believes : (W → Prop) → W → Prop) : TwoDim W (W → Prop) :=
  ⟨fun w ↦ ¬ believes p.atIssue w, fun w ↦ p.notAtIssue w ∧ p.atIssue w⟩

/-- Under a complement that presupposes nothing, the negative factive is the negation of the
factive sentence. -/
theorem toTrivalent_negFactive (believes : (W → Prop) → W → Prop) (h : ∀ w, p.notAtIssue w) :
    (negFactive p believes).toTrivalent = (Presupposition.factive believes p.atIssue)ᶜ := by
  rw [Presupposition.factive, Trivalent.compl_condEvent, toTrivalent]
  congr 1
  funext w
  simp [h w]

end Trivalent

end ConventionalImplicature.TwoDim
