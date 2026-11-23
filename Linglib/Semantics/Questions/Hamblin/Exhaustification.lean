module

public import Mathlib.Data.Set.Finite.Basic
public import Linglib.Semantics.Questions.Hamblin.Exhaustive
public import Linglib.Semantics.Exhaustification.Basic

/-!
# Exhaustification against a Hamblin set

Let `p` be a member of a Hamblin set `H`. Exhaustifying `p` against `H` gives the proposition that
`p` holds and that every member of `H` not entailed by `p` fails. This is
`Exhaustification.exh H p`, following [fox-2018].

The main result is that the exhaustified `p` holds exactly at the worlds where `p` is the strongest
true answer. See `Question.mem_exh_iff_isStrongestTrueAnswer`. At such a world it coincides with the
strong answer.

## References

* [fox-2018]
* [dayal-1996]
* [heim-1994]
-/

@[expose] public section

namespace Question

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### Exhaustification ([fox-2018])

Exhaustifying a member `p` against `H`, `Exhaustification.exh H p`, asserts `p` and denies every
member `p` does not entail. On a member it holds exactly where `p` is the strongest true member,
so it is a cell of the partition. -/

theorem trueAnswers_eq_of_isStrongestTrueAnswer {p : Set W}
    (h : IsStrongestTrueAnswer H w p) : trueAnswers H w = {q ∈ H | p ⊆ q} :=
  Set.ext fun _ => ⟨fun hq => ⟨hq.1, h.2 hq⟩, fun ⟨hq, hpq⟩ => ⟨hq, hpq h.1.2⟩⟩

variable {H w} in
/-- A member exhaustified against the question holds where it is the strongest true member: Fox's
`Exh(Q, p)` is the set of worlds `w` with `Max_inf(Q, w) = p` ([fox-2018], (11), after
[dayal-1996]'s `Max_inf`). -/
theorem mem_exh_iff_isStrongestTrueAnswer {p : Set W} (hp : p ∈ H) :
    w ∈ Exhaustification.exh H p ↔ IsStrongestTrueAnswer H w p :=
  Exhaustification.mem_exh_iff_isLeast_of_mem hp

theorem exh_eq_strongAnswer {p : Set W} (h : IsStrongestTrueAnswer H w p) :
    Exhaustification.exh H p = strongAnswer H w := by
  ext v
  rw [mem_exh_iff_isStrongestTrueAnswer h.1.1, mem_strongAnswer]
  constructor
  · exact fun hv q hq =>
      ⟨fun hwq => h.2 ⟨hq, hwq⟩ hv.1.2, fun hvq => hv.2 ⟨hq, hvq⟩ h.1.2⟩
  · exact fun hv =>
      ⟨⟨h.1.1, (hv p h.1.1).1 h.1.2⟩, fun _ hq => h.2 ⟨hq.1, (hv _ hq.1).2 hq.2⟩⟩

/-- Dayal's strong operator Ans-D/H, [heim-1994]'s strengthening of Ans-D, returns the worlds with
the same strongest true member as `w`. -/
noncomputable def dayalStrongAns : Option (Set W) := (dayalAns H w).map (Exhaustification.exh H)

theorem dayalStrongAns_eq_some_iff {A : Set W} :
    dayalStrongAns H w = some A ↔ IsExhaustivelyResolvable H w ∧ A = strongAnswer H w := by
  simp only [dayalStrongAns, Option.map_eq_some_iff, dayalAns_eq_some_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, exh_eq_strongAnswer H w hp⟩
  · rintro ⟨⟨p, hp⟩, rfl⟩
    exact ⟨p, hp, exh_eq_strongAnswer H w hp⟩

/-- Ans-D/H returns the worlds where Ans-D returns what it returns at `w`, Heim's form of the
strong operator. -/
theorem dayalStrongAns_eq_some_iff_eq_setOf {A : Set W} :
    dayalStrongAns H w = some A ↔
      IsExhaustivelyResolvable H w ∧ A = {v | dayalAns H v = dayalAns H w} := by
  rw [dayalStrongAns_eq_some_iff]
  refine and_congr_right fun ⟨p, hp⟩ ↦ ?_
  rw [(dayalAns_eq_some_iff H w).2 hp, ← exh_eq_strongAnswer H w hp]
  exact Eq.congr_right <| Set.ext fun v ↦
    (mem_exh_iff_isStrongestTrueAnswer hp.1.1).trans (dayalAns_eq_some_iff H v).symm

variable {H} in
/-- The presupposition holds throughout `C` exactly when, for each world of `C`, exhaustifying some
member gives its cell inside `C`. -/
theorem forall_isExhaustivelyResolvable_iff_exh_inter (C : Set W) :
    (∀ w ∈ C, IsExhaustivelyResolvable H w) ↔
      ∀ w ∈ C, ∃ p ∈ H, Exhaustification.exh H p ∩ C = strongAnswer H w ∩ C := by
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · obtain ⟨p, hp⟩ := h w hw
    exact ⟨p, hp.1.1, by rw [exh_eq_strongAnswer H w hp]⟩
  · obtain ⟨p, hp, he⟩ := h w hw
    have : w ∈ Exhaustification.exh H p ∩ C := he ▸ ⟨self_mem_strongAnswer H w, hw⟩
    exact ⟨p, (mem_exh_iff_isStrongestTrueAnswer hp).1 this.1⟩

variable {H} in
/-- The presupposition holds everywhere exactly when every cell of the partition is the
exhaustification of a member. -/
theorem forall_isExhaustivelyResolvable_iff_classes_subset :
    (∀ w, IsExhaustivelyResolvable H w) ↔
      (Setoid.ofProps H).classes ⊆ Exhaustification.exh H '' H := by
  rw [classes_ofProps, Set.range_subset_iff]
  simpa using forall_isExhaustivelyResolvable_iff_exh_inter (H := H) Set.univ

variable {H w} in
theorem not_dominated_of_isStrongestTrueAnswer {p : Set W} (h : IsStrongestTrueAnswer H w p) :
    ¬ Exhaustification.Dominated H p := fun hd ↦
  let ⟨_, ⟨hq, hqp⟩, hwq⟩ := hd h.1.2
  hqp.2 (h.2 ⟨hq, hwq⟩)

variable {H} in
/-- Where the presupposition holds everywhere, a member that is not dominated is the strongest true
one somewhere. -/
theorem exists_isStrongestTrueAnswer_of_not_dominated (h : ∀ w, IsExhaustivelyResolvable H w)
    {p : Set W} (hp : p ∈ H) (hd : ¬ Exhaustification.Dominated H p) :
    ∃ w, IsStrongestTrueAnswer H w p := by
  obtain ⟨w, hwp, hw⟩ := Set.not_subset.1 hd
  obtain ⟨q, hq⟩ := h w
  obtain rfl : q = p := Classical.byContradiction fun hne ↦
    hw ⟨q, ⟨hq.1.1, (hq.2 ⟨hp, hwp⟩).ssubset_of_ne hne⟩, hq.1.2⟩
  exact ⟨w, hq⟩

variable {H w} in
/-- Among finitely many members, the strongest true one among those not dominated is the strongest
true one. -/
theorem isStrongestTrueAnswer_of_setOf_not_dominated (hH : H.Finite) {p : Set W}
    (h : IsStrongestTrueAnswer {q ∈ H | ¬ Exhaustification.Dominated H q} w p) :
    IsStrongestTrueAnswer H w p :=
  ⟨⟨h.1.1.1, h.1.2⟩, fun _ ⟨hq, hwq⟩ ↦
    let ⟨_, hm, hmd, hwm, hmq⟩ := Exhaustification.exists_mem_subset_not_dominated hH hq hwq
    (h.2 ⟨⟨hm, hmd⟩, hwm⟩).trans hmq⟩

end Question
