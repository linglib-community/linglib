module

public import Linglib.Data.Examples.Elliott2023
public import Linglib.Semantics.Dynamic.Bilateral
public import Mathlib.Order.Setoid.Basic

/-!
# Elliott (2023): Donkey disjunctions and overlapping updates

This file formalizes Elliott's analysis of donkey disjunctions such as *either there's no bathroom
in this house, or it's in a funny place* in Bilateral Update Semantics. The denial of the negated
existential in the first disjunct introduces the pronoun's referent, so [the positive
update](##Elliott2023.positive_donkey) keeps the points with no bathroom and extends the others to
a bathroom in a funny place, a heterogeneous existential reading, and [the disjunction and its
negation hold together](##Elliott2023.nonempty_lnc_iff) where there are bathrooms of both kinds.
Asserted exhaustively relative to its negation, the disjunction [keeps the worlds where every
bathroom is in a funny place](##Elliott2023.world_exhAssert_bot), unless [the question under
discussion distinguishes no worlds](##Elliott2023.exhAssert_top). Since the negative update of an
existential is defined by subsistence, [the anaphoric presupposition of a free variable in its
scope projects](##Elliott2023.negative_exists_pred2).

## Implementation notes

* Assertion and exhaustive assertion are a definedness condition, `BilateralUpdate.Assertable`,
  and an output, the positive update or `exhAssert`.
* A question under discussion is a partition of all worlds, so the cell-mate of exhaustive
  assertion is required to be a world of the context, which the paper's partition of the context
  set guarantees.
* The projection of the presupposition of `y` holds at states whose points all define the same
  referents; where two points of one world differ in whether they define `y`, the one that does
  not subsists in the updates of the one that does.

## References

* [elliott-2023]
* [krahmer-muskens-1995]
* [groenendijk-stokhof-veltman-1996]
* [champollion-bumford-henderson-2019]
-/

@[expose] public section

namespace Elliott2023

open DynamicSemantics BilateralUpdate

variable {W V E : Type*} [DecidableEq V] {s : Set (Possibility W V (Part E))} {x : V}

private theorem mem_pred1_pred1_randomAssign (P Q : E → W → Prop)
    {t : Set (Possibility W V (Part E))} {r : Possibility W V (Part E)} :
    r ∈ (pred1 Q x).positive ((pred1 P x).positive (State.randomAssign t x)) ↔
      ∃ q ∈ t, ∃ e : E, r = q.update x (.some e) ∧ P e q.world ∧ Q e q.world := by
  simp only [mem_positive_pred1]
  constructor
  · rintro ⟨⟨⟨q, hq, m, rfl⟩, e, he, hP⟩, e', he', hQ⟩
    obtain rfl : e = m := by simpa using he
    obtain rfl : e' = e := by simpa using he'
    exact ⟨q, hq, e', rfl, hP, hQ⟩
  · rintro ⟨q, hq, e, rfl, hP, hQ⟩
    exact ⟨⟨⟨q, hq, e, rfl⟩, e, by simp, hP⟩, e, by simp, hQ⟩

/-! ### Donkey disjunctions (§2.4.3) -/

section Donkey

variable (B U : E → W → Prop)

/-- The donkey disjunction `¬∃x B(x) ∨ U(x)` of (30). -/
noncomputable abbrev donkey (x : V) : BilateralUpdate W V E :=
  (~(exists_ x (pred1 B x))) ⊕ pred1 U x

-- (31)
theorem firstPart_donkey (hx : State.Novel s x) :
    firstPart .true (~(exists_ x (pred1 B x))) (pred1 U x) s =
      (exists_ x (pred1 B x)).negative s := by
  have hn := hx.mono (negative_exists_subset x (pred1 B x) s)
  ext p
  simp only [mem_firstPart, update_true, positive_neg]
  refine ⟨fun ⟨b, hp⟩ ↦ ?_, fun hp ↦
    ⟨.undefined, by simpa [unknownUpdate_pred1_of_novel U hn] using hp⟩⟩
  cases b
  · simp [update, negative_pred1_of_novel U hn] at hp
  · simpa [update, unknownUpdate_pred1_of_novel U hn] using hp
  · simp [update, positive_pred1_of_novel U hn] at hp

-- §2.4.3, before (31)
theorem not_cover_pred1 :
    ∃ s : Set (Possibility Unit ℕ (Part Unit)),
      (pred1 (fun _ _ ↦ True) 0).positive s ∪ (pred1 (fun _ _ ↦ True) 0).negative s ∪
        (pred1 (fun _ _ ↦ True) 0).unknownUpdate s ≠ s := by
  let p₀ : Possibility Unit ℕ (Part Unit) := Possibility.bot ()
  have h₁ : p₀.update 0 (.some ()) ∈
      (pred1 (fun _ _ ↦ True) 0).positive {p₀.update 0 (.some ()), p₀} := by simp
  refine ⟨{p₀.update 0 (.some ()), p₀}, fun h ↦ ?_⟩
  have hp : p₀ ∈ ({p₀.update 0 (.some ()), p₀} : Set (Possibility Unit ℕ (Part Unit))) :=
    Set.mem_insert_of_mem _ rfl
  rw [← h] at hp
  rcases hp with (hp | hp) | ⟨-, hpos, -⟩
  · simp [p₀, Possibility.bot, Part.bot_eq_none, Part.notMem_none] at hp
  · simp [p₀, Possibility.bot, Part.bot_eq_none, Part.notMem_none] at hp
  · exact hpos ⟨_, h₁, Possibility.le_update_of_notMem (by simp [p₀]) _⟩

-- (32), with the empty cell where both disjuncts are true
theorem secondPart_donkey [Nonempty E] (hx : State.Novel s x) :
    secondPart .true (~(exists_ x (pred1 B x))) (pred1 U x) s =
      (pred1 U x).positive ((exists_ x (pred1 B x)).positive s) := by
  have hn := hx.mono (negative_exists_subset x (pred1 B x) s)
  ext p
  simp only [mem_secondPart, update_true]
  refine ⟨fun ⟨a, hp⟩ ↦ ?_, fun hp ↦ ⟨.false, by simpa using hp⟩⟩
  cases a
  · simpa [update] using hp
  · simp [update, unknownUpdate_neg, unknownUpdate_exists_pred1 B hx] at hp
  · simp [update, positive_pred1_of_novel U hn] at hp

/-- The positive update of the donkey disjunction keeps the points without a bathroom and extends
the others to a bathroom in a funny place, (33). -/
theorem positive_donkey [Nonempty E] (hx : State.Novel s x) :
    (donkey B U x).positive s =
      {p ∈ s | ∀ e, ¬ B e p.world} ∪ (pred1 U x).positive ((exists_ x (pred1 B x)).positive s) := by
  rw [donkey, positive_disj_eq_union, firstPart_donkey B U hx, secondPart_donkey B U hx,
    negative_exists_pred1 B hx]

-- (35)
theorem negative_donkey :
    (donkey B U x).negative s = (pred1 U x).negative ((exists_ x (pred1 B x)).positive s) := by
  simp

theorem mem_positive_donkey [Nonempty E] (hx : State.Novel s x) {p : Possibility W V (Part E)} :
    p ∈ (donkey B U x).positive s ↔ (p ∈ s ∧ ∀ e, ¬ B e p.world) ∨
      ∃ q ∈ s, ∃ e : E, p = q.update x (.some e) ∧ B e q.world ∧ U e q.world := by
  rw [positive_donkey B U hx]
  exact Iff.or Iff.rfl (mem_pred1_pred1_randomAssign B U)

theorem mem_negative_donkey {r : Possibility W V (Part E)} :
    r ∈ (donkey B U x).negative s ↔
      ∃ q ∈ s, ∃ e : E, r = q.update x (.some e) ∧ B e q.world ∧ ¬ U e q.world := by
  rw [negative_donkey, negative_pred1]
  exact mem_pred1_pred1_randomAssign B _

theorem mem_world_negative_donkey {w : W} :
    w ∈ Possibility.world '' (donkey B U x).negative s ↔
      (∃ p ∈ s, p.world = w) ∧ ∃ e, B e w ∧ ¬ U e w := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨q, hq, e, rfl, hB, hU⟩ := (mem_negative_donkey B U).1 hr
    exact ⟨⟨q, hq, rfl⟩, e, hB, hU⟩
  · rintro ⟨⟨q, hq, rfl⟩, e, hB, hU⟩
    exact ⟨q.update x (.some e), (mem_negative_donkey B U).2 ⟨q, hq, e, rfl, hB, hU⟩, rfl⟩

theorem assertable_donkey [Nonempty E] (hx : State.Novel s x) : (donkey B U x).Assertable s := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ ?_
  have hle (e : E) : p ≤ p.update x (.some e) := Possibility.le_update_of_notMem (hx p hp) _
  by_cases hb : ∃ e, B e p.world
  · obtain ⟨e, hB⟩ := hb
    by_cases hU : U e p.world
    · exact hpos ⟨_, (mem_positive_donkey B U hx).2 (.inr ⟨p, hp, e, rfl, hB, hU⟩), hle e⟩
    · exact hneg ⟨_, (mem_negative_donkey B U).2 ⟨p, hp, e, rfl, hB, hU⟩, hle e⟩
  · push Not at hb
    exact hpos (subset_lowerClosure ((mem_positive_donkey B U hx).2 (.inl ⟨hp, hb⟩)))

theorem ex7 [Nonempty E] (hx : State.Novel s x) :
    (donkey B U x).Assertable s ↔ Examples.ex_7.judgment = .acceptable :=
  iff_of_true (assertable_donkey B U hx) rfl

/-! ### The law of non-contradiction (§2.4.3) -/

/-- The donkey disjunction and its negation hold together exactly where there is a bathroom in a
funny place and a bathroom elsewhere, (37). -/
theorem nonempty_lnc_iff [Nonempty E] (hx : State.Novel s x) :
    ((donkey B U x ⊙ ~(donkey B U x)).positive s).Nonempty ↔
      ∃ p ∈ s, (∃ e, B e p.world ∧ U e p.world) ∧ ∃ e, B e p.world ∧ ¬ U e p.world := by
  rw [positive_conj, positive_neg]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, hq, e, rfl, hB, hU⟩ := (mem_negative_donkey B U).1 hr
    rcases (mem_positive_donkey B U hx).1 hq with ⟨-, hno⟩ | ⟨p, hp, e', rfl, hB', hU'⟩
    · exact absurd hB (hno e)
    · exact ⟨p, hp, ⟨e', hB', hU'⟩, e, hB, hU⟩
  · rintro ⟨p, hp, ⟨e', hB', hU'⟩, e, hB, hU⟩
    exact ⟨_, (mem_negative_donkey B U).2 ⟨p.update x (.some e'),
      (mem_positive_donkey B U hx).2 (.inr ⟨p, hp, e', rfl, hB', hU'⟩), e, rfl, hB, hU⟩⟩

/-! ### Exhaustive assertion (§3) -/

/-- Exhaustive assertion of `φ` at `c` relative to a question under discussion `Q`, (46): the
points of the positive update whose world shares a cell of `Q` with a world of `c` that the
negative update does not reach. At the fact-finding question `⊥` every world is its own cell,
which is (45). -/
def exhAssert (Q : Setoid W) (φ : BilateralUpdate W V E) (c : Set (Possibility W V (Part E))) :
    Set (Possibility W V (Part E)) :=
  {p ∈ φ.positive c | ∃ w ∈ Possibility.world '' c, Q p.world w ∧
    w ∉ Possibility.world '' φ.negative c}

theorem world_mem_of_mem_positive_donkey [Nonempty E] (hx : State.Novel s x)
    {p : Possibility W V (Part E)} (hp : p ∈ (donkey B U x).positive s) :
    p.world ∈ Possibility.world '' s := by
  rcases (mem_positive_donkey B U hx).1 hp with ⟨hp, -⟩ | ⟨q, hq, e, rfl, -⟩
  exacts [⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩]

/-- Asserted exhaustively at the fact-finding question, the donkey disjunction keeps exactly the
worlds where every bathroom is in a funny place. -/
theorem world_exhAssert_bot [Nonempty E] (hx : State.Novel s x) :
    Possibility.world '' exhAssert ⊥ (donkey B U x) s =
      Possibility.world '' s ∩ {w | ∀ e, B e w → U e w} := by
  ext w
  constructor
  · rintro ⟨p, ⟨hp, w', -, hw', hneg⟩, rfl⟩
    obtain rfl : p.world = w' := hw'
    have hs := world_mem_of_mem_positive_donkey B U hx hp
    exact ⟨hs, fun e hB ↦ by_contra fun hU ↦
      hneg ((mem_world_negative_donkey B U).2 ⟨hs, e, hB, hU⟩)⟩
  · rintro ⟨⟨p, hp, rfl⟩, h⟩
    have hneg : p.world ∉ Possibility.world '' (donkey B U x).negative s := fun hw ↦
      let ⟨_, e, hB, hU⟩ := (mem_world_negative_donkey B U).1 hw
      hU (h e hB)
    by_cases hb : ∃ e, B e p.world
    · obtain ⟨e, hB⟩ := hb
      exact ⟨p.update x (.some e), ⟨(mem_positive_donkey B U hx).2
        (.inr ⟨p, hp, e, rfl, hB, h e hB⟩), p.world, ⟨p, hp, rfl⟩, rfl, hneg⟩, rfl⟩
    · push Not at hb
      exact ⟨p, ⟨(mem_positive_donkey B U hx).2 (.inl ⟨hp, hb⟩), p.world, ⟨p, hp, rfl⟩, rfl,
        hneg⟩, rfl⟩

theorem world_exhAssert_bot_neg [Nonempty E] (hx : State.Novel s x) :
    Possibility.world '' exhAssert ⊥ (~(donkey B U x)) s =
      Possibility.world '' s ∩ {w | (∃ e, B e w) ∧ ∀ e, B e w → ¬ U e w} := by
  ext w
  constructor
  · rintro ⟨p, ⟨hp, w', -, hw', hpos⟩, rfl⟩
    obtain rfl : p.world = w' := hw'
    obtain ⟨⟨q, hq, hqw⟩, e, hB, -⟩ := (mem_world_negative_donkey B U).1 ⟨p, hp, rfl⟩
    refine ⟨⟨q, hq, hqw⟩, ⟨e, hB⟩, fun e' hB' hU' ↦ hpos ⟨q.update x (.some e'),
      (mem_positive_donkey B U hx).2 (.inr ⟨q, hq, e', rfl, hqw ▸ hB', hqw ▸ hU'⟩), hqw⟩⟩
  · rintro ⟨⟨p, hp, rfl⟩, ⟨e, hB⟩, h⟩
    have hpos : p.world ∉ Possibility.world '' (donkey B U x).positive s := by
      rintro ⟨r, hr, hrw⟩
      rcases (mem_positive_donkey B U hx).1 hr with ⟨-, hno⟩ | ⟨q, -, e', rfl, hB', hU'⟩
      · exact hno e (hrw ▸ hB)
      · exact h e' (hrw ▸ hB') (hrw ▸ hU')
    exact ⟨p.update x (.some e), ⟨(mem_negative_donkey B U).2 ⟨p, hp, e, rfl, hB, h e hB⟩, p.world,
      ⟨p, hp, rfl⟩, rfl, hpos⟩, rfl⟩

theorem ex12 [Nonempty E] (hx : State.Novel s x) :
    (∀ w ∈ Possibility.world '' exhAssert ⊥ (~(donkey B U x)) s, ∀ e, B e w → ¬ U e w) ↔
      Examples.ex_12.judgment = .acceptable := by
  refine iff_of_true (fun w hw ↦ ?_) rfl
  rw [world_exhAssert_bot_neg B U hx] at hw
  exact hw.2.2

theorem exhAssert_top (h : ∃ p ∈ s, ∀ e, B e p.world → U e p.world) :
    exhAssert ⊤ (donkey B U x) s = (donkey B U x).positive s := by
  obtain ⟨q, hq, hqU⟩ := h
  refine Set.ext fun p ↦ ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, q.world, ⟨q, hq, rfl⟩, trivial, ?_⟩⟩
  rintro hw
  obtain ⟨-, e, hB, hU⟩ := (mem_world_negative_donkey B U).1 hw
  exact hU (hqU e hB)

end Donkey

omit [DecidableEq V] in
-- (47)
theorem lift_material_eq_disj (φ ψ : BilateralUpdate W V E) :
    lift (fun a b ↦ aᶜ ⊔ b) φ ψ = (~φ) ⊕ ψ := by
  have key (c : Trivalent) (p : Possibility W V (Part E)) (s) :
      (∃ a b, aᶜ ⊔ b = c ∧ p ∈ ψ.update b (φ.update a s)) ↔
        ∃ a b, a ⊔ b = c ∧ p ∈ ψ.update b ((~φ).update a s) := by
    simp only [update_neg]
    exact ⟨fun ⟨a, b, h, hp⟩ ↦ ⟨aᶜ, b, h, by simpa using hp⟩,
      fun ⟨a, b, h, hp⟩ ↦ ⟨aᶜ, b, by simpa using h, hp⟩⟩
  ext s p
  · simpa [disj] using key .true p s
  · simp [disj]

/-! ### Existential statements (§2.3) -/

-- (24)
theorem familiar_positive_neg_neg_exists (P : E → W → Prop)
    (s : Set (Possibility W V (Part E))) :
    State.Familiar ((~~(exists_ x (pred1 P x))).positive s) x :=
  (State.familiar_randomAssign s x).mono Set.inter_subset_left

theorem ex24 :
    (∀ (s : Set (Possibility W V (Part E))) (P : E → W → Prop),
      State.Familiar ((~~(exists_ x (pred1 P x))).positive s) x) ↔
      Examples.ex_24.judgment = .acceptable :=
  iff_of_true (fun s P ↦ familiar_positive_neg_neg_exists P s) rfl

private theorem eq_of_le_update {X : Set V} (hs : State.UniformAt X s) (hx : x ∉ X)
    {p q : Possibility W V (Part E)} (hp : p ∈ s) (hq : q ∈ s) {m : Part E}
    (h : p ≤ q.update x m) : p = q := by
  refine Possibility.eq_of_le_of_domain_eq (Possibility.le_def.mpr
    ⟨(Possibility.le_def.mp h).1, fun v ↦ ?_⟩) ((hs p hp).trans (hs q hq).symm)
  by_cases hv : v = x
  · subst hv
    rw [Part.eq_bot_iff_not_dom.2 fun hd ↦ hx ((hs p hp).subset hd)]
    exact bot_le
  · simpa [Possibility.update, Function.update_of_ne hv] using (Possibility.le_def.mp h).2 v

private theorem mem_lowerClosure_pred2_randomAssign {X : Set V} (hs : State.UniformAt X s)
    (hx : x ∉ X) {y : V} (hyx : y ≠ x) (R : E → E → W → Prop) {p : Possibility W V (Part E)}
    (hp : p ∈ s) :
    p ∈ lowerClosure ((pred2 R x y).positive (State.randomAssign s x)) ↔
      ∃ a ∈ p.assignment y, ∃ e, R e a p.world := by
  have hy (q : Possibility W V (Part E)) (m : Part E) :
      (q.update x m).assignment y = q.assignment y := by
    simp [Possibility.update, Function.update_of_ne hyx]
  constructor
  · rintro ⟨r, hr, hpr⟩
    obtain ⟨⟨q, hq, m, rfl⟩, e, -, a, ha, hR⟩ := mem_positive_pred2.1 hr
    obtain rfl := eq_of_le_update hs hx hp hq hpr
    exact ⟨a, hy p _ ▸ ha, e, hR⟩
  · rintro ⟨a, ha, e, hR⟩
    exact ⟨p.update x (.some e), mem_positive_pred2.2 ⟨⟨p, hp, e, rfl⟩, e, by simp, a,
      (hy p _).symm ▸ ha, hR⟩,
      Possibility.le_update_of_notMem (fun hd ↦ hx ((hs p hp).subset hd)) _⟩

/-- At a state whose points all define the same referents, the denial of `∃x R(x, y)` at a novel
`x` keeps the points that define `y` and whose value for `y` nothing bears `R` to: the anaphoric
presupposition of `y` projects, (23). -/
theorem negative_exists_pred2 [Nonempty E] (R : E → E → W → Prop) {X : Set V} {y : V}
    (hs : State.UniformAt X s) (hx : x ∉ X) (hyx : y ≠ x) :
    (exists_ x (pred2 R x y)).negative s =
      {p ∈ s | ∃ a ∈ p.assignment y, ∀ e, ¬ R e a p.world} := by
  ext p
  refine ⟨fun ⟨hp, hpos, hneg⟩ ↦ ?_, fun ⟨hp, a, ha, h⟩ ↦ ⟨hp, fun hpos ↦ ?_, ?_⟩⟩
  · rw [negative_pred2] at hneg
    obtain ⟨a, ha, -⟩ := (mem_lowerClosure_pred2_randomAssign hs hx hyx
      (fun e a w ↦ ¬ R e a w) hp).1 hneg
    exact ⟨hp, a, ha, fun e he ↦
      hpos ((mem_lowerClosure_pred2_randomAssign hs hx hyx R hp).2 ⟨a, ha, e, he⟩)⟩
  · obtain ⟨a', ha', e, he⟩ := (mem_lowerClosure_pred2_randomAssign hs hx hyx R hp).1 hpos
    obtain rfl : a = a' := Part.mem_unique ha ha'
    exact h e he
  · obtain ⟨e⟩ := ‹Nonempty E›
    rw [negative_pred2]
    exact (mem_lowerClosure_pred2_randomAssign hs hx hyx (fun e a w ↦ ¬ R e a w) hp).2
      ⟨a, ha, e, h e⟩

-- (23)
theorem not_negative_exists_pred2 :
    ∃ (W E : Type) (x y : ℕ) (R : E → E → W → Prop) (s : Set (Possibility W ℕ (Part E))),
      (exists_ x (pred2 R x y)).negative s ≠
        {p ∈ s | ∃ a ∈ p.assignment y, ∀ e, ¬ R e a p.world} := by
  let p₀ : Possibility Unit ℕ (Part Unit) := Possibility.bot ()
  let s : Set (Possibility Unit ℕ (Part Unit)) := {p₀, p₀.update 1 (.some ())}
  refine ⟨Unit, Unit, 0, 1, fun _ _ _ ↦ False, s, fun h ↦ ?_⟩
  have hmem : p₀ ∈ (exists_ 0 (pred2 (fun _ _ _ ↦ False) 0 1)).negative s := by
    refine ⟨Set.mem_insert _ _, fun ⟨r, hr, _⟩ ↦ by simp at hr,
      (p₀.update 1 (.some ())).update 0 (.some ()),
      mem_negative_pred2.2 ⟨⟨_, Set.mem_insert_of_mem _ rfl, (), rfl⟩, (), by simp, (), by simp,
        not_false⟩, Possibility.bot_le⟩
  rw [h] at hmem
  obtain ⟨a, ha, -⟩ := hmem.2
  simp [p₀, Possibility.bot, Part.bot_eq_none, Part.notMem_none] at ha

-- (41b)
theorem not_egli_negative :
    ∃ (W E : Type) (x : ℕ) (P Q : E → W → Prop) (s : Set (Possibility W ℕ (Part E))),
      (exists_ x (pred1 P x ⊙ pred1 Q x)).negative s ≠
        (exists_ x (pred1 P x) ⊙ pred1 Q x).negative s := by
  refine ⟨Unit, Unit, 0, fun _ _ ↦ True, fun _ _ ↦ False, {Possibility.bot ()}, fun h ↦ ?_⟩
  have hmem : (Possibility.bot () : Possibility Unit ℕ (Part Unit)).update 0 (.some ()) ∈
      (exists_ 0 (pred1 (fun _ _ ↦ True) 0) ⊙ pred1 (fun _ _ ↦ False) 0).negative
        {Possibility.bot ()} := by
    have h₁ : (Possibility.bot () : Possibility Unit ℕ (Part Unit)).update 0 (.some ()) ∈
        (pred1 (fun _ _ ↦ True) 0).positive
          (State.randomAssign ({Possibility.bot ()} : Set (Possibility Unit ℕ (Part Unit))) 0) :=
      mem_positive_pred1.2 ⟨⟨_, rfl, (), rfl⟩, (), by simp, trivial⟩
    have h₂ : (Possibility.bot () : Possibility Unit ℕ (Part Unit)).update 0 (.some ()) ∈
        (pred1 (fun _ _ ↦ False) 0).negative ((pred1 (fun _ _ ↦ True) 0).positive
          (State.randomAssign ({Possibility.bot ()} : Set (Possibility Unit ℕ (Part Unit))) 0)) :=
      mem_negative_pred1.2 ⟨h₁, (), by simp, not_false⟩
    simp only [conj, mem_negative_lift]
    exact ⟨.true, .false, rfl, by rw [update_false, update_true]; exact h₂⟩
  rw [← h] at hmem
  have := congrArg (fun p : Possibility Unit ℕ (Part Unit) ↦ p.assignment 0)
    (Set.mem_singleton_iff.mp (negative_exists_subset _ _ _ hmem))
  simp [Possibility.bot] at this

/-! ### Assertion (§2.4.1) -/

-- §2.4.1, before (26)
theorem assertable_not_familiar :
    ∃ s : Set (Possibility Unit ℕ (Part Unit)),
      (pred1 (fun _ _ ↦ True) 0).Assertable s ∧ ¬ State.Familiar s 0 := by
  let p₀ : Possibility Unit ℕ (Part Unit) := Possibility.bot ()
  have h₁ : p₀.update 0 (.some ()) ∈
      (pred1 (fun _ _ ↦ True) 0).positive {p₀.update 0 (.some ()), p₀} := by simp
  refine ⟨{p₀.update 0 (.some ()), p₀},
    Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, _⟩ ↦ hpos ?_,
    fun h ↦ by simpa [p₀] using h p₀ (Set.mem_insert_of_mem _ rfl)⟩
  rcases hp with rfl | rfl
  · exact subset_lowerClosure h₁
  · exact ⟨_, h₁, Possibility.le_update_of_notMem (by simp [p₀]) _⟩

end Elliott2023
