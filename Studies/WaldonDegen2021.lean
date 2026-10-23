module

public import Linglib.Pragmatics.RSA.Incremental
public import Studies.DegenEtAl2020
public import Linglib.Data.Examples.WaldonDegen2021

/-!
# Waldon and Degen (2021): Modeling Cross-Linguistic Production of Referring Expressions

Waldon and Degen's continuous-incremental rational speech act model of redundant modification,
which joins two earlier models. From Cohn-Gordon, Goodman and Potts it takes word-by-word
production: an incomplete string means the average of the complete utterances that continue it,
the speaker chooses each word against a listener who hears the string so far, and the probability
of an utterance is the product of its word choices. From Degen and colleagues it takes the
continuous semantics, on which an adjective of semantic value `v` holds to degree `v` of the pins
it is true of and to degree `1 − v` of the others. The incremental model with Boolean meanings is
the case of both values one.

English puts both adjectives before the noun, and the paper's postnominal Spanish puts both after
it, colour first. The Spanish alternatives are then the mirror image of the English ones, with
size and colour exchanged, so the Spanish speaker in a scene is the English speaker in the
counterpart of the scene with the two semantic values exchanged.

## Main statements

* `spanish_cs_production_eq_english_ss`, `spanish_ss_production_eq_english_cs`: for the small blue
  pin, *pin blue small* in one scene of Spanish is as likely as *small blue pin* in the other
  scene of English with the semantic values exchanged. With equal values, and so with Boolean
  meanings, redundant size in Spanish is as likely as redundant colour in English, and redundant
  colour in Spanish as redundant size in English.
* `english_step_eq_sigmoid`: after *small*, the English speaker adds the redundant *blue* with a
  probability that is a logistic function of the log of the gain of the redundant adjective, less
  its cost.
* `spanish_size_step_lt_english_color_step_iff`: the Spanish speaker adds the redundant size after
  *pin blue* less readily than the English speaker adds the redundant colour after *small*
  exactly when size is noisier than colour.
* `meaning_perm`: the meaning of an utterance does not depend on the order of its words, so a
  speaker who chooses among whole utterances cannot tell the two languages apart.

## Implementation notes

* The word-level speaker `step` is the speaker of Degen and colleagues at the string meaning, so
  the redundancy step is their comparison of the redundant with the sufficient expression.
* A scene lists three pins in the order of the paper's first figure, with the target last.
* The costs are any that give a word and its counterpart the same cost. The paper charges each
  adjective 0.1 and the noun and the stop token nothing.

## TODO

* The paper prints the utility of the incremental speaker without the logarithm. The transition
  probabilities of its third figure are those of the speaker with the logarithm, which is the one
  formalized.
* The utterance probabilities at the simulated values, the split and conjunctive Spanish
  idiolects, and the comparison over parameter values are not encoded.

## References

* [waldon-degen-2021]
* [cohn-gordon-goodman-potts-2019]
* [degen-etal-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace WaldonDegen2021

open MeasureTheory ProbabilityTheory RSA DegenEtAl2020

/-! ### Words and their meanings -/

/-- The words of the reference game, with a stop token that closes an utterance. -/
inductive Word where
  | blue
  | red
  | big
  | small
  | pin
  | stop
  deriving DecidableEq, Fintype

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- A word is true of a pin of a given size and colour. The noun and the stop token are true of
every pin. -/
def Word.Holds : Word → Size × Color → Prop
  | .big, r => r.1 = .big
  | .small, r => r.1 = .small
  | .blue, r => r.2 = .blue
  | .red, r => r.2 = .red
  | .pin, _ => True
  | .stop, _ => True

instance : ∀ (w : Word) (r : Size × Color), Decidable (w.Holds r)
  | .big, r => inferInstanceAs (Decidable (r.1 = .big))
  | .small, r => inferInstanceAs (Decidable (r.1 = .small))
  | .blue, r => inferInstanceAs (Decidable (r.2 = .blue))
  | .red, r => inferInstanceAs (Decidable (r.2 = .red))
  | .pin, _ => inferInstanceAs (Decidable True)
  | .stop, _ => inferInstanceAs (Decidable True)

/-- The semantic value of a word is `vs` for a size adjective, `vc` for a colour adjective, and
one for the noun and the stop token. -/
def value (vs vc : ℝ) : Word → ℝ
  | .big | .small => vs
  | .blue | .red => vc
  | .pin | .stop => 1

/-- In the continuous lexicon a word holds of a pin it is true of to the degree of its semantic
value, and of any other pin to the complementary degree. -/
def lexicon (vs vc : ℝ) (w : Word) (r : Size × Color) : ℝ := noisy (value vs vc w) (w.Holds r)

/-! ### Languages and scenes -/

/-- English puts size, then colour, before the noun. -/
def english : List (List Word) :=
  [[.blue, .pin, .stop], [.red, .pin, .stop], [.big, .pin, .stop], [.small, .pin, .stop],
   [.small, .blue, .pin, .stop], [.small, .red, .pin, .stop],
   [.big, .blue, .pin, .stop], [.big, .red, .pin, .stop]]

/-- Postnominal Spanish puts colour, then size, after the noun. -/
def spanish : List (List Word) :=
  [[.pin, .blue, .stop], [.pin, .red, .stop], [.pin, .big, .stop], [.pin, .small, .stop],
   [.pin, .blue, .small, .stop], [.pin, .red, .small, .stop],
   [.pin, .blue, .big, .stop], [.pin, .red, .big, .stop]]

/-- A scene shows three pins, of which the third is the target. -/
abbrev Scene := Fin 3 → Size × Color

/-- The target of every prediction is the small blue pin, the third of each scene. -/
abbrev target : Fin 3 := 2

/-- In the size-sufficient scene the target is the only small pin. -/
def ss : Scene
  | 0 => (.big, .blue)
  | 1 => (.big, .red)
  | 2 => (.small, .blue)

/-- In the colour-sufficient scene the target is the only blue pin. -/
def cs : Scene
  | 0 => (.small, .red)
  | 1 => (.big, .red)
  | 2 => (.small, .blue)

/-- The alternatives of a language in a scene are its utterances true of one of the pins. -/
def alternatives (L : List (List Word)) (s : Scene) : List (List Word) :=
  L.filter fun u ↦ ∃ i, ∀ w ∈ u, w.Holds (s i)

/-- The continuous meaning of an utterance at a pin of the scene is the product of the degrees to
which its words hold of the pin. -/
def meaning (vs vc : ℝ) (s : Scene) (u : List Word) (i : Fin 3) : ℝ :=
  prodMeaning (lexicon vs vc) u (s i)

section Meaning

variable {vs vc : ℝ}

theorem meaning_nonneg (hs0 : 0 ≤ vs) (hs1 : vs ≤ 1) (hc0 : 0 ≤ vc) (hc1 : vc ≤ 1) (s : Scene)
    (u : List Word) (i : Fin 3) : 0 ≤ meaning vs vc s u i :=
  prodMeaning_nonneg (fun w r ↦ by
    cases w <;> exact noisy_nonneg (by simp [value, *]) (by simp [value, *]) _) u (s i)

theorem meaning_perm (s : Scene) {u u' : List Word} (h : u.Perm u') :
    meaning vs vc s u = meaning vs vc s u' :=
  funext fun i ↦ prodMeaning_perm h (s i)

theorem meaning_one_one (s : Scene) (u : List Word) (i : Fin 3) :
    meaning 1 1 s u i = if ∀ w ∈ u, w.Holds (s i) then 1 else 0 := by
  induction u with
  | nil => simp [meaning]
  | cons w u ih =>
    rw [meaning, prodMeaning_cons, ← meaning, ih, lexicon,
      show value 1 1 w = 1 by cases w <;> rfl, noisy]
    by_cases hw : w.Holds (s i) <;> simp [hw]

end Meaning

/-! ### The incremental speaker -/

/-- At a context the incremental speaker is the speaker of Degen and colleagues against a
listener who interprets the context extended by the next word as a string. -/
noncomputable def step (α : ℝ) (cost : Word → ℝ) (vs vc : ℝ) (L : List (List Word)) (s : Scene)
    (ctx : List Word) : Kernel (Fin 3) Word :=
  S1 α cost fun w i ↦ stringMeaning (alternatives L s) (meaning vs vc s) (ctx ++ [w]) i

/-- The probability of an utterance for the target is the product of its word choices. -/
noncomputable def production (α : ℝ) (cost : Word → ℝ) (vs vc : ℝ) (L : List (List Word))
    (s : Scene) (u : List Word) : ℝ :=
  chain (step α cost vs vc L s) target [] u

/-! ### Spanish as the mirror image of English -/

/-- The counterpart of a word exchanges size with colour, and the noun, which closes the
adjectives of an English utterance, with the stop token, which closes those of a Spanish one. -/
def mirror : Word → Word
  | .small => .blue
  | .blue => .small
  | .big => .red
  | .red => .big
  | .pin => .stop
  | .stop => .pin

theorem mirror_mirror (w : Word) : mirror (mirror w) = w := by cases w <;> rfl

/-- The counterpart of a pin exchanges its size with its colour, small with blue and big with
red. -/
def swap : Size × Color → Size × Color
  | (.small, .blue) => (.small, .blue)
  | (.big, .blue) => (.small, .red)
  | (.small, .red) => (.big, .blue)
  | (.big, .red) => (.big, .red)

/-- The Spanish counterpart of an English utterance puts the noun first and the counterparts of
the adjectives after it. -/
def mirrorUtterance (u : List Word) : List Word :=
  .pin :: u.dropLast.dropLast.map mirror ++ [.stop]

theorem cs_eq_swap_ss (i : Fin 3) : cs i = swap (ss i) := by revert i; decide

theorem ss_eq_swap_cs (i : Fin 3) : ss i = swap (cs i) := by revert i; decide

theorem alternatives_spanish_cs :
    (alternatives spanish cs).Perm ((alternatives english ss).map mirrorUtterance) := by decide

theorem alternatives_spanish_ss :
    (alternatives spanish ss).Perm ((alternatives english cs).map mirrorUtterance) := by decide

section Mirror

variable {vs vc α : ℝ} {cost : Word → ℝ} {s s' : Scene}

theorem lexicon_mirror (w : Word) (r : Size × Color) :
    lexicon vs vc (mirror w) (swap r) = lexicon vc vs w r := by
  obtain ⟨_ | _, _ | _⟩ := r <;> cases w <;> simp [lexicon, value, Word.Holds, mirror, swap]

theorem meaning_mirror (hs : ∀ i, s' i = swap (s i)) {u : List Word} (hu : u ∈ english)
    (i : Fin 3) : meaning vs vc s' (mirrorUtterance u) i = meaning vc vs s u i := by
  have hpin (a b : ℝ) (r : Size × Color) : lexicon a b .pin r = 1 := by
    simp [lexicon, value, Word.Holds, noisy]
  have hstop (a b : ℝ) (r : Size × Color) : lexicon a b .stop r = 1 := by
    simp [lexicon, value, Word.Holds, noisy]
  simp only [english, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mirrorUtterance, meaning, prodMeaning, hs, lexicon_mirror, hpin, hstop]

private theorem step_mirror (hcost : ∀ w, cost (mirror w) = cost w)
    (hs : ∀ i, s' i = swap (s i))
    (hperm : (alternatives spanish s').Perm ((alternatives english s).map mirrorUtterance))
    {ctx ctx' : List Word}
    (hpfx : ∀ w, ∀ u ∈ alternatives english s,
      (ctx' ++ [mirror w]) <+: mirrorUtterance u ↔ (ctx ++ [w]) <+: u)
    (w : Word) (i : Fin 3) :
    step α cost vs vc spanish s' ctx' i {mirror w} = step α cost vc vs english s ctx i {w} := by
  have := S1_apply_singleton_of_equiv (Function.Involutive.toPerm mirror mirror_mirror) α cost
    (m := fun w i ↦ stringMeaning (alternatives english s) (meaning vc vs s) (ctx ++ [w]) i)
    (m' := fun w i ↦ stringMeaning (alternatives spanish s') (meaning vs vc s') (ctx' ++ [w]) i)
    (fun v ↦ funext fun i ↦ stringMeaning_eq_of_perm_map mirrorUtterance hperm (hpfx v)
      fun u hu ↦ meaning_mirror hs (List.mem_filter.1 hu).1 i) i w
  rw [show cost ∘ ⇑(Function.Involutive.toPerm mirror mirror_mirror) = cost from
    funext hcost] at this
  exact this

private theorem stringMeaning_nonneg' (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc) (hc1 : vc ≤ 1)
    (L : List (List Word)) (s : Scene) (ctx : List Word) (v : Word) (i : Fin 3) :
    0 ≤ stringMeaning (alternatives L s) (meaning vs vc s) (ctx ++ [v]) i :=
  stringMeaning_nonneg fun u _ ↦ meaning_nonneg hs0.le hs1 hc0.le hc1 s u i

private theorem step_real_eq_one (hα : 0 < α) (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc)
    (hc1 : vc ≤ 1) {L : List (List Word)} {ctx u : List Word} {w : Word}
    (h : ∀ v, v ≠ w → continuations (alternatives L s) (ctx ++ [v]) = [])
    (hu : u ∈ continuations (alternatives L s) (ctx ++ [w])) (hpos : 0 < meaning vs vc s u target) :
    (step α cost vs vc L s ctx target).real {w} = 1 :=
  S1_real_eq_one hα (stringMeaning_nonneg' hs0 hs1 hc0 hc1 L s ctx)
    (stringMeaning_pos (fun u _ ↦ meaning_nonneg hs0.le hs1 hc0.le hc1 s u target) hu hpos)
    fun v hv ↦ stringMeaning_of_continuations_eq_nil (h v hv) _

private theorem meaning_small_blue (ht : s target = (.small, .blue)) :
    meaning vs vc s [.small, .blue, .pin, .stop] target = vs * vc := by
  simp [meaning, prodMeaning, lexicon, value, Word.Holds, noisy, ht]

private theorem meaning_pin_blue_small (ht : s target = (.small, .blue)) :
    meaning vs vc s [.pin, .blue, .small, .stop] target = vc * vs := by
  simp [meaning, prodMeaning, lexicon, value, Word.Holds, noisy, ht]

private theorem production_mirror (hα : 0 < α) (hcost : ∀ w, cost (mirror w) = cost w)
    (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc) (hc1 : vc ≤ 1) (hs : ∀ i, s' i = swap (s i))
    (ht : s target = (.small, .blue)) (ht' : s' target = (.small, .blue))
    (hperm : (alternatives spanish s').Perm ((alternatives english s).map mirrorUtterance))
    (hchoice : ∀ w, ∀ u ∈ alternatives english s,
      ([Word.pin] ++ [mirror w]) <+: mirrorUtterance u ↔ ([] ++ [w]) <+: u)
    (hredundancy : ∀ w, ∀ u ∈ alternatives english s,
      ([Word.pin, Word.blue] ++ [mirror w]) <+: mirrorUtterance u ↔ ([Word.small] ++ [w]) <+: u)
    (he3 : ∀ v, v ≠ Word.pin →
      continuations (alternatives english s) ([Word.small, Word.blue] ++ [v]) = [])
    (he3' : [Word.small, Word.blue, Word.pin, Word.stop] ∈
      continuations (alternatives english s) ([Word.small, Word.blue] ++ [Word.pin]))
    (he4 : ∀ v, v ≠ Word.stop →
      continuations (alternatives english s) ([Word.small, Word.blue, Word.pin] ++ [v]) = [])
    (he4' : [Word.small, Word.blue, Word.pin, Word.stop] ∈
      continuations (alternatives english s) ([Word.small, Word.blue, Word.pin] ++ [Word.stop]))
    (hs1' : ∀ v, v ≠ Word.pin → continuations (alternatives spanish s') ([] ++ [v]) = [])
    (hs1'' : [Word.pin, Word.blue, Word.small, Word.stop] ∈
      continuations (alternatives spanish s') ([] ++ [Word.pin]))
    (hs4 : ∀ v, v ≠ Word.stop →
      continuations (alternatives spanish s') ([Word.pin, Word.blue, Word.small] ++ [v]) = [])
    (hs4' : [Word.pin, Word.blue, Word.small, Word.stop] ∈
      continuations (alternatives spanish s') ([Word.pin, Word.blue, Word.small] ++ [Word.stop])) :
    production α cost vs vc spanish s' [.pin, .blue, .small, .stop] =
      production α cost vc vs english s [.small, .blue, .pin, .stop] := by
  have h1 : step α cost vs vc spanish s' [.pin] target {.blue} =
      step α cost vc vs english s [] target {.small} :=
    step_mirror hcost hs hperm hchoice .small target
  have h2 : step α cost vs vc spanish s' [.pin, .blue] target {.small} =
      step α cost vc vs english s [.small] target {.blue} :=
    step_mirror hcost hs hperm hredundancy .blue target
  have e3 : (step α cost vc vs english s [.small, .blue] target).real {.pin} = 1 :=
    step_real_eq_one hα hc0 hc1 hs0 hs1 he3 he3' (by rw [meaning_small_blue ht]; positivity)
  have e4 : (step α cost vc vs english s [.small, .blue, .pin] target).real {.stop} = 1 :=
    step_real_eq_one hα hc0 hc1 hs0 hs1 he4 he4' (by rw [meaning_small_blue ht]; positivity)
  have s1 : (step α cost vs vc spanish s' [] target).real {.pin} = 1 :=
    step_real_eq_one hα hs0 hs1 hc0 hc1 hs1' hs1''
      (by rw [meaning_pin_blue_small ht']; positivity)
  have s4 : (step α cost vs vc spanish s' [.pin, .blue, .small] target).real {.stop} = 1 :=
    step_real_eq_one hα hs0 hs1 hc0 hc1 hs4 hs4'
      (by rw [meaning_pin_blue_small ht']; positivity)
  simp only [production, chain_cons, chain_nil, List.nil_append, List.cons_append, mul_one]
  rw [s1, s4, e3, e4, measureReal_def, measureReal_def, h1, h2, ← measureReal_def,
    ← measureReal_def]
  ring

theorem spanish_cs_production_eq_english_ss (hα : 0 < α)
    (hcost : ∀ w, cost (mirror w) = cost w) (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc)
    (hc1 : vc ≤ 1) :
    production α cost vs vc spanish cs [.pin, .blue, .small, .stop] =
      production α cost vc vs english ss [.small, .blue, .pin, .stop] :=
  production_mirror hα hcost hs0 hs1 hc0 hc1 cs_eq_swap_ss rfl rfl alternatives_spanish_cs
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem spanish_ss_production_eq_english_cs (hα : 0 < α)
    (hcost : ∀ w, cost (mirror w) = cost w) (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc)
    (hc1 : vc ≤ 1) :
    production α cost vs vc spanish ss [.pin, .blue, .small, .stop] =
      production α cost vc vs english cs [.small, .blue, .pin, .stop] :=
  production_mirror hα hcost hs0 hs1 hc0 hc1 ss_eq_swap_cs rfl rfl alternatives_spanish_ss
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### The redundancy step -/

theorem english_step_eq_sigmoid (hα : 0 < α) (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc)
    (hc1 : vc ≤ 1) :
    (step α cost vs vc english ss [.small] target).real {.blue} =
      Real.sigmoid (α * (Real.log (gain 1 vs vc) - (cost .blue - cost .pin))) := by
  have hb (i : Fin 3) : stringMeaning (alternatives english ss) (meaning vs vc ss)
      ([.small] ++ [.blue]) i = meaning vs vc ss [.small, .blue, .pin, .stop] i :=
    stringMeaning_of_continuations_eq_singleton (by decide) i
  have hp (i : Fin 3) : stringMeaning (alternatives english ss) (meaning vs vc ss)
      ([.small] ++ [.pin]) i = meaning vs vc ss [.small, .pin, .stop] i :=
    stringMeaning_of_continuations_eq_singleton (by decide) i
  have hdead : ∀ v, v ≠ .blue → v ≠ .pin →
      continuations (alternatives english ss) ([.small] ++ [v]) = [] := by decide
  have hpt : meaning vs vc ss [.small, .pin, .stop] target = vs := by
    simp [meaning, prodMeaning, lexicon, value, Word.Holds, noisy, ss]
  have hbs : ∑ i, meaning vs vc ss [.small, .blue, .pin, .stop] i = 1 - vs + vs * vc := by
    simp [Fin.sum_univ_three, meaning, prodMeaning, lexicon, value, Word.Holds, noisy, ss]
    ring
  have hps : ∑ i, meaning vs vc ss [.small, .pin, .stop] i = 2 - vs := by
    simp [Fin.sum_univ_three, meaning, prodMeaning, lexicon, value, Word.Holds, noisy, ss]
    ring
  have h1 : 0 < 1 - vs + vs * vc := by nlinarith
  rw [step, S1_real_of_pair hα (u' := .pin) (by decide)
      (stringMeaning_nonneg' hs0 hs1 hc0 hc1 english ss [.small])
      (by rw [hb, meaning_small_blue (s := ss) rfl]; positivity) (by rwa [hp, hpt])
      (fun v hv ↦ by
        by_contra h
        rw [not_or] at h
        exact hv.ne' (stringMeaning_of_continuations_eq_nil (hdead v h.1 h.2) _))]
  simp only [hb, hp, hbs, hps, meaning_small_blue (s := ss) rfl, hpt]
  rw [sub_sub_sub_comm, ← Real.log_div (div_pos (by positivity) h1).ne'
    (div_pos hs0 (by linarith)).ne', div_div_eq_gain_one hs0 hs1 hc0]

theorem boolean_english_step (hα : 0 < α) :
    (step α cost 1 1 english ss [.small] target).real {.blue} =
      Real.sigmoid (-(α * (cost .blue - cost .pin))) := by
  rw [english_step_eq_sigmoid hα one_pos le_rfl one_pos le_rfl, gain_one_left one_ne_zero,
    Real.log_one, zero_sub, mul_neg]

theorem spanish_size_step_lt_english_color_step_iff (hα : 0 < α)
    (hcost : ∀ w, cost (mirror w) = cost w) (hs0 : 0 < vs) (hs1 : vs ≤ 1) (hc0 : 0 < vc)
    (hc1 : vc ≤ 1) :
    (step α cost vs vc spanish cs [.pin, .blue] target).real {.small} <
      (step α cost vs vc english ss [.small] target).real {.blue} ↔ vs < vc := by
  have h : step α cost vs vc spanish cs [.pin, .blue] target {.small} =
      step α cost vc vs english ss [.small] target {.blue} :=
    step_mirror hcost cs_eq_swap_ss alternatives_spanish_cs (by decide) .blue target
  rw [measureReal_def, h, ← measureReal_def, english_step_eq_sigmoid hα hc0 hc1 hs0 hs1,
    english_step_eq_sigmoid hα hs0 hs1 hc0 hc1, Real.sigmoid_lt_iff, mul_lt_mul_iff_right₀ hα,
    sub_lt_sub_iff_right, Real.log_lt_log_iff (gain_pos hc0 hc1 hs0 hs1)
      (gain_pos hs0 hs1 hc0 hc1), gain_swap_lt_iff one_pos hs0 hs1 hc0 hc1]

end Mirror

end WaldonDegen2021
