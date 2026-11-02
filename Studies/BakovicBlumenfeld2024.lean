module

public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.Subregular.LocalRewrite
public import Linglib.Fragments.Finnish.Phonology
public import Linglib.Fragments.Turkish.Phonology

/-!
# Baković and Blumenfeld (2024): A formal typology of process interactions

This file formalizes the algebra of interactions between two maps on strings. The input set of a map
holds the strings it changes, its output set their images, and the input-rank of a string the most
pieces the map rewrites independently. The four atoms are feeding and bleeding of the other map's
input-rank or output set; feeding, bleeding and seeding are configurations of atoms, and an order is
opaque where the map applying first is input-provided or output-removed. [Raising gives
palatalization in *kike* a second locus the set-based definitions miss](##feeds_kike),
[counterfeeding leaves the fed map's input on the surface](##underapplication), [seeding makes both
orders opaque](##seeding_turkish), and [flipping a feeding map makes it bleed](##Feeding.flip).

## Implementation notes

* The pieces of a nonvacuous break are nonempty, so the input-rank of a string is at most its
  length.
* Output interactions are the paper's case (26), where one of the two strings has no nonvacuous
  input, so they compare membership in the output set.
* The rules are the library's local rewrite rules, except epenthesis, which inserts and is a
  map. The Bedouin Arabic, Polish and hypothetical forms use chart segments, the Finnish and
  Turkish forms their fragments' phonemes.

## TODO

* Output-rank for strings with several nonvacuous inputs (25), misapplication in Palestinian
  Arabic and Yokuts, the typology of §5, and cropping.

## References

* [bakovic-blumenfeld-2024]
* [kiparsky-1968]
-/

@[expose] public section

namespace BakovicBlumenfeld2024

open Function RuleInteraction Phonology Subregular.LocalRewrite Data.PHOIBLE

/-! ### Input and output sets, input-rank -/

section Maps

variable {σ : Type*} (P Q : List σ → List σ)

/-- The input set of a map (§3.1), the strings it maps nonvacuously. -/
def inputSet : Set (List σ) := {x | P x ≠ x}

/-- The output set of a map (§3.1), the strings it maps some other string onto. -/
def outputSet : Set (List σ) := P '' inputSet P

/-- The breaks of a string into nonempty pieces. -/
def breaks : List σ → List (List (List σ))
  | [] => [[]]
  | a :: x => (breaks x).flatMap fun
    | [] => [[[a]]]
    | b :: bs => [[a] :: b :: bs, (a :: b) :: bs]

-- (20a): the breaks of `x` are the lists of nonempty pieces concatenating to `x`
theorem mem_breaks {x : List σ} {bs : List (List σ)} :
    bs ∈ breaks x ↔ bs.flatten = x ∧ ∀ b ∈ bs, b ≠ [] := by
  induction x generalizing bs with
  | nil =>
    simp only [breaks, List.mem_singleton]
    refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ ↦ ?_⟩
    simpa [List.flatten_eq_nil_iff, List.eq_nil_iff_forall_not_mem] using
      fun b hb ↦ h₂ b hb (List.flatten_eq_nil_iff.mp h₁ b hb)
  | cons a x ih =>
    simp only [breaks, List.mem_flatMap]
    constructor
    · rintro ⟨cs, hcs, hbs⟩
      obtain ⟨hf, hn⟩ := ih.mp hcs
      match cs, hbs with
      | [], hbs => simp at hbs; subst hbs; simp_all
      | c :: cs, hbs =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbs
        rcases hbs with rfl | rfl <;> simp_all
    · rintro ⟨hf, hn⟩
      match bs, hf, hn with
      | [], hf, _ => simp at hf
      | [] :: _, _, hn => exact absurd rfl (hn [] (by simp))
      | (a' :: b) :: rest, hf, hn =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        cases b with
        | nil =>
          refine ⟨rest, ih.mpr ⟨by simp, fun c hc ↦ hn c (by simp [hc])⟩, ?_⟩
          cases rest <;> simp
        | cons b₀ b =>
          refine ⟨(b₀ :: b) :: rest, ih.mpr ⟨by simp, fun c hc ↦ ?_⟩, by simp⟩
          rcases List.mem_cons.mp hc with rfl | hc
          · simp
          · exact hn c (by simp [hc])

/-- A break of `x` is nonvacuous for `P` (20) when `P` rewrites each piece and the images
concatenate to `P x`. -/
def IsNonvacuousBreak (x : List σ) (bs : List (List σ)) : Prop :=
  (bs.map P).flatten = P x ∧ ∀ b ∈ bs, b ∈ inputSet P

variable [DecidableEq σ]

instance : DecidablePred (· ∈ inputSet P) := fun x ↦ inferInstanceAs (Decidable (P x ≠ x))

instance (x : List σ) : DecidablePred (IsNonvacuousBreak P x) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The input-rank of a string (21): `0` outside the input set, and otherwise the largest rank of
a nonvacuous break, which the string itself gives rank `1`. -/
def inputRank (x : List σ) : ℕ :=
  if P x = x then 0 else (((breaks x).filter (IsNonvacuousBreak P x)).map List.length).foldr max 1

variable {P Q} {x : List σ}

theorem inputRank_pos_iff : 0 < inputRank P x ↔ x ∈ inputSet P := by
  unfold inputRank
  split_ifs with h
  · simp [inputSet, h]
  · refine iff_of_true ?_ h
    generalize List.map _ _ = l
    induction l with
    | nil => exact one_pos
    | cons n l ih => exact ih.trans_le (le_max_right _ _)

/-- Provisional feeding (18), making a string the second map applies to, is input-provision (23). -/
theorem feeds_inputRank (h : Feeds P (· ∈ inputSet Q) x) : Feeds P (inputRank Q) x := by
  refine Feeds.of_comp (φ := (0 < ·)) (fun _ _ hab h ↦ h.trans_le hab) ?_
  simpa [Function.comp_def, inputRank_pos_iff] using h

theorem bleeds_inputRank (h : Bleeds P (· ∈ inputSet Q) x) : Bleeds P (inputRank Q) x := by
  refine Bleeds.of_comp (φ := (0 < ·)) (fun _ _ hab h ↦ h.trans_le hab) ?_
  simpa [Function.comp_def, inputRank_pos_iff] using h

omit [DecidableEq σ] in
/-- In the counterfeeding order the fed map underapplies: where `P` makes a string `Q` applies
to, applying `Q` first changes nothing, and `P` then gives a string in `Q`'s input set. -/
theorem underapplication (h : Feeds P (· ∈ inputSet Q) x) :
    P (Q x) = P x ∧ P (Q x) ∈ inputSet Q := by
  have hQ : Q x = x := h.isFixedPt fun _ ↦ not_not.mp
  rw [hQ]
  exact ⟨rfl, (feeds_iff.mp h).2⟩

end Maps

/-! ### Molecules and opacity -/

section Molecules

variable {σ : Type*} [DecidableEq σ] {P Q P' : List σ → List σ} {a b c d : List σ}

/-- `P` **feeds** `Q` at `(a, b, c, d)` (27a): `P` maps `a` to `b` and `d` to `c`, `Q` maps `b`
to `c`, `P` input-provides `Q` at `a` and output-provides it at `d`. -/
structure Feeding (P Q : List σ → List σ) (a b c d : List σ) : Prop where
  map_a : P a = b
  map_b : Q b = c
  map_d : P d = c
  inputProvides : Feeds P (inputRank Q) a
  outputProvides : Feeds P (· ∈ outputSet Q) d

/-- `P` **bleeds** `Q` at `(a, b, c, d)` (27b): `P` maps `a` to `b` and `c` to `d`, `Q` maps `a`
to `c`, `P` input-removes `Q` at `a` and output-removes it at `c`. -/
structure Bleeding (P Q : List σ → List σ) (a b c d : List σ) : Prop where
  map_a : P a = b
  map_a' : Q a = c
  map_c : P c = d
  inputRemoves : Bleeds P (inputRank Q) a
  outputRemoves : Bleeds P (· ∈ outputSet Q) c

/-- `P` **seeds** `Q` at `(a, b, c)` (28): `P` maps `a` to `b`, `Q` maps `b` to `c`, `P`
input-provides `Q` at `a`, and `Q` output-removes `P` at `b`. -/
structure Seeding (P Q : List σ → List σ) (a b c : List σ) : Prop where
  map_a : P a = b
  map_b : Q b = c
  inputProvides : Feeds P (inputRank Q) a
  outputRemoves : Bleeds Q (· ∈ outputSet P) b

/-- Ordered before `Y`, the map `X` **underapplies** (30a) when `Y` input-provides `X`. -/
def Underapplies (X Y : List σ → List σ) : Prop := ∃ x, Feeds Y (inputRank X) x

/-- Ordered before `Y`, the map `X` **misapplies** (31b) when `Y` output-removes `X`;
overapplication is the case in which the transparent alternative is vacuous. -/
def Misapplies (X Y : List σ → List σ) : Prop := ∃ x, Bleeds Y (· ∈ outputSet X) x

-- §4.1: a fed map ordered first underapplies
theorem Feeding.underapplies (h : Feeding P Q a b c d) : Underapplies Q P := ⟨a, h.inputProvides⟩

-- §4.1: a bled map ordered first misapplies
theorem Bleeding.misapplies (h : Bleeding P Q a b c d) : Misapplies Q P := ⟨c, h.outputRemoves⟩

-- §4.1: under seeding both orders are opaque
theorem Seeding.opaque (h : Seeding P Q a b c) : Underapplies Q P ∧ Misapplies P Q :=
  ⟨⟨a, h.inputProvides⟩, ⟨b, h.outputRemoves⟩⟩

/-- Flipping turns feeding into bleeding (§6): a map reversing the two arrows of a feeding map
bleeds what it fed. -/
theorem Feeding.flip (h : Feeding P Q a b c d) (hb : P' b = a) (hc : P' c = d) :
    Bleeding P' Q b a c d := by
  obtain ⟨rfl, hQ, rfl, hi, ho⟩ := h
  exact ⟨hb, hQ, hc, (bleeds_iff_feeds_of_apply_eq hb).2 hi,
    (bleeds_iff_feeds_of_apply_eq hc).2 ho⟩

end Molecules

/-! ### Replacement rules

A rule that replaces its target and reads nothing to its left maps onto a string only from the
string itself, unless an occurrence of the replacing segment stands before the rule's right
context. -/

section Replacement

variable {r : Rule} {t : Segment}

theorem eq_of_apply_eq (hl : r.leftReach = 0) (he : r.effect = .replace t) {x y : List Segment}
    (hy : ∀ j (hj : j < y.length), y[j] = t → ¬ MatchesRight r.rightContext (y.drop (j + 1)))
    (h : r.apply x = y) : x = y := by
  have hc : r.leftContext = [] := List.length_eq_zero_iff.mp (by
    have := le_max_left r.leftContext.length r.effect.leftReach
    rw [← Rule.leftReach, hl] at this; omega)
  induction x generalizing y with
  | nil => simpa [Rule.apply, Rule.apply.go] using h.symm
  | cons s x ih =>
    have hv : r.verdict [] s x =
        [if r.target ≤ s ∧ MatchesRight r.rightContext x then t else s] := by
      simp only [Rule.verdict, hc, he, Effect.apply, MatchesLeft, List.reverse_nil, MatchesRight,
        true_and]
      split_ifs <;> rfl
    rw [Rule.apply_cons_of_leftReach_eq_zero hl, hv, List.singleton_append] at h
    subst h
    have hx : x = r.apply x := ih (fun j hj hjt ↦ by
      simpa using hy (j + 1) (by simpa using hj) (by simpa using hjt)) rfl
    have h0 := hy 0 (by simp)
    rw [← hx] at h0 ⊢
    split_ifs at h0 ⊢ with hs
    · exact absurd hs.2 (by simpa using h0 rfl)
    · rfl

theorem notMem_outputSet (hl : r.leftReach = 0) (he : r.effect = .replace t) {y : List Segment}
    (hy : ∀ j (hj : j < y.length), y[j] = t → ¬ MatchesRight r.rightContext (y.drop (j + 1))) :
    y ∉ outputSet r.apply := fun ⟨_, hx, h⟩ ↦ hx (h.trans (eq_of_apply_eq hl he hy h).symm)

end Replacement

/-! ### Segments of the Bedouin Arabic, Polish and hypothetical examples -/

/-- A consonant, as a rule context. -/
def C : Segment := Segment.ofSpecs [(.syllabic, false)]

/-- A vowel, as a rule context. -/
def V : Segment := Segment.ofSpecs [(.syllabic, true)]

namespace Chart

/-- The segment /a/. -/
def a : Segment := .ofChart .«a»
/-- The segment /b/. -/
def b : Segment := .ofChart .«b»
/-- The segment /d/. -/
def d : Segment := .ofChart .«d»
/-- The segment /e/. -/
def e : Segment := .ofChart .«e»
/-- The segment /i/. -/
def i : Segment := .ofChart .«i»
/-- The segment /k/. -/
def k : Segment := .ofChart .«k»
/-- The segment /o/. -/
def o : Segment := .ofChart .«o»
/-- The segment /p/. -/
def p : Segment := .ofChart .«p»
/-- The segment /t/. -/
def t : Segment := .ofChart .«t»
/-- The segment /u/. -/
def u : Segment := .ofChart .«u»
/-- The segment /w/. -/
def w : Segment := .ofChart .«w»
/-- The segment /ʒ/. -/
def ezh : Segment := .ofChart .«ʒ»
/-- The segment /č/. -/
def č : Segment := .ofChart .«t̠ʃ»

end Chart

section ChartExamples

open Chart

/-! ### Input-rank and the second locus (19) -/

/-- Word-final raising `e → i / __ #` of (19). -/
def finalRaising : Rule := { target := e, effect := .replace i, rightContext := [.wordBoundary] }

/-- Velar palatalization `k → č / __ i` of (19). -/
def palatalization : Rule := { target := k, effect := .replace č, rightContext := [.seg i] }

/-- Final devoicing `[−son] → [−voi] / __ #` of (6). -/
def devoicing : Rule where
  target := Segment.ofSpecs [(.sonorant, false)]
  effect := .changeFeatures (Segment.ofSpecs [(.voice, false)])
  rightContext := [.wordBoundary]

-- (22): *kiki* breaks into two palatalizable pieces
theorem inputRank_kiki : inputRank palatalization.apply [k, i, k, i] = 2 := by decide +kernel

-- §3.3: *adad* has input-rank 1 for final devoicing, since *ad-ad* would give *atat*
theorem inputRank_adad : inputRank devoicing.apply [a, d, a, d] = 1 := by decide +kernel

/-- Raising gives palatalization a second locus in *kike*: it input-provides palatalization
(23), though *kike* is already in palatalization's input set, so raising does not feed it in the
set-based sense of (18). -/
theorem feeds_kike : Feeds finalRaising.apply (inputRank palatalization.apply) [k, i, k, e] ∧
    ¬ Feeds finalRaising.apply (· ∈ inputSet palatalization.apply) [k, i, k, e] := by
  decide +kernel

/-! ### Feeding and counterfeeding: Bedouin Arabic (5) -/

/-- Vocalization `[−cons] → [+syll] / C __ #` of (5). -/
def vocalization : Rule where
  target := Segment.ofSpecs [(.consonantal, false)]
  effect := .changeFeatures (Segment.ofSpecs [(.syllabic, true)])
  leftContext := [.seg C]
  rightContext := [.wordBoundary]

/-- Raising `a → i / __ CV` of (5). -/
def raising : Rule := { target := a, effect := .replace i, rightContext := [.seg C, .seg V] }

-- (5), Figure 4: vocalization feeds raising at *badw*, *badu*, *bidu*, *bidw*
theorem feeding_bedouin : Feeding vocalization.apply raising.apply [b, a, d, w] [b, a, d, u]
    [b, i, d, u] [b, i, d, w] := by
  have hd : vocalization.apply [b, i, d, w] = [b, i, d, u] := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, hd, by decide +kernel, feeds_iff.mpr ⟨?_, ?_⟩⟩
  · exact notMem_outputSet (by decide) rfl (by decide +kernel)
  · rw [hd]
    exact ⟨[b, a, d, u], by decide +kernel, by decide +kernel⟩

-- (5): in the attested order raising underapplies to *badu*
theorem underapplication_bedouin :
    vocalization.apply (raising.apply [b, a, d, w]) = [b, a, d, u] ∧
      [b, a, d, u] ∈ inputSet raising.apply := by
  obtain ⟨h₁, h₂⟩ := underapplication (P := vocalization.apply) (Q := raising.apply)
    (x := [b, a, d, w]) (by decide +kernel)
  have h := h₁.trans (show vocalization.apply [b, a, d, w] = [b, a, d, u] by decide +kernel)
  exact ⟨h, h ▸ h₂⟩

/-! ### Bleeding and counterbleeding: Polish (6) -/

/-- Raising `o → u / __ [+voi, −nas] #` of (6). -/
def raisingPolish : Rule where
  target := o
  effect := .replace u
  rightContext := [.seg (Segment.ofSpecs [(.voice, true), (.nasal, false)]), .wordBoundary]

-- (6), Figure 5: devoicing bleeds raising at *ʒwob*, *ʒwop*, *ʒwub*, *ʒwup*
theorem bleeding_polish : Bleeding devoicing.apply raisingPolish.apply [ezh, w, o, b]
    [ezh, w, o, p] [ezh, w, u, b] [ezh, w, u, p] := by
  have hc : devoicing.apply [ezh, w, u, b] = [ezh, w, u, p] := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, hc, by decide +kernel, bleeds_iff.mpr ⟨?_, ?_⟩⟩
  · exact ⟨[ezh, w, o, b], by decide +kernel, by decide +kernel⟩
  · rw [hc]
    exact notMem_outputSet (by decide) rfl (by decide +kernel)

-- (6): in the attested order raising overapplies
theorem misapplies_polish : Misapplies raisingPolish.apply devoicing.apply :=
  bleeding_polish.misapplies

end ChartExamples

/-! ### Seeding: Turkish (14) -/

section Turkish

open Turkish.Phonology (b e i k n)

/-- Epenthesis `∅ → i / C __ C#` of (14) inserts `i` into a word-final cluster. -/
def epenthesis (x : List Segment) : List Segment :=
  match x.reverse with
  | c₂ :: c₁ :: rest => if C ≤ c₁ ∧ C ≤ c₂ then (c₂ :: i :: c₁ :: rest).reverse else x
  | _ => x

/-- Deletion `k → ∅ / V __ V` of (14). -/
def deletion : Rule where
  target := k
  effect := .delete
  leftContext := [.seg V]
  rightContext := [.seg V]

theorem epenthesis_eq_self_or (x : List Segment) : epenthesis x = x ∨
    ∃ c₂ c₁ rest, C ≤ c₁ ∧ x.reverse = c₂ :: c₁ :: rest ∧
      epenthesis x = (c₂ :: i :: c₁ :: rest).reverse := by
  unfold epenthesis
  split
  · split_ifs with h
    · exact .inr ⟨_, _, _, h.1, by assumption, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem notMem_outputSet_epenthesis {y : List Segment}
    (hc : ∀ c₂ c₁ rest, y.reverse = c₂ :: i :: c₁ :: rest → ¬ C ≤ c₁) :
    y ∉ outputSet epenthesis := by
  rintro ⟨x, hx, rfl⟩
  obtain h | ⟨c₂, c₁, rest, h₁, -, h⟩ := epenthesis_eq_self_or x
  · exact hx h
  · exact hc c₂ c₁ rest (by rw [h, List.reverse_reverse]) h₁

/-- Epenthesis seeds deletion at *bebekn*, *bebekin*, *bebein*, so both orders are opaque:
epenthesis overapplies in the attested order and deletion underapplies in the other. -/
theorem seeding_turkish :
    Seeding epenthesis deletion.apply [b, e, b, e, k, n] [b, e, b, e, k, i, n]
        [b, e, b, e, i, n] ∧
      Underapplies deletion.apply epenthesis ∧ Misapplies epenthesis deletion.apply := by
  have hb : deletion.apply [b, e, b, e, k, i, n] = [b, e, b, e, i, n] := by decide +kernel
  have h : Seeding epenthesis deletion.apply [b, e, b, e, k, n] [b, e, b, e, k, i, n]
      [b, e, b, e, i, n] := by
    refine ⟨by decide +kernel, hb, by decide +kernel, bleeds_iff.mpr ⟨?_, ?_⟩⟩
    · exact ⟨[b, e, b, e, k, n], by decide +kernel, by decide +kernel⟩
    · rw [hb]
      refine notMem_outputSet_epenthesis fun c₂ c₁ rest h ↦ ?_
      obtain ⟨-, -, rfl, -⟩ : n = c₂ ∧ i = i ∧ e = c₁ ∧ [b, e, b] = rest := by simpa using h
      decide +kernel
  exact ⟨h, h.opaque⟩

end Turkish

/-! ### Flipping: Finnish (47) -/

section Finnish

open Finnish (e i s t v)

/-- Raising `e → i / __ #` of (47). -/
def raisingFinnish : Rule := { target := e, effect := .replace i, rightContext := [.wordBoundary] }

/-- Lowering `i → e / __ #` of (47), the flipped raising. -/
def lowering : Rule := { target := i, effect := .replace e, rightContext := [.wordBoundary] }

/-- Assibilation `t → s / __ i` of (47). -/
def assibilation : Rule := { target := t, effect := .replace s, rightContext := [.seg i] }

-- (47): raising feeds assibilation at *vete*, *veti*, *vesi*, *vese*, so lowering bleeds it
theorem flip_finnish :
    Feeding raisingFinnish.apply assibilation.apply [v, e, t, e] [v, e, t, i] [v, e, s, i]
        [v, e, s, e] ∧
      Bleeding lowering.apply assibilation.apply [v, e, t, i] [v, e, t, e] [v, e, s, i]
        [v, e, s, e] := by
  have hd : raisingFinnish.apply [v, e, s, e] = [v, e, s, i] := by decide +kernel
  have h : Feeding raisingFinnish.apply assibilation.apply [v, e, t, e] [v, e, t, i]
      [v, e, s, i] [v, e, s, e] := by
    refine ⟨by decide +kernel, by decide +kernel, hd, by decide +kernel, feeds_iff.mpr ⟨?_, ?_⟩⟩
    · exact notMem_outputSet (by decide) rfl (by decide +kernel)
    · rw [hd]
      exact ⟨[v, e, t, i], by decide +kernel, by decide +kernel⟩
  exact ⟨h, h.flip (by decide +kernel) (by decide +kernel)⟩

end Finnish

end BakovicBlumenfeld2024
