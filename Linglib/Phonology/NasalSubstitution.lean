module

public import Linglib.Phonology.Segmental.FeatureClass
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Nasal place assimilation and nasal substitution

Many Austronesian languages have prefixes that end in a nasal. Before a stem-initial consonant the
nasal takes the consonant's place, and under nasal substitution the consonant is in addition not
realized, as in Tagalog *mamigáj* from *maŋ-* and *bigáj*. Following Donohue, both outcomes have
the same nasal: [the assimilated cluster is the substituted nasal followed by the
consonant](##assimilate_pair). [That nasal has the consonant's
place](##substitute_apply_of_mem_place), and before a consonant with no oral articulator, such as
the glottal stop, [it is the prefix nasal unchanged](##substitute_eq_of_placeless). A language
fixes which consonants trigger assimilation and which substitute.

## Implementation notes

Assimilation copies the whole place class, as Hayes's rule does, and the class contains [strident]
and [lateral]. A nasal assimilated to a sibilant or a lateral therefore copies `+` for them, which
`nonstrident` and `nonlateral` reset, and a nasal assimilated to a consonant with no oral
articulator loses its place, which `defaultPlace` restores.

Pater analyses substitution as fusion, one nasal that corresponds to both input segments, rather
than as the loss of the consonant. The two give the same string, and only strings are computed here.

## TODO

Donohue's table of nasal prefixes before plosives in seventeen languages, as `Data/` rows. Its
geminate nasals (Makasar, Ilokano), which keep the consonant's slot, lie outside both outcomes.

## References

* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [M. Donohue, *Phonotactics and morphophonology* (2024)][donohue-2024]
* [J. Pater, *Austronesian nasal substitution revisited: what's wrong with \*NC (and what's
  not)* (2001)][pater-2001]
* [K. Zuraw, *A model of lexical variation and the grammar with application to Tagalog nasal
  substitution* (2010)][zuraw-2010]
-/

@[expose] public section

namespace Phonology.NasalSubstitution

open Subregular.LocalRewrite

/-- A nasal takes every place feature value of a following segment of the class `trigger`. This
is Hayes's /n/ Assimilation with its target widened from /n/ to every nasal and its [−syllabic]
trigger made a parameter ([hayes-2009] p. 89). -/
def placeAssimilation (trigger : Segment) : Rule where
  target := Segment.ofSpecs [(.nasal, true)]
  effect := .copyRight FeatureClass.place
  rightContext := [.seg trigger]

/-- A nasal is not strident. -/
def nonstrident : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.strident, true)]
  effect := .changeFeatures (Segment.ofSpecs [(.strident, false)])

/-- A nasal is not lateral. -/
def nonlateral : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.lateral, true)]
  effect := .changeFeatures (Segment.ofSpecs [(.lateral, false)])

/-- A nasal with no oral articulator is the nasal `N`. -/
def defaultPlace (N : Segment) : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.labial, false), (.coronal, false), (.dorsal, false)]
  effect := .replace N

/-- The rules of nasal place assimilation, for the triggers `trigger` and the default nasal
`N`. -/
def rules (trigger N : Segment) : List Rule :=
  [placeAssimilation trigger, nonstrident, nonlateral, defaultPlace N]

/-- `assimilate trigger N w` is the word `w` with each nasal assimilated to a following segment
of the class `trigger`. -/
def assimilate (trigger N : Segment) : List Segment → List Segment := derive (rules trigger N)

/-- Assimilation neither deletes nor inserts a segment. -/
theorem length_assimilate (trigger N : Segment) (w : List Segment) :
    (assimilate trigger N w).length = w.length :=
  length_derive (by simp [rules, placeAssimilation, nonstrident, nonlateral, defaultPlace]) w

/-- `substitute trigger N x` is the nasal that `N` and a following `x` surface as under nasal
substitution, which is the nasal that `N` assimilates to before `x`. -/
def substitute (trigger N x : Segment) : Segment :=
  (assimilate trigger N [N, x]).head (List.ne_nil_of_length_pos (by simp [length_assimilate]))

/-! ### What the rules compute -/

variable {trigger N x : Segment}

private theorem verdict_placeAssimilation (s : Segment) (w : List Segment) :
    (placeAssimilation trigger).verdict [] s (x :: w) =
      [if (placeAssimilation trigger).target ≤ s ∧ trigger ≤ x then
        FeatureClass.place.piecewise x s else s] := by
  simp only [Rule.verdict, MatchesLeft, MatchesRight, placeAssimilation, List.reverse_nil,
    and_true, true_and]
  split_ifs <;> simp_all [Effect.apply]

private theorem verdict_changeFeatures {r : Rule} {f : Feature} {v : Bool}
    (he : r.effect = .changeFeatures (Segment.ofSpecs [(f, v)])) (hl : r.leftContext = [])
    (hr : r.rightContext = []) (s : Segment) (d : List Segment) :
    r.verdict [] s d = [if r.target ≤ s then s.setFeature f v else s] := by
  simp only [Rule.verdict, MatchesLeft, MatchesRight, hl, hr, List.reverse_nil, and_true]
  split_ifs
  · simp only [he, Effect.apply, Option.toList_some, List.cons.injEq, and_true]
    funext g
    by_cases h : g = f
    · subst h
      rw [show s.setFeature g v g = some v from Segment.setFeature_hasValue s g v,
        Segment.ofSpecs_apply, List.lookup_cons, beq_self_eq_true]
      rfl
    · rw [Segment.setFeature_apply_of_ne s (Ne.symm h), Segment.ofSpecs_apply,
        List.lookup_cons, beq_false_of_ne h, List.lookup_nil]
      rfl
  · rfl

private theorem verdict_defaultPlace (s : Segment) (d : List Segment) :
    (defaultPlace N).verdict [] s d = [if (defaultPlace N).target ≤ s then N else s] := by
  simp only [Rule.verdict, MatchesLeft, MatchesRight, defaultPlace, List.reverse_nil, and_true]
  split_ifs <;> simp_all [Effect.apply]

private theorem assimilate_cons_cons (w : List Segment) :
    assimilate trigger N (N :: x :: w) =
      (let s₁ : Segment := if (placeAssimilation trigger).target ≤ N ∧ trigger ≤ x then
          FeatureClass.place.piecewise x N else N
        let s₂ : Segment := if nonstrident.target ≤ s₁ then s₁.setFeature .strident false else s₁
        let s₃ : Segment := if nonlateral.target ≤ s₂ then s₂.setFeature .lateral false else s₂
        if (defaultPlace N).target ≤ s₃ then N else s₃) :: assimilate trigger N (x :: w) := by
  simp only [assimilate, derive, rules, List.foldl_cons, List.foldl_nil]
  rw [Rule.apply_cons_of_leftReach_eq_zero rfl, verdict_placeAssimilation, List.singleton_append,
    Rule.apply_cons_of_leftReach_eq_zero rfl, verdict_changeFeatures rfl rfl rfl,
    List.singleton_append, Rule.apply_cons_of_leftReach_eq_zero rfl,
    verdict_changeFeatures rfl rfl rfl, List.singleton_append,
    Rule.apply_cons_of_leftReach_eq_zero rfl, verdict_defaultPlace, List.singleton_append]

private theorem substitute_eq : substitute trigger N x =
    let s₁ : Segment := if (placeAssimilation trigger).target ≤ N ∧ trigger ≤ x then
        FeatureClass.place.piecewise x N else N
      let s₂ : Segment := if nonstrident.target ≤ s₁ then s₁.setFeature .strident false else s₁
      let s₃ : Segment := if nonlateral.target ≤ s₂ then s₂.setFeature .lateral false else s₂
      if (defaultPlace N).target ≤ s₃ then N else s₃ := by
  simp only [substitute, assimilate_cons_cons, List.head_cons]

/-- Assimilation leaves a segment that is not a nasal as it is. -/
theorem assimilate_singleton (hx : ¬ x.HasValue .nasal true) : assimilate trigger N [x] = [x] := by
  have h (l : List (Feature × Bool)) : ¬ Segment.ofSpecs ((.nasal, true) :: l) ≤ x :=
    fun hle ↦ hx ((Segment.le_iff_forall_hasValue x).1 hle _ _ rfl)
  have h₁ {r : Rule} (hl : r.leftReach = 0) (ht : ¬ r.target ≤ x) : r.apply [x] = [x] := by
    rw [Rule.apply_cons_of_leftReach_eq_zero hl]
    simp [Rule.verdict, ht, Rule.apply, Rule.apply.go]
  simp only [assimilate, derive, rules, List.foldl_cons, List.foldl_nil]
  rw [h₁ rfl (h _), h₁ rfl (h _), h₁ rfl (h _), h₁ rfl (h _)]

/-- Substitution is assimilation together with the loss of the consonant: the nasal `N` and a
following `x` that is not a nasal assimilate to the substituted nasal followed by `x`
([donohue-2024] p. 719). -/
theorem assimilate_pair (hx : ¬ x.HasValue .nasal true) :
    assimilate trigger N [N, x] = [substitute trigger N x, x] := by
  simp only [substitute, assimilate_cons_cons, List.head_cons, assimilate_singleton hx]

/-- The substituted segment of a nasal is a nasal. -/
theorem substitute_hasValue_nasal (hN : N.HasValue .nasal true) :
    (substitute trigger N x).HasValue .nasal true := by
  rw [substitute_eq, Segment.HasValue]
  simp only [ite_apply, ne_eq, reduceCtorEq, not_false_eq_true, Segment.setFeature_apply_of_ne,
    Finset.piecewise_eq_of_notMem _ _ _ (by decide : Feature.nasal ∉ FeatureClass.place),
    ite_self]
  exact hN

/-- The substituted nasal is homorganic with a consonant that has an oral articulator: it agrees
with the consonant on every place feature but [strident] and [lateral]. -/
theorem substitute_apply_of_mem_place (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (ha : x.articulators.Nonempty) {f : Feature} (hf : f ∈ FeatureClass.place)
    (hs : f ≠ .strident) (hl : f ≠ .lateral) : substitute trigger N x f = x f := by
  obtain ⟨a, ha⟩ := ha
  simp only [Segment.articulators, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at ha
  obtain ⟨hmem, hxa⟩ := ha
  have hpa : a ∈ FeatureClass.place ∧ a ≠ .strident ∧ a ≠ .lateral := by
    rcases hmem with rfl | rfl | rfl <;> decide
  have hN' : (placeAssimilation trigger).target ≤ N := (Segment.hasValue_iff_ofSpecs_le N _ _).1 hN
  rw [substitute_eq]
  dsimp only
  simp only [hN', hx, and_self, ite_true]
  rw [ite_eq_right]
  · simp only [ite_apply, ne_eq, hs.symm, hl.symm, not_false_eq_true,
      Segment.setFeature_apply_of_ne, ite_self, Finset.piecewise_eq_of_mem _ _ _ hf]
  · intro h
    have h := (Segment.le_iff_forall_hasValue _).1 h a false
      (by rcases hmem with rfl | rfl | rfl <;> rfl)
    simp only [Segment.HasValue, ite_apply, ne_eq, hpa.2.1.symm, hpa.2.2.symm,
      not_false_eq_true, Segment.setFeature_apply_of_ne, ite_self,
      Finset.piecewise_eq_of_mem _ _ _ hpa.1] at h
    cases h.symm.trans hxa

/-- A consonant with no oral articulator, such as the glottal stop, leaves the place of the nasal
unchanged: the two substitute to the nasal `N` itself. -/
theorem substitute_eq_of_placeless (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (hp : Segment.ofSpecs [(.labial, false), (.coronal, false), (.dorsal, false)] ≤ x) :
    substitute trigger N x = N := by
  obtain ⟨hl, hc, hd⟩ : x.HasValue .labial false ∧ x.HasValue .coronal false ∧
      x.HasValue .dorsal false := by
    simpa using (Segment.ofSpecs_le_iff_forall_mem
      (specs := [(.labial, false), (.coronal, false), (.dorsal, false)]) x (by decide)).1 hp
  have hN' : (placeAssimilation trigger).target ≤ N := (Segment.hasValue_iff_ofSpecs_le N _ _).1 hN
  rw [substitute_eq]
  dsimp only
  simp only [hN', hx, and_self, ite_true]
  rw [ite_eq_left]
  refine (Segment.ofSpecs_le_iff_forall_mem (specs := [(.nasal, true), (.labial, false),
    (.coronal, false), (.dorsal, false)]) _ (by decide)).2 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Segment.HasValue, ite_apply, ne_eq, reduceCtorEq, not_false_eq_true,
    Segment.setFeature_apply_of_ne, ite_self,
    Finset.piecewise_eq_of_notMem _ _ _ (by decide : Feature.nasal ∉ FeatureClass.place),
    Finset.piecewise_eq_of_mem _ _ _ (by decide : Feature.labial ∈ FeatureClass.place),
    Finset.piecewise_eq_of_mem _ _ _ (by decide : Feature.coronal ∈ FeatureClass.place),
    Finset.piecewise_eq_of_mem _ _ _ (by decide : Feature.dorsal ∈ FeatureClass.place)]
  exact ⟨hN, hl, hc, hd⟩

end Phonology.NasalSubstitution
