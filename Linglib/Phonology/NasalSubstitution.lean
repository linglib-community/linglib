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
and [lateral]. A nasal assimilated to a sibilant or a lateral therefore copies `+` for them, and a
nasal assimilated to a consonant with no oral articulator loses its place. `repair` resets the
first two and restores the place, segment by segment, since it reads no context.

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

/-- `repair N s` keeps a nasal a possible nasal: a nasal with no oral articulator is the nasal
`N`, and otherwise a nasal is neither strident nor lateral. Other segments are unchanged. -/
def repair (N s : Segment) : Segment :=
  if s.HasValue .nasal true then
    if s.HasValue .labial false ∧ s.HasValue .coronal false ∧ s.HasValue .dorsal false then N
    else
      let s' := if s.HasValue .strident true then s.setFeature .strident false else s
      if s.HasValue .lateral true then s'.setFeature .lateral false else s'
  else s

/-- `assimilate trigger N w` is the word `w` with each nasal assimilated to a following segment
of the class `trigger`, the nasal `N` standing in for one left with no place. -/
def assimilate (trigger N : Segment) (w : List Segment) : List Segment :=
  ((placeAssimilation trigger).apply w).map (repair N)

/-- Assimilation neither deletes nor inserts a segment. -/
theorem length_assimilate (trigger N : Segment) (w : List Segment) :
    (assimilate trigger N w).length = w.length := by
  simp [assimilate, Rule.length_apply (r := placeAssimilation trigger) nofun]

/-- `substitute trigger N x` is the nasal that `N` and a following `x` surface as under nasal
substitution, which is the nasal that `N` assimilates to before `x`. -/
def substitute (trigger N x : Segment) : Segment :=
  (assimilate trigger N [N, x]).head (List.ne_nil_of_length_pos (by simp [length_assimilate]))

variable {trigger N s x : Segment}

/-! ### Repair -/

theorem repair_of_not_hasValue_nasal (h : ¬ s.HasValue .nasal true) : repair N s = s := by
  simp [repair, h]

theorem repair_of_placeless (h : s.HasValue .nasal true) (hl : s.HasValue .labial false)
    (hc : s.HasValue .coronal false) (hd : s.HasValue .dorsal false) : repair N s = N := by
  simp [repair, h, hl, hc, hd]

theorem repair_apply_of_ne (h : ¬ (s.HasValue .labial false ∧ s.HasValue .coronal false ∧
      s.HasValue .dorsal false)) {f : Feature} (hs : f ≠ .strident) (hl : f ≠ .lateral) :
    repair N s f = s f := by
  unfold repair
  split_ifs <;> simp_all [Segment.setFeature_apply_of_ne, Ne.symm]

theorem repair_hasValue_nasal (hN : N.HasValue .nasal true) (h : s.HasValue .nasal true) :
    (repair N s).HasValue .nasal true := by
  unfold repair
  split_ifs <;> simp_all [Segment.HasValue, Segment.setFeature_apply_of_ne]

/-! ### Substitution -/

/-- Before a second segment `x`, a nasal takes the place of `x` when `x` is a trigger, and `x`
itself is unchanged. -/
theorem placeAssimilation_apply_pair (y : Segment) :
    (placeAssimilation trigger).apply [y, x] =
      [if y.HasValue .nasal true ∧ trigger ≤ x then FeatureClass.place.piecewise x y else y,
        x] := by
  rw [Rule.apply_cons_of_leftReach_eq_zero rfl, Rule.apply_cons_of_leftReach_eq_zero rfl]
  by_cases h : y.HasValue .nasal true ∧ trigger ≤ x <;>
    simp [h, Rule.verdict, placeAssimilation, MatchesLeft, MatchesRight, Effect.apply,
      ← Segment.hasValue_iff_ofSpecs_le]

theorem substitute_eq : substitute trigger N x =
    repair N (if N.HasValue .nasal true ∧ trigger ≤ x then FeatureClass.place.piecewise x N
      else N) := by
  simp only [substitute, assimilate, placeAssimilation_apply_pair, List.map_cons, List.head_cons]

/-- Substitution is assimilation together with the loss of the consonant: the nasal `N` and a
following `x` that is not a nasal assimilate to the substituted nasal followed by `x`
([donohue-2024] p. 719). -/
theorem assimilate_pair (hx : ¬ x.HasValue .nasal true) :
    assimilate trigger N [N, x] = [substitute trigger N x, x] := by
  simp only [substitute, assimilate, placeAssimilation_apply_pair, List.map_cons, List.map_nil,
    List.head_cons, repair_of_not_hasValue_nasal hx]

/-- The substituted segment of a nasal is a nasal. -/
theorem substitute_hasValue_nasal (hN : N.HasValue .nasal true) :
    (substitute trigger N x).HasValue .nasal true := by
  rw [substitute_eq]
  refine repair_hasValue_nasal hN ?_
  split_ifs
  · rwa [Segment.HasValue, Finset.piecewise_eq_of_notMem _ _ _ (by decide)]
  · exact hN

/-- The substituted nasal is homorganic with a consonant that has an oral articulator: it agrees
with the consonant on every place feature but [strident] and [lateral]. -/
theorem substitute_apply_of_mem_place (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (ha : x.articulators.Nonempty) {f : Feature} (hf : f ∈ FeatureClass.place)
    (hs : f ≠ .strident) (hl : f ≠ .lateral) : substitute trigger N x f = x f := by
  obtain ⟨a, ha⟩ := ha
  simp only [Segment.articulators, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at ha
  obtain ⟨hmem, ha⟩ := ha
  rw [substitute_eq, ite_eq_left ⟨hN, hx⟩, repair_apply_of_ne _ hs hl,
    Finset.piecewise_eq_of_mem _ _ _ hf]
  rintro ⟨hl, hc, hd⟩
  have hpa : a ∈ FeatureClass.place := by rcases hmem with rfl | rfl | rfl <;> decide
  have h : Segment.HasValue (FeatureClass.place.piecewise x N) a false := by
    rcases hmem with rfl | rfl | rfl <;> assumption
  rw [Segment.HasValue, Finset.piecewise_eq_of_mem _ _ _ hpa] at h
  cases h.symm.trans ha

/-- A consonant with no oral articulator, such as the glottal stop, leaves the place of the nasal
unchanged: the two substitute to the nasal `N` itself. -/
theorem substitute_eq_of_placeless (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (hl : x.HasValue .labial false) (hc : x.HasValue .coronal false)
    (hd : x.HasValue .dorsal false) : substitute trigger N x = N := by
  rw [substitute_eq, ite_eq_left ⟨hN, hx⟩]
  apply repair_of_placeless <;>
    simpa [Segment.HasValue, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem,
      FeatureClass.mem_place, Feature.featureClass?]

end Phonology.NasalSubstitution
