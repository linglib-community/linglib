module

public import Linglib.Phonology.Segmental.FeatureClass
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Nasal place assimilation and nasal substitution

Many Austronesian languages have prefixes that end in a nasal. Before a stem-initial consonant the
nasal takes the consonant's place, and under nasal substitution the consonant is in addition not
realized, as in Tagalog *mamigáj* from *maŋ-* and *bigáj*. Following Donohue, both outcomes have
the same nasal: [the assimilated cluster is the substituted nasal followed by the
consonant](##assimilate_pair). That nasal is [the nasal of the language homorganic with the
consonant](##substitute_mem_homorganicNasals), and where the language has none, as before the
glottal stop, [the prefix nasal is unchanged](##substitute_of_card_ne_one). A language fixes
which consonants trigger assimilation and which substitute.

## Implementation notes

Assimilation spreads the major articulator features, Hayes's rule with a smaller class, and the
result is realized as a nasal of the language's inventory. Spreading Hayes's whole place class
copies features such as [strident], [lateral] and [labiodental] that no nasal of the inventory
bears, so the result is identified with a phoneme by its major articulators.

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

/-- A nasal takes the major articulator values of a following segment of the class `trigger`.
This is Hayes's /n/ Assimilation with its target widened from /n/ to every nasal, its
[−syllabic] trigger made a parameter, and its class the major articulators rather than every
place feature ([hayes-2009] p. 89). -/
def placeAssimilation (trigger : Segment) : Rule where
  target := Segment.ofSpecs [(.nasal, true)]
  effect := .copyRight Feature.majorArticulators
  rightContext := [.seg trigger]

/-- The nasals of the inventory `I` homorganic with `s`. -/
def homorganicNasals (I : Finset Segment) (s : Segment) : Finset Segment :=
  I.filter fun y ↦ y.IsNasal ∧ y.Homorganic s

/-- `realize I N s` is the nasal `s` as a phoneme of the inventory `I`: the nasal of `I`
homorganic with it if there is exactly one, and the nasal `N` otherwise. Other segments are
unchanged. -/
def realize (I : Finset Segment) (N s : Segment) : Segment :=
  if s.HasValue .nasal true then
    if h : (homorganicNasals I s).card = 1 then
      (homorganicNasals I s).choose (fun _ ↦ True) <| by
        obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h
        exact ⟨y, by simp [hy], fun z hz ↦ by simpa [hy] using hz.1⟩
    else N
  else s

/-- `assimilate I trigger N w` is the word `w` with each nasal assimilated to a following segment
of the class `trigger` and realized as a nasal of the inventory `I`, the nasal `N` standing in
where `I` has no single one. -/
def assimilate (I : Finset Segment) (trigger N : Segment) (w : List Segment) : List Segment :=
  ((placeAssimilation trigger).apply w).map (realize I N)

/-- Assimilation neither deletes nor inserts a segment. -/
theorem length_assimilate (I : Finset Segment) (trigger N : Segment) (w : List Segment) :
    (assimilate I trigger N w).length = w.length := by
  simp [assimilate, Rule.length_apply (r := placeAssimilation trigger) nofun]

/-- `substitute I trigger N x` is the nasal that `N` and a following `x` surface as under nasal
substitution, which is the nasal that `N` assimilates to before `x`. -/
def substitute (I : Finset Segment) (trigger N x : Segment) : Segment :=
  (assimilate I trigger N [N, x]).head (List.ne_nil_of_length_pos (by simp [length_assimilate]))

variable {I : Finset Segment} {trigger N s x : Segment}

/-! ### Realization -/

@[simp] theorem mem_homorganicNasals {y : Segment} :
    y ∈ homorganicNasals I s ↔ y ∈ I ∧ y.IsNasal ∧ y.Homorganic s :=
  Finset.mem_filter

theorem realize_of_not_hasValue_nasal (h : ¬ s.HasValue .nasal true) : realize I N s = s := by
  simp [realize, h]

theorem realize_mem_homorganicNasals (h : s.HasValue .nasal true)
    (h₁ : (homorganicNasals I s).card = 1) : realize I N s ∈ homorganicNasals I s := by
  simp only [realize, h, ↓reduceIte, h₁, ↓reduceDIte]
  exact Finset.choose_mem _ _ _

theorem realize_of_card_ne_one (h : s.HasValue .nasal true)
    (h₁ : (homorganicNasals I s).card ≠ 1) : realize I N s = N := by
  simp [realize, h, h₁]

/-- Spreading the major articulators of `x` makes a segment homorganic with exactly the segments
`x` is homorganic with. -/
theorem homorganicNasals_piecewise :
    homorganicNasals I (Feature.majorArticulators.piecewise x N) = homorganicNasals I x := by
  ext y
  simp only [mem_homorganicNasals, Segment.Homorganic]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  refine ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [h hf, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.1 hf)]
  · rw [h hf, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.1 hf)]

/-! ### Substitution -/

/-- Before a second segment `x`, a nasal takes the major articulators of `x` when `x` is a
trigger, and `x` itself is unchanged. -/
theorem placeAssimilation_apply_pair (y : Segment) :
    (placeAssimilation trigger).apply [y, x] =
      [if y.HasValue .nasal true ∧ trigger ≤ x then Feature.majorArticulators.piecewise x y
        else y, x] := by
  rw [Rule.apply_cons_of_leftReach_eq_zero rfl, Rule.apply_cons_of_leftReach_eq_zero rfl]
  by_cases h : y.HasValue .nasal true ∧ trigger ≤ x <;>
    simp [h, Rule.verdict, placeAssimilation, MatchesLeft, MatchesRight, Effect.apply,
      ← Segment.hasValue_iff_ofSpecs_le]

theorem substitute_eq : substitute I trigger N x =
    realize I N (if N.HasValue .nasal true ∧ trigger ≤ x then
      Feature.majorArticulators.piecewise x N else N) := by
  simp only [substitute, assimilate, placeAssimilation_apply_pair, List.map_cons, List.head_cons]

/-- Substitution is assimilation together with the loss of the consonant: the nasal `N` and a
following `x` that is not a nasal assimilate to the substituted nasal followed by `x`
([donohue-2024] p. 719). -/
theorem assimilate_pair (hx : ¬ x.HasValue .nasal true) :
    assimilate I trigger N [N, x] = [substitute I trigger N x, x] := by
  simp only [substitute, assimilate, placeAssimilation_apply_pair, List.map_cons, List.map_nil,
    List.head_cons, realize_of_not_hasValue_nasal hx]

private theorem hasValue_nasal_piecewise (hN : N.HasValue .nasal true) :
    Segment.HasValue (Feature.majorArticulators.piecewise x N) .nasal true := by
  rwa [Segment.HasValue, Finset.piecewise_eq_of_notMem _ _ _ (by decide)]

/-- The substituted nasal is the nasal of the inventory homorganic with the consonant, when the
inventory has exactly one. -/
theorem substitute_mem_homorganicNasals (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (h : (homorganicNasals I x).card = 1) :
    substitute I trigger N x ∈ homorganicNasals I x := by
  have hp := homorganicNasals_piecewise (I := I) (x := x) (N := N)
  rw [substitute_eq, ite_eq_left ⟨hN, hx⟩, ← hp]
  exact realize_mem_homorganicNasals (hasValue_nasal_piecewise hN) (by rwa [hp])

/-- Where the inventory has no single nasal homorganic with the consonant, as before a glottal
stop, the nasal `N` is unchanged. -/
theorem substitute_of_card_ne_one (hN : N.HasValue .nasal true) (hx : trigger ≤ x)
    (h : (homorganicNasals I x).card ≠ 1) : substitute I trigger N x = N := by
  rw [substitute_eq, ite_eq_left ⟨hN, hx⟩]
  exact realize_of_card_ne_one (hasValue_nasal_piecewise hN) (by rwa [homorganicNasals_piecewise])

end Phonology.NasalSubstitution
