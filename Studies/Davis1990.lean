module

public import Linglib.Fragments.Romance.Italian.Phonology

/-!
# Davis (1990): Italian onset structure and the distribution of *il* and *lo*

Davis accounts for the two forms of the Italian masculine singular definite article by
syllabification: *il* occurs before a word that begins with a consonant syllabified into the onset
of its first syllable, and *lo* before any other word. Steriade's onset rule joins the first of
two word-initial consonants to the onset only when the second is at least four steps more
sonorous on Davis's hierarchy for Italian, so that *s* before a consonant and clusters such as
*ps*, *ft* and *mn* begin with a consonant outside the onset; and /ʃ ɲ ts dz/ are underlyingly
long, so that their first half has no onset to join. The one condition covers the vowel-initial
words, the *s* clusters and the long consonants, and it sets the rare clusters apart where
Radzinski's rule, *lo* before a cluster containing /s/, does not: *lo ftalacene* but *il Tlingit*.

## Main results

* `Davis1990.beginsWithOnset_ilClusters`, `Davis1990.not_beginsWithOnset_loOnsets`: the clusters
  of (1) begin with an onset consonant and the onsets of (3) do not.
* `Davis1990.not_beginsWithOnset_unusualClusters`: neither do the clusters without /s/ of (13a).
* `Davis1990.ofSegment_le_of_sonority_le`: the hierarchy refines the modal one (note 6).
* `Davis1990.onsetOf_eq_consonant_of_beginsWithOnset`: a word that begins with an onset consonant
  is in the class of `Italian.Phonology.Onset` before which the fragment has *il*.

## Implementation notes

The analysis puts *il* exactly before the words that begin with an onset consonant, so its
predictions are stated with `BeginsWithOnset`. The data are the clusters of (1), (3) and (13),
each followed by the vowel /a/; the words of (2) and (4) are not encoded. The *s* clusters are
written with /s/, as Davis writes them. Davis leaves the affricates and the glides off the
hierarchy (note 6), and `sonority` gives them no rank, so that they never join a following
consonant; a consonant before a glide begins a diphthong-initial syllable and is in its onset.
Davis does not discuss /ʎ/, and the elision of *lo* before a vowel is set aside. The rising cluster
of *gnu* (13a) begins with no onset consonant, though the fragment's classes put it with the
consonants.

## TODO

* The syntactic doubling of (9), which the clusters of (1) undergo and those of (3) block.

## References

* [davis-1990]
-/

@[expose] public section

namespace Davis1990

open Phonology Italian.Phonology

/-! ### The analysis -/

/-- The sonority of a segment on the hierarchy (6): the voiceless stops at 1, the voiced stops at
2, the noncoronal and the coronal fricatives at 3 and 4, the nasals *n* at 5 and *m* at 6, the
liquids at 7 and the vowels at 8, and no rank for the affricates and the glides. -/
def sonority (x : Segment) : Option ℕ :=
  match Sonority.ofSegment x with
  | .vowel => some 8
  | .liquid => some 7
  | .nasal => some (if x.HasValue .labial true then 6 else 5)
  | .glide => none
  | .obstruent =>
    if ¬ x.HasValue .delayedRelease true then some (if x.HasValue .voice true then 2 else 1)
    else if x.HasValue .continuant true then some (if x.HasValue .coronal true then 4 else 3)
    else none

/-- The onset rule (5b) under the condition on minimal sonority distance: the first of two
consonants joins the onset when the second is at least four steps more sonorous. -/
def JoinsOnset (x y : Segment) : Prop := ∃ a ∈ sonority x, ∃ b ∈ sonority y, a + 4 ≤ b

instance : DecidableRel JoinsOnset := fun x y ↦
  inferInstanceAs (Decidable (∃ a ∈ sonority x, ∃ b ∈ sonority y, a + 4 ≤ b))

/-- The consonants that are underlyingly long, (11). -/
def underlyinglyLong : Finset Segment := {«ʃ», «ɲ», ts, dz}

/-- A word begins with an onset consonant when the rules (5) syllabify its first segment into the
onset of its first syllable: a consonant that is not underlyingly long, before a vowel or a glide
by the CV rule (5a), or before a consonant that the onset rule joins it to. -/
def BeginsWithOnset : List Segment → Prop
  | x :: y :: _ => x.IsConsonant ∧ x ∉ underlyinglyLong ∧ (¬ y.IsConsonant ∨ JoinsOnset x y)
  | _ => False

instance : DecidablePred BeginsWithOnset := fun w ↦ by
  unfold BeginsWithOnset; split <;> infer_instance

theorem beginsWithOnset_cons_cons (x y : Segment) (rest : List Segment) :
    BeginsWithOnset (x :: y :: rest) ↔ BeginsWithOnset [x, y] :=
  Iff.rfl

/-! ### The data -/

/-- The clusters *il* precedes, (1). -/
def ilClusters : List (List Segment) :=
  [[b, l], [b, r], [p, l], [p, r], [f, l], [f, r], [d, r], [t, r], [k, l], [k, r], [g, l], [g, r],
    [p, n]]

/-- The clusters and consonants *lo* precedes, (3). -/
def loOnsets : List (List Segment) :=
  [[s, p], [s, b], [s, t], [s, d], [s, f], [s, v], [s, k], [s, g], [s, l], [s, m], [s, n], [p, s],
    [k, s], [«ʃ»], [«ɲ»], [ts], [dz]]

/-- The clusters that begin *ftalacene*, *pterodattilo*, *mnemometro* and *gnu*, (13a). -/
def unusualClusters : List (List Segment) := [[f, t], [p, t], [m, n], [g, n]]

theorem beginsWithOnset_ilClusters : ∀ c ∈ ilClusters, BeginsWithOnset (c ++ [a]) := by decide

theorem not_beginsWithOnset_loOnsets : ∀ c ∈ loOnsets, ¬ BeginsWithOnset (c ++ [a]) := by decide

/-- None of the clusters of (13) contains /s/, so Radzinski's rule puts *il* before all five. The
four of (13a) begin with no onset consonant, so the analysis puts *lo* before them, as Davis's
consultant does, and *il* before *Tlingit* (pp. 51–52). -/
theorem not_beginsWithOnset_unusualClusters :
    ∀ c ∈ unusualClusters, s ∉ c ∧ ¬ BeginsWithOnset (c ++ [a]) := by
  decide

theorem beginsWithOnset_tl : BeginsWithOnset [t, l, i] := by decide

/-- The hierarchy follows the modal one of obstruents, nasals, liquids and vowels in its general
form and divides its classes further (note 6). -/
theorem ofSegment_le_of_sonority_le : ∀ x ∈ inventory, ∀ y ∈ inventory, ∀ m ∈ sonority x,
    ∀ n ∈ sonority y, m ≤ n → Sonority.ofSegment x ≤ Sonority.ofSegment y := by
  decide

/-! ### The fragment's classes -/

/-- A word that begins with an onset consonant other than /ʎ/, which Davis leaves aside, is in the
class before which the fragment's masculine article is *il*. -/
theorem onsetOf_eq_consonant_of_beginsWithOnset {x y : Segment} (hx : x ∈ inventory)
    (hy : y ∈ inventory) (hne : x ≠ «ʎ») (rest : List Segment)
    (h : BeginsWithOnset (x :: y :: rest)) : Onset.of (x :: y :: rest) = .consonant := by
  have key : ∀ x ∈ inventory, ∀ y ∈ inventory, x ≠ «ʎ» → BeginsWithOnset [x, y] →
      Onset.of [x, y] = .consonant := by
    decide
  exact (Onset.of_cons_cons x y rest).trans (key x hx y hy hne h)

example : ¬ BeginsWithOnset [g, n, u] ∧ Onset.of [g, n, u] = .consonant ∧
    BeginsWithOnset [«ʎ», i] ∧ Onset.of [«ʎ», i] = .inherentlyLong := by
  decide

end Davis1990
