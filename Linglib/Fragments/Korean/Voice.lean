module

public import Linglib.Syntax.Voice.Basic

/-!
# Korean voice

Korean forms its passive and its short causative with a suffix on the stem. The passive suffix
has four variants, chosen largely by the final sound of the stem, and the causative suffix eleven,
which that sound does not wholly predict. Every passive variant is also a causative one, so
*ilk-hi-* is both 'be read' and 'cause to read'. Creissels takes such a shared suffix to mark only
the demotion of the initial A, which the passive compensates by making the P the subject and the
causative by introducing a causer. The long causative, *ha-ta* 'do' after a clause in *-key*, is
a complex sentence, so it is a construction of `Korean.ha` rather than a voice.

## Main definitions

* `Korean.passiveSuffixes`, `Korean.causativeSuffixes`: the variants of the two suffixes.
* `Korean.passive`, `Korean.causative`, `Korean.causativeOfTransitive`: the voices.

## Main results

* `Korean.passiveSuffixes_subset_causativeSuffixes`: every passive suffix is a causative suffix.
* `Korean.fateOfRole_passive_causativeOfTransitive`: the passive and the causative of a
  transitive verb both demote the initial A.

## References

* [sohn-1999]
* [creissels-2024]
-/

@[expose] public section

namespace Korean

open ArgumentFrame.Slot

/-! ### Suffixes -/

/-- The variants of the passive suffix, conditioned largely by the final sound of the stem
([sohn-1999] p. 368). -/
def passiveSuffixes : Finset String := {"i", "hi", "li", "ki"}

/-- The variants of the causative suffix, which the final sound of the stem does not wholly
predict ([sohn-1999] p. 374). -/
def causativeSuffixes : Finset String :=
  {"y", "i", "hi", "li", "ki", "khi", "wu", "ywu", "iwu", "chwu", "kwu"}

/-- Every passive suffix is a causative suffix ([sohn-1999] p. 374). -/
theorem passiveSuffixes_subset_causativeSuffixes : passiveSuffixes ⊆ causativeSuffixes := by
  decide

/-! ### Voices -/

/-- The passive in the suffix `sfx` makes the object the subject and demotes the agent, which a
locative or goal particle may mark ([sohn-1999] p. 368). -/
def passive (sfx : passiveSuffixes) : Voice := Voice.passive.marked [.suff sfx]

/-- The causative of an intransitive verb or an adjective in the suffix `sfx` makes a causer the
A and the initial S the P ([sohn-1999] p. 375). -/
def causative (sfx : causativeSuffixes) : Voice := Voice.causative.marked [.suff sfx]

/-- The causative of a transitive verb in the suffix `sfx` makes a causer the A and the initial A
a dative before the initial P; the dative may also be accusative, as in other ditransitive
clauses ([sohn-1999] p. 375). -/
def causativeOfTransitive (sfx : causativeSuffixes) : Voice :=
  (Voice.of .np ⟨some .nominal, [.adpositional (some .grammatical), .nominal]⟩
    [some (complement 0), some (complement 1), some external]).marked [.suff sfx]

section

variable (s : passiveSuffixes) (t : causativeSuffixes)

theorem coding_passive : (passive s).coding = .synthetic := by
  simp [passive, Voice.Coding.ofMarker]

theorem coding_causative : (causative t).coding = .synthetic := by
  simp [causative, Voice.Coding.ofMarker]

theorem coding_causativeOfTransitive : (causativeOfTransitive t).coding = .synthetic := by
  simp [causativeOfTransitive, Voice.Coding.ofMarker]

theorem isValencyIncreasing_causative : (causative t).IsValencyIncreasing :=
  Voice.causative_isValencyIncreasing

/-- The passive and the causative of a transitive verb both demote the initial A, the one
making the P the subject and the other introducing a causer as the new A
([creissels-2024] §12.5.1). -/
theorem fateOfRole_passive_causativeOfTransitive :
    (passive s).fateOfRole .A = .denucleativized ∧
      (causativeOfTransitive t).fateOfRole .A = .denucleativized ∧
      (causativeOfTransitive t).newParticipant = some .A := by
  simp only [passive, causativeOfTransitive, Voice.fateOfRole_marked,
    Voice.newParticipant_marked]
  decide

end

end Korean
