/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.ElementTheory
public import Linglib.Phonology.Autosegmental.Skeleton
public import Linglib.Phonology.StrictCV.Basic
public import Linglib.Fragments.Slavic.Czech.Phonology
public import Linglib.Data.Wordlist.CaviraniVandenWyngaerd2026

/-!
# Cavirani and Vanden Wyngaerd (2026): A representational analysis of Czech palatalisation

Czech suffixes palatalise the consonant before them in three patterns, small, medium and big,
which the vowel of the suffix does not tell apart: *-ě*, *-ěj* and *-ěn* begin alike and
palatalise differently. Cavirani and Vanden Wyngaerd give each suffix floating elements that dock
onto the base-final consonant, |I| for the small pattern, |H| and |I| for the medium one, |H| and
a headed |I| for the big one. What is built is pronounced by lookup in a phonetic lexicon, so
several structures may share a phone. A labial and /l/ have |U| at the place node, which repels
|I|. After a labial the |I| is then heard as a segment of its own, unless the vowel of the suffix
floats, and after /l/ it is not heard.

The rows are the word pairs of the paper's tables, and the Czech fragment reads the alternating
consonant off their spelling.

## Main statements

* `derive_eq_sup`: on a velar or a coronal the palataliser docks whole, whatever the suffix.
* `associate_of_mem`: a consonant with |U| at its place keeps its place and leaves |I| afloat.
* `interpret_roots`: outside /ɦ/, the root nodes built for a row are pronounced as the phonemes
  of its attested alternant.
* `derive_comparative`, `derive_h`: a fricative builds one structure under small and medium
  palatalisation, where /ɦ/ has two reflexes.
* `loket_lokte`: the paper's illustration of proper government, *loket* against *lok_te*.

## Implementation notes

* The skeleton is reduced to what the outcome depends on: the root node of the base-final
  consonant, whether the vowel of the suffix floats, and what a sonorant spreads. The analysis
  uses neither government nor licensing; only the illustration of proper government in the
  paper's presentation of strict CV is checked, against the Strict CV substrate.
* The melodies are those of the paper's tables of plain and palatalised consonants. Its closing
  summary table prints /s/ without |I| and /n/ without |A|.
* Union is taken in the structure, so small and medium palatalisation of /x/ build one structure
  where the paper counts two.
* The palatal segment after a labial is a root node under a V slot, a vowel for the paper. The
  fragment follows Short in writing it /j/.

## TODO

The paper derives a voiced obstruent as its voiceless counterpart with a headed |L| at the
laryngeal node, and pairs /ɦ/ with /x/. Since /x/ has |H| at its manner node, /ɦ/ then has one
structure under small and medium palatalisation, where the forms have [z] and [ʒ] (`derive_h`).
The reflexes of /ɦ/ pattern as those of /k/ do, small against medium and big.

## References

* [cavirani-vandenwyngaerd-2026]
* [backley-2011]
* [backley-2017]
* [short-1993-czech]
* [lowenstamm-1996]
* [scheer-2004]
-/

@[expose] public section

namespace CaviraniVandenWyngaerd2026

open ElementTheory CLDF.Wordlist
open Autosegmental (Slot)

/-! ### The plain consonants -/

/-- The stop /k/ is |ʔ|, with no place. -/
def k : Segment := { manner := .simplex .glottal }

/-- The fricative /x/ is |H|, with no place. -/
def x : Segment := { manner := .simplex .H }

/-- The stop /t/ is |ʔ.A|. -/
def t : Segment := { manner := .simplex .glottal, place := .simplex .A }

/-- The fricative /s/ is |H.AI|. -/
def s : Segment := { manner := .simplex .H, place := .simplex .A ⊔ .simplex .I }

/-- The nasal /n/ is |L.A|. -/
def n : Segment := { manner := .simplex .L, place := .simplex .A }

/-- The rhotic /r/ is |A| at the manner node, where /s/ has |A| at the place node. -/
def r : Segment := { manner := .simplex .A }

/-- The stop /p/ is |ʔ.U|. -/
def p : Segment := { manner := .simplex .glottal, place := .simplex .U }

/-- The fricative /f/ is |H.U|. -/
def f : Segment := { manner := .simplex .H, place := .simplex .U }

/-- The nasal /m/ is |L.U|. -/
def m : Segment := { manner := .simplex .L, place := .simplex .U }

/-- The lateral /l/ is |A.U|, a liquid with the place of the labials. -/
def l : Segment := { manner := .simplex .A, place := .simplex .U }

/-- Voicing is a headed |L| at the laryngeal node. -/
def voice : Segment := { laryngeal := .headedSimplex .L }

/-- The consonants of the paper's tables by the letters that write them, each with its phoneme in
the fragment and with its melody if the paper analyses it. A voiced obstruent is its voiceless
counterpart with voicing. The paper sets /g/ and /ʦ/ aside. -/
def consonants : List (String × Phonology.Segment × Option Segment) :=
  [("k", Czech.Phonology.k, some k), ("g", Czech.Phonology.g, none),
   ("ch", Czech.Phonology.ch, some x), ("h", Czech.Phonology.h, some (x ⊔ voice)),
   ("t", Czech.Phonology.t, some t), ("d", Czech.Phonology.d, some (t ⊔ voice)),
   ("c", Czech.Phonology.c, none), ("s", Czech.Phonology.s, some s),
   ("z", Czech.Phonology.z, some (s ⊔ voice)), ("n", Czech.Phonology.n, some n),
   ("r", Czech.Phonology.r, some r), ("l", Czech.Phonology.l, some l),
   ("p", Czech.Phonology.p, some p), ("b", Czech.Phonology.b, some (p ⊔ voice)),
   ("f", Czech.Phonology.f, some f), ("v", Czech.Phonology.v, some (f ⊔ voice)),
   ("m", Czech.Phonology.m, some m)]

/-- Each letter writes its phoneme. -/
theorem ofString?_consonants : ∀ a ∈ consonants, Czech.Phonology.ofString? a.1 = some [a.2.1] := by
  decide +kernel

/-- Each node of a melody holds only elements that it hosts. -/
theorem wellFormed_consonants : ∀ a ∈ consonants, ∀ c ∈ a.2.2, c.WellFormed := by decide

/-! ### The palatalisers and their suffixes -/

/-- The small palataliser is a floating |I|. -/
def PAL₁ : Segment := { place := .simplex .I }

/-- The medium palataliser is a floating |H| and |I|. -/
def PAL₂ : Segment := { manner := .simplex .H, place := .simplex .I }

/-- The big palataliser is a floating |H| and a headed |I|. -/
def PAL₃ : Segment := { manner := .simplex .H, place := .headedSimplex .I }

theorem PAL₁_lt_PAL₂ : PAL₁ < PAL₂ := by decide

theorem PAL₂_lt_PAL₃ : PAL₂ < PAL₃ := by decide

theorem wellFormed_PAL : PAL₁.WellFormed ∧ PAL₂.WellFormed ∧ PAL₃.WellFormed := by decide

/-- How the vowel of a suffix sits on the skeleton. -/
inductive Link
  /-- The vowel is linked to a V slot of the suffix, which begins with an empty C slot. -/
  | linked
  /-- The vowel is on a root node that floats. -/
  | floating
  deriving DecidableEq, Repr

/-- A palatalising suffix has a floating palataliser before its vowel. -/
structure Suffix where
  /-- The floating elements. -/
  palataliser : Segment
  /-- The melody of the vowel. -/
  vowel : MR
  /-- How the vowel sits on the skeleton. -/
  link : Link
  deriving DecidableEq

/-- The locative and dative singular feminine *-ě* has the small palataliser and a linked
/ɛ/ (14). -/
def locDat : Suffix := ⟨PAL₁, .simplex .A ⊔ .simplex .I, .linked⟩

/-- The comparative *-ěj* has the medium palataliser and a linked /ɛ/ (15). -/
def comparative : Suffix := ⟨PAL₂, .simplex .A ⊔ .simplex .I, .linked⟩

/-- The causative *-i* has the medium palataliser and a floating /i/ (16). -/
def causative : Suffix := ⟨PAL₂, .simplex .I, .floating⟩

/-- The passive participle *-ěn* has the big palataliser and a floating /ɛ/ (17). -/
def passPtcp : Suffix := ⟨PAL₃, .simplex .A ⊔ .simplex .I, .floating⟩

/-! ### Docking -/

variable {b a : Segment} {σ : Suffix}

/-- A stronger palataliser builds a larger structure on any base. -/
theorem sup_PAL_mono (b : Segment) :
    b ≤ b ⊔ PAL₁ ∧ b ⊔ PAL₁ ≤ b ⊔ PAL₂ ∧ b ⊔ PAL₂ ≤ b ⊔ PAL₃ :=
  ⟨le_sup_left, sup_le_sup_left PAL₁_lt_PAL₂.le b, sup_le_sup_left PAL₂_lt_PAL₃.le b⟩

/-- /s/ contains the small and the medium palataliser, so neither changes it. -/
theorem s_sup_PAL : s ⊔ PAL₁ = s ∧ s ⊔ PAL₂ = s :=
  ⟨sup_eq_left.2 (by decide), sup_eq_left.2 (by decide)⟩

/-- Big-palatalised /d/ has two heads, |I| at its place node and |L| at its laryngeal node, one
for each of two fundamentals. -/
theorem heads_d_sup_PAL₃ :
    (t ⊔ voice ⊔ PAL₃).place.heads ∪ (t ⊔ voice ⊔ PAL₃).laryngeal.heads = {.I, .L} ∧
      Element.AntagonismFree {.I, .L} := by
  decide

/-! ### Association -/

/-- The association of floating elements with a root node (13). They join its nodes, except that
floating place elements stay afloat where the place node would come to hold both |I| and |U|,
which Czech has on one tier. The result is the root node and the elements left afloat. -/
def associate (root floating : Segment) : Segment × Segment :=
  if Element.AntagonismFree (root.place ⊔ floating.place).elements then (root ⊔ floating, ⊥)
  else (root ⊔ { floating with place := ⊥ }, { place := floating.place })

/-- Floating elements associate whole with a root node whose place holds at most |A| and |I|, as
that of a velar or a coronal does. -/
theorem associate_eq_sup (hb : b.place.elements ⊆ {.A, .I}) (ha : a.place.elements ⊆ {.A, .I}) :
    associate b a = (b ⊔ a, ⊥) :=
  ite_eq_left <| .subset (t := {.A, .I}) (by decide) (Finset.union_subset hb ha)

/-- A root node with |U| at its place repels a floating |I|. The root node keeps its place and
the floating place elements stay afloat, while the other floating elements associate. -/
theorem associate_of_mem (hU : .U ∈ b.place.elements) (hI : .I ∈ a.place.elements) :
    associate b a = (b ⊔ { a with place := ⊥ }, { place := a.place }) :=
  ite_eq_right fun h ↦ Element.noConfusion <|
    h (Finset.mem_coe.2 (Finset.mem_union_left _ hU))
      (Finset.mem_coe.2 (Finset.mem_union_right _ hI)) rfl

/-- Elements away from the place node commute with association, so a voiced base is derived as
its voiceless counterpart is, with voicing added. -/
theorem associate_sup {c : Segment} (hc : c.place = ⊥) (b a : Segment) :
    associate (b ⊔ c) a = ((associate b a).1 ⊔ c, (associate b a).2) := by
  have hp : (b ⊔ c).place = b.place := by rw [Segment.sup_place, hc, sup_bot_eq]
  simp only [associate, hp]
  split_ifs <;> simp only [sup_right_comm]

/-- A base with |H| at its manner node associates with the medium palataliser as with the small
one. -/
theorem associate_PAL₂ (h : .H ∈ b.manner.elements) : associate b PAL₂ = associate b PAL₁ :=
  have hm : b.manner ⊔ .simplex .H = b.manner ⊔ ⊥ := by simpa using h
  congrArg₂ (fun c c' ↦ if Element.AntagonismFree (b.place ⊔ PAL₁.place).elements
    then (c, (⊥ : Segment)) else (c', { place := PAL₁.place }))
    (Segment.ext hm rfl rfl) (Segment.ext hm rfl rfl)

/-! ### Derivations -/

/-- What a sonorant spreads to a following C slot, a nasal its manner node (29) and a liquid its
root node (34). An obstruent spreads nothing. -/
def spread (c : Segment) : Option Segment :=
  if .L ∈ c.manner.elements then some { manner := c.manner }
  else if .A ∈ c.manner.elements then some c
  else none

/-- The root nodes on which a base-final consonant and the palataliser of a suffix are pronounced,
each with the slot of the skeleton it is linked to. The palataliser associates with the
consonant. Elements left afloat join a floating vowel on the base-final V slot, and so have no
root node of their own (31), (33). Before a linked vowel they take the base-final V slot (28),
unless the consonant spreads to the C slot of the suffix and so bars the way, when they associate
with that slot if it does not repel them (29) and otherwise stay afloat (34). -/
def derive (b : Segment) (σ : Suffix) : List (Slot × Segment) :=
  let c := associate b σ.palataliser
  (.C, c.1) :: if c.2 = ⊥ ∨ σ.link = .floating then [] else
    match spread c.1 with
    | none => [(.V, c.2)]
    | some c' => if (associate c' c.2).2 = ⊥ then [(.C, (associate c' c.2).1)] else []

/-- On a velar or a coronal the palataliser docks whole, whatever the suffix. -/
theorem derive_eq_sup (hb : b.place.elements ⊆ {.A, .I})
    (hσ : σ.palataliser.place.elements ⊆ {.A, .I}) :
    derive b σ = [(.C, b ⊔ σ.palataliser)] := by
  simp [derive, associate_eq_sup hb hσ]

/-- Before a floating vowel the palataliser has no root node of its own, whatever the base. -/
theorem derive_of_floating (h : σ.link = .floating) :
    derive b σ = [(.C, (associate b σ.palataliser).1)] := by
  simp [derive, h]

/-- A floating vowel has every element that its palataliser can leave afloat, so the two are one
vowel when they meet on the base-final V slot. -/
theorem palataliser_place_subset_vowel :
    causative.palataliser.place.elements ⊆ causative.vowel.elements ∧
      passPtcp.palataliser.place.elements ⊆ passPtcp.vowel.elements := by
  decide

/-- The labials and the lateral before the comparative, the causative and the locative. /p/ takes
the |H| and leaves |I| to the base-final V slot, or to the floating vowel. /m/ spreads its manner
node, where the |I| docks, and /l/ spreads its root node, which repels it. -/
theorem derive_labial :
    derive p comparative = [(.C, p ⊔ { manner := .simplex .H }), (.V, PAL₁)] ∧
      derive p causative = [(.C, p ⊔ { manner := .simplex .H })] ∧
      derive m comparative = [(.C, m ⊔ { manner := .simplex .H }),
        (.C, { manner := .simplex .L ⊔ .simplex .H, place := .simplex .I })] ∧
      derive l locDat = [(.C, l)] := by
  decide

private theorem derive_congr {τ : Suffix}
    (hp : associate b σ.palataliser = associate b τ.palataliser) (hl : σ.link = τ.link) :
    derive b σ = derive b τ := by
  unfold derive
  rw [hp, hl]

/-- A base with |H| at its manner node builds in the comparative what it builds in the locative,
so a fricative cannot tell medium palatalisation from small. -/
theorem derive_comparative (h : .H ∈ b.manner.elements) :
    derive b comparative = derive b locDat :=
  derive_congr (associate_PAL₂ h) rfl

/-! ### The rows of the tables -/

/-- The phonemes that the alternating consonant of a form writes, its second segment, read in the
context of the whole form. -/
def alternant (form : Form Wordlist.Cell) : Option (List Phonology.Segment) :=
  match form.segments.map fun w ↦ w.toList.map Char.toLower with
  | stem :: c :: ending => do
    let whole ← Czech.Phonology.ofChars (stem ++ c ++ ending.flatten)
    let pre ← Czech.Phonology.ofChars stem
    let post ← Czech.Phonology.ofChars ending.flatten
    pure ((whole.drop pre.length).take (whole.length - pre.length - post.length))
  | _ => none

/-- A row of the tables pairs a base-final consonant and a suffix with the suffixed form. -/
structure Row where
  /-- The base-final consonant. -/
  base : Phonology.Segment
  /-- The melody of the base-final consonant, if the paper analyses it. -/
  melody : Option Segment
  /-- The suffix. -/
  suffix : Suffix
  /-- The suffixed form. -/
  form : Form Wordlist.Cell

/-- The suffixes, by the names of the relations in the data. -/
def suffixes : List (String × Suffix) :=
  [("locDatFSg", locDat), ("comparative", comparative), ("causative", causative),
   ("passPtcp", passPtcp)]

/-- The base-final consonant of a base form, the consonant of the tables that its second segment
writes. -/
def baseConsonant (form : Form Wordlist.Cell) :
    Option (String × Phonology.Segment × Option Segment) :=
  match form.segments with
  | _ :: c :: _ => consonants.find? (·.1 = c)
  | _ => none

/-- The row of a relation between a base form and a suffixed form, with the base-final consonant
of the base form. -/
def Row.ofRelation (rel : FormRelation (Form Wordlist.Cell)) : Option Row := do
  let suffix ← suffixes.lookup rel.relation
  let (_, base, melody) ← baseConsonant rel.form
  pure ⟨base, melody, suffix, rel.target⟩

/-- Every pair of the tables is a row, save the two possessives that stand in for a participle. -/
theorem isSome_ofRelation : ∀ rel ∈ Wordlist.relations,
    rel.relation ≠ "possessive" → (Row.ofRelation rel).isSome := by
  decide +kernel

/-- A noun or an adjective writes the base-final consonant itself, read in the context of the
whole form. The base form of a participle is an infinitive, whose theme vowel palatalises. -/
theorem alternant_base : ∀ rel ∈ Wordlist.relations,
    rel.relation ∈ ["locDatFSg", "comparative", "causative"] →
      alternant rel.form = (baseConsonant rel.form).map ([·.2.1]) := by
  decide +kernel

/-- The rows of the tables of small and big palatalisation, of the comparative and of the
causative. -/
def rows : List Row := Wordlist.relations.filterMap Row.ofRelation

/-- The root nodes that the analysis builds for a row, if it gives the base a melody. -/
def Row.roots (a : Row) : Option (List (Slot × Segment)) := a.melody.map (derive · a.suffix)

/-- Small palatalisation of a velar is the second palatalisation of velars. -/
theorem alternant_eq_secondPalatalization : ∀ a ∈ rows, a.suffix = locDat →
    a.base ∈ Czech.Phonology.palatalizing →
      alternant a.form = some [Czech.Phonology.secondPalatalization a.base] := by
  decide +kernel

/-! ### Lexical access -/

/-- The phonetic lexicon that the rows induce, each root node that the analysis builds with the
phoneme attested for it. A plain consonant is listed first, with its melody. -/
def lexicon : List ((Slot × Segment) × Phonology.Segment) :=
  consonants.filterMap (fun a ↦ a.2.2.map fun c ↦ ((.C, c), a.2.1)) ++
    rows.flatMap fun a ↦ (a.roots.getD []).zip ((alternant a.form).getD [])

/-- Lexical access pronounces a root node as the lexicon lists it. -/
def interpret (c : Slot × Segment) : Option Phonology.Segment := lexicon.lookup c

/-- Outside /ɦ/, the root nodes that the analysis builds for a row are pronounced as the phonemes
of its alternant. Since the lexicon is read off the rows, this says that there is a root node for
each phoneme, two where a palatal segment follows a labial before a linked vowel, and that root
nodes built alike are pronounced alike. -/
theorem interpret_roots : ∀ a ∈ rows, a.base ≠ Czech.Phonology.h →
    ∀ c ∈ a.roots, c.mapM interpret = alternant a.form := by
  decide +kernel

/-- As the voiced counterpart of /x/, /ɦ/ builds one structure under small and medium
palatalisation, while *knize* has [z] and *strožejší* has [ʒ]. -/
theorem derive_h :
    derive (x ⊔ voice) comparative = derive (x ⊔ voice) locDat ∧
      alternant Wordlist.knize = some [Czech.Phonology.z] ∧
      alternant Wordlist.strozejsi = some [Czech.Phonology.ž] :=
  ⟨derive_comparative (by decide), by decide +kernel⟩

/-- Three structures are pronounced [ʃ], palatalised /x/ with unheaded and with headed |I|, and
big-palatalised /s/. -/
theorem interpret_š :
    [x ⊔ PAL₁, x ⊔ PAL₃, s ⊔ PAL₃].Nodup ∧
      ∀ c ∈ [x ⊔ PAL₁, x ⊔ PAL₃, s ⊔ PAL₃], interpret (.C, c) = some Czech.Phonology.š := by
  decide +kernel

/-- The medium pattern goes with the big one on a velar and with the small one on a coronal.
/k/ gives [ts], [tʃ], [tʃ] and /t/ gives [c], [c], [ts], though the three structures differ on
each. -/
theorem interpret_medium :
    [k ⊔ PAL₁, k ⊔ PAL₂, k ⊔ PAL₃].Nodup ∧ [t ⊔ PAL₁, t ⊔ PAL₂, t ⊔ PAL₃].Nodup ∧
      [k ⊔ PAL₁, k ⊔ PAL₂, k ⊔ PAL₃].map (fun c ↦ interpret (.C, c)) =
        [some Czech.Phonology.c, some Czech.Phonology.č, some Czech.Phonology.č] ∧
      [t ⊔ PAL₁, t ⊔ PAL₂, t ⊔ PAL₃].map (fun c ↦ interpret (.C, c)) =
        [some Czech.Phonology.ť, some Czech.Phonology.ť, some Czech.Phonology.c] := by
  decide +kernel

/-! ### Proper government (§3.3)

The paper illustrates proper government with the alternation in Czech 'elbow': Czech allows an
empty final nucleus but does not let it govern. -/

/-- A Czech final nucleus may be empty and then neither governs nor licenses. -/
def czechFinal : StrictCV.FinalNucleus := ⟨true, false⟩

/-- In *loket* 'elbow.NOM.SG' the final nucleus is empty and governs nothing, so the alternating
vowel before it is pronounced; in *lok_te* 'elbow.GEN.SG' the suffix vowel governs it and it
stays silent (§3.3). The nuclei are those of *lo*, *ke* and *t(e)*. -/
theorem loket_lokte :
    (StrictCV.standard czechFinal
        [{ melody := .associated }, { melody := .floating }, { melody := .empty }]).map
        Prod.snd = [true, true, false] ∧
      (StrictCV.standard czechFinal
        [{ melody := .associated }, { melody := .floating }, { melody := .associated }]).map
        Prod.snd = [true, false, true] := by
  decide

end CaviraniVandenWyngaerd2026
