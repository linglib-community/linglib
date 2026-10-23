module

public import Linglib.Morphology.Morph
public import Mathlib.Data.List.DropRight

/-!
# English inflectional suffixes and their spelling

The regular inflectional suffixes of English are *-s*, *-ed*, *-ing*, *-er* and *-est*. A suffix
is written on its base with four spelling alternations, which the Cambridge Grammar states once
for nouns, verbs and adjectives. Three change the end of the base: a final consonant letter
doubles before a suffix that begins with a vowel (*hopping*), a final *e* drops before one
(*hoping*), and a final *y* after a consonant becomes *i*, or *ie* before *-s* (*pitied*,
*tries*). The fourth is in the suffix: *-s* is *-es* after a sibilant and after *o* (*foxes*,
*goes*).

## Main definitions

* `English.Inflection.s`, `ed`, `ing`, `er`, `est`: the suffixes.
* `English.Inflection.attach`: the spelling of a base with a suffix.
* `English.Inflection.spell`: the spelling of a sequence of morphs.

## Main statements

* `English.Inflection.suffix_attach`: a suffixed form ends in its suffix.
* `English.Inflection.rdrop_prefix_attach`: the alternations reach no further into the base than
  its last two letters.

## Implementation notes

* The rules read the spelling. A vowel symbol is a vowel letter or *y*, other than the *u* of
  *qu* and an initial *y*.
* A final consonant doubles when the last syllable is stressed. A base of one syllable is, and
  its spelling shows that it has one; for a longer base the argument `doubling` says so,
  *regretted* against *visited*.
* An entry lists what the rules do not give: *ch* for /k/ (*epochs*), a final *e* that is the
  vowel of a longer base (*acme*), *ie* for /ɪ/ (*sortieing*), a doubled *s* (*gasses*) and
  nouns in *o* with *-s* (*dynamos*).

## References

* [huddleston-pullum-2002]
-/

@[expose] public section

open Morphology

namespace English.Inflection

/-! ### The suffixes -/

/-- The *-s* of the plural and of the third person singular present. -/
def s : Morph := .suff "s"

/-- The *-ed* of the past and the past participle. -/
def ed : Morph := .suff "ed"

/-- The *-ing* of the present participle. -/
def ing : Morph := .suff "ing"

/-- The *-er* of the comparative. -/
def er : Morph := .suff "er"

/-- The *-est* of the superlative. -/
def est : Morph := .suff "est"

/-! ### Spelling

A base is read from its end, so the rules take its reversal `r`. -/

/-- The letters *a*, *e*, *i*, *o* and *u*. -/
def IsVowelLetter (c : Char) : Prop := c ∈ ['a', 'e', 'i', 'o', 'u']

instance : DecidablePred IsVowelLetter := fun c ↦ inferInstanceAs (Decidable (c ∈ _))

/-- `EndsInVowel r` says that the spelling whose reversal is `r` ends in a vowel symbol, which is
a vowel letter or *y* other than the *u* of *qu* and an initial *y*. -/
def EndsInVowel (r : List Char) : Prop :=
  (∃ c ∈ r.head?, IsVowelLetter c ∨ c = 'y') ∧ ¬['u', 'q'] <+: r ∧ r ≠ ['y']

instance : DecidablePred EndsInVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `alternant r suffix` is the suffix as written after the base whose reversal is `r`. The
suffix *-s* is *-es* after *s*, *x*, *z*, *sh* and *ch*, and after *o* that follows a
consonant. -/
def alternant : List Char → List Char → List Char
  | 's' :: _, ['s'] | 'x' :: _, ['s'] | 'z' :: _, ['s'] | 'h' :: 's' :: _, ['s']
  | 'h' :: 'c' :: _, ['s'] => ['e', 's']
  | 'o' :: c :: r, ['s'] => if EndsInVowel (c :: r) then ['s'] else ['e', 's']
  | _, suffix => suffix

/-- `baseBefore r suffix doubling` is the reversal of the base as written before `suffix`, where
`r` is the reversal of the base. A final *y* after a consonant is *i*, or *ie* before *-s*, and
stays before *i*, where a final *ie* is *y*. A final *e* drops before a vowel when the base has
another vowel, but *ee*, *oe* and *ye* keep it before *i*. A final consonant letter other than
*h*, *w*, *x* and *y* doubles before a vowel after a single vowel letter, in a base of one
syllable or, if `doubling` holds, a longer one; an *s* does not double before *-es*. -/
def baseBefore (r suffix : List Char) (doubling : Bool := false) : List Char :=
  match r, suffix with
  | 'y' :: r', x :: _ =>
    if EndsInVowel r' ∨ x = 'i' then r else if suffix = ['s'] then 'e' :: 'i' :: r' else 'i' :: r'
  | 'e' :: 'i' :: r', 'i' :: _ => 'y' :: r'
  | 'e' :: r', x :: _ =>
    if IsVowelLetter x ∧ (∃ t ∈ r'.tails, EndsInVowel t) ∧
      (x = 'e' ∨ r'.head? ∉ [some 'e', some 'o', some 'y']) then r' else r
  | c :: v :: r', x :: _ =>
    if IsVowelLetter x ∧ ¬IsVowelLetter c ∧ c ∉ ['h', 'w', 'x', 'y'] ∧
      ¬(c = 's' ∧ suffix = ['e', 's']) ∧ EndsInVowel (v :: r') ∧ ¬EndsInVowel r' ∧
      (doubling = true ∨ ∀ t ∈ r'.tails, ¬EndsInVowel t) then c :: r else r
  | _, _ => r

/-- `attach b suffix doubling` is the spelling of the base `b` with `suffix`. For a base of more
than one syllable, `doubling` says that its final consonant doubles, as it does when the last
syllable is stressed. -/
def attach (b suffix : List Char) (doubling : Bool := false) : List Char :=
  (baseBefore b.reverse (alternant b.reverse suffix) doubling).reverse ++
    alternant b.reverse suffix

/-- `spell ms doubling` is the spelling of the sequence of morphs `ms`, with each suffix written
on what precedes it in its word by `attach` and the words separated by spaces. -/
def spell (ms : List Morph) (doubling : Bool := false) : String :=
  String.ofList <| [' '].intercalate <| (Morph.wordsAt .clitic ms).map fun w ↦
    w.foldl (fun b m ↦ if m.kind = .bound .after .affix then attach b m.form.toList doubling
      else b ++ m.form.toList) []

variable (doubling : Bool) (b r suffix : List Char)

theorem suffix_alternant : suffix <:+ alternant r suffix := by
  unfold alternant; split <;> try split
  all_goals simp [List.suffix_cons]

/-- A suffixed form ends in its suffix. -/
theorem suffix_attach : suffix <:+ attach b suffix doubling :=
  (suffix_alternant _ _).trans (List.suffix_append _ _)

theorem drop_suffix_baseBefore : r.drop 2 <:+ baseBefore r suffix doubling := by
  unfold baseBefore; split <;> try split_ifs
  all_goals simp [List.suffix_cons_iff, List.tail_suffix, List.drop_suffix]

/-- The alternations reach no further into the base than its last two letters. -/
theorem rdrop_prefix_attach : b.rdrop 2 <+: attach b suffix doubling := by
  rw [List.rdrop_eq_reverse_drop_reverse]
  exact (List.reverse_prefix.2 (drop_suffix_baseBefore ..)).trans (List.prefix_append _ _)

/-! ### The grammar's examples -/

/-- `suffixed b m doubling` is the spelling of the root `b` with the suffix `m`. -/
private abbrev suffixed (b : String) (m : Morph) (doubling : Bool := false) : String :=
  spell [.root b, m] doubling

/-- The four alternations. -/
example : suffixed "hop" ing = "hopping" ∧ suffixed "hope" ing = "hoping" ∧
    suffixed "pity" ed = "pitied" ∧ suffixed "cat" s = "cats" ∧ suffixed "fox" s = "foxes" := by
  decide

/-- A consonant doubles after a single vowel letter in a stressed last syllable, and so not in
*bleated*, *neater* and *offered*; *h*, *w*, *x* and *y* do not double, and a *z* does before
*-es*. -/
example : suffixed "bat" ed = "batted" ∧ suffixed "fat" er = "fatter" ∧
    suffixed "prefer" ed true = "preferred" ∧ suffixed "unfit" est true = "unfittest" ∧
    suffixed "equip" ing true = "equipping" ∧ suffixed "bleat" ed = "bleated" ∧
    suffixed "neat" er = "neater" ∧ suffixed "offer" ed = "offered" ∧
    suffixed "hurrah" ed = "hurrahed" ∧ suffixed "saw" ing = "sawing" ∧
    suffixed "stay" ed = "stayed" ∧ suffixed "box" ing = "boxing" ∧
    suffixed "quiz" s = "quizzes" ∧ suffixed "quiz" ed = "quizzed" ∧
    suffixed "gas" s = "gases" ∧ suffixed "sip" s = "sips" := by
  decide

/-- A mute *e* drops before a vowel and stays before *-s*; the *e* of *ee*, *oe* and *ye* stays
before *-ing*, and *ie* is *y* there. -/
example : suffixed "like" ing = "liking" ∧ suffixed "like" s = "likes" ∧
    suffixed "edge" ed = "edged" ∧ suffixed "simple" er = "simpler" ∧
    suffixed "subdue" ing = "subduing" ∧ suffixed "free" ing = "freeing" ∧
    suffixed "free" ed = "freed" ∧ suffixed "free" est = "freest" ∧
    suffixed "hoe" ing = "hoeing" ∧ suffixed "dye" ing = "dyeing" ∧ suffixed "dye" ed = "dyed" ∧
    suffixed "lie" ing = "lying" ∧ suffixed "lie" ed = "lied" ∧ suffixed "be" ing = "being" := by
  decide

/-- A *y* that is a vowel symbol by itself is replaced, and one in *ay*, *oy* or *uy* is not. -/
example : suffixed "try" ing = "trying" ∧ suffixed "try" s = "tries" ∧
    suffixed "try" ed = "tried" ∧ suffixed "silly" er = "sillier" ∧
    suffixed "city" s = "cities" ∧ suffixed "soliloquy" s = "soliloquies" ∧
    suffixed "stay" s = "stays" ∧ suffixed "coy" er = "coyer" ∧ suffixed "guy" s = "guys" := by
  decide

/-- The suffix *-s* is *-es* after a sibilant and after *o* that follows a consonant. -/
example : suffixed "miss" s = "misses" ∧ suffixed "buzz" s = "buzzes" ∧
    suffixed "wish" s = "wishes" ∧ suffixed "fix" s = "fixes" ∧ suffixed "bench" s = "benches" ∧
    suffixed "echo" s = "echoes" ∧ suffixed "go" s = "goes" ∧ suffixed "veto" s = "vetoes" ∧
    suffixed "boo" s = "boos" ∧ suffixed "embryo" s = "embryos" ∧
    suffixed "radio" s = "radios" := by
  decide

/-- A suffix is written on the root, before a particle. -/
example : spell [.root "depend", s, .free "on"] = "depends on" := by decide

end English.Inflection
