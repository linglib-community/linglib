module

public import Linglib.Morphology.Nanosyntax.Lexicalization
public import Linglib.Fragments.Xhosa.Basic

/-!
# Taraldsen, Taraldsen Medová and Langa (2018): Class prefixes as specifiers in Southern Bantu

Taraldsen, Taraldsen Medová and Langa analyse the Southern Bantu noun-class prefixes as morphemes
that lexicalize a whole Specifier built on a silent classifier-like noun: a singular prefix stores
`[Nₓ]` and a plural prefix `[# Nₓ]`. Agreement with conjoined singulars shows which singular and
plural prefixes share their noun. The Specifier is a derivation of its own, the classifier first
and the number head merged on it. No entry lexicalizes the number head alone, so the Specifier
gets a single prefix or none, and where it gets none a second Specifier is built inside it as a
last resort, which stacks a plural prefix on the singular one, as in classes 3, 5 and 9 of
Changana and Rhonga.

## Main results

* `exponents_cls_num`: the Specifier `[# Nₓ]` is lexicalized by a single prefix or not at all.
* `stacks_iff_no_entry`: a plural stacks exactly when no entry lexicalizes the plural Specifier
  on the singular's classifier (section 4.5).
* `rhonga_plurals`, `rhonga_stacking_iff_not_sharesClassifierN`: Changana and Rhonga stack in
  classes 3, 5 and 9 and not in 1 and 7, the classes whose prefixes share no classifier.
* `shona_double_plural`: the Shona double plural *ma-mi-sha*.

## Implementation notes

The exponents are the post-augment prefixes, which the paper takes as the prefix proper. The
derivations are those inside the Specifier. Merging the number head on the noun's own spine, the
paper's first try, and raising the noun over it are not modelled, the paper setting both aside.
The classifier of the second Specifier is a parameter of `pluralPrefixes`: the paper leaves the
pairing of prefixes with nouns to the meaning of the silent N or to idiom listing (section 5.3).
The phonological elision of stacked class-5 prefixes and the secondary prefixes of section 5 are
not formalized.

## References

* [taraldsen-et-al-2018]
* [bachetti-2006]
* [starke-2018]
-/

@[expose] public section

namespace TaraldsenEtAl2018

open Morphology.Nanosyntax Morphology.Exponence RoseTree

/-! ### Features and entries -/

/-- The nominal features are the number head `#` and the classifier-like silent nouns `Nₙ`. -/
inductive NCFeature where
  | num : NCFeature
  | cls : ℕ → NCFeature
  deriving DecidableEq, Repr

/-- The structure a singular prefix lexicalizes, the bare classifier `[Nₙ]` (48a). -/
def sgTree (n : ℕ) : RoseTree (Option NCFeature) := spine (.cls n) []

/-- The structure a plural prefix lexicalizes, the Specifier `[# Nₙ]` (41), (48b). -/
def plTree (n : ℕ) : RoseTree (Option NCFeature) := spine (.cls n) [.num]

/-- `SharesClassifierN sg pl` holds when a singular and a plural entry contain the same classifier
N, the foot of each stored tree, which is the conjoined-subject diagnostic of section 2. -/
def SharesClassifierN (sg pl : LexicalEntry (Option NCFeature) String) : Prop :=
  foot sg.tree = foot pl.tree

instance : DecidableRel SharesClassifierN := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### Lexicalizing the Specifier (section 4.2)

The Specifier is derived from its classifier up. The standing assumption is that every entry
with the number head also has a classifier below it, (67), so that none lexicalizes the number
head alone, the work of the Foot Condition (68). -/

variable {L : RuleSet (LexicalEntry (Option NCFeature) String)} {base spec : ℕ}

/-- The Specifier `[# Nₙ]` is lexicalized whole by a single prefix or not at all, the classifier
never evacuating to leave the number head a suffix of its own. -/
theorem exponents_cls_num (h : treeSpellout L (leaf (some .num)) = none) (n : ℕ) :
    exponents L [.cls n, .num] = (treeSpellout L (plTree n)).map fun x ↦ [x] :=
  exponents_cons_of_forall_leaf (L := L) (NCFeature.cls n) (fs := [NCFeature.num])
    (by simpa using h)

/-- The prefixes of a plural noun whose root merged with the classifier `base`, outermost first,
(65)–(75). The Specifier `[# N_base]` is lexicalized as it is where it can be. Otherwise, as a
last resort, a second Specifier `[# N_spec]` is built inside it and the first keeps its singular
prefix. -/
def pluralPrefixes (L : RuleSet (LexicalEntry (Option NCFeature) String)) (base spec : ℕ) :
    Option (List String) :=
  exponents L [.cls base, .num] <|>
    (exponents L [.cls spec, .num]).bind fun outer ↦ (exponents L [.cls base]).map (outer ++ ·)

/-- A plural has a single prefix if an entry lexicalizes the Specifier on the singular's classifier,
and otherwise stacks prefixes (75). -/
theorem pluralPrefixes_eq (h : treeSpellout L (leaf (some .num)) = none) (base spec : ℕ) :
    pluralPrefixes L base spec =
      (((treeSpellout L (plTree base)).map fun x ↦ [x]) <|>
        (treeSpellout L (plTree spec)).bind fun outer ↦
          (treeSpellout L (sgTree base)).map fun inner ↦ [outer, inner]) := by
  rw [pluralPrefixes, exponents_cls_num h, exponents_cls_num h, exponents_singleton, sgTree,
    spine_nil]
  rcases treeSpellout L (plTree spec) with - | o <;>
    rcases treeSpellout L (leaf (some (.cls base))) with - | i <;> rfl

/-- A plural stacks exactly when no entry lexicalizes the plural Specifier on the singular's
classifier, the correlation of section 4.5. -/
theorem stacks_iff_no_entry (h : treeSpellout L (leaf (some .num)) = none) {r : List String}
    (hr : pluralPrefixes L base spec = some r) :
    1 < r.length ↔ ∀ e ∈ L, ¬ e.Matches (plTree base) := by
  rw [← treeSpellout_eq_none_iff]
  rw [pluralPrefixes_eq h] at hr
  rcases hb : treeSpellout L (plTree base) with - | x
  · rcases ho : treeSpellout L (plTree spec) with - | o <;>
      rcases hi : treeSpellout L (sgTree base) with - | i <;> simp [hb, ho, hi] at hr
    simp [← hr]
  · simp [hb] at hr
    simp [← hr]

theorem outer_prefix_is_plural (h : treeSpellout L (leaf (some .num)) = none)
    {outer inner : String} (hr : pluralPrefixes L base spec = some [outer, inner]) :
    ∃ e ∈ L, e.Matches (plTree spec) ∧ e.exponent = outer := by
  rw [pluralPrefixes_eq h] at hr
  rcases hb : treeSpellout L (plTree base) with - | x
  · rcases ho : treeSpellout L (plTree spec) with - | o
    · simp [hb, ho] at hr
    · rcases hi : treeSpellout L (sgTree base) with - | i
      · simp [hb, ho, hi] at hr
      · obtain ⟨rfl, -⟩ : o = outer ∧ i = inner := by simpa [hb, ho, hi] using hr
        obtain ⟨e, he, rfl, hw⟩ := treeSpellout_isElsewhereWinner ho
        exact ⟨e, he, hw.1.2, rfl⟩
  · simp [hb] at hr

/-- Where the plural entry's own classifier merges with the root, (82)–(83), the Specifier and
the last resort are one derivation, so nothing stacks. -/
theorem pluralPrefixes_self (L : RuleSet (LexicalEntry (Option NCFeature) String)) (n : ℕ) :
    pluralPrefixes L n n = exponents L [.cls n, .num] := by
  rw [pluralPrefixes]
  cases exponents L [.cls n, .num] <;> rfl

/-! ### Class pairs -/

/-- A singular class paired with its plural, the singular prefix on its classifier and the
plural prefix on its own. -/
structure ClassPair where
  /-- The classifier the singular prefix lexicalizes. -/
  sgN : ℕ
  sgPrefix : String
  /-- The classifier inside the Specifier the plural prefix lexicalizes. -/
  plN : ℕ
  plPrefix : String

/-- The singular entry `[N]`. -/
def ClassPair.sg (p : ClassPair) : LexicalEntry (Option NCFeature) String :=
  ⟨sgTree p.sgN, p.sgPrefix⟩

/-- The plural entry `[# N]`. -/
def ClassPair.pl (p : ClassPair) : LexicalEntry (Option NCFeature) String :=
  ⟨plTree p.plN, p.plPrefix⟩

/-- The class-prefix lexicon of a list of class pairs. -/
def lexicon (ps : List ClassPair) : RuleSet (LexicalEntry (Option NCFeature) String) :=
  ps.map (·.sg) ++ ps.map (·.pl)

/-- No class prefix lexicalizes the number head alone, every stored tree bottoming out in a
classifier (67). -/
theorem treeSpellout_lexicon_num (ps : List ClassPair) :
    treeSpellout (lexicon ps) (leaf (some .num)) = none := by
  refine treeSpellout_eq_none_iff.2 fun e he hm ↦ ?_
  rcases List.mem_append.1 he with he | he <;> obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
  · simp [LexicalEntry.Matches, ClassPair.sg, sgTree] at hm
  · simp [LexicalEntry.Matches, ClassPair.pl, plTree, spine, phrase, isSubtree_node_iff] at hm

/-! ### The Xhosa lexicon

Gender A (1/2) has *m* `[N₁]` (48a) and *ba* `[# N₁]` (48b), B (3/4) *m* `[N₃]` and *mi* `[# N₄]`
(41a), C (5/6) *li* `[N₅]` (50a) and *ma* `[# N₆]` (50b), and D (7/8) *si* `[N₇]` (49a) and *zi*
`[# N₇]` (49b). For gender E (9/10) the paper gives no entries. The homorganic nasal on `[N₉]`
and *zi* on `[# N₉]` follow its finding that conjoined class-9 singulars take class-10 agreement
(section 2.3), the *zi* of class 10 being an accidental homophone of the class-8 prefix. -/

/-- The Xhosa genders. A, D and E share their N between singular and plural, and B and C
contain distinct Ns, the finding of section 2. -/
def xhosa : Xhosa.Gender → ClassPair
  | .genderA => ⟨1, "m", 1, "ba"⟩
  | .genderB => ⟨3, "m", 4, "mi"⟩
  | .genderC => ⟨5, "li", 6, "ma"⟩
  | .genderD => ⟨7, "si", 7, "zi"⟩
  | .genderE => ⟨9, "n", 9, "zi"⟩

/-- The Xhosa singular entries. -/
def xhosaSg (g : Xhosa.Gender) : LexicalEntry (Option NCFeature) String := (xhosa g).sg

/-- The Xhosa plural entries. -/
def xhosaPl (g : Xhosa.Gender) : LexicalEntry (Option NCFeature) String := (xhosa g).pl

/-- The five Xhosa genders. -/
def xhosaGenders : List Xhosa.Gender := [.genderA, .genderB, .genderC, .genderD, .genderE]

/-- The Xhosa class-prefix lexicon. -/
def xhosaPrefixes : RuleSet (LexicalEntry (Option NCFeature) String) :=
  lexicon (xhosaGenders.map xhosa)

/-- `[N₁]` is lexicalized as *m*, the singular entry winning over *ba* as the smaller match,
and `[# N₁]` as *ba* (48). -/
theorem xhosa_genderA :
    exponents xhosaPrefixes [.cls 1] = some ["m"] ∧
      exponents xhosaPrefixes [.cls 1, .num] = some ["ba"] := by
  decide

theorem xhosa_sharesClassifierN (g : Xhosa.Gender) :
    SharesClassifierN (xhosaSg g) (xhosaPl g) ↔ g ∈ [.genderA, .genderD, .genderE] := by
  cases g <;> decide

/-- Every Xhosa plural, including genders B and C, has a single prefix ((82)–(83)). -/
theorem xhosa_plurals :
    xhosaGenders.map (fun g ↦ pluralPrefixes xhosaPrefixes (xhosa g).plN (xhosa g).plN) =
      [some ["ba"], some ["mi"], some ["ma"], some ["zi"], some ["zi"]] := by
  decide

/-- The class-prefix entries lexicalize the Fragment's subject concords of classes 5, 7, 2
and 8, so one set of entries serves prefixes and concords (60)–(61). -/
theorem xhosa_prefix_sc_identity :
    exponents xhosaPrefixes [.cls 5] = (Xhosa.subjPrefix .cl5).map ([·]) ∧
      exponents xhosaPrefixes [.cls 7] = (Xhosa.subjPrefix .cl7).map ([·]) ∧
      exponents xhosaPrefixes [.cls 1, .num] = (Xhosa.subjPrefix .cl2).map ([·]) ∧
      exponents xhosaPrefixes [.cls 7, .num] = (Xhosa.subjPrefix .cl8).map ([·]) := by
  decide

/-! ### The Changana and Rhonga lexicon

The plural classifiers N₄, N₆ and N₁₀ are no singular's and do not merge with the root, so
classes 3, 5 and 9 stack (62). -/

/-- The Changana and Rhonga genders are 1/2 *mu* (79a) and *va* (79b), 3/4 *mu* (76a) and *mi*
(77a), 5/6 *rhi* (76b) and *ma* (77b), 7/8 *xi* (80a) and *swi* (80b), and 9/10 *yi* (76c) and
*ti* (77c). -/
def rhonga : List ClassPair :=
  [⟨1, "mu", 1, "va"⟩, ⟨3, "mu", 4, "mi"⟩, ⟨5, "rhi", 6, "ma"⟩, ⟨7, "xi", 7, "swi"⟩,
    ⟨9, "yi", 10, "ti"⟩]

/-- The Changana and Rhonga class-prefix lexicon. -/
def rhongaPrefixes : RuleSet (LexicalEntry (Option NCFeature) String) := lexicon rhonga

/-- In Rhonga, classes 3, 5 and 9 stack prefixes and classes 1 and 7 have one ((62), (78)). -/
theorem rhonga_plurals :
    rhonga.map (fun p ↦ pluralPrefixes rhongaPrefixes p.sgN p.plN) =
      [some ["va"], some ["mi", "mu"], some ["ma", "rhi"], some ["swi"], some ["ti", "yi"]] := by
  decide

/-- In Changana and Rhonga a plural stacks exactly when its prefix and the singular's share no
classifier, the correlation of section 4.5 with the agreement facts: those are the genders
with no entry for the plural Specifier on the singular's classifier. -/
theorem rhonga_stacking_iff_not_sharesClassifierN {p : ClassPair} (hp : p ∈ rhonga)
    {r : List String} (hr : pluralPrefixes rhongaPrefixes p.sgN p.plN = some r) :
    1 < r.length ↔ ¬ SharesClassifierN p.sg p.pl := by
  rw [stacks_iff_no_entry (treeSpellout_lexicon_num rhonga) hr]
  clear hr
  revert p
  decide

/-! ### Shona double plurals (section 4.3) -/

/-- Shona *mi* on the bare `[N₄]` (89) and *ma* on `[# N₆]`. -/
def shonaPrefixes : RuleSet (LexicalEntry (Option NCFeature) String) :=
  [⟨sgTree 4, "mi"⟩, ⟨plTree 6, "ma"⟩]

/-- The double plural *ma-mi-sha* 'groups of villages' ((84), (88)) derives from the entry (89) but
not from (87). -/
theorem shona_double_plural :
    pluralPrefixes shonaPrefixes 4 6 = some ["ma", "mi"] ∧
      pluralPrefixes [⟨plTree 4, "mi"⟩, ⟨plTree 6, "ma"⟩] 4 6 = some ["mi"] := by
  decide

end TaraldsenEtAl2018
