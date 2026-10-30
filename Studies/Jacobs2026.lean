module

public import Linglib.Data.Experiments.Jacobs2026
public import Linglib.Data.Wordlist.Jacobs2026
public import Linglib.Fragments.Latin.Phonology
public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.SearchCopy
public import Studies.Belth2026

/-!
# Jacobs (2026): Latin liquid dissimilation and the relevance of phonological structure

The Latin suffix -alis surfaces as -aris after a stem [l] unless [r], a dorsal or the glide [w]
intervenes; labials and the other coronals do not block. McMullin's tier for the pattern "cannot
be described as a natural class" ([mcmullin-2016], p. 120). Jacobs puts [lateral] under a LINGUAL
node beside CORONAL and DORSAL, specifies it only on liquids, and leaves CORONAL unspecified, and
then the segments bearing LINGUAL are [exactly the liquids, the dorsals and the
glides](##onLingualTier_iff), a class of the geometry. Dissimilation across that tier [derives
every form the paper accounts for and misses the others](##dissimilate_predicts_iff), where
Steriade's [lateral] tier, McMullin's and Cser's blockers and Belth's consonant tier [each
mispredict a form](##rivals_mispredict). The constraints of (18) [select the rule's
output](##optimal_image_output), and a [j] from a front vowel in hiatus [joins the tier and
reverses the outcome](##dissimilate_glide).

## Implementation notes

* Segments are the Fragment's, with PHOIBLE's values. `underlying` reads Jacobs's representations
  off them (p. 134): [lateral] only on liquids, after Steriade, CORONAL never, and LABIAL and
  DORSAL where present. The tree is Jacobs's statement of the LINGUAL node, which he attributes
  to Clements and Hume (1995: 291); the attribution is his. The tier is that of C-place, so a
  segment on it is [−syllabic]: a vowel in hiatus is off the tier, the glide on it.
* The rule is a `SearchCopy` whose target is the suffix liquid `L`, unspecified for [lateral].
  Jacobs's input has the suffix -alis, which the tableau of (18) takes. Only the suffix liquid
  alternates, as (18c) restricts the ban to the suffix: Latin has stem-internal [l]…[l] (fn. 7).
* A row is compared on the paper's underlying stem, *latj* for *Latialis* and *glajb* for
  *glebalis* (p. 139), with the suffix liquid read off the attested form.
* Steriade's tier is derived like Jacobs's, as the segments specified for [lateral]. McMullin's
  tier (13) and Cser's blockers (Table 2) are listed as their sources list them, and Belth's rule
  is his study's, over its own transcription. Roberts's correspondence account of 2011 is known
  here only from Jacobs's report (pp. 122–129) and is not formalized.
* McMullin's grammar (13) bans adjacent [l]…[l] on the tier over whole words, which also rules out
  his own *stell-ar-is* (p. 118), whose geminate is [l l] on the tier. The rule here changes only
  the suffix liquid, as (18c) restricts the ban to the suffix.
* `dissimilate_glide` applies to every stem whose last LINGUAL segment is [l], so it also predicts
  later -alis forms for *tricliniaris* (1d) and Cser's *Saliaris*, which the paper does not check.

## Errata

* The paper predicts that the -alis forms of the hiatus pairs "did not occur prior to 200AD"
  (p. 138), but its own (23) has *Latialis* [three times before 200 AD](##latialis_before200).
* The variation is said to occur "only … with intervening coronal consonants" and a front vowel in
  hiatus (p. 120), but *fulminalis* and *fulminaris* both occur in the 5th century, with [m] and no
  hiatus (p. 133), and the rule misses *fulminalis*.
* [j] is "specified as [CORONAL] and [DORSAL]" (p. 120), has "a lingual [dorsal] articulation"
  (p. 137), and in (21) is [lingual] over [coronal]. With CORONAL never specified, a [j] of (21)
  [is off the tier](##not_onLingualTier_coronalGlide) and could not block; the account needs
  [DORSAL], as in PHOIBLE.
* (17) is captioned *pluvialis* but spells *fluvialis* (p. 136). The text refers to (15a) as (14a)
  (p. 130), and quotes Cser (2010) at p. 40 for what Cser prints on p. 39.

## TODO

* Cser's further condition, at least three moræ between the stem and the suffix liquid (p. 38),
  needs vowel length, which the Fragment's segments do not carry. *limitaris* is the rival case
  either way: its [m] blocks for Cser, and it has more than three moræ.

## References

* [jacobs-2026]
* [steriade-1987]
* [mcmullin-2016]
* [cser-2010]
* [cser-2020]
* [belth-2026]
* [clements-hume-1995]
-/

@[expose] public section

namespace Jacobs2026

open Phonology Phonology.FeatureGeometry OptimalityTheory

/-! ### The geometry -/

/-- §4: C-place over LABIAL and LINGUAL, and LINGUAL over CORONAL and DORSAL. -/
inductive Node where
  | cPlace
  | labial
  | lingual
  | coronal
  | dorsal
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The node immediately dominating each node, C-place fixed. -/
def pred : Node → Node
  | .cPlace | .labial | .lingual => .cPlace
  | .coronal | .dorsal => .lingual

/-- `a ≤ b` when `a` lies on the walk from `b` up to C-place. -/
instance : PartialOrder Node where
  le a b := a ∈ List.iterate pred b (Fintype.card Node)
  le_refl := by decide
  le_trans := by decide +kernel
  le_antisymm := by decide

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (a ∈ List.iterate pred b _))

end Node

/-- The node each place feature hangs from: [lateral] from LINGUAL, as a sister of CORONAL and
DORSAL. -/
def node : Feature → Option Node
  | .lateral => some .lingual
  | .labial | .round | .labiodental => some .labial
  | .coronal | .anterior | .distributed => some .coronal
  | .dorsal | .high | .low | .front | .back => some .dorsal
  | _ => none

theorem lateral_mem_featureClass_lingual : Feature.lateral ∈ featureClass node .lingual := by
  decide

/-! ### Underlying representations and the tier -/

/-- Jacobs's underlying representation of a segment (§4): [lateral] only on a liquid, CORONAL
never, and LABIAL and DORSAL where present. -/
def underlying (s : Segment) : Segment
  | .lateral => if Sonority.ofSegment s = .liquid then s .lateral else none
  | .labial => if s.HasValue .labial true then some true else none
  | .dorsal => if s.HasValue .dorsal true then some true else none
  | _ => none

/-- A segment bears a node when it specifies a feature of the node's class. -/
def Bears (s : Segment) (a : Node) : Prop := ∃ f ∈ featureClass node a, (s f).isSome

instance (s : Segment) (a : Node) : Decidable (Bears s a) := by unfold Bears; infer_instance

/-- The LINGUAL tier: the C-place segments whose underlying representation bears LINGUAL. -/
def OnLingualTier (s : Segment) : Prop :=
  s.HasValue .syllabic false ∧ Bears (underlying s) .lingual

instance : DecidablePred OnLingualTier := fun s ↦ by unfold OnLingualTier; infer_instance

/-- Steriade's tier: the C-place segments whose underlying representation specifies
[lateral]. -/
def OnLateralTier (s : Segment) : Prop :=
  s.HasValue .syllabic false ∧ (underlying s .lateral).isSome

instance : DecidablePred OnLateralTier := fun s ↦ by unfold OnLateralTier; infer_instance

/-- Against McMullin's "no natural class": of the Latin phonemes, the liquids, the dorsals and the
two glides, and only they, bear LINGUAL. -/
theorem onLingualTier_iff : ∀ x ∈ Latin.inventory, OnLingualTier x ↔
    x ∈ ({Latin.l, Latin.r, Latin.k, Latin.g, Latin.w, Latin.j} : Finset Segment) := by
  decide

theorem onLateralTier_iff : ∀ x ∈ Latin.inventory, OnLateralTier x ↔ x = Latin.l ∨ x = Latin.r := by
  decide

theorem OnLateralTier.onLingualTier {s : Segment} (h : OnLateralTier s) : OnLingualTier s :=
  ⟨h.1, _, lateral_mem_featureClass_lingual, h.2⟩

/-! ### Dissimilation -/

/-- The suffix liquid, unspecified for [lateral]: what /l/ and /r/ share. -/
def L : Segment := Latin.l ⊓ Latin.r

/-- Dissimilation on a tier: the suffix liquid takes the opposite laterality of the closest
segment on the tier before it, and is [l] when that segment has none. -/
def dissimilate (T : Segment → Prop) [DecidablePred T] : SearchCopy Segment where
  tier s := T s ∨ s = L
  IsTarget s := s = L
  IsSource _ _ := True
  relation := .disagree
  value s := underlying s .lateral
  write v _ := if v then Latin.l else Latin.r
  value_write v _ _ := by cases v <;> decide
  write_value v _ hs hv := by subst hs; cases v <;> revert hv <;> decide
  default := some true

/-! ### The forms -/

open Wordlist

/-- A segment from its letter in the transcriptions. -/
def ofChar : Char → Option Segment
  | 'a' => some Latin.a | 'e' => some Latin.e | 'i' => some Latin.i | 'o' => some Latin.o
  | 'u' => some Latin.u | 'p' => some Latin.p | 'b' => some Latin.b | 't' => some Latin.t
  | 'd' => some Latin.d | 'k' => some Latin.k | 'g' => some Latin.g | 'f' => some Latin.f
  | 's' => some Latin.s | 'm' => some Latin.m | 'n' => some Latin.n | 'l' => some Latin.l
  | 'r' => some Latin.r | 'w' => some Latin.w | 'j' => some Latin.j
  | _ => none

/-- The underlying stem of an analysis, its underlying form up to the morpheme boundary. -/
def stem (a : Analysis) : List Segment :=
  ((a.underlying.toList.drop 1).takeWhile (· ≠ '-')).filterMap ofChar

/-- The suffix liquid of the attested form, its third segment from the end. -/
def suffixLiquid (a : Analysis) : List Segment :=
  ((a.form.segments.reverse[2]?).bind fun x ↦ x.toList.head?.bind ofChar).toList

/-- The rule on a tier predicts a form when, run on the stem and the suffix, it leaves the stem
and writes the attested suffix liquid. -/
def Predicts (T : Segment → Prop) [DecidablePred T] (a : Analysis) : Prop :=
  (dissimilate T).apply (stem a ++ [Latin.a, L, Latin.i, Latin.s]) =
    stem a ++ Latin.a :: suffixLiquid a ++ [Latin.i, Latin.s]

instance (T : Segment → Prop) [DecidablePred T] (a : Analysis) : Decidable (Predicts T a) :=
  inferInstanceAs (Decidable (_ = _))

/-- Dissimilation on the LINGUAL tier predicts a form exactly when the paper accounts for it: the
regular forms and the later forms with [j], and none of its exceptions. -/
theorem dissimilate_predicts_iff : ∀ a ∈ analyses,
    Predicts OnLingualTier a ↔ a.status = .regular ∨ a.status = .glide := by
  decide

/-! ### The rivals -/

/-- (13) of [mcmullin-2016]: the liquids, labials and velars, [h] aside. -/
def mcMullinTier : Finset Segment :=
  {Latin.l, Latin.r, Latin.p, Latin.b, Latin.f, Latin.m, Latin.w, Latin.k, Latin.g}

/-- Table 2 of [cser-2010]: the blockers [r] and [m b g k w], with the stem [l]. -/
def cserTier : Finset Segment := {Latin.l, Latin.r, Latin.m, Latin.b, Latin.g, Latin.k, Latin.w}

-- (1), the forms the [lateral] tier was proposed for
theorem predicts_onLateralTier_one : ∀ a ∈ [navalis.analysis, natalis.analysis,
    criminalis.analysis, solaris.analysis, militaris.analysis, lunaris.analysis,
    floralis.analysis, lateralis.analysis, ridicularis.analysis, tricliniaris.analysis],
    Predicts OnLateralTier a := by
  decide

/-- Each rival tier mispredicts a form the LINGUAL tier predicts: the [lateral] tier gives
*legaris*, McMullin's tier and Belth's rule *lupanalis*, and Cser's blockers *limitalis*. -/
theorem rivals_mispredict :
    Predicts OnLingualTier legalis.analysis ∧ ¬ Predicts OnLateralTier legalis.analysis ∧
      Predicts OnLingualTier lupanaris.analysis ∧
      ¬ Predicts (· ∈ mcMullinTier) lupanaris.analysis ∧
      Belth2026.latinDissimRule.apply [.l, .u, .p, .a, .n, .a, .L, .i, .s] =
        [.l, .u, .p, .a, .n, .a, .l, .i, .s] ∧
      Predicts OnLingualTier limitaris.analysis ∧ ¬ Predicts (· ∈ cserTier) limitaris.analysis := by
  decide

/-! ### The glide -/

/-- A glide [j] of (21), [coronal] under [lingual] and no [dorsal]. -/
def coronalGlide : Segment := (Latin.j.setFeature .dorsal false).setFeature .coronal true

theorem not_onLingualTier_coronalGlide : ¬ OnLingualTier coronalGlide := by
  decide

/-! ### The run on a stem without the suffix liquid -/

section Run

variable {T : Segment → Prop} [DecidablePred T]

private theorem emit_of_ne {x : Segment} (hx : x ≠ L) (w : Option Segment) :
    (dissimilate T).emit w x = x :=
  (dissimilate T).emit_of_not_isTarget hx w

private theorem runFrom_of_notMem (w : Option Segment) {xs : List Segment} (h : L ∉ xs) :
    (dissimilate T).toMealy.runFrom w xs = xs := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mem_cons, not_or] at h
    rw [Mealy.runFrom_cons, SearchCopy.toMealy_output, emit_of_ne (Ne.symm h.1), ih _ h.2]

private theorem evalFrom_of_notMem (w : Option Segment) {xs : List Segment} (h : L ∉ xs) :
    (dissimilate T).toMealy.evalFrom w xs = (xs.filter fun x ↦ T x).getLast?.or w := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [List.mem_append, List.mem_singleton, not_or] at h
    rw [Mealy.evalFrom_append, ih h.1, List.filter_append, Mealy.evalFrom_cons,
      Mealy.evalFrom_nil, SearchCopy.toMealy_step]
    by_cases hx : T x
    · have ht : (dissimilate T).tier x := Or.inl hx
      simp only [ht, ↓reduceIte, emit_of_ne (Ne.symm h.2)]
      simp [hx]
    · have ht : ¬ (dissimilate T).tier x := fun h' ↦ h'.elim hx fun e ↦ h.2 e.symm
      simp only [ht, ↓reduceIte]
      simp [hx]

private theorem apply_append {xs : List Segment} (h : L ∉ xs) (ys : List Segment) :
    (dissimilate T).apply (xs ++ ys) =
      xs ++ (dissimilate T).toMealy.runFrom (xs.filter fun x ↦ T x).getLast? ys := by
  rw [(dissimilate T).apply_eq_scan rfl, SearchCopy.scan_eq_runFrom, Mealy.runFrom_append,
    runFrom_of_notMem _ h, evalFrom_of_notMem _ h, Option.or_none]

end Run

/-- A [j] formed from a front vowel in hiatus reverses the outcome: after a stem whose last
LINGUAL segment is [l], the suffix is -aris with the vowel and -alis with the glide. -/
theorem dissimilate_glide {pre : List Segment} (hL : L ∉ pre)
    (hl : (pre.filter fun x ↦ OnLingualTier x).getLast? = some Latin.l) {v : Segment}
    (hv : v = Latin.i ∨ v = Latin.e) :
    (dissimilate OnLingualTier).apply (pre ++ [v, Latin.a, L, Latin.i, Latin.s]) =
        pre ++ [v, Latin.a, Latin.r, Latin.i, Latin.s] ∧
      (dissimilate OnLingualTier).apply (pre ++ [Latin.j, Latin.a, L, Latin.i, Latin.s]) =
        pre ++ [Latin.j, Latin.a, Latin.l, Latin.i, Latin.s] := by
  rw [apply_append hL, apply_append hL, hl]
  refine ⟨congrArg _ ?_, congrArg _ ?_⟩
  · rcases hv with rfl | rfl <;> decide
  · decide

-- (23)
theorem latialis_before200 : (table23 .before200).latialis = 3 := rfl

/-! ### The constraints of (18) -/

/-- A candidate for a stem of `n` segments: whether each stem liquid changes its [lateral] value,
and the [lateral] value of the suffix liquid. -/
abbrev Candidate (n : ℕ) := (Fin n → Bool) × Bool

/-- A liquid with its [lateral] value reversed; other segments unchanged. -/
def swap (x : Segment) : Segment :=
  if x = Latin.l then Latin.r else if x = Latin.r then Latin.l else x

variable (base : List Segment)

/-- The stem a candidate outputs. -/
def outStem (c : Candidate base.length) : List Segment :=
  List.ofFn fun i ↦ if c.1 i then swap base[i] else base[i]

/-- The output of a candidate, its stem and the suffix. -/
def output (c : Candidate base.length) : List Segment :=
  outStem base c ++ [Latin.a, if c.2 then Latin.l else Latin.r, Latin.i, Latin.s]

/-- The [lateral] value of the last LINGUAL segment of a string. -/
def lastLateral (w : List Segment) : Option Bool :=
  (w.filter fun x ↦ OnLingualTier x).getLast?.bind (underlying · .lateral)

/-- (18c): the suffix liquid and the closest LINGUAL segment before it are both [+lateral]. -/
def ocp (c : Candidate base.length) : ℕ :=
  if c.2 = true ∧ lastLateral (outStem base c) = some true then 1 else 0

/-- (18a): the stem liquids whose [lateral] value changes. -/
def identBase (c : Candidate base.length) : ℕ :=
  (Finset.univ.filter fun i ↦ c.1 i = true ∧ swap base[i] ≠ base[i]).card

/-- (18b): the suffix liquid changes from the [+lateral] of the input -alis. -/
def identSuffix (c : Candidate base.length) : ℕ := if c.2 then 0 else 1

/-- The tableau of (19) and (20) for a stem: *LINGUAL[+LAT]–LINGUAL[+LAT] ≫ IDENT-IO-[LAT]/BASE ≫
IDENT-IO-[LAT]/SUFFIX over every candidate. -/
def tableau : Tableau (Candidate base.length) 3 :=
  .ofList Finset.univ [ocp base, identBase base, identSuffix base]

variable {base}

private theorem outStem_eq_self {c : Candidate base.length} (h : identBase base c = 0) :
    outStem base c = base := by
  refine List.ext_getElem (by simp [outStem]) fun i h₁ h₂ ↦ ?_
  simp only [outStem, List.getElem_ofFn]
  split_ifs with hc
  · by_contra hne
    refine Finset.card_ne_zero_of_mem (a := ⟨i, h₂⟩) ?_ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hne⟩
  · rfl

private theorem runFrom_suffix (st : Option Segment) :
    (dissimilate OnLingualTier).toMealy.runFrom st [Latin.a, L, Latin.i, Latin.s] =
      [Latin.a, if st.bind (underlying · .lateral) = some true then Latin.r else Latin.l, Latin.i,
        Latin.s] := by
  have hta : ¬ (dissimilate OnLingualTier).tier Latin.a := by decide
  simp only [Mealy.runFrom_cons, Mealy.runFrom_nil, SearchCopy.toMealy_output,
    SearchCopy.toMealy_step, emit_of_ne (by decide : Latin.a ≠ L),
    emit_of_ne (by decide : Latin.i ≠ L), emit_of_ne (by decide : Latin.s ≠ L), hta,
    ↓reduceIte]
  simp only [SearchCopy.emit, SearchCopy.copied, SearchCopy.found, dissimilate, ↓reduceIte]
  generalize st.bind (underlying · .lateral) = o
  rcases o with _ | _ | _ <;> rfl

/-- The ranking of (18) selects the output of dissimilation on the LINGUAL tier, for every stem. -/
theorem optimal_image_output (hL : L ∉ base) :
    (tableau base).optimal.image (output base) =
      {(dissimilate OnLingualTier).apply (base ++ [Latin.a, L, Latin.i, Latin.s])} := by
  set b := decide (lastLateral base ≠ some true) with hb
  let d : Candidate base.length := (fun _ ↦ false, b)
  have hd0 : identBase base d = 0 := by simp [identBase, d]
  have hocp (c : Candidate base.length) (hc : identBase base c = 0) :
      ocp base c = 0 ↔ ¬ (c.2 = true ∧ lastLateral base = some true) := by
    simp only [ocp, outStem_eq_self hc]
    split_ifs with h <;> simp [h]
  have hdocp : ocp base d = 0 := (hocp d hd0).2 (by simp [d, hb])
  have h1 : Finset.univ.argmin (ocp base) = Finset.univ.filter (ocp base · = 0) := by
    ext c
    simp only [Finset.mem_argmin, Finset.mem_univ, true_and, Finset.mem_filter, true_implies]
    exact ⟨fun h ↦ Nat.le_zero.1 (hdocp ▸ h d), fun h e ↦ h ▸ Nat.zero_le _⟩
  have h2 : (Finset.univ.filter (ocp base · = 0)).argmin (identBase base) =
      Finset.univ.filter fun c ↦ ocp base c = 0 ∧ identBase base c = 0 := by
    ext c
    simp only [Finset.mem_argmin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h, hmin⟩ ↦ ⟨h, Nat.le_zero.1 (hd0 ▸ hmin d hdocp)⟩,
      fun ⟨h, h0⟩ ↦ ⟨h, fun _ _ ↦ h0 ▸ Nat.zero_le _⟩⟩
  have hS (c : Candidate base.length) :
      c ∈ (Finset.univ.filter fun c ↦ ocp base c = 0 ∧ identBase base c = 0).argmin
        (identSuffix base) ↔ identBase base c = 0 ∧ c.2 = b := by
    simp only [Finset.mem_argmin, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hl : lastLateral base = some true
    · have hb' : b = false := by simp [hb, hl]
      constructor
      · rintro ⟨⟨hc, hc0⟩, -⟩
        exact ⟨hc0, by simpa [hb', hl] using (hocp c hc0).1 hc⟩
      · rintro ⟨hc0, hcb⟩
        refine ⟨⟨(hocp c hc0).2 (by simp [hcb, hb']), hc0⟩, fun e ⟨he, he0⟩ ↦ ?_⟩
        have he2 : e.2 = false := by simpa [hl] using (hocp e he0).1 he
        simp [identSuffix, hcb, hb', he2]
    · have hb' : b = true := by simp [hb, hl]
      constructor
      · rintro ⟨⟨-, hc0⟩, hmin⟩
        refine ⟨hc0, ?_⟩
        have := hmin d ⟨hdocp, hd0⟩
        simp only [identSuffix, d, hb', ↓reduceIte, Nat.le_zero] at this
        rw [hb']
        cases h : c.2 <;> simp_all
      · rintro ⟨hc0, hcb⟩
        refine ⟨⟨(hocp c hc0).2 (by simp [hl]), hc0⟩, fun _ _ ↦ ?_⟩
        simp [identSuffix, hcb, hb']
  rw [tableau, Tableau.optimal_ofList_cons, Tableau.optimal_ofList_cons,
    Tableau.optimal_ofList_cons, Tableau.optimal_ofList_nil, h1, h2, apply_append hL,
    runFrom_suffix]
  have hout (c : Candidate base.length) (hc : identBase base c = 0 ∧ c.2 = b) :
      output base c = base ++ [Latin.a, if lastLateral base = some true then Latin.r else Latin.l,
        Latin.i, Latin.s] := by
    rw [output, outStem_eq_self hc.1, hc.2, hb]
    by_cases hl : lastLateral base = some true <;> simp [hl]
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_image.2 ⟨d, (hS d).2 ⟨hd0, rfl⟩,
    hout d ⟨hd0, rfl⟩⟩, fun y hy ↦ ?_⟩
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
  exact hout c ((hS c).1 hc)

end Jacobs2026
