module

public import Linglib.Semantics.Root.Defs
public import Linglib.Semantics.ArgumentStructure.SalienceClass
public import Linglib.Morphology.Exponence.Select
public import Linglib.Data.Wordlist.Lucy1994

/-!
# Lucy (1994): The Role of Semantic Value in Lexical Comparison

This file formalizes the morpho-distributional diagnostic of Lucy: the lexical classes
of a language are to be identified by their morphology rather than by notional content, and
the notional class of motion verbs, assembled from English intuition, coincides with no
morphologically defined class of Yucatec. The diagnostic is the derivation a root requires to
form a transitive stem, the affective suffix *=t* for agent-salient roots, no derivation for
agent-patient-salient roots, and the causative suffix *=s* for patient-salient roots
(`affectiveT`, `zeroDeriv`, `causativeS`), salience being a set of default semantic values in
a root that influence case marking. Roots are encoded by their entailment signature and their
valency after Beavers and Koontz-Garboden and after Coon, the classifier is the substrate's
`ArgumentStructure.SalienceClass.ofKinds`, and the derivations predicted from the encoding
reproduce every derivation the paper attests (`predicted_matches_attested`), the attestations
being the form relations of `Data/Wordlist/Lucy1994`. Notional motion roots land in the
patient-salient class, each classified as *kíim* 'die' is (`motion_roots_not_separate_class`);
at best the roots lacking the *-Vl* imperfective form a formal class of motion verbs, a
distinction invisible to the entailment grid (`hash_not_signature_definable`). Positional
roots, which take the positional derivation *=lah*, cross-cut the transitiviser classes, *čin*
'bend' also zero-deriving a transitive (`positional_crosscuts_transitiviser_classes`), and each
class's derivation adds the complement of its underived stem's valency
(`transitiviser_adds_compl`).

## Implementation notes

The agent-patient class is carried by valency rather than by a signature, since its roots
share none: *p'is* 'measure' is manner-only and *k'os* 'cut' manner and result. The affective
class is inflated by denominal and loanword verbalization, so *=t* is a weaker signal of manner
entailments than the other two derivations are of theirs. Root spellings are the paper's, read
from the form rows; the class sizes and the two-way split of intransitives the paper aligns
with the unaccusativity tradition are described in prose.

## References

* [lucy-1994]
* [beavers-koontz-garboden-2020]
* [coon-2019]
-/

@[expose] public section

namespace Lucy1994

open ArgumentStructure Morphology CLDF.Wordlist

/-- A sampled root, the meaning of a root with the form row that spells it. -/
structure SampledRoot extends Root where
  /-- The form row that spells the root. -/
  form : Form Wordlist.Cell
  deriving DecidableEq

/-- The root of the sample that a form spells, with its kind signature. -/
def ofForm (f : Form Wordlist.Cell) (kinds : Root.Kinds) : SampledRoot := { form := f, kinds }

/-! ### Agent-salient roots ((1a), p. 629) -/

/-- síit' 'jump' (1a). -/
def siit : SampledRoot := ofForm Wordlist.siit {.manner}

/-- ¢'iib' 'write' (p. 629). -/
def tziib : SampledRoot := ofForm Wordlist.tziib {.manner}

/-- mìis 'sweep' (p. 629), denominal from 'broom'. -/
def miis : SampledRoot := ofForm Wordlist.miis {.manner}

/-- čé'eh 'smile' (p. 629). -/
def cheh : SampledRoot := ofForm Wordlist.cheh {.manner}

/-- páak 'weed' (p. 629). -/
def paak : SampledRoot := ofForm Wordlist.paak {.manner}

/-! ### Agent-patient-salient roots ((1b), p. 629)

Root transitives, carrying no uniform signature: *kuč*, *p'is*, *ha¢* and *loš* are manner-only,
surface contact without an entailed result, while *k'os* 'cut' is manner and result. -/

/-- kuč 'carry' (1b). -/
def kuc : SampledRoot := ofForm Wordlist.kuc {.manner}

/-- k'os 'cut' (p. 629), manner and result. -/
def kos : SampledRoot := ofForm Wordlist.kos {.manner, .result}

/-- p'is 'measure' (p. 629), no entailed change of state. -/
def pis : SampledRoot := ofForm Wordlist.pis {.manner}

/-- ha¢ 'whip' (p. 629). -/
def hats : SampledRoot := ofForm Wordlist.hats {.manner}

/-- loš 'punch' (p. 629), surface contact without an entailed result. -/
def los : SampledRoot := ofForm Wordlist.los {.manner}

/-! ### Patient-salient roots ((2), pp. 629–630)

List (2) is arranged in antonym pairs listed in vertical adjacency: 'ah ~ wen, siih ~ kíim,
tú'ub' ~ k'a'ah, ču'un ~ č'en, hó'op' ~ háaw. The order below is the list's. -/

/-- 'ah '(a)wake(n)', 'ah=s 'wake (someone)'. -/
def ah : SampledRoot := ofForm Wordlist.ah {.result}

/-- wen '(fall a)sleep', ween=s 'put to sleep'; fn. 7 flags it as also denoting continuation in
the state. -/
def wen : SampledRoot := ofForm Wordlist.wen {.result}

/-- siih 'be born', siih=s 'give birth, bear'. -/
def siih : SampledRoot := ofForm Wordlist.siih {.result}

/-- kíim 'die' (1c), kíim=s 'kill'. -/
def kiim : SampledRoot := ofForm Wordlist.kiim {.result}

/-- tú'ub' 'forget', tú'ub'=s 'distract, cause to forget'. -/
def tuub : SampledRoot := ofForm Wordlist.tuub {.result}

/-- k'a'ah 'remember', k'á'ah=s 'remind, mention, invoke'. -/
def kaah : SampledRoot := ofForm Wordlist.kaah {.result}

/-- ču'un 'begin activity', ču'un=s 'cause to begin'. -/
def chuun : SampledRoot := ofForm Wordlist.chuun {.result}

/-- č'en 'stop, cease', č'en=s 'cause to stop, suspend'. -/
def chen : SampledRoot := ofForm Wordlist.chen {.result}

/-- hó'op' 'begin, start', hó'op'=s 'cause to begin'. -/
def hoop : SampledRoot := ofForm Wordlist.hoop {.result}

/-- háaw 'stop, cease, heal', háaw=s 'stop, revoke, medicate'. -/
def haaw : SampledRoot := ofForm Wordlist.haaw {.result}

/-- hé'el 'rest, stop at', hé'e(l)=s 'rest'. -/
def heel : SampledRoot := ofForm Wordlist.heel {.result}

/-- p'át 'remain', p'át=s 'abandon'. -/
def paat : SampledRoot := ofForm Wordlist.paat {.result}

/-! ### Motion roots ((4), p. 640)

Locational-spatial state-change predicates: notionally motion, formally plain members of the
patient-salient class. The five roots marked `#` do not, and cannot, take the *-Vl* suffix in
the imperfective; fn. 17 adds that *péek* and *'ú'ul* are also irregular in their agent-focused
perfective forms, where they pattern like agent-salient roots. -/

/-- máan 'pass by' (`#`), maan=s 'pass, transfer, transport'. -/
def maan : SampledRoot := ofForm Wordlist.maan {.result}

/-- péek 'move, vibrate' (`#`), pek=s 'cause to move, vibrate'. -/
def peek : SampledRoot := ofForm Wordlist.peek {.result}

/-- b'in 'go' (`#`), bi(n)=s 'take'. -/
def bin : SampledRoot := ofForm Wordlist.bin {.result}

/-- tàal 'come (here)' (`#`), taa(l)=s 'bring'. -/
def taal : SampledRoot := ofForm Wordlist.taal {.result}

/-- 'ú'ul 'arrive (here)' (`#`), 'u'uh=s 'bring it to here'. -/
def uul : SampledRoot := ofForm Wordlist.uul {.result}

/-- 'ok 'enter, intrude', 'ook=s 'move it in(to)'. -/
def ok : SampledRoot := ofForm Wordlist.ok {.result}

/-- lúub' 'fall', luub'=s 'fell'. -/
def luub : SampledRoot := ofForm Wordlist.luub {.result}

/-- líik' '(a)rise, ascend', lii(k)'=s 'raise, lift, put away'. -/
def liik : SampledRoot := ofForm Wordlist.liik {.result}

/-- ná'ak '(a)rise, ascend', na'ak=s 'raise'; distinct from náak 'arrive, reach, hit', not
sampled here. -/
def naak : SampledRoot := ofForm Wordlist.naak {.result}

/-! ### Positional roots ((5) to (7), pp. 642–644) -/

/-- čin 'bow, bend down, bend over' ((5) to (7)); zero-derives a transitive, (6) 'I bent it'. -/
def cin : SampledRoot := ofForm Wordlist.cin {.state}

/-- čil 'lie down, lying down' (7). -/
def cil : SampledRoot := ofForm Wordlist.cil {.state}

/-! ### Valency and class lists -/

/-- The roots attested forming a transitive stem by zero derivation, the sampled `=∅` predicate
roots (p. 629) and the positional *čin* (6). -/
def rootTransitives : List SampledRoot := [kuc, kos, pis, hats, los, cin]

/-- Root valency for the sample, [coon-2019]'s √TV as `{.internal}`: zero-derivers introduce
their internal argument, every other sampled root none. -/
def valency (r : SampledRoot) : Valency :=
  if r ∈ rootTransitives then {.internal} else ∅

/-- The sampled agent-salient roots. -/
def agentSalientRoots : List SampledRoot := [siit, tziib, miis, cheh, paak]

/-- The sampled agent-patient-salient roots. -/
def agentPatientSalientRoots : List SampledRoot := [kuc, kos, pis, hats, los]

/-- The sampled patient-salient roots of list (2), in the list's order. -/
def patientSalientRoots : List SampledRoot :=
  [ah, wen, siih, kiim, tuub, kaah, chuun, chen, hoop, haaw, heel, paat]

/-- The sampled motion roots of (4). -/
def motionRoots : List SampledRoot :=
  [maan, peek, bin, taal, uul, ok, luub, liik, naak]

/-- The `#`-marked subset of (4), the roots lacking the *-Vl* imperfective: for the paper, the
only candidate formal class of motion verbs (p. 641). -/
def hashMarked : List SampledRoot := [maan, peek, bin, taal, uul]

/-- The sampled positional roots. -/
def positionalRoots : List SampledRoot := [cin, cil]

/-- Every sampled root. -/
def sampledRoots : List SampledRoot :=
  agentSalientRoots ++ agentPatientSalientRoots ++ patientSalientRoots ++
    motionRoots ++ positionalRoots

/-! ### Diagnostic operators -/

/-- A diagnostic derivational operator is given by its exponent, the core-argument positions it
adds, and its structural applicability condition with bundled decidability, since the inventory
holds heterogeneous conditions. Selection comes from the `Morphology.Exponence.Rule` instance. -/
structure DiagOp where
  /-- The suffix, in the paper's orthography. -/
  exponent : String
  /-- The core-argument positions the derivation adds (`transitiviser_adds_compl`). -/
  adds : Valency
  /-- The structural condition on the root. -/
  Applies : SampledRoot → Prop
  /-- Bundled decidability of the condition. -/
  decApplies : DecidablePred Applies

instance : Exponence.Rule DiagOp SampledRoot String where
  exponent := DiagOp.exponent
  Applies := DiagOp.Applies

instance : DecidableRel (Exponence.Applies : DiagOp → SampledRoot → Prop) :=
  fun op r ↦ op.decApplies r

@[simp] theorem applies_iff (op : DiagOp) (r : SampledRoot) :
    Exponence.Applies op r ↔ op.Applies r := Iff.rfl

/-- Affective *=t* transitivises an agent-salient root by adding a patient argument. -/
def affectiveT : DiagOp :=
  ⟨"=t", {.internal}, fun r ↦ IsAgentSalient r.kinds (valency r), inferInstance⟩

/-- Under zero derivation *=∅* the root alone supports a transitive stem. -/
def zeroDeriv : DiagOp :=
  ⟨"=∅", ∅, fun r ↦ .internal ∈ valency r, inferInstance⟩

/-- Causative *=s* transitivises a patient-salient root by adding an agent argument. -/
def causativeS : DiagOp :=
  ⟨"=s", {.external}, fun r ↦ IsPatientSalient r.kinds (valency r), inferInstance⟩

/-- The positional derivation, realized *=lah* ~ *=tal* by status, the *=tal* incompletive
apparently compounding with *tàal* 'come' (p. 643). -/
def positionalLah : DiagOp :=
  ⟨"=lah", ∅, fun r ↦ IsPositional r.kinds, inferInstance⟩

/-- The diagnostic inventory in the paper's order, the three transitivisers of (1) and then the
positional derivation. -/
def inventory : Exponence.RuleSet DiagOp :=
  [affectiveT, zeroDeriv, causativeS, positionalLah]

/-- The exponents of the inventory's applicable operators at `r`, in inventory order, which are
the root's predicted derivational behaviour. -/
def predictedExponents (r : SampledRoot) : List String :=
  (inventory.applicable r).map DiagOp.exponent

/-! ### Predicted against attested derivations -/

/-- The derivations the paper attests for a root. Each is the final segment of a form that the
root's row is related to, a derived stem or the bare derivational morpheme. -/
def attested (r : SampledRoot) : List String :=
  (Wordlist.relations.filter (·.form.form == r.form.form)).filterMap (·.target.segments.getLast?)

/-- The derivations predicted from signature and valency reproduce every derivation the paper
attests. -/
theorem predicted_matches_attested : ∀ r ∈ sampledRoots, predictedExponents r = attested r := by
  decide

/-! ### The derived classification -/

/-- A root's predicted salience class. -/
def predictedClass (r : SampledRoot) : Option SalienceClass :=
  SalienceClass.ofKinds r.kinds (valency r)

/-- The transitiviser each salience class requires. -/
def exponentOf : SalienceClass → String
  | .agent => "=t"
  | .agentPatient => "=∅"
  | .patient => "=s"

theorem predictedExponents_eq (r : SampledRoot) :
    predictedExponents r =
      (predictedClass r).toList.map exponentOf ++
        (if IsPositional r.kinds then ["=lah"] else []) := by
  simp only [predictedExponents, predictedClass, Exponence.RuleSet.applicable,
    applies_iff, inventory, affectiveT, zeroDeriv, causativeS,
    positionalLah, List.filter_cons, List.filter_nil, decide_eq_true_eq,
    SalienceClass.ofKinds]
  generalize r.kinds = s
  generalize valency r = v
  revert s v
  decide

theorem agentSalient_class :
    ∀ r ∈ agentSalientRoots, predictedClass r = some .agent := by decide

theorem agentPatientSalient_class :
    ∀ r ∈ agentPatientSalientRoots, predictedClass r = some .agentPatient := by decide

theorem patientSalient_class :
    ∀ r ∈ patientSalientRoots, predictedClass r = some .patient := by decide

theorem rootTransitives_not_signature_uniform :
    ∃ r ∈ agentPatientSalientRoots, ∃ r' ∈ agentPatientSalientRoots, r.kinds ≠ r'.kinds := by
  decide

/-! ### The motion-verb non-class -/

/-- Notional motion roots form no salience class of their own, the paper's central typological
point: each is classified exactly as the plain state-change root *kíim* 'die'. -/
theorem motion_roots_not_separate_class :
    ∀ r ∈ motionRoots, predictedClass r = predictedClass kiim := by decide

/-- The `#` subclass, the paper's only candidate formal motion class, is not a function of the
entailment grid: *péek* (`#`) and *lúub'* (plain) agree in signature and valency. The class is
carried by a morphological gap, not by lexical semantics. -/
theorem hash_not_signature_definable :
    ∃ r ∈ hashMarked, ∃ r' ∈ motionRoots,
      r' ∉ hashMarked ∧ r.kinds = r'.kinds ∧ valency r = valency r' := by
  decide

/-- The transitiviser system is complementation in the valency lattice: each class's required
derivation adds the Boolean complement of its underived stem's valency, *=t* the patient the
agent stem lacks, *=s* the agent the patient stem lacks, *=∅* nothing. -/
theorem transitiviser_adds_compl :
    affectiveT.adds = (SalienceClass.stemValency .agent)ᶜ ∧
    zeroDeriv.adds = (SalienceClass.stemValency .agentPatient)ᶜ ∧
    causativeS.adds = (SalienceClass.stemValency .patient)ᶜ := by decide

/-! ### Positional interstitiality -/

/-- The positional diagnostic cross-cuts the transitiviser cut: *čin* is positional yet
zero-derives a transitive, while *čil* is positional and outside the cut altogether. The
paper's classes are diagnostics, not a partition. -/
theorem positional_crosscuts_transitiviser_classes :
    IsPositional cin.kinds ∧ predictedClass cin = some .agentPatient ∧
    IsPositional cil.kinds ∧ predictedClass cil = none := by decide

/-! ### Closure robustness -/

theorem predictedClass_closure_invariant (r : SampledRoot) (h : Root.Kind.cause ∉ r.kinds) :
    SalienceClass.ofKinds r.closedKinds (valency r) = predictedClass r :=
  SalienceClass.ofKinds_close r.kinds (valency r) h

end Lucy1994
