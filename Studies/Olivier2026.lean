module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Olivier (2026): Agree in Restructuring

This file formalizes the account of auxiliary switch in [olivier-2026]. Auxiliary switch,
BE in place of HAVE on a modal in a compound tense whose infinitive is
unaccusative or reflexive — is ordinary auxiliary selection across a transparent
restructuring domain. Auxiliary selection itself is not driven by argument structure: a
person value carries the referential identity of its bearer, Voice's valued φ-set is
redistributed by head splitting onto `vAux[uPers]` and `VoicePrt[uGen, uNum]`, and the
Vocabulary Items insert BE when `[vAux + T]` carry the same identity, HAVE elsewhere — so
unaccusatives and bound reflexives take BE and transitives HAVE. In a
restructuring clause the auxiliary belongs to the modal, and whether Voice(*) KEEPs its
φ-features or SHAREs them with vMOD decides clitic climbing and the switch at once:
KEEP leaves vAux featureless, HAVE; SHARE brings the bound reflexive's identity — the
subject's — to vAux, BE. Prepositional clitics (*y/ci*, *en/ne*, *lui/gli*)
climb without a switch since they introduce no coreferential person value, and a vAux that
also probes the internal argument gives the Italian and Sardinian speakers' BE. Out of
scope: conditions 1–2, which the restructuring structure presupposes; gender and number on
the participle; impersonal *si*; the corpus counts. The simple compound tense is `compound`
and the restructuring one `Restructuring.matrixAux`.

## References

* [olivier-2026]
* [olivier-2025b] — person-identity auxiliary selection (§6.2)
* [ouali-2008] — the KEEP and SHARE transfers
-/

@[expose] public section

namespace Olivier2026

open ArgumentStructure (TransitivityClass)
open Verb (PerfectAuxiliary)

/-! ### Person values with identity -/

/-- `[Person: X [ID: α]]` (54): a person value with the referential index of its bearer;
two values match for the Vocabulary Items (55) when their indices agree. -/
structure IndexedPerson where
  person : Person
  id : ℕ
  deriving DecidableEq, Repr

/-- The clitics the paper distinguishes: the reflexive *se/si*, bound by the external
argument through Voice* and so sharing its identity (54b), (60); the accusative *le/lo*
and dative *lui/gli*, with identities of their own; the locative *y/ci* and partitive
*en/ne*, which value a P-feature and carry no coreferential person (§7.3); and (65)'s
*je ne m'aurais pas foutu dehors*, a reflexive whose identity is not its binder's
(§6.2.3). -/
inductive Clitic
  | reflexive | detachedReflexive | accusative | dative | locative | partitive
  deriving DecidableEq, Repr, Fintype

/-- The "prepositional" clitics of §3.2.2 — locative, partitive and non-reflexive dative —
which pronominalise PP-constituents and never introduce the subject's identity. -/
def Clitic.prepositional : Clitic → Bool
  | .locative | .partitive | .dative => true
  | _ => false

/-- A clause by the class of its verb and its clitic, if any. -/
structure Clause where
  verb : TransitivityClass
  clitic : Option Clitic := none
  deriving DecidableEq, Repr

/-- The external argument's value carries index `0`, the internal argument's `1`, and any
other bearer's — a cognate object (fn. 26), a detached reflexive — `2`. -/
def externalArg (ea : Person) : IndexedPerson := ⟨ea, 0⟩

/-- The internal argument's value. -/
def internalArg (ia : Person) : IndexedPerson := ⟨ia, 1⟩

/-- The person/identity Voice(*) comes to bear after probing (58)–(61): the internal
argument's for unaccusatives and transitives (a DP or an accusative clitic), the bound
reflexive's — the external argument's identity — for reflexive verbs (60), the identity
of its own for a detached reflexive (65), and a default value for the cognate object of
unergatives (fn. 26). -/
def voicePerson (ea ia : Person) : Clause → IndexedPerson
  | ⟨.unaccusative, _⟩ | ⟨.transitive, _⟩ => internalArg ia
  | ⟨.reflexive, some .detachedReflexive⟩ => ⟨ea, 2⟩
  | ⟨.reflexive, _⟩ => externalArg ea
  | ⟨.unergative, _⟩ => ⟨.third, 2⟩

/-- T's person/identity: the external argument's, or the raised internal argument's for
unaccusatives (59). -/
def tPerson (ea ia : Person) : TransitivityClass → IndexedPerson
  | .unaccusative => internalArg ia
  | _ => externalArg ea

/-- Vocabulary Items (55): BE when `vAux` and `T` carry the same identity, HAVE elsewhere —
HAVE is the default auxiliary. -/
def insert (vAux : Option IndexedPerson) (t : IndexedPerson) : PerfectAuxiliary :=
  if vAux.map (·.id) = some t.id then .be else .have

/-! ### Simple compound tenses (§6.2.2) -/

/-- The auxiliary of a simple compound tense (58): Voice splits, so vAux carries Voice's
person/identity, and T carries the subject's. -/
def compound (ea ia : Person) (cl : Clause) : PerfectAuxiliary :=
  insert (some (voicePerson ea ia cl)) (tPerson ea ia cl.verb)

/-- (59)–(61): identity matching yields the canonical distribution — BE with unaccusatives
and reflexives, HAVE with transitives and unergatives — for every pair of persons. -/
theorem compound_eq_canonical (ea ia : Person) (c : TransitivityClass) :
    compound ea ia ⟨c, none⟩ = c.canonicalSelection := by
  revert ea ia c; decide

/-- (52): *Jean s'est regardé* against *Jean l'a regardé* — the same third-person value,
identities matching only under binding. -/
example : compound .third .third ⟨.reflexive, some .reflexive⟩ = .be ∧
    compound .third .third ⟨.transitive, some .accusative⟩ = .have := by decide

/-- (65): a reflexive whose identity is not its binder's takes HAVE. -/
example : compound .first .first ⟨.reflexive, some .detachedReflexive⟩ = .have := by decide

/-! ### Restructuring clauses (§5, §7) -/

/-- The transfer of Voice(*)'s φ-features to vMOD (45), after [ouali-2008]: KEEP leaves them on
Voice(*), SHARE puts them on vMOD as well. Ouali's third operation, DONATE, plays no role in
the paper. -/
inductive TransferStyle where
  | keep
  | share
  deriving DecidableEq, Repr

/-- A modal in a compound tense over an infinitive (40): the embedded clause, whether
Voice(*) KEEPs its φ-features or SHAREs them with vMOD (45), and whether a vAux that
receives a prepositional clitic's P-feature also receives the internal argument's person
(§7.3's "rich" vAux). -/
structure Restructuring where
  embedded : Clause
  transfer : TransferStyle
  richAux : Bool := true
  deriving DecidableEq, Repr

/-- A clitic climbs iff its φ-features are shared upwards — it spells out on the head that
bears them (45), clitic reduplication showing the copies (41)–(44). -/
def Restructuring.climbs (r : Restructuring) : Prop :=
  r.embedded.clitic.isSome ∧ r.transfer = .share

instance (r : Restructuring) : Decidable r.climbs := inferInstanceAs (Decidable (_ ∧ _))

/-- The person/identity vAux receives after splitting vMOD: nothing under KEEP (69), (74);
under SHARE, Voice's — unless a prepositional clitic climbed to a "poor" vAux, which then
carries only its P-feature (§7.3). -/
def Restructuring.vAuxPerson (ea ia : Person) (r : Restructuring) : Option IndexedPerson :=
  match r.transfer with
  | .share =>
    if (r.embedded.clitic.map Clitic.prepositional).getD false ∧ !r.richAux then none
    else some (voicePerson ea ia r.embedded)
  | .keep => none

/-- The modal's auxiliary. -/
def Restructuring.matrixAux (ea ia : Person) (r : Restructuring) : PerfectAuxiliary :=
  insert (r.vAuxPerson ea ia) (tPerson ea ia r.embedded.verb)

/-- Auxiliary Switch: the modal surfaces with BE. -/
def Restructuring.Switch (ea ia : Person) (r : Restructuring) : Prop :=
  r.matrixAux ea ia = .be

instance (ea ia : Person) (r : Restructuring) : Decidable (r.Switch ea ia) :=
  inferInstanceAs (Decidable (_ = _))

/-- (69), (74): under KEEP vAux is featureless, so the modal takes HAVE and no clitic
climbs. -/
theorem keep_have (ea ia : Person) (r : Restructuring) (h : r.transfer = .keep) :
    r.matrixAux ea ia = .have ∧ ¬ r.climbs := by
  refine ⟨?_, fun hc ↦ TransferStyle.noConfusion (h.symm.trans hc.2)⟩
  simp [Restructuring.matrixAux, Restructuring.vAuxPerson, h, insert]

/-- Under SHARE with no prepositional clitic, the modal switches to BE iff the infinitive selects BE
(Condition 3; (71), (76) versus (61)). -/
theorem share_switch_iff_selectsBe (ea ia : Person) (c : TransitivityClass)
    (cl : Option Clitic) (hcl : cl ≠ some .detachedReflexive)
    (hp : (cl.map Clitic.prepositional).getD false = false) (rich : Bool) :
    Restructuring.Switch ea ia ⟨⟨c, cl⟩, .share, rich⟩ ↔ c.SelectsBe := by
  rcases cl with _ | cl
  · revert ea ia c rich; decide
  · cases cl <;> first | exact absurd rfl hcl | (revert ea ia c rich; decide) | cases hp

/-- With a reflexive infinitive, auxiliary switch obtains iff the reflexive clitic climbs
((19b)/(20a) against (19a)/(20b); Condition α, Table 1). -/
theorem reflexive_switch_iff_climbs (ea ia : Person) (t : TransferStyle) (rich : Bool) :
    Restructuring.Switch ea ia ⟨⟨.reflexive, some .reflexive⟩, t, rich⟩ ↔
      Restructuring.climbs ⟨⟨.reflexive, some .reflexive⟩, t, rich⟩ := by
  revert ea ia rich; cases t <;> decide

/-- §7.2: with an unaccusative infinitive and no clitic nothing but the auxiliary
distinguishes SHARE (75)/(76) from KEEP (73)/(74) — AS is optional. -/
theorem unaccusative_optional (ea ia : Person) (rich : Bool) :
    Restructuring.matrixAux ea ia ⟨⟨.unaccusative, none⟩, .share, rich⟩ = .be ∧
      Restructuring.matrixAux ea ia ⟨⟨.unaccusative, none⟩, .keep, rich⟩ = .have := by
  revert ea ia rich; decide

/-- A prepositional clitic climbing from an unaccusative leaves HAVE if vAux has only its P-feature
((25)–(27), (36)), BE if it also probes the internal argument ((28)–(30), (37a), §7.3). -/
theorem prepositional_climbing (ea ia : Person) (cl : Clitic) (hcl : cl.prepositional = true)
    (rich : Bool) :
    Restructuring.climbs ⟨⟨.unaccusative, some cl⟩, .share, rich⟩ ∧
      (Restructuring.Switch ea ia ⟨⟨.unaccusative, some cl⟩, .share, rich⟩ ↔ rich = true) := by
  revert ea ia cl rich; decide

/-- An accusative clitic climbs out of a transitive infinitive without auxiliary switch ((31),
[cardinaletti-shlonsky-2004]'s *lo sarei voluto andare a trovare* aside). -/
theorem accusative_climbing (ea ia : Person) (rich : Bool) :
    Restructuring.climbs ⟨⟨.transitive, some .accusative⟩, .share, rich⟩ ∧
      Restructuring.matrixAux ea ia ⟨⟨.transitive, some .accusative⟩, .share, rich⟩ = .have := by
  revert ea ia rich; decide

/-! ### Varieties (§7.1) -/

/-- The grammars the paper compares by the transfers they admit: Modern French only KEEP,
earlier French and Standard Italian both, Sardinian only SHARE. -/
inductive Variety
  | modernFrench | earlierFrench | standardItalian | sardinian
  deriving DecidableEq, Repr, Fintype

/-- The transfer operations a variety admits. -/
def Variety.admits : Variety → TransferStyle → Prop
  | .modernFrench, t => t = .keep
  | .sardinian, t => t = .share
  | _, t => t = .keep ∨ t = .share

instance : (v : Variety) → (t : TransferStyle) → Decidable (v.admits t)
  | .modernFrench, _ | .sardinian, _ => inferInstanceAs (Decidable (_ = _))
  | .earlierFrench, _ | .standardItalian, _ => inferInstanceAs (Decidable (_ ∨ _))

/-- (38): in Sardinian the reflexive clitic climbs and the modal takes BE, obligatorily. -/
theorem sardinian_reflexive (ea ia : Person) (r : Restructuring)
    (hv : Variety.sardinian.admits r.transfer)
    (he : r.embedded = ⟨.reflexive, some .reflexive⟩) : r.climbs ∧ r.Switch ea ia := by
  obtain ⟨e, t, rich⟩ := r
  have ht : t = .share := hv
  have he' : e = ⟨.reflexive, some .reflexive⟩ := he
  subst ht he'; revert ea ia rich; decide

/-- In Modern French KEEP yields neither climbing nor auxiliary switch ((2a), (3a)), the switch of
§3.3 being the SHARE derivation (71). -/
theorem modernFrench_no_switch (ea ia : Person) (r : Restructuring)
    (hv : Variety.modernFrench.admits r.transfer) : ¬ r.climbs ∧ ¬ r.Switch ea ia := by
  have hk : r.transfer = .keep := hv
  have := keep_have ea ia r hk
  exact ⟨this.2, fun h ↦ by simp [Restructuring.Switch, this.1] at h⟩

end Olivier2026
