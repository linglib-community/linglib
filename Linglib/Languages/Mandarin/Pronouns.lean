module

public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Mandarin interrogative words

The Mandarin interrogative words are quexistentials: *shéi* is 'who' in a question and, in the
environments that license it, 'someone, anyone'. The forms are those of the interrogative column
of Haspelmath's table.

## References

* [haspelmath-1997]
* [hengeveld-iatridou-roelofsen-2023]
-/

@[expose] public section

namespace Mandarin.Pronouns

/-- 谁 *shéi* 'who, someone'. -/
def shei : ProForm := { form := "shéi", script := some "谁", ontology := .person }

/-- 什么 *shénme* 'what, something'. -/
def shenme : ProForm := { form := "shénme", script := some "什么", ontology := .thing }

/-- *nǎr* 'where, somewhere'. -/
def nar : ProForm := { form := "nǎr", ontology := .place }

/-- *shénme dìfang* 'what place'. -/
def shenmeDifang : ProForm := { form := "shénme dìfang", ontology := .place }

/-- *shénme shíhou* 'what time'. -/
def shenmeShihou : ProForm := { form := "shénme shíhou", ontology := .time }

/-- *zěnme* 'how, somehow'. -/
def zenme : ProForm := { form := "zěnme", ontology := .manner }

/-- *něi* 'which, some'. -/
def nei : ProForm := { form := "něi", ontology := .determiner }

/-- The quexistentials. -/
def quexistentials : Finset ProForm :=
  {shei, shenme, nar, shenmeDifang, shenmeShihou, zenme, nei}

/-- The interrogative pronouns, the quexistentials in their interrogative use. -/
def interrogatives : Finset InterrogativePronoun := quexistentials.image (⟨·⟩)

end Mandarin.Pronouns
