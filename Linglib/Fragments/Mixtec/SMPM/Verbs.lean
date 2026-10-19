module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# San Martín Peras Mixtec complement-taking verbs

San Martín Peras Mixtec has no non-finite verb forms: every clause is completive, continuous or
irrealis, marked mostly by the tone of the first vowel, and every clause has an overt subject.
Complement-taking verbs take one of two kinds of clause. A finite complement is free in aspect
and in its subject. The other kind is always irrealis. Under verbs of wanting, hoping and
fearing, its subject may differ from the matrix subject, which *ná* can mark, and it may have a
time adverb of its own. Under verbs of trying, beginning, remembering and needing, its subject
is a clitic pronoun that refers to the matrix subject, and its time is the matrix time.

## Implementation notes

A finite complement is `ArgumentFrame.finiteClause`. An irrealis complement is
`subjunctiveFrame`, in Noonan's subjunctive coding with an overt subject. A verb whose
irrealis complement has a coreferent subject has its subject as the controller of that
complement; the other irrealis-taking verbs have no controller. The forms are the citation
forms of the source's predicate lists, with its tone marks, and each entry is named by its
English gloss.

## References

* [ostrove-2026]
* [noonan-2007]
-/

@[expose] public section

namespace Mixtec.SMPM

/-- The irrealis complement is a declarative clause in the subjunctive coding with an overt
subject. -/
def subjunctiveFrame : ArgumentFrame :=
  ⟨some .nominal, [.clausal (some .subjunctive) (.only .declarative) (some (.overt none))]⟩

/-! ### Verbs taking a finite complement ((27a)) -/

/-- *ka'án* 'think' takes a finite complement. -/
def think : Verb where
  morphs := [.root "ka'án"]
  valency := .ofFrame .finiteClause

/-- *nakanini* 'believe' takes a finite complement. -/
def believe : Verb where
  morphs := [.root "nakanini"]
  valency := .ofFrame .finiteClause

/-- *kuntàà ini* 'wonder' takes a finite complement. -/
def wonder : Verb where
  morphs := [.root "kuntàà", .root "ini"]
  valency := .ofFrame .finiteClause

/-- *kònì* 'know' takes a finite complement, and as 'know how to', optionally with *xá kasa*,
an irrealis complement with a coreferent subject ((27c)). -/
def know : Verb where
  morphs := [.root "kònì"]
  valency := .of [(.finiteClause, [0, 1]), (subjunctiveFrame, [0, 1])]
    (controllers := [none, some 0])

/-- *kà'àn* 'say' takes a finite complement. -/
def say : Verb where
  morphs := [.root "kà'àn"]
  valency := .ofFrame .finiteClause
  speechActVerb := true

/-- *ntatǔ'un* 'chat' takes a finite complement. -/
def chat : Verb where
  morphs := [.root "ntatǔ'un"]
  valency := .ofFrame .finiteClause

/-- *káchi* 'said' takes a finite complement; it is defective, with only a completive form
(fn. 5). -/
def said : Verb where
  morphs := [.root "káchi"]
  valency := .ofFrame .finiteClause
  speechActVerb := true

/-- *kusijǐ ini* 'be happy' takes a finite complement. -/
def beHappy : Verb where
  morphs := [.root "kusijǐ", .root "ini"]
  valency := .ofFrame .finiteClause

/-- *ntsi'i ini* 'be sad' takes a finite complement. -/
def beSad : Verb where
  morphs := [.root "ntsi'i", .root "ini"]
  valency := .ofFrame .finiteClause

/-- *ntsiko ini* 'regret' takes a finite complement. -/
def regret : Verb where
  morphs := [.root "ntsiko", .root "ini"]
  valency := .ofFrame .finiteClause

/-! ### Verbs taking an irrealis complement with a free subject ((27b)) -/

/-- *kòni* 'want' takes an irrealis complement with a free subject. It is the one such verb out
of whose complement a quantifier can front (fn. 8). -/
def want : Verb where
  morphs := [.root "kòni"]
  valency := .ofFrame subjunctiveFrame

/-- *síso ini* 'hate' (lit. 'boil inside') takes an irrealis complement with a free subject. -/
def hate : Verb where
  morphs := [.root "síso", .root "ini"]
  valency := .ofFrame subjunctiveFrame

/-- *iyǐ'bi* 'fear, be afraid' takes an irrealis complement with a free subject. -/
def fear : Verb where
  morphs := [.root "iyǐ'bi"]
  valency := .ofFrame subjunctiveFrame

/-- *kuntasí* 'be scared' takes an irrealis complement with a free subject. -/
def beScared : Verb where
  morphs := [.root "kuntasí"]
  valency := .ofFrame subjunctiveFrame

/-- *nakwatu* 'pray' takes an irrealis complement with a free subject. -/
def pray : Verb where
  morphs := [.root "nakwatu"]
  valency := .ofFrame subjunctiveFrame

/-- *ntatu* 'hope' takes an irrealis complement with a free subject. -/
def hope : Verb where
  morphs := [.root "ntatu"]
  valency := .ofFrame subjunctiveFrame

/-- *xiinka* 'agree' takes an irrealis complement with a free subject. -/
def agree : Verb where
  morphs := [.root "xiinka"]
  valency := .ofFrame subjunctiveFrame

/-- *xǐinka* 'refuse' (lit. 'not agree') takes an irrealis complement with a free subject. -/
def refuse : Verb where
  morphs := [.root "xǐinka"]
  valency := .ofFrame subjunctiveFrame

/-- *chikàà ini* 'get the idea to' (lit. 'put inside') takes an irrealis complement with a free
subject. -/
def getIdea : Verb where
  morphs := [.root "chikàà", .root "ini"]
  valency := .ofFrame subjunctiveFrame

/-! ### Verbs taking an irrealis complement with a coreferent subject ((27c)) -/

/-- *ntukú* 'try' (lit. 'look for') takes an irrealis complement with a coreferent subject. -/
def try_ : Verb where
  morphs := [.root "ntukú"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *nakú'ún ini* 'remember' takes an irrealis complement with a coreferent subject. -/
def remember : Verb where
  morphs := [.root "nakú'ún", .root "ini"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *nantǒso* 'forget' takes an irrealis complement with a coreferent subject. -/
def forget : Verb where
  morphs := [.root "nantǒso"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *kutô* 'like to' takes an irrealis complement with a coreferent subject. -/
def likeTo : Verb where
  morphs := [.root "kutô"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *kixǎ* 'start, begin' takes an irrealis complement with a coreferent subject. -/
def start : Verb where
  morphs := [.root "kixǎ"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *ntsi'i* 'finish' takes an irrealis complement with a coreferent subject. -/
def finish : Verb where
  morphs := [.root "ntsi'i"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *xikwîn* 'stop' takes an irrealis complement with a coreferent subject. -/
def stop : Verb where
  morphs := [.root "xikwîn"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *kò xikwîn* 'continue' (lit. 'not stop') takes an irrealis complement with a coreferent
subject. -/
def continue_ : Verb where
  morphs := [.free "kò", .root "xikwîn"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *xiniñu'u* 'need' takes an irrealis complement with a coreferent subject. -/
def need : Verb where
  morphs := [.root "xiniñu'u"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *sakwǎ'a* 'learn how to' takes an irrealis complement with a coreferent subject. -/
def learn : Verb where
  morphs := [.root "sakwǎ'a"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- *kò ntaa* 'not bother' (lit. 'not climb') takes an irrealis complement with a coreferent
subject. -/
def notBother : Verb where
  morphs := [.free "kò", .root "ntaa"]
  valency := .ofFrame subjunctiveFrame (controller := some 0)

/-- The complement-taking verbs of the source's lists. -/
def verbs : List Verb :=
  [think, believe, wonder, know, say, chat, said, beHappy, beSad, regret,
   want, hate, fear, beScared, pray, hope, agree, refuse, getIdea,
   try_, remember, forget, likeTo, start, finish, stop, continue_, need, learn, notBother]

end Mixtec.SMPM
