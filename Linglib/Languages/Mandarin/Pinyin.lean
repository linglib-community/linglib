module

/-!
# Pinyin without tone marks

The Mandarin fragment writes its forms in pinyin with tone marks, as *nà* 'that'. Many sources
print their examples without the marks, as Jenks does, so that *nà* appears as *na*. This file
gives the toneless spelling of a form, by which a study checks that a word a source prints is a
form of the entry its data names.

## Implementation notes

* The map is on letters and stands in for a phonology of Mandarin: with the segments and tones of
  a form given, a source that prints no tone marks writes the segments alone, and the toneless
  spelling is derived.
* Dropping the marks is not injective: *nà* 'that' and *nǎ* 'which' are both written *na*. The
  toneless spelling therefore confirms that a word is a form of a named entry and does not
  identify the entry.

## References

* [jenks-2018]
-/

@[expose] public section

namespace Mandarin

/-- A letter of pinyin without its tone mark. -/
def tonelessChar : Char → Char
  | 'ā' | 'á' | 'ǎ' | 'à' => 'a'
  | 'ē' | 'é' | 'ě' | 'è' => 'e'
  | 'ī' | 'í' | 'ǐ' | 'ì' => 'i'
  | 'ō' | 'ó' | 'ǒ' | 'ò' => 'o'
  | 'ū' | 'ú' | 'ǔ' | 'ù' => 'u'
  | 'ǖ' | 'ǘ' | 'ǚ' | 'ǜ' => 'ü'
  | c => c

/-- The letters of a form in pinyin without its tone marks. -/
def toneless (form : String) : List Char := form.toList.map tonelessChar

end Mandarin
