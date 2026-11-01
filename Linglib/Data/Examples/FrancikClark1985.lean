module

public import Linglib.Data.Examples.Schema

/-!
# `FrancikClark1985` — typed example data

Auto-generated from `Linglib/Data/Examples/FrancikClark1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FrancikClark1985.Examples`.
-/

@[expose] public section

namespace FrancikClark1985.Examples

def read_newspaper : Datum :=
  { id := "francikclark1985_read_newspaper"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you happen to read in the newspaper this morning what time the governor's lecture is today?"
    glossedTokens := []
    context := "Anne wants to know the time of a lecture announced in that morning's newspaper and thinks Bernard would tell her if only he had seen the announcement."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("obstacle", "source"), ("appropriate", "yes")] }

def want_to_tell : Datum :=
  { id := "francikclark1985_want_to_tell"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you want to tell me what time the governor's lecture is today?"
    glossedTokens := []
    context := "Anne wants to know the time of a lecture announced in that morning's newspaper and thinks Bernard would tell her if only he had seen the announcement."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "source"), ("appropriate", "no")] }

def willing_middle_name : Datum :=
  { id := "francikclark1985_willing_middle_name"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would you be willing to tell me your middle name?"
    glossedTokens := []
    context := "Anne asks Bernard for his middle name."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "willingness"), ("appropriate", "yes")] }

def know_middle_name : Datum :=
  { id := "francikclark1985_know_middle_name"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you happen to know your middle name?"
    glossedTokens := []
    context := "Anne asks Bernard for his middle name."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "willingness"), ("appropriate", "no")] }

def can_unsure : Datum :=
  { id := "francikclark1985_can_unsure"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you tell me when the governor's lecture is?"
    glossedTokens := []
    context := "Anne is unsure whether the obstacle is Bernard's finding out the time, remembering it, or being allowed to tell it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "ability"), ("appropriate", "yes")] }

def gradient1 : Datum :=
  { id := "francikclark1985_gradient1"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you tell me when the governor's lecture is?"
    glossedTokens := []
    context := "Anne has narrowed the obstacle down to Bernard's perhaps not having read the morning's newspaper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "source"), ("appropriate", "yes"), ("gradient", "yes")] }

def gradient2 : Datum :=
  { id := "francikclark1985_gradient2"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you know when the governor's lecture is?"
    glossedTokens := []
    context := "Anne has narrowed the obstacle down to Bernard's perhaps not having read the morning's newspaper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "source"), ("appropriate", "yes"), ("gradient", "yes")] }

def gradient3 : Datum :=
  { id := "francikclark1985_gradient3"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you happen to know when the governor's lecture is?"
    glossedTokens := []
    context := "Anne has narrowed the obstacle down to Bernard's perhaps not having read the morning's newspaper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "source"), ("appropriate", "yes"), ("gradient", "yes")] }

def gradient4 : Datum :=
  { id := "francikclark1985_gradient4"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you happen to see an announcement of when the governor's lecture is?"
    glossedTokens := []
    context := "Anne has narrowed the obstacle down to Bernard's perhaps not having read the morning's newspaper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("obstacle", "source"), ("appropriate", "yes"), ("gradient", "yes")] }

def gradient5 : Datum :=
  { id := "francikclark1985_gradient5"
    source := ⟨"francik-clark-1985", "introduction"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you happen to read in the newspaper this morning when the governor's lecture is?"
    glossedTokens := []
    context := "Anne has narrowed the obstacle down to Bernard's perhaps not having read the morning's newspaper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("obstacle", "source"), ("appropriate", "yes"), ("gradient", "yes")] }

def remember_concert : Datum :=
  { id := "francikclark1985_remember_concert"
    source := ⟨"francik-clark-1985", "abstract"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you remember what time the concert begins tonight?"
    glossedTokens := []
    context := "The speaker thinks the addressee might not remember the time of the concert."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "memory"), ("obstacle", "memory"), ("appropriate", "yes")] }

def know_concert : Datum :=
  { id := "francikclark1985_know_concert"
    source := ⟨"francik-clark-1985", "Experiment 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you know when the next orchestra concert is?"
    glossedTokens := []
    context := "At breakfast you are talking with your roommate and want to find out the time of the next orchestra concert; the roommate may not know about it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "knowledge"), ("appropriate", "yes")] }

def have_asked : Datum :=
  { id := "francikclark1985_have_asked"
    source := ⟨"francik-clark-1985", "Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have I already asked you?"
    glossedTokens := []
    context := "You are making conversation with your sister's boyfriend and decide to ask about his schoolwork, but you have forgotten whether that has already come up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "speakerMemory"), ("obstacle", "speakerMemory"), ("appropriate", "yes")] }

def could_give : Datum :=
  { id := "francikclark1985_could_give"
    source := ⟨"francik-clark-1985", "Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could you give me?"
    glossedTokens := []
    context := "The addressee has the information but may not be allowed to divulge it, as doing so would violate a set policy (scenarios 11 and 12)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "permission"), ("appropriate", "yes")] }

def see_concert : Datum :=
  { id := "francikclark1985_see_concert"
    source := ⟨"francik-clark-1985", "General Discussion"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did you happen to see what time the concert begins?"
    glossedTokens := []
    context := "Anne asks Bernard the time of the concert; he may not have seen it announced."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("obstacle", "source"), ("appropriate", "yes")] }

def want_concert : Datum :=
  { id := "francikclark1985_want_concert"
    source := ⟨"francik-clark-1985", "General Discussion"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Don't you want to tell me what time the concert begins?"
    glossedTokens := []
    context := "Anne asks Bernard the time of the concert; he may not have seen it announced."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "source"), ("appropriate", "no")] }

def time1 : Datum :=
  { id := "francikclark1985_time1"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "What time is it?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "direct"), ("directness", "10"), ("producedHigh", "0"), ("producedLow", "2")] }

def time2 : Datum :=
  { id := "francikclark1985_time2"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you know what time it is?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("directness", "30"), ("producedHigh", "4"), ("producedLow", "2")] }

def time3 : Datum :=
  { id := "francikclark1985_time3"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Could you tell me what time it is?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("directness", "34"), ("producedHigh", "0"), ("producedLow", "5")] }

def time4 : Datum :=
  { id := "francikclark1985_time4"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you have the time?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("directness", "42"), ("producedHigh", "1"), ("producedLow", "6")] }

def time5 : Datum :=
  { id := "francikclark1985_time5"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you happen to know what time it is?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("directness", "45"), ("producedHigh", "4"), ("producedLow", "0")] }

def time6 : Datum :=
  { id := "francikclark1985_time6"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you have any idea what time it is?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("directness", "60"), ("producedHigh", "2"), ("producedLow", "0")] }

def time7 : Datum :=
  { id := "francikclark1985_time7"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "You wouldn't happen to know the time, would you?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("directness", "67"), ("producedHigh", "2"), ("producedLow", "0")] }

def time8 : Datum :=
  { id := "francikclark1985_time8"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you happen to have a watch, or know what time it is, or anything?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("directness", "73"), ("producedHigh", "1"), ("producedLow", "0")] }

def time9 : Datum :=
  { id := "francikclark1985_time9"
    source := ⟨"francik-clark-1985", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Do you know if there's a clock anywhere around here?"
    glossedTokens := []
    context := "You see a student sitting at a table outside Tresidder, and you notice that he is clearly not wearing a watch [high obstacle] / he is wearing a watch [low obstacle]. You want to ask him the time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "source"), ("directness", "88"), ("producedHigh", "1"), ("producedLow", "0")] }

def rating_ability_1 : Datum :=
  { id := "francikclark1985_rating_ability_1"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you know X?"
    glossedTokens := []
    context := "An ability scenario of Experiment 1, such as asking the roommate the time of the next orchestra concert: the addressee may not know the information, remember it, be able to find it out, or be allowed to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "knowledge"), ("ratingHigh", "552"), ("ratingLow", "485")] }

def rating_willingness_1 : Datum :=
  { id := "francikclark1985_rating_willingness_1"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you know X?"
    glossedTokens := []
    context := "A willingness scenario of Experiment 1, such as asking a friend whether his parents were divorced: the addressee has the information but may be reluctant to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "willingness"), ("ratingHigh", "246"), ("ratingLow", "279")] }

def rating_memory_1 : Datum :=
  { id := "francikclark1985_rating_memory_1"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you know X?"
    glossedTokens := []
    context := "A speaker-memory scenario of Experiment 1, such as asking your sister's boyfriend about his schoolwork: you may already have asked."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "knowledge"), ("obstacle", "speakerMemory"), ("ratingHigh", "350"), ("ratingLow", "361")] }

def rating_ability_2 : Datum :=
  { id := "francikclark1985_rating_ability_2"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you tell me X?"
    glossedTokens := []
    context := "An ability scenario of Experiment 1, such as asking the roommate the time of the next orchestra concert: the addressee may not know the information, remember it, be able to find it out, or be allowed to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "knowledge"), ("ratingHigh", "526"), ("ratingLow", "533")] }

def rating_willingness_2 : Datum :=
  { id := "francikclark1985_rating_willingness_2"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you tell me X?"
    glossedTokens := []
    context := "A willingness scenario of Experiment 1, such as asking a friend whether his parents were divorced: the addressee has the information but may be reluctant to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "willingness"), ("ratingHigh", "419"), ("ratingLow", "503")] }

def rating_memory_2 : Datum :=
  { id := "francikclark1985_rating_memory_2"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you tell me X?"
    glossedTokens := []
    context := "A speaker-memory scenario of Experiment 1, such as asking your sister's boyfriend about his schoolwork: you may already have asked."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "speakerMemory"), ("ratingHigh", "458"), ("ratingLow", "475")] }

def rating_ability_3 : Datum :=
  { id := "francikclark1985_rating_ability_3"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could you tell me X?"
    glossedTokens := []
    context := "An ability scenario of Experiment 1, such as asking the roommate the time of the next orchestra concert: the addressee may not know the information, remember it, be able to find it out, or be allowed to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "knowledge"), ("ratingHigh", "512"), ("ratingLow", "549")] }

def rating_willingness_3 : Datum :=
  { id := "francikclark1985_rating_willingness_3"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could you tell me X?"
    glossedTokens := []
    context := "A willingness scenario of Experiment 1, such as asking a friend whether his parents were divorced: the addressee has the information but may be reluctant to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "willingness"), ("ratingHigh", "456"), ("ratingLow", "514")] }

def rating_memory_3 : Datum :=
  { id := "francikclark1985_rating_memory_3"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could you tell me X?"
    glossedTokens := []
    context := "A speaker-memory scenario of Experiment 1, such as asking your sister's boyfriend about his schoolwork: you may already have asked."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "general"), ("obstacle", "speakerMemory"), ("ratingHigh", "472"), ("ratingLow", "481")] }

def rating_ability_4 : Datum :=
  { id := "francikclark1985_rating_ability_4"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would you mind telling me X?"
    glossedTokens := []
    context := "An ability scenario of Experiment 1, such as asking the roommate the time of the next orchestra concert: the addressee may not know the information, remember it, be able to find it out, or be allowed to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "knowledge"), ("ratingHigh", "429"), ("ratingLow", "507")] }

def rating_willingness_4 : Datum :=
  { id := "francikclark1985_rating_willingness_4"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would you mind telling me X?"
    glossedTokens := []
    context := "A willingness scenario of Experiment 1, such as asking a friend whether his parents were divorced: the addressee has the information but may be reluctant to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "willingness"), ("ratingHigh", "550"), ("ratingLow", "572")] }

def rating_memory_4 : Datum :=
  { id := "francikclark1985_rating_memory_4"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would you mind telling me X?"
    glossedTokens := []
    context := "A speaker-memory scenario of Experiment 1, such as asking your sister's boyfriend about his schoolwork: you may already have asked."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "willingness"), ("obstacle", "speakerMemory"), ("ratingHigh", "330"), ("ratingLow", "356")] }

def rating_ability_5 : Datum :=
  { id := "francikclark1985_rating_ability_5"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you already told me X?"
    glossedTokens := []
    context := "An ability scenario of Experiment 1, such as asking the roommate the time of the next orchestra concert: the addressee may not know the information, remember it, be able to find it out, or be allowed to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "speakerMemory"), ("obstacle", "knowledge"), ("ratingHigh", "178"), ("ratingLow", "197")] }

def rating_willingness_5 : Datum :=
  { id := "francikclark1985_rating_willingness_5"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you already told me X?"
    glossedTokens := []
    context := "A willingness scenario of Experiment 1, such as asking a friend whether his parents were divorced: the addressee has the information but may be reluctant to give it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "speakerMemory"), ("obstacle", "willingness"), ("ratingHigh", "215"), ("ratingLow", "235")] }

def rating_memory_5 : Datum :=
  { id := "francikclark1985_rating_memory_5"
    source := ⟨"francik-clark-1985", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you already told me X?"
    glossedTokens := []
    context := "A speaker-memory scenario of Experiment 1, such as asking your sister's boyfriend about his schoolwork: you may already have asked."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("query", "speakerMemory"), ("obstacle", "speakerMemory"), ("ratingHigh", "525"), ("ratingLow", "306")] }

def all : List Datum := [read_newspaper, want_to_tell, willing_middle_name, know_middle_name, can_unsure, gradient1, gradient2, gradient3, gradient4, gradient5, remember_concert, know_concert, have_asked, could_give, see_concert, want_concert, time1, time2, time3, time4, time5, time6, time7, time8, time9, rating_ability_1, rating_willingness_1, rating_memory_1, rating_ability_2, rating_willingness_2, rating_memory_2, rating_ability_3, rating_willingness_3, rating_memory_3, rating_ability_4, rating_willingness_4, rating_memory_4, rating_ability_5, rating_willingness_5, rating_memory_5]

end FrancikClark1985.Examples
