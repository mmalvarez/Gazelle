theory File imports Main

begin

text_raw \<open>%Snippet testy\<close>
datatype boo =
  hi
  | bye

fun meh :: "boo \<Rightarrow> nat" where
"meh hi = 1"
| "meh bye = 2"
text_raw \<open>%EndSnippet\<close>


end