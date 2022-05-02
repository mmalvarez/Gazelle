theory Calc_Syntax_Example imports "../Syntax/Gensyn"
begin

text_raw \<open>%Snippet paper_examples__calc_syntax_example__arith_manual\<close>
datatype arith_manual =
  AmLit int
  | AmPlus arith_manual arith_manual
  | AmMinus arith_manual arith_manual
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__example_manual\<close>
definition example_manual :: arith_manual where
"example_manual =
  AmMinus (AmPlus (AmLit 4) (AmLit 3))
          (AmPlus (AmLit 2) (AmLit 1))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__arith_label\<close>
datatype arith_label =
  ALit int
  | APlus
  | AMinus
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__arith_gensyn\<close>
type_synonym arith = "arith_label gensyn"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__example_gensyn\<close>
definition example :: arith where
"example =
  G AMinus [G APlus [G (ALit 4) [], G (ALit 3) []],
            G APlus [G (ALit 2) [], G (ALit 1) []]]"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__example_gensyn_sugared\<close>
definition example_sugared :: arith where
"example_sugared =
  \<diamond> AMinus [\<diamond> APlus [\<dagger> ALit 4, \<dagger> ALit 3]
           , \<diamond> APlus [\<dagger> ALit 2, \<dagger> ALit 1]]"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__calc_syntax_example__example_gensyn_bad\<close>
definition bad_arith :: arith where
"bad_arith =
  \<diamond> (ALit 1) [\<dagger> APlus, \<dagger> AMinus]"
text_raw \<open>%EndSnippet\<close>
end