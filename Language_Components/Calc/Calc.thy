theory Calc imports Main begin

text_raw \<open>%Snippet gazelle__language_components__calc__calc__calc\<close>
datatype calc = 
  Cadd
  | Csub
  | Cmul
  | Cdiv
  | Cnum int
  | Cskip
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__calc__calc__calc_state\<close>
type_synonym calc_state =
  "(int * int * int)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__calc__calc__calc_sem\<close>
fun calc_sem :: "calc \<Rightarrow> calc_state \<Rightarrow> calc_state" where
"calc_sem (Cadd) (x1, x2, x3) =
  (x1, x2, x1 + x2)"
| "calc_sem (Csub) (x1, x2, _) = (x1, x2, x1 - x2)"
| "calc_sem (Cmul) (x1, x2, _) = (x1, x2, x1 * x2)"
| "calc_sem (Cdiv) (x1, x2, _) = (x1, x2, divide_int_inst.divide_int x1 x2)"
| "calc_sem (Cnum i) (x1, x2, _) = (x1, x2, i)"
| "calc_sem (Cskip) st = st"
text_raw \<open>%EndSnippet\<close>

end