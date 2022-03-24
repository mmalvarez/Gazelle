theory Cond imports Main
begin

(* conditional/boolean expressions *)
text_raw \<open>%Snippet gazelle__language_components__cond__cond__cond\<close>
datatype cond =
  Seqz
  | Sltz
  | Sgtz
  | Sskip_cond
text_raw \<open>%EndSnippet\<close>

(* first int is a boolean flag. *)
text_raw \<open>%Snippet gazelle__language_components__cond__cond__cond_state\<close>
type_synonym cond_state = "int * int"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__cond__cond__encode_bool\<close>
abbreviation encode_bool :: "bool \<Rightarrow> int" where
"encode_bool b \<equiv>
  (if b then 1 else 0)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__language_components__cond__cond__cond_sem\<close>
definition cond_sem :: "cond \<Rightarrow> cond_state \<Rightarrow> cond_state" where
"cond_sem x s =
  (case s of (b, i) \<Rightarrow>
    (case x of
      Seqz \<Rightarrow> (encode_bool (i = 0), i)
      | Sltz \<Rightarrow> (encode_bool (i < 0), i)
      | Sgtz \<Rightarrow> (encode_bool (i > 0), i)
      | Sskip_cond \<Rightarrow> s))"
text_raw \<open>%EndSnippet\<close>

end