theory Adhoc4
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

(* we need to have imported "HOL-Library.Adhoc_Overloading" for this to work *)
consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"

definition tyn_option_bad ::
  "('a option itself \<Rightarrow> char list)" where
"tyn_option_bad _ =
  (tyname (TYPE('a))) @ '' OPTION''"

definition tyn_option ::
  "('a itself \<Rightarrow> char list) \<Rightarrow> ('a option itself \<Rightarrow> char list)" where
"tyn_option t _ =
  (t (TYPE( 'a))) @ '' OPTION''"

text_raw \<open>%Snippet paper_examples__gazelle__tyname\<close>
definition tyn_noname_bad :: "'a itself \<Rightarrow> char list" where
"tyn_noname_bad _ = ''UHOH''"

adhoc_overloading tyname
  tyn_unit
  tyn_nat
  tyn_noname_bad
 "tyn_option tyname"

(* this produces a type error *)
(* value [nbe] "tyname (TYPE (nat))" *)
text_raw \<open>%EndSnippet\<close>

end