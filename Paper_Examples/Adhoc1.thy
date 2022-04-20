theory Adhoc1
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

class noname

instantiation bool :: noname
begin
instance proof qed
end

instantiation char :: noname
begin
instance proof qed
end

text_raw \<open>%Snippet paper_examples__adhoc1__tyname\<close>
(* we need to have imported "HOL-Library.Adhoc_Overloading" for this to work *)
consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"
(* check the output for nat *)

adhoc_overloading tyname
  tyn_unit
  tyn_nat

value "tyname (TYPE (nat))"
\<comment> \<open>Result:\<close>
text \<open>@{value "tyname (TYPE (nat))"}\<close>
text_raw \<open>%EndSnippet\<close>

end