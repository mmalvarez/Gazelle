theory Composition_Tuple_Components imports Main
begin

text_raw \<open>%Snippet paper_examples__composition_tuple_components__composed_f1_f2\<close>

type_synonym state = "(int * int)"

definition f1 :: "state \<Rightarrow> state"
  where
"f1 st = 
  (case st of
    (x1, x2) \<Rightarrow> (x1 + 1, x2))"

definition f2 :: " state \<Rightarrow> state"
  where
"f2 st =
  (case st of
    (x1, x2) \<Rightarrow> (x1, x2 - 1))" (* ... f2 definition *)

definition composed_f1_f2 :: "state \<Rightarrow> state" where
"composed_f1_f2 x =
	(case f1 x of (x1, _) \<Rightarrow>
		(case f2 x of (_, x2) \<Rightarrow>
			(x1, x2)))"
text_raw \<open>%EndSnippet\<close>

end