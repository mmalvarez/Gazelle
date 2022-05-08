theory Composition_Priority imports Main
begin

text_raw \<open>%Snippet paper_examples__composition_priority__f1_f2\<close>
datatype syn =
	op1
	| op2

type_synonym state = "(nat * nat * nat)"

definition f1 :: "syn \<Rightarrow> state \<Rightarrow> state" where
"f1 s x =
(case x of
	(x1, x2, x3) \<Rightarrow>
		(case s of
			op1 \<Rightarrow> (x1, x2, x1 + x2)
			| op2 \<Rightarrow> (x1, x2, x1 - x2)))"

definition f2 :: "syn \<Rightarrow> state \<Rightarrow> state" where
"f2 s x =
(case x of
	(x1, x2, x3) \<Rightarrow>
		(case s of
			op1 \<Rightarrow> (x1, x2, x1 * x2)
			| op2 \<Rightarrow> (x1, x2,
               divide_nat_inst.divide_nat x1 x2)))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__composition_priority__composed_f1_f2\<close>
definition priority_f1 :: "syn \<Rightarrow> nat" where
"priority_f1 x =
	(case x of
		op1 \<Rightarrow> 2
		| op2 \<Rightarrow> 1)"

definition priority_f2 :: "syn \<Rightarrow> nat" where
"priority_f2 x =
	(case x of
		op1 \<Rightarrow> 1
		| op2 \<Rightarrow> 2)"

definition composed_f1_f2 :: "syn \<Rightarrow> state \<Rightarrow> state" where
"composed_f1_f2 s x =
	(if priority_f1 s > priority_f2 s then f1 s x
	 else (if priority_f2 s > priority_f1 s then f2 s x
	 	else undefined \<comment> \<open> can't happen for priorities as defined above \<close>))"
text_raw \<open>%EndSnippet\<close>

end