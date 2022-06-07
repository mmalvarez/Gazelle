theory Composition_Option imports Main
begin

text_raw \<open>%Snippet paper_examples__composition_option__f1_f2\<close>
datatype flag =
	IS_ONE
	| IS_TWO

definition f1 :: "(nat * flag option) \<Rightarrow> (nat * flag option)" where
	"f1 p = (case p of (x, _) \<Rightarrow> 
    (x, (if x = 1 then Some IS_ONE 
                  else None)))"
definition f2 :: "(nat * flag option) \<Rightarrow> (nat * flag option)" where
	"f2 p = (case p of (x, _) \<Rightarrow> 
    (x, (if x = 2 then Some IS_TWO
                  else None)))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__composition_option__composed_f1_f2\<close>
definition composed_f1_f2 ::
  "(nat * flag option \<Rightarrow> nat * flag option)" where
"composed_f1_f2 x =
(case x of
	(x1, x2) \<Rightarrow>
	(case f1 (x1, x2) of
		(x1', None) \<Rightarrow> f2 (x1, x2)
		| (x1', Some x2') \<Rightarrow> 
			(case f2 (x1, x2) of
        (x1'', None) \<Rightarrow> (x1', Some x2')
				| (x1'', Some x2'') \<Rightarrow> 
          \<comment> \<open>can't occur for f1, f2 as defined above\<close>
          undefined)))"
text_raw \<open>%EndSnippet\<close>

end