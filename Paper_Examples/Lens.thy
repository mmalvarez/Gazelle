theory Lens imports Main
begin

text_raw \<open>%Snippet paper_examples__lens__lens\<close>
locale lens =
	fixes get :: "'b \<Rightarrow> 'a"
	fixes put :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

locale lens_valid = lens +
	assumes get_put :
		"\<And> (a :: 'a) (b :: 'b) . get (put a b) = a"
	assumes put_get :
		"\<And> (b :: 'b) . put (get b) b = b"
	assumes put_put :
		"\<And> (a1 :: 'a) (a2 :: 'a) (b :: 'b) .
			put a2 (put a1 b) = put a2 b"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__lens__lens_lift\<close>
definition (in lens)
	lens_lift :: "('syn \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('syn \<Rightarrow> 'b \<Rightarrow> 'b)" where
"lens_lift f syn st =
	(put (f syn (get st)) st)"
text_raw \<open>%EndSnippet\<close>


end