theory Hoare_Indexed_Complete
  imports "../Hoare/Hoare_Indexed_Sound"
begin
text_raw \<open>%Snippet \<close>
lemma HT_imp_HT' :
  assumes "|gs| {-P-} c {-Q-}"
  shows "|gs| {~P~} c {~Q~}"
text_raw \<open>%EndSnippet\<close>
  sorry
end