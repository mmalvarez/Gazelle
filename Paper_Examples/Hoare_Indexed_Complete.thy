theory Hoare_Indexed_Complete
  imports "../Hoare/Hoare_Indexed_Sound"
begin
text_raw \<open>%Snippet paper_examples__hoare_indexed_complete__HT_imp_HT'\<close>
lemma HT_imp_HT' :
  assumes "|gs| {-P-} c {-Q-}"
  shows "|gs| {~P~} c {~Q~}"
text_raw \<open>%EndSnippet\<close>
  oops
end