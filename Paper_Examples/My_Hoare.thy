theory My_Hoare imports Main

begin

type_synonym state = "int"
type_synonym prog = "unit"

definition sem :: "prog \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
"sem x y z = (y = z)"

text_raw \<open>%Snippet paper_examples__my_hoare__triple\<close>
definition triple :: "(state \<Rightarrow> bool) \<Rightarrow> prog \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" 
  ("{_} _ {_}")
  where
"triple P c Q =
	(\<forall> (st :: state) (st' :: state) . P st \<longrightarrow> sem c st st' \<longrightarrow> Q st')"
text_raw \<open>%EndSnippet\<close>

definition seq ::
  "prog \<Rightarrow> prog \<Rightarrow> prog" ("_;_")where
"seq p1 p2 = ()"

text_raw \<open>%Snippet paper_examples__my_hoare__HSeq\<close>
lemma HSeq :
	assumes Hc1 : "{P1} c1 {P2}"
	assumes Hc2 : "{P2} c2 {P3}"
	shows "{P1} c1 ; c2 {P3}"
text_raw \<open>%EndSnippet\<close>
	sorry

text_raw \<open>%Snippet paper_examples__my_hoare__HConseq\<close>
lemma HConseq :
	assumes HP : "\<And> st . P' st \<Longrightarrow> P st"
	assumes HQ : "\<And> st . Q st \<Longrightarrow> Q' st"
	assumes H : "{P} c {Q}"
	shows "{P'} c {Q'}"	
text_raw \<open>%EndSnippet\<close>
	sorry


end