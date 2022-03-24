theory Mem_Sem_Excerpt
  imports "../Language_Components/Mem/Mem_Simple"
begin

text_raw \<open>%Snippet paper_examples__mem_sem_excerpt__mem0_sem\<close>
fun mem0_sem :: "syn \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem (Sread s r) (reg_flag, reg_c, reg_a, reg_b, mem) = 
  (case get mem s of
    Some v \<Rightarrow>
      (case r of
        Reg_a \<Rightarrow> (reg_flag, reg_c, v, reg_b, mem)
        | Reg_b \<Rightarrow> (reg_flag, reg_c, reg_a, v, mem)
        \<comment> \<open>... remaining cases similar\<close>)
    | None \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, mem))"
| "mem0_sem (Swrite s r) (reg_flag, reg_c, reg_a, reg_b, mem) =
  (case r of
    Reg_a \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_a mem)
    | Reg_b \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_b mem)
    \<comment> \<open>... remaining cases similar\<close>)"
| "mem0_sem _ st = st"
text_raw \<open>%EndSnippet\<close>

end