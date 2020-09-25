theory Merge_Semantics imports "Gensyn_Semantics" "../Syntax/Syntax" "../Syntax/MiniPack" "../Syntax_Utils"
  "../Syntax/Merge_Syntax"
begin

(* merge semantics with the same view of state *)
(* we may not even need gensyn to define this? *)
(* the idea here is that we are going to enforce that the two have the same xp *)
locale Merge_Sum_Mpack_Simple = Syn_Merge +
  fixes xr :: "'xr itself"
  fixes ms :: "'mstate itself"
  fixes x_sem_left :: "('a, 'c, 'd) mpackf \<Rightarrow>
                       'mstate \<Rightarrow> 'mstate \<Rightarrow>
                       childpath \<Rightarrow> ('a, 'c, 'd) mpackf option gensyn \<Rightarrow>
                       'xr gs_result \<Rightarrow> bool"
  fixes x_sem_right :: "('b, 'c, 'e) mpackf \<Rightarrow>
                       'mstate \<Rightarrow> 'mstate \<Rightarrow>
                       childpath \<Rightarrow> ('b, 'c, 'e) mpackf option gensyn \<Rightarrow>
                       'xr gs_result \<Rightarrow> bool"
  fixes dummy_xs1 :: "'d itself"
  fixes dummy_xs2 :: "'e itself"
begin
print_context


(* idea: the primary semantics will ignore the product-annotations of the secondary
   however perhaps we can do better. for instance, maybe the outer mpack is prepared to
   take in instances of the inner mpack's product already? *)

inductive x_sem_merged ::
  "('a, 'c, ('b, 'd + 'e) mmpack) mpackf \<Rightarrow>
                       'mstate \<Rightarrow> 'mstate \<Rightarrow>
                       childpath \<Rightarrow> ('a, 'c, ('b, 'd + 'e) mmpack) mpackf option gensyn \<Rightarrow>
                       'xr gs_result \<Rightarrow> bool"
  where
" x_sem_left (c, xp, Inl d1) m m' cp (gs_map (flip obnd lowerl) g) r \<Longrightarrow>
  x_sem_merged (c, xp, Inl d1) m m' cp g r"

| "x_sem_left (c, xp, Inr xs1) m m' cp (gs_map (flip obnd lowerl )g) r \<Longrightarrow>
  x_sem_merged (c, xp, Inr (Inr (Inl xs1))) m m' cp g r"


| "x_sem_right (c, xp, Inl d2) m m' cp (gs_map (flip obnd lowerr) g) r \<Longrightarrow>
   x_sem_merged (c, xp, Inr (Inl d2)) m m' cp g r"

| "x_sem_right (c, xp, Inr xs2) m m' cp (gs_map (flip obnd lowerr) g) r \<Longrightarrow>
   x_sem_merged (c, xp, Inr (Inr (Inr xs2))) m m' cp g r"


end

(* another scenario: we are trying to merge two syntaxes, but we have a
   way of converting from xsl to the second pack 
   this will be necessary when we combine Elle and Seq semantics (?)

*)

locale Merge_Sum_Mpack_Full = Syn_Merge +
  fixes xr :: "'xr itself"
  fixes ms :: "'mstate itself"
  fixes x_sem_left :: "('a, 'c, 'd) mpackf \<Rightarrow>
                       'mstate \<Rightarrow> 'mstate \<Rightarrow>
                       childpath \<Rightarrow> ('a, 'c, 'd) mpackf option gensyn \<Rightarrow>
                       'xr gs_result \<Rightarrow> bool"
  fixes x_sem_right :: "('b, 'c, 'e) mpackf \<Rightarrow>
                       'mstate \<Rightarrow> 'mstate \<Rightarrow>
                       childpath \<Rightarrow> ('b, 'c, 'e) mpackf option gensyn \<Rightarrow>
                       'xr gs_result \<Rightarrow> bool"
  fixes dummy_xs1 :: "'d itself"
  fixes dummy_xs2 :: "'e itself"
begin

end

end