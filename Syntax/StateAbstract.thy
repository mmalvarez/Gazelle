theory StateAbstract imports "../Syntax_Utils" MiniPack
begin

locale halfiso_c_weak =
  fixes forget   :: "'more \<Rightarrow> 'less"
  fixes conc :: "'less \<Rightarrow> 'more"
  assumes Hhisol : "\<And> less . forget (conc less) = less"
  (*assumes Hhisor : "? more . (abstract (forget more)) = more" (* unclear if we need this *) *)


locale halfiso =
  fixes forget   :: "'more \<Rightarrow> 'less"
  fixes conc :: "'less \<Rightarrow> 'more set"
  assumes Hhisol : "\<And> less . Set.image forget (conc less) = {less}"
  assumes Hhisor : "\<And> more . more \<in> conc (forget more)"

locale halfiso_c =
  fixes forget   :: "'more \<Rightarrow> 'less"
  fixes conc :: "'less \<Rightarrow> 'more"
  assumes Hhisol : "\<And> less . forget (conc less) = less"
begin
definition represent :: "'more \<Rightarrow> 'more set" where
"represent more = {more' . forget more = forget more'}"
(*
  assumes Hhisor' : "\<And> more . represent more = represent (conc (forget more))"
  assumes Hrep : "\<And> more . more \<in> represent more" 
*)
end

sublocale halfiso_c \<subseteq> halfiso
  where forget = forget
  and conc = "represent o conc"


  apply(unfold_locales) apply(simp)
   apply(auto simp add:represent_def) apply(simp add:Hhisol)
   apply(subgoal_tac "less \<in> forget ` {more'. conc less = more'}") 
  apply(auto)
   apply(simp add:Hhisol)

   apply(simp add:Hhisol) 
  done

sublocale iso \<subseteq> halfiso_c
  where forget = to_l
  and conc = to_r
  apply(unfold_locales)
  apply(simp add:Hisol)
  done
   
end