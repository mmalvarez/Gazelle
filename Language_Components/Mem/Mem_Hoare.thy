theory Mem_Hoare imports Mem "../../Hoare/Hoare"  "../../Hoare/Hoare_Indexed"
  "../../Hoare/Hoare_Indexed_Sound" "../../Composition/Dominant"
begin
(* need to figure out appropriate way to state these lifting theorems
 * when they are not purely control.
 * 
 *)
lemma HLit :
  assumes H0 : "gs = pcomps fs"
  assumes HF : "f = mem_sem_l_gen lfts lft"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "\<And> s i . (f \<downharpoonleft> (set fs) (Slit' s i))"
  assumes Hsyn : "\<And> s i . lfts (Slit' s i) = Slit s i"
(* we are in an arbitrary larger state.
 * we need to project out the memory field.
 * maybe we should just use the regular Hoare lifting rules for this?. (?) *)

proof

end