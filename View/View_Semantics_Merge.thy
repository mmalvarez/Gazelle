theory View_Semantics_Merge
  imports View_Comp View_Merge View_Fun
begin

(* idea: we have a syntax that split into 2 sub syntaxes
         we have a state that splits into 2 sub states
         we have semantics for each one
         we want to get a semantics for the overall syntax, talking about overall states *)

record ('s1, 's2, 's, 'm1, 'm2, 'm) view_semantics_merge_parms =
  vm_syn :: "('s1, 's2, 's) view_merge_parms"
  vm_sem :: "('m1, 'm2, 'm) view_merge_parms"
  sem1 :: "'s1 \<Rightarrow> 'm1 \<Rightarrow> 'm1"
  sem2 :: "'s2 \<Rightarrow> 'm2 \<Rightarrow> 'm2"

locale View_Semantics_Merge' =
  fixes View_Semantics_Merge_parms :: "('s1, 's2, 's, 'm1, 'm2, 'm) view_semantics_merge_parms"

locale View_Semantics_Merge = View_Semantics_Merge' +
  VMSyn : View_Merge_Spec "vm_syn View_Semantics_Merge_parms" +
  VMSem : View_Merge_Spec "vm_sem View_Semantics_Merge_parms" +
  VF1 : View_Fun "sem1 View_Semantics_Merge_parms" +
  VF2 : View_Fun "sem2 View_Semantics_Merge_parms"

begin
print_context
abbreviation sem1' :: "'a \<Rightarrow> 'd \<Rightarrow> 'd" where
"sem1' \<equiv> sem1 View_Semantics_Merge_parms"

abbreviation sem2' :: "'b \<Rightarrow> 'e \<Rightarrow> 'e" where
"sem2' \<equiv> sem2 View_Semantics_Merge_parms"

(* we can generalize this, making fewer assumptions about the
   nature of the syntax involved *)
fun sem :: "'c \<Rightarrow> 'f \<Rightarrow> 'f" where
"sem s m = 
  (case VMSyn.V1.prj s of
    Inl s1 \<Rightarrow> (case VMSem.V1.prj m of
                Inl m1 \<Rightarrow> VMSem.V1.inj (sem1' s1 m1, m))
    | Inr _ \<Rightarrow> 
  (case VMSyn.V2.prj s of
    Inl s2 \<Rightarrow> (case VMSem.V2.prj m of
                Inl m2 \<Rightarrow> VMSem.V2.inj (sem2' s2 m2, m))))
    "

fun sem_gen :: "'c \<Rightarrow> 'f \<Rightarrow> 'f option" where
"sem_gen s m = 
  (case (VMSyn.V1.prj s, VMSem.V1.prj m) of
    (Inl s1, Inl m1) \<Rightarrow> Some (VMSem.V1.inj (sem1' s1 m1, m))
    | _ \<Rightarrow>
  (case (VMSyn.V2.prj s, VMSem.V2.prj m) of
    (Inl s2, Inl m2) \<Rightarrow> Some (VMSem.V2.inj (sem2' s2 m2, m))
    | _ \<Rightarrow> None))"

fun sem_gen_partial :: "'c \<Rightarrow> 'f \<Rightarrow> 'f" where
"sem_gen_partial s m = 
  (case sem_gen s m of
    Some m' \<Rightarrow> m')"

fun sem_gen_nop :: "'c \<Rightarrow> 'f \<Rightarrow> 'f" where
"sem_gen_nop s m =
  (case sem_gen s m of
    Some m' \<Rightarrow> m'
    | None \<Rightarrow> m)"

end




end