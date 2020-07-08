theory I_Seq_Semantics
  imports I_Semantics Seq_Semantics Merge_Semantics
begin

(*
locale I_Seq_Semantics_Sig = I_Semantics_Sig + Seq_Semantics_Sig

locale I_Seq_Semantics = I_Seq_Semantics_Sig
*)
sublocale I_Semantics \<subseteq> Base_Next_Semantics
  where xr = xr
  and ms = ms
  and x_sem = x_sem_i
  done

interpretation Seq_Semantics_Nop :
  Seq_Semantics "TYPE(unit)" _ seq_nop
  done

(* no parameters... ?*)
locale I_Seq_Semantics = I_Semantics + Seq_Semantics

(* this approach will not let us do multiple merges? *)
sublocale I_Seq_Semantics \<subseteq> Merge_Sum_Mpack_Simple
  where
  ms = ms
  and x_sem_left = x_sem_next
  and x_sem_right = x_sem_seq
  and dummy_xs1 = "()"
and dummy_xs2 = "()"
  done

(*
sublocale I_Seq_Semantics \<subseteq> I_Semantics
  where xr = xr
  and ms = ms
  and i_sem = i_sem
  done

sublocale I_Seq_Semantics \<subseteq> Seq_Semantics
  where xr = xr
  and ms = ms
  and seq_sem = seq_sem
  done
*)
(* we need a module to govern the merging *)

(* problem now is with merging the states *)

print_locale I_Seq_Semantics

locale I_Seq_Semantics_Final = I_Seq_Semantics


sublocale I_Seq_Semantics_Final \<subseteq> Gensyn_Semantics
  where ms = ms
    and x_sem = x_sem_summed
  done

interpretation I_Seq_Semantics_FinalI
  : I_Seq_Semantics_Final "TYPE(unit)" _ calc_semb seq_nop

  done
  
(* need a way to disambiguate the syntax.
   perhaps this is why we originally wanted to use associativity? *)
lemma testout2 : "I_Seq_Semantics_FinalI.gensyn_sem (G (LSeq (), ()) [(G (LInst AccReset, ()))
                                                                    ,(G (LInst (AccAdd 1), ()))]) [] 0 43"

  apply(fastforce intro : I_Seq_Semantics_FinalI.gensyn_sem.intros
I_Seq_Semantics_FinalI.x_sem_summed.intros
seq_nop.intros
I_Semantics_Calc.x_sem_next.intros
I_Semantics_Calc.x_sem_i.intros
calc_semb.intros)

(*  
  apply(rule Gensyn_Semantics_Seq_Calc.gensyn_sem.intros(4)) apply(auto)
   apply(rule "Gensyn_Semantics_Seq_Calc.seq_rec_sem.intros") apply(auto)
   apply(rule "seq_nop.intros")
  apply(rule "Gensyn_Semantics_Seq_Calc.gensyn_sem.intros"(2))
    apply(auto)
   apply(rule "I_Semantics_Calc.base_sem_next.intros") apply(auto)
   apply(rule "I_Semantics_Calc.i_base_sem.intros")
   apply(rule "calc_semb.intros") apply(auto)
  apply(rule "Gensyn_Semantics_Seq_Calc.gensyn_sem.intros"(1))
   apply(auto)
  apply(rule "I_Semantics_Calc.base_sem_next.intros"(2)) apply(auto)
  apply(rule "I_Semantics_Calc.i_base_sem.intros")
  apply(rule "calc_semb.intros") apply(auto)
*)
  done


end