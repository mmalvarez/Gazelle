theory I_Seq_Semantics
  imports I_Semantics Seq_Semantics
begin

locale I_Seq_Semantics_Sig = I_Semantics_Sig + Seq_Semantics_Sig

locale I_Seq_Semantics = I_Seq_Semantics_Sig

sublocale I_Semantics \<subseteq> Base_Next_Semantics
  where xr = xr
  and ms = ms
  and base_sem = i_base_sem
  done


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

(* problem now is with merging the states *)

locale I_Seq_Semantics_Final = I_Seq_Semantics

sublocale I_Seq_Semantics_Final \<subseteq> Gensyn_Semantics
  where xr = xr
  and ms = ms
  and base_sem = base_sem_next
  and rec_sem = seq_rec_sem
  done

print_locale I_Seq_Semantics

interpretation Gensyn_Semantics_Seq_Calc :
  I_Seq_Semantics_Final "TYPE(unit)" _ calc_semb seq_nop
  done
term "Gensyn_Semantics_Seq_Calc.gensyn_sem"

lemma testout2 : "Gensyn_Semantics_Seq_Calc.gensyn_sem (GRec () (LSeq ()) [(GBase () (LInst AccReset))
                                                                         ,(GBase () (LInst (AccAdd 1)))]) [] 0 43"
  
  apply(fastforce intro : Gensyn_Semantics_Seq_Calc.gensyn_sem.intros
Gensyn_Semantics_Seq_Calc.seq_rec_sem.intros
seq_nop.intros
I_Semantics_Calc.base_sem_next.intros
I_Semantics_Calc.i_base_sem.intros
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