theory I_Seq_Semantics
  imports I_Semantics Seq_Semantics
begin

locale I_Seq_Semantics = I_Semantics_Sig + Seq_Semantics_Sig

sublocale I_Semantics \<subseteq> Base_Next_Semantics
  where base_sem = i_base_sem
  done


sublocale I_Seq_Semantics \<subseteq> I_Semantics
  where i_sem = i_sem
  done

sublocale I_Seq_Semantics \<subseteq> Seq_Semantics
  where seq_sem = seq_sem
  done


print_locale! I_Seq_Semantics

sublocale I_Seq_Semantics \<subseteq> Gensyn_Semantics
  where base_sem = i_base_sem
    and rec_sem = seq_rec_sem

end