theory I_Elle_Semantics
  imports I_Semantics Elle_Semantics I_Seq_Semantics
begin

locale I_Elle_Semantics_Sig = I_Seq_Semantics_Sig +
  Elle_Semantics_Sig

(*locale I_Elle_Semantics = I_Elle_Semantics_Sig*)

locale I_Elle_Semantics = I_Seq_Semantics + Elle_Semantics

locale I_Elle_Semantics_Final = I_Elle_Semantics


sublocale I_Elle_Semantics_Final \<subseteq> Gensyn_Semantics
  where xr = xr and ms = ms and 
    
  done

sublocale 

end