theory Syn_Elle imports Main "../Syntax_Utils" (*Syn_I*)
begin

(* Elle syntax *)

(* TODO: do we even need to import Syn_I? *)

type_synonym ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle =
  "'xb + 'llx + 'ljx + 'ljix + 'xa"

type_synonym ('llx, 'ljx, 'ljix, 'xb, 'xa, 'llxo, 'ljxo, 'ljixo) syn_elle_disc =
  "('xb * ('llx \<Rightarrow> 'llxo) * ('ljx \<Rightarrow> 'ljxo) * ('ljix \<Rightarrow> 'ljixo) * 'xa)"

definition LLab :: "'llx \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LLab x = snth2h x"

definition LJmp :: "'ljx \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LJmp x = snth3h x"

definition LJmpI :: "'ljix \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LJmpI x = snth4h x"

end