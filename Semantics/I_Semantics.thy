theory I_Semantics imports "Gensym_Semantics" "../Syntax/Sym_I"
begin

(* Do we interpret or extend?
sublocale? 
use rewrites to change base_sem and rec_sem?
should this have trivial control flow, or allow insts
to do weird control flow things?
for generality i think we want to allow weird control flow
also how do we handle cases where we were not given
a real instruction but rather something else?
*)

local I_Semantics = Gensym_Semantics +
  fixes i_sem :: "'i \<Rightarrow> 'g \<Rightarrow> childpath \<Rightarrow> 'mstate =

(* approach for now: new locale that instantiates the old one
   and adds new ones 
   this might not enable us to make maximal use of the locale
   hierarchy though
 *)

end