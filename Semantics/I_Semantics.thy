theory I_Semantics imports "Gensym_Semantics" "../Syntax/Sym_I"
begin

(* Do we interpret or extend?
sublocale? 
use rewrites to change base_sem and rec_sem?
should this have trivial control flow, or allow insts
to do weird control flow things?
*)
(* Do we want both a regular and exec? i think so *)

(* options

(idea: is generic gensym_sem the "top" or "bottom"
element of our "lattice" of semantics?)

1. take just i_sem. do semantics for gensyms extending
instruction sym, but return None on unknown ones
- rely on being "downcalled" from higher levels

2. take a gensym semantics and override it in the
case of instructions
- "upcall" in the case of unknown instructions
- what if higher levels impose restrictions on
instructions?
  - could use explicit subtyping...
eed

*)

locale I_Semantics = 
  fixes i_sem :: "'i \<Rightarrow> 'g \<Rightarrow> childpath \<Rightarrow> 'mstate => 'mstate \<Rightarrow> childpath option \<Rightarrow> bool"

fun i_base_sem :: "('b, 'r, 'g) gensym \<Rightarrow>
                   'g \<Rightarrow> 'b \<Rightarrow> childpath \<Rightarrow> 'mstate \<Rightarrow>
                    
                    

(* should this be for anything extending inst gensym?
it seems like we don't lose much by doing that
*)
interpretation Gensym_I_Semantics 

(* approach for now: new locale that instantiates the old one
   and adds new ones 
   this might not enable us to make maximal use of the locale
   hierarchy though
 *)

end